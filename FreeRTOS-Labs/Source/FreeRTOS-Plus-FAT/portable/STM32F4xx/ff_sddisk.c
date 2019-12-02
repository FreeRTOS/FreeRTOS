/*
 * FreeRTOS+FAT build 191128 - Note:  FreeRTOS+FAT is still in the lab!
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 * Authors include James Walmsley, Hein Tibosch and Richard Barry
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 *
 */

/* Standard includes. */
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <stdio.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"
#include "portmacro.h"

/* FreeRTOS+FAT includes. */
#include "ff_sddisk.h"
#include "ff_sys.h"

/* ST HAL includes. */
#include "stm32f4xx_hal.h"

/* Misc definitions. */
#define sdSIGNATURE 			0x41404342UL
#define sdHUNDRED_64_BIT		( 100ull )
#define sdBYTES_PER_MB			( 1024ull * 1024ull )
#define sdSECTORS_PER_MB		( sdBYTES_PER_MB / 512ull )
#define sdIOMAN_MEM_SIZE		4096

/* DMA constants. */
#define SD_DMAx_Tx_CHANNEL					DMA_CHANNEL_4
#define SD_DMAx_Rx_CHANNEL					DMA_CHANNEL_4
#define SD_DMAx_Tx_STREAM					DMA2_Stream6
#define SD_DMAx_Rx_STREAM					DMA2_Stream3
#define SD_DMAx_Tx_IRQn						DMA2_Stream6_IRQn
#define SD_DMAx_Rx_IRQn						DMA2_Stream3_IRQn
#define __DMAx_TxRx_CLK_ENABLE				__DMA2_CLK_ENABLE
#define configSDIO_DMA_INTERRUPT_PRIORITY	( configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY )

/* Define a time-out for all DMA transactions in msec. */
#ifndef sdMAX_TIME_TICKS
	#define sdMAX_TIME_TICKS	pdMS_TO_TICKS( 2000UL )
#endif

#ifndef configSD_DETECT_PIN
	#error configSD_DETECT_PIN must be defined in FreeRTOSConfig.h to the pin used to detect if the SD card is present.
#endif

#ifndef configSD_DETECT_GPIO_PORT
	#error configSD_DETECT_GPIO_PORT must be defined in FreeRTOSConfig.h to the port on which configSD_DETECT_PIN is located.
#endif

#ifndef sdCARD_DETECT_DEBOUNCE_TIME_MS
	/* Debouncing time is applied only after card gets inserted. */
	#define sdCARD_DETECT_DEBOUNCE_TIME_MS	( 5000 )
#endif

#ifndef sdARRAY_SIZE
	#define	sdARRAY_SIZE( x )	( int )( sizeof( x ) / sizeof( x )[ 0 ] )
#endif

/*-----------------------------------------------------------*/

/*
 * Return pdFALSE if the SD card is not inserted.  This function just reads the
 * value of the GPIO C/D pin.
 */
static BaseType_t prvSDDetect( void );

/*
 * Translate a numeric code like 'SD_TX_UNDERRUN' to a printable string.
 */
static const char *prvSDCodePrintable( uint32_t ulCode );

/*
 * The following 'hook' must be provided by the user of this module.  It will be
 * called from a GPIO ISR after every change.  Note that during the ISR, the
 * value of the GPIO is not stable and it can not be used.  All you can do from
 * this hook is wake-up some task, which will call FF_SDDiskDetect().
 */
extern void vApplicationCardDetectChangeHookFromISR( BaseType_t *pxHigherPriorityTaskWoken );

/*
 * Hardware initialisation.
 */
static void prvSDIO_SD_Init( void );
static void vGPIO_SD_Init( SD_HandleTypeDef* xSDHandle );

/*
 * Check if the card is present, and if so, print out some info on the card.
 */
static BaseType_t prvSDMMCInit( BaseType_t xDriveNumber );

#if( SDIO_USES_DMA != 0 )
	/*
	 * Initialise the DMA for SDIO cards.
	 */
	static void prvSDIO_DMA_Init( void );
#endif

#if( SDIO_USES_DMA != 0 )
	/*
	 * A function will be called at the start of a DMA action.
	 */
	static void prvEventSetupFunction( SD_HandleTypeDef * pxHandle );
#endif

#if( SDIO_USES_DMA != 0 )
	/*
	 * This function is supposed to wait for an event: SDIO or DMA.
	 * Return non-zero if a timeout has been reached.
	 */
	static uint32_t prvEventWaitFunction( SD_HandleTypeDef *pxHandle );
#endif

/*-----------------------------------------------------------*/

typedef struct
{
	/* Only after a card has been inserted, debouncing is necessary. */
	TickType_t xRemainingTime;
	TimeOut_t xTimeOut;
	UBaseType_t
		bLastPresent : 1,
		bStableSignal : 1;
} CardDetect_t;

/* Used to handle timeouts. */
static TickType_t xDMARemainingTime;
static TimeOut_t xDMATimeOut;

/* Used to unblock the task that calls prvEventWaitFunction() after an event has
occurred. */
static SemaphoreHandle_t xSDCardSemaphore = NULL;

/* Handle of the SD card being used. */
static SD_HandleTypeDef xSDHandle;

/* Holds parameters for the detected SD card. */
static HAL_SD_CardInfoTypedef xSDCardInfo;

/* Mutex for partition. */
static SemaphoreHandle_t xPlusFATMutex = NULL;

/* Remembers if the card is currently considered to be present. */
static BaseType_t xSDCardStatus = pdFALSE;

/* Maintains state for card detection. */
static CardDetect_t xCardDetect;

/*-----------------------------------------------------------*/

static int32_t prvFFRead( uint8_t *pucBuffer, uint32_t ulSectorNumber, uint32_t ulSectorCount, FF_Disk_t *pxDisk )
{
int32_t lReturnCode = FF_ERR_IOMAN_OUT_OF_BOUNDS_READ | FF_ERRFLAG;

	if( ( pxDisk != NULL ) &&
		( xSDCardStatus == pdPASS ) &&
		( pxDisk->ulSignature == sdSIGNATURE ) &&
		( pxDisk->xStatus.bIsInitialised != pdFALSE ) &&
		( ulSectorNumber < pxDisk->ulNumberOfSectors ) &&
		( ( pxDisk->ulNumberOfSectors - ulSectorNumber ) >= ulSectorCount ) )
	{
	uint64_t ullReadAddr;
	HAL_SD_ErrorTypedef sd_result;

		ullReadAddr = 512ull * ( uint64_t ) ulSectorNumber;

		#if( SDIO_USES_DMA == 0 )
		{
			sd_result = HAL_SD_ReadBlocks( &xSDHandle, (uint32_t *) pucBuffer, ullReadAddr, 512ul, ulSectorCount );
		}
		#else
		{
			if( ( ( ( size_t )pucBuffer ) & ( sizeof( size_t ) - 1 ) ) == 0 )
			{
				/* The buffer is word-aligned, call DMA read directly. */
				sd_result = HAL_SD_ReadBlocks_DMA( &xSDHandle, (uint32_t *) pucBuffer, ullReadAddr, 512ul, ulSectorCount);
				if( sd_result == SD_OK )
				{
					sd_result = HAL_SD_CheckReadOperation( &xSDHandle, sdMAX_TIME_TICKS );
				}
			}
			else
			{
			uint32_t ulSector;
			uint8_t *pucDMABuffer = ffconfigMALLOC( 512ul );

				/* The buffer is NOT word-aligned, copy first to an aligned buffer. */
				if( pucDMABuffer != NULL )
				{
					sd_result = SD_OK;
					for( ulSector = 0; ulSector < ulSectorCount; ulSector++ )
					{
						ullReadAddr = 512ull * ( ( uint64_t ) ulSectorNumber + ( uint64_t ) ulSector );
						sd_result = HAL_SD_ReadBlocks_DMA( &xSDHandle, ( uint32_t * )pucDMABuffer, ullReadAddr, 512ul, 1 );

						if( sd_result == SD_OK )
						{
							sd_result = HAL_SD_CheckReadOperation( &xSDHandle, sdMAX_TIME_TICKS );
							if( sd_result != SD_OK )
							{
								break;
							}
							memcpy( pucBuffer + 512ul * ulSector, pucDMABuffer, 512ul );
						}
					}
					ffconfigFREE( pucDMABuffer );
				}
				else
				{
					sd_result = SD_INVALID_PARAMETER;
				}
			}
		}
		#endif	/* SDIO_USES_DMA */

		if( sd_result == SD_OK )
		{
			lReturnCode = 0L;
		}
		else
		{
			/* Some error occurred. */
			FF_PRINTF( "prvFFRead: %lu: %u (%s)\n", ulSectorNumber, sd_result, prvSDCodePrintable( sd_result ) );
		}
	}
	else
	{
		/* Make sure no random data is in the returned buffer. */
		memset( ( void * ) pucBuffer, '\0', ulSectorCount * 512UL );

		if( pxDisk->xStatus.bIsInitialised != pdFALSE )
		{
			FF_PRINTF( "prvFFRead: warning: %lu + %lu > %lu\n", ulSectorNumber, ulSectorCount, pxDisk->ulNumberOfSectors );
		}
	}

	return lReturnCode;
}
/*-----------------------------------------------------------*/

static int32_t prvFFWrite( uint8_t *pucBuffer, uint32_t ulSectorNumber, uint32_t ulSectorCount, FF_Disk_t *pxDisk )
{
int32_t lReturnCode = FF_ERR_IOMAN_OUT_OF_BOUNDS_READ | FF_ERRFLAG;

	if( ( pxDisk != NULL ) &&
		( xSDCardStatus == pdPASS ) &&
		( pxDisk->ulSignature == sdSIGNATURE ) &&
		( pxDisk->xStatus.bIsInitialised != pdFALSE ) &&
		( ulSectorNumber < pxDisk->ulNumberOfSectors ) &&
		( ( pxDisk->ulNumberOfSectors - ulSectorNumber ) >= ulSectorCount ) )
	{
		HAL_SD_ErrorTypedef sd_result;
		uint64_t ullWriteAddr;
		ullWriteAddr = 512ull * ulSectorNumber;

		#if( SDIO_USES_DMA == 0 )
		{
			sd_result = HAL_SD_WriteBlocks( &xSDHandle, ( uint32_t * )pucBuffer, ullWriteAddr, 512ul, ulSectorCount );
		}
		#else
		{
			if( ( ( ( size_t )pucBuffer ) & ( sizeof( size_t ) - 1 ) ) == 0 )
			{
				/* The buffer is word-aligned, call DMA reawrite directly. */
				sd_result = HAL_SD_WriteBlocks_DMA( &xSDHandle, ( uint32_t * )pucBuffer, ullWriteAddr, 512ul, ulSectorCount );
				if( sd_result == SD_OK )
				{
					sd_result = HAL_SD_CheckWriteOperation( &xSDHandle, sdMAX_TIME_TICKS );
				}
			}
			else
			{
			uint32_t ulSector;
			uint8_t *pucDMABuffer = ffconfigMALLOC( 512ul );

				/* The buffer is NOT word-aligned, read to an aligned buffer and then
				copy the data to the user provided buffer. */
				if( pucDMABuffer != NULL )
				{
					sd_result = SD_OK;
					for( ulSector = 0; ulSector < ulSectorCount; ulSector++ )
					{
						memcpy( pucDMABuffer, pucBuffer + 512ul * ulSector, 512ul );
						ullWriteAddr = 512ull * ( ulSectorNumber + ulSector );
						sd_result = HAL_SD_WriteBlocks_DMA( &xSDHandle, ( uint32_t * )pucDMABuffer, ullWriteAddr, 512ul, 1 );
						if( sd_result == SD_OK )
						{
							sd_result = HAL_SD_CheckWriteOperation( &xSDHandle, sdMAX_TIME_TICKS );
							if( sd_result != SD_OK )
							{
								break;
							}
						}
					}
					ffconfigFREE( pucDMABuffer );
				}
				else
				{
					sd_result = SD_INVALID_PARAMETER;
				}
			}
		}
		#endif	/* SDIO_USES_DMA */

		if( sd_result == SD_OK )
		{
			/* No errors. */
			lReturnCode = 0L;
		}
		else
		{
			FF_PRINTF( "prvFFWrite: %lu: %u (%s)\n", ulSectorNumber, sd_result, prvSDCodePrintable( sd_result ) );
		}
	}
	else
	{
		if( pxDisk->xStatus.bIsInitialised != pdFALSE )
		{
			FF_PRINTF( "prvFFWrite: warning: %lu + %lu > %lu\n", ulSectorNumber, ulSectorCount, pxDisk->ulNumberOfSectors );
		}
	}

	return lReturnCode;
}
/*-----------------------------------------------------------*/

void FF_SDDiskFlush( FF_Disk_t *pxDisk )
{
	if( ( pxDisk != NULL ) &&
		( pxDisk->xStatus.bIsInitialised != pdFALSE ) &&
		( pxDisk->pxIOManager != NULL ) )
	{
		FF_FlushCache( pxDisk->pxIOManager );
	}
}
/*-----------------------------------------------------------*/

static void vGPIO_SD_Init(SD_HandleTypeDef* xSDHandle)
{
GPIO_InitTypeDef GPIO_InitStruct;

	if( xSDHandle->Instance == SDIO )
	{
		/* Peripheral clock enable */
		__SDIO_CLK_ENABLE();

		/**SDIO GPIO Configuration
		PC8     ------> SDIO_D0
		PC9     ------> SDIO_D1
		PC10    ------> SDIO_D2
		PC11    ------> SDIO_D3
		PC12    ------> SDIO_CK
		PD2     ------> SDIO_CMD
		*/
		__HAL_RCC_GPIOC_CLK_ENABLE();
		#if( BUS_4BITS != 0 )
		{
			GPIO_InitStruct.Pin = GPIO_PIN_8 | GPIO_PIN_9 | GPIO_PIN_10 | GPIO_PIN_11 | GPIO_PIN_12;
		}
		#else
		{
			GPIO_InitStruct.Pin = GPIO_PIN_8 | GPIO_PIN_9 | GPIO_PIN_12;
		}
		#endif
		GPIO_InitStruct.Mode = GPIO_MODE_AF_PP;
		GPIO_InitStruct.Pull = GPIO_NOPULL;
		GPIO_InitStruct.Speed = GPIO_SPEED_FAST;
		GPIO_InitStruct.Alternate = GPIO_AF12_SDIO;
		HAL_GPIO_Init(GPIOC, &GPIO_InitStruct);

		__HAL_RCC_GPIOD_CLK_ENABLE();
		GPIO_InitStruct.Pin = GPIO_PIN_2;
		GPIO_InitStruct.Mode = GPIO_MODE_AF_PP;
		GPIO_InitStruct.Pull = GPIO_NOPULL;
		GPIO_InitStruct.Speed = GPIO_SPEED_LOW;
		GPIO_InitStruct.Alternate = GPIO_AF12_SDIO;
		HAL_GPIO_Init(GPIOD, &GPIO_InitStruct);
	}
}
/*-----------------------------------------------------------*/

FF_Disk_t *FF_SDDiskInit( const char *pcName )
{
FF_Error_t xFFError;
BaseType_t xPartitionNumber = 0;
FF_CreationParameters_t xParameters;
FF_Disk_t *pxDisk;

	xSDCardStatus = prvSDMMCInit( 0 );

	if( xSDCardStatus != pdPASS )
	{
		FF_PRINTF( "FF_SDDiskInit: prvSDMMCInit failed\n" );
		pxDisk = NULL;
	}
	else
	{
		pxDisk = (FF_Disk_t *)ffconfigMALLOC( sizeof( *pxDisk ) );
		if( pxDisk == NULL )
		{
			FF_PRINTF( "FF_SDDiskInit: Malloc failed\n" );
		}
		else
		{
			/* Initialise the created disk structure. */
			memset( pxDisk, '\0', sizeof( *pxDisk ) );

			pxDisk->ulNumberOfSectors = xSDCardInfo.CardCapacity / 512;

			if( xPlusFATMutex == NULL )
			{
				xPlusFATMutex = xSemaphoreCreateRecursiveMutex();
			}
			pxDisk->ulSignature = sdSIGNATURE;

			if( xPlusFATMutex != NULL)
			{
				memset( &xParameters, '\0', sizeof( xParameters ) );
				xParameters.ulMemorySize = sdIOMAN_MEM_SIZE;
				xParameters.ulSectorSize = 512;
				xParameters.fnWriteBlocks = prvFFWrite;
				xParameters.fnReadBlocks = prvFFRead;
				xParameters.pxDisk = pxDisk;

				/* prvFFRead()/prvFFWrite() are not re-entrant and must be
				protected with the use of a semaphore. */
				xParameters.xBlockDeviceIsReentrant = pdFALSE;

				/* The semaphore will be used to protect critical sections in
				the +FAT driver, and also to avoid concurrent calls to
				prvFFRead()/prvFFWrite() from different tasks. */
				xParameters.pvSemaphore = ( void * ) xPlusFATMutex;

				pxDisk->pxIOManager = FF_CreateIOManger( &xParameters, &xFFError );

				if( pxDisk->pxIOManager == NULL )
				{
					FF_PRINTF( "FF_SDDiskInit: FF_CreateIOManger: %s\n", (const char*)FF_GetErrMessage( xFFError ) );
					FF_SDDiskDelete( pxDisk );
					pxDisk = NULL;
				}
				else
				{
					pxDisk->xStatus.bIsInitialised = pdTRUE;
					pxDisk->xStatus.bPartitionNumber = xPartitionNumber;
					if( FF_SDDiskMount( pxDisk ) == 0 )
					{
						FF_SDDiskDelete( pxDisk );
						pxDisk = NULL;
					}
					else
					{
						if( pcName == NULL )
						{
							pcName = "/";
						}
						FF_FS_Add( pcName, pxDisk );
						FF_PRINTF( "FF_SDDiskInit: Mounted SD-card as root \"%s\"\n", pcName );
						FF_SDDiskShowPartition( pxDisk );
					}
				}	/* if( pxDisk->pxIOManager != NULL ) */
			}	/* if( xPlusFATMutex != NULL) */
		}	/* if( pxDisk != NULL ) */
	}	/* if( xSDCardStatus == pdPASS ) */

	return pxDisk;
}
/*-----------------------------------------------------------*/

BaseType_t FF_SDDiskFormat( FF_Disk_t *pxDisk, BaseType_t xPartitionNumber )
{
FF_Error_t xError;
BaseType_t xReturn = pdFAIL;

	xError = FF_Unmount( pxDisk );

	if( FF_isERR( xError ) != pdFALSE )
	{
		FF_PRINTF( "FF_SDDiskFormat: unmount fails: %08x\n", ( unsigned ) xError );
	}
	else
	{
		/* Format the drive - try FAT32 with large clusters. */
		xError = FF_Format( pxDisk, xPartitionNumber, pdFALSE, pdFALSE);

		if( FF_isERR( xError ) )
		{
			FF_PRINTF( "FF_SDDiskFormat: %s\n", (const char*)FF_GetErrMessage( xError ) );
		}
		else
		{
			FF_PRINTF( "FF_SDDiskFormat: OK, now remounting\n" );
			pxDisk->xStatus.bPartitionNumber = xPartitionNumber;
			xError = FF_SDDiskMount( pxDisk );
			FF_PRINTF( "FF_SDDiskFormat: rc %08x\n", ( unsigned )xError );
			if( FF_isERR( xError ) == pdFALSE )
			{
				xReturn = pdPASS;
				FF_SDDiskShowPartition( pxDisk );
			}
		}
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

BaseType_t FF_SDDiskUnmount( FF_Disk_t *pxDisk )
{
FF_Error_t xFFError;
BaseType_t xReturn = pdPASS;

	if( ( pxDisk != NULL ) && ( pxDisk->xStatus.bIsMounted != pdFALSE ) )
	{
		pxDisk->xStatus.bIsMounted = pdFALSE;
		xFFError = FF_Unmount( pxDisk );

		if( FF_isERR( xFFError ) )
		{
			FF_PRINTF( "FF_SDDiskUnmount: rc %08x\n", ( unsigned )xFFError );
			xReturn = pdFAIL;
		}
		else
		{
			FF_PRINTF( "Drive unmounted\n" );
		}
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

BaseType_t FF_SDDiskReinit( FF_Disk_t *pxDisk )
{
BaseType_t xStatus = prvSDMMCInit( 0 ); /* Hard coded index. */

	/*_RB_ parameter not used. */
	( void ) pxDisk;

	FF_PRINTF( "FF_SDDiskReinit: rc %08x\n", ( unsigned ) xStatus );
	return xStatus;
}
/*-----------------------------------------------------------*/

BaseType_t FF_SDDiskMount( FF_Disk_t *pxDisk )
{
FF_Error_t xFFError;
BaseType_t xReturn;

	/* Mount the partition */
	xFFError = FF_Mount( pxDisk, pxDisk->xStatus.bPartitionNumber );

	if( FF_isERR( xFFError ) )
	{
		FF_PRINTF( "FF_SDDiskMount: %08lX\n", xFFError );
		xReturn = pdFAIL;
	}
	else
	{
		pxDisk->xStatus.bIsMounted = pdTRUE;
		FF_PRINTF( "****** FreeRTOS+FAT initialized %lu sectors\n", pxDisk->pxIOManager->xPartition.ulTotalSectors );
		xReturn = pdPASS;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

FF_IOManager_t *sddisk_ioman( FF_Disk_t *pxDisk )
{
FF_IOManager_t *pxReturn;

	if( ( pxDisk != NULL ) && ( pxDisk->xStatus.bIsInitialised != pdFALSE ) )
	{
		pxReturn = pxDisk->pxIOManager;
	}
	else
	{
		pxReturn = NULL;
	}
	return pxReturn;
}
/*-----------------------------------------------------------*/

/* Release all resources */
BaseType_t FF_SDDiskDelete( FF_Disk_t *pxDisk )
{
	if( pxDisk != NULL )
	{
		pxDisk->ulSignature = 0;
		pxDisk->xStatus.bIsInitialised = 0;
		if( pxDisk->pxIOManager != NULL )
		{
			if( FF_Mounted( pxDisk->pxIOManager ) != pdFALSE )
			{
				FF_Unmount( pxDisk );
			}
			FF_DeleteIOManager( pxDisk->pxIOManager );
		}

		vPortFree( pxDisk );
	}
	return 1;
}
/*-----------------------------------------------------------*/

BaseType_t FF_SDDiskShowPartition( FF_Disk_t *pxDisk )
{
FF_Error_t xError;
uint64_t ullFreeSectors;
uint32_t ulTotalSizeMB, ulFreeSizeMB;
int iPercentageFree;
FF_IOManager_t *pxIOManager;
const char *pcTypeName = "unknown type";
BaseType_t xReturn = pdPASS;

	if( pxDisk == NULL )
	{
		xReturn = pdFAIL;
	}
	else
	{
		pxIOManager = pxDisk->pxIOManager;

		FF_PRINTF( "Reading FAT and calculating Free Space\n" );

		switch( pxIOManager->xPartition.ucType )
		{
			case FF_T_FAT12:
				pcTypeName = "FAT12";
				break;

			case FF_T_FAT16:
				pcTypeName = "FAT16";
				break;

			case FF_T_FAT32:
				pcTypeName = "FAT32";
				break;

			default:
				pcTypeName = "UNKOWN";
				break;
		}

		FF_GetFreeSize( pxIOManager, &xError );

		ullFreeSectors = pxIOManager->xPartition.ulFreeClusterCount * pxIOManager->xPartition.ulSectorsPerCluster;
		iPercentageFree = ( int ) ( ( sdHUNDRED_64_BIT * ullFreeSectors + pxIOManager->xPartition.ulDataSectors / 2 ) /
			( ( uint64_t )pxIOManager->xPartition.ulDataSectors ) );

		ulTotalSizeMB = pxIOManager->xPartition.ulDataSectors / sdSECTORS_PER_MB;
		ulFreeSizeMB = ( uint32_t ) ( ullFreeSectors / sdSECTORS_PER_MB );

		/* It is better not to use the 64-bit format such as %Lu because it
		might not be implemented. */
		FF_PRINTF( "Partition Nr   %8u\n", pxDisk->xStatus.bPartitionNumber );
		FF_PRINTF( "Type           %8u (%s)\n", pxIOManager->xPartition.ucType, pcTypeName );
		FF_PRINTF( "VolLabel       '%8s' \n", pxIOManager->xPartition.pcVolumeLabel );
		FF_PRINTF( "TotalSectors   %8lu\n", pxIOManager->xPartition.ulTotalSectors );
		FF_PRINTF( "SecsPerCluster %8lu\n", pxIOManager->xPartition.ulSectorsPerCluster );
		FF_PRINTF( "Size           %8lu MB\n", ulTotalSizeMB );
		FF_PRINTF( "FreeSize       %8lu MB ( %d perc free )\n", ulFreeSizeMB, iPercentageFree );
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

/* SDIO init function */
static void prvSDIO_SD_Init( void )
{
	xSDHandle.Instance = SDIO;
	xSDHandle.Init.ClockEdge = SDIO_CLOCK_EDGE_RISING;
	xSDHandle.Init.ClockBypass = SDIO_CLOCK_BYPASS_DISABLE;
	xSDHandle.Init.ClockPowerSave = SDIO_CLOCK_POWER_SAVE_DISABLE;

	/* Start as a 1-bit bus and switch to 4-bits later on. */
	xSDHandle.Init.BusWide = SDIO_BUS_WIDE_1B;

	xSDHandle.Init.HardwareFlowControl = SDIO_HARDWARE_FLOW_CONTROL_DISABLE;

	/* Use fastest CLOCK at 0. */
	xSDHandle.Init.ClockDiv = 32;

	#if( SDIO_USES_DMA != 0 )
	{
		xSDHandle.EventSetupFunction = prvEventSetupFunction;
		xSDHandle.EventWaitFunction = prvEventWaitFunction;
	}
	#else
	{
		xSDHandle.EventSetupFunction = NULL;
		xSDHandle.EventWaitFunction = NULL;
	}
	#endif
	__HAL_RCC_SDIO_CLK_ENABLE( );
}
/*-----------------------------------------------------------*/

/* This routine returns true if the SD-card is inserted.  After insertion, it
will wait for sdCARD_DETECT_DEBOUNCE_TIME_MS before returning pdTRUE. */
BaseType_t FF_SDDiskDetect( FF_Disk_t *pxDisk )
{
int xReturn;

	xReturn = prvSDDetect();

	if( xReturn != pdFALSE )
	{
		if( xCardDetect.bStableSignal == pdFALSE )
		{
			/* The card seems to be present. */
			if( xCardDetect.bLastPresent == pdFALSE )
			{
				xCardDetect.bLastPresent = pdTRUE;
				xCardDetect.xRemainingTime = pdMS_TO_TICKS( ( TickType_t ) sdCARD_DETECT_DEBOUNCE_TIME_MS );
				/* Fetch the current time. */
				vTaskSetTimeOutState( &xCardDetect.xTimeOut );
			}
			/* Has the timeout been reached? */
			if( xTaskCheckForTimeOut( &xCardDetect.xTimeOut, &xCardDetect.xRemainingTime ) != pdFALSE )
			{
				xCardDetect.bStableSignal = pdTRUE;
			}
			else
			{
				/* keep returning false until de time-out is reached. */
				xReturn = pdFALSE;
			}
		}
	}
	else
	{
		xCardDetect.bLastPresent = pdFALSE;
		xCardDetect.bStableSignal = pdFALSE;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

/* Raw SD-card detection, just return the GPIO status. */
static BaseType_t prvSDDetect( void )
{
int iReturn;

	/*!< Check GPIO to detect SD */
	if( HAL_GPIO_ReadPin( configSD_DETECT_GPIO_PORT, configSD_DETECT_PIN ) != 0 )
	{
		/* The internal pull-up makes the signal high. */
		iReturn = pdFALSE;
	}
	else
	{
		/* The card will pull the GPIO signal down. */
		iReturn = pdTRUE;
	}

	return iReturn;
}
/*-----------------------------------------------------------*/

static BaseType_t prvSDMMCInit( BaseType_t xDriveNumber )
{
	/* 'xDriveNumber' not yet in use. */
	( void )xDriveNumber;

	if( xSDCardSemaphore == NULL )
	{
		xSDCardSemaphore = xSemaphoreCreateBinary();
	}
	prvSDIO_SD_Init();

	vGPIO_SD_Init( &xSDHandle );

	#if( SDIO_USES_DMA != 0 )
	{
		prvSDIO_DMA_Init( );
	}
	#endif

	int SD_state = SD_OK;
	/* Check if the SD card is plugged in the slot */
	if( prvSDDetect() == pdFALSE )
	{
		FF_PRINTF( "No SD card detected\n" );
		return 0;
	}
	/* When starting up, skip debouncing of the Card Detect signal. */
	xCardDetect.bLastPresent = pdTRUE;
	xCardDetect.bStableSignal = pdTRUE;
	/* Initialise the SDIO device and read the card parameters. */
	SD_state = HAL_SD_Init( &xSDHandle, &xSDCardInfo );
	#if( BUS_4BITS != 0 )
    {
		if( SD_state == SD_OK )
		{
			HAL_SD_ErrorTypedef rc;

			xSDHandle.Init.BusWide = SDIO_BUS_WIDE_4B;
			rc = HAL_SD_WideBusOperation_Config(&xSDHandle, SDIO_BUS_WIDE_4B);
			if( rc != SD_OK )
			{
				FF_PRINTF( "HAL_SD_WideBus: %d: %s\n", rc, prvSDCodePrintable( ( uint32_t )rc ) );
			}
		}
    }
	#endif
	FF_PRINTF( "HAL_SD_Init: %d: %s type: %s Capacity: %lu MB\n",
		SD_state,
		prvSDCodePrintable( ( uint32_t )SD_state ),
		xSDHandle.CardType == HIGH_CAPACITY_SD_CARD ? "SDHC" : "SD",
		xSDCardInfo.CardCapacity / ( 1024 * 1024 ) );

	return SD_state == SD_OK ? 1 : 0;
}
/*-----------------------------------------------------------*/

struct xCODE_NAME
{
	uint32_t ulValue;
	const char *pcName;
};

const struct xCODE_NAME xSD_CODES[] =
{
	{ SD_CMD_CRC_FAIL,          "CMD_CRC_FAIL: Command response received (but CRC check failed)" },
	{ SD_DATA_CRC_FAIL,         "DATA_CRC_FAIL: Data block sent/received (CRC check failed)" },
	{ SD_CMD_RSP_TIMEOUT,       "CMD_RSP_TIMEOUT: Command response timeout" },
	{ SD_DATA_TIMEOUT,          "DATA_TIMEOUT: Data timeout" },
	{ SD_TX_UNDERRUN,           "TX_UNDERRUN: Transmit FIFO underrun" },
	{ SD_RX_OVERRUN,            "RX_OVERRUN: Receive FIFO overrun" },
	{ SD_START_BIT_ERR,         "START_BIT_ERR: Start bit not detected on all data signals in wide bus mode" },
	{ SD_CMD_OUT_OF_RANGE,      "CMD_OUT_OF_RANGE: Command's argument was out of range" },
	{ SD_ADDR_MISALIGNED,       "ADDR_MISALIGNED: Misaligned address" },
	{ SD_BLOCK_LEN_ERR,         "BLOCK_LEN_ERR: Transferred block length is not allowed for the card or the number of transferred bytes does not match the block length" },
	{ SD_ERASE_SEQ_ERR,         "ERASE_SEQ_ERR: An error in the sequence of erase command occurs." },
	{ SD_BAD_ERASE_PARAM,       "BAD_ERASE_PARAM: An invalid selection for erase groups" },
	{ SD_WRITE_PROT_VIOLATION,  "WRITE_PROT_VIOLATION: Attempt to program a write protect block" },
	{ SD_LOCK_UNLOCK_FAILED,    "LOCK_UNLOCK_FAILED: Sequence or password error has been detected in unlock command or if there was an attempt to access a locked card" },
	{ SD_COM_CRC_FAILED,        "COM_CRC_FAILED: CRC check of the previous command failed" },
	{ SD_ILLEGAL_CMD,           "ILLEGAL_CMD: Command is not legal for the card state" },
	{ SD_CARD_ECC_FAILED,       "CARD_ECC_FAILED: Card internal ECC was applied but failed to correct the data" },
	{ SD_CC_ERROR,              "CC_ERROR: Internal card controller error" },
	{ SD_GENERAL_UNKNOWN_ERROR, "GENERAL_UNKNOWN_ERROR: General or unknown error" },
	{ SD_STREAM_READ_UNDERRUN,  "STREAM_READ_UNDERRUN: The card could not sustain data transfer in stream read operation" },
	{ SD_STREAM_WRITE_OVERRUN,  "STREAM_WRITE_OVERRUN: The card could not sustain data programming in stream mode" },
	{ SD_CID_CSD_OVERWRITE,     "CID_CSD_OVERWRITE: CID/CSD overwrite error" },
	{ SD_WP_ERASE_SKIP,         "WP_ERASE_SKIP: Only partial address space was erased" },
	{ SD_CARD_ECC_DISABLED,     "CARD_ECC_DISABLED: Command has been executed without using internal ECC" },
	{ SD_ERASE_RESET,           "ERASE_RESET: Erase sequence was cleared before executing because an out of erase sequence command was received" },
	{ SD_AKE_SEQ_ERROR,         "AKE_SEQ_ERROR: Error in sequence of authentication" },
	{ SD_INVALID_VOLTRANGE,     "INVALID_VOLTRANGE" },
	{ SD_ADDR_OUT_OF_RANGE,     "ADDR_OUT_OF_RANGE" },
	{ SD_SWITCH_ERROR,          "SWITCH_ERROR" },
	{ SD_SDIO_DISABLED,         "SDIO_DISABLED" },
	{ SD_SDIO_FUNCTION_BUSY,    "SDIO_FUNCTION_BUSY" },
	{ SD_SDIO_FUNCTION_FAILED,  "SDIO_FUNCTION_FAILED" },
	{ SD_SDIO_UNKNOWN_FUNCTION, "SDIO_UNKNOWN_FUNCTION" },

	/**
	* @brief  Standard error defines
	*/
	{ SD_INTERNAL_ERROR,        "INTERNAL_ERROR" },
	{ SD_NOT_CONFIGURED,        "NOT_CONFIGURED" },
	{ SD_REQUEST_PENDING,       "REQUEST_PENDING" },
	{ SD_REQUEST_NOT_APPLICABLE,"REQUEST_NOT_APPLICABLE" },
	{ SD_INVALID_PARAMETER,     "INVALID_PARAMETER" },
	{ SD_UNSUPPORTED_FEATURE,   "UNSUPPORTED_FEATURE" },
	{ SD_UNSUPPORTED_HW,        "UNSUPPORTED_HW" },
	{ SD_ERROR,                 "ERROR" },
	{ SD_OK,                    "OK" },
};
/*-----------------------------------------------------------*/

static const char *prvSDCodePrintable( uint32_t ulCode )
{
static char retString[32];
const struct xCODE_NAME *pxCode;

	for( pxCode = xSD_CODES; pxCode <= xSD_CODES + sdARRAY_SIZE( xSD_CODES ) - 1; pxCode++ )
	{
		if( pxCode->ulValue == ulCode )
		{
			return pxCode->pcName;
		}
	}
	snprintf( retString, sizeof( retString ), "SD code %lu\n", ulCode );
	return retString;
}
/*-----------------------------------------------------------*/

#if( SDIO_USES_DMA != 0 )

	static void prvSDIO_DMA_Init( void )
	{
	static DMA_HandleTypeDef xRxDMAHandle;
	static DMA_HandleTypeDef xTxDMAHandle;

		/* Enable DMA2 clocks */
		__DMAx_TxRx_CLK_ENABLE();

		/* NVIC configuration for SDIO interrupts */
		HAL_NVIC_SetPriority(SDIO_IRQn, configSDIO_DMA_INTERRUPT_PRIORITY, 0);
		HAL_NVIC_EnableIRQ(SDIO_IRQn);

		/* Configure DMA Rx parameters */
		xRxDMAHandle.Init.Channel             = SD_DMAx_Rx_CHANNEL;
		xRxDMAHandle.Init.Direction           = DMA_PERIPH_TO_MEMORY;
		/* Peripheral address is fixed (FIFO). */
		xRxDMAHandle.Init.PeriphInc           = DMA_PINC_DISABLE;
		/* Memory address increases. */
		xRxDMAHandle.Init.MemInc              = DMA_MINC_ENABLE;
		xRxDMAHandle.Init.PeriphDataAlignment = DMA_PDATAALIGN_WORD;
		xRxDMAHandle.Init.MemDataAlignment    = DMA_MDATAALIGN_WORD;
		/* The peripheral has flow-control. */
		xRxDMAHandle.Init.Mode                = DMA_PFCTRL;
		xRxDMAHandle.Init.Priority            = DMA_PRIORITY_VERY_HIGH;
		xRxDMAHandle.Init.FIFOMode            = DMA_FIFOMODE_ENABLE;
		xRxDMAHandle.Init.FIFOThreshold       = DMA_FIFO_THRESHOLD_FULL;
		xRxDMAHandle.Init.MemBurst            = DMA_MBURST_INC4;
		xRxDMAHandle.Init.PeriphBurst         = DMA_PBURST_INC4;

		/* DMA2_Stream3. */
		xRxDMAHandle.Instance = SD_DMAx_Rx_STREAM;

		/* Associate the DMA handle */
		__HAL_LINKDMA(&xSDHandle, hdmarx, xRxDMAHandle);

		/* Deinitialize the stream for new transfer */
		HAL_DMA_DeInit(&xRxDMAHandle);

		/* Configure the DMA stream */
		HAL_DMA_Init(&xRxDMAHandle);

		/* Configure DMA Tx parameters */
		xTxDMAHandle.Init.Channel             = SD_DMAx_Tx_CHANNEL;
		xTxDMAHandle.Init.Direction           = DMA_MEMORY_TO_PERIPH;
		xTxDMAHandle.Init.PeriphInc           = DMA_PINC_DISABLE;
		xTxDMAHandle.Init.MemInc              = DMA_MINC_ENABLE;
		xTxDMAHandle.Init.PeriphDataAlignment = DMA_PDATAALIGN_WORD;
		xTxDMAHandle.Init.MemDataAlignment    = DMA_MDATAALIGN_WORD;
		xTxDMAHandle.Init.Mode                = DMA_PFCTRL;
		xTxDMAHandle.Init.Priority            = DMA_PRIORITY_VERY_HIGH;
		xTxDMAHandle.Init.FIFOMode            = DMA_FIFOMODE_ENABLE;
		xTxDMAHandle.Init.FIFOThreshold       = DMA_FIFO_THRESHOLD_FULL;
		xTxDMAHandle.Init.MemBurst            = DMA_MBURST_SINGLE;
		xTxDMAHandle.Init.PeriphBurst         = DMA_PBURST_INC4;

		/* DMA2_Stream6. */
		xTxDMAHandle.Instance = SD_DMAx_Tx_STREAM;

		/* Associate the DMA handle */
		__HAL_LINKDMA(&xSDHandle, hdmatx, xTxDMAHandle);

		/* Deinitialize the stream for new transfer */
		HAL_DMA_DeInit(&xTxDMAHandle);

		/* Configure the DMA stream */
		HAL_DMA_Init(&xTxDMAHandle);

		/* NVIC configuration for DMA transfer complete interrupt */
		HAL_NVIC_SetPriority(SD_DMAx_Rx_IRQn, configSDIO_DMA_INTERRUPT_PRIORITY + 2, 0);
		HAL_NVIC_EnableIRQ(SD_DMAx_Rx_IRQn);

		/* NVIC configuration for DMA transfer complete interrupt */
		HAL_NVIC_SetPriority(SD_DMAx_Tx_IRQn, configSDIO_DMA_INTERRUPT_PRIORITY + 2, 0);
		HAL_NVIC_EnableIRQ(SD_DMAx_Tx_IRQn);
	}
#endif	/* SDIO_USES_DMA */
/*-----------------------------------------------------------*/

#if( SDIO_USES_DMA != 0 )
	void SDIO_IRQHandler(void)
	{
	BaseType_t xHigherPriorityTaskWoken = 0;

		HAL_SD_IRQHandler( &xSDHandle );
		if( xSDCardSemaphore != NULL )
		{
			xSemaphoreGiveFromISR( xSDCardSemaphore, &xHigherPriorityTaskWoken );
		}
		portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
	}

#endif	/* SDIO_USES_DMA */
/*-----------------------------------------------------------*/

#if( SDIO_USES_DMA != 0 )

	void DMA2_Stream6_IRQHandler(void)
	{
	BaseType_t xHigherPriorityTaskWoken = 0;

		/* DMA SDIO-TX interrupt handler. */
		HAL_DMA_IRQHandler (xSDHandle.hdmatx);
		if( xSDCardSemaphore != NULL )
		{
			xSemaphoreGiveFromISR( xSDCardSemaphore, &xHigherPriorityTaskWoken );
		}
		portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
	}

#endif	/* SDIO_USES_DMA */
/*-----------------------------------------------------------*/

#if( SDIO_USES_DMA != 0 )

	void DMA2_Stream3_IRQHandler(void)
	{
	BaseType_t xHigherPriorityTaskWoken = 0;

		/* DMA SDIO-RX interrupt handler. */
		HAL_DMA_IRQHandler (xSDHandle.hdmarx);
		if( xSDCardSemaphore != NULL )
		{
			xSemaphoreGiveFromISR( xSDCardSemaphore, &xHigherPriorityTaskWoken );
		}
		portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
	}

#endif	/* SDIO_USES_DMA */
/*-----------------------------------------------------------*/

#if( SDIO_USES_DMA != 0 )

	static void prvEventSetupFunction( SD_HandleTypeDef * pxHandle )
	{
		/* A DMA transfer to or from the SD-card is about to start.
		Reset the timers that will be used in prvEventWaitFunction() */
		xDMARemainingTime = sdMAX_TIME_TICKS;
		vTaskSetTimeOutState( &xDMATimeOut );
	}

#endif	/* SDIO_USES_DMA != 0 */
/*-----------------------------------------------------------*/

#if( SDIO_USES_DMA != 0 )

	static uint32_t prvEventWaitFunction( SD_HandleTypeDef *pxHandle )
	{
	uint32_t ulReturn;

		/*
		 * It was measured how quickly a DMA interrupt was received. It varied
		 * between 0 and 4 ms.
		 * <= 1 ms : 8047
		 * <= 2 ms : 1850
		 * <= 3 ms :   99
		 * <= 4 ms :   79
		 * >= 5 ms :    0 times
		 */

		if( xTaskCheckForTimeOut( &xDMATimeOut, &xDMARemainingTime ) != pdFALSE )
		{
			/* The timeout has been reached, no need to block. */
			ulReturn = 1UL;
		}
		else
		{
			/* The timeout has not been reached yet, block on the semaphore. */
			xSemaphoreTake( xSDCardSemaphore, xDMARemainingTime );
			if( xTaskCheckForTimeOut( &xDMATimeOut, &xDMARemainingTime ) != pdFALSE )
			{
				ulReturn = 1UL;
			}
			else
			{
				ulReturn = 0UL;
			}
		}

		return ulReturn;
	}

#endif	/* SDIO_USES_DMA != 0 */
/*-----------------------------------------------------------*/

void HAL_GPIO_EXTI_Callback( uint16_t GPIO_Pin )
{
BaseType_t xHigherPriorityTaskWoken = pdFALSE;

	if( GPIO_Pin == configSD_DETECT_PIN )
	{
		vApplicationCardDetectChangeHookFromISR( &xHigherPriorityTaskWoken );
		portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
	}
}
/*-----------------------------------------------------------*/

void EXTI15_10_IRQHandler( void )
{
	HAL_GPIO_EXTI_IRQHandler( configSD_DETECT_PIN );	/* GPIO PIN H.13 */
}
/*-----------------------------------------------------------*/
