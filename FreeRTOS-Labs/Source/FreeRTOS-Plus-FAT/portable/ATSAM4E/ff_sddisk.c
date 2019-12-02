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

/* Atmel includes. */
#include <board.h>
#include <sd_mmc.h>

#include "hr_gettime.h"

/* Misc definitions. */
#define sdSIGNATURE 			0x41404342UL
#define sdHUNDRED_64_BIT		( 100ull )
#define sdBYTES_PER_MB			( 1024ull * 1024ull )
#define sdSECTORS_PER_MB		( sdBYTES_PER_MB / 512ull )
#define sdIOMAN_MEM_SIZE		4096
#define xSDCardInfo				( sd_mmc_cards[ 0 ] )
#define sdAligned( pvAddress )	( ( ( ( size_t ) ( pvAddress ) ) & ( sizeof( size_t ) - 1 ) ) == 0 )

#if( ffconfigSDIO_DRIVER_USES_INTERRUPT != 0 )

	/* Define a time-out for all DMA transactions in msec. */
	#ifndef sdMAX_TRANSFER_TIME
		#define sdMAX_TRANSFER_TIME			4000
	#endif

	/* Define all possible interrupts of interest. */
	#define sdHSMCI_INTERRUPT_FLAGS \
		HSMCI_IER_NOTBUSY | \
		HSMCI_IER_UNRE | \
		HSMCI_IER_OVRE | \
		HSMCI_IER_DTOE | \
		HSMCI_IER_DCRCE | \
		HSMCI_IER_TXBUFE | \
		HSMCI_IER_RXBUFF | \
		HSMCI_IER_XFRDONE

	#define sdMSMCI_USE_SEMAPHORE  1

#endif /* ffconfigSDIO_DRIVER_USES_INTERRUPT */

/*-----------------------------------------------------------*/

#if( ffconfigSDIO_DRIVER_USES_INTERRUPT != 0 )

	static TickType_t xDMARemainingTime;
	static TimeOut_t xDMATimeOut;
	static volatile uint32_t ulSDInterruptStatus;
	static volatile int iWaitForWriting;

	#if( sdMSMCI_USE_SEMAPHORE != 0 )
		static SemaphoreHandle_t xSDSemaphore = NULL;
	#else
		static TaskHandle_t xSDTaskHandle = NULL;
	#endif

#endif /* ffconfigSDIO_DRIVER_USES_INTERRUPT */

/*
 * Return pdFALSE if the SD card is not inserted.
 */
static BaseType_t prvSDDetect( void );

/*
 * Check if the card is present, and if so, print out some info on the card.
 */
static BaseType_t prvSDMMCInit( BaseType_t xDriveNumber );

/*-----------------------------------------------------------*/

/*
 * Mutex for partition.
 */
static SemaphoreHandle_t xPlusFATMutex = NULL;

/*
 * Remembers if the card is currently considered to be present.
 */
static BaseType_t xSDCardStatus = pdFALSE;

/*-----------------------------------------------------------*/

typedef struct {
	uint32_t ulStart;
	uint32_t ulSize;
} MemoryGroup_t;

#define ARRAY_SIZE(x) (int)(sizeof(x)/sizeof(x)[0])

static const MemoryGroup_t xMemories[] = {
	{ IRAM_ADDR, IRAM_SIZE },
	{ EBI_CS1_ADDR, 512ul * 1024ul },
	{ EBI_CS3_ADDR, 512ul * 1024ul },
};

static BaseType_t prvIsInternalRAM( uint8_t *pucBuffer )
{
BaseType_t xResult = pdFALSE, xIndex;
uint32_t ulAddress = ( uint32_t ) pucBuffer;

	for( xIndex = 0; xIndex < ARRAY_SIZE( xMemories ); xIndex++ )
	{
		if( ( ulAddress >= xMemories[ xIndex].ulStart ) && ( ulAddress < xMemories[ xIndex].ulStart + xMemories[ xIndex].ulSize ) )
		{
			xResult = pdTRUE;
			break;
		}
	}

	return xResult;
}
/*-----------------------------------------------------------*/

static int32_t prvFFRead( uint8_t *pucBuffer, uint32_t ulSectorNumber, uint32_t ulSectorCount, FF_Disk_t *pxDisk )
{
int32_t lReturnCode = FF_ERR_IOMAN_OUT_OF_BOUNDS_READ | FF_ERRFLAG, lResult = pdFALSE;

	if( ( pxDisk != NULL ) &&
		( xSDCardStatus == pdPASS ) &&
		( pxDisk->ulSignature == sdSIGNATURE ) &&
		( pxDisk->xStatus.bIsInitialised != pdFALSE ) &&
		( ulSectorNumber < pxDisk->ulNumberOfSectors ) &&
		( ( pxDisk->ulNumberOfSectors - ulSectorNumber ) >= ulSectorCount ) )
	{
		/* As the MCI driver is configured to use DMA, it must be tested that
		the buffer is located in internal SRAM ("IRAM") and if it is 4-byte aligned. */
		if( sdAligned( pucBuffer ) && prvIsInternalRAM( pucBuffer ) )
		{
			lResult = sd_physical_read( ulSectorNumber, pucBuffer, ulSectorCount );
		}
		else
		{
		uint32_t ulSector;
		uint8_t *pucDMABuffer = ffconfigMALLOC( 512ul );

			/* The buffer is NOT word-aligned, read to an aligned buffer and then
			copy the data to the user provided buffer. */
			if( pucDMABuffer != NULL )
			{
				for( ulSector = 0; ulSector < ulSectorCount; ulSector++ )
				{
					lResult = sd_physical_read( ulSectorNumber + ulSector, pucDMABuffer, 1 );
					if( lResult == pdFALSE )
					{
						break;
					}
					/* Copy to the user-provided buffer. */
					memcpy( pucBuffer + 512ul * ulSector, pucDMABuffer, 512ul );
				}
				ffconfigFREE( pucDMABuffer );
			}
			else
			{
				FF_PRINTF( "prvFFRead: malloc failed\n" );
				lResult = pdFALSE;
			}
		}
		
		if( lResult != pdFALSE )
		{
			lReturnCode = 0L;
		}
		else
		{
			/* Some error occurred. */
			FF_PRINTF( "prvFFRead: %lu: %ld\n", ulSectorNumber, lResult );
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
int32_t lReturnCode = FF_ERR_IOMAN_OUT_OF_BOUNDS_READ | FF_ERRFLAG, lResult = pdFALSE;

	if( ( pxDisk != NULL ) &&
		( xSDCardStatus == pdPASS ) &&
		( pxDisk->ulSignature == sdSIGNATURE ) &&
		( pxDisk->xStatus.bIsInitialised != pdFALSE ) &&
		( ulSectorNumber < pxDisk->ulNumberOfSectors ) &&
		( ( pxDisk->ulNumberOfSectors - ulSectorNumber ) >= ulSectorCount ) )
	{
		/* As the MCI driver is configured to use DMA, it must be tested that
		the buffer is located in internal SRAM ("IRAM") and if it is 4-byte aligned. */
		if( sdAligned( pucBuffer ) && prvIsInternalRAM( pucBuffer ) )
		{
			lResult = sd_physical_write( ulSectorNumber, pucBuffer, ulSectorCount );
		}
		else
		{
		uint32_t ulSector;
		uint8_t *pucDMABuffer = ffconfigMALLOC( 512ul );

			/* The buffer is NOT word-aligned, read to an aligned buffer and then
			copy the data to the user provided buffer. */
			if( pucDMABuffer != NULL )
			{
				for( ulSector = 0; ulSector < ulSectorCount; ulSector++ )
				{
					/* Copy from the user provided buffer to the temporary buffer. */
					memcpy( pucDMABuffer, pucBuffer + 512ul * ulSector, 512ul );
					lResult = sd_physical_write( ulSectorNumber + ulSector, pucDMABuffer, 1 );
					if( lResult == pdFALSE )
					{
						break;
					}
				}
				ffconfigFREE( pucDMABuffer );
			}
			else
			{
				FF_PRINTF( "prvFFWrite: malloc failed\n" );
				lResult = pdFALSE;
			}
		}

		if( lResult != pdFALSE )
		{
			/* No errors. */
			lReturnCode = 0L;
		}
		else
		{
			FF_PRINTF( "prvFFWrite: %lu: %ld\n", ulSectorNumber, lResult  );
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

/* Initialise the SDIO driver and mount an SD card */
FF_Disk_t *FF_SDDiskInit( const char *pcName )
{
FF_Error_t xFFError;
BaseType_t xPartitionNumber = 0;
FF_CreationParameters_t xParameters;
FF_Disk_t *pxDisk;

	#if( ffconfigSDIO_DRIVER_USES_INTERRUPT != 0 )
	{
		NVIC_SetPriority( HSMCI_IRQn, configHSMCI_INTERRUPT_PRIORITY );
		NVIC_EnableIRQ( HSMCI_IRQn );
		#if( sdMSMCI_USE_SEMAPHORE != 0 )
		{
			if( xSDSemaphore == NULL )
			{
				xSDSemaphore = xSemaphoreCreateBinary();
			}
		}
		#endif /* sdMSMCI_USE_SEMAPHORE */
	}
	#endif /* ffconfigSDIO_DRIVER_USES_INTERRUPT */

	xSDCardStatus = prvSDMMCInit( 0 );

	if( xSDCardStatus == pdPASS )
	{
		pxDisk = (FF_Disk_t *)ffconfigMALLOC( sizeof( *pxDisk ) );
		if( pxDisk != NULL )
		{
			/* Initialise the created disk structure. */
			memset( pxDisk, '\0', sizeof( *pxDisk ) );

			/* The Atmel MMC driver sets capacity as a number of KB.
			Divide by two to get the number of 512-byte sectors. */
			pxDisk->ulNumberOfSectors = xSDCardInfo.capacity << 1;

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
					}
				}	/* if( pxDisk->pxIOManager != NULL ) */
			}	/* if( xPlusFATMutex != NULL) */
		}	/* if( pxDisk != NULL ) */
		else
		{
			FF_PRINTF( "FF_SDDiskInit: Malloc failed\n" );
		}
	}	/* if( xSDCardStatus == pdPASS ) */
	else
	{
		FF_PRINTF( "FF_SDDiskInit: prvSDMMC_Init failed\n" );
		pxDisk = NULL;
	}

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
		FF_SDDiskShowPartition( pxDisk );
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

BaseType_t FF_SDDiskDetect( FF_Disk_t *pxDisk )
{
BaseType_t xIsPresent;
void *pvSemaphore;

	if( ( pxDisk != NULL ) && ( pxDisk->pxIOManager ) )
	{
		pvSemaphore = pxDisk->pxIOManager->pvSemaphore;
	}
	else
	{
		pvSemaphore = NULL;
	}

	/*_RB_ Can these NULL checks be moved inside the FF_nnnSemaphore() functions? */
	/*_HT_ I'm afraid not, both functions start with configASSERT( pxSemaphore ); */
	if( pvSemaphore != NULL )
	{
		FF_PendSemaphore( pvSemaphore );
	}

	xIsPresent = prvSDDetect();

	if( pvSemaphore != NULL )
	{
		FF_ReleaseSemaphore( pvSemaphore );
	}

	return xIsPresent;
}
/*-----------------------------------------------------------*/

static BaseType_t prvSDDetect( void )
{
static BaseType_t xWasPresent;
BaseType_t xIsPresent;
sd_mmc_err_t xSDPresence;

	if( xWasPresent == pdFALSE )
	{
		/* Try to initialize SD MMC stack */
		sd_mmc_init();
		xSDPresence = sd_mmc_check( 0 );
		if( ( xSDPresence == SD_MMC_OK ) || ( xSDPresence == SD_MMC_INIT_ONGOING ) )
		{
			xIsPresent = pdTRUE;
		}
		else
		{
			xIsPresent = pdFALSE;
		}
	}
	else
	{
		/* See if the card is still present. */
		xSDPresence = sd_mmc_check_status(0);
		if( xSDPresence == SD_MMC_OK )
		{
			xIsPresent = pdTRUE;
		}
		else
		{
			xIsPresent = pdFALSE;
		}
	}
	xWasPresent = xIsPresent;

	return xIsPresent;
}
/*-----------------------------------------------------------*/

static BaseType_t prvSDMMCInit( BaseType_t xDriveNumber )
{
BaseType_t xReturn;

	/* 'xDriveNumber' not yet in use. */
	( void ) xDriveNumber;

	/* Check if the SD card is plugged in the slot */
	if( prvSDDetect() == pdFALSE )
	{
		FF_PRINTF( "No SD card detected\n" );
		xReturn = pdFAIL;
	}
	else
	{
		FF_PRINTF( "HAL_SD_Init: type: %s Capacity: %lu MB\n",
			xSDCardInfo.type & CARD_TYPE_HC ? "SDHC" : "SD",
			( xSDCardInfo.capacity << 1 ) / 2048 );

		xReturn = pdPASS;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/
#if( ffconfigSDIO_DRIVER_USES_INTERRUPT != 0 )
	void HSMCI_Handler( void )
	{
	uint32_t ulSR;
	BaseType_t xSwitchRequired = pdFALSE;
	
		ulSR = HSMCI->HSMCI_SR & HSMCI->HSMCI_IMR;
		HSMCI->HSMCI_IDR = ulSR;
		ulSDInterruptStatus |= ulSR;
		#if( sdMSMCI_USE_SEMAPHORE != 0 )
		{
			if( xSDSemaphore != NULL )
			{
				xSemaphoreGiveFromISR( xSDSemaphore, &xSwitchRequired );
			}
		}
		#else
		{
			if( xSDTaskHandle != NULL )
			{
				vTaskNotifyGiveFromISR( xSDTaskHandle, ( BaseType_t * ) &xSwitchRequired );
			}
		}
		#endif
		if( xSwitchRequired != pdFALSE )
		{
			portEND_SWITCHING_ISR( xSwitchRequired );
		}
	}
#endif /* ffconfigSDIO_DRIVER_USES_INTERRUPT */
/*-----------------------------------------------------------*/

#if( ffconfigSDIO_DRIVER_USES_INTERRUPT != 0 )
	void vMCIEventSetupFunction( int iForWriting )
	{
		iWaitForWriting = iForWriting != 0;
	
		#if( sdMSMCI_USE_SEMAPHORE == 0 )
		{
			xSDTaskHandle = xTaskGetCurrentTaskHandle();
		}
		#endif
		ulSDInterruptStatus = 0;
		HSMCI->HSMCI_IER = sdHSMCI_INTERRUPT_FLAGS;
	
		/* A DMA transfer to or from the SD-card is about to start.
		Reset the timers that will be used in prvEventWaitFunction() */
		xDMARemainingTime = pdMS_TO_TICKS( sdMAX_TRANSFER_TIME );
		vTaskSetTimeOutState( &xDMATimeOut );
	}
#endif /* ffconfigSDIO_DRIVER_USES_INTERRUPT */
/*-----------------------------------------------------------*/

#if( ffconfigSDIO_DRIVER_USES_INTERRUPT != 0 )
	void vMCIEventReadyFunction()
	{
		#if( sdMSMCI_USE_SEMAPHORE == 0 )
		{
			xSDTaskHandle = NULL;
		}
		#endif
		ulSDInterruptStatus = 0;
		HSMCI->HSMCI_IDR = sdHSMCI_INTERRUPT_FLAGS;
	}
#endif /* ffconfigSDIO_DRIVER_USES_INTERRUPT */
/*-----------------------------------------------------------*/

#if( ffconfigSDIO_DRIVER_USES_INTERRUPT != 0 )
	uint32_t ulMCIEventWaitFunction( uint32_t ulMask )
	{
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
			FF_PRINTF( "ulMCIEventWaitFunction: %s timed out. SR = %08x\n",
				iWaitForWriting ? "Write" : "Read", ulSDInterruptStatus );
		}
		else
		{
			/* The timeout has not been reached yet, block on the semaphore. */
			#if( sdMSMCI_USE_SEMAPHORE != 0 )
			{
				if( ( ulSDInterruptStatus & ulMask ) == 0ul )
				{
					xSemaphoreTake( xSDSemaphore, xDMARemainingTime );
				}
			}
			#else
			{
				if( ( ulSDInterruptStatus & ulMask ) == 0ul )
				{
					ulTaskNotifyTake( pdFALSE, xDMARemainingTime );
				}
			}
			#endif
			if( xTaskCheckForTimeOut( &xDMATimeOut, &xDMARemainingTime ) != pdFALSE )
			{
				FF_PRINTF( "ulMCIEventWaitFunction: %s timed out. SR = %08x\n",
					iWaitForWriting ? "Write" : "Read", ulSDInterruptStatus );
			}
		}

		return ulSDInterruptStatus;
	}
#endif /* ffconfigSDIO_DRIVER_USES_INTERRUPT */
/*-----------------------------------------------------------*/

