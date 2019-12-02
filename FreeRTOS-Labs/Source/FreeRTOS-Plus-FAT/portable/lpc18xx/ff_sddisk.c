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

/* LPC18xx includes. */
#include "chip.h"
#include "board.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"
#include "portmacro.h"

/* FreeRTOS+FAT includes. */
#include "ff_sddisk.h"
#include "ff_sys.h"

#include "hr_gettime.h"

/* Misc definitions. */
#define sdSIGNATURE 			0x41404342UL
#define sdHUNDRED_64_BIT		( 100ull )
#define sdBYTES_PER_MB			( 1024ull * 1024ull )
#define sdSECTORS_PER_MB		( sdBYTES_PER_MB / 512ull )
#define sdIOMAN_MEM_SIZE		4096
#define xSDCardInfo				( sd_mmc_cards[ 0 ] )
#define sdAligned( pvAddress )	( ( ( ( size_t ) ( pvAddress ) ) & ( sizeof( size_t ) - 1 ) ) == 0 )



/*-----------------------------------------------------------*/

/*_RB_ Functions require comment blocks. */
static void prvSDMMCSetupWakeup( void *pvInfo );
static uint32_t prvSDMMCWait( void );
static void prvSDMMCDelay_ms( uint32_t time );
static void prvInitialiseCardInfo( void );
static int32_t prvSDMMC_Init( void );
static int32_t prvFFRead( uint8_t *pucBuffer, uint32_t ulSectorNumber, uint32_t ulSectorCount, FF_Disk_t *pxDisk );
static int32_t prvFFWrite( uint8_t *pucBuffer, uint32_t ulSectorNumber, uint32_t ulSectorCount, FF_Disk_t *pxDisk );


/*-----------------------------------------------------------*/

/*_RB_ Variables require a comment block where appropriate. */
static int32_t lSDDetected = 0;
static mci_card_struct xCardInfo;
static volatile int32_t lSDIOWaitExit;
static BaseType_t xSDCardStatus;
static SemaphoreHandle_t xSDCardSemaphore;
static SemaphoreHandle_t xPlusFATMutex;

/*-----------------------------------------------------------*/

#warning Update to make read and write functions static and make use of the FF_Disk_t type.

static int32_t prvFFRead( uint8_t *pucBuffer, uint32_t ulSectorNumber, uint32_t ulSectorCount, FF_Disk_t *pxDisk )
{
int32_t iReturn;

	/*_RB_ Many of the comments in this file apply to other functions in the file. */

	if( ( pxDisk != NULL ) &&
		( xSDCardStatus == pdPASS ) &&
		( pxDisk->ulSignature == sdSIGNATURE ) &&
		( pxDisk->xStatus.bIsInitialised != pdFALSE ) &&
		( ulSectorNumber < pxDisk->ulNumberOfSectors ) &&
		( ( pxDisk->ulNumberOfSectors - ulSectorNumber ) >= ulSectorCount ) )
	{

		iReturn = Chip_SDMMC_ReadBlocks( LPC_SDMMC, pucBuffer, ulSectorNumber, ulSectorCount );

		/*_RB_ I'm guessing 512 is a sector size, but that needs to be clear.
		Is it defined in a header somewhere?  If so we can do a search and
		replace in files on it as it seems to be used everywhere. */
		if( iReturn == ( ulSectorCount * 512 ) ) /*_RB_ Signed/unsigned mismatch (twice!) */
		{
			iReturn = FF_ERR_NONE;
		}
		else
		{
			/*_RB_ Signed number used to return bitmap (again below). */
			iReturn = ( FF_ERR_IOMAN_OUT_OF_BOUNDS_READ | FF_ERRFLAG );
		}
	}
	else
	{
		memset( ( void * ) pucBuffer, '\0', ulSectorCount * 512 );

		if( pxDisk->xStatus.bIsInitialised != 0 )
		{
			FF_PRINTF( "prvFFRead: warning: %lu + %lu > %lu\n", ulSectorNumber, ulSectorCount, pxDisk->ulNumberOfSectors );
		}

		iReturn = ( FF_ERR_IOMAN_OUT_OF_BOUNDS_READ | FF_ERRFLAG );
	}

	return iReturn;
}
/*-----------------------------------------------------------*/

static int32_t prvFFWrite( uint8_t *pucBuffer, uint32_t ulSectorNumber, uint32_t ulSectorCount, FF_Disk_t *pxDisk )
{
int32_t iReturn;

	if( ( pxDisk != NULL ) &&
		( xSDCardStatus == pdPASS ) &&
		( pxDisk->ulSignature == sdSIGNATURE ) &&
		( pxDisk->xStatus.bIsInitialised != pdFALSE ) &&
		( ulSectorNumber < pxDisk->ulNumberOfSectors ) &&
		( ( pxDisk->ulNumberOfSectors - ulSectorNumber ) >= ulSectorCount ) )
	{
		iReturn = Chip_SDMMC_WriteBlocks( LPC_SDMMC, pucBuffer, ulSectorNumber, ulSectorCount );

		if( iReturn == ( ulSectorCount * 512 ) ) /*_RB_ Signed/unsigned mismatch (twice!) */
		{
			iReturn = 0;
		}
		else
		{
			iReturn = ( FF_ERR_IOMAN_OUT_OF_BOUNDS_WRITE | FF_ERRFLAG );
		}
	}
	else
	{
		memset( ( void * ) pucBuffer, '\0', ulSectorCount * 512 );
		if( pxDisk->xStatus.bIsInitialised )
		{
			FF_PRINTF( "prvFFWrite: warning: %lu + %lu > %lu\n", ulSectorNumber, ulSectorCount, pxDisk->ulNumberOfSectors );
		}

		iReturn = ( FF_ERR_IOMAN_OUT_OF_BOUNDS_WRITE | FF_ERRFLAG );
	}

	return iReturn;
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
FF_Disk_t * pxDisk;

	xSDCardStatus = prvSDMMC_Init();
	if( xSDCardStatus == pdPASS )
	{
		pxDisk = ( FF_Disk_t * ) pvPortMalloc( sizeof( *pxDisk ) );

		if( pxDisk != NULL )
		{

			/* Initialise the created disk structure. */
			memset( pxDisk, '\0', sizeof( *pxDisk ) );


			if( xPlusFATMutex == NULL)
			{
				xPlusFATMutex = xSemaphoreCreateRecursiveMutex();
			}
			pxDisk->ulNumberOfSectors = xCardInfo.card_info.blocknr;
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
					FF_PRINTF( "FF_SDDiskInit: FF_CreateIOManger: %s\n", ( const char * ) FF_GetErrMessage( xFFError ) );
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

/* Get a pointer to IOMAN, which can be used for all FreeRTOS+FAT functions */
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

void SDIO_IRQHandler( void )
{
BaseType_t xHigherPriorityTaskWoken = pdFALSE;

	/* All SD based register handling is done in the callback function. The SDIO
	interrupt is not enabled as part of this driver and needs to be
	enabled/disabled in the callbacks or application as needed. This is to allow
	flexibility with IRQ handling for applications and RTOSes. */

	/* Set wait exit flag to tell wait function we are ready. In an RTOS, this
	would trigger wakeup of a thread waiting for the IRQ. */
	NVIC_DisableIRQ( SDIO_IRQn );
	xSemaphoreGiveFromISR( xSDCardSemaphore, &xHigherPriorityTaskWoken );
	lSDIOWaitExit = 1;
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

/* Sets up the SD event driven wakeup */
static void prvSDMMCSetupWakeup( void *pvInfo )
{
uint32_t *ulWaitStatus = ( uint32_t * ) pvInfo;

	/* Wait for IRQ - for an RTOS, you would pend on an event here with a IRQ
	based wakeup. */
	/*_RB_ Don't understand why this is spinning on a block time of 0.  Is it
	really meant to be != pdFALSE? */
	while( xSemaphoreTake( xSDCardSemaphore, 0 ) != pdFALSE )
	{
	}

	NVIC_ClearPendingIRQ( SDIO_IRQn );
	lSDIOWaitExit = 0;
	Chip_SDIF_SetIntMask( LPC_SDMMC, *ulWaitStatus );
	NVIC_EnableIRQ( SDIO_IRQn );
}
/*-----------------------------------------------------------*/

static uint32_t prvSDMMCWait( void )
{
uint32_t ulStatus;

	/*_RB_ 2000 needs to be defined and use pdMS_TO_TICKS so the delay period
	remains constant no matter how the end user sets configTICK_RATE_MS. */
	xSemaphoreTake( xSDCardSemaphore, 2000 );

	ulStatus = Chip_SDIF_GetIntStatus( LPC_SDMMC );
	if( ( ( ulStatus & MCI_INT_CMD_DONE ) == 0 ) || ( lSDIOWaitExit == 0 ) )
	{
		FF_PRINTF( "Wait SD: int32_t %ld ulStatus 0x%02lX\n", lSDIOWaitExit, ulStatus );
	}

	return ulStatus;
}
/*-----------------------------------------------------------*/

static void prvSDMMCDelay_ms( uint32_t ulTime )
{
	/* In an RTOS, the thread would sleep allowing other threads to run.
	For standalone operation, just spin on a timer */
	vTaskDelay( pdMS_TO_TICKS( ulTime ) );
}
/*-----------------------------------------------------------*/

static int32_t prvSDMMC_Init( void )
{
int32_t lSDCardStatus;

	if( xSDCardSemaphore == NULL )
	{
		xSDCardSemaphore = xSemaphoreCreateBinary();
		configASSERT( xSDCardSemaphore );
		xSemaphoreGive( xSDCardSemaphore );
	}

	prvInitialiseCardInfo();
	NVIC_SetPriority( SDIO_IRQn, configSD_INTERRUPT_PRIORITY );

	/*_RB_ Board_SDMMC_Init() is library specific code that is also specific to
	the target development board.The SDMMC peripheral should be initialised from
	the application code before this code is called. */
	Board_SDMMC_Init();
	Chip_SDIF_Init( LPC_SDMMC );
	lSDDetected = !Chip_SDIF_CardNDetect( LPC_SDMMC );

	Chip_SDIF_PowerOn( LPC_SDMMC );
	lSDCardStatus = Chip_SDMMC_Acquire( LPC_SDMMC, &xCardInfo );
	FF_PRINTF( "Acquire: %ld\n", lSDCardStatus );

	return lSDCardStatus;
}
/*-----------------------------------------------------------*/

static void prvInitialiseCardInfo( void )
{
	memset( &xCardInfo, 0, sizeof( xCardInfo ) );
	xCardInfo.card_info.evsetup_cb = prvSDMMCSetupWakeup;
	xCardInfo.card_info.waitfunc_cb = prvSDMMCWait;
	xCardInfo.card_info.msdelay_func = prvSDMMCDelay_ms;
}
