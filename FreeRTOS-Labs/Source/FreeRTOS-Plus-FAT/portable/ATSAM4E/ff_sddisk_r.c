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
#include <sd_mmc.h>

/* Misc definitions. */
#define sdSIGNATURE 			0x41404342UL
#define sdHUNDRED_64_BIT		( 100ull )
#define sdBYTES_PER_MB			( 1024ull * 1024ull )
#define sdSECTORS_PER_MB		( sdBYTES_PER_MB / 512ull )
#define sdIOMAN_MEM_SIZE		4096
#define xSDCardInfo				( sd_mmc_cards[ 0 ] )

/*-----------------------------------------------------------*/

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

static int32_t prvFFRead( uint8_t *pucBuffer, uint32_t ulSectorNumber, uint32_t ulSectorCount, FF_Disk_t *pxDisk )
{
int32_t lReturnCode = FF_ERR_IOMAN_OUT_OF_BOUNDS_READ | FF_ERRFLAG, lResult;

	if( ( pxDisk != NULL ) &&
		( xSDCardStatus == pdPASS ) &&
		( pxDisk->ulSignature == sdSIGNATURE ) &&
		( pxDisk->xStatus.bIsInitialised != pdFALSE ) &&
		( ulSectorNumber < pxDisk->ulNumberOfSectors ) &&
		( ( pxDisk->ulNumberOfSectors - ulSectorNumber ) >= ulSectorCount ) )
	{
		lResult = sd_physical_read( ulSectorNumber, pucBuffer, ulSectorCount);

		if( lResult != pdFALSE )
		{
			lReturnCode = 0L;
		}
		else
		{
			/* Some error occurred. */
			FF_PRINTF( "prvFFRead: %lu: %lu\n", ulSectorNumber, lResult );
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
BaseType_t xResult;

	if( ( pxDisk != NULL ) &&
		( xSDCardStatus == pdPASS ) &&
		( pxDisk->ulSignature == sdSIGNATURE ) &&
		( pxDisk->xStatus.bIsInitialised != pdFALSE ) &&
		( ulSectorNumber < pxDisk->ulNumberOfSectors ) &&
		( ( pxDisk->ulNumberOfSectors - ulSectorNumber ) >= ulSectorCount ) )
	{
		xResult = sd_physical_write( ulSectorNumber, pucBuffer, ulSectorCount );

		if( xResult != pdFALSE )
		{
			/* No errors. */
			lReturnCode = 0L;
		}
		else
		{
			FF_PRINTF( "prvFFWrite: %lu: %lu\n", ulSectorNumber, xResult  );
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

	xSDCardStatus = prvSDMMCInit( 0 );

	if( xSDCardStatus != pdPASS )
	{
		FF_PRINTF( "FF_SDDiskInit: prvSDMMCInit failed\n" );
		pxDisk = NULL;
	}
	else
	{
		pxDisk = ( FF_Disk_t * )pvPortMalloc( sizeof( *pxDisk ) );
		if( pxDisk == NULL )
		{
			FF_PRINTF( "FF_SDDiskInit: Malloc failed\n" );
		}
		else
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
						FF_SDDiskShowPartition( pxDisk );
					}
				}	/* if( pxDisk->pxIOManager != NULL ) */
			}	/* if( xPlusFATMutex != NULL) */
		}	/* if( pxDisk != NULL ) */
	}	/* if( xSDCardStatus == pdPASS ) */

	return pxDisk;
}
/*-----------------------------------------------------------*/

BaseType_t FF_SDDiskFormat( FF_Disk_t *pxDisk, BaseType_t aPart )
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
		xError = FF_Format( pxDisk, aPart, pdFALSE, pdFALSE);

		if( FF_isERR( xError ) )
		{
			FF_PRINTF( "FF_SDDiskFormat: %s\n", (const char*)FF_GetErrMessage( xError ) );
		}
		else
		{
			FF_PRINTF( "FF_SDDiskFormat: OK, now remounting\n" );
			pxDisk->xStatus.bPartitionNumber = aPart;
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

BaseType_t FF_SDDiskDetect( FF_Disk_t *pxDisk )
{
BaseType_t xIsPresent;
void *pvSemaphore;

	if( ( pxDisk != NULL ) &&
		( pxDisk->pxIOManager ) )
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
