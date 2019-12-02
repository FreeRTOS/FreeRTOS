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

/* Xilinx library includes. */
#include "xparameters.h"
#include "xil_types.h"
#include "xsdps.h"		/* SD device driver */
#include "xsdps_info.h"	/* SD info */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"
#include "portmacro.h"

/* FreeRTOS+FAT includes. */
#include "ff_headers.h"
#include "ff_sddisk.h"
#include "ff_sys.h"

#if( ffconfigSDIO_DRIVER_USES_INTERRUPT != 0 )
	#include "xil_exception.h"
	#include "xscugic_hw.h"
#endif /* ffconfigSDIO_DRIVER_USES_INTERRUPT */

#include "uncached_memory.h"

#define sdSIGNATURE 0x41404342

#ifndef ARRAY_SIZE
	#define	ARRAY_SIZE(x)	(int) (sizeof(x)/sizeof(x)[0])
#endif

#define STA_NOINIT		0x01	/* Drive not initialized */
#define STA_NODISK		0x02	/* No medium in the drive */
#define STA_PROTECT		0x04	/* Write protected */

#define SD_DEVICE_ID					XPAR_XSDPS_0_DEVICE_ID
#define HIGH_SPEED_SUPPORT				0x01
#define WIDTH_4_BIT_SUPPORT				0x4
#define SD_CLK_12_MHZ					12000000
#define SD_CLK_25_MHZ					25000000
#define SD_CLK_26_MHZ					26000000
#define SD_CLK_52_MHZ					52000000
#define EXT_CSD_DEVICE_TYPE_BYTE		196
#define EXT_CSD_4_BIT_WIDTH_BYTE		183
#define EXT_CSD_HIGH_SPEED_BYTE			185
#define EXT_CSD_DEVICE_TYPE_HIGH_SPEED	0x3

#define HUNDRED_64_BIT			100ULL
#define BYTES_PER_MB			( 1024ull * 1024ull )
#define SECTORS_PER_MB			( BYTES_PER_MB / 512ull )

#define XSDPS_INTR_NORMAL_ENABLE ( XSDPS_INTR_CC_MASK | XSDPS_INTR_TC_MASK | \
	XSDPS_INTR_DMA_MASK | XSDPS_INTR_CARD_INSRT_MASK | XSDPS_INTR_CARD_REM_MASK | \
	XSDPS_INTR_ERR_MASK )

/* Two defines used to set or clear the interrupt */
#define INTC_BASE_ADDR		XPAR_SCUGIC_CPU_BASEADDR
#define INTC_DIST_BASE_ADDR	XPAR_SCUGIC_DIST_BASEADDR

/* Interupt numbers for SDIO units 0 and 1: */
#define SCUGIC_SDIO_0_INTR	0x38
#define SCUGIC_SDIO_1_INTR	0x4F

/* Define a timeout on data transfers for SDIO: */
#define sdWAIT_INT_TIME_OUT_MS		5000UL

/* Define a short timeout, used during card-detection only (CMD1): */
#define sdQUICK_WAIT_INT_TIME_OUT_MS	1000UL

/* XSdPs xSDCardInstance; */
static XSdPs *pxSDCardInstance;

static int sd_disk_status = STA_NOINIT;	/* Disk status */
const int drive_nr = 0;
static SemaphoreHandle_t xPlusFATMutex;
#if( ffconfigSDIO_DRIVER_USES_INTERRUPT != 0 )
	/* Create a semaphore for each of the two memory-card slots. */
	static SemaphoreHandle_t xSDSemaphores[ 2 ];
#endif

static int vSDMMC_Init( int iDriveNumber );
static int vSDMMC_Status( int iDriveNumber );

#if( ffconfigSDIO_DRIVER_USES_INTERRUPT != 0 )
	static void vInstallInterrupt( void );
#endif

struct xCACHE_MEMORY_INFO
{
	/* Reserve 'uncached' memory for caching sectors, will be passed to the +FAT library. */
	uint8_t pucCacheMemory[ 0x10000 ];
	/* Reserve 'uncached' memory for i/o to the SD-card. */
	uint8_t pucHelpMemory[ 0x40000 ];
	XSdPs xSDCardInstance;
};

struct xCACHE_STATS
{
	uint32_t xMemcpyReadCount;
	uint32_t xMemcpyWriteCount;
	uint32_t xPassReadCount;
	uint32_t xPassWriteCount;
	uint32_t xFailReadCount;
	uint32_t xFailWriteCount;
};

struct xCACHE_STATS xCacheStats;
struct xCACHE_MEMORY_INFO *pxCacheMem = NULL;

static const uint8_t *prvStoreSDCardData( const uint8_t *pucBuffer, uint32_t ulByteCount );
static uint8_t *prvReadSDCardData( uint8_t *pucBuffer, uint32_t ulByteCount );

#if( ffconfigSDIO_DRIVER_USES_INTERRUPT != 0 )
	void XSdPs_IntrHandler(void *XSdPsPtr);
#endif /* ffconfigSDIO_DRIVER_USES_INTERRUPT */

static int32_t prvFFRead( uint8_t *pucBuffer, uint32_t ulSectorNumber, uint32_t ulSectorCount, FF_Disk_t *pxDisk )
{
int32_t lReturnCode;
int iResult;
uint8_t *pucReadBuffer;

	if( ( pxDisk != NULL ) &&		/*_RB_ Could this be changed to an assert? */
		( pxDisk->ulSignature == sdSIGNATURE ) &&
		( pxDisk->xStatus.bIsInitialised != pdFALSE ) &&
		( ulSectorNumber < pxDisk->ulNumberOfSectors ) &&
		( pxDisk->ulNumberOfSectors - ulSectorNumber ) >= ulSectorCount )
	{
		iResult = vSDMMC_Status( drive_nr );
		if( ( iResult & STA_NODISK ) != 0 )
		{
			lReturnCode = FF_ERR_DRIVER_NOMEDIUM | FF_ERRFLAG;
			FF_PRINTF( "prvFFRead: NOMEDIUM\n" );
		}
		else if( ( iResult & STA_NOINIT ) != 0 )
		{
			lReturnCode = FF_ERR_IOMAN_OUT_OF_BOUNDS_READ | FF_ERRFLAG;
			FF_PRINTF( "prvFFRead: NOINIT\n" );
		}
		else if( ulSectorCount == 0ul )
		{
			lReturnCode = 0;
		}
		else
		{
			/* Convert LBA to byte address if needed */
			if( pxSDCardInstance->HCS == 0 )
			{
				ulSectorNumber *= XSDPS_BLK_SIZE_512_MASK;
			}

			pucReadBuffer = prvReadSDCardData( pucBuffer, 512UL * ulSectorCount );

			if( ucIsCachedMemory( pucReadBuffer ) != pdFALSE )
			{
				xCacheStats.xFailReadCount++;
			}

			iResult  = XSdPs_ReadPolled( pxSDCardInstance, ulSectorNumber, ulSectorCount, pucReadBuffer );
			if( pucBuffer != pucReadBuffer )
			{
				xCacheStats.xMemcpyReadCount++;
				memcpy( pucBuffer, pucReadBuffer, 512 * ulSectorCount );
			}
			else
			{
				xCacheStats.xPassReadCount++;
			}
			if( iResult == XST_SUCCESS )
			{
				lReturnCode = 0l;
			}
			else
			{
				lReturnCode = FF_ERR_IOMAN_OUT_OF_BOUNDS_READ | FF_ERRFLAG;
			}
		}
	}
	else
	{
		memset( ( void *) pucBuffer, '\0', ulSectorCount * 512 );

		if( pxDisk->xStatus.bIsInitialised != pdFALSE )
		{
			FF_PRINTF( "prvFFRead: warning: %lu + %lu > %lu\n", ulSectorNumber, ulSectorCount, pxDisk->ulNumberOfSectors );
		}

		lReturnCode = FF_ERR_IOMAN_OUT_OF_BOUNDS_READ | FF_ERRFLAG;
	}

	return lReturnCode;
}
/*-----------------------------------------------------------*/

static int32_t prvFFWrite( uint8_t *pucBuffer, uint32_t ulSectorNumber, uint32_t ulSectorCount, FF_Disk_t *pxDisk )
{
int32_t lReturnCode;

	if( ( pxDisk != NULL ) &&
		( pxDisk->ulSignature == sdSIGNATURE ) &&
		( pxDisk->xStatus.bIsInitialised != pdFALSE ) &&
		( ulSectorNumber < pxDisk->ulNumberOfSectors ) &&
		( ( pxDisk->ulNumberOfSectors - ulSectorNumber ) >= ulSectorCount ) )
	{
		int iResult;
		iResult = vSDMMC_Status(drive_nr);

		if( ( iResult & STA_NODISK ) != 0 )
		{
			lReturnCode = FF_ERR_DRIVER_NOMEDIUM | FF_ERRFLAG;
			FF_PRINTF( "prvFFWrite: NOMEDIUM\n" );
		}
		else if( ( iResult & STA_NOINIT ) != 0 )
		{
			lReturnCode = FF_ERR_IOMAN_OUT_OF_BOUNDS_WRITE | FF_ERRFLAG;
			FF_PRINTF( "prvFFWrite: NOINIT\n" );
		}
		else
		{
			if( ulSectorCount == 0ul )
			{
				lReturnCode = 0l;
			}
			else
			{
				/* Convert LBA to byte address if needed */
				if (!(pxSDCardInstance->HCS)) ulSectorNumber *= XSDPS_BLK_SIZE_512_MASK;

				pucBuffer = ( uint8_t * )prvStoreSDCardData( pucBuffer, 512UL * ulSectorCount );

				if( ucIsCachedMemory( pucBuffer ) != pdFALSE )
				{
					xCacheStats.xFailWriteCount++;
				}

				iResult = XSdPs_WritePolled( pxSDCardInstance, ulSectorNumber, ulSectorCount, pucBuffer );

				if( iResult == XST_SUCCESS )
				{
					lReturnCode = 0;
				}
				else
				{
					FF_PRINTF( "prvFFWrite[%d]: at 0x%X count %ld : %d\n",
						(int)drive_nr, (unsigned)ulSectorNumber, ulSectorCount, iResult );
					lReturnCode = FF_ERR_IOMAN_OUT_OF_BOUNDS_WRITE | FF_ERRFLAG;
				}
			}
		}
	}
	else
	{
		lReturnCode = FF_ERR_IOMAN_OUT_OF_BOUNDS_WRITE | FF_ERRFLAG;
		if( pxDisk->xStatus.bIsInitialised )
		{
			FF_PRINTF( "prvFFWrite::read: warning: %lu + %lu > %lu\n",
				ulSectorNumber, ulSectorCount, pxDisk->ulNumberOfSectors );
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

static const uint8_t *prvStoreSDCardData( const uint8_t *pucBuffer, uint32_t ulByteCount )
{
const uint8_t *pucReturn;

	if( ( ucIsCachedMemory( pucBuffer ) != pdFALSE ) && ( ulByteCount <= sizeof( pxCacheMem->pucHelpMemory ) ) )
	{
		memcpy( pxCacheMem->pucHelpMemory, pucBuffer, ulByteCount );
		pucReturn = pxCacheMem->pucHelpMemory;
		xCacheStats.xMemcpyWriteCount++;
	}
	else
	{
		pucReturn = pucBuffer;
		xCacheStats.xPassWriteCount++;
	}

	return pucReturn;
}
/*-----------------------------------------------------------*/

static uint8_t *prvReadSDCardData( uint8_t *pucBuffer, uint32_t ulByteCount )
{
uint8_t *pucReturn;

	if( ( ucIsCachedMemory( pucBuffer ) != pdFALSE ) && ( ulByteCount <= sizeof( pxCacheMem->pucHelpMemory ) ) )
	{
		pucReturn = pxCacheMem->pucHelpMemory;
	}
	else
	{
		pucReturn = pucBuffer;
	}

	return pucReturn;
}
/*-----------------------------------------------------------*/

static struct xCACHE_MEMORY_INFO *pucGetSDIOCacheMemory( )
{
	if( pxCacheMem == NULL )
	{
		pxCacheMem = ( struct xCACHE_MEMORY_INFO * ) pucGetUncachedMemory( sizeof( *pxCacheMem ) );
		memset( pxCacheMem, '\0', sizeof( *pxCacheMem ) );
	}
	return pxCacheMem;
}
/*-----------------------------------------------------------*/

/* Initialise the SDIO driver and mount an SD card */
FF_Disk_t *FF_SDDiskInit( const char *pcName )
{
FF_Error_t xFFError;
BaseType_t xPartitionNumber = 0;
FF_CreationParameters_t xParameters;
FF_Disk_t * pxDisk;
#if( ffconfigSDIO_DRIVER_USES_INTERRUPT != 0 )
	int iIndex;
#endif

	pucGetSDIOCacheMemory();

	pxDisk = (FF_Disk_t *)pvPortMalloc( sizeof( *pxDisk ) );
	if( pxDisk == NULL )
	{
		FF_PRINTF( "FF_SDDiskInit: Malloc failed\n" );
	}
	else if( pxCacheMem == NULL )
	{
		FF_PRINTF( "FF_SDDiskInit: Cached memory failed\n" );
	}
	else
	{
		pxSDCardInstance = &( pxCacheMem->xSDCardInstance );

		#if( ffconfigSDIO_DRIVER_USES_INTERRUPT != 0 )
		{
			for( iIndex = 0; iIndex < ARRAY_SIZE( xSDSemaphores ); iIndex++ )
			{
				if( xSDSemaphores[ iIndex ] == NULL )
				{
					xSDSemaphores[ iIndex ] = xSemaphoreCreateBinary();
					configASSERT( xSDSemaphores[ iIndex ] != NULL );
				}
			}
		}
		#endif

		vSDMMC_Init( 0 );

		/* Initialise the created disk structure. */
		memset( pxDisk, '\0', sizeof( *pxDisk ) );

		pxDisk->ulNumberOfSectors = myCSD.sd_last_block_address + 1;

		if( xPlusFATMutex == NULL )
		{
			xPlusFATMutex = xSemaphoreCreateRecursiveMutex();
		}
		pxDisk->ulSignature = sdSIGNATURE;

		if( xPlusFATMutex != NULL)
		{
			memset( &xParameters, '\0', sizeof( xParameters ) );
			xParameters.pucCacheMemory = pxCacheMem->pucCacheMemory;
			xParameters.ulMemorySize = sizeof( pxCacheMem->pucCacheMemory );
			xParameters.ulSectorSize = 512;
			xParameters.fnWriteBlocks = prvFFWrite;
			xParameters.fnReadBlocks = prvFFRead;
			xParameters.pxDisk = pxDisk;

			/* prvFFRead()/prvFFWrite() are not re-entrant and must be protected with
			the use of a semaphore. */
			xParameters.xBlockDeviceIsReentrant = pdFALSE;

			/* The semaphore will be used to protect critical sections in the +FAT driver,
			and also to avoid concurrent calls to prvFFRead()/prvFFWrite() from different tasks. */
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
			}
		}
	}

	return pxDisk;
}
/*-----------------------------------------------------------*/

BaseType_t FF_SDDiskFormat( FF_Disk_t *pxDisk, BaseType_t aPart )
{
FF_Error_t xError;
BaseType_t xReturn = 0;

	FF_SDDiskUnmount( pxDisk );
	{
		/* Format the drive */
		xError = FF_Format( pxDisk, aPart, pdFALSE, pdFALSE);  // Try FAT32 with large clusters
		if( FF_isERR( xError ) )
		{
			FF_PRINTF( "FF_SDDiskFormat: %s\n", (const char*)FF_GetErrMessage( xError ) );
			return 0;
		}
		else
		{
			FF_PRINTF( "FF_SDDiskFormat: OK, now remounting\n" );
			pxDisk->xStatus.bPartitionNumber = aPart;
			xError = FF_SDDiskMount( pxDisk );
			FF_PRINTF( "FF_SDDiskFormat: rc %08x\n", ( unsigned )xError );
			if( FF_isERR( xError ) == pdFALSE )
			{
				xReturn = 1;
				FF_SDDiskShowPartition( pxDisk );
			}
		}
	}
	return xReturn;
}
/*-----------------------------------------------------------*/

/* Unmount the volume */
BaseType_t FF_SDDiskUnmount( FF_Disk_t *pxDisk )
{
FF_Error_t xFFError;
BaseType_t xReturn = 1;

	if( ( pxDisk != NULL ) && ( pxDisk->xStatus.bIsMounted != pdFALSE ) )
	{
		pxDisk->xStatus.bIsMounted = pdFALSE;
		xFFError = FF_Unmount( pxDisk );
		FF_PRINTF( "FF_SDDiskUnmount: rc %08x\n", ( unsigned )xFFError );
		if( FF_isERR( xFFError ) )
		{
			xReturn = 0;
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
int iStatus = vSDMMC_Init( 0 ); /* Hard coded index. */

	/*_RB_ parameter not used. */
	( void ) pxDisk;

	FF_PRINTF( "FF_SDDiskReinit: rc %08x\n", ( unsigned )iStatus );
	return iStatus;
}
/*-----------------------------------------------------------*/

BaseType_t FF_SDDiskMount( FF_Disk_t *pxDisk )
{
FF_Error_t xFFError;
BaseType_t xReturn = 1;

	/* Mount the partition */
	xFFError = FF_Mount( pxDisk, pxDisk->xStatus.bPartitionNumber );

	if( FF_isERR( xFFError ) )
	{
		FF_PRINTF( "FF_SDDiskMount: %08lX\n", xFFError );
		xReturn = 0;
	}
	else
	{
		pxDisk->xStatus.bIsMounted = pdTRUE;
		FF_PRINTF( "****** FreeRTOS+FAT initialized %lu sectors\n", pxDisk->pxIOManager->xPartition.ulTotalSectors );
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

/* Get a pointer to IOMAN, which can be used for all FreeRTOS+FAT functions */
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
		iPercentageFree = ( int ) ( ( HUNDRED_64_BIT * ullFreeSectors + pxIOManager->xPartition.ulDataSectors / 2 ) /
			( ( uint64_t )pxIOManager->xPartition.ulDataSectors ) );

		ulTotalSizeMB = pxIOManager->xPartition.ulDataSectors / SECTORS_PER_MB;
		ulFreeSizeMB = ( uint32_t ) ( ullFreeSectors / SECTORS_PER_MB );

		/* It is better not to use the 64-bit format such as %Lu because it
		might not be implemented. */
		FF_PRINTF( "Partition Nr   %8u\n", pxDisk->xStatus.bPartitionNumber );
		FF_PRINTF( "Type           %8u (%s)\n", pxIOManager->xPartition.ucType, pcTypeName );
		FF_PRINTF( "VolLabel       '%8s' \n", pxIOManager->xPartition.pcVolumeLabel );
		FF_PRINTF( "TotalSectors   %8lu\n", pxIOManager->xPartition.ulTotalSectors );
		FF_PRINTF( "DataSectors    %8lu\n", pxIOManager->xPartition.ulDataSectors );
		FF_PRINTF( "SecsPerCluster %8lu\n", pxIOManager->xPartition.ulSectorsPerCluster );
		FF_PRINTF( "Size           %8lu MB\n", ulTotalSizeMB );
		FF_PRINTF( "FreeSize       %8lu MB ( %d perc free )\n", ulFreeSizeMB, iPercentageFree );
		FF_PRINTF( "BeginLBA       %8lu\n", pxIOManager->xPartition.ulBeginLBA );
		FF_PRINTF( "FATBeginLBA    %8lu\n", pxIOManager->xPartition.ulFATBeginLBA );
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

#if( ffconfigSDIO_DRIVER_USES_INTERRUPT != 0 )
	static void vInstallInterrupt( void )
	{
		/* Install an interrupt handler for SDIO_0 */
		XScuGic_RegisterHandler( INTC_BASE_ADDR, SCUGIC_SDIO_0_INTR,
			( Xil_ExceptionHandler )XSdPs_IntrHandler,
			( void * )pxSDCardInstance );

		/* Enable this interrupt. */
		XScuGic_EnableIntr( INTC_DIST_BASE_ADDR, SCUGIC_SDIO_0_INTR );

		/* Choose the signals. */
		XSdPs_WriteReg16(pxSDCardInstance->Config.BaseAddress,
				XSDPS_NORM_INTR_SIG_EN_OFFSET,
				XSDPS_INTR_NORMAL_ENABLE );
		XSdPs_WriteReg16(pxSDCardInstance->Config.BaseAddress,
				XSDPS_ERR_INTR_SIG_EN_OFFSET,
				0x0 );
	}
#endif /* ffconfigSDIO_DRIVER_USES_INTERRUPT */
/*-----------------------------------------------------------*/

static int vSDMMC_Init( int iDriveNumber )
{
int iReturnCode, iStatus;
XSdPs_Config *SdConfig;

	/*_RB_ Function name not following convention, parameter not used, parameter
	using plain int type. */


	/* Open a do {} while(0) loop to allow the use of break. */
	do
	{
		/* Check if card is in the socket */
		iStatus = vSDMMC_Status( iDriveNumber );
		if( ( iStatus & STA_NODISK ) != 0 )
		{
			break;
		}

		/* Assume that the initialisation will fail: set the 'STA_NOINIT' bit. */
		iStatus |= STA_NOINIT;

		/* Initialize the host controller */
		SdConfig = XSdPs_LookupConfig(SD_DEVICE_ID);
		if( SdConfig == NULL )
		{
			break;
		}

		iReturnCode = XSdPs_CfgInitialize(pxSDCardInstance, SdConfig, SdConfig->BaseAddress);
		if( iReturnCode != XST_SUCCESS )
		{
			break;
		}

		#if( ffconfigSDIO_DRIVER_USES_INTERRUPT != 0 )
		{
			vInstallInterrupt();
		}
		#endif	/* ffconfigSDIO_DRIVER_USES_INTERRUPT */
		iReturnCode = XSdPs_CardInitialize( pxSDCardInstance );
		if( iReturnCode != XST_SUCCESS )
		{
			break;
		}

		/* Disk is initialized OK: clear the 'STA_NOINIT' bit. */
		iStatus &= ~( STA_NOINIT );
	} while( 0 );

	sd_disk_status = iStatus;

	return iStatus;
}
/*-----------------------------------------------------------*/

static int vSDMMC_Status( int iDriveNumber )
{
int iStatus = sd_disk_status;
u32 ulStatusReg;

	/*_RB_ Function name not following convention, parameter not used, parameter
	using plain int type. */
	( void ) iDriveNumber;

	ulStatusReg = XSdPs_GetPresentStatusReg( XPAR_XSDPS_0_BASEADDR );
	if( ( ulStatusReg & XSDPS_PSR_CARD_INSRT_MASK ) == 0 )
	{
		iStatus = STA_NODISK | STA_NOINIT;
	}
	else
	{
		iStatus &= ~STA_NODISK;
		if( ( ulStatusReg & XSDPS_PSR_WPS_PL_MASK ) != 0 )
		{
			iStatus &= ~STA_PROTECT;
		}
		else
		{
			iStatus |= STA_PROTECT;
		}
	}

	sd_disk_status = iStatus;
	return iStatus;
}
/*-----------------------------------------------------------*/

BaseType_t FF_SDDiskInserted( BaseType_t xDriveNr )
{
BaseType_t xReturn;
int iStatus;

	/* Check if card is in the socket */
	iStatus = vSDMMC_Status( xDriveNr );
	if( ( iStatus & STA_NODISK ) != 0 )
	{
		xReturn = pdFALSE;
	}
	else
	{
		xReturn = pdTRUE;
	}

	return xReturn;
}

volatile unsigned sd_int_count = 0;

#if( ffconfigSDIO_DRIVER_USES_INTERRUPT != 0 )
	volatile u32 ulSDInterruptStatus[2];

	void XSdPs_IntrHandler(void *XSdPsPtr)
	{
	XSdPs *InstancePtr = (XSdPs *)XSdPsPtr;
	int iIndex = InstancePtr->Config.DeviceId;
	uint32_t ulStatusReg;

		configASSERT( iIndex <= 1 );
		sd_int_count++;

		/* Read the current status. */
		ulStatusReg = XSdPs_ReadReg( InstancePtr->Config.BaseAddress, XSDPS_NORM_INTR_STS_OFFSET );

		/* Write to clear error bits. */
		XSdPs_WriteReg( InstancePtr->Config.BaseAddress, XSDPS_NORM_INTR_STS_OFFSET, ulStatusReg );

		/* The new value must be OR-ed, if not the
		Command Complete (CC) event might get overwritten
		by the Transfer Complete (TC) event. */
		ulSDInterruptStatus[ iIndex ] |= ulStatusReg;

		if( ( ulStatusReg & ( XSDPS_INTR_CARD_INSRT_MASK | XSDPS_INTR_CARD_REM_MASK ) ) != 0 )
		{
			/* Could wake-up another task. */
		}
		if( xSDSemaphores[ iIndex ] != NULL )
		{
		BaseType_t xHigherPriorityTaskWoken = pdFALSE;

			xSemaphoreGiveFromISR( xSDSemaphores[ iIndex ], &xHigherPriorityTaskWoken );
			if( xHigherPriorityTaskWoken != 0 )
			{
				portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
			}
		}
	}
#endif /* ffconfigSDIO_DRIVER_USES_INTERRUPT */
/*-----------------------------------------------------------*/

#if( ffconfigSDIO_DRIVER_USES_INTERRUPT != 0 )
	void XSdPs_ClearInterrupt( XSdPs *InstancePtr )
	{
	int iIndex = InstancePtr->Config.DeviceId;

		configASSERT( iIndex <= 1 );
		ulSDInterruptStatus[ iIndex ] = 0;
	}
#endif /* ffconfigSDIO_DRIVER_USES_INTERRUPT */
/*-----------------------------------------------------------*/

#if( ffconfigSDIO_DRIVER_USES_INTERRUPT != 0 )
	/* Wait for an interrupt and return the 32 bits of the status register.
	A return value of 0 means: time-out. */
	u32 XSdPs_WaitInterrupt( XSdPs *InstancePtr, u32 ulMask, u32 ulWait )
	{
	u32 ulStatusReg;
	int iIndex = InstancePtr->Config.DeviceId;
	TickType_t xRemainingTime = pdMS_TO_TICKS( sdWAIT_INT_TIME_OUT_MS );
	TimeOut_t xTimeOut;

		if( ulWait == 0UL )
		{
			xRemainingTime = pdMS_TO_TICKS( sdQUICK_WAIT_INT_TIME_OUT_MS );
		}

		configASSERT( iIndex <= 1 );
		configASSERT( xSDSemaphores[ iIndex ] != 0 );
		vTaskSetTimeOutState( &xTimeOut );
		/* Loop until:
		1. Expected bit (ulMask) becomes high
		2. Time-out reached (normally 2 seconds)
		*/
		do
		{
			if( xRemainingTime != 0 )
			{
				xSemaphoreTake( xSDSemaphores[ iIndex ], xRemainingTime );
			}
			ulStatusReg = ulSDInterruptStatus[ iIndex ];
			if( ( ulStatusReg & XSDPS_INTR_ERR_MASK ) != 0 )
			{
				break;
			}
		}
		while( ( xTaskCheckForTimeOut( &xTimeOut, &xRemainingTime ) == pdFALSE ) &&
			   ( ( ulStatusReg & ulMask ) == 0 ) );

		if( ( ulStatusReg & ulMask ) == 0 )
		{
		ulStatusReg = XSdPs_ReadReg( InstancePtr->Config.BaseAddress, XSDPS_NORM_INTR_STS_OFFSET );
			if( ulWait != 0UL )
			{
				FF_PRINTF( "XSdPs_WaitInterrupt[ %d ]: Got %08lx, expect %08lx ints: %d\n",
					iIndex,
					ulStatusReg,
					ulMask,
					sd_int_count );
			}
		}

		return ulStatusReg;
	}

#endif /* ffconfigSDIO_DRIVER_USES_INTERRUPT */
/*-----------------------------------------------------------*/
