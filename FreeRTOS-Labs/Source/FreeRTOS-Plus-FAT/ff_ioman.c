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

/**
 *	@file		ff_ioman.c
 *	@ingroup	IOMAN
 *
 *	@defgroup	IOMAN	I/O Manager
 *	@brief		Handles IO buffers for FreeRTOS+FAT safely.
 *
 *	Provides a simple static interface to the rest of FreeRTOS+FAT to manage
 *	buffers. It also defines the public interfaces for Creating and
 *	Destroying a FreeRTOS+FAT IO object.
 **/

#include <time.h>
#include <string.h>

#include "ff_headers.h"

#define FAT16_SECTOR_COUNT_4085		4085
#define FAT32_SECTOR_COUNT_65525	65525 /* 65536 clusters */

/* Some values and offsets describing the special sector FS INFO: */
#define  FS_INFO_SIGNATURE1_0x41615252			0x41615252UL
#define  FS_INFO_SIGNATURE2_0x61417272			0x61417272UL
#define  FS_INFO_OFFSET_SIGNATURE1_000			0
#define  FS_INFO_OFFSET_SIGNATURE2_484			484
#define  FS_INFO_OFFSET_FREE_COUNT_488			488
#define  FS_INFO_OFFSET_FREE_CLUSTER_492		492

/* Inspect the PBR (Partition Boot Record) to determine the type of FAT */
static FF_Error_t prvDetermineFatType( FF_IOManager_t *pxIOManager );

/* Check if a given ID introduces an extended partition. */
static BaseType_t prvIsExtendedPartition( uint8_t ucPartitionID );

/* Return pdTRUE if the media byte in an MBR is valid. */
static BaseType_t prvIsValidMedia( uint8_t media );

/* Read the MBR to see what extended partitions have been defined.
Definitions of extended partitions may be chained.
Walk down the chain to find all extended partitions. */
static FF_Error_t FF_ParseExtended( FF_IOManager_t *pxIOManager, uint32_t ulFirstSector, uint32_t ulFirstSize,
	FF_SPartFound_t *pPartsFound );

static FF_Error_t FF_GetEfiPartitionEntry( FF_IOManager_t *pxIOManager, uint32_t ulPartitionNumber );

static BaseType_t prvHasActiveHandles( FF_IOManager_t *pxIOManager );


/**
 *	@public
 *	@brief	Creates an FF_IOManager_t object, to initialise FreeRTOS+FAT
 *
 *	@param	pucCacheMem			Pointer to a buffer for the cache. (NULL if ok to Malloc).
 *	@param	ulCacheSize			The size of the provided buffer, or size of the cache to be created.
 *								(Must be at least 2 * ulSectorSize). Always a multiple of ulSectorSize.
 *	@param	usSectorSize		The block size of devices to be attached. If in doubt use 512.
 *	@param	pError				Pointer to a signed byte for error checking. Can be NULL if not required.
 *								To be checked when a NULL pointer is returned.
 *
 *	@Return	Returns a pointer to an FF_IOManager_t type object. NULL on xError, check the contents of
 *	@Return pError
 **/
FF_IOManager_t *FF_CreateIOManger( FF_CreationParameters_t *pxParameters, FF_Error_t *pError )
{
FF_IOManager_t *pxIOManager = NULL;
FF_Error_t xError;
uint32_t ulCacheSize = pxParameters->ulMemorySize;
uint32_t usSectorSize = pxParameters->ulSectorSize;

	/* Normally:
	ulSectorSize = 512
	ulCacheSize = N x ulSectorSize. */
	if( ( ( usSectorSize % 512 ) != 0 ) || ( usSectorSize == 0 ) )
	{
		/* ulSectorSize Size not a multiple of 512 or it is zero*/
		xError = FF_ERR_IOMAN_BAD_BLKSIZE | FF_CREATEIOMAN;
	}
	else if( ( ( ulCacheSize % ( uint32_t ) usSectorSize ) != 0 ) || ( ulCacheSize == 0 ) ||
			 ( ulCacheSize == ( uint32_t ) usSectorSize ) )
	{
		/* The size of the caching memory (ulCacheSize) must now be atleast 2 * ulSectorSize (or a deadlock will occur). */
		xError = FF_ERR_IOMAN_BAD_MEMSIZE | FF_CREATEIOMAN;
	}
	else
	{
		pxIOManager = ( FF_IOManager_t * ) ffconfigMALLOC( sizeof( FF_IOManager_t ) );

		/* Ensure malloc() succeeded. */
		if( pxIOManager != NULL )
		{
			/* Use memset() to clear every single bit. */
			memset( pxIOManager, '\0', sizeof( FF_IOManager_t ) );
			if( FF_CreateEvents( pxIOManager ) != pdFALSE )
			{
				xError = FF_ERR_NONE;
			}
			else
			{
				/* xEventGroupCreate() probably failed. */
				xError = FF_ERR_NOT_ENOUGH_MEMORY | FF_CREATEIOMAN;
			}
		}
		else
		{
			/* ffconfigMALLOC() failed. */
			xError = FF_ERR_NOT_ENOUGH_MEMORY | FF_CREATEIOMAN;
		}
	}

	if( FF_isERR( xError ) == pdFALSE )
	{
		/* pxIOManager is created, FF_CreateEvents() succeeded. */
		if( pxParameters->pucCacheMemory != NULL )
		{
			/* The caller has provided a piece of memory, use it. */
			pxIOManager->pucCacheMem = pxParameters->pucCacheMemory;
		}
		else
		{
			/* No cache buffer provided, call malloc(). */
			pxIOManager->pucCacheMem = ( uint8_t * ) ffconfigMALLOC( ulCacheSize );
			if( pxIOManager->pucCacheMem != NULL )
			{
				/* Indicate that malloc() was used for pucCacheMem. */
				pxIOManager->ucFlags |= FF_IOMAN_ALLOC_BUFFERS;
			}
			else
			{
				xError = FF_ERR_NOT_ENOUGH_MEMORY | FF_CREATEIOMAN;
			}
		}

		if( pxIOManager->pucCacheMem != NULL )
		{
			memset( pxIOManager->pucCacheMem, '\0', ulCacheSize );
		}
	}

	if( FF_isERR( xError ) == pdFALSE )
	{
		pxIOManager->usSectorSize = usSectorSize;
		pxIOManager->usCacheSize = ( uint16_t ) ( ulCacheSize / ( uint32_t ) usSectorSize );

		/* Malloc() memory for buffer objects. FreeRTOS+FAT never refers to a
		buffer directly but uses buffer objects instead. Allows for thread
		safety. */
		pxIOManager->pxBuffers = ( FF_Buffer_t * ) ffconfigMALLOC( sizeof( FF_Buffer_t ) * pxIOManager->usCacheSize );

		if( pxIOManager->pxBuffers != NULL )
		{
			/* From now on a call to FF_IOMAN_InitBufferDescriptors will clear
			pxBuffers. */
			pxIOManager->ucFlags |= FF_IOMAN_ALLOC_BUFDESCR;

			FF_IOMAN_InitBufferDescriptors( pxIOManager );

			/* Finally store the semaphore for Buffer Description modifications. */
			pxIOManager->pvSemaphore = pxParameters->pvSemaphore;

			if( pxParameters->xBlockDeviceIsReentrant != pdFALSE )
			{
				pxIOManager->ucFlags |= FF_IOMAN_BLOCK_DEVICE_IS_REENTRANT;
			}

			pxIOManager->xBlkDevice.fnpReadBlocks	= pxParameters->fnReadBlocks;
			pxIOManager->xBlkDevice.fnpWriteBlocks	= pxParameters->fnWriteBlocks;
			pxIOManager->xBlkDevice.pxDisk			= pxParameters->pxDisk;
		}
		else
		{
			xError = FF_ERR_NOT_ENOUGH_MEMORY | FF_CREATEIOMAN;
		}
	}

	if( FF_isERR( xError ) )
	{
		if( pxIOManager != NULL )
		{
			FF_DeleteIOManager( pxIOManager );
			pxIOManager = NULL;
		}
	}

	if( pError != NULL )
	{
		*pError = xError;
	}

	return pxIOManager;
}	/* FF_CreateIOManger() */
/*-----------------------------------------------------------*/

/**
 *	@public
 *	@brief	Destroys an FF_IOManager_t object, and frees all assigned memory.
 *
 *	@param	pxIOManager	Pointer to an FF_IOManager_t object, as returned from FF_CreateIOManger.
 *
 *	@Return	FF_ERR_NONE on sucess, or a documented error code on failure. (FF_ERR_NULL_POINTER)
 *
 **/
FF_Error_t FF_DeleteIOManager( FF_IOManager_t *pxIOManager )
{
FF_Error_t xError;

	/* Ensure no NULL pointer was provided. */
	if( pxIOManager == NULL )
	{
		xError = FF_ERR_NULL_POINTER | FF_DESTROYIOMAN;
	}
	else
	{
		xError = FF_ERR_NONE;

		/* Ensure pxBuffers pointer was allocated. */
		if( ( pxIOManager->ucFlags & FF_IOMAN_ALLOC_BUFDESCR ) != 0 )
		{
			ffconfigFREE( pxIOManager->pxBuffers );
		}

		/* Ensure pucCacheMem pointer was allocated. */
		if( ( pxIOManager->ucFlags & FF_IOMAN_ALLOC_BUFFERS ) != 0 )
		{
			ffconfigFREE( pxIOManager->pucCacheMem );
		}

		/* Delete the event group object within the IO manager before deleting
		the manager. */
		FF_DeleteEvents( pxIOManager );

		/* Finally free the FF_IOManager_t object. */
		ffconfigFREE( pxIOManager );
	}

	return xError;
}	/* FF_DeleteIOManager() */
/*-----------------------------------------------------------*/

/**
 *	@private
 *	@brief	Initialises Buffer Descriptions as part of the FF_IOManager_t object initialisation.
 *
 *	@param	pxIOManager		IOMAN Object.
 *
 **/
void FF_IOMAN_InitBufferDescriptors( FF_IOManager_t *pxIOManager )
{
uint8_t *pucBuffer = pxIOManager->pucCacheMem;
FF_Buffer_t *pxBuffer = pxIOManager->pxBuffers;
FF_Buffer_t *pxLastBuffer = pxBuffer + pxIOManager->usCacheSize;

	/* Clear the contents of the buffer descriptors. */
	memset( ( void * ) pxBuffer, '\0', sizeof( FF_Buffer_t ) * pxIOManager->usCacheSize );

	while( pxBuffer < pxLastBuffer )
	{
		pxBuffer->pucBuffer = pucBuffer;
		pxBuffer++;
		pucBuffer += pxIOManager->usSectorSize;
	}
}	/* FF_IOMAN_InitBufferDescriptors() */
/*-----------------------------------------------------------*/

/**
 *	@private
 *	@brief		Flushes all Write cache buffers with no active Handles.
 *
 *	@param		pxIOManager	IOMAN Object.
 *
 *	@Return		FF_ERR_NONE on Success.
 **/
FF_Error_t FF_FlushCache( FF_IOManager_t *pxIOManager )
{
BaseType_t xIndex, xIndex2;
FF_Error_t xError;

	if( pxIOManager == NULL )
	{
		xError = FF_ERR_NULL_POINTER | FF_FLUSHCACHE;
	}
	else
	{
		xError = FF_ERR_NONE;

		FF_PendSemaphore( pxIOManager->pvSemaphore );
		{
			for( xIndex = 0; xIndex < pxIOManager->usCacheSize; xIndex++ )
			{
				/* If a buffers has no users and if it has been modified... */
				if( ( pxIOManager->pxBuffers[ xIndex ].usNumHandles == 0 ) && ( pxIOManager->pxBuffers[ xIndex ].bModified == pdTRUE ) )
				{
					/* The buffer may be flushed to disk. */
					FF_BlockWrite( pxIOManager, pxIOManager->pxBuffers[ xIndex ].ulSector, 1, pxIOManager->pxBuffers[ xIndex ].pucBuffer, pdTRUE );

					/* Buffer has now been flushed, mark it as a read buffer and unmodified. */
					pxIOManager->pxBuffers[ xIndex ].ucMode = FF_MODE_READ;
					pxIOManager->pxBuffers[ xIndex ].bModified = pdFALSE;

					/* Search for other buffers that used this sector, and mark them as modified
					So that further requests will result in the new sector being fetched. */
					for( xIndex2 = 0; xIndex2 < pxIOManager->usCacheSize; xIndex2++ )
					{
						if( ( xIndex != xIndex2 ) &&
							( pxIOManager->pxBuffers[ xIndex2 ].ulSector == pxIOManager->pxBuffers[ xIndex ].ulSector ) &&
							( pxIOManager->pxBuffers[ xIndex2 ].ucMode == FF_MODE_READ ) )
						{
							pxIOManager->pxBuffers[ xIndex2 ].bModified = pdTRUE;
						}
					}
				}
			}
		}
		if( ( pxIOManager->xBlkDevice.pxDisk != NULL ) &&
			( pxIOManager->xBlkDevice.pxDisk->fnFlushApplicationHook != NULL ) )
		{
			/* Let the low-level driver also flush data.
			See comments in ff_ioman.h. */
			pxIOManager->xBlkDevice.pxDisk->fnFlushApplicationHook( pxIOManager->xBlkDevice.pxDisk );
		}

		FF_ReleaseSemaphore( pxIOManager->pvSemaphore );
	}

	return xError;
}	/* FF_FlushCache() */
/*-----------------------------------------------------------*/

/*
	A new version of FF_GetBuffer() with a simple mechanism for timeout
*/
#define FF_GETBUFFER_SLEEP_TIME_MS	10
#define FF_GETBUFFER_WAIT_TIME_MS	( 20000 / FF_GETBUFFER_SLEEP_TIME_MS )

FF_Buffer_t *FF_GetBuffer( FF_IOManager_t *pxIOManager, uint32_t ulSector, uint8_t ucMode )
{
FF_Buffer_t *pxBuffer;
/* Least Recently Used Buffer */
FF_Buffer_t *pxRLUBuffer;
FF_Buffer_t *pxMatchingBuffer = NULL;
int32_t lRetVal;
BaseType_t xLoopCount = FF_GETBUFFER_WAIT_TIME_MS;
const FF_Buffer_t *pxLastBuffer = &( pxIOManager->pxBuffers[ pxIOManager->usCacheSize ] );

	/* 'pxIOManager->usCacheSize' is bigger than zero and it is a multiple of ulSectorSize. */

	while( pxMatchingBuffer == NULL )
	{
		xLoopCount--;
		if( xLoopCount == 0 )
		{
			break;
		}

		FF_PendSemaphore( pxIOManager->pvSemaphore );

		for( pxBuffer = pxIOManager->pxBuffers; pxBuffer < pxLastBuffer; pxBuffer++ )
		{
			if( ( pxBuffer->ulSector == ulSector ) && ( pxBuffer->bValid ) )
			{
				pxMatchingBuffer = pxBuffer;
				/* Don't look further if you found a perfect match. */
				break;
			}
		}

		if( pxMatchingBuffer != NULL )
		{
			/* A Match was found process! */
			if( ( ucMode == FF_MODE_READ ) && ( pxMatchingBuffer->ucMode == FF_MODE_READ ) )
			{
				pxMatchingBuffer->usNumHandles += 1;
				pxMatchingBuffer->usPersistance += 1;
				break;
			}

			if( pxMatchingBuffer->usNumHandles == 0 )
			{
				pxMatchingBuffer->ucMode = ( ucMode & FF_MODE_RD_WR );
				if( ( ucMode & FF_MODE_WRITE ) != 0 )
				{
					/* This buffer has no attached handles. */
					pxMatchingBuffer->bModified = pdTRUE;
				}

				pxMatchingBuffer->usNumHandles = 1;
				pxMatchingBuffer->usPersistance += 1;
				break;
			}

			pxMatchingBuffer = NULL;	/* Sector is already in use, keep yielding until its available! */
		}
		else
		{
			/* There is no valid buffer now for the desired sector.
			Find a free buffer and use it for that sector. */
			pxRLUBuffer = NULL;

			for( pxBuffer = pxIOManager->pxBuffers; pxBuffer < pxLastBuffer; pxBuffer++ )
			{
				if( pxBuffer->usNumHandles != 0 )
				{
					continue;	/* Occupied */
				}

				pxBuffer->ulLRU += 1;

				if( ( pxRLUBuffer == NULL ) ||
					( pxBuffer->ulLRU > pxRLUBuffer->ulLRU ) ||
					( ( pxBuffer->ulLRU == pxRLUBuffer->ulLRU ) && ( pxBuffer->usPersistance > pxRLUBuffer->usPersistance ) ) )
				{
					pxRLUBuffer = pxBuffer;
				}
			}

			/* A free buffer with the highest value of 'ulLRU' was found: */
			if( pxRLUBuffer != NULL )
			{
				/* Process the suitable candidate. */
				if( pxRLUBuffer->bModified == pdTRUE )
				{
					/* Along with the pdTRUE parameter to indicate semaphore has been claimed already. */
					lRetVal = FF_BlockWrite( pxIOManager, pxRLUBuffer->ulSector, 1, pxRLUBuffer->pucBuffer, pdTRUE );
					if( lRetVal < 0 )
					{
						/* NULL will be returned because 'pxMatchingBuffer' is still NULL. */
						break;
					}
				}

				if( ucMode == FF_MODE_WR_ONLY )
				{
					memset( pxRLUBuffer->pucBuffer, '\0', pxIOManager->usSectorSize );
				}
				else
				{
					lRetVal = FF_BlockRead( pxIOManager, ulSector, 1, pxRLUBuffer->pucBuffer, pdTRUE );
					if( lRetVal < 0 )
					{
						/* 'pxMatchingBuffer' is NULL. */
						break;
					}
				}

				pxRLUBuffer->ucMode = ( ucMode & FF_MODE_RD_WR );
				pxRLUBuffer->usPersistance = 1;
				pxRLUBuffer->ulLRU = 0;
				pxRLUBuffer->usNumHandles = 1;
				pxRLUBuffer->ulSector = ulSector;

				pxRLUBuffer->bModified = ( ucMode & FF_MODE_WRITE ) != 0;

				pxRLUBuffer->bValid = pdTRUE;
				pxMatchingBuffer = pxRLUBuffer;
				break;
			} /* if( pxRLUBuffer != NULL ) */
		} /* else ( pxMatchingBuffer == NULL ) */

		FF_ReleaseSemaphore( pxIOManager->pvSemaphore );

		/* Better to go asleep to give low-priority task a chance to release buffer(s). */
		FF_BufferWait( pxIOManager, FF_GETBUFFER_SLEEP_TIME_MS );
	} /* while( pxMatchingBuffer == NULL ) */

	if( xLoopCount > 0 )
	{
		/* If xLoopCount is 0 here, the semaphore was not taken. */
		FF_ReleaseSemaphore( pxIOManager->pvSemaphore );
	}
	if( pxMatchingBuffer == NULL )
	{
		FF_PRINTF( "FF_GetBuffer[0x%X]: failed mode 0x%X\n", ( unsigned )ulSector, ( unsigned )ucMode );
	}
	return pxMatchingBuffer;	/* Return the Matched Buffer! */
}	/* FF_GetBuffer() */
/*-----------------------------------------------------------*/

/**
 *	@private
 *	@brief	Releases a buffer resource.
 *
 *	@param	pxIOManager	Pointer to an FF_IOManager_t object.
 *	@param	pxBuffer	Pointer to an FF_Buffer_t object.
 *
 **/
FF_Error_t FF_ReleaseBuffer( FF_IOManager_t *pxIOManager, FF_Buffer_t *pxBuffer )
{
	FF_Error_t xError = FF_ERR_NONE;

	/* Protect description changes with a semaphore. */
	FF_PendSemaphore( pxIOManager->pvSemaphore );
	{
#if( ffconfigCACHE_WRITE_THROUGH != 0 )
		if( pxBuffer->bModified == pdTRUE )
		{
			xError = FF_BlockWrite( pxIOManager, pxBuffer->ulSector, 1, pxBuffer->pucBuffer, pdTRUE );
			if( FF_isERR( xError ) == pdFALSE )
			{
				/* Ensure if an error occurs its still possible to write the block again. */
				pxBuffer->bModified = pdFALSE;
			}
		}
#endif
		configASSERT( pxBuffer->usNumHandles != 0 );

		if( pxBuffer->usNumHandles != 0 )
		{
			pxBuffer->usNumHandles--;
		}
		else
		{
			/*printf ("FF_ReleaseBuffer: buffer not claimed\n"); */
		}
	}

	FF_ReleaseSemaphore( pxIOManager->pvSemaphore );

	/* Notify tasks which may be waiting in FF_GetBuffer() */
	FF_BufferProceed( pxIOManager );

	return xError;
}	/* FF_ReleaseBuffer() */
/*-----------------------------------------------------------*/

/* New Interface for FreeRTOS+FAT to read blocks. */
int32_t FF_BlockRead( FF_IOManager_t *pxIOManager, uint32_t ulSectorLBA, uint32_t ulNumSectors, void *pxBuffer,
	BaseType_t xSemLocked )
{
int32_t slRetVal = 0;

	if( pxIOManager->xPartition.ulTotalSectors != 0ul )
	{
		/* At some point while formatting a partition, ulTotalSectors might be unknown.
		In that case this test will be skipped. */
		if( ( ulSectorLBA + ulNumSectors ) > ( pxIOManager->xPartition.ulTotalSectors + pxIOManager->xPartition.ulBeginLBA ) )
		{
			slRetVal = FF_ERR_IOMAN_OUT_OF_BOUNDS_READ | FF_BLOCKREAD;
		}
	}

	if( ( slRetVal == 0ul ) && ( pxIOManager->xBlkDevice.fnpReadBlocks != NULL ) )
	{
		do
		{
			/* Make sure we don't execute a NULL. */
			if( ( xSemLocked == pdFALSE ) &&
				( ( pxIOManager->ucFlags & FF_IOMAN_BLOCK_DEVICE_IS_REENTRANT ) == pdFALSE ) )
			{
				FF_PendSemaphore( pxIOManager->pvSemaphore );
			}

			slRetVal = pxIOManager->xBlkDevice.fnpReadBlocks( pxBuffer, ulSectorLBA, ulNumSectors, pxIOManager->xBlkDevice.pxDisk );

			if( ( xSemLocked == pdFALSE ) &&
				( ( pxIOManager->ucFlags & FF_IOMAN_BLOCK_DEVICE_IS_REENTRANT ) == pdFALSE ) )
			{
				FF_ReleaseSemaphore( pxIOManager->pvSemaphore );
			}

			if( FF_GETERROR( slRetVal ) != FF_ERR_DRIVER_BUSY )
			{
				break;
			}

			FF_Sleep( ffconfigDRIVER_BUSY_SLEEP_MS );
		} while( pdTRUE );
	}

	return slRetVal;
}	/* FF_BlockRead() */
/*-----------------------------------------------------------*/

int32_t FF_BlockWrite( FF_IOManager_t *pxIOManager, uint32_t ulSectorLBA, uint32_t ulNumSectors, void *pxBuffer,
	BaseType_t xSemLocked )
{
int32_t slRetVal = 0;

	if( pxIOManager->xPartition.ulTotalSectors != 0 )
	{
		/* At some point while formatting a partition, ulTotalSectors might be unknown.
		In that case this test will be skipped. */
		if( ( ulSectorLBA + ulNumSectors ) > ( pxIOManager->xPartition.ulTotalSectors + pxIOManager->xPartition.ulBeginLBA ) )
		{
			slRetVal = FF_ERR_IOMAN_OUT_OF_BOUNDS_WRITE | FF_BLOCKWRITE;
		}
	}

	if( ( slRetVal == 0ul ) && ( pxIOManager->xBlkDevice.fnpWriteBlocks != NULL ) )
	{
		do
		{	/* Make sure we don't execute a NULL. */

			if( ( xSemLocked == pdFALSE ) &&
				( ( pxIOManager->ucFlags & FF_IOMAN_BLOCK_DEVICE_IS_REENTRANT ) == pdFALSE ) )
			{
				FF_PendSemaphore( pxIOManager->pvSemaphore );
			}

			slRetVal = pxIOManager->xBlkDevice.fnpWriteBlocks( pxBuffer, ulSectorLBA, ulNumSectors, pxIOManager->xBlkDevice.pxDisk );

			if( ( xSemLocked == pdFALSE ) &&
				( ( pxIOManager->ucFlags & FF_IOMAN_BLOCK_DEVICE_IS_REENTRANT ) == pdFALSE ) )
			{
				FF_ReleaseSemaphore( pxIOManager->pvSemaphore );
			}

			if( FF_GETERROR( slRetVal ) != FF_ERR_DRIVER_BUSY )
			{
				break;
			}

			FF_Sleep( ffconfigDRIVER_BUSY_SLEEP_MS );
		} while( pdTRUE );
	}

	return slRetVal;
}	/* FF_BlockWrite() */
/*-----------------------------------------------------------*/

/*
 * This global variable is a kind of expert option:
 * It may be set to one of these values: FF_T_FAT[12,16,32]
 * just to force the driver to assume a certain FAT type.
 */
uint8_t ucAssumeFATType;

/* The history of FAT types:
 * The Microsoft documents says that the actual type: FAT-12, FAT-16 and FAT-32
 * of a partition can be found by looking at the total number of data clusters:
 *
 * if( clusters < 4085 )
 *     Assume FAT-12
 * else if( clusters < 65525 )
 *     Assume FAT-16
 * else
 *     Assume FAT-32
 *
 * In practice however, this does not always seem to be a correct assumption.
 *
 * The first 12 or 16 bits in the FAT table may also help to determine the
 * correct FAT-type:
 *
 *    FAT-12: ( firstWord & 0x3FF ) == 0x3F8 )
 *    FAT-16: ( firstWord == 0xFFF8 )
 */

static FF_Error_t prvDetermineFatType( FF_IOManager_t *pxIOManager )
{
FF_Partition_t *pxPartition;
FF_Buffer_t *pxBuffer;
uint32_t ulFirstWord = 0ul;
FF_Error_t xError = FF_ERR_NONE;

	pxPartition = &( pxIOManager->xPartition );
	if( ucAssumeFATType != 0 )
	{
		switch( ucAssumeFATType )
		{
		case FF_T_FAT12:
		case FF_T_FAT16:
		case FF_T_FAT32:
			pxPartition->ucType = ucAssumeFATType;
			break;
		default:
			/* An invalid value will be ignored, and the FAT type is determined dynamically. */
			ucAssumeFATType = 0;
			break;
		}
		xError = FF_ERR_NONE;
	}

	/* Test again, the value may have become zero now: */
	if( ucAssumeFATType == 0 )
	{
		pxBuffer = FF_GetBuffer( pxIOManager, pxIOManager->xPartition.ulFATBeginLBA, FF_MODE_READ );
		if( pxBuffer == NULL )
		{
			xError = FF_ERR_DEVICE_DRIVER_FAILED | FF_DETERMINEFATTYPE;
		}
		else
		{
			ulFirstWord = ( uint32_t ) FF_getShort( pxBuffer->pucBuffer, 0x0000 );
			xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
		}
	}

	if( ( ucAssumeFATType == 0 ) && ( FF_isERR( xError ) == pdFALSE ) )
	{
	#if( ffconfigFAT12_SUPPORT != 0 )
		if( pxPartition->ulNumClusters < FAT16_SECTOR_COUNT_4085 )
		{
			/* FAT12 */
			pxPartition->ucType = FF_T_FAT12;
			#if( ffconfigFAT_CHECK != 0 )
			if( ( ulFirstWord & 0x3FF ) != 0x3F8 )
			{
				xError = FF_ERR_IOMAN_NOT_FAT_FORMATTED | FF_DETERMINEFATTYPE;
			}
			else
			#endif /* ffconfigFAT_CHECK */
			{
				xError = FF_ERR_NONE;
			}
		}
		else
	#endif /* ffconfigFAT12_SUPPORT */

		if( pxPartition->ulNumClusters < FAT32_SECTOR_COUNT_65525 )
		{
			/* FAT 16 */
			pxPartition->ucType = FF_T_FAT16;
			#if( ffconfigFAT_CHECK != 0 )
			{
				if( ulFirstWord == 0xFFF8 )
				{
					xError = FF_ERR_NONE;
				}
				else {
					if( ( ulFirstWord & 0x3FF ) != 0x3F8 )
					{
						FF_PRINTF( "Part at %lu is probably a FAT12\n", pxIOManager->xPartition.ulFATBeginLBA );
					}
					else
					{
						FF_PRINTF( "Partition at %lu has strange FAT data %08lX\n",
							pxIOManager->xPartition.ulFATBeginLBA, ulFirstWord );
					}
					xError = FF_ERR_IOMAN_INVALID_FORMAT | FF_DETERMINEFATTYPE;
				}
			}
			#endif /* ffconfigFAT_CHECK */
		}
		else
		{
			/* FAT 32! */
			pxPartition->ucType = FF_T_FAT32;
	#if( ffconfigFAT_CHECK != 0 )
			if( ( ( ulFirstWord & 0x0FFFFFF8 ) != 0x0FFFFFF8 ) &&
				( ( ulFirstWord & 0x0FFFFFF8 ) != 0x0FFFFFF0 ) )
			{
				/* _HT_
				I had an SD-card which worked well in Linux/W32
				but FreeRTOS+FAT returned me this error
				So for me I left out this check (just issue a warning for now)
				*/
				FF_PRINTF( "prvDetermineFatType: firstWord %08lX\n", ulFirstWord );
				xError = FF_ERR_NONE; /* FF_ERR_IOMAN_NOT_FAT_FORMATTED; */
			}

	#endif	/* ffconfigFAT_CHECK */
			xError = FF_ERR_NONE;
		}
	}

	return xError;
}	/* prvDetermineFatType() */
/*-----------------------------------------------------------*/

/* Check if ucPartitionID introduces an extended partition. */
static BaseType_t prvIsExtendedPartition( uint8_t ucPartitionID )
{
BaseType_t xResult;

	if( ( ucPartitionID == FF_DOS_EXT_PART ) ||
		( ucPartitionID == FF_WIN98_EXT_PART ) ||
		( ucPartitionID == FF_LINUX_EXT_PART ) )
	{
		xResult = pdTRUE;
	}
	else
	{
		xResult = pdFALSE;
	}

	return xResult;
}	/* prvIsExtendedPartition() */
/*-----------------------------------------------------------*/

/* Check if the media byte in an MBR is valid */
static BaseType_t prvIsValidMedia( uint8_t media )
{
BaseType_t xResult;
	/*
	 * 0xF8 is the standard value for “fixed” (non-removable) media. For
	 * removable media, 0xF0 is frequently used. The legal values for this
	 * field are 0xF0, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE, and
	 * 0xFF. The only other important point is that whatever value is put
	 * in here must also be put in the low byte of the FAT[0] entry. This
	 * dates back to the old MS-DOS 1.x media determination noted
	 * earlier and is no longer usually used for anything.
	 */
	if( ( 0xf8 <= media ) || ( media == 0xf0 ) )
	{
		xResult = pdTRUE;
	}
	else
	{
		xResult = pdFALSE;
	}

	return xResult;
}	/* prvIsValidMedia() */
/*-----------------------------------------------------------*/

void FF_ReadParts( uint8_t *pucBuffer, FF_Part_t *pxParts )
{
BaseType_t xPartNr;
UBaseType_t uxOffset = FF_FAT_PTBL;

	/* pxParts is expected to be declared as an array of 4 elements:
		FF_Part_t pxParts[4];
		FF_ReadParts( pxBuffer->pucBuffer, pxParts );
	*/
	for( xPartNr = 0; xPartNr < 4; xPartNr++, uxOffset += 16, pxParts++ )
	{
		pxParts->ucActive = FF_getChar( pucBuffer, uxOffset + FF_FAT_PTBL_ACTIVE );
		pxParts->ucPartitionID = FF_getChar( pucBuffer, uxOffset + FF_FAT_PTBL_ID );
		pxParts->ulSectorCount = FF_getLong( pucBuffer, uxOffset + FF_FAT_PTBL_SECT_COUNT );
		pxParts->ulStartLBA = FF_getLong( pucBuffer, uxOffset + FF_FAT_PTBL_LBA );
	}
}
/*-----------------------------------------------------------*/

/*  This function will traverse through a chain of extended partitions. */

/* It is protected against rubbish data by a counter. */
static FF_Error_t FF_ParseExtended( FF_IOManager_t *pxIOManager, uint32_t ulFirstSector, uint32_t ulFirstSize,
	FF_SPartFound_t *pPartsFound )
{
uint32_t ulThisSector, ulThisSize;
uint32_t ulSectorSize = pxIOManager->usSectorSize / 512;
uint32_t prevTotalSectors = pxIOManager->xPartition.ulTotalSectors;
FF_Buffer_t *pxBuffer = NULL;
BaseType_t xTryCount = 100;
BaseType_t xPartNr;
BaseType_t xExtendedPartNr;
FF_Error_t xError = FF_ERR_NONE;
FF_Part_t pxPartitions[ 4 ];

	ulThisSector = ulFirstSector;
	ulThisSize = ulFirstSize;

	/* Disable sector checking in FF_BlockRead, because the
	exact disk (partition) parameters are not yet known.
	Let user driver return an error is appropriate. */
	pxIOManager->xPartition.ulTotalSectors = 0;

	while( xTryCount-- )
	{
		if( ( pxBuffer == NULL ) || ( pxBuffer->ulSector != ulThisSector ) )
		{
			/* Moving to a different sector. Release the
			previous one and allocate a new buffer. */
			if( pxBuffer != NULL )
			{
				xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
				pxBuffer = NULL;
				if( FF_isERR( xError ) )
				{
					break;
				}
			}
			FF_PRINTF( "FF_ParseExtended: Read sector %u\n", ( unsigned) ulThisSector );
			pxBuffer = FF_GetBuffer( pxIOManager, ulThisSector, FF_MODE_READ );
			if( pxBuffer == NULL )
			{
				xError = FF_PARSEEXTENDED | FF_ERR_DEVICE_DRIVER_FAILED; /* | FUNCTION...; */
				break;
			}
		}

		{
		uint8_t a = FF_getChar( pxBuffer->pucBuffer, FF_FAT_MBR_SIGNATURE + 0 );
		uint8_t b = FF_getChar( pxBuffer->pucBuffer, FF_FAT_MBR_SIGNATURE + 1 );

			if( ( a != 0x55 ) || ( b != 0xAA ) )
			{
				FF_PRINTF( "FF_ParseExtended: No signature %02X,%02X\n", a, b );
				break;
			}
		}

		/* Check for data partition(s),
		and remember if there is an extended partition */

		FF_ReadParts( pxBuffer->pucBuffer, pxPartitions );

		/* Assume there is no next ext partition. */
		xExtendedPartNr = -1;

		for( xPartNr = 0; xPartNr < 4; xPartNr++ )
		{
		uint32_t ulOffset, ulSize, ulNext;
			if( pxPartitions[ xPartNr ].ulSectorCount == 0 )
			{
				/* Partition is empty */
				continue;
			}

			if( prvIsExtendedPartition( pxPartitions[ xPartNr ].ucPartitionID ) )
			{
				if( xExtendedPartNr < 0 )
				{
					xExtendedPartNr = xPartNr;
				}

				continue;	/* We'll examine this ext partition later */
			}

			/* Some sanity checks */
			ulOffset = pxPartitions[ xPartNr ].ulStartLBA * ulSectorSize;
			ulSize = pxPartitions[ xPartNr ].ulSectorCount * ulSectorSize;
			ulNext = ulThisSector + ulOffset;
			if(
				/* Is it oversized? */
				( ulOffset + ulSize > ulThisSize ) ||
				/* or going backward? */
				( ulNext < ulFirstSector ) ||
				/* Or outsize the logical partition? */
				( ulNext > ulFirstSector + ulFirstSize )
				)
			{
				FF_PRINTF( "Part %d looks insane: ulThisSector %u ulOffset %u ulNext %u\n",
					( int ) xPartNr, ( unsigned )ulThisSector, ( unsigned )ulOffset, ( unsigned )ulNext );
				continue;
			}

			{
				/* Store this partition for the caller */
				FF_Part_t *p = &pPartsFound->pxPartitions[ pPartsFound->iCount++ ];

				/* Copy the whole structure */
				memcpy( p, pxPartitions + xPartNr, sizeof( *p ) );

				/* and make LBA absolute to sector-0. */
				p->ulStartLBA += ulThisSector;
				p->bIsExtended = pdTRUE;
			}

			if( pPartsFound->iCount >= ffconfigMAX_PARTITIONS )
			{
				break;
			}

			xTryCount = 100;
		}	/* for( xPartNr = 0; xPartNr < 4; xPartNr++ ) */

		if( xExtendedPartNr < 0 )
		{
			FF_PRINTF( "No more extended partitions\n" );
			break;		/* nothing left to do */
		}

		/* Examine the ulNext extended partition */
		ulThisSector = ulFirstSector + pxPartitions[ xExtendedPartNr ].ulStartLBA * ulSectorSize;
		ulThisSize = pxPartitions[ xExtendedPartNr ].ulSectorCount * ulSectorSize;
	}

	if( pxBuffer != NULL )
	{
		FF_Error_t xTempError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
		if( FF_isERR( xError ) == pdFALSE )
		{
			xError = xTempError;
		}
	}

	pxIOManager->xPartition.ulTotalSectors = prevTotalSectors;

	return xError;
}	/* FF_ParseExtended() */
/*-----------------------------------------------------------*/

/**
 *	@public
 *	@brief	Searches a disk for all primary and extended/logical partitions
 *	@brief	Previously called FF_PartitionCount
 *
 *	@param	pxIOManager		FF_IOManager_t object.
 *	@param	pPartsFound		Contains an array of ffconfigMAX_PARTITIONS partitions
 *
 *	@Return	>=0 Number of partitions found
 *	@Return	<0 error
 **/
FF_Error_t FF_PartitionSearch( FF_IOManager_t *pxIOManager, FF_SPartFound_t *pPartsFound )
{
BaseType_t xPartNr;
FF_Buffer_t *pxBuffer;
uint8_t *ucDataBuffer;
BaseType_t isPBR = pdFALSE;
FF_Error_t xError = FF_ERR_NONE;
uint32_t prevTotalSectors = pxIOManager->xPartition.ulTotalSectors;
FF_Part_t pxPartitions[ 4 ];

	memset( pPartsFound, '\0', sizeof( *pPartsFound ) );

	do
	{
		pxBuffer = FF_GetBuffer( pxIOManager, 0, FF_MODE_READ );
		if( pxBuffer == NULL )
		{
			xError = FF_ERR_DEVICE_DRIVER_FAILED | FF_PARTITIONSEARCH;
			break;
		}

		/* Disable sector checking in FF_BlockRead
		Let user driver return an error is appropriate. */
		pxIOManager->xPartition.ulTotalSectors = 0;
		ucDataBuffer = pxBuffer->pucBuffer;

		/* Check MBR (Master Boot Record) or
		PBR (Partition Boot Record) signature. */
		if( ( FF_getChar( ucDataBuffer, FF_FAT_MBR_SIGNATURE ) != 0x55 ) &&
			( FF_getChar( ucDataBuffer, FF_FAT_MBR_SIGNATURE ) != 0xAA ) )
		{
			/* No MBR, but is it a PBR ?
			Partition Boot Record */
			if( ( FF_getChar( ucDataBuffer, 0 ) == 0xEB ) && /* PBR Byte 0 */
				( FF_getChar( ucDataBuffer, 2 ) == 0x90 ) )
			{
				/* PBR Byte 2
				No MBR but PBR exist then there is only one partition
				Handle this later. */
				isPBR = pdTRUE;
			}
			else
			{
				FF_PRINTF( "FF_PartitionSearch: [%02X,%02X] No signature (%02X %02X), no PBR neither\n",
					FF_getChar( ucDataBuffer, 0 ),
					FF_getChar( ucDataBuffer, 2 ),
					FF_getChar( ucDataBuffer, FF_FAT_MBR_SIGNATURE ),
					FF_getChar( ucDataBuffer, FF_FAT_MBR_SIGNATURE + 1 ) );

				/* No MBR and no PBR then no partition found. */
				xError = FF_ERR_IOMAN_INVALID_FORMAT | FF_PARTITIONSEARCH;
				break;
			}
		}
		/* Copy the 4 partition records into 'pxPartitions': */
		FF_ReadParts( ucDataBuffer, pxPartitions );

		for( xPartNr = 0; ( xPartNr < 4 ) && ( isPBR == pdFALSE ); xPartNr++ )
		{
			/*		FF_PRINTF ("FF_Part[%d]: id %02X act %02X Start %6lu Len %6lu (sectors)\n", */
			/*			xPartNr, pxPartitions[ xPartNr ].ucPartitionID, */
			/*			pxPartitions[ xPartNr ].ucActive, */
			/*			pxPartitions[ xPartNr ].ulStartLBA, */
			/*			pxPartitions[ xPartNr ].ulSectorCount); */
			if( prvIsExtendedPartition( pxPartitions[ xPartNr ].ucPartitionID ) != pdFALSE )
			{
				continue;		/* Do this later */
			}

			/* The first sector must be a MBR, then check the partition entry in the MBR */
			if( ( pxPartitions[ xPartNr ].ucActive != 0x80 ) &&
				( pxPartitions[ xPartNr ].ucActive != 0x00 ) )
			{
				if( ( xPartNr == 0 ) &&
					( FF_getShort( ucDataBuffer, FF_FAT_RESERVED_SECTORS ) != 0 ) &&
					( FF_getChar( ucDataBuffer, FF_FAT_NUMBER_OF_FATS ) != 0 ) )
				{
					isPBR = pdTRUE;
				}
				else
				{
					xError = FF_ERR_IOMAN_INVALID_FORMAT | FF_PARTITIONSEARCH;
					break;
				}
			}
			else if( pxPartitions[ xPartNr ].ulSectorCount )
			{
				FF_Part_t	*p = &pPartsFound->pxPartitions[ pPartsFound->iCount++ ];
				*p = pxPartitions[ xPartNr ];
				p->bIsExtended = 0;
				if( pPartsFound->iCount >= ffconfigMAX_PARTITIONS )
				{
					break;
				}
			}
		}
		if( FF_isERR( xError ) || ( pPartsFound->iCount >= ffconfigMAX_PARTITIONS ) )
		{
			break;
		}
		for( xPartNr = 0; xPartNr < 4; xPartNr++ )
		{
			if( prvIsExtendedPartition( pxPartitions[ xPartNr ].ucPartitionID ) )
			{
				xError = FF_ParseExtended( pxIOManager, pxPartitions[ xPartNr ].ulStartLBA,
					pxPartitions[ xPartNr ].ulSectorCount, pPartsFound );

				if( ( FF_isERR( xError ) != pdFALSE ) || ( pPartsFound->iCount >= ffconfigMAX_PARTITIONS ) )
				{
					goto done;
				}
			}
		}

		if( pPartsFound->iCount == 0 )
		{
			FF_PRINTF( "FF_Part: no partitions, try as PBR\n" );
			isPBR = pdTRUE;
		}

		if( isPBR )
		{
			uint8_t media = FF_getChar( ucDataBuffer, FF_FAT_MEDIA_TYPE );
			FF_Part_t	*p;
			if( !prvIsValidMedia( media ) )
			{
				FF_PRINTF( "FF_Part: Looks like PBR but media %02X\n", media );
				xError = FF_ERR_IOMAN_NO_MOUNTABLE_PARTITION | FF_PARTITIONSEARCH;
				goto done;
			}

			/* This looks like a PBR because it has a valid media type */
			p = pPartsFound->pxPartitions;
			p->ulStartLBA = 0;	/* FF_FAT_PTBL_LBA */
			p->ulSectorCount = ( uint32_t ) FF_getShort( pxBuffer->pucBuffer, FF_FAT_16_TOTAL_SECTORS );
			if( p->ulSectorCount == 0ul )
			{
				p->ulSectorCount = FF_getLong( pxBuffer->pucBuffer, FF_FAT_32_TOTAL_SECTORS );
			}

			p->ucActive = 0x80;	/* FF_FAT_PTBL_ACTIVE */
			p->ucPartitionID = 0x0B;	/* FF_FAT_PTBL_ID MSDOS data partition */
			p->bIsExtended = 0;
			pPartsFound->iCount = 1;
		}
	} while( pdFALSE );
done:
	if( pxBuffer )
	{
		FF_Error_t xTempError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
		if( FF_isERR( xError ) == pdFALSE )
		{
			xError = xTempError;
		}
	}

	pxIOManager->xPartition.ulTotalSectors = prevTotalSectors;

	return FF_isERR( xError ) ? xError : pPartsFound->iCount;
}	/* FF_PartitionSearch() */
/*-----------------------------------------------------------*/

/*
	Mount GPT Partition Tables
*/
#define FF_GPT_HEAD_ENTRY_SIZE			0x54
#define FF_GPT_HEAD_TOTAL_ENTRIES		0x50
#define FF_GPT_HEAD_PART_ENTRY_LBA		0x48
#define FF_GPT_ENTRY_FIRST_SECTOR_LBA	0x20
#define FF_GPT_HEAD_CRC					0x10
#define FF_GPT_HEAD_LENGTH				0x0C

static FF_Error_t FF_GetEfiPartitionEntry( FF_IOManager_t *pxIOManager, uint32_t ulPartitionNumber )
{
/* Continuing on from FF_Mount() pPartition->ulBeginLBA should be the sector of the GPT Header */
FF_Buffer_t *pxBuffer;
FF_Partition_t *pxPartition = &( pxIOManager->xPartition );

uint32_t ulBeginGPT;
uint32_t ulEntrySector;
uint32_t ulSectorOffset;
uint32_t ulPartitionEntrySize;
uint32_t ulGPTHeadCRC, ulGPTCrcCheck, ulGPTHeadLength;

FF_Error_t xError;

	do
	{
		if( ulPartitionNumber >= 128 )
		{
			xError = FF_ERR_IOMAN_INVALID_PARTITION_NUM | FF_GETEFIPARTITIONENTRY;
			break;
		}
		pxBuffer = FF_GetBuffer( pxIOManager, pxPartition->ulBeginLBA, FF_MODE_READ );
		if( pxBuffer == NULL )
		{
			xError = FF_ERR_DEVICE_DRIVER_FAILED | FF_GETEFIPARTITIONENTRY;
			break;
		}

		/* Verify this is an EFI header with the text "EFI PART": */
		if( memcmp( pxBuffer->pucBuffer, "EFI PART", 8 ) != 0 )
		{
			/* Already returning an error, but this error would override the current one. */
			xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
			if( FF_isERR( xError ) == pdFALSE )
			{
				xError = FF_ERR_IOMAN_INVALID_FORMAT | FF_GETEFIPARTITIONENTRY;
			}
			break;
		}

		ulBeginGPT					= FF_getLong( pxBuffer->pucBuffer, FF_GPT_HEAD_PART_ENTRY_LBA );
		ulPartitionEntrySize		= FF_getLong( pxBuffer->pucBuffer, FF_GPT_HEAD_ENTRY_SIZE );
		ulGPTHeadCRC				= FF_getLong( pxBuffer->pucBuffer, FF_GPT_HEAD_CRC );
		ulGPTHeadLength				= FF_getLong( pxBuffer->pucBuffer, FF_GPT_HEAD_LENGTH );

		/* Calculate Head CRC */
		/* Blank CRC field */
		FF_putLong( pxBuffer->pucBuffer, FF_GPT_HEAD_CRC, 0x00000000 );

		/* Calculate CRC */
		ulGPTCrcCheck = FF_GetCRC32( pxBuffer->pucBuffer, ulGPTHeadLength );

		/* Restore The CRC field */
		FF_putLong( pxBuffer->pucBuffer, FF_GPT_HEAD_CRC, ulGPTHeadCRC );

		xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
		if( FF_isERR( xError ) )
		{
			break;
		}

		/* Check CRC */
		if( ulGPTHeadCRC != ulGPTCrcCheck )
		{
			xError = FF_ERR_IOMAN_GPT_HEADER_CORRUPT | FF_GETEFIPARTITIONENTRY;
			break;
		}

		/* Calculate Sector Containing the Partition Entry we want to use. */
		ulEntrySector = ( ( ulPartitionNumber * ulPartitionEntrySize ) / pxIOManager->usSectorSize ) + ulBeginGPT;
		ulSectorOffset = ( ulPartitionNumber % ( pxIOManager->usSectorSize / ulPartitionEntrySize ) ) * ulPartitionEntrySize;

		pxBuffer = FF_GetBuffer( pxIOManager, ulEntrySector, FF_MODE_READ );
		{
			if( pxBuffer == NULL )
			{
				xError = FF_ERR_DEVICE_DRIVER_FAILED | FF_GETEFIPARTITIONENTRY;
				break;
			}

			pxPartition->ulBeginLBA = FF_getLong( pxBuffer->pucBuffer, ulSectorOffset + FF_GPT_ENTRY_FIRST_SECTOR_LBA );
		}

		xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
		if( FF_isERR( xError ) == pdFALSE )
		{
			if( pxPartition->ulBeginLBA == 0ul )
			{
				xError = FF_ERR_IOMAN_INVALID_PARTITION_NUM | FF_GETEFIPARTITIONENTRY;
			}
		}
	}
	while( pdFALSE );

	return xError;
}	/* FF_GetEfiPartitionEntry() */
/*-----------------------------------------------------------*/

/**
 *	@public
 *	@brief	Mounts the Specified partition, the volume specified by the FF_IOManager_t object provided.
 *
 *	The device drivers must adhere to the specification provided by
 *	FF_WriteBlocks_t and FF_ReadBlocks_t.
 *
 *	@param	pxIOManager			FF_IOManager_t object.
 *	@param	PartitionNumber	The primary or logical partition number to be mounted,
 *                          ranging between 0 and ffconfigMAX_PARTITIONS-1 (normally 0)
 *                          Note that FF_PartitionSearch can be called in advance to
 *                          enumerate all available partitions
 *
 *	@Return	0 on success.
 *	@Return FF_ERR_NULL_POINTER if a pxIOManager object wasn't provided.
 *	@Return FF_ERR_IOMAN_INVALID_PARTITION_NUM if the partition number is out of range.
 *	@Return FF_ERR_IOMAN_NO_MOUNTABLE_PARTITION if no partition was found.
 *	@Return FF_ERR_IOMAN_INVALID_FORMAT if the master boot record or partition boot block didn't provide sensible data.
 *	@Return FF_ERR_IOMAN_NOT_FAT_FORMATTED if the volume or partition couldn't be determined to be FAT. (@see FreeRTOSFATConfig.h)
 *
 **/
FF_Error_t FF_Mount( FF_Disk_t *pxDisk, BaseType_t xPartitionNumber )
{
FF_Partition_t *pxPartition;
FF_Buffer_t *pxBuffer = 0;
FF_Error_t xError = FF_ERR_NONE;
int16_t rootEntryCount;
FF_IOManager_t *pxIOManager = pxDisk->pxIOManager;

/* HT TODO: find a method to safely determine the FAT type: 32/16/12 */
/* other than only counting Clusters */
/*	UBaseType_t		fat32Indicator = 0; */
FF_Part_t *pxMyPartition;
#if( ffconfigHASH_CACHE != 0 )
	BaseType_t i;
#endif
FF_Error_t xPartitionCount = 0;
FF_SPartFound_t partsFound;
partsFound.iCount = 0;

	do
	{
		if( pxIOManager == NULL )
		{
			xError = FF_ERR_NULL_POINTER | FF_MOUNT;
			break;
		}

		pxPartition = &( pxIOManager->xPartition );

		#if( ffconfigREMOVABLE_MEDIA != 0 )
		{
			pxIOManager->ucFlags &= ( uint8_t ) ( ~ ( FF_IOMAN_DEVICE_IS_EXTRACTED ) );
		}
		#endif /* ffconfigREMOVABLE_MEDIA */

		/* FF_IOMAN_InitBufferDescriptors will clear 'pxBuffers' */
		memset( pxIOManager->pucCacheMem, '\0', ( size_t ) pxIOManager->usSectorSize * pxIOManager->usCacheSize );

		#if( ffconfigHASH_CACHE != 0 )
		{
			memset( pxIOManager->xHashCache, '\0', sizeof( pxIOManager->xHashCache ) );
			for( i = 0; i < ffconfigHASH_CACHE_DEPTH; i++ )
			{
				/* _HT_ Check why did JW put it to 100? */
				pxIOManager->xHashCache[ i ].ulMisses = 100;
			}
		}
		#endif
		#if( ffconfigPATH_CACHE != 0 )
		{
			memset( pxPartition->pxPathCache, '\0', sizeof( pxPartition->pxPathCache ) );
		}
		#endif
		FF_IOMAN_InitBufferDescriptors( pxIOManager );
		pxIOManager->FirstFile = 0;

		xPartitionCount = FF_PartitionSearch( pxIOManager, &partsFound );
		if( FF_isERR( xPartitionCount ) )
		{
			xError = xPartitionCount;
			break;
		}

		if( xPartitionCount == 0 )
		{
			xError = FF_ERR_IOMAN_NO_MOUNTABLE_PARTITION | FF_MOUNT;
			break;
		}

		if( xPartitionNumber >= xPartitionCount )
		{
			xError = FF_ERR_IOMAN_INVALID_PARTITION_NUM | FF_MOUNT;
			break;
		}

		pxMyPartition = &( partsFound.pxPartitions[ xPartitionNumber ] );

		pxPartition->ulBeginLBA = pxMyPartition->ulStartLBA;

		if( pxMyPartition->ucPartitionID == 0xEE )
		{
			xError = FF_GetEfiPartitionEntry( pxIOManager, xPartitionNumber );

			if( FF_isERR( xError ) )
			{
				break;
			}
		}

		/* Now we get the Partition sector. */
		pxBuffer = FF_GetBuffer( pxIOManager, pxPartition->ulBeginLBA, FF_MODE_READ );
		if( pxBuffer == NULL )
		{
			xError = FF_ERR_DEVICE_DRIVER_FAILED | FF_MOUNT;
			break;
		}

		pxPartition->usBlkSize = FF_getShort( pxBuffer->pucBuffer, FF_FAT_BYTES_PER_SECTOR );
		if( ( ( pxPartition->usBlkSize % 512 ) != 0 ) || ( pxPartition->usBlkSize == 0 ) )
		{
			/* An error here should override the current error, as its likely fatal. */
			xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
			if( FF_isERR( xError ) == pdFALSE )
			{
				xError = FF_ERR_IOMAN_INVALID_FORMAT | FF_MOUNT;
			}
			break;
		}

		/* Assume FAT16, then we'll adjust if its FAT32 */
		pxPartition->usReservedSectors = FF_getShort( pxBuffer->pucBuffer, FF_FAT_RESERVED_SECTORS );
		pxPartition->ulFATBeginLBA = pxPartition->ulBeginLBA + pxPartition->usReservedSectors;

		pxPartition->ucNumFATS = ( uint8_t ) FF_getShort( pxBuffer->pucBuffer, FF_FAT_NUMBER_OF_FATS );
		pxPartition->ulSectorsPerFAT = ( uint32_t ) FF_getShort( pxBuffer->pucBuffer, FF_FAT_16_SECTORS_PER_FAT );

		pxPartition->ulSectorsPerCluster = FF_getChar( pxBuffer->pucBuffer, FF_FAT_SECTORS_PER_CLUS );

		/* Set the BlockFactor (How many real-blocks in a fake block!). */
		pxPartition->ucBlkFactor = ( uint8_t ) ( pxPartition->usBlkSize / pxIOManager->usSectorSize );
		pxPartition->ulTotalSectors = ( uint32_t ) FF_getShort( pxBuffer->pucBuffer, FF_FAT_16_TOTAL_SECTORS );
		if( pxPartition->ulTotalSectors == 0 )
		{
			pxPartition->ulTotalSectors = FF_getLong( pxBuffer->pucBuffer, FF_FAT_32_TOTAL_SECTORS );
		}

		if( pxPartition->ulSectorsPerFAT == 0 )
		{	/* FAT32 */
			pxPartition->ulSectorsPerFAT = FF_getLong( pxBuffer->pucBuffer, FF_FAT_32_SECTORS_PER_FAT );
			pxPartition->ulRootDirCluster = FF_getLong( pxBuffer->pucBuffer, FF_FAT_ROOT_DIR_CLUSTER );
			memcpy( pxPartition->pcVolumeLabel, pxBuffer->pucBuffer + FF_FAT_32_VOL_LABEL, sizeof( pxPartition->pcVolumeLabel ) - 1 );
		}
		else
		{	/* FAT16 */
			pxPartition->ulRootDirCluster = 1;			/* 1st Cluster is RootDir! */
			memcpy( pxPartition->pcVolumeLabel, pxBuffer->pucBuffer + FF_FAT_16_VOL_LABEL, sizeof( pxPartition->pcVolumeLabel ) - 1);
		}

		pxPartition->ulClusterBeginLBA = pxPartition->ulFATBeginLBA + ( pxPartition->ucNumFATS * pxPartition->ulSectorsPerFAT );
		#if( ffconfigWRITE_FREE_COUNT != 0 )
		{
			pxPartition->ulFSInfoLBA = pxPartition->ulBeginLBA + FF_getShort( pxBuffer->pucBuffer, 48 );
		}
		#endif
		FF_ReleaseBuffer( pxIOManager, pxBuffer );	/* Release the buffer finally! */
		if( pxPartition->usBlkSize == 0 )
		{
			xError = FF_ERR_IOMAN_INVALID_FORMAT | FF_MOUNT;
			break;
		}

		rootEntryCount = FF_getShort( pxBuffer->pucBuffer, FF_FAT_ROOT_ENTRY_COUNT );
		pxPartition->ulRootDirSectors = ( ( rootEntryCount * 32 ) + pxPartition->usBlkSize - 1 ) / pxPartition->usBlkSize;
		pxPartition->ulFirstDataSector = pxPartition->ulClusterBeginLBA + pxPartition->ulRootDirSectors;
		pxPartition->ulDataSectors = pxPartition->ulTotalSectors - ( pxPartition->usReservedSectors + ( pxPartition->ucNumFATS * pxPartition->ulSectorsPerFAT ) + pxPartition->ulRootDirSectors );

		/*
		 * HT: fat32Indicator not yet used
		 * As there is so much confusion about the FAT types
		 * I was thinking of collecting indications for either FAT12, 16 or 32
		 */

		/*
		if( FF_getShort( pxBuffer->pucBuffer, FF_FAT_EXT_BOOT_SIGNATURE ) == 0x29 )
			fat32Indicator++;
		if( rootEntryCount == 0 )
			fat32Indicator++;
		*/
		if( pxPartition->ulSectorsPerCluster == 0 )
		{
			xError = FF_ERR_IOMAN_INVALID_FORMAT | FF_MOUNT;
			break;
		}

		pxPartition->ulNumClusters = pxPartition->ulDataSectors / pxPartition->ulSectorsPerCluster;

		xError = prvDetermineFatType( pxIOManager );
		if( FF_isERR( xError ) )
		{
			break;
		}

		if( !rootEntryCount && pxPartition->ucType != FF_T_FAT32 )
		{
			FF_PRINTF( "No root dir, must be a FAT32\n" );
			pxPartition->ucType = FF_T_FAT32;
		}

		pxPartition->ucPartitionMounted = pdTRUE;
		pxPartition->ulLastFreeCluster = 0;
		#if( ffconfigMOUNT_FIND_FREE != 0 )
		{
			FF_LockFAT( pxIOManager );
			{
				/* The parameter 'pdFALSE' means: do not claim the free cluster found. */
				pxPartition->ulLastFreeCluster = FF_FindFreeCluster( pxIOManager, &xError, pdFALSE );
			}
			FF_UnlockFAT( pxIOManager );

			if( FF_isERR( xError ) )
			{
				if( FF_GETERROR( xError ) == FF_ERR_IOMAN_NOT_ENOUGH_FREE_SPACE )
				{
					pxPartition->ulLastFreeCluster = 0;
				}
				else
				{
					break;
				}
			}

			pxPartition->ulFreeClusterCount = FF_CountFreeClusters( pxIOManager, &xError );
			if( FF_isERR( xError ) )
			{
				break;
			}
		}
		#else
		{
			pxPartition->ulFreeClusterCount = 0;
		}
		#endif	/* ffconfigMOUNT_FIND_FREE */
	}
	while( pdFALSE );

	if( FF_isERR( xError ) == pdFALSE )
	{
		xError = 0;
	}

	return xError;
}	/* FF_Mount() */
/*-----------------------------------------------------------*/

/**
 *	@private
 *	@brief		Checks the cache for Active Handles
 *
 *	@param		pxIOManager FF_IOManager_t Object.
 *
 *	@Return		pdTRUE if an active handle is found, else pdFALSE.
 *
 *	@pre		This function must be wrapped with the cache handling semaphore.
 **/
static BaseType_t prvHasActiveHandles( FF_IOManager_t *pxIOManager )
{
BaseType_t xResult;
FF_Buffer_t *pxBuffer = pxIOManager->pxBuffers;
FF_Buffer_t *pxLastBuffer = pxBuffer + pxIOManager->usCacheSize;

	for( ; ; )
	{
		if( pxBuffer->usNumHandles )
		{
			xResult = pdTRUE;
			break;
		}
		pxBuffer++;
		if( pxBuffer == pxLastBuffer )
		{
			xResult = pdFALSE;
			break;
		}
	}

	return xResult;
}	/* prvHasActiveHandles() */
/*-----------------------------------------------------------*/

/**
 *	@public
 *	@brief	Unmounts the active partition.
 *
 *	@param	pxIOManager	FF_IOManager_t Object.
 *
 *	@Return FF_ERR_NONE on success.
 **/
FF_Error_t FF_Unmount( FF_Disk_t *pxDisk )
{
FF_Error_t xError = FF_ERR_NONE;
FF_IOManager_t *pxIOManager;

#if( ffconfigMIRROR_FATS_UMOUNT != 0 )
	UBaseType_t uxIndex, y;
	FF_Buffer_t	*pxBuffer;
#endif

	if( pxDisk->pxIOManager == NULL )
	{
		xError = FF_ERR_NULL_POINTER | FF_UNMOUNT;
	}
	else if( pxDisk->pxIOManager->xPartition.ucPartitionMounted == 0 )
	{
		xError = FF_ERR_NONE;
	}
	else
	{
		pxIOManager = pxDisk->pxIOManager;
		FF_PendSemaphore( pxIOManager->pvSemaphore );		/* Ensure that there are no File Handles */
		{
			if( prvHasActiveHandles( pxIOManager ) != 0 )
			{
				/* Active handles found on the cache. */
				xError = FF_ERR_IOMAN_ACTIVE_HANDLES | FF_UNMOUNT;
			}
			else if( pxIOManager->FirstFile != NULL )
			{
				/* Open files in this partition. */
				xError = FF_ERR_IOMAN_ACTIVE_HANDLES | FF_UNMOUNT;
			}
			else
			{
				/* Release Semaphore to call this function! */
				FF_ReleaseSemaphore( pxIOManager->pvSemaphore );
				/* Flush any unwritten sectors to disk. */
				xError = FF_FlushCache( pxIOManager );
				/* Reclaim Semaphore */
				FF_PendSemaphore( pxIOManager->pvSemaphore );

				if( FF_isERR( xError ) == pdFALSE )
				{
					pxIOManager->xPartition.ucPartitionMounted = pdFALSE;

					#if( ffconfigMIRROR_FATS_UMOUNT != 0 )
					{
						FF_ReleaseSemaphore( pxIOManager->pvSemaphore );
						for( uxIndex = 0; uxIndex < pxIOManager->xPartition.ulSectorsPerFAT; uxIndex++ )
						{
							pxBuffer = FF_GetBuffer( pxIOManager, pxIOManager->xPartition.ulFATBeginLBA + uxIndex, FF_MODE_READ );
							if( !pxBuffer )
							{
								xError = FF_ERR_DEVICE_DRIVER_FAILED | FF_UNMOUNT;
								break;
							}
							for( y = 0; y < pxIOManager->xPartition.ucNumFATS; y++ )
							{
								FF_BlockWrite( pxIOManager,
									pxIOManager->xPartition.ulFATBeginLBA + ( y * pxIOManager->xPartition.ulSectorsPerFAT ) + uxIndex, 1,
									pxBuffer->pucBuffer, pdFALSE );
							}
						}
						FF_PendSemaphore( pxIOManager->pvSemaphore );
					}
					#endif
				}
			}
		}
		FF_ReleaseSemaphore( pxIOManager->pvSemaphore );
	}

	return xError;
}	/* FF_Unmount() */
/*-----------------------------------------------------------*/

FF_Error_t FF_IncreaseFreeClusters( FF_IOManager_t *pxIOManager, uint32_t Count )
{
FF_Error_t xError;

#if( ffconfigWRITE_FREE_COUNT != 0 )
	FF_Buffer_t	*pxBuffer;
#endif

	do
	{
		/* Open a do {} while( pdFALSE ) loop to allow the use of break statements. */
		if( pxIOManager->xPartition.ulFreeClusterCount == 0ul )
		{
			/* Apparently the number of free clusters has not been calculated yet,
			or no free cluster was available. Now check it. */
			pxIOManager->xPartition.ulFreeClusterCount = FF_CountFreeClusters( pxIOManager, &xError );
			if( FF_isERR( xError ) )
			{
				break;
			}
		}
		else
		{
			xError = FF_ERR_NONE;
			taskENTER_CRITICAL();
			{
				pxIOManager->xPartition.ulFreeClusterCount += Count;
			}
			taskEXIT_CRITICAL();
		}

		if( pxIOManager->xPartition.ulLastFreeCluster == 0 )
		{
		BaseType_t xTakeLock = FF_Has_Lock( pxIOManager, FF_FAT_LOCK ) == pdFALSE;

			if( xTakeLock )
			{
				FF_LockFAT( pxIOManager );
			}
			/* Find the an available cluster. */
			pxIOManager->xPartition.ulLastFreeCluster = FF_FindFreeCluster( pxIOManager, &xError, pdFALSE );
			if( xTakeLock )
			{
				FF_UnlockFAT( pxIOManager );
			}
			if( FF_isERR( xError ) )
			{
				break;
			}
		}

		#if( ffconfigWRITE_FREE_COUNT != 0 )
		{
			/* FAT32 updates the FSINFO sector. */
			if( pxIOManager->xPartition.ucType == FF_T_FAT32 )
			{
				/* Find the FSINFO sector. */
				pxBuffer = FF_GetBuffer( pxIOManager, pxIOManager->xPartition.ulFSInfoLBA, FF_MODE_WRITE );
				if( pxBuffer == NULL )
				{
					xError = FF_ERR_DEVICE_DRIVER_FAILED | FF_INCREASEFREECLUSTERS;
				}
				else
				{
				uint32_t ulSignature1;
				uint32_t ulSignature2;

					ulSignature1 = FF_getLong( pxBuffer->pucBuffer, FS_INFO_OFFSET_SIGNATURE1_000 );
					ulSignature2 = FF_getLong( pxBuffer->pucBuffer, FS_INFO_OFFSET_SIGNATURE2_484 );

					if( ( ulSignature1 == FS_INFO_SIGNATURE1_0x41615252 ) &&
						( ulSignature2 == FS_INFO_SIGNATURE2_0x61417272 ) )
					{
						/* FSINFO sector magic numbers we're verified. Safe to write. */
						FF_putLong( pxBuffer->pucBuffer, FS_INFO_OFFSET_FREE_COUNT_488, pxIOManager->xPartition.ulFreeClusterCount );
						FF_putLong( pxBuffer->pucBuffer, FS_INFO_OFFSET_FREE_CLUSTER_492, pxIOManager->xPartition.ulLastFreeCluster );
					}
					xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
				}
			}
		}
		#endif
	}
	while( pdFALSE );

	return xError;
}	/* FF_IncreaseFreeClusters() */
/*-----------------------------------------------------------*/

FF_Error_t FF_DecreaseFreeClusters( FF_IOManager_t *pxIOManager, uint32_t Count )
{
FF_Error_t	xError = FF_ERR_NONE;
#if( ffconfigWRITE_FREE_COUNT != 0 )
	FF_Buffer_t	*pxBuffer;
#endif

	if( pxIOManager->xPartition.ulFreeClusterCount == 0ul )
	{
		pxIOManager->xPartition.ulFreeClusterCount = FF_CountFreeClusters( pxIOManager, &xError );
	}
	else
	{
		taskENTER_CRITICAL();
		pxIOManager->xPartition.ulFreeClusterCount -= Count;
		taskEXIT_CRITICAL();
	}

	if( FF_isERR( xError ) == pdFALSE )
	{
		if( pxIOManager->xPartition.ulLastFreeCluster == 0 )
		{
			FF_LockFAT( pxIOManager );
			{
				pxIOManager->xPartition.ulLastFreeCluster = FF_FindFreeCluster( pxIOManager, &xError, pdFALSE );
			}
			FF_UnlockFAT( pxIOManager );
		}
	}
	if( FF_isERR( xError ) == pdFALSE )
	{
		#if( ffconfigWRITE_FREE_COUNT != 0 )
		{
			/* FAT32 update the FSINFO sector. */
			if( pxIOManager->xPartition.ucType == FF_T_FAT32 )
			{
				/* Find the FSINFO sector. */
				pxBuffer = FF_GetBuffer( pxIOManager, pxIOManager->xPartition.ulFSInfoLBA, FF_MODE_WRITE );
				if( pxBuffer == NULL )
				{
					xError = FF_ERR_DEVICE_DRIVER_FAILED | FF_DECREASEFREECLUSTERS;
				}
				else
				{
					if( ( FF_getLong( pxBuffer->pucBuffer, FS_INFO_OFFSET_SIGNATURE1_000 ) == FS_INFO_SIGNATURE1_0x41615252 ) &&
						( FF_getLong( pxBuffer->pucBuffer, FS_INFO_OFFSET_SIGNATURE2_484 ) == FS_INFO_SIGNATURE2_0x61417272 ) )
					{
						/* FSINFO sector magic nums we're verified. Safe to write. */
						FF_putLong( pxBuffer->pucBuffer, FS_INFO_OFFSET_FREE_COUNT_488, pxIOManager->xPartition.ulFreeClusterCount );
						FF_putLong( pxBuffer->pucBuffer, FS_INFO_OFFSET_FREE_CLUSTER_492, pxIOManager->xPartition.ulLastFreeCluster );
					}
					xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
				}
			}
		}
		#endif
	}

	return xError;
}	/* FF_DecreaseFreeClusters() */
/*-----------------------------------------------------------*/

/**
 *	@brief	Returns the Block-size of a mounted Partition
 *
 *	The purpose of this function is to provide API access to information
 *	that might be useful in special cases. Like USB sticks that require a sector
 *	knocking sequence for security. After the sector knock, some secure USB
 *	sticks then present a different BlockSize.
 *
 *	@param	pxIOManager		FF_IOManager_t Object returned from FF_CreateIOManger()
 *
 *	@Return	The blocksize of the partition. A value less than 0 when an error occurs.
 *	@Return	Any negative value can be cast to the FF_Error_t type.
 **/
int32_t FF_GetPartitionBlockSize( FF_IOManager_t *pxIOManager )
{
int32_t lReturn;
	if( pxIOManager )
	{
		lReturn = ( int32_t ) pxIOManager->xPartition.usBlkSize;
	}
	else
	{
		lReturn = FF_ERR_NULL_POINTER | FF_GETPARTITIONBLOCKSIZE;
	}

	return lReturn;
}	/* FF_GetPartitionBlockSize() */
/*-----------------------------------------------------------*/

#if( ffconfig64_NUM_SUPPORT != 0 )

	/**
	 *	@brief	Returns the number of bytes contained within the mounted partition or volume.
	 *
	 *	@param	pxIOManager		FF_IOManager_t Object returned from FF_CreateIOManger()
	 *
	 *	@Return The total number of bytes that the mounted partition or volume contains.
	 *
	 **/
	uint64_t FF_GetVolumeSize( FF_IOManager_t *pxIOManager )
	{
	uint64_t ullResult;

		if( pxIOManager )
		{
			uint32_t TotalClusters = ( pxIOManager->xPartition.ulDataSectors / pxIOManager->xPartition.ulSectorsPerCluster );
			ullResult = ( uint64_t )
				(
					( uint64_t ) TotalClusters * ( uint64_t )
						( ( uint64_t ) pxIOManager->xPartition.ulSectorsPerCluster * ( uint64_t ) pxIOManager->xPartition.usBlkSize )
				);
		}
		else
		{
			ullResult = 0ULL;
		}

		return ullResult;
	}	/* FF_GetVolumeSize() */
#else
	uint32_t FF_GetVolumeSize( FF_IOManager_t *pxIOManager )
	{
	uint32_t ulResult;
		if( pxIOManager )
		{
			uint32_t	TotalClusters = pxIOManager->xPartition.ulDataSectors / pxIOManager->xPartition.ulSectorsPerCluster;
			ulResult = ( uint32_t ) ( TotalClusters * ( pxIOManager->xPartition.ulSectorsPerCluster * pxIOManager->xPartition.usBlkSize ) );
		}
		else
		{
			ulResult = 0UL;
		}

		return ulResult;
	}	/* FF_GetVolumeSize() */
#endif
/*-----------------------------------------------------------*/
