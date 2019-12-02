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
 *	@file		ff_fat.c
 *	@ingroup	FAT
 *
 *	@defgroup	FAT Fat File-System
 *	@brief		Handles FAT access and traversal.
 *
 *	Provides file-system interfaces for the FAT file-system.
 **/

#include "ff_headers.h"
#include <string.h>


#if ffconfigFAT_USES_STAT
	/* This module make use of a buffer caching called 'FF_FATBuffers_t'.
	 * The struct below may gather statistics about its usage: hits/misses.
	 */
	struct SFatStat fatStat;
#endif /* ffconfigFAT_USES_STAT */


/* prvGetFromFATBuffers() will see if the FF_Buffer_t pointed to by ppxBuffer contains the
 * buffer that is needed, i.e. opened for the same sector and with the correct R/W mode.
 * If ppxBuffer is NULL or if it can not be used, a new buffer will be created.
 * The buffer pointed to by ppxBuffer will either be released or its pointer will be returned.
 */
FF_Buffer_t *prvGetFromFATBuffers( FF_IOManager_t *pxIOManager, FF_FATBuffers_t *pxFATBuffers, BaseType_t xBufferIndex, uint32_t ulFATSector,
	FF_Error_t *pxError, uint8_t ucMode );

#if( ffconfigFAT12_SUPPORT != 0 )
	/* A very special case for FAT12: an entry is stored in two sectors.
	 * Read the two sectors and merge the two values found.
	 */
	static uint32_t prvGetFAT12Entry( FF_IOManager_t *pxIOManager, FF_Error_t *pxError, FF_FATBuffers_t *pxFATBuffers, uint32_t ulFATSector );
#endif

#if( ffconfigFAT12_SUPPORT != 0 )
	/* Same as above: put a FAT12 entry that is spread-out over two sectors.
	 * Read the current value first to preserve and merge the earlier 4 bits
	 * of an adjacent FAT12 entry.
	 */
	static FF_Error_t prvPutFAT12Entry( FF_IOManager_t *pxIOManager, uint32_t ulCluster, uint32_t ulValue, FF_FATBuffers_t *pxFATBuffers,
		uint32_t ulFATSector );
#endif

#if( ffconfigFAT12_SUPPORT != 0 )
	/* A generic less-optimised way of finding the first free cluster.
	 * Used for FAT12 only.
	 */
	static uint32_t prvFindFreeClusterSimple( FF_IOManager_t *pxIOManager, FF_Error_t *pxError );
#endif	/* ffconfigFAT12_SUPPORT */

#if( ffconfigFAT12_SUPPORT != 0 )
	/* A generic less-optimised way of counting free clusters.
	 * Used for FAT12 only.
	 */
	static uint32_t prvCountFreeClustersSimple( FF_IOManager_t *pxIOManager, FF_Error_t *pxError );
#endif	/* ffconfigFAT12_SUPPORT */



/* Have a cluster number and translate it to an LBA (Logical Block Address).
'ulSectorsPerCluster' should be seen as 'blocks per cluster', where the length of one
block is defined in the PBR (Partition Boot Record) at FF_FAT_BYTES_PER_SECTOR (offset 0x0B).
*/
uint32_t FF_Cluster2LBA( FF_IOManager_t *pxIOManager, uint32_t ulCluster )
{
uint32_t ulLBA = 0;
FF_Partition_t *pxPartition;

	if( pxIOManager != NULL )
	{
		pxPartition = &( pxIOManager->xPartition );

		if( ulCluster >= 2 )
		{
			ulLBA = ( ( ulCluster - 2 ) * pxPartition->ulSectorsPerCluster ) + pxPartition->ulFirstDataSector;
		}
		else
		{
			ulLBA = pxPartition->ulClusterBeginLBA;
		}
	}

	return ulLBA;
}
/*-----------------------------------------------------------*/

/*
 * Major and Minor sectors/blocks:
 *
 * A cluster is defined as N "sectors". Those sectors in fact are "major blocks"
 * whose size is defined in a field called 'FF_FAT_BYTES_PER_SECTOR' in the PBR.
 *
 * I/O to the disk takes place in "minor block" of usually 512 byte and the addressing
 * is also based on "minor block" sector numbers.
 *
 * In most cases, Major == Minor == 512 bytes.
 *
 * Here below some translations are done for 'entries', which can be 1-byte entries
 * as well as the 32-byte directory entries.
 *
 */

/* Translate an 'entry number' (ulEntry) to a relative cluster number,
where e.g. 'ulEntry' may be a sequence number of a directory entry for
which ulEntrySize = 32 bytes.
*/
uint32_t FF_getClusterChainNumber( FF_IOManager_t *pxIOManager, uint32_t ulEntry, uint32_t ulEntrySize )
{
uint32_t ulBytesPerCluster = pxIOManager->xPartition.usBlkSize * pxIOManager->xPartition.ulSectorsPerCluster;
uint32_t ulEntriesPerCluster =  ( ulBytesPerCluster / ulEntrySize );

	/* E.g. ulBytesPerCluster = 16384, ulEntrySize = 32: 16384 / 32 = 512 entries per cluster. */
	return ulEntry / ulEntriesPerCluster;
}
/*-----------------------------------------------------------*/

/* If the above function returns a cluster number, this function
returns a BYTE position within that cluster. */
uint32_t FF_getClusterPosition( FF_IOManager_t *pxIOManager, uint32_t ulEntry, uint32_t ulEntrySize )
{
uint32_t ulBytesPerCluster = pxIOManager->xPartition.usBlkSize * pxIOManager->xPartition.ulSectorsPerCluster;
uint32_t ulEntriesPerCluster =  ( ulBytesPerCluster / ulEntrySize );

	/* Return the block offset within the current cluster: */
	return ( ulEntry % ulEntriesPerCluster ) * ulEntrySize;
}
/*-----------------------------------------------------------*/

/* Return the block offset (= number of major blocks) within the current cluster: */
uint32_t FF_getMajorBlockNumber( FF_IOManager_t *pxIOManager, uint32_t ulEntry, uint32_t ulEntrySize )
{
uint32_t ulBytesPerCluster = pxIOManager->xPartition.usBlkSize * pxIOManager->xPartition.ulSectorsPerCluster;
uint32_t ulEntriesPerCluster = ( ulBytesPerCluster / ulEntrySize );
uint32_t ulRelClusterEntry;

	/* Calculate the entry number within a cluster: */
	ulRelClusterEntry = ulEntry % ulEntriesPerCluster;

	/* Return the block offset within the current cluster: */
	return ulRelClusterEntry / ( pxIOManager->xPartition.usBlkSize / ulEntrySize );
}
/*-----------------------------------------------------------*/

/* Return the minor block number within the current major block */
uint32_t FF_getMinorBlockNumber( FF_IOManager_t *pxIOManager, uint32_t ulEntry, uint32_t ulEntrySize )
{
uint32_t ulBytesPerCluster = pxIOManager->xPartition.usBlkSize * pxIOManager->xPartition.ulSectorsPerCluster;
uint32_t ulEntriesPerCluster = ( ulBytesPerCluster / ulEntrySize );
uint32_t ulRelClusterEntry;
uint32_t ulRelMajorBlockEntry;

	/* Calculate the entry number within a cluster: */
	ulRelClusterEntry = ulEntry % ulEntriesPerCluster;

	ulRelMajorBlockEntry = ulRelClusterEntry % ( pxIOManager->xPartition.usBlkSize / ulEntrySize );

	return ulRelMajorBlockEntry / ( pxIOManager->usSectorSize / ulEntrySize );
}
/*-----------------------------------------------------------*/

/* Get the entry number within the minor block */
uint32_t FF_getMinorBlockEntry( FF_IOManager_t *pxIOManager, uint32_t ulEntry, uint32_t ulEntrySize )
{
uint32_t ulBytesPerCluster = pxIOManager->xPartition.usBlkSize * pxIOManager->xPartition.ulSectorsPerCluster;
uint32_t ulEntriesPerCluster =  ( ulBytesPerCluster / ulEntrySize );
uint32_t ulRelClusterEntry;
uint32_t ulRelMajorBlockEntry;

	/* Calculate the entry number within a cluster: */
	ulRelClusterEntry = ulEntry % ulEntriesPerCluster;

	ulRelMajorBlockEntry = ulRelClusterEntry % ( pxIOManager->xPartition.usBlkSize / ulEntrySize );

	return ulRelMajorBlockEntry % ( pxIOManager->usSectorSize / ulEntrySize );
}
/*-----------------------------------------------------------*/

FF_Error_t FF_ReleaseFATBuffers( FF_IOManager_t *pxIOManager, FF_FATBuffers_t *pxFATBuffers )
{
BaseType_t xIndex;
FF_Error_t xError = FF_ERR_NONE;
FF_Buffer_t *pxBuffer;
#if ffconfigBUF_STORE_COUNT != 2
	#warning Only maintaining one FAT table
#endif
	/* 'ffconfigBUF_STORE_COUNT' equals to the number of FAT tables. */
	for( xIndex = 0; xIndex < ffconfigBUF_STORE_COUNT; xIndex++ )
	{
		pxBuffer = pxFATBuffers->pxBuffers[ xIndex ];
		if( pxBuffer != NULL )
		{
		FF_Error_t xTempError = FF_ERR_NONE;

			pxFATBuffers->pxBuffers[ xIndex ] = NULL;
			xTempError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
			if( FF_isERR( xError ) == pdFALSE )
			{
				/* as everywhere, this function will return
				the first error that occurred, if any. */
				xError = xTempError;
			}
		}
	}
	#if ffconfigFAT_USES_STAT
	{
		fatStat.clearCount++;
	}
	#endif /* ffconfigFAT_USES_STAT */

	return xError;
}
/*-----------------------------------------------------------*/

FF_Buffer_t *prvGetFromFATBuffers( FF_IOManager_t *pxIOManager, FF_FATBuffers_t *pxFATBuffers, BaseType_t xBufferIndex,
	uint32_t ulFATSector, FF_Error_t *pxError, uint8_t ucMode )
{
FF_Error_t xError = FF_ERR_NONE;
FF_Buffer_t *pxBuffer = NULL;

	if( pxFATBuffers != NULL )
	{
		/* See if the same buffer can be reused. */
		pxBuffer = pxFATBuffers->pxBuffers[ xBufferIndex ];

		if( pxBuffer != NULL )
		{
			/* Now the buffer is either owned by pxBuffer,
			or it has been released, so put it to NULL. */
			pxFATBuffers->pxBuffers[ xBufferIndex ] = NULL;

			if(
				( pxBuffer->ulSector == ulFATSector ) &&
				( ( ( ucMode & FF_MODE_WRITE ) == 0 ) ||
				  ( ( pxBuffer->ucMode & FF_MODE_WRITE ) != 0 ) )
			)
			{
				/* Same sector, AND
				write-permission is not required OR the buffer has write permission:
				it can be reused. */
				#if ffconfigFAT_USES_STAT
				{
					fatStat.reuseCount[ ( ucMode & FF_MODE_WRITE ) ? 1 : 0 ]++;
				}
				#endif /* ffconfigFAT_USES_STAT */
			}
			else
			{
				xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
				pxBuffer = NULL;
				#if ffconfigFAT_USES_STAT
				{
					fatStat.missCount[ ( ucMode & FF_MODE_WRITE ) ? 1 : 0 ]++;
				}
				#endif /* ffconfigFAT_USES_STAT */
			}
		}
		else
		{
			#if ffconfigFAT_USES_STAT
			{
				fatStat.getCount[ ( ucMode & FF_MODE_WRITE ) ? 1 : 0 ]++;
			}
			#endif /* ffconfigFAT_USES_STAT */
		}
	}

	if( ( pxBuffer == NULL ) && ( FF_isERR( xError ) == pdFALSE ) )
	{
		pxBuffer = FF_GetBuffer( pxIOManager, ulFATSector, ucMode );
		if( pxBuffer == NULL )
		{
			/* Setting an error code without the Module/Function,
			will be filled-in by the caller. */
			xError = ( FF_Error_t ) ( FF_ERR_DEVICE_DRIVER_FAILED | FF_ERRFLAG );
		}
	}
	*pxError = xError;

	return pxBuffer;
}

#if( ffconfigFAT12_SUPPORT != 0 )
	/* A very special case for FAT12: an entry is stored in two sectors.
	Read the two sectors and merge the two values found. */
	static uint32_t prvGetFAT12Entry( FF_IOManager_t *pxIOManager, FF_Error_t *pxError, FF_FATBuffers_t *pxFATBuffers,
		uint32_t ulFATSector )
	{
	FF_Error_t xError = FF_ERR_NONE;
	FF_Buffer_t *pxBuffer = NULL;
	/* preferred buffer access mode, user might want to update this entry
	and set it to FF_MODE_WRITE. */
	uint8_t ucMode = pxFATBuffers ? pxFATBuffers->ucMode : FF_MODE_READ;
	/* Collect the two bytes in an array. */
	uint8_t ucBytes[ 2 ];
	/* The function return value. */
	uint32_t ulFATEntry = 0UL;

		pxBuffer = prvGetFromFATBuffers( pxIOManager, pxFATBuffers, 0, ulFATSector, &xError, ucMode );

		if( FF_isERR( xError ) )
		{
			xError = FF_GETERROR( xError ) | FF_GETFATENTRY;
		}
		else
		{
			/* Fetch the very last byte of this segment. */
			ucBytes[ 0 ] = FF_getChar( pxBuffer->pucBuffer, ( uint16_t ) ( pxIOManager->usSectorSize - 1 ) );

			xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );

			/* release the other buffer as well. */
			if( ( FF_isERR( xError ) == pdFALSE ) && ( pxFATBuffers != NULL ) )
			{
				xError = FF_ReleaseFATBuffers( pxIOManager, pxFATBuffers );
			}

			if( FF_isERR( xError ) == pdFALSE )
			{
				/* Second Buffer get the first Byte in buffer (second byte of out address)! */
				pxBuffer = FF_GetBuffer( pxIOManager, ulFATSector + 1, ucMode );
				if( pxBuffer == NULL )
				{
					xError = ( FF_Error_t ) ( FF_ERR_DEVICE_DRIVER_FAILED | FF_GETFATENTRY );
				}
				else
				{
					/* Read the first byte from the subsequent sector. */
					ucBytes[ 1 ] = FF_getChar( pxBuffer->pucBuffer, 0 );
					/* And release that buffer. */
					xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
					if( FF_isERR( xError ) == pdFALSE )
					{
						/* Join the two bytes: */
						ulFATEntry = ( uint32_t ) FF_getShort( ( uint8_t * )ucBytes, 0 );
					}
				}
			}
		}
		*pxError = xError;

		return ( int32_t ) ulFATEntry;
	}
#endif	/* ffconfigFAT12_SUPPORT */
/*-----------------------------------------------------------*/


/* Get a FAT entry, which is nothing more than a number referring to a sector. */
uint32_t FF_getFATEntry( FF_IOManager_t *pxIOManager, uint32_t ulCluster, FF_Error_t *pxError, FF_FATBuffers_t *pxFATBuffers )
{
FF_Buffer_t *pxBuffer = NULL;
uint32_t ulFATOffset;
uint32_t ulFATSector = 0;
uint32_t ulFATSectorEntry;
/* The function result. */
uint32_t ulFATEntry = 0;
uint32_t ulLBAAdjust;
uint32_t ulRelClusterEntry = 0;
FF_Error_t xError = FF_ERR_NONE;
/* preferred mode, user might want to update this entry. */
uint8_t ucMode = pxFATBuffers ? pxFATBuffers->ucMode : FF_MODE_READ;

	FF_Assert_Lock( pxIOManager, FF_FAT_LOCK );

	if( ulCluster >= pxIOManager->xPartition.ulNumClusters )
	{
		/* _HT_ find a more specific error code.
		Probably not really important as this is a function internal to the library. */
		xError = ( FF_Error_t ) ( FF_ERR_IOMAN_NOT_ENOUGH_FREE_SPACE | FF_GETFATENTRY );
	}
	else
	{
		if( pxIOManager->xPartition.ucType == FF_T_FAT32 )
		{
			ulFATOffset = ulCluster * 4;
		}
		else if( pxIOManager->xPartition.ucType == FF_T_FAT16 )
		{
			ulFATOffset = ulCluster * 2;
		}
		else /* pxIOManager->xPartition.ucType == FF_T_FAT12 */
		{
			ulFATOffset = ulCluster + ( ulCluster / 2 );
		}

		ulFATSector = pxIOManager->xPartition.ulFATBeginLBA + ( ulFATOffset / pxIOManager->xPartition.usBlkSize );
		ulFATSectorEntry = ulFATOffset % pxIOManager->xPartition.usBlkSize;

		ulLBAAdjust = ulFATSectorEntry / ( ( uint32_t ) pxIOManager->usSectorSize );
		ulRelClusterEntry = ulFATSectorEntry % pxIOManager->usSectorSize;

		ulFATSector = FF_getRealLBA( pxIOManager, ulFATSector );
		ulFATSector += ulLBAAdjust;
	}

#if( ffconfigFAT12_SUPPORT != 0 )
	if( ( pxIOManager->xPartition.ucType == FF_T_FAT12 ) &&
		( FF_isERR( xError ) == pdFALSE ) &&
		( ulRelClusterEntry == ( uint32_t ) ( ( pxIOManager->usSectorSize - 1 ) ) ) )
	{
		/* Fat Entry SPANS a Sector!
		It has 4 bits on one sector and 8 bits on the other sector.
		Handle this in a separate function prvGetFAT12Entry(). */
		ulFATEntry = prvGetFAT12Entry( pxIOManager, &xError, pxFATBuffers, ulFATSector );

		if( ( ulCluster & 0x0001 ) != 0 )
		{
			/* For odd clusters, shift the address 4 bits to the right: */
			ulFATEntry = ( ulFATEntry & 0xfff0 ) >> 4;
		}
		else
		{
			/* For even clusters, take the lower 12 bits: */
			ulFATEntry = ( ulFATEntry & 0x0fff );
		}
		/* Return ulFATEntry, unless xError contains an error. */
	}
	else
#endif /* ffconfigFAT12_SUPPORT */
	if( FF_isERR( xError ) == pdFALSE )
	{
		/* Handle FAT16, FAT32, and FAT12 (in case the entry lies on a single sector). */

		pxBuffer = prvGetFromFATBuffers( pxIOManager, pxFATBuffers, 0, ulFATSector, &xError, ucMode );
		if( FF_isERR( xError ) )
		{
			xError = FF_GETERROR( xError ) | FF_GETFATENTRY;
		}
		else
		{
			switch( pxIOManager->xPartition.ucType )
			{
				case FF_T_FAT32:
					ulFATEntry = FF_getLong( pxBuffer->pucBuffer, ulRelClusterEntry );
					/* Clear the top 4 bits. */
					ulFATEntry &= 0x0fffffff;
					break;
				case FF_T_FAT16:
					ulFATEntry = ( uint32_t ) FF_getShort( pxBuffer->pucBuffer, ulRelClusterEntry );
					break;
			#if( ffconfigFAT12_SUPPORT != 0 )
				case FF_T_FAT12:
					ulFATEntry = ( uint32_t ) FF_getShort( pxBuffer->pucBuffer, ulRelClusterEntry );
					/* Entries are either stored as 4 + 8 bits or as 8 + 4 bits,
					depending on the cluster being odd or even.						*/
					if( ( ulCluster & 0x0001 ) != 0 )
					{
						/* For odd clusters, shift the address 4 bits to the right: */
						ulFATEntry = ( ulFATEntry & 0xfff0 ) >> 4;
					}
					else
					{
						/* For even clusters, take the lower 12 bits: */
						ulFATEntry = ( ulFATEntry & 0x0fff );
					}
					break;
			#endif
				default:
					ulFATEntry = 0;
					break;
			}

			if( pxFATBuffers != NULL )
			{
				/* Store the buffer. */
				pxFATBuffers->pxBuffers[ 0 ] = pxBuffer;
			}
			else
			{
				/* Or release it. */
				xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
			}
		}	/* if( FF_isERR( xError ) == pdFALSE ) */
	}	/* else Handle FAT16, FAT32, and FAT12 (in case the entry lies on a single sector). */

	if( FF_isERR( xError ) )
	{
		/* The sector address 0 is not meaningful and here it is used as the 'error value'. */
		ulFATEntry = 0UL;
	}

	if( pxError != NULL )
	{
		*pxError = xError;
	}

	return ( int32_t )ulFATEntry;
}	/* FF_getFATEntry() */
/*-----------------------------------------------------------*/

/* Write all zero's to all sectors of a given cluster. */
FF_Error_t FF_ClearCluster( FF_IOManager_t *pxIOManager, uint32_t ulCluster )
{
FF_Error_t xError = FF_ERR_NONE;
FF_Buffer_t *pxBuffer = NULL;
BaseType_t xIndex;
uint32_t ulBaseLBA;

	/* Calculate from cluster number to a real block address. */
	ulBaseLBA = FF_Cluster2LBA( pxIOManager, ulCluster );
	ulBaseLBA = FF_getRealLBA( pxIOManager, ulBaseLBA );

	for( xIndex = 0; xIndex < ( BaseType_t ) pxIOManager->xPartition.ulSectorsPerCluster; xIndex++ )
	{
		if( xIndex == 0 )
		{
			/* When using the FF_MODE_WR_ONLY flag, the data will not be read from disk.
			Only in the first round a buffer will be claimed. */
			pxBuffer = FF_GetBuffer( pxIOManager, ulBaseLBA, FF_MODE_WR_ONLY );
			if( pxBuffer == NULL )
			{
				xError = ( FF_Error_t ) ( FF_ERR_DEVICE_DRIVER_FAILED | FF_CLEARCLUSTER );
				break;
			}
			memset( pxBuffer->pucBuffer, 0x00, pxIOManager->usSectorSize );
		}

		xError = FF_BlockWrite( pxIOManager, ulBaseLBA + xIndex, 1, pxBuffer->pucBuffer, pdFALSE );
		if( FF_isERR( xError ) )
		{
			break;
		}
	}

	if( pxBuffer != NULL )
	{
	FF_Error_t xTempError;

		/* The contents of the buffer (all zero's) has been written explicitly to disk
		by calling FF_BlockWrite().  Therefore, the bModified should be cleared. */
		pxBuffer->bModified = pdFALSE;
		/* Releasing the handle will not write anything */
		xTempError = FF_ReleaseBuffer( pxIOManager, pxBuffer );

		if( FF_isERR( xError ) == pdFALSE )
		{
			xError = xTempError;
		}
	}

	return xError;
}
/*-----------------------------------------------------------*/

/**
 *	@private
 *	@brief	Returns the Cluster address of the Cluster number from the beginning of a chain.
 *
 *	@param	pxIOManager	FF_IOManager_t Object
 *	@param	ulStart		Cluster address of the first cluster in the chain.
 *	@param	ulCount		Number of Cluster in the chain,
 *
 *
 *
 **/
uint32_t FF_TraverseFAT( FF_IOManager_t *pxIOManager, uint32_t ulStart, uint32_t ulCount, FF_Error_t *pxError )
{
FF_Error_t xError = FF_ERR_NONE;
uint32_t ulIndex;
uint32_t ulFatEntry = ulStart;
uint32_t ulCurrentCluster = ulStart;
FF_FATBuffers_t xFATBuffers;
BaseType_t xTakeLock = FF_Has_Lock( pxIOManager, FF_FAT_LOCK ) == pdFALSE;

	/* xFATBuffers is nothing more than an array of FF_Buffer_t's.
	One buffer for each FAT copy on disk. */
	FF_InitFATBuffers( &xFATBuffers, FF_MODE_READ );

	if( xTakeLock )
	{
		FF_LockFAT( pxIOManager );
	}
	for( ulIndex = 0; ulIndex < ulCount; ulIndex++ )
	{
		ulFatEntry = FF_getFATEntry( pxIOManager, ulCurrentCluster, &xError, &xFATBuffers );
		if( FF_isERR( xError ) )
		{
			ulFatEntry = 0;
			break;
		}

		if( FF_isEndOfChain( pxIOManager, ulFatEntry ) )
		{
			ulFatEntry = ulCurrentCluster;
			break;
		}

		ulCurrentCluster = ulFatEntry;
	}
	if( xTakeLock )
	{
		FF_UnlockFAT( pxIOManager );
	}

	{
	FF_Error_t xTempError;

		xTempError = FF_ReleaseFATBuffers( pxIOManager, &xFATBuffers );
		if( FF_isERR( xError ) == pdFALSE )
		{
			xError = xTempError;
		}
	}

	*pxError = xError;

	return ulFatEntry;
}
/*-----------------------------------------------------------*/

uint32_t FF_FindEndOfChain( FF_IOManager_t *pxIOManager, uint32_t ulStart, FF_Error_t *pxError )
{
uint32_t ulFatEntry = ulStart;
FF_Error_t xError;

	if( FF_isEndOfChain( pxIOManager, ulStart ) == pdFALSE )
	{
		/* Traverse FAT for (2^32-1) items/clusters,
		or until end-of-chain is encountered. */
		ulFatEntry = FF_TraverseFAT( pxIOManager, ulStart, ~0UL, &xError );
	}
	else
	{
		xError = FF_ERR_NONE;
	}

	*pxError = xError;

	return ulFatEntry;
}
/*-----------------------------------------------------------*/

/**
 *	@private
 *	@brief	Tests if the ulFATEntry is an End of Chain Marker.
 *
 *	@param	pxIOManager	FF_IOManager_t Object
 *	@param	ulFATEntry	The fat entry from the FAT table to be checked.
 *
 *	@return	pdTRUE if it is an end of chain, otherwise pdFALSE.
 *
 **/
BaseType_t FF_isEndOfChain( FF_IOManager_t *pxIOManager, uint32_t ulFATEntry )
{
BaseType_t	xResult = pdFALSE;

	if( pxIOManager->xPartition.ucType == FF_T_FAT32 )
	{
		if( ( ulFATEntry & 0x0fffffff ) >= 0x0ffffff8 )
		{
			xResult = pdTRUE;
		}
	}
	else if( pxIOManager->xPartition.ucType == FF_T_FAT16 )
	{
		if( ulFATEntry >= 0x0000fff8 )
		{
			xResult = pdTRUE;
		}
	}
	else
	{
		if( ulFATEntry >= 0x00000ff8 )
		{
			xResult = pdTRUE;
		}
	}

	if( ulFATEntry == 0x00000000 )
	{
		xResult = pdTRUE;	/* Perhaps trying to read a deleted file! */
	}

	return xResult;
}
/*-----------------------------------------------------------*/

#if( ffconfigFAT12_SUPPORT != 0 )
	static FF_Error_t prvPutFAT12Entry( FF_IOManager_t *pxIOManager, uint32_t ulCluster, uint32_t ulValue, FF_FATBuffers_t *pxFATBuffers,
		uint32_t ulFATSector )
	{
	FF_Buffer_t *pxBuffer = NULL;
	/* For FAT12 FAT Table Across sector boundary traversal. */
	uint8_t ucBytes[ 2 ];
	/* The function result value. */
	uint32_t ulFATEntry;
	FF_Error_t xError = FF_ERR_NONE;
	BaseType_t xIndex;
	#if( ffconfigWRITE_BOTH_FATS != 0 )
		const BaseType_t xNumFATs = pxIOManager->xPartition.ucNumFATS;
	#else
		const BaseType_t xNumFATs = 1;
	#endif

		/* This routine will only change 12 out of 16 bits.
		Get the current 16-bit value, 4 bits shall be preserved. */
		ulFATEntry = prvGetFAT12Entry( pxIOManager, &xError, pxFATBuffers, ulFATSector );

		if( FF_isERR( xError ) == pdFALSE )
		{
			if( ( ulCluster & 0x0001 ) != 0 )
			{
				 ulFATEntry &= 0x000F;
				 ulValue	 = ( ulValue << 4 );
				 ulValue    &= 0xFFF0;
			}
			else
			{
				 ulFATEntry	&= 0xF000;
				 ulValue	&= 0x0FFF;
			}
			ulFATEntry |= ulValue;

			/* Write at offset 0 in the array ucBytes. */
			FF_putShort( ucBytes, 0, ( uint16_t ) ulFATEntry );

			for( xIndex = 0;
				 xIndex < xNumFATs;
				 xIndex++, ulFATSector += pxIOManager->xPartition.ulSectorsPerFAT )
			{
				/* Write the last byte in the first sector. */
				pxBuffer = FF_GetBuffer( pxIOManager, ulFATSector, FF_MODE_WRITE );
				{
					if( pxBuffer == NULL )
					{
						xError = ( FF_Error_t ) ( FF_ERR_DEVICE_DRIVER_FAILED | FF_PUTFATENTRY );
						break;
					}
					FF_putChar( pxBuffer->pucBuffer, ( uint16_t )( pxIOManager->usSectorSize - 1 ), ucBytes[ 0 ] );
				}
				xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
				if( FF_isERR( xError ) )
				{
					break;
				}

				/* Write the first byte in the subsequent sector. */
				pxBuffer = FF_GetBuffer( pxIOManager, ulFATSector + 1, FF_MODE_WRITE );
				{
					if( pxBuffer == NULL )
					{
						xError = ( FF_Error_t ) ( FF_ERR_DEVICE_DRIVER_FAILED | FF_PUTFATENTRY );
						break;
					}
					FF_putChar( pxBuffer->pucBuffer, 0x0000, ucBytes[ 1 ] );
				}
				xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
				if( FF_isERR( xError ) )
				{
					break;
				}
			} /* for ( xIndex = 0; xIndex < xNumFATs; xIndex++ ) */
		}

		return xError;
	}
#endif

/**
 *	@private
 *	@brief	Writes a new Entry to the FAT Tables.
 *
 *	@param	pxIOManager		IOMAN object.
 *	@param	ulCluster	Cluster Number to be modified.
 *	@param	ulValue		The value to store.
 **/
FF_Error_t FF_putFATEntry( FF_IOManager_t *pxIOManager, uint32_t ulCluster, uint32_t ulValue, FF_FATBuffers_t *pxFATBuffers )
{
FF_Buffer_t *pxBuffer;
uint32_t ulFATOffset;
uint32_t ulFATSector = 0;
uint32_t ulFATSectorEntry;
uint32_t ulFATEntry;
uint32_t ulLBAAdjust;
uint32_t ulRelClusterEntry = 0;
BaseType_t xIndex;
FF_Error_t xError = FF_ERR_NONE;
#if( ffconfigWRITE_BOTH_FATS != 0 )
	const BaseType_t xNumFATs = pxIOManager->xPartition.ucNumFATS;
#else
	const BaseType_t xNumFATs = 1;
#endif


	FF_Assert_Lock( pxIOManager, FF_FAT_LOCK );

	/* Avoid corrupting the disk. */
	if( ( ulCluster == 0ul ) || ( ulCluster >= pxIOManager->xPartition.ulNumClusters ) )
	{
		/* find a more specific error code. */
		xError = ( FF_Error_t ) ( FF_ERR_IOMAN_NOT_ENOUGH_FREE_SPACE | FF_PUTFATENTRY );
	}
	else
	{
		if( pxIOManager->xPartition.ucType == FF_T_FAT32 )
		{
			ulFATOffset = ulCluster * 4;
		}
		else if( pxIOManager->xPartition.ucType == FF_T_FAT16 )
		{
			ulFATOffset = ulCluster * 2;
		}
		else /* pxIOManager->xPartition.ucType == FF_T_FAT12 */
		{
			ulFATOffset = ulCluster + ( ulCluster / 2 );
		}

		ulFATSector = pxIOManager->xPartition.ulFATBeginLBA + ( ulFATOffset / pxIOManager->xPartition.usBlkSize );
		ulFATSectorEntry = ulFATOffset % pxIOManager->xPartition.usBlkSize;

		ulLBAAdjust = ulFATSectorEntry / ( ( uint32_t ) pxIOManager->usSectorSize );
		ulRelClusterEntry = ulFATSectorEntry % pxIOManager->usSectorSize;

		ulFATSector = FF_getRealLBA( pxIOManager, ulFATSector );
		ulFATSector += ulLBAAdjust;
	}

#if( ffconfigFAT12_SUPPORT != 0 )
	if( ( pxIOManager->xPartition.ucType == FF_T_FAT12 ) &&
		( FF_isERR( xError ) == pdFALSE ) &&
		( ulRelClusterEntry == ( uint32_t ) ( ( pxIOManager->usSectorSize - 1 ) ) ) )
	{
		/* The special case in which one FAT12 entries is divided over 2 sectors.
		Treat this in a separate function. */
		xError = prvPutFAT12Entry( pxIOManager, ulCluster, ulValue, pxFATBuffers, ulFATSector );
		/* Return xError. */
	}
	else
#endif /* ffconfigFAT12_SUPPORT */
	if( FF_isERR( xError ) == pdFALSE )
	{
		/* Handle FAT16, FAT32, and FAT12 (in case the entry lies on a single sector). */
		for( xIndex = 0;
			 xIndex < xNumFATs;
			 xIndex++, ulFATSector += pxIOManager->xPartition.ulSectorsPerFAT )
		{
			pxBuffer = prvGetFromFATBuffers( pxIOManager, pxFATBuffers, xIndex, ulFATSector, &xError, FF_MODE_WRITE );

			if( FF_isERR( xError ) )
			{
				xError = FF_GETERROR( xError ) | FF_PUTFATENTRY;
				break;
			}

			if( pxIOManager->xPartition.ucType == FF_T_FAT32 )
			{
				/* Clear the top 4 bits. */
				ulValue &= 0x0fffffff;
				FF_putLong( pxBuffer->pucBuffer, ulRelClusterEntry, ulValue );
			}
			else if( pxIOManager->xPartition.ucType == FF_T_FAT16 )
			{
				FF_putShort( pxBuffer->pucBuffer, ulRelClusterEntry, ( uint16_t ) ulValue );
			}
			else
			{
				ulFATEntry	= ( uint32_t ) FF_getShort( pxBuffer->pucBuffer, ulRelClusterEntry );
				if( ( ulCluster & 0x0001 ) != 0 )
				{
					ulFATEntry &= 0x000F;
					ulValue		= ( ulValue << 4 );
					ulValue	   &= 0xFFF0;
				}
				else
				{
					ulFATEntry	&= 0xF000;
					ulValue		&= 0x0FFF;
				}

				FF_putShort( pxBuffer->pucBuffer, ulRelClusterEntry, ( uint16_t ) ( ulFATEntry | ulValue ) );
			}

			if( ( xIndex < ffconfigBUF_STORE_COUNT ) && ( pxFATBuffers != NULL ) )
			{
				/* Store it for later use. */
				pxFATBuffers->pxBuffers[ xIndex ] = pxBuffer;
				pxFATBuffers->ucMode = FF_MODE_WRITE;
			}
			else
			{
				xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
				if( FF_isERR( xError ) )
				{
					break;
				}
			}
		}
	}

	/* FF_putFATEntry() returns just an error code, not an address. */
	return xError;
}	/* FF_putFATEntry() */
/*-----------------------------------------------------------*/

/**
 *	@private
 *	@brief	Finds a Free Cluster and returns its number.
 *
 *	@param	pxIOManager	IOMAN Object.
 *
 *	@return	The number of the cluster found to be free.
 *	@return 0 on error.
 **/
#if( ffconfigFAT12_SUPPORT != 0 )
	static uint32_t prvFindFreeClusterSimple( FF_IOManager_t *pxIOManager, FF_Error_t *pxError )
	{
	FF_Error_t xError = FF_ERR_NONE;
	uint32_t ulCluster = 0;
	uint32_t ulFATEntry;
	FF_FATBuffers_t xFATBuffers;

		FF_InitFATBuffers( &xFATBuffers, FF_MODE_READ );

		for( ulCluster = pxIOManager->xPartition.ulLastFreeCluster;
			 ulCluster < pxIOManager->xPartition.ulNumClusters;
			 ulCluster++ )
		{
			ulFATEntry = FF_getFATEntry( pxIOManager, ulCluster, &xError, &xFATBuffers );
			if( FF_isERR( xError ) )
			{
				break;
			}
			if( ulFATEntry == 0 )
			{
				pxIOManager->xPartition.ulLastFreeCluster = ulCluster;
				break;

			}
		}
		{
		FF_Error_t xTempError;

			xTempError = FF_ReleaseFATBuffers( pxIOManager, &xFATBuffers );
			if( FF_isERR( xError ) == pdFALSE )
			{
				xError = xTempError;
			}
		}
		if( ( FF_isERR( xError ) == pdFALSE ) &&
			( ulCluster == pxIOManager->xPartition.ulNumClusters ) )
		{
			/* There is no free cluster any more. */
			ulCluster = 0;
			xError = FF_FINDFREECLUSTER | FF_ERR_IOMAN_NOT_ENOUGH_FREE_SPACE;
		}

		*pxError = xError;

		return ulCluster;
	}
#endif
/*-----------------------------------------------------------*/

uint32_t FF_FindFreeCluster( FF_IOManager_t *pxIOManager, FF_Error_t *pxError, BaseType_t xDoClaim )
{
FF_Error_t xError = FF_ERR_NONE;
FF_Buffer_t *pxBuffer = NULL;
uint32_t x, ulCluster;
uint32_t ulFATSectorEntry;
uint32_t ulEntriesPerSector;
uint32_t ulFATEntry = 1;
const BaseType_t xEntrySize = ( pxIOManager->xPartition.ucType == FF_T_FAT32 ) ? 4 : 2;
const uint32_t uNumClusters = pxIOManager->xPartition.ulNumClusters;

BaseType_t xTakeLock = FF_Has_Lock( pxIOManager, FF_FAT_LOCK ) == pdFALSE;

	if( xTakeLock )
	{
		FF_LockFAT( pxIOManager );
	}

	ulCluster = pxIOManager->xPartition.ulLastFreeCluster;

#if( ffconfigFAT12_SUPPORT != 0 )
	/* FAT12 tables are too small to optimise, and would make it very complicated! */
	if( pxIOManager->xPartition.ucType == FF_T_FAT12 )
	{
		ulCluster = prvFindFreeClusterSimple( pxIOManager, &xError );
	}
	else
#endif
	{
		#if( ffconfigFSINFO_TRUSTED != 0 )
		{
			/* If 'ffconfigFSINFO_TRUSTED', the contents of the field 'ulLastFreeCluster' is trusted.
			Only ready it in case of FAT32 and only during the very first time, i.e. when
			ulLastFreeCluster is still zero. */
			if( ( pxIOManager->xPartition.ucType == FF_T_FAT32 ) && ( pxIOManager->xPartition.ulLastFreeCluster == 0ul ) )
			{
				pxBuffer = FF_GetBuffer( pxIOManager, pxIOManager->xPartition.ulFSInfoLBA, FF_MODE_READ );
				if( pxBuffer == NULL )
				{
					xError = ( FF_Error_t ) ( FF_ERR_DEVICE_DRIVER_FAILED | FF_FINDFREECLUSTER );
				}
				else
				{
					if( ( FF_getLong(pxBuffer->pucBuffer, 0 ) == 0x41615252 ) &&
						( FF_getLong(pxBuffer->pucBuffer, 484 ) == 0x61417272 ) )
					{
						ulCluster = FF_getLong( pxBuffer->pucBuffer, 492 );
					}
					xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
					pxBuffer = NULL;
				}

			}
		}
		#endif
		if( FF_isERR( xError ) == pdFALSE )
		{
		uint32_t ulFATSector;
		uint32_t ulFATOffset;

			ulEntriesPerSector = pxIOManager->usSectorSize / xEntrySize;
			ulFATOffset = ulCluster * xEntrySize;

			/* Start from a sector where the first free entry is expected,
			and iterate through every FAT sector. */
			for( ulFATSector = ( ulFATOffset / pxIOManager->xPartition.usBlkSize );
				 ulFATSector < pxIOManager->xPartition.ulSectorsPerFAT;
				 ulFATSector++ )
			{
				pxBuffer = FF_GetBuffer( pxIOManager, pxIOManager->xPartition.ulFATBeginLBA + ulFATSector, FF_MODE_READ );
				if( pxBuffer == NULL )
				{
					xError = ( FF_Error_t ) ( FF_ERR_DEVICE_DRIVER_FAILED | FF_FINDFREECLUSTER );
					break;
				}
				for( x = ( ulCluster % ulEntriesPerSector ); x < ulEntriesPerSector; x++ )
				{
					/* Double-check: don't use non-existing clusters */
					if( ulCluster >= uNumClusters )
					{
						xError = ( FF_Error_t ) ( FF_ERR_IOMAN_NOT_ENOUGH_FREE_SPACE | FF_FINDFREECLUSTER );
						break;
					}
					ulFATSectorEntry = ulFATOffset % pxIOManager->xPartition.usBlkSize;
					if( pxIOManager->xPartition.ucType == FF_T_FAT32 )
					{
						ulFATEntry = FF_getLong( pxBuffer->pucBuffer, ulFATSectorEntry );
						/* Clear the top 4 bits. */
						ulFATEntry &= 0x0fffffff;
					}
					else
					{
						ulFATEntry = ( uint32_t ) FF_getShort( pxBuffer->pucBuffer, ulFATSectorEntry );
					}
					if( ulFATEntry == 0x00000000 )
					{
						/* Break and return 'ulCluster' */
						break;
					}
					ulFATOffset += xEntrySize;
					ulCluster++;
				}
				xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
				pxBuffer = NULL;
				if( FF_isERR( xError ) )
				{
					break;
				}
				if( ulFATEntry == 0x00000000 )
				{
					/* And break from the outer loop. */
					break;
				}
			}
			if( ( FF_isERR( xError ) == pdFALSE ) &&
				( ulFATSector == pxIOManager->xPartition.ulSectorsPerFAT ) )
			{
				xError = ( FF_Error_t ) ( FF_ERR_IOMAN_NOT_ENOUGH_FREE_SPACE | FF_FINDFREECLUSTER );
			}
		} /* if( FF_isERR( xError ) == pdFALSE ) */
	} /* if( pxIOManager->xPartition.ucType != FF_T_FAT12 ) */

	if( FF_isERR( xError ) )
	{
		ulCluster = 0UL;
	}
	if( ( ulCluster != 0UL ) && ( xDoClaim != pdFALSE ) )
	{
	FF_Error_t xTempError;

		/* Found a free cluster! */
		pxIOManager->xPartition.ulLastFreeCluster = ulCluster + 1;

		xTempError = FF_putFATEntry( pxIOManager, ulCluster, 0xFFFFFFFF, NULL );
		if( FF_isERR( xError ) == pdFALSE )
		{
			xError = xTempError;
		}

		if( FF_isERR( xError ) )
		{
			ulCluster = 0UL;
		}
	}
	if( xTakeLock )
	{
		FF_UnlockFAT( pxIOManager );
	}
	*pxError = xError;

	return ulCluster;
}	/* FF_FindFreeCluster */
/*-----------------------------------------------------------*/

/**
 * @private
 * @brief	Creates a Cluster Chain
 *	@return > 0 New created cluster
 *	@return = 0 See pxError
 **/
uint32_t FF_CreateClusterChain( FF_IOManager_t *pxIOManager, FF_Error_t *pxError )
{
uint32_t ulStartCluster;
FF_Error_t xError = FF_ERR_NONE;

	FF_LockFAT( pxIOManager );
	{
		ulStartCluster = FF_FindFreeCluster( pxIOManager, &xError, pdTRUE );
	}
	FF_UnlockFAT( pxIOManager );

	if( ulStartCluster != 0L )
	{
		xError = FF_DecreaseFreeClusters( pxIOManager, 1 );
	}
	*pxError = xError;

	return ulStartCluster;
}
/*-----------------------------------------------------------*/

uint32_t FF_GetChainLength( FF_IOManager_t *pxIOManager, uint32_t ulStartCluster, uint32_t *pulEndOfChain, FF_Error_t *pxError )
{
uint32_t ulLength = 0;
FF_FATBuffers_t xFATBuffers;
FF_Error_t xError = FF_ERR_NONE;

	FF_InitFATBuffers( &xFATBuffers, FF_MODE_READ );

	FF_LockFAT( pxIOManager );
	{
		while( FF_isEndOfChain( pxIOManager, ulStartCluster ) == pdFALSE )
		{
			ulStartCluster = FF_getFATEntry( pxIOManager, ulStartCluster, &xError, &xFATBuffers );
			if( FF_isERR( xError ) )
			{
				ulLength = 0;
				break;
			}
			ulLength++;
		}
		if( pulEndOfChain != NULL )
		{
			/* _HT_
			ulStartCluster has just been tested as an end-of-chain token.
			Not sure if the caller expects this. */
			*pulEndOfChain = ulStartCluster;
		}
		xError = FF_ReleaseFATBuffers( pxIOManager, &xFATBuffers );
	}
	FF_UnlockFAT( pxIOManager );

	*pxError = xError;

	return ulLength;
}
/*-----------------------------------------------------------*/

/**
 *	@private
 *	@brief Free's Disk space by freeing unused links on Cluster Chains
 *
 *	@param	pxIOManager,			IOMAN object.
 *	@param	ulStartCluster	Cluster Number that starts the chain.
 *	@param	ulCount			Number of Clusters from the end of the chain to unlink.
 *	@param	ulCount			0 Means Free the entire chain (delete file).
 *	@param	ulCount			1 Means mark the start cluster with EOF.
 *
 *	@return 0 On Success.
 *	@return	-1 If the device driver failed to provide access.
 *
 **/
FF_Error_t FF_UnlinkClusterChain( FF_IOManager_t *pxIOManager, uint32_t ulStartCluster, BaseType_t xDoTruncate )
{
uint32_t ulFATEntry;
uint32_t ulCurrentCluster;
uint32_t ulLength = 0;
uint32_t ulLastFree = ulStartCluster;
FF_Error_t xTempError;
FF_Error_t xError = FF_ERR_NONE;
FF_FATBuffers_t xFATBuffers;

BaseType_t xTakeLock = FF_Has_Lock( pxIOManager, FF_FAT_LOCK ) == pdFALSE;

	if( xTakeLock )
	{
		FF_LockFAT( pxIOManager );
	}

	FF_InitFATBuffers( &xFATBuffers, FF_MODE_WRITE );

	ulFATEntry = ulStartCluster;

	/* Free all clusters in the chain! */
	ulCurrentCluster = ulStartCluster;
	ulFATEntry = ulCurrentCluster;
	do
	{
		/* Sector will now be fetched in write-mode. */
		ulFATEntry = FF_getFATEntry( pxIOManager, ulFATEntry, &xError, &xFATBuffers );
		if( FF_isERR( xError ) )
		{
			break;
		}

		if( ( xDoTruncate != pdFALSE ) && ( ulCurrentCluster == ulStartCluster ) )
		{
			xError = FF_putFATEntry( pxIOManager, ulCurrentCluster, 0xFFFFFFFF, &xFATBuffers );
		}
		else
		{
			xError = FF_putFATEntry( pxIOManager, ulCurrentCluster, 0x00000000, &xFATBuffers );
			ulLength++;
		}
		if( FF_isERR( xError ) )
		{
			break;
		}

		if( ulLastFree > ulCurrentCluster )
		{
			ulLastFree = ulCurrentCluster;
		}
		ulCurrentCluster = ulFATEntry;
	} while( FF_isEndOfChain( pxIOManager, ulFATEntry ) == pdFALSE );

	if( FF_isERR( xError ) == pdFALSE )
	{
		if( pxIOManager->xPartition.ulLastFreeCluster > ulLastFree )
		{
			pxIOManager->xPartition.ulLastFreeCluster = ulLastFree;
		}
	}

	xTempError = FF_ReleaseFATBuffers( pxIOManager, &xFATBuffers );
	if( FF_isERR( xError ) == pdFALSE )
	{
		xError = xTempError;
	}

	if( xTakeLock )
	{
		FF_UnlockFAT( pxIOManager );
	}
	if( ulLength != 0 )
	{
		xTempError = FF_IncreaseFreeClusters( pxIOManager, ulLength );
		if( FF_isERR( xError ) == pdFALSE )
		{
			xError = xTempError;
		}
	}

	return xError;
}
/*-----------------------------------------------------------*/

#if( ffconfigFAT12_SUPPORT != 0 )
	static uint32_t prvCountFreeClustersSimple( FF_IOManager_t *pxIOManager, FF_Error_t *pxError )
	{
	FF_Error_t xError = FF_ERR_NONE;
	uint32_t ulIndex;
	uint32_t ulFATEntry;
	uint32_t ulFreeClusters = 0;
	const uint32_t xTotalClusters =
		pxIOManager->xPartition.ulDataSectors / pxIOManager->xPartition.ulSectorsPerCluster;

		for( ulIndex = 0; ulIndex < xTotalClusters; ulIndex++ )
		{
			ulFATEntry = FF_getFATEntry( pxIOManager, ulIndex, &xError, NULL );
			if( FF_isERR( xError) )
			{
				break;
			}
			if( ulFATEntry == 0UL )
			{
				ulFreeClusters++;
			}
		}

		*pxError = xError;

		return ulFreeClusters;
	}
#endif
/*-----------------------------------------------------------*/


uint32_t FF_CountFreeClusters( FF_IOManager_t *pxIOManager, FF_Error_t *pxError )
{
FF_Error_t xError = FF_ERR_NONE;
FF_Buffer_t *pxBuffer;
uint32_t ulIndex, x;
uint32_t ulFATEntry;
uint32_t ulEntriesPerSector;
uint32_t ulFreeClusters = 0;
uint32_t ClusterNum = 0;
BaseType_t xInfoKnown = pdFALSE;
BaseType_t xTakeLock = FF_Has_Lock( pxIOManager, FF_FAT_LOCK ) == pdFALSE;

	if( xTakeLock )
	{
		FF_LockFAT( pxIOManager );
	}

#if( ffconfigFAT12_SUPPORT != 0 )
	/* FAT12 tables are too small to optimise, and would make it very complicated! */
	if( pxIOManager->xPartition.ucType == FF_T_FAT12 )
	{
		ulFreeClusters = prvCountFreeClustersSimple( pxIOManager, &xError );
	}
	else
#endif
	{
		/* For FAT16 and FAT32 */
		#if( ffconfigFSINFO_TRUSTED != 0 )
		{
			/* If 'ffconfigFSINFO_TRUSTED', the contents of the field 'ulFreeClusterCount' is trusted. */
			if( pxIOManager->xPartition.ucType == FF_T_FAT32 )
			{
				pxBuffer = FF_GetBuffer( pxIOManager, pxIOManager->xPartition.ulFSInfoLBA, FF_MODE_READ );
				if( pxBuffer == NULL )
				{
					xError = ( FF_Error_t ) ( FF_ERR_DEVICE_DRIVER_FAILED | FF_COUNTFREECLUSTERS );
				}
				else
				{
					if( ( FF_getLong( pxBuffer->pucBuffer, 0 ) == 0x41615252 ) &&
						( FF_getLong( pxBuffer->pucBuffer, 484 ) == 0x61417272 ) )
					{
						ulFreeClusters = FF_getLong( pxBuffer->pucBuffer, 488 );

						if( ulFreeClusters != ~0ul )
						{
							xInfoKnown = pdTRUE;
						}
						else
						{
							ulFreeClusters = 0ul;
						}
					}

					xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
					pxBuffer = NULL;

					if( xInfoKnown != pdFALSE )
					{
						pxIOManager->xPartition.ulFreeClusterCount = ulFreeClusters;
					}
				}
			}
		}
		#endif
		if( ( xInfoKnown == pdFALSE ) && ( pxIOManager->xPartition.usBlkSize != 0 ) )
		{
			if( pxIOManager->xPartition.ucType == FF_T_FAT32 )
			{
				ulEntriesPerSector = pxIOManager->usSectorSize / 4;
			}
			else
			{
				ulEntriesPerSector = pxIOManager->usSectorSize / 2;
			}
			for( ulIndex = 0; ulIndex < pxIOManager->xPartition.ulSectorsPerFAT; ulIndex++ )
			{
				pxBuffer = FF_GetBuffer( pxIOManager, pxIOManager->xPartition.ulFATBeginLBA + ulIndex, FF_MODE_READ );

				if( pxBuffer == NULL )
				{
					xError = ( FF_Error_t ) ( FF_ERR_DEVICE_DRIVER_FAILED | FF_COUNTFREECLUSTERS );
					break;
				}
				#if USE_SOFT_WDT
				{
					/* _HT_ : FF_CountFreeClusters was a little too busy, have it call the WDT and sleep */
					clearWDT( );
					if( ( ( ulIndex + 1 ) % 32 ) == 0 )
					{
						FF_Sleep( 1 );
					}
				}
				#endif
				for( x = 0; x < ulEntriesPerSector; x++ )
				{
					if( pxIOManager->xPartition.ucType == FF_T_FAT32 )
					{
						/* Clearing the top 4 bits. */
						ulFATEntry = FF_getLong( pxBuffer->pucBuffer, x * 4 ) & 0x0fffffff;
					}
					else
					{
						ulFATEntry = ( uint32_t ) FF_getShort( pxBuffer->pucBuffer, x * 2 );
					}
					if( ulFATEntry == 0ul )
					{
						ulFreeClusters++;
					}
					/* FAT table might not be cluster aligned. */
					if( ClusterNum > pxIOManager->xPartition.ulNumClusters )
					{
						/* Stop counting if that's the case. */
						break;
					}
					ClusterNum++;
				}

				xError = FF_ReleaseBuffer( pxIOManager, pxBuffer );
				pxBuffer = NULL;
				if( FF_isERR( xError ) )
				{
					break;
				}
				if( ClusterNum > pxIOManager->xPartition.ulNumClusters )
				{
					/* Break out of 2nd loop too ^^ */
					break;
				}
				/* ulFreeClusters is -2 because the first 2 fat entries in the table are reserved. */
				if( ulFreeClusters > pxIOManager->xPartition.ulNumClusters )
				{
					ulFreeClusters = pxIOManager->xPartition.ulNumClusters;
				}
			}	/* for( ulIndex = 0; ulIndex < pxIOManager->xPartition.ulSectorsPerFAT; ulIndex++ ) */
		}
	}

	if( xTakeLock )
	{
		FF_UnlockFAT( pxIOManager );
	}

	if( FF_isERR( xError ) )
	{
		ulFreeClusters = 0;
	}
	*pxError = xError;

	return ulFreeClusters;
}
/*-----------------------------------------------------------*/

#if( ffconfig64_NUM_SUPPORT != 0 )
	uint64_t FF_GetFreeSize( FF_IOManager_t *pxIOManager, FF_Error_t *pxError )
	{
	FF_Error_t xError = FF_ERR_NONE;
	uint32_t ulFreeClusters;
	uint64_t ulFreeSize = 0;

		if( pxIOManager != NULL )
		{
			if( pxIOManager->xPartition.ulFreeClusterCount == 0ul )
			{
				FF_LockFAT( pxIOManager );
				{
					pxIOManager->xPartition.ulFreeClusterCount = FF_CountFreeClusters( pxIOManager, &xError );
				}
				FF_UnlockFAT( pxIOManager );
			}
			ulFreeClusters = pxIOManager->xPartition.ulFreeClusterCount;
			ulFreeSize = ( uint64_t )
				( ( uint64_t ) ulFreeClusters * ( uint64_t )
				( ( uint64_t ) pxIOManager->xPartition.ulSectorsPerCluster *
				  ( uint64_t ) pxIOManager->xPartition.usBlkSize ) );
		}
		if( pxError != NULL )
		{
			*pxError = xError;
		}

		return ulFreeSize;
	}
#else
	uint32_t FF_GetFreeSize( FF_IOManager_t *pxIOManager, FF_Error_t *pxError )
	{
	FF_Error_t xError = FF_ERR_NONE;
	uint32_t ulFreeClusters;
	uint32_t ulFreeSize = 0;

		if( pxIOManager != NULL )
		{
			if( pxIOManager->xPartition.ulFreeClusterCount == 0ul )
			{
				FF_LockFAT( pxIOManager );
				{
					 pxIOManager->xPartition.ulFreeClusterCount = FF_CountFreeClusters( pxIOManager, &xError );
				}
				FF_UnlockFAT( pxIOManager );
			}
			ulFreeClusters = pxIOManager->xPartition.ulFreeClusterCount;
			ulFreeSize = ( uint32_t )
				( ( uint32_t ) ulFreeClusters * ( uint32_t )
				( ( uint32_t ) pxIOManager->xPartition.ulSectorsPerCluster *
				  ( uint32_t ) pxIOManager->xPartition.usBlkSize ) );
		}

		if( pxError != NULL )
		{
			*pxError = xError;
		}

		return ulFreeSize;
	}
#endif	/* ffconfig64_NUM_SUPPORT */
/*-----------------------------------------------------------*/

