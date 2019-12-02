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
 *	@file		ff_fat.h
 *	@ingroup	FAT
 **/

#ifndef _FF_FAT_H_
#define _FF_FAT_H_

#ifndef PLUS_FAT_H
	#error this header will be included from "plusfat.h"
#endif

/*---------- ERROR CODES */


/*---------- PROTOTYPES */

/* HT statistics Will be taken away after testing: */
#if( ffconfigFAT_USES_STAT != 0 )
struct SFatStat
{
	unsigned initCount;
	unsigned clearCount;
	unsigned getCount[2];	/* Index 0 for READ counts, index 1 for WRITE counts. */
	unsigned reuseCount[2];
	unsigned missCount[2];
};

extern struct SFatStat fatStat;
#endif

#if( ffconfigWRITE_BOTH_FATS != 0 )
	#define ffconfigBUF_STORE_COUNT 2
#else
	#define ffconfigBUF_STORE_COUNT 1
#endif

typedef struct _FatBuffers
{
	FF_Buffer_t *pxBuffers[ffconfigBUF_STORE_COUNT];
	uint8_t ucMode; /* FF_MODE_READ or WRITE. */
} FF_FATBuffers_t;

uint32_t FF_getClusterPosition( FF_IOManager_t *pxIOManager, uint32_t ulEntry, uint32_t ulEntrySize );
uint32_t FF_getClusterChainNumber( FF_IOManager_t *pxIOManager, uint32_t ulEntry, uint32_t ulEntrySize );
uint32_t FF_getMajorBlockNumber( FF_IOManager_t *pxIOManager, uint32_t ulEntry, uint32_t ulEntrySize );
uint32_t FF_getMinorBlockNumber( FF_IOManager_t *pxIOManager, uint32_t ulEntry, uint32_t ulEntrySize );
uint32_t FF_getMinorBlockEntry( FF_IOManager_t *pxIOManager, uint32_t ulEntry, uint32_t ulEntrySize );

/* A partition may define a block size larger than 512 bytes (at offset 0x0B of the PBR).
This function translates a block address to an address based on 'pxIOManager->usBlkSize',
which is usually 512 bytes.
*/
static portINLINE uint32_t FF_getRealLBA( FF_IOManager_t *pxIOManager, uint32_t LBA )
{
	return LBA * pxIOManager->xPartition.ucBlkFactor;
}

uint32_t FF_Cluster2LBA( FF_IOManager_t *pxIOManager, uint32_t ulCluster );
uint32_t FF_LBA2Cluster( FF_IOManager_t *pxIOManager, uint32_t ulAddress );
uint32_t FF_getFATEntry( FF_IOManager_t *pxIOManager, uint32_t ulCluster, FF_Error_t *pxError, FF_FATBuffers_t *pxFATBuffers );
FF_Error_t FF_putFATEntry( FF_IOManager_t *pxIOManager, uint32_t ulCluster, uint32_t ulValue, FF_FATBuffers_t *pxFATBuffers );
BaseType_t FF_isEndOfChain( FF_IOManager_t *pxIOManager, uint32_t ulFatEntry );
uint32_t FF_FindFreeCluster( FF_IOManager_t *pxIOManager, FF_Error_t *pxError, BaseType_t aDoClaim );
uint32_t FF_ExtendClusterChain( FF_IOManager_t *pxIOManager, uint32_t ulStartCluster, uint32_t ulCount );
FF_Error_t FF_UnlinkClusterChain( FF_IOManager_t *pxIOManager, uint32_t ulStartCluster, BaseType_t xDoTruncate );
uint32_t FF_TraverseFAT( FF_IOManager_t *pxIOManager, uint32_t ulStart, uint32_t ulCount, FF_Error_t *pxError );
uint32_t FF_CreateClusterChain( FF_IOManager_t *pxIOManager, FF_Error_t *pxError );
uint32_t FF_GetChainLength( FF_IOManager_t *pxIOManager, uint32_t pa_nStartCluster, uint32_t *piEndOfChain, FF_Error_t *pxError );
uint32_t FF_FindEndOfChain( FF_IOManager_t *pxIOManager, uint32_t Start, FF_Error_t *pxError );
FF_Error_t FF_ClearCluster( FF_IOManager_t *pxIOManager, uint32_t ulCluster  );

#if( ffconfig64_NUM_SUPPORT != 0 )
	uint64_t FF_GetFreeSize( FF_IOManager_t *pxIOManager, FF_Error_t *pxError );
#else
	uint32_t FF_GetFreeSize( FF_IOManager_t *pxIOManager, FF_Error_t *pxError );
#endif

/* WARNING: If this prototype changes, it must be updated in ff_ioman.c also! */
uint32_t FF_CountFreeClusters( FF_IOManager_t *pxIOManager, FF_Error_t *pxError );

FF_Error_t FF_ReleaseFATBuffers( FF_IOManager_t *pxIOManager, FF_FATBuffers_t *pxFATBuffers );

static portINLINE void FF_InitFATBuffers( FF_FATBuffers_t *pxFATBuffers, uint8_t ucMode )
{
	pxFATBuffers->pxBuffers[ 0 ] = NULL;
#if ffconfigBUF_STORE_COUNT > 1
	pxFATBuffers->pxBuffers[ 1 ] = NULL;
#endif
#if ffconfigBUF_STORE_COUNT > 2
	#error Please check this code, maybe it is time to use memset
#endif
	pxFATBuffers->ucMode = ucMode; /* FF_MODE_READ/WRITE */
	#if ffconfigFAT_USES_STAT
	{
		fatStat.initCount++;
	}
	#endif
}

#endif

