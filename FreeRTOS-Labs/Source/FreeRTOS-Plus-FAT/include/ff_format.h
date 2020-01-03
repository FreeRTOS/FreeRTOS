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
 *	@file		ff_format.c
 *	@ingroup	FORMAT
 *
 **/


#ifndef _FF_FORMAT_H_
#define _FF_FORMAT_H_

#ifdef	__cplusplus
extern "C" {
#endif


#ifndef PLUS_FAT_H
	#error this header will be included from "ff_headers.h"
#endif

/*---------- PROTOTYPES */
/* PUBLIC (Interfaces): */

typedef enum _FF_SizeType {
	eSizeIsQuota,    /* Assign a quotum (sum of xSizes is free, all disk space will be allocated) */
	eSizeIsPercent,  /* Assign a percentage of the available space (sum of xSizes must be <= 100) */
	eSizeIsSectors,  /* Assign fixed number of sectors (sum of xSizes must be < ulSectorCount) */
} eSizeType_t;

typedef struct _FF_PartitionParameters {
	uint32_t ulSectorCount;     /* Total number of sectors on the disk, including hidden/reserved */
								/* Must be obtained from the block driver */
	uint32_t ulHiddenSectors;   /* Keep at least these initial sectors free  */
	uint32_t ulInterSpace;      /* Number of sectors to keep free between partitions (when 0 -> 2048) */
	BaseType_t xSizes[ ffconfigMAX_PARTITIONS ];  /* E.g. 80, 20, 0, 0 (see eSizeType) */
    BaseType_t xPrimaryCount;    /* The number of partitions that must be "primary" */
	eSizeType_t eSizeType;
} FF_PartitionParameters_t;

FF_Error_t FF_Partition( FF_Disk_t *pxDisk, FF_PartitionParameters_t *pParams );

FF_Error_t FF_Format( FF_Disk_t *pxDisk, BaseType_t xPartitionNumber, BaseType_t xPreferFAT16, BaseType_t xSmallClusters );

/* Private : */

#ifdef	__cplusplus
} /* extern "C" */
#endif

#endif
