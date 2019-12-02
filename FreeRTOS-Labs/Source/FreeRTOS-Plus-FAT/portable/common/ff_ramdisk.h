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

#ifndef __RAMDISK_H__

#define __RAMDISK_H__

#ifdef __cplusplus
extern "C" {
#endif

#include "ff_headers.h"

/* Create a RAM disk, supplying enough memory to hold N sectors of 512 bytes each */
FF_Disk_t *FF_RAMDiskInit( char *pcName, uint8_t *pucDataBuffer, uint32_t ulSectorCount, size_t xIOManagerCacheSize );

/* Release all resources */
BaseType_t FF_RAMDiskDelete( FF_Disk_t *pxDisk );

/* Show some partition information */
BaseType_t FF_RAMDiskShowPartition( FF_Disk_t *pxDisk );

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* __RAMDISK_H__ */
