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
 *	@file		ff_devices.h
 **/
#ifndef FF_DEVICES_H
#define FF_DEVICES_H

#ifndef PLUS_FAT_H
	#error this header will be included from "plusfat.h"
#endif

#ifdef __cplusplus
extern "C" {
#endif

#define FF_DEV_NO_DEV		0
#define FF_DEV_CHAR_DEV		1
#define FF_DEV_BLOCK_DEV	2

BaseType_t xCheckDevicePath( const char *pcPath );

int FF_Device_Seek( FF_FILE *pxStream, long lOffset, int iWhence );

BaseType_t FF_Device_Open( const char *pcPath, FF_FILE * pxStream );

void FF_Device_Close( FF_FILE * pxStream );

size_t FF_Device_Read( void *pvBuf, size_t lSize, size_t lCount, FF_FILE * pxStream );

size_t FF_Device_Write( const void *pvBuf, size_t lSize, size_t lCount, FF_FILE * pxStream );


int FF_Device_GetDirEnt( const char *pcPath, FF_DirEnt_t *pxDirEnt );

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* FF_DEVICES_H */
