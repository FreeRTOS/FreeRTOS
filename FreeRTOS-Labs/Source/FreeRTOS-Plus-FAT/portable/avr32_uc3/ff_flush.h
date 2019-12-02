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

#if	!defined(__FF_FLUSH_H__)

#define	__FF_FLUSH_H__

#ifdef	__cplusplus
extern "C" {
#endif

// HT addition: call FF_FlushCache and in addition call cache_write_flush (see secCache.cpp)
FF_Error_t FF_FlushWrites( FF_IOManager_t *pxIOManager, BaseType_t xForced );

#define	FLUSH_DISABLE	1
#define	FLUSH_ENABLE	0

// HT addition: prevent flushing temporarily FF_StopFlush(pIoMan, true)
FF_Error_t FF_StopFlush( FF_IOManager_t *pxIOManager, BaseType_t xFlag );
#ifdef	__cplusplus
}	// extern "C"
#endif


#endif	// !defined(__FF_FLUSH_H__)
