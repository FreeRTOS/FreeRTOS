/******************************************************************************
*
* Copyright (C) 2009 - 2015 Xilinx, Inc. All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
* XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/
/*****************************************************************************/
/**
*
* @file xil_cache_vxworks.h
*
* Contains the cache related functions for VxWorks that is wrapped by
* xil_cache.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date	 Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00a hbm  12/11/09 Initial release
*
* </pre>
*
* @note
*
******************************************************************************/

#ifndef XIL_CACHE_VXWORKS_H
#define XIL_CACHE_VXWORKS_H

#ifdef __cplusplus
extern "C" {
#endif

#include "vxWorks.h"
#include "vxLib.h"
#include "sysLibExtra.h"
#include "cacheLib.h"

#if (CPU_FAMILY==PPC)

#define Xil_DCacheEnable()		cacheEnable(DATA_CACHE)

#define Xil_DCacheDisable()		cacheDisable(DATA_CACHE)

#define Xil_DCacheInvalidateRange(Addr, Len) \
		cacheInvalidate(DATA_CACHE, (void *)(Addr), (Len))

#define Xil_DCacheFlushRange(Addr, Len) \
		cacheFlush(DATA_CACHE, (void *)(Addr), (Len))

#define Xil_ICacheEnable()		cacheEnable(INSTRUCTION_CACHE)

#define Xil_ICacheDisable()		cacheDisable(INSTRUCTION_CACHE)

#define Xil_ICacheInvalidateRange(Addr, Len) \
		cacheInvalidate(INSTRUCTION_CACHE, (void *)(Addr), (Len))


#else
#error "Unknown processor / architecture. Must be PPC for VxWorks."
#endif

#ifdef __cplusplus
}
#endif

#endif
