/******************************************************************************
*
* Copyright (C) 2010 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xil_cache_l.h
*
* Contains L1 and L2 specific functions for the ARM cache functionality
* used by xcache.c. This functionality is being made available here for
* more sophisticated users.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a ecm  01/24/10 First release
* </pre>
*
******************************************************************************/
#ifndef XIL_CACHE_MACH_H
#define XIL_CACHE_MACH_H

#include "xil_types.h"
#ifdef __cplusplus
extern "C" {
#endif

/************************** Function Prototypes ******************************/

void Xil_DCacheInvalidateLine(u32 adr);
void Xil_DCacheFlushLine(u32 adr);
void Xil_DCacheStoreLine(u32 adr);
void Xil_ICacheInvalidateLine(u32 adr);

void Xil_L1DCacheEnable(void);
void Xil_L1DCacheDisable(void);
void Xil_L1DCacheInvalidate(void);
void Xil_L1DCacheInvalidateLine(u32 adr);
void Xil_L1DCacheInvalidateRange(u32 adr, u32 len);
void Xil_L1DCacheFlush(void);
void Xil_L1DCacheFlushLine(u32 adr);
void Xil_L1DCacheFlushRange(u32 adr, u32 len);
void Xil_L1DCacheStoreLine(u32 adr);

void Xil_L1ICacheEnable(void);
void Xil_L1ICacheDisable(void);
void Xil_L1ICacheInvalidate(void);
void Xil_L1ICacheInvalidateLine(u32 adr);
void Xil_L1ICacheInvalidateRange(u32 adr, u32 len);

void Xil_L2CacheEnable(void);
void Xil_L2CacheDisable(void);
void Xil_L2CacheInvalidate(void);
void Xil_L2CacheInvalidateLine(u32 adr);
void Xil_L2CacheInvalidateRange(u32 adr, u32 len);
void Xil_L2CacheFlush(void);
void Xil_L2CacheFlushLine(u32 adr);
void Xil_L2CacheFlushRange(u32 adr, u32 len);
void Xil_L2CacheStoreLine(u32 adr);

#ifdef __cplusplus
}
#endif

#endif
