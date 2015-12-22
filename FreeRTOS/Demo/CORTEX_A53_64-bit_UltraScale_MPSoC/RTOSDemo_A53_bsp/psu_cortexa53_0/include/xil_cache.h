/******************************************************************************
*
* Copyright (C) 2014 Xilinx, Inc. All rights reserved.
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
* @file xil_cache.h
*
* Contains required functions for the ARM cache functionality
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 5.00 	pkp  05/29/14 First release
* </pre>
*
******************************************************************************/
#ifndef XIL_CACHE_H
#define XIL_CACHE_H

#include "xil_types.h"

#ifdef __cplusplus
extern "C" {
#endif

void Xil_DCacheEnable(void);
void Xil_DCacheDisable(void);
void Xil_DCacheInvalidate(void);
void Xil_DCacheInvalidateRange(INTPTR adr, u32 len);
void Xil_DCacheInvalidateLine(INTPTR adr);
void Xil_DCacheFlush(void);
void Xil_DCacheFlushRange(INTPTR adr, u32 len);
void Xil_DCacheFlushLine(INTPTR adr);

void Xil_ICacheEnable(void);
void Xil_ICacheDisable(void);
void Xil_ICacheInvalidate(void);
void Xil_ICacheInvalidateRange(INTPTR adr, u32 len);
void Xil_ICacheInvalidateLine(INTPTR adr);
#ifdef __cplusplus
}
#endif

#endif
