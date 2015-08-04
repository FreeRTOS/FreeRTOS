/******************************************************************************
*
* Copyright (C) 2008 - 2014 Xilinx, Inc.  All rights reserved.
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
* microblaze_invalidate_cache_ext()
*
*Invalidate the entire L2 Cache 
*
*
*******************************************************************************/

#include "xparameters.h"

#define XPAR_MICROBLAZE_EXT_CACHE_LINE_LEN	16

	.text
	.globl	microblaze_invalidate_cache_ext
	.ent	microblaze_invalidate_cache_ext
	.align	2

microblaze_invalidate_cache_ext:

#if ((XPAR_MICROBLAZE_INTERCONNECT==3) && (XPAR_MICROBLAZE_USE_DCACHE==1))
	addik	r5, r0, XPAR_MICROBLAZE_DCACHE_BASEADDR & (-(4 * XPAR_MICROBLAZE_EXT_CACHE_LINE_LEN))
	
	addik	r6, r0, XPAR_MICROBLAZE_DCACHE_BYTE_SIZE-(4 * XPAR_MICROBLAZE_EXT_CACHE_LINE_LEN)
 	andi	r6, r6, -(4 * XPAR_MICROBLAZE_EXT_CACHE_LINE_LEN)

Loop_start:
	wdc.ext.clear	r5, r6
	bgtid	r6,Loop_start
	addik	r6, r6,-(4 * XPAR_MICROBLAZE_EXT_CACHE_LINE_LEN)
#endif	
	rtsd	r15, 8
	nop

	.end	microblaze_invalidate_cache_ext

	
  
