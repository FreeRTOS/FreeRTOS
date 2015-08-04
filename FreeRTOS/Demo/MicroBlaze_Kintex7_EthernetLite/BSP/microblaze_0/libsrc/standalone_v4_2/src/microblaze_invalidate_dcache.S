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
* microblaze_invalidate_dcache()
*    
*    Invalidate the entire L1 DCache 
*
*
*******************************************************************************/

#include "xparameters.h"

#define MICROBLAZE_MSR_DCACHE_ENABLE        0x00000080
#define MICROBLAZE_MSR_INTR_ENABLE          0x00000002
    
#ifndef XPAR_MICROBLAZE_DCACHE_LINE_LEN
#define XPAR_MICROBLAZE_DCACHE_LINE_LEN   1
#endif

#ifndef XPAR_MICROBLAZE_DCACHE_USE_WRITEBACK
#define MB_VERSION_LT_v720
#endif
    
	.text
	.globl	microblaze_invalidate_dcache
	.ent	microblaze_invalidate_dcache
	.align	2

microblaze_invalidate_dcache:

#ifdef MB_VERSION_LT_v720                                       /* Disable Dcache and interrupts before invalidating */           
	mfs	r9, rmsr                                        
	andi	r10, r9, ~(MICROBLAZE_MSR_DCACHE_ENABLE | MICROBLAZE_MSR_INTR_ENABLE)
	mts	rmsr, r10
#endif
    	addik 	r5, r0, XPAR_MICROBLAZE_DCACHE_BASEADDR & (-(4 * XPAR_MICROBLAZE_DCACHE_LINE_LEN))
    	addik	r6, r5, XPAR_MICROBLAZE_DCACHE_BYTE_SIZE &  (-(4 * XPAR_MICROBLAZE_DCACHE_LINE_LEN))        /* Compute end */
        
L_start:
	wdc	r5, r0                                          /* Invalidate the Cache */
    
    	cmpu	r18, r5, r6                                     /* Are we at the end? */
	blei	r18, L_done                                     

     	brid	L_start                                         /* Branch to the beginning of the loop */
	addik	r5, r5, (XPAR_MICROBLAZE_DCACHE_LINE_LEN * 4)   /* Increment the addrees by 4 (delay slot) */

L_done:	
	rtsd	r15, 8                                          /* Return */
#ifdef MB_VERSION_LT_v720                                       /* restore MSR only for MB version < v7.20 */
	mts	rmsr, r9
#else
        nop
#endif

	.end	microblaze_invalidate_dcache

	
  
