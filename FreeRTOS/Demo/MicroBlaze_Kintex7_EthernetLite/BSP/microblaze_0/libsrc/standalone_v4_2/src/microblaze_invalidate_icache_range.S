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
*
* microblaze_invalidate_icache_range(unsigned int cacheaddr, unsigned int len)
*    
*    Invalidate an ICache range
*    
*    Parameters:  
*       'cacheaddr' - address in the Icache where invalidation begins
*	'len'       - length (in bytes) worth of Icache to be invalidated
*
*
*******************************************************************************/

#include "xparameters.h"

#define MICROBLAZE_MSR_ICACHE_ENABLE        0x00000020
#define MICROBLAZE_MSR_INTR_ENABLE          0x00000002
    
#ifndef XPAR_MICROBLAZE_ICACHE_LINE_LEN
#define XPAR_MICROBLAZE_ICACHE_LINE_LEN   1
#endif

#ifndef XPAR_MICROBLAZE_DCACHE_USE_WRITEBACK
#define MB_VERSION_LT_v720
#endif
    
	.text
	.globl	microblaze_invalidate_icache_range
	.ent	microblaze_invalidate_icache_range
	.align	2

microblaze_invalidate_icache_range:

#ifdef MB_VERSION_LT_v720                                       /* Disable Icache and interrupts before invalidating */    
	mfs	r9, rmsr                                        
	andi	r10, r9, ~(MICROBLAZE_MSR_ICACHE_ENABLE | MICROBLAZE_MSR_INTR_ENABLE)
	mts	rmsr, r10
#endif

        beqi    r6, L_done                                      /* Skip loop if size is zero */
    
        add	r6, r5, r6                                      /* Compute end address */
        addik   r6, r6, -1
    
        andi    r6, r6, -(4 * XPAR_MICROBLAZE_ICACHE_LINE_LEN)  /* Align end down to cache line */   
        andi    r5, r5, -(4 * XPAR_MICROBLAZE_ICACHE_LINE_LEN)  /* Align start down to cache line */

L_start:
    	cmpu	r18, r5, r6                                     /* Are we at the end? */
	blti	r18, L_done                                     

	wic	r5, r0                                          /* Invalidate the cache line */
        
     	brid	L_start                                         /* Branch to the beginning of the loop */
	addik	r5, r5, (XPAR_MICROBLAZE_ICACHE_LINE_LEN * 4)   /* Increment the addrees by 4 (delay slot) */

L_done:
	rtsd	r15, 8                                          /* Return */
#ifdef MB_VERSION_LT_v720                                       /* restore MSR only for MB version < v7.20 */
	mts	rmsr, r9
#else
        nop
#endif
	.end	microblaze_invalidate_icache_range

	
  
