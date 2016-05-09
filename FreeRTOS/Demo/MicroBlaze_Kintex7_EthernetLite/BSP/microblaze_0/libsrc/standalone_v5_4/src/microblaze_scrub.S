/******************************************************************************
*
* Copyright (C) 2012 - 2014 Xilinx, Inc. All rights reserved.
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
/******************************************************************************
*
* microblaze_scrub ()
*
*    Scrub LMB memory and all internal BRAMs (data cache, instruction cache,
*    MMU UTLB and branch target cache) in MicroBlaze to reduce the possibility
*    of an uncorrectable error when fault tolerance support is enabled.
*
*    This routine assumes that the processor is in privileged mode when it is
*    called, if the MMU is enabled.
*
*    Call this routine regularly from a timer interrupt.
*
*    Parameters:
*       None
*
*
*******************************************************************************/

#include "xparameters.h"

/* Define if fault tolerance is used */
#ifdef XPAR_MICROBLAZE_FAULT_TOLERANT
  #if XPAR_MICROBLAZE_FAULT_TOLERANT > 0
    #define FAULT_TOLERANT
  #endif
#endif

/* Define if LMB is used and can be scrubbed */
#if defined(XPAR_MICROBLAZE_D_LMB) &&            \
	    defined(XPAR_DLMB_CNTLR_BASEADDR) && \
	    defined(XPAR_DLMB_CNTLR_HIGHADDR)
  #if XPAR_MICROBLAZE_D_LMB == 1
    #define HAS_SCRUBBABLE_LMB
    #define DLMB_MASK (XPAR_DLMB_CNTLR_HIGHADDR - XPAR_DLMB_CNTLR_BASEADDR)
  #endif
#endif

/* Set default cache line lengths */
#ifndef XPAR_MICROBLAZE_DCACHE_LINE_LEN
  #define XPAR_MICROBLAZE_DCACHE_LINE_LEN   4
#endif

#ifndef XPAR_MICROBLAZE_ICACHE_LINE_LEN
  #define XPAR_MICROBLAZE_ICACHE_LINE_LEN   4
#endif

/* Define if internal Data Cache BRAMs are used */
#if defined(XPAR_MICROBLAZE_USE_DCACHE) && defined(XPAR_MICROBLAZE_DCACHE_BYTE_SIZE)
  #if XPAR_MICROBLAZE_USE_DCACHE == 1 && XPAR_MICROBLAZE_DCACHE_BYTE_SIZE > 1024
    #define HAS_BRAM_DCACHE
    #define DCACHE_INCREMENT (XPAR_MICROBLAZE_DCACHE_LINE_LEN * 4)
    #define DCACHE_MASK (XPAR_MICROBLAZE_DCACHE_BYTE_SIZE - 1)
  #endif
#endif

/* Define if internal Instruction Cache BRAMs are used */
#if defined(XPAR_MICROBLAZE_USE_ICACHE) && defined(XPAR_MICROBLAZE_CACHE_BYTE_SIZE)
  #if XPAR_MICROBLAZE_USE_ICACHE == 1 && XPAR_MICROBLAZE_CACHE_BYTE_SIZE > 1024
    #define HAS_BRAM_ICACHE
    #define ICACHE_INCREMENT (XPAR_MICROBLAZE_ICACHE_LINE_LEN * 4)
    #define ICACHE_MASK (XPAR_MICROBLAZE_CACHE_BYTE_SIZE - 1)
  #endif
#endif

/* Define if internal MMU UTLB BRAM is used */
#ifdef XPAR_MICROBLAZE_USE_MMU
  #if XPAR_MICROBLAZE_USE_MMU > 1
    #define HAS_BRAM_MMU_UTLB
  #endif
#endif

/* Define if internal BTC BRAM is used, and match BTC clear to a complete cache scrub */
#if defined(XPAR_MICROBLAZE_USE_BRANCH_TARGET_CACHE) && \
    defined(XPAR_MICROBLAZE_BRANCH_TARGET_CACHE_SIZE)
  #if XPAR_MICROBLAZE_USE_BRANCH_TARGET_CACHE == 1
    #if XPAR_MICROBLAZE_BRANCH_TARGET_CACHE_SIZE == 0 || \
	XPAR_MICROBLAZE_BRANCH_TARGET_CACHE_SIZE >  4
      #define HAS_BRAM_BRANCH_TARGET_CACHE
      #ifdef HAS_BRAM_DCACHE
	#define BTC_MASK_D (XPAR_MICROBLAZE_DCACHE_BYTE_SIZE/DCACHE_INCREMENT-1)
      #else
	#define BTC_MASK_D 256
      #endif
      #ifdef HAS_BRAM_ICACHE
	#define BTC_MASK_I (XPAR_MICROBLAZE_CACHE_BYTE_SIZE/ICACHE_INCREMENT-1)
      #else
	#define BTC_MASK_I 256
      #endif
      #if BTC_MASK_D > BTC_MASK_I
	#define BTC_MASK BTC_MASK_D
      #else
	#define BTC_MASK BTC_MASK_I
      #endif
    #endif
  #endif
#endif

/* Define index offsets to persistent data used by this routine */
#define DLMB_INDEX_OFFSET     0
#define DCACHE_INDEX_OFFSET   4
#define ICACHE_INDEX_OFFSET   8
#define MMU_INDEX_OFFSET      12
#define BTC_CALL_COUNT_OFFSET 16

	.text
	.globl	microblaze_scrub
	.ent	microblaze_scrub
	.align	2

microblaze_scrub:
#ifdef FAULT_TOLERANT
	la	r6, r0, L_persistent_data		/* Get pointer to data */

#ifdef HAS_SCRUBBABLE_LMB
L_dlmb:
	lwi	r5, r6, DLMB_INDEX_OFFSET		/* Get dlmb index */
	lw	r7, r5, r0				/* Load and store */
	sw	r7, r5, r0
	addik	r5, r5, 4				/* Increment and save dlmb index */
	andi	r5, r5, DLMB_MASK
	swi	r5, r6, DLMB_INDEX_OFFSET
#endif /* HAS_SCRUBBABLE_LMB */

#ifdef HAS_BRAM_DCACHE
L_dcache:
	lwi	r5, r6, DCACHE_INDEX_OFFSET		/* Get dcache line index */
	wdc	r5, r0					/* Invalidate data cache line */
	addik	r5, r5, DCACHE_INCREMENT		/* Increment and save entry index */
	andi	r5, r5, DCACHE_MASK
	swi	r5, r6, DCACHE_INDEX_OFFSET
#endif /* HAS_BRAM_DCACHE */

#ifdef HAS_BRAM_ICACHE
L_icache:
	lwi	r5, r6, ICACHE_INDEX_OFFSET		/* Get icache line index */
	wic	r5, r0					/* Invalidate data cache line */
	addik	r5, r5, ICACHE_INCREMENT		/* Increment and save entry index */
	andi	r5, r5, ICACHE_MASK
	swi	r5, r6, ICACHE_INDEX_OFFSET
#endif /* HAS_BRAM_ICACHE */

#ifdef HAS_BRAM_MMU_UTLB
L_mmu:
	lwi	r5, r6, MMU_INDEX_OFFSET		/* Get UTLB entry index */
	mts	rtlbx, r5				/* Access next entry in UTLB */
	mts	rtlbhi, r0				/* Clear the UTLB entry */

	addik	r5, r5, 1				/* Increment and save entry index */
	andi	r5, r5, 0x3F
	swi	r5, r6, MMU_INDEX_OFFSET
#endif /* HAS_BRAM_MMU_UTLB */

#ifdef HAS_BRAM_BRANCH_TARGET_CACHE
L_btc:
	lwi	r5, r6, BTC_CALL_COUNT_OFFSET		/* Get BTC call count offset */
	addik	r5, r5, 1				/* Increment and save call count */
	andi	r5, r5, BTC_MASK
	swi	r5, r6, BTC_CALL_COUNT_OFFSET

	bnei	r5, L_skip_btc_scrub			/* Skip scrub unless count wrap */
	bri	4					/* Clear branch target cache */
L_skip_btc_scrub:
#endif /* HAS_BRAM_BRANCH_TARGET_CACHE */

#endif /* FAULT_TOLERANT */
L_done:
	rtsd	r15, 8					/* Return */
	nop
	.end	microblaze_scrub

	/* Persistent data used by this routine */
	.data
	.align	2
L_persistent_data:
	.long	0					/* dlmb index      */
	.long	0					/* dcache index    */
	.long	0					/* icache index    */
	.long	0					/* mmu entry index */
	.long	0					/* btc call count  */
