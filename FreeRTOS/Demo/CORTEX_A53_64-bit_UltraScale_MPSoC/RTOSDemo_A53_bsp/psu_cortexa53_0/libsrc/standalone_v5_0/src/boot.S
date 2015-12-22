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
* @file boot.S
*
* This file contains the initial startup code for the Cortex A53 processor
* Currently the processor starts at EL3 and boot code, startup and main
* code will run on secure EL3.
*
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who     Date     Changes
* ----- ------- -------- ---------------------------------------------------
* 5.00  pkp	5/21/14 Initial version
*
* @note
*
* None.
*
******************************************************************************/

#include "xparameters.h"

.globl MMUTableL0
.globl MMUTableL1
.globl MMUTableL2
.global _prestart
.global _boot

.global __el3_stack
.global __el2_stack
.global __el1_stack
.global __el0_stack
.global _vector_table


.set EL3_stack,		__el3_stack
.set EL2_stack,		__el2_stack
.set EL1_stack,		__el1_stack
.set EL0_stack,		__el0_stack

.set TT_S1_FAULT,	0x0
.set TT_S1_TABLE,	0x3

.set L0Table,	MMUTableL0
.set L1Table,	MMUTableL1
.set L2Table,	MMUTableL2
.set vector_base,	_vector_table

.section .boot,"ax"


/* this initializes the various processor modes */

_prestart:
_boot:
	mov      x0, #0
	mov      x1, #0
	mov      x2, #0
	mov      x3, #0
	mov      x4, #0
	mov      x5, #0
	mov      x6, #0
	mov      x7, #0
	mov      x8, #0
	mov      x9, #0
	mov      x10, #0
	mov      x11, #0
	mov      x12, #0
	mov      x13, #0
	mov      x14, #0
	mov      x15, #0
	mov      x16, #0
	mov      x17, #0
	mov      x18, #0
	mov      x19, #0
	mov      x20, #0
	mov      x21, #0
	mov      x22, #0
	mov      x23, #0
	mov      x24, #0
	mov      x25, #0
	mov      x26, #0
	mov      x27, #0
	mov      x28, #0
	mov      x29, #0
	mov      x30, #0
#if 0 //dont put other a53 cpus in wfi
   //Which core am I
   // ----------------
	mrs      x0, MPIDR_EL1
	and      x0, x0, #0xFF                     //Mask off to leave Aff0
	cbz      x0, OKToRun                          //If core 0, run the primary init code
EndlessLoop0:
	wfi
	b        EndlessLoop0
#endif
OKToRun:

	/*Set vector table base addresses. */
	ldr	x1, =vector_base
	msr	VBAR_EL3,x1
	msr	VBAR_EL2,x1
	msr	VBAR_EL1,x1

	/*Define stack pointer for current exception level*/
	ldr	 x2,=EL3_stack
	mov	 sp,x2

	/* Disable trapping of CPTR_EL3 accesses or use of Adv.SIMD/FPU*/
	mov      x0, #0                 // Clear all trap bits
	msr      CPTR_EL3, x0


	/* Configure SCR_EL3 */
	mov      w1, #0              	//; Initial value of register is unknown
	orr      w1, w1, #(1 << 11)  	//; Set ST bit (Secure EL1 can access CNTPS_TVAL_EL1, CNTPS_CTL_EL1 & CNTPS_CVAL_EL1)
	orr      w1, w1, #(1 << 10)  	//; Set RW bit (EL1 is AArch64, as this is the Secure world)
	orr      w1, w1, #(1 << 3)   	//; Set EA bit (SError routed to EL3)
	orr      w1, w1, #(1 << 2)   	//; Set FIQ bit (FIQs routed to EL3)
	orr      w1, w1, #(1 << 1)   	//; Set IRQ bit (IRQs routed to EL3)
	msr      SCR_EL3, x1

	/*Enable ECC protection*/
	mrs	x0, S3_1_C11_C0_2  	// register L2CTLR_EL1
	orr	x0, x0, #(1<<22)
	msr	S3_1_C11_C0_2, x0

	/*configure cpu auxiliary control register EL1 */
	ldr	x0,=0x80CA000 		// L1 Data prefetch control - 5, Enable device split throttle, 2 independent data prefetch streams
	msr	S3_1_C15_C2_0, x0 	//CPUACTLR_EL1


	/*Enable hardware coherency between cores*/
	mrs      x0, S3_1_c15_c2_1  	//Read EL1 CPU Extended Control Register
	orr      x0, x0, #(1 << 6)  	//Set the SMPEN bit
	msr      S3_1_c15_c2_1, x0  	//Write EL1 CPU Extended Control Register
	isb

	tlbi 	ALLE3
	ic      IALLU                  	//; Invalidate I cache to PoU
	bl 	invalidate_dcaches
	dsb	 sy
	isb

	ldr      x1, =L0Table 		//; Get address of level 0 for TTBR0_EL1
	msr      TTBR0_EL3, x1		//; Set TTBR0_EL3 (NOTE: There is no TTBR1 at EL1)


	/**********************************************
	* Set up memory attributes
	* This equates to:
	* 0 = b01000100 = Normal, Inner/Outer Non-Cacheable
	* 1 = b11111111 = Normal, Inner/Outer WB/WA/RA
	* 2 = b00000000 = Device-nGnRnE
	**********************************************/
	ldr      x1, =0x000000000000FF44
	msr      MAIR_EL3, x1

        /**********************************************
        * Set up TCR_EL3
	* Physical Address Size PS =  010 -> 40bits 1TB
	* Granual Size TG0 = 00 -> 4KB
        * size offset of the memory region T0SZ = 24 -> (region size 2^(64-24) = 2^40)
        ***************************************************/
        ldr     x1,=0x80823518
        msr     TCR_EL3, x1
        isb

	/* Configure SCTLR_EL3 */
	mov      x1, #0                //Most of the SCTLR_EL3 bits are unknown at reset
	orr      x1, x1, #(1 << 12)	//Enable I cache
	orr      x1, x1, #(1 << 3)	//Enable SP alignment check
	orr      x1, x1, #(1 << 2)	//Enable caches
	orr      x1, x1, #(1 << 0)	//Enable MMU
	msr      SCTLR_EL3, x1
	dsb	 sy
	isb

	bl 	 _startup		//jump to start

loop:	b	loop


invalidate_dcaches:

	dmb     ISH
	mrs     x0, CLIDR_EL1          //; x0 = CLIDR
	ubfx    w2, w0, #24, #3        //; w2 = CLIDR.LoC
	cmp     w2, #0                 //; LoC is 0?
	b.eq    invalidateCaches_end   //; No cleaning required and enable MMU
	mov     w1, #0                 //; w1 = level iterator

invalidateCaches_flush_level:
	add     w3, w1, w1, lsl #1     //; w3 = w1 * 3 (right-shift for cache type)
	lsr     w3, w0, w3             //; w3 = w0 >> w3
	ubfx    w3, w3, #0, #3         //; w3 = cache type of this level
	cmp     w3, #2                 //; No cache at this level?
	b.lt    invalidateCaches_next_level

	lsl     w4, w1, #1
	msr     CSSELR_EL1, x4         //; Select current cache level in CSSELR
	isb                            //; ISB required to reflect new CSIDR
	mrs     x4, CCSIDR_EL1         //; w4 = CSIDR

	ubfx    w3, w4, #0, #3
	add    	w3, w3, #2             //; w3 = log2(line size)
	ubfx    w5, w4, #13, #15
	ubfx    w4, w4, #3, #10        //; w4 = Way number
	clz     w6, w4                 //; w6 = 32 - log2(number of ways)

invalidateCaches_flush_set:
	mov     w8, w4                 //; w8 = Way number
invalidateCaches_flush_way:
	lsl     w7, w1, #1             //; Fill level field
	lsl     w9, w5, w3
	orr     w7, w7, w9             //; Fill index field
	lsl     w9, w8, w6
	orr     w7, w7, w9             //; Fill way field
	dc      CISW, x7               //; Invalidate by set/way to point of coherency
	subs    w8, w8, #1             //; Decrement way
	b.ge    invalidateCaches_flush_way
	subs    w5, w5, #1             //; Descrement set
	b.ge    invalidateCaches_flush_set

invalidateCaches_next_level:
	add     w1, w1, #1             //; Next level
	cmp     w2, w1
	b.gt    invalidateCaches_flush_level

invalidateCaches_end:
	ret

.end
