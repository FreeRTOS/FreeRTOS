/******************************************************************************
*
* Copyright (C) 2014 - 2015 Xilinx, Inc. All rights reserved.
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
* @addtogroup r5_boot_code Cortex R5 Processor Boot Code
* @{
* <h2> boot.S </h2>
* The boot code performs minimum configuration which is required for an
* application to run starting from processor's reset state. Below is a
* sequence illustrating what all configuration is performed before control
* reaches to main function.
*
* 1. Program vector table base for exception handling
* 2. Program stack pointer for various modes (IRQ, FIQ, supervisor, undefine,
*    abort, system)
* 3. Disable instruction cache, data cache and MPU
* 4. Invalidate instruction and data cache
* 5. Configure MPU with short descriptor translation table format and program
*    base address of translation table
* 6. Enable data cache, instruction cache and MPU
* 7. Enable Floating point unit
* 8. Transfer control to _start which clears BSS sections and jumping to main
*    application
*
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- ---------------------------------------------------
* 5.00  pkp  02/10/14 Initial version
* 5.04	pkp  09/11/15 Disabled ACTLR.DBWR bit to avoid potential R5 deadlock
*		      for errata 780125
* 5.04 pkp   02/04/16 Enabled the fault log for lock-step mode
* 5.04 pkp   02/25/16 Initialized the banked registers for various modes,
*		      initialized floating point registers and enabled the
*		      cache ECC check before enabling the fault log for
*		      lock step mode
* 5.04 pkp   03/24/16 Reset the dbg_lpd_reset before enabling the fault log
*		      to avoid intervention for lock-step mode
* 5.05 pkp   04/11/16 Enable the comparators for non-JTAG boot mode for
*		      lock-step to avoid putting debug logic to reset
* 6.02 pkp   02/13/17 Added support for hard float
* 6.6  mus   02/23/17 Enable/Disable the debug logic in non-JTAG boot mode(when
*		      processor is in lockstep configuration), based
*		      on the mld parameter "lockstep_mode_debug".
* </pre>
*
******************************************************************************/

#include "xparameters.h"


.global _prestart
.global _boot
.global __stack
.global __irq_stack
.global __supervisor_stack
.global __abort_stack
.global __fiq_stack
.global __undef_stack
.global _vector_table


/* Stack Pointer locations for boot code */
.set Undef_stack,	__undef_stack
.set FIQ_stack,		__fiq_stack
.set Abort_stack,	__abort_stack
.set SPV_stack,		__supervisor_stack
.set IRQ_stack,		__irq_stack
.set SYS_stack,		__stack

.set vector_base,	_vector_table

.set RPU_GLBL_CNTL,	0xFF9A0000
.set RPU_ERR_INJ,	0xFF9A0020
.set RST_LPD_DBG,	0xFF5E0240
.set BOOT_MODE_USER,	0xFF5E0200
.set fault_log_enable,	0x101

.section .boot,"axS"


/* this initializes the various processor modes */

_prestart:
_boot:

OKToRun:

/* Initialize processor registers to 0 */
	mov	r0,#0
	mov	r1,#0
	mov	r2,#0
	mov	r3,#0
	mov	r4,#0
	mov	r5,#0
	mov	r6,#0
	mov	r7,#0
	mov	r8,#0
	mov	r9,#0
	mov	r10,#0
	mov	r11,#0
	mov	r12,#0

/* Initialize stack pointer and banked registers for various mode */
	mrs	r0, cpsr			/* get the current PSR */
	mvn	r1, #0x1f			/* set up the irq stack pointer */
	and	r2, r1, r0
	orr	r2, r2, #0x12			/* IRQ mode */
	msr	cpsr, r2
	ldr	r13,=IRQ_stack			/* IRQ stack pointer */
	mov 	r14,#0

	mrs	r0, cpsr			/* get the current PSR */
	mvn	r1, #0x1f			/* set up the supervisor stack pointer */
	and	r2, r1, r0
	orr	r2, r2, #0x13			/* supervisor mode */
	msr	cpsr, r2
	ldr	r13,=SPV_stack			/* Supervisor stack pointer */
	mov 	r14,#0

	mrs	r0, cpsr			/* get the current PSR */
	mvn	r1, #0x1f			/* set up the Abort  stack pointer */
	and	r2, r1, r0
	orr	r2, r2, #0x17			/* Abort mode */
	msr	cpsr, r2
	ldr	r13,=Abort_stack		/* Abort stack pointer */
	mov 	r14,#0

	mrs	r0, cpsr			/* get the current PSR */
	mvn	r1, #0x1f			/* set up the FIQ stack pointer */
	and	r2, r1, r0
	orr	r2, r2, #0x11			/* FIQ mode */
	msr	cpsr, r2
	mov 	r8, #0
	mov 	r9, #0
	mov 	r10, #0
	mov 	r11, #0
	mov 	r12, #0
	ldr	r13,=FIQ_stack			/* FIQ stack pointer */
	mov 	r14,#0

	mrs	r0, cpsr			/* get the current PSR */
	mvn	r1, #0x1f			/* set up the Undefine stack pointer */
	and	r2, r1, r0
	orr	r2, r2, #0x1b			/* Undefine mode */
	msr	cpsr, r2
	ldr	r13,=Undef_stack		/* Undefine stack pointer */
	mov 	r14,#0

	mrs	r0, cpsr			/* get the current PSR */
	mvn	r1, #0x1f			/* set up the system stack pointer */
	and	r2, r1, r0
	orr	r2, r2, #0x1F			/* SYS mode */
	msr	cpsr, r2
	ldr	r13,=SYS_stack			/* SYS stack pointer */
	mov 	r14,#0

/*
 * Enable access to VFP by enabling access to Coprocessors 10 and 11.
 * Enables Full Access i.e. in both privileged and non privileged modes
 */
	mrc     p15, 0, r0, c1, c0, 2      	/* Read Coprocessor Access Control Register (CPACR) */
        orr     r0, r0, #(0xF << 20)       	/* Enable access to CP 10 & 11 */
        mcr     p15, 0, r0, c1, c0, 2      	/* Write Coprocessor Access Control Register (CPACR) */
        isb

/* enable fpu access  */
	vmrs	r3, FPEXC
	orr	r1, r3, #(1<<30)
	vmsr	FPEXC, r1

/* clear the floating point register*/
	mov	r1,#0
	vmov	d0,r1,r1
	vmov	d1,r1,r1
	vmov	d2,r1,r1
	vmov	d3,r1,r1
	vmov	d4,r1,r1
	vmov	d5,r1,r1
	vmov	d6,r1,r1
	vmov	d7,r1,r1
	vmov	d8,r1,r1
	vmov	d9,r1,r1
	vmov	d10,r1,r1
	vmov	d11,r1,r1
	vmov	d12,r1,r1
	vmov	d13,r1,r1
	vmov	d14,r1,r1
	vmov	d15,r1,r1

#ifdef __SOFTFP__
/* Disable the FPU if SOFTFP is defined*/
	vmsr	FPEXC,r3
#endif

/* Disable MPU and caches */
        mrc     p15, 0, r0, c1, c0, 0       	/* Read CP15 Control Register*/
        bic     r0, r0, #0x05               	/* Disable MPU (M bit) and data cache (C bit) */
        bic     r0, r0, #0x1000             	/* Disable instruction cache (I bit) */
        dsb                                 	/* Ensure all previous loads/stores have completed */
        mcr     p15, 0, r0, c1, c0, 0       	/* Write CP15 Control Register */
        isb                                 	/* Ensure subsequent insts execute wrt new MPU settings */

/* Disable Branch prediction, TCM ECC checks */
        mrc     p15, 0, r0, c1, c0, 1       	/* Read ACTLR */
        orr     r0, r0, #(0x1 << 17)        	/* Enable RSDIS bit 17 to disable the return stack */
        orr     r0, r0, #(0x1 << 16)        	/* Clear BP bit 15 and set BP bit 16:*/
        bic     r0, r0, #(0x1 << 15)        	/* Branch always not taken and history table updates disabled*/
        orr     r0, r0, #(0x1 << 27)		/* Enable B1TCM ECC check */
        orr     r0, r0, #(0x1 << 26)		/* Enable B0TCM ECC check */
        orr     r0, r0, #(0x1 << 25)		/* Enable ATCM ECC check */
	bic	r0, r0, #(0x1 << 5)		/* Generate abort on parity errors, with [5:3]=b 000*/
	bic 	r0, r0, #(0x1 << 4)
	bic	r0, r0, #(0x1 << 3)
        mcr     p15, 0, r0, c1, c0, 1       	/* Write ACTLR*/
	dsb				    	/* Complete all outstanding explicit memory operations*/

/* Invalidate caches */
	mov	r0,#0				/* r0 = 0  */
	dsb
	mcr	p15, 0, r0, c7, c5, 0		/* invalidate icache */
	mcr 	p15, 0, r0, c15, c5, 0      	/* Invalidate entire data cache*/
	isb
#if LOCKSTEP_MODE_DEBUG == 0
/* enable fault log for lock step */
	ldr	r0,=RPU_GLBL_CNTL
	ldr	r1, [r0]
	ands	r1, r1, #0x8
/* branch to initialization if split mode*/
	bne 	init
/* check for boot mode if in lock step, branch to init if JTAG boot mode*/
	ldr	r0,=BOOT_MODE_USER
	ldr 	r1, [r0]
	ands	r1, r1, #0xF
	beq 	init
/* reset the debug logic */
	ldr	r0,=RST_LPD_DBG
	ldr	r1, [r0]
	orr	r1, r1, #(0x1 << 1)
	orr	r1, r1, #(0x1 << 4)
	orr	r1, r1, #(0x1 << 5)
	str	r1, [r0]
/* enable fault log */
	ldr	r0,=RPU_ERR_INJ
	ldr	r1,=fault_log_enable
	ldr	r2, [r0]
	orr	r2, r2, r1
	str	r2, [r0]
	nop
	nop
#endif

init:
	bl 	Init_MPU		/* Initialize MPU */

/* Enable Branch prediction */
	mrc     p15, 0, r0, c1, c0, 1       /* Read ACTLR*/
        bic     r0, r0, #(0x1 << 17)        /* Clear RSDIS bit 17 to enable return stack*/
        bic     r0, r0, #(0x1 << 16)        /* Clear BP bit 15 and BP bit 16:*/
        bic     r0, r0, #(0x1 << 15)        /* Normal operation, BP is taken from the global history table.*/
        orr	r0, r0, #(0x1 << 14)	    /* Disable DBWR for errata 780125 */
	mcr     p15, 0, r0, c1, c0, 1       /* Write ACTLR*/

/* Enable icahce and dcache */
	mrc 	p15,0,r1,c1,c0,0
	ldr	r0, =0x1005
	orr 	r1,r1,r0
	dsb
	mcr	p15,0,r1,c1,c0,0		/* Enable cache  */
	isb					/* isb	flush prefetch buffer */

/* Warning message to be removed after 2016.1 */
/* USEAMP was introduced in 2015.4 with ZynqMP and caused confusion with USE_AMP */
#ifdef USEAMP
#warning "-DUSEAMP=1 is deprecated, use -DVEC_TABLE_IN_OCM instead to set vector table in OCM"
#endif

/* Set vector table in TCM/LOVEC */
#ifndef VEC_TABLE_IN_OCM
	mrc	p15, 0, r0, c1, c0, 0
	mvn	r1, #0x2000
	and	r0, r0, r1
	mcr	p15, 0, r0, c1, c0, 0
#endif

/* enable asynchronous abort exception */
	mrs	r0, cpsr
	bic	r0, r0, #0x100
	msr	cpsr_xsf, r0

        b 	_startup                       /* jump to C startup code */


.Ldone:	b	.Ldone				/* Paranoia: we should never get here */


.end
/**
* @} End of "addtogroup r5_boot_code".
*/
