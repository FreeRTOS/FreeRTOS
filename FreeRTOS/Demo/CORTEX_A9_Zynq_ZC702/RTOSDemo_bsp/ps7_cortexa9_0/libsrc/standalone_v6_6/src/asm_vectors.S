/******************************************************************************
*
* Copyright (C) 2009 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file asm_vectors.s
*
* This file contains the initial vector table for the Cortex A9 processor
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who     Date     Changes
* ----- ------- -------- ---------------------------------------------------
* 1.00a ecm/sdm 10/20/09 Initial version
* 3.05a sdm	02/02/12 Save lr when profiling is enabled
* 3.10a srt     04/18/13 Implemented ARM Erratas. Please refer to file
*			 'xil_errata.h' for errata description
* 4.00a pkp	22/01/14 Modified return addresses for interrupt
*			 handlers (DataAbortHandler and SVCHandler)
*			 to fix CR#767251
* 5.1	pkp	05/13/15 Saved the addresses of instruction causing data
*			 abort and prefetch abort into DataAbortAddr and
*			 PrefetchAbortAddr for further use to fix CR#854523
* 5.4	pkp	12/03/15 Added handler for undefined exception
* </pre>
*
* @note
*
* None.
*
******************************************************************************/
#include "xil_errata.h"

#define __ARM_NEON__ 1

.org 0
.text

.globl _vector_table

.section .vectors
_vector_table:
	B	_boot
	B	Undefined
	B	SVCHandler
	B	PrefetchAbortHandler
	B	DataAbortHandler
	NOP	/* Placeholder for address exception vector*/
	B	IRQHandler
	B	FIQHandler


IRQHandler:					/* IRQ vector handler */

	stmdb	sp!,{r0-r3,r12,lr}		/* state save from compiled code*/
#ifdef __ARM_NEON__
	vpush {d0-d7}
	vpush {d16-d31}
	vmrs r1, FPSCR
	push {r1}
	vmrs r1, FPEXC
	push {r1}
#endif

#ifdef PROFILING
	ldr	r2, =prof_pc
	subs	r3, lr, #0
	str	r3, [r2]
#endif

	bl	IRQInterrupt			/* IRQ vector */

#ifdef __ARM_NEON__
	pop 	{r1}
	vmsr    FPEXC, r1
	pop 	{r1}
	vmsr    FPSCR, r1
	vpop    {d16-d31}
	vpop    {d0-d7}
#endif
	ldmia	sp!,{r0-r3,r12,lr}		/* state restore from compiled code */


	subs	pc, lr, #4			/* adjust return */


FIQHandler:					/* FIQ vector handler */
	stmdb	sp!,{r0-r3,r12,lr}		/* state save from compiled code */
#ifdef __ARM_NEON__
	vpush {d0-d7}
	vpush {d16-d31}
	vmrs r1, FPSCR
	push {r1}
	vmrs r1, FPEXC
	push {r1}
#endif

FIQLoop:
	bl	FIQInterrupt			/* FIQ vector */

#ifdef __ARM_NEON__
	pop 	{r1}
	vmsr    FPEXC, r1
	pop 	{r1}
	vmsr    FPSCR, r1
	vpop    {d16-d31}
	vpop    {d0-d7}
#endif
	ldmia	sp!,{r0-r3,r12,lr}		/* state restore from compiled code */
	subs	pc, lr, #4			/* adjust return */


Undefined:					/* Undefined handler */
	stmdb	sp!,{r0-r3,r12,lr}		/* state save from compiled code */
	ldr     r0, =UndefinedExceptionAddr
	sub     r1, lr, #4
	str     r1, [r0]            		/* Store address of instruction causing undefined exception */

	bl	UndefinedException		/* UndefinedException: call C function here */
	ldmia	sp!,{r0-r3,r12,lr}		/* state restore from compiled code */
	movs	pc, lr

SVCHandler:					/* SWI handler */
	stmdb	sp!,{r0-r3,r12,lr}		/* state save from compiled code */

	tst	r0, #0x20			/* check the T bit */
	ldrneh	r0, [lr,#-2]			/* Thumb mode */
	bicne	r0, r0, #0xff00			/* Thumb mode */
	ldreq	r0, [lr,#-4]			/* ARM mode */
	biceq	r0, r0, #0xff000000		/* ARM mode */

	bl	SWInterrupt			/* SWInterrupt: call C function here */

	ldmia	sp!,{r0-r3,r12,lr}		/* state restore from compiled code */

	movs	pc, lr		/*return to the next instruction after the SWI instruction */


DataAbortHandler:				/* Data Abort handler */
#ifdef CONFIG_ARM_ERRATA_775420
	dsb
#endif
	stmdb	sp!,{r0-r3,r12,lr}		/* state save from compiled code */
	ldr     r0, =DataAbortAddr
	sub     r1, lr, #8
	str     r1, [r0]            		/* Stores instruction causing data abort */

	bl	DataAbortInterrupt		/*DataAbortInterrupt :call C function here */

	ldmia	sp!,{r0-r3,r12,lr}		/* state restore from compiled code */

	subs	pc, lr, #8			/* points to the instruction that caused the Data Abort exception */

PrefetchAbortHandler:				/* Prefetch Abort handler */
#ifdef CONFIG_ARM_ERRATA_775420
	dsb
#endif
	stmdb	sp!,{r0-r3,r12,lr}		/* state save from compiled code */
	ldr     r0, =PrefetchAbortAddr
	sub     r1, lr, #4
	str     r1, [r0]            		/* Stores instruction causing prefetch abort */

	bl	PrefetchAbortInterrupt		/* PrefetchAbortInterrupt: call C function here */

	ldmia	sp!,{r0-r3,r12,lr}		/* state restore from compiled code */

	subs	pc, lr, #4			/* points to the instruction that caused the Prefetch Abort exception */

.end
