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
* @file asm_vectors.s
*
* This file contains the initial vector table for the Cortex R5 processor
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who     Date     Changes
* ----- ------- -------- ---------------------------------------------------
* 5.00  pkp	02/10/14 Initial version
* </pre>
*
* @note
*
* None.
*
******************************************************************************/
.org 0
.text

.globl _boot
.globl _freertos_vector_table

.globl FreeRTOS_FIQInterrupt
.globl FreeRTOS_DataAbortHandler
.globl FreeRTOS_PrefetchAbortHandler
.globl vPortInstallFreeRTOSVectorTable

.globl IRQHandler
.globl prof_pc

.extern FreeRTOS_IRQ_Handler
.extern FreeRTOS_SWI_Handler


.section .freertos_vectors
_freertos_vector_table:
	ldr	pc,=_boot
	ldr	pc,=FreeRTOS_Undefined
	LDR pc, _swi
	ldr	pc,=FreeRTOS_PrefetchAbortHandler
	ldr	pc,=FreeRTOS_DataAbortHandler
	NOP	/* Placeholder for address exception vector*/
	LDR pc, _irq
	ldr	pc,=FreeRTOS_FIQHandler

_irq:   .word FreeRTOS_IRQ_Handler
_swi:   .word FreeRTOS_SWI_Handler


.text

FreeRTOS_FIQHandler:			/* FIQ vector handler */
	stmdb	sp!,{r0-r3,r12,lr}	/* state save from compiled code */
FreeRTOS_FIQLoop:
	bl	FIQInterrupt			/* FIQ vector */
	ldmia	sp!,{r0-r3,r12,lr}	/* state restore from compiled code */
	subs	pc, lr, #4			/* adjust return */

FreeRTOS_Undefined:				/* Undefined handler */
	b	FreeRTOS_Undefined

FreeRTOS_DataAbortHandler:		/* Data Abort handler */
	b	FreeRTOS_DataAbortHandler

FreeRTOS_PrefetchAbortHandler:	/* Prefetch Abort handler */
	b	FreeRTOS_PrefetchAbortHandler


.end
