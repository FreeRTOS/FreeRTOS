/*
 * FreeRTOS Kernel V10.1.1
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */
	SECTION intvec:CODE:ROOT(2)
	ARM

	EXTERN pxISRFunction
	EXTERN FreeRTOS_Tick_Handler
	EXTERN FreeRTOS_IRQ_Handler
	EXTERN vCMT_1_Channel_0_ISR
	EXTERN vCMT_1_Channel_1_ISR
	EXTERN r_scifa2_txif2_interrupt
	EXTERN r_scifa2_rxif2_interrupt
	EXTERN r_scifa2_drif2_interrupt
	EXTERN r_scifa2_brif2_interrupt

	PUBLIC FreeRTOS_Tick_Handler_Entry
	PUBLIC vCMT_1_Channel_0_ISR_Entry
	PUBLIC vCMT_1_Channel_1_ISR_Entry
	PUBLIC r_scifa2_txif2_interrupt_entry
	PUBLIC r_scifa2_rxif2_interrupt_entry
	PUBLIC r_scifa2_drif2_interrupt_entry
	PUBLIC r_scifa2_brif2_interrupt_entry

FreeRTOS_Tick_Handler_Entry:
	/* Save used registers (probably not necessary). */
	PUSH	{r0-r1}
	/* Save the address of the C portion of this handler in pxISRFunction. */
	LDR		r0, =pxISRFunction
	LDR		R1, =FreeRTOS_Tick_Handler
	STR		R1, [r0]
	/* Restore used registers then branch to the FreeRTOS IRQ handler. */
	POP		{r0-r1}
	B		FreeRTOS_IRQ_Handler
/*-----------------------------------------------------------*/

vCMT_1_Channel_0_ISR_Entry:
	/* Save used registers (probably not necessary). */
	PUSH	{r0-r1}
	/* Save the address of the C portion of this handler in pxISRFunction. */
	LDR		r0, =pxISRFunction
	LDR		R1, =vCMT_1_Channel_0_ISR
	STR		R1, [r0]
	/* Restore used registers then branch to the FreeRTOS IRQ handler. */
	POP		{r0-r1}
	B		FreeRTOS_IRQ_Handler
/*-----------------------------------------------------------*/

vCMT_1_Channel_1_ISR_Entry:
	/* Save used registers (probably not necessary). */
	PUSH	{r0-r1}
	/* Save the address of the C portion of this handler in pxISRFunction. */
	LDR		r0, =pxISRFunction
	LDR		R1, =vCMT_1_Channel_1_ISR
	STR		R1, [r0]
	/* Restore used registers then branch to the FreeRTOS IRQ handler. */
	POP		{r0-r1}
	B		FreeRTOS_IRQ_Handler
/*-----------------------------------------------------------*/

r_scifa2_txif2_interrupt_entry:
	/* Save used registers (probably not necessary). */
	PUSH	{r0-r1}
	/* Save the address of the C portion of this handler in pxISRFunction. */
	LDR		r0, =pxISRFunction
	LDR		R1, =r_scifa2_txif2_interrupt
	STR		R1, [r0]
	/* Restore used registers then branch to the FreeRTOS IRQ handler. */
	POP		{r0-r1}
	B		FreeRTOS_IRQ_Handler
/*-----------------------------------------------------------*/

r_scifa2_rxif2_interrupt_entry:
	/* Save used registers (probably not necessary). */
	PUSH	{r0-r1}
	/* Save the address of the C portion of this handler in pxISRFunction. */
	LDR		r0, =pxISRFunction
	LDR		R1, =r_scifa2_rxif2_interrupt
	STR		R1, [r0]
	/* Restore used registers then branch to the FreeRTOS IRQ handler. */
	POP		{r0-r1}
	B		FreeRTOS_IRQ_Handler
/*-----------------------------------------------------------*/

r_scifa2_drif2_interrupt_entry:
	/* Save used registers (probably not necessary). */
	PUSH	{r0-r1}
	/* Save the address of the C portion of this handler in pxISRFunction. */
	LDR		r0, =pxISRFunction
	LDR		R1, =r_scifa2_drif2_interrupt
	STR		R1, [r0]
	/* Restore used registers then branch to the FreeRTOS IRQ handler. */
	POP		{r0-r1}
	B		FreeRTOS_IRQ_Handler
/*-----------------------------------------------------------*/

r_scifa2_brif2_interrupt_entry:
	/* Save used registers (probably not necessary). */
	PUSH	{r0-r1}
	/* Save the address of the C portion of this handler in pxISRFunction. */
	LDR		r0, =pxISRFunction
	LDR		R1, =r_scifa2_brif2_interrupt
	STR		R1, [r0]
	/* Restore used registers then branch to the FreeRTOS IRQ handler. */
	POP		{r0-r1}
	B		FreeRTOS_IRQ_Handler

	END
