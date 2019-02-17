/*
 * FreeRTOS Kernel V10.2.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/*
 * This file contains the non-portable and therefore RZ/T specific parts of
 * the IntQueue standard demo task - namely the configuration of the timers
 * that generate the interrupts and the interrupt entry points.
 */

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "IntQueueTimer.h"
#include "IntQueue.h"

/* Renesas includes. */
#include "r_cg_macrodriver.h"
#include "r_cg_cmt.h"
#include "r_reset.h"

#define tmrCMT_1_CHANNEL_0_HZ	( 4000UL )
#define tmrCMT_1_CHANNEL_1_HZ	( 2011UL )

/*
 * Handlers for the two timers used.  See the documentation page
 * for this port on TBD for more information on writing
 * interrupt handlers.
 */
void vCMT_1_Channel_0_ISR( void );
void vCMT_1_Channel_1_ISR( void );

/*
 * Entry point for the handlers.  These set the pxISRFunction variable to point
 * to the C handler for each timer, then branch to the FreeRTOS IRQ handler.
 */
#ifdef __GNUC__
	static void vCMT_1_Channel_0_ISR_Entry( void ) __attribute__((naked));
	static void vCMT_1_Channel_1_ISR_Entry( void ) __attribute__((naked));
#endif /* __GNUC__ */
#ifdef __ICCARM__
	/* IAR requires the entry point to be in an assembly file.  The functions
	are	implemented in $PROJ_DIR$/System/IAR/Interrupt_Entry_Stubs.asm. */
	extern void vCMT_1_Channel_0_ISR_Entry( void );
	extern void vCMT_1_Channel_1_ISR_Entry( void );
#endif /* __ICCARM__ */
/*-----------------------------------------------------------*/

void vInitialiseTimerForIntQueueTest( void )
{
uint32_t ulCompareMatchValue;
const uint32_t ulPeripheralClockDivider = 6UL, ulCMTClockDivider = 8UL;

	/* Disable CMI2 and CMI3 interrupts. */
	VIC.IEC0.LONG = ( 1UL << 23UL ) | ( 1UL << 24UL );

	/* Cancel CMT stop state in LPC. */
	r_rst_write_enable();
	MSTP( CMT1 ) = 0U;
	r_rst_write_disable();

	/* Interrupt on compare match. */
	CMT2.CMCR.BIT.CMIE = 1;
	CMT3.CMCR.BIT.CMIE = 1;

	/* Calculate the compare match value. */
	ulCompareMatchValue = configCPU_CLOCK_HZ / ulPeripheralClockDivider;
	ulCompareMatchValue /= ulCMTClockDivider;
	ulCompareMatchValue /= tmrCMT_1_CHANNEL_0_HZ;
	ulCompareMatchValue -= 1UL;
	CMT2.CMCOR = ( unsigned short ) ulCompareMatchValue;

	ulCompareMatchValue = configCPU_CLOCK_HZ / ulPeripheralClockDivider;
	ulCompareMatchValue /= ulCMTClockDivider;
	ulCompareMatchValue /= tmrCMT_1_CHANNEL_1_HZ;
	ulCompareMatchValue -= 1UL;
	CMT3.CMCOR = ( unsigned short ) ulCompareMatchValue;

	/* Divide the PCLK by 8. */
	CMT2.CMCR.BIT.CKS = 0;
	CMT3.CMCR.BIT.CKS = 0;

	/* Clear count to 0. */
	CMT2.CMCNT = 0;
	CMT3.CMCNT = 0;

	/* Set CMI2 and CMI3 edge detection type. */
	VIC.PLS0.LONG |= ( 1UL << 23UL ) | ( 1UL << 24UL );

	/* Set CMI2 and CMI3 priority levels so they nest. */
	VIC.PRL23.LONG = _CMT_PRIORITY_LEVEL2;
	VIC.PRL24.LONG = _CMT_PRIORITY_LEVEL9;

	/* Set CMI2 and CMI3 interrupt address. */
	VIC.VAD23.LONG = ( uint32_t ) vCMT_1_Channel_0_ISR_Entry;
	VIC.VAD24.LONG = ( uint32_t ) vCMT_1_Channel_1_ISR_Entry;

    /* Enable CMI2 and CMI3 interrupts in ICU. */
	VIC.IEN0.LONG |= ( 1UL << 23UL ) | ( 1UL << 24UL );

    /* Start CMT1 channel 0 and 1 count. */
    CMT.CMSTR1.BIT.STR2 = 1U;
	CMT.CMSTR1.BIT.STR3 = 1U;
}
/*-----------------------------------------------------------*/

void vCMT_1_Channel_0_ISR( void )
{
	/* Clear the interrupt. */
	VIC.PIC0.LONG = ( 1UL << 23UL );

	/* Call the handler that is part of the common code - this is where the
	non-portable code ends and the actual test is performed. */
	portYIELD_FROM_ISR( xFirstTimerHandler() );
}
/*-----------------------------------------------------------*/

void vCMT_1_Channel_1_ISR( void )
{
	/* Clear the interrupt. */
	VIC.PIC0.LONG = ( 1UL << 24UL );

	/* Call the handler that is part of the common code - this is where the
	non-portable code ends and the actual test is performed. */
	portYIELD_FROM_ISR( xSecondTimerHandler() );
}
/*-----------------------------------------------------------*/

/*
 * The RZ/T vectors directly to a peripheral specific interrupt handler, rather
 * than using the Cortex-R IRQ vector.  Therefore each interrupt handler
 * installed by the application must follow the examples below, which save a
 * pointer to a standard C function in the pxISRFunction variable, before
 * branching to the FreeRTOS IRQ handler.  The FreeRTOS IRQ handler then manages
 * interrupt entry (including interrupt nesting), before calling the C function
 * saved in the pxISRFunction variable.  NOTE:  The entry points are naked
 * functions - do not add C code to these functions.
 *
 * See http://www.freertos.org/Renesas_RZ-T_Cortex-R4F-RTOS.html
 */
#ifdef __GNUC__
	/* The IAR equivalent is implemented in
	$PROJ_DIR$/System/IAR/Interrupt_Entry_Stubs.asm */
	static void vCMT_1_Channel_0_ISR_Entry( void )
	{
		__asm volatile (
							"PUSH	{r0-r1}								\t\n"
							"LDR	r0, =pxISRFunction					\t\n"
							"LDR	r1, =vCMT_1_Channel_0_ISR			\t\n"
							"STR	r1, [r0]							\t\n"
							"POP	{r0-r1}								\t\n"
							"B		FreeRTOS_IRQ_Handler					"
						);
	}
#endif /* __GNUC__ */
/*-----------------------------------------------------------*/

#ifdef __GNUC__
	/* The IAR equivalent is implemented in
	$PROJ_DIR$/System/IAR/Interrupt_Entry_Stubs.asm */
	static void vCMT_1_Channel_1_ISR_Entry( void )
	{
		__asm volatile (
							"PUSH	{r0-r1}								\t\n"
							"LDR	r0, =pxISRFunction					\t\n"
							"LDR	r1, =vCMT_1_Channel_1_ISR			\t\n"
							"STR	r1, [r0]							\t\n"
							"POP	{r0-r1}								\t\n"
							"B		FreeRTOS_IRQ_Handler					"
						);
	}
#endif /* __GNUC__ */





