/*
 * FreeRTOS Kernel V10.0.1
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* Renesas includes. */
#include "r_cg_macrodriver.h"
#include "r_cg_cmt.h"
#include "r_reset.h"

/*-----------------------------------------------------------*/

/*
 * Entry point for the FreeRTOS tick interrupt.  This sets the pxISRFunction
 * variable to point to the RTOS tick handler, then branches to the FreeRTOS
 * IRQ handler.
 */
#ifdef __GNUC__
	static void FreeRTOS_Tick_Handler_Entry( void ) __attribute__((naked));
#endif /* __GNUC__ */
#ifdef __ICCARM__
	/* IAR requires the entry point to be in an assembly file.  The function is
	implemented in $PROJ_DIR$/System/IAR/Interrupt_Entry_Stubs.asm. */
	extern void FreeRTOS_Tick_Handler_Entry( void );
#endif /* __ICCARM__ */

/*
 * The FreeRTOS IRQ handler, which is implemented in the RTOS port layer.
 */
extern void FreeRTOS_IRQ_Handler( void );

/*
 * The function called by the FreeRTOS_IRQ_Handler() to call the actual
 * peripheral handler.
 */
void vApplicationIRQHandler( void );

/*-----------------------------------------------------------*/

/*
 * Variable used to hold the address of the interrupt handler the FreeRTOS IRQ
 * handler will branch to.
 */
ISRFunction_t pxISRFunction = NULL;

/*-----------------------------------------------------------*/

/*
 * The application must provide a function that configures a peripheral to
 * create the FreeRTOS tick interrupt, then define configSETUP_TICK_INTERRUPT()
 * in FreeRTOSConfig.h to call the function.
 */
void vConfigureTickInterrupt( void )
{
uint32_t ulCompareMatchValue;
const uint32_t ulPeripheralClockDivider = 6UL, ulCMTClockDivider = 8UL;

	/* Disable CMI5 interrupt. */
	VIC.IEC9.LONG = 0x00001000UL;

	/* Cancel CMT stop state in LPC. */
	r_rst_write_enable();
	MSTP( CMT2 ) = 0U;
	r_rst_write_disable();

	/* Interrupt on compare match. */
	CMT5.CMCR.BIT.CMIE = 1;

	/* Calculate the compare match value. */
	ulCompareMatchValue = configCPU_CLOCK_HZ / ulPeripheralClockDivider;
	ulCompareMatchValue /= ulCMTClockDivider;
	ulCompareMatchValue /= configTICK_RATE_HZ;
	ulCompareMatchValue -= 1UL;

	/* Set the compare match value. */
	CMT5.CMCOR = ( unsigned short ) ulCompareMatchValue;

	/* Divide the PCLK by 8. */
	CMT5.CMCR.BIT.CKS = 0;

	CMT5.CMCNT = 0;

	/* Set CMI5 edge detection type. */
	VIC.PLS9.LONG |= 0x00001000UL;

	/* Set CMI5 priority level to the lowest possible. */
	VIC.PRL300.LONG = _CMT_PRIORITY_LEVEL31;

	/* Set CMI5 interrupt address */
	VIC.VAD300.LONG = ( uint32_t ) FreeRTOS_Tick_Handler_Entry;

	/* Enable CMI5 interrupt in ICU. */
	VIC.IEN9.LONG |= 0x00001000UL;

	/* Start CMT5 count. */
	CMT.CMSTR2.BIT.STR5 = 1U;
}
/*-----------------------------------------------------------*/

/*
 * The function called by the FreeRTOS IRQ handler, after it has managed
 * interrupt entry.  This function creates a local copy of pxISRFunction before
 * re-enabling interrupts and actually calling the handler pointed to by
 * pxISRFunction.
 */
void vApplicationIRQHandler( void )
{
ISRFunction_t pxISRToCall = pxISRFunction;

	portENABLE_INTERRUPTS();

	/* Call the installed ISR. */
	pxISRToCall();
}
/*-----------------------------------------------------------*/

/*
 * The RZ/T vectors directly to a peripheral specific interrupt handler, rather
 * than using the Cortex-R IRQ vector.  Therefore each interrupt handler
 * installed by the application must follow the example below, which saves a
 * pointer to a standard C function in the pxISRFunction variable, before
 * branching to the FreeRTOS IRQ handler.  The FreeRTOS IRQ handler then manages
 * interrupt entry (including interrupt nesting), before calling the C function
 * saved in the pxISRFunction variable.  NOTE:  This entry point is a naked
 * function - do not add C code to this function.
 */
#ifdef __GNUC__
	/* The IAR equivalent is implemented in
	$PROJ_DIR$/System/IAR/Interrupt_Entry_Stubs.asm */
	static void FreeRTOS_Tick_Handler_Entry( void )
	{
		__asm volatile (
							"PUSH	{r0-r1}								\t\n"
							"LDR	r0, =pxISRFunction					\t\n"
							"LDR	R1, =FreeRTOS_Tick_Handler			\t\n"
							"STR	R1, [r0]							\t\n"
							"POP	{r0-r1}								\t\n"
							"B		FreeRTOS_IRQ_Handler					"
						);
	}
#endif /* __GNUC__ */
/*-----------------------------------------------------------*/




