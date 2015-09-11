/*
    FreeRTOS V8.2.2 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "ISR_Support.h"

/* Renesas includes. */
#include "r_cg_macrodriver.h"
#include "r_cg_cmt.h"
#include "r_reset.h"

/*-----------------------------------------------------------*/

/*
 * Entry point for the FreeRTOS tick interrupt.  This provides the prolog code
 * necessary to support interrupt nesting.
 */
static void FreeRTOS_Tick_Handler_Entry( void ) __attribute__((naked));

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

#warning Tick rate is not yet accurate.
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

static void FreeRTOS_Tick_Handler_Entry( void )
{
	/* This is a naked function, and should not include any C code. */
	portNESTING_INTERRUPT_ENTRY();
	__asm volatile( " LDR		r1, vTickHandlerConst				\t\n"
					" BLX		r1									\t\n"
					" vTickHandlerConst: .word FreeRTOS_Tick_Handler	" );
	portNESTING_INTERRUPT_EXIT();
}
/*-----------------------------------------------------------*/




