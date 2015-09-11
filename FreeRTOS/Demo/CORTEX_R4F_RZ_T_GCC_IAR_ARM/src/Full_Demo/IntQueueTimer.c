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

#define tmrCMT_1_CHANNEL_0_HZ	( 2000UL )
#define tmrCMT_1_CHANNEL_1_HZ	( 2011UL )

/* Handlers for the two timers used.  See the documentation page
for this port on http://www.FreeRTOS.org for more information on writing
interrupt handlers. */
void vCMT_1_Channel_0_ISR( void );
void vCMT_1_Channel_1_ISR( void );

/*-----------------------------------------------------------*/

void vInitialiseTimerForIntQueueTest( void )
{
uint32_t ulCompareMatchValue;
const uint32_t ulPeripheralClockDivider = 6UL, ulCMTClockDivider = 8UL;
extern void FreeRTOS_IRQ_Handler( void );

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
	VIC.PRL23.LONG = _CMT_PRIORITY_LEVEL10;
	VIC.PRL24.LONG = _CMT_PRIORITY_LEVEL9;

	/* Set CMI2 and CMI3 interrupt address. */
#warning Int 1 timer handler addresses not set.
	VIC.VAD23.LONG = ( uint32_t ) NULL;
	VIC.VAD24.LONG = ( uint32_t ) NULL;

    /* Enable CMI2 and CMI3 interrupts in ICU. */
    VIC.IEN0.LONG |= ( 1UL << 23UL ) | ( 1UL << 24UL );

    /* Start CMT1 channel 0 and 1 count. */
    CMT.CMSTR1.BIT.STR2 = 1U;
	CMT.CMSTR1.BIT.STR3 = 1U;
}
/*-----------------------------------------------------------*/

void vCMT_1_Channel_0_ISR( void )
{
	/* Re-enabled interrupts. */
	taskENABLE_INTERRUPTS();

	/* Call the handler that is part of the common code - this is where the
	non-portable code ends and the actual test is performed. */
	portYIELD_FROM_ISR( xFirstTimerHandler() );
}
/*-----------------------------------------------------------*/

void vCMT_1_Channel_1_ISR( void )
{
	/* Re-enabled interrupts. */
	portENABLE_INTERRUPTS();

	/* Call the handler that is part of the common code - this is where the
	non-portable code ends and the actual test is performed. */
	portYIELD_FROM_ISR( xSecondTimerHandler() );
}
/*-----------------------------------------------------------*/






