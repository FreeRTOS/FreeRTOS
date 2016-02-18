/*
    FreeRTOS V9.0.0rc1 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

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
 * This file contains the non-portable and therefore RX62N specific parts of
 * the IntQueue standard demo task - namely the configuration of the timers
 * that generate the interrupts and the interrupt entry points.
 */

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "IntQueueTimer.h"
#include "IntQueue.h"

/* Hardware specifics. */
#include "iodefine.h"

#define tmrTIMER_0_1_FREQUENCY	( 2000UL )
#define tmrTIMER_2_3_FREQUENCY	( 2001UL )

/* Handlers for the two timers used.  See the documentation page 
for this port on http://www.FreeRTOS.org for more information on writing
interrupt handlers. */
void vT0_1_ISR_Handler( void ) __attribute((interrupt));
void vT2_3_ISR_Handler( void ) __attribute((interrupt));

void vInitialiseTimerForIntQueueTest( void )
{
	/* Ensure interrupts do not start until full configuration is complete. */
	portENTER_CRITICAL();
	{
		/* Cascade two 8bit timer channels to generate the interrupts. 
		8bit timer unit 1 (TMR0 and TMR1) and 8bit timer unit 2 (TMR2 and TMR3 are
		utilised for this test. */

		/* Enable the timers. */
		SYSTEM.MSTPCRA.BIT.MSTPA5 = 0;
		SYSTEM.MSTPCRA.BIT.MSTPA4 = 0;

		/* Enable compare match A interrupt request. */
		TMR0.TCR.BIT.CMIEA = 1;
		TMR2.TCR.BIT.CMIEA = 1;

		/* Clear the timer on compare match A. */
		TMR0.TCR.BIT.CCLR = 1;
		TMR2.TCR.BIT.CCLR = 1;

		/* Set the compare match value. */
		TMR01.TCORA = ( unsigned short ) ( ( ( configPERIPHERAL_CLOCK_HZ / tmrTIMER_0_1_FREQUENCY ) -1 ) / 8 );
		TMR23.TCORA = ( unsigned short ) ( ( ( configPERIPHERAL_CLOCK_HZ / tmrTIMER_0_1_FREQUENCY ) -1 ) / 8 );

		/* 16 bit operation ( count from timer 1,2 ). */
		TMR0.TCCR.BIT.CSS = 3;
		TMR2.TCCR.BIT.CSS = 3;
	
		/* Use PCLK as the input. */
		TMR1.TCCR.BIT.CSS = 1;
		TMR3.TCCR.BIT.CSS = 1;
	
		/* Divide PCLK by 8. */
		TMR1.TCCR.BIT.CKS = 2;
		TMR3.TCCR.BIT.CKS = 2;
	
		/* Enable TMR 0, 2 interrupts. */
		IEN( TMR0, CMIA0 ) = 1;
		IEN( TMR2, CMIA2 ) = 1;

		/* Set the timer interrupts to be above the kernel.  The interrupts are
		assigned different priorities so they nest with each other. */
		IPR( TMR0, CMIA0 ) = configMAX_SYSCALL_INTERRUPT_PRIORITY - 1;
		IPR( TMR2, CMIA2 ) = ( configMAX_SYSCALL_INTERRUPT_PRIORITY - 2 );
	}
	portEXIT_CRITICAL();
	
	/* Ensure the interrupts are clear as they are edge detected. */
	IR( TMR0, CMIA0 ) = 0;
	IR( TMR2, CMIA2 ) = 0;
}
/*-----------------------------------------------------------*/

void vT0_1_ISR_Handler( void )
{
	/* Re-enabled interrupts. */
	__asm volatile( "SETPSW	I" );

	/* Call the handler that is part of the common code - this is where the
	non-portable code ends and the actual test is performed. */
	portYIELD_FROM_ISR( xFirstTimerHandler() );	
}
/*-----------------------------------------------------------*/

void vT2_3_ISR_Handler( void )
{
	/* Re-enabled interrupts. */
	__asm volatile( "SETPSW	I" );

	/* Call the handler that is part of the common code - this is where the
	non-portable code ends and the actual test is performed. */
	portYIELD_FROM_ISR( xSecondTimerHandler() );	
}
/*-----------------------------------------------------------*/






