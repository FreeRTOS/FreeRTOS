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
 * This file initialises the two timers available in the Timer32 peripheral.
 *
 * Channels 0 and 1 provide the interrupts that are used with the IntQ
 * standard demo tasks, which test interrupt nesting and using queues from
 * interrupts.
 */

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo includes. */
#include "IntQueueTimer.h"
#include "IntQueue.h"

/* The frequencies at which the two timers expire are slightly offset to ensure
they don't remain synchronised. */
#define tmrTIMER_0_FREQUENCY	( 2000UL )
#define tmrTIMER_1_FREQUENCY	( 2003UL )

/* The interrupts use the FreeRTOS API so must be at or below the max syscall
interrupt priority.  Counter-intuitively, the higher the numeric number the
lower the logical priority. http://www.freertos.org/RTOS-Cortex-M3-M4.html */
#define tmrLOWER_PRIORITY		( configMAX_SYSCALL_INTERRUPT_PRIORITY )
#define tmrHIGHER_PRIORITY		( configMAX_SYSCALL_INTERRUPT_PRIORITY + 1 )
/*-----------------------------------------------------------*/

/* Handlers for the two timer peripherals - two channels are used in the TC0
timer. */
void vT32_0_Handler( void );
void vT32_1_Handler( void );

/*-----------------------------------------------------------*/

void vInitialiseTimerForIntQueueTest( void )
{
    /* Configure the timer channels. */
	MAP_Timer32_initModule( TIMER32_0_MODULE, TIMER32_PRESCALER_1, TIMER32_32BIT, TIMER32_PERIODIC_MODE );
	MAP_Timer32_setCount( TIMER32_0_MODULE, CS_getMCLK() / tmrTIMER_0_FREQUENCY );
	MAP_Timer32_enableInterrupt( TIMER32_0_MODULE );
	MAP_Timer32_startTimer( TIMER32_0_MODULE, false );
	MAP_Interrupt_setPriority( INT_T32_INT1, tmrLOWER_PRIORITY );
	MAP_Interrupt_enableInterrupt( INT_T32_INT1 );

	MAP_Timer32_initModule( TIMER32_1_MODULE, TIMER32_PRESCALER_1, TIMER32_32BIT, TIMER32_PERIODIC_MODE );
	MAP_Timer32_setCount( TIMER32_1_MODULE, CS_getMCLK() / tmrTIMER_1_FREQUENCY );
	MAP_Timer32_enableInterrupt( TIMER32_1_MODULE );
	MAP_Timer32_startTimer( TIMER32_1_MODULE, false );
	MAP_Interrupt_setPriority( INT_T32_INT2, tmrHIGHER_PRIORITY );
	MAP_Interrupt_enableInterrupt( INT_T32_INT2 );
}
/*-----------------------------------------------------------*/

void vT32_0_Handler( void )
{
    MAP_Timer32_clearInterruptFlag( TIMER32_0_MODULE );
	portYIELD_FROM_ISR( xFirstTimerHandler() );
}
/*-----------------------------------------------------------*/

void vT32_1_Handler( void )
{
    MAP_Timer32_clearInterruptFlag( TIMER32_1_MODULE );
	portYIELD_FROM_ISR( xSecondTimerHandler() );
}

