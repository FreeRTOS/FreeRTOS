/*
 * FreeRTOS Kernel V10.1.0
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
	MAP_Timer32_initModule( (uint32_t)TIMER32_0_BASE, TIMER32_PRESCALER_1, TIMER32_32BIT, TIMER32_PERIODIC_MODE );
	MAP_Timer32_setCount( (uint32_t)TIMER32_0_BASE, CS_getMCLK() / tmrTIMER_0_FREQUENCY );
	MAP_Timer32_enableInterrupt( (uint32_t)TIMER32_0_BASE );
	MAP_Timer32_startTimer( (uint32_t)TIMER32_0_BASE, false );
	MAP_Interrupt_setPriority( INT_T32_INT1, tmrLOWER_PRIORITY );
	MAP_Interrupt_enableInterrupt( INT_T32_INT1 );

	MAP_Timer32_initModule( (uint32_t)TIMER32_1_BASE, TIMER32_PRESCALER_1, TIMER32_32BIT, TIMER32_PERIODIC_MODE );
	MAP_Timer32_setCount( (uint32_t)TIMER32_1_BASE, CS_getMCLK() / tmrTIMER_1_FREQUENCY );
	MAP_Timer32_enableInterrupt( (uint32_t)TIMER32_1_BASE );
	MAP_Timer32_startTimer( (uint32_t)TIMER32_1_BASE, false );
	MAP_Interrupt_setPriority( INT_T32_INT2, tmrHIGHER_PRIORITY );
	MAP_Interrupt_enableInterrupt( INT_T32_INT2 );
}
/*-----------------------------------------------------------*/

void vT32_0_Handler( void )
{
    MAP_Timer32_clearInterruptFlag( (uint32_t)TIMER32_0_BASE );
	portYIELD_FROM_ISR( xFirstTimerHandler() );
}
/*-----------------------------------------------------------*/

void vT32_1_Handler( void )
{
    MAP_Timer32_clearInterruptFlag( (uint32_t)TIMER32_1_BASE );
	portYIELD_FROM_ISR( xSecondTimerHandler() );
}

