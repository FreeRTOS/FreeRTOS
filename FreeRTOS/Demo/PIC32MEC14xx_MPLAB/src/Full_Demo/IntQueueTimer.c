/*
 * FreeRTOS Kernel V10.2.1
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

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* Standard demo includes. */
#include "IntQueueTimer.h"
#include "IntQueue.h"

/* Microchip includes. */
#include "MEC14xx/mec14xx_timers.h"
#include "MEC14xx/mec14xx_jtvic.h"
#include "MEC14xx/mec14xx.h"

/* The frequency of the two timers is offset so the time between the timers
expiring is not always the same. */
#define timerINTERRUPT0_FREQUENCY	( 2000UL )
#define timerINTERRUPT1_FREQUENCY	( 2221UL )

/* MEC14xx JTVIC external interrupt controller is mapped to M14K closely-coupled
peripheral space. */
#define portMMCR_JTVIC_GIRQ23_PRIA		*((volatile uint32_t *)(0xBFFFC3F0ul))

/*-----------------------------------------------------------*/

/* These are the C handlers called from the asm wrappers. */
void vT0InterruptHandler( void );
void vT1InterruptHandler( void );

/*-----------------------------------------------------------*/

void vInitialiseTimerForIntQueueTest( void )
{
	/* Timer RT is used for the tick interrupt, timer 3 is used for the high
	frequency interrupt test.  This file therefore uses timers 0 and 1. */
	uint32_t ulPreload = ( unsigned short ) ( ( configPERIPHERAL_CLOCK_HZ / ( unsigned long ) timerINTERRUPT0_FREQUENCY ) );

	btmr_sleep_en( BTMR0_ID, 0 );
	btmr_init( BTMR0_ID, BTMR_COUNT_DOWN + BTMR_AUTO_RESTART + BTMR_INT_EN, 0, ulPreload, ulPreload );
	btmr_start( BTMR0_ID );

	jtvic_clr_source( MEC14xx_GIRQ23_ID, 0 );
	portMMCR_JTVIC_GIRQ23_PRIA &= ~( 0x0Ful << 0 );
	portMMCR_JTVIC_GIRQ23_PRIA |= ( ( portIPL_TO_CODE( configMAX_SYSCALL_INTERRUPT_PRIORITY ) ) << 0 );
	jtvic_en_source( MEC14xx_GIRQ23_ID, 0, pdTRUE );

	ulPreload = ( unsigned short ) ( ( configPERIPHERAL_CLOCK_HZ / ( unsigned long ) timerINTERRUPT1_FREQUENCY ) );
	btmr_sleep_en( BTMR1_ID, 0 );
	btmr_init( BTMR1_ID, BTMR_COUNT_DOWN + BTMR_AUTO_RESTART + BTMR_INT_EN, 0, ulPreload, ulPreload );
	btmr_start( BTMR1_ID );

	jtvic_clr_source( MEC14xx_GIRQ23_ID, 1 );
	portMMCR_JTVIC_GIRQ23_PRIA &= ~( 0x0Ful << 4 );
	portMMCR_JTVIC_GIRQ23_PRIA |= ( ( portIPL_TO_CODE( configMAX_SYSCALL_INTERRUPT_PRIORITY ) ) << 4 );
	jtvic_en_source( MEC14xx_GIRQ23_ID, 1, pdTRUE );
}
/*-----------------------------------------------------------*/

void vT0InterruptHandler( void )
{
	/* Disable all interrupts because the source bit is shared with a bit used
	by the other timer and the high frequency timer test. */
	__asm volatile( "di" );
	/* Clear the timer interrupt. */
	jtvic_clr_source( MEC14xx_GIRQ23_ID, 0 );
	__asm volatile( "ei" );

	portEND_SWITCHING_ISR( xFirstTimerHandler() );
}
/*-----------------------------------------------------------*/

void vT1InterruptHandler( void )
{
	/* Disable all interrupts because the source bit is shared with a bit used
	by the other timer and the high frequency timer test. */
	__asm volatile( "di" );
	/* Clear the timer interrupt. */
	jtvic_clr_source( MEC14xx_GIRQ23_ID, 1 );
	__asm volatile( "ei" );

	portEND_SWITCHING_ISR( xSecondTimerHandler() );
}


