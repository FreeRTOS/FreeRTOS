/*
    FreeRTOS V8.2.3 - Copyright (C) 2015 Real Time Engineers Ltd.
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


