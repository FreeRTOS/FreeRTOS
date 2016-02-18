/*
    FreeRTOS V9.0.0rc1 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/* High speed timer test as described in main.c. */

/* System port includes */
#include "appcfg.h"
#include "platform.h"
#include "MEC14xx/mec14xx.h"
#include "MEC14xx/mec14xx_girqs.h"

/* Scheduler includes. */
#include "FreeRTOS.h"

/* The priority of the high speed timer interrupt. */
#define timerTEST_INT_PRIORITY  ( 7 )

/* MEC14xx Timer 3 Timer MMCR's */
#define portMMCR_TMR3_COUNT		*((volatile uint32_t *)(0xA0000C60ul))
#define portMMCR_TMR3_PRELOAD	*((volatile uint32_t *)(0xA0000C64ul))
#define portMMCR_TMR3_STATUS	*((volatile uint32_t *)(0xA0000C68ul))
#define portMMCR_TMR3_INTEN		*((volatile uint32_t *)(0xA0000C6Cul))
#define portMMCR_TMR3_CONTROL	*((volatile uint32_t *)(0xA0000C70ul))

/* MEC14xx JTVIC external interrupt controller
 * is mapped to M14K closely-coupled peripheral space.
 */
#define portGIRQ23_TMR3_TIMER_BITPOS	(3)
#define portGIRQ23_TMR3_TIMER_MASK		(1ul << (portGIRQ23_TMR3_TIMER_BITPOS))
#define portMMCR_JTVIC_GIRQ23_SRC		*((volatile uint32_t *)(0xBFFFC0F0ul))
#define portMMCR_JTVIC_GIRQ23_SETEN		*((volatile uint32_t *)(0xBFFFC0F4ul))
#define portMMCR_JTVIC_GIRQ23_PRIA		*((volatile uint32_t *)(0xBFFFC3F0ul))

/*-----------------------------------------------------------*/

/* Incremented every 20,000 interrupts, so should count in seconds. */
unsigned long ulHighFrequencyTimerInterrupts = 0;

/*-----------------------------------------------------------*/

void vSetupTimerTest( unsigned short usFrequencyHz )
{
/* Timer 3 is going to interrupt at usFrequencyHz Hz. */
const uint32_t ulPreload = ( unsigned short ) ( ( configPERIPHERAL_CLOCK_HZ / ( unsigned long ) usFrequencyHz ) - 1 );

	/* Timer 3 is used to generate interrupts above the kernel and max syscall 
	interrupt priorities. No system library calls are used here as they are not 
	guaranteed to be re-entrant. */
	portMMCR_TMR3_CONTROL = 1ul;
	portMMCR_TMR3_PRELOAD = ulPreload;
	portMMCR_TMR3_COUNT = ulPreload;
	portMMCR_TMR3_INTEN = 0x0001ul;
	portMMCR_TMR3_STATUS = 0x0001ul;
	/* Enable Timer 3, and set for auto restart, counting down. */
	portMMCR_TMR3_CONTROL |= 0x0008;
	portMMCR_TMR3_CONTROL |= 0x0020;

	/* Configure interrupts from the Timer 3. */
	portMMCR_JTVIC_GIRQ23_SRC = ( portGIRQ23_TMR3_TIMER_MASK );
	portMMCR_JTVIC_GIRQ23_PRIA &= ~( 0x0Ful << 12 );
	portMMCR_JTVIC_GIRQ23_PRIA |= ( ( portIPL_TO_CODE( timerTEST_INT_PRIORITY ) ) << 12 );
	portMMCR_JTVIC_GIRQ23_SETEN = ( portGIRQ23_TMR3_TIMER_MASK );

}
/*-----------------------------------------------------------*/

/* Interrupt handler for Timer 3 interrupts, no library functions are used
 here as they may not be re-entrant. */
void __attribute__((interrupt, nomips16)) girq23_b3( void )
{
	ulHighFrequencyTimerInterrupts++;

	/* The interrupt flag registered is shared with the lower priority timer
	 interrupts and the RTOS timer so disable interrupts here. This is not
	 strictly necessary since this is the highest priority interrupt. */
	__asm volatile( "di" );
	/* Clear the timer interrupt. */
	portMMCR_JTVIC_GIRQ23_SRC = portGIRQ23_TMR3_TIMER_MASK;
	__asm volatile( "ei" );
}


