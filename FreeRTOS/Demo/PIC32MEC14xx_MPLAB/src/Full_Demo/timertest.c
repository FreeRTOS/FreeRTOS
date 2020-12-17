/*
 * FreeRTOS V202012.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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


