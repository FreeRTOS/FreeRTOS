/*
 * FreeRTOS Kernel V10.1.1
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
 * High frequency timer test as described in main.c. 
 */

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Hardware specifics. */
#include "iodefine.h"

/* The set frequency of the interrupt.  Deviations from this are measured as
the jitter. */
#define timerINTERRUPT_FREQUENCY		( 20000UL )

/* The expected time between each of the timer interrupts - if the jitter was
zero. */
#define timerEXPECTED_DIFFERENCE_VALUE	( ( unsigned short ) ( ( configPERIPHERAL_CLOCK_HZ / 8UL ) / timerINTERRUPT_FREQUENCY ) )

/* The highest available interrupt priority. */
#define timerHIGHEST_PRIORITY			( 15 )

/* Misc defines. */
#define timerTIMER_3_COUNT_VALUE		( *( ( unsigned short * ) 0x8801a ) ) /*( CMT3.CMCNT )*/

/*-----------------------------------------------------------*/

/* Interrupt handler in which the jitter is measured. */
void vTimer2_ISR_Handler( void ) __attribute__((interrupt));

/* Stores the value of the maximum recorded jitter between interrupts.  This is
displayed on one of the served web pages. */
volatile unsigned short usMaxJitter = 0;

/* Counts the number of high frequency interrupts - used to generate the run
time stats. */
volatile unsigned long ulHighFrequencyTickCount = 0UL;

/*-----------------------------------------------------------*/

void vSetupHighFrequencyTimer( void )
{
	/* Timer CMT2 is used to generate the interrupts, and CMT3 is used
	to measure the jitter. */

	/* Enable compare match timer 2 and 3. */
	MSTP( CMT2 ) = 0;
	MSTP( CMT3 ) = 0;
	
	/* Interrupt on compare match. */
	CMT2.CMCR.BIT.CMIE = 1;
	
	/* Set the compare match value. */
	CMT2.CMCOR = ( unsigned short ) ( ( ( configPERIPHERAL_CLOCK_HZ / timerINTERRUPT_FREQUENCY ) -1 ) / 8 );
	
	/* Divide the PCLK by 8. */
	CMT2.CMCR.BIT.CKS = 0;
	CMT3.CMCR.BIT.CKS = 0;
	
	/* Enable the interrupt... */
	_IEN( _CMT2_CMI2 ) = 1;
	
	/* ...and set its priority to the maximum possible, this is above the priority
	set by configMAX_SYSCALL_INTERRUPT_PRIORITY so will nest. */
	_IPR( _CMT2_CMI2 ) = timerHIGHEST_PRIORITY;
	
	/* Start the timers. */
	CMT.CMSTR1.BIT.STR2 = 1;
	CMT.CMSTR1.BIT.STR3 = 1;
}
/*-----------------------------------------------------------*/

void vTimer2_ISR_Handler( void )
{
volatile unsigned short usCurrentCount;
static unsigned short usMaxCount = 0;
static unsigned long ulErrorCount = 0UL;

	/* This is the highest priority interrupt in the system, so there is no
	advantage to re-enabling interrupts here.
	
	We use the timer 1 counter value to measure the clock cycles between
	the timer 0 interrupts.  First stop the clock. */
	CMT.CMSTR1.BIT.STR3 = 0;
	portNOP();
	portNOP();
	usCurrentCount = timerTIMER_3_COUNT_VALUE;

	/* Is this the largest count we have measured yet? */
	if( usCurrentCount > usMaxCount )
	{
		if( usCurrentCount > timerEXPECTED_DIFFERENCE_VALUE )
		{
			usMaxJitter = usCurrentCount - timerEXPECTED_DIFFERENCE_VALUE;
		}
		else
		{
			/* This should not happen! */
			ulErrorCount++;
		}
		
		usMaxCount = usCurrentCount;
	}

	/* Used to generate the run time stats. */
	ulHighFrequencyTickCount++;
	
	/* Clear the timer. */
	timerTIMER_3_COUNT_VALUE = 0;
	
	/* Then start the clock again. */
	CMT.CMSTR1.BIT.STR3 = 1;
}







