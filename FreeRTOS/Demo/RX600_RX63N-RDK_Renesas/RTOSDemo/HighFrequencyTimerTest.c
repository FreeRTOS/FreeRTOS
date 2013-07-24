/*
    FreeRTOS V7.5.2 - Copyright (C) 2013 Real Time Engineers Ltd.

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
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

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

/* 
 * High frequency timer test as described in main.c. 
 */

/* Scheduler includes. */
#include "FreeRTOS.h"

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
static void prvTimer2IntHandler( void );

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

#pragma interrupt ( prvTimer2IntHandler( vect = _VECT( _CMT2_CMI2 ), enable ) )
static void prvTimer2IntHandler( void )
{
volatile unsigned short usCurrentCount;
static unsigned short usMaxCount = 0;
static unsigned long ulErrorCount = 0UL;

	/* We use the timer 1 counter value to measure the clock cycles between
	the timer 0 interrupts.  First stop the clock. */
	CMT.CMSTR1.BIT.STR3 = 0;
	nop();
	nop();
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







