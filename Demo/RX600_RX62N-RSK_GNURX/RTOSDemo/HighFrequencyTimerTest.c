/*
    FreeRTOS V7.0.0 - Copyright (C) 2011 Real Time Engineers Ltd.
	

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
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







