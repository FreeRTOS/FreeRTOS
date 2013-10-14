/*
    FreeRTOS V7.5.3 - Copyright (C) 2013 Real Time Engineers Ltd. 
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
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the demo application tasks.
 * 
 * This demo is configured to execute on the ES449 prototyping board from
 * SoftBaugh. The ES449 has a built in LCD display and a single built in user
 * LED.  Therefore, in place of flashing an LED, the 'flash' and 'check' tasks
 * toggle '*' characters on the LCD.  The left most '*' represents LED 0, the
 * next LED 1, etc.
 *
 * Main. c also creates a task called 'Check'.  This only executes every three 
 * seconds but has the highest priority so is guaranteed to get processor time.  
 * Its main function is to check that all the other tasks are still operational.  
 * Each task that does not flash an LED maintains a unique count that is 
 * incremented each time the task successfully completes its function.  Should 
 * any error occur within such a task the count is permanently halted.  The 
 * 'check' task inspects the count of each task to ensure it has changed since
 * the last time the check task executed.  If all the count variables have 
 * changed all the tasks are still executing error free, and the check task
 * toggles an LED with a three second period.  Should any task contain an error 
 * at any time the LED toggle rate will increase to 500ms.
 *
 * Please read the documentation for the MSP430 port available on
 * http://www.FreeRTOS.org.
 */

/* Standard includes. */
#include <stdlib.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo application includes. */
#include "partest.h"
#include "flash.h"
#include "integer.h"
#include "comtest2.h"
#include "PollQ.h"

/* Constants required for hardware setup. */
#define mainALL_BITS_OUTPUT		( ( unsigned char ) 0xff )
#define mainMAX_FREQUENCY		( ( unsigned char ) 121 )

/* Constants that define the LED's used by the various tasks. [in this case
the '*' characters on the LCD represent LED's] */
#define mainCHECK_LED			( 4 )
#define mainCOM_TEST_LED		( 10 )

/* Demo task priorities. */
#define mainCHECK_TASK_PRIORITY			( tskIDLE_PRIORITY + 3 )
#define mainCOM_TEST_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainLED_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )

/* Baud rate used by the COM test tasks. */
#define mainCOM_TEST_BAUD_RATE			( ( unsigned long ) 19200 )

/* The frequency at which the 'Check' tasks executes.  See the comments at the 
top of the page.  When the system is operating error free the 'Check' task
toggles an LED every three seconds.  If an error is discovered in any task the
rate is increased to 500 milliseconds.  [in this case the '*' characters on the 
LCD represent LED's]*/
#define mainNO_ERROR_CHECK_DELAY		( ( portTickType ) 3000 / portTICK_RATE_MS  )
#define mainERROR_CHECK_DELAY			( ( portTickType ) 500 / portTICK_RATE_MS  )

/* The constants used in the calculation. */
#define intgCONST1				( ( long ) 123 )
#define intgCONST2				( ( long ) 234567 )
#define intgCONST3				( ( long ) -3 )
#define intgCONST4				( ( long ) 7 )
#define intgEXPECTED_ANSWER		( ( ( intgCONST1 + intgCONST2 ) * intgCONST3 ) / intgCONST4 )

/* 
 * The function that implements the Check task.  See the comments at the head
 * of the page for implementation details.
 */ 
static void vErrorChecks( void *pvParameters );

/*
 * Called by the Check task.  Returns pdPASS if all the other tasks are found
 * to be operating without error - otherwise returns pdFAIL.
 */
static short prvCheckOtherTasksAreStillRunning( void );

/* 
 * Perform the hardware setup required by the ES449 in order to run the demo
 * application.
 */
static void prvSetupHardware( void );


portBASE_TYPE xLocalError = pdFALSE;
volatile unsigned long ulIdleLoops = 0UL;

/*-----------------------------------------------------------*/

/*
 * Start the demo application tasks - then start the real time scheduler.
 */
int main( void )
{
	/* Setup the hardware ready for the demo. */
	prvSetupHardware();
	vParTestInitialise();

	/* Start the standard demo application tasks. */
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED - 1 );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );

	/* Start the 'Check' task which is defined in this file. */
	xTaskCreate( vErrorChecks, ( const signed char * const ) "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );	

	/* Start the scheduler. */
	vTaskStartScheduler();

	/* As the scheduler has been started the demo applications tasks will be
	executing and we should never get here! */
	return 0;
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vErrorChecks, pvParameters )
{
portTickType xDelayPeriod = mainNO_ERROR_CHECK_DELAY;

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error. */
	for( ;; )
	{
		/* Wait until it is time to check again.  The time we wait here depends
		on whether an error has been detected or not.  When an error is 
		detected the time is shortened resulting in a faster LED flash rate. */
		vTaskDelay( xDelayPeriod );

		/* See if the other tasks are all ok. */
		if( prvCheckOtherTasksAreStillRunning() != pdPASS )
		{
			/* An error occurred in one of the tasks so shorten the delay 
			period - which has the effect of increasing the frequency of the
			LED toggle. */
			xDelayPeriod = mainERROR_CHECK_DELAY;
		}

		/* Flash! */
		vParTestToggleLED( mainCHECK_LED );
	}
}
/*-----------------------------------------------------------*/

static short prvCheckOtherTasksAreStillRunning( void )
{
static short sNoErrorFound = pdTRUE;
static unsigned long ulLastIdleLoopCount = 0UL;

	/* The demo tasks maintain a count that increments every cycle of the task
	provided that the task has never encountered an error.  This function 
	checks the counts maintained by the tasks to ensure they are still being
	incremented.  A count remaining at the same value between calls therefore
	indicates that an error has been detected.  Only tasks that do not flash
	an LED are checked. */

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}

	if( xLocalError == pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}

    if( ulIdleLoops == ulLastIdleLoopCount )
    {
        sNoErrorFound = pdFALSE;
    }
    else
    {
        ulLastIdleLoopCount = ulIdleLoops;
    }
	
	return sNoErrorFound;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Stop the watchdog. */
	WDTCTL = WDTPW + WDTHOLD;

	/* Setup DCO+ for ( xtal * D * (N + 1) ) operation. */
	FLL_CTL0 |= DCOPLUS + XCAP18PF; 

	/* X2 DCO frequency, 8MHz nominal DCO */
	SCFI0 |= FN_4;                  

	/* (121+1) x 32768 x 2 = 7.99 Mhz */
	SCFQCTL = mainMAX_FREQUENCY;

	/* Setup the IO.  This is just copied from the demo supplied by SoftBaugh
	 for the ES449 demo board. */
	P1SEL = 0x32;
	P2SEL = 0x00;
	P3SEL = 0x00;
	P4SEL = 0xFC;
	P5SEL = 0xFF;
}
/*-----------------------------------------------------------*/

/* The idle hook is just a copy of the standard integer maths tasks.  See
Demo/Common/integer.c for rationale. */

void vApplicationIdleHook( void ) __toplevel
{
/* These variables are all effectively set to constants so they are volatile to
ensure the compiler does not just get rid of them. */
volatile long lValue;
volatile signed portBASE_TYPE *pxTaskHasExecuted;

	/* Keep performing a calculation and checking the result against a constant. */
	for( ;; )
	{
		/* Perform the calculation.  This will store partial value in
		registers, resulting in a good test of the context switch mechanism. */
		lValue = intgCONST1;
		lValue += intgCONST2;

		/* Yield in case cooperative scheduling is being used. */
		#if configUSE_PREEMPTION == 0
		{
			taskYIELD();
		}
		#endif

		/* Finish off the calculation. */
		lValue *= intgCONST3;
		lValue /= intgCONST4;

		/* If the calculation is found to be incorrect we stop setting the 
		TaskHasExecuted variable so the check task can see an error has 
		occurred. */
		if( lValue != intgEXPECTED_ANSWER ) /*lint !e774 volatile used to prevent this being optimised out. */
		{
			/* Don't bother with mutual exclusion - it is only read from the
			check task and never written. */
			xLocalError = pdTRUE;
		}
		/* Yield in case cooperative scheduling is being used. */
		#if configUSE_PREEMPTION == 0
		{
			taskYIELD();
		}
		#endif

        ulIdleLoops++;

        /* Place the processor into low power mode. */
        LPM3;
	}
}





