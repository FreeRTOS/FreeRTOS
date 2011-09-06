/*
    FreeRTOS V7.0.1 - Copyright (C) 2011 Real Time Engineers Ltd.
	

	FreeRTOS supports many tools and architectures. V7.0.0 is sponsored by:
	Atollic AB - Atollic provides professional embedded systems development
	tools for C/C++ development, code analysis and test automation.
	See http://www.atollic.com
	

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

/* Standard includes. */
#include <stdlib.h>
#include <string.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"

/* Standard demo includes. */
#include "dynamic.h"
#include "PollQ.h"
#include "semtest.h"

/* The period at which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_RATE_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_RATE_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_RATE_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 200UL / portTICK_RATE_MS )

/* The LED toggled by the check task. */
#define mainLED_0   						P7_bit.no7

/* A block time of zero simple means "don't block". */
#define mainDONT_BLOCK						( 0U )

/*-----------------------------------------------------------*/

/*
 * The 'check' timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( xTimerHandle xTimer );

/*
 * This function is called from the C startup routine to setup the processor -
 * in particular the clock source.
 */
int __low_level_init(void);

/*
 * Functions that define the RegTest tasks as described at the top of this file.
 */
extern void vRegTest1( void *pvParameters );
extern void vRegTest2( void *pvParameters );


/*-----------------------------------------------------------*/

/* If an error is discovered by one of the RegTest tasks then this flag is set
to pdFAIL.  The 'check' task then inspects this flag to detect errors within
the RegTest tasks. */
static short sRegTestStatus = pdPASS;

/* The check timer.  This uses prvCheckTimerCallback() as its callback
function. */
static xTimerHandle xCheckTimer = NULL;

/* RL78/G13 Option Byte Definition. Watchdog disabled, LVI enabled, OCD interface
enabled. */
__root __far const unsigned char OptionByte[] @ 0x00C0 =
{
	WATCHDOG_DISABLED, LVI_ENABLED, RESERVED_FF, OCD_ENABLED
};

/* Security byte definition */
__root __far const unsigned char SecuIDCode[]  @ 0x00C4 =
{
	0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x54
};

/*-----------------------------------------------------------*/

short main( void )
{
	/* Creates all the tasks and timers, then starts the scheduler. */

	/* First create the 'standard demo' tasks.  These are used to demonstrate
	API functions being used and also to test the kernel port.  More information
	is provided on the FreeRTOS.org WEB site. */
	vStartDynamicPriorityTasks();
	vStartPolledQueueTasks( tskIDLE_PRIORITY );
	vStartSemaphoreTasks( tskIDLE_PRIORITY + 1U );

	/* Create the RegTest tasks as described at the top of this file. */
	xTaskCreate( vRegTest1, "Reg1", configMINIMAL_STACK_SIZE, NULL, 0, NULL );
	xTaskCreate( vRegTest2, "Reg2", configMINIMAL_STACK_SIZE, NULL, 0, NULL );	

	/* Create the software timer that performs the 'check' functionality,
	as described at the top of this file. */
	xCheckTimer = xTimerCreate( ( const signed char * ) "CheckTimer",/* A text name, purely to help debugging. */
								( mainCHECK_TIMER_PERIOD_MS ),		/* The timer period, in this case 3000ms (3s). */
								pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) 0,						/* The ID is not used, so can be set to anything. */
								prvCheckTimerCallback				/* The callback function that inspects the status of all the other tasks. */
							  );
							
	
	/* Send a command to start the check timer.  It will not actually start
	until the scheduler is running (when vTaskStartScheduler() is called). */
	xTimerStart( xCheckTimer, mainDONT_BLOCK );
	
	/* Finally start the scheduler running. */
	vTaskStartScheduler();

	/* If this line is reached then vTaskStartScheduler() returned because there
	was insufficient heap memory remaining for the idle task to be created. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTimerCallback( xTimerHandle xTimer )
{
static portBASE_TYPE xChangedTimerPeriodAlready = pdFALSE, xErrorStatus = pdPASS;

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		xErrorStatus = pdFAIL;
	}
	
	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		xErrorStatus = pdFAIL;
	}
	
	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		xErrorStatus = pdFAIL;
	}

	if( sRegTestStatus != pdPASS )
	{
		xErrorStatus = pdFAIL;
	}

	if( ( xErrorStatus == pdFAIL ) && ( xChangedTimerPeriodAlready == pdFALSE ) )
	{
		/* An error has occurred, but the timer's period has not yet been changed,
		change it now, and remember that it has been changed.  Shortening the
		timer's period means the LED will toggle at a faster rate, giving a
		visible indication that something has gone wrong. */
		xChangedTimerPeriodAlready = pdTRUE;
			
		/* This call to xTimerChangePeriod() uses a zero block time.  Functions
		called from inside of a timer callback function must *never* attempt to
		block. */
		xTimerChangePeriod( xCheckTimer, ( mainERROR_CHECK_TIMER_PERIOD_MS ), mainDONT_BLOCK );
	}
	
	/* Toggle the LED.  The toggle rate will depend on whether or not an error
	has been found in any tasks. */
	mainLED_0 = !mainLED_0;
}
/*-----------------------------------------------------------*/

int __low_level_init(void)
{
unsigned portCHAR ucResetFlag = RESF;

	portDISABLE_INTERRUPTS();

	/* Clock Configuration:
	In this port, to use the internal high speed clock source of the
	microcontroller, define the configCLOCK_SOURCE as 1 in FreeRTOSConfig.h.  To
	use an external	clock define configCLOCK_SOURCE as 0. */
	#if configCLOCK_SOURCE == 1
	{
		/* Set fMX */
		CMC = 0x00;
		MSTOP = 1U;
		
		/* Set fMAIN */
		MCM0 = 0U;
		
		/* Set fSUB */
		XTSTOP = 1U;
		OSMC = 0x10;
		
		/* Set fCLK */
		CSS = 0U;
		
		/* Set fIH */
		HIOSTOP = 0U;
	}
	#else
	{
		unsigned char ucTempStabset, ucTempStabWait;	

		/* Set fMX */
		CMC = 0x41;
		OSTS = 0x07;
		MSTOP = 0U;
		ucTempStabset = 0xFF;
		
		do
		{
			ucTempStabWait = OSTC;
			ucTempStabWait &= ucTempStabset;
		}
		while( ucTempStabWait != ucTempStabset );
		
		/* Set fMAIN */
		MCM0 = 1U;
		
		/* Set fSUB */
		XTSTOP = 1U;
		OSMC = 0x10;
		
		/* Set fCLK */
		CSS = 0U;
		
		/* Set fIH */
		HIOSTOP = 0U;
	}
	#endif /* configCLOCK_SOURCE == 1 */
	
	/* LED port initialization - set port register. */
	P7 &= 0x7F;
	
	/* Set port mode register. */
	PM7 &= 0x7F;
	
	/* Switch pin initialization - enable pull-up resistor. */
	PU12_bit.no0  = 1;

	return pdTRUE;
}
/*-----------------------------------------------------------*/

void vRegTestError( void )
{
	/* Called by the RegTest tasks if an error is found.  lRegTestStatus is
	inspected by the check task. */
	sRegTestStatus = pdFAIL;

	/* Do not return from here as the reg test tasks clobber all registers so
	function calls may not function correctly. */
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* Called if a call to pvPortMalloc() fails because there is insufficient
	free memory available in the FreeRTOS heap.  pvPortMalloc() is called
	internally by FreeRTOS API functions that create tasks, queues, software
	timers, and semaphores.  The size of the FreeRTOS heap is set by the
	configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
volatile size_t xFreeHeapSpace;

	/* This is just a trivial example of an idle hook.  It is called on each
	cycle of the idle task.  It must *NOT* attempt to block.  In this case the
	idle task just queries the amount of FreeRTOS heap that remains.  See the
	memory management section on the http://www.FreeRTOS.org web site for memory
	management options.  If there is a lot of heap memory free then the
	configTOTAL_HEAP_SIZE value in FreeRTOSConfig.h can be reduced to free up
	RAM. */
	xFreeHeapSpace = xPortGetFreeHeapSize();	
}

