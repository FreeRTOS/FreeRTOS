/*
    FreeRTOS V7.0.1 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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
 *******************************************************************************
 * -NOTE- The Win32 port is a simulation (or is that emulation?) only!  Do not
 * expect to get real time behaviour from the Win32 port or this demo
 * application.  It is provided as a convenient development and demonstration
 * test bed only.  This was tested using Windows XP on a dual core laptop.
 *
 * - READ THE WEB DOCUMENTATION FOR THIS PORT FOR MORE INFORMATION ON USING IT -
 * - http://www.freertos.org/FreeRTOS-Windows-Simulator-Emulator-for-Visual-Studio-and-Eclipse-MingW.html
 * - Note that the above linked page describes the simulator environment.  It
 * - is not the correct page to view for information on using this lwIP demo.
 *******************************************************************************
 *
 * This project demonstrates use of the lwIP stack.  The lwIP raw API is 
 * demonstrated by a simple http server that comes as part of the lwIP 
 * distribution - and executes in the tcpip task.  The lwIP sockets API
 * is demonstrated by a simple command line interpreter interface, which
 * executes in its own task.
 *
 * Both the http and command line server can be used to view task stats, and
 * run time stats.  Task stats give a snapshot of the state of each task in
 * the system.  Run time stats show how much processing time has been allocated
 * to each task.  A few of the standard demo tasks are created, just to ensure
 * there is some data to be viewed.
 *
 * Finally, a check timer is created.  The check timer is a software timer that
 * inspects the few standard demo tasks that are created to ensure they are
 * executing as expected.  It maintains a status string that can be viewed on
 * the "task stats" page served by the web server.
 *
 * More information about this demo, including details of how to set up the 
 * network interface, and the command line commands that are available, is
 * available on the documentation page for this demo on the 
 * http://www.FreeRTOS.org web site.
 *
 */


/* Standard includes. */
#include <stdio.h>

/* Kernel includes. */
#include <FreeRTOS.h>
#include "task.h"
#include "timers.h"

/* Standard demo includes. */
#include "GenQTest.h"

/* lwIP includes. */
#include "lwip/tcpip.h"
#include "lwIP_Apps.h"

/* Utils includes. */
#include "CommandInterpreter.h"

/* Priorities at which the tasks are created. */
#define mainGEN_QUEUE_TASK_PRIORITY	( tskIDLE_PRIORITY )

/* The period at which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_RATE_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_RATE_MS )

/* Check timer callback function. */
static void prvCheckTimerCallback( xTimerHandle xTimer );

/* Defined in lwIPApps.c. */
extern void lwIPAppsInit( void *pvArguments );

/* Callbacks to handle the command line commands defined by the xTaskStats and
xRunTimeStats command definitions respectively.  These functions are not
reentrant!  They must be used from one task only - or at least by only one task
at a time. */
static const signed char *prvTaskStatsCommand( void );
static const signed char *prvRunTimeStatsCommand( void );

/* The string that latches the current demo status. */
static char *pcStatusMessage = "All tasks running without error";

/* Variables used in the creation of the run time stats time base.  Run time 
stats record how much time each task spends in the Running state. */
long long llInitialRunTimeCounterValue = 0LL, llRunTimeStatsDivisor = 0LL;

/* The check timer.  This uses prvCheckTimerCallback() as its callback
function. */
static xTimerHandle xCheckTimer = NULL;

/* Structure that defines the "run-time-stats" command line command. */
static const xCommandLineInput xRunTimeStats =
{
	"run-time-stats",
	"run-time-stats: Displays a table showing how much processing time each FreeRTOS task has used\r\n",
	prvRunTimeStatsCommand,
};

/* Structure that defines the "task-stats" command line command. */
static const xCommandLineInput xTaskStats =
{
	"task-stats",
	"task-stats: Displays a table showing the state of each FreeRTOS task\r\n",
	prvTaskStatsCommand,
};

/*-----------------------------------------------------------*/

int main( void )
{
const unsigned long ulLongTime_ms = 1000UL;

	/* This call creates the TCP/IP thread. */
	tcpip_init( lwIPAppsInit, NULL );

	/* Create and start the check timer, as described at the top of this file. */
	xCheckTimer = xTimerCreate( ( const signed char * ) "CheckTimer",/* A text name, purely to help debugging. */
								( mainCHECK_TIMER_PERIOD_MS ),		/* The timer period, in this case 3000ms (3s). */
								pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) 0,						/* The ID is not used, so can be set to anything. */
								prvCheckTimerCallback				/* The callback function that inspects the status of all the other tasks. */
							  );

	/* Sanity check that the timer was created. */
	configASSERT( xCheckTimer );

	/* Start the check timer. */
	xTimerStart( xCheckTimer, 0UL );

	/* Create a few standard demo tasks, just so there are tasks running to
	view on the web server and via the command line command interpreter. */
	vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );

	/* Register two command line commands to show task stats and run time stats
	respectively. */
	xCmdIntRegisterCommand( &xTaskStats );
	xCmdIntRegisterCommand( &xRunTimeStats );

	/* Start the scheduler itself. */
	vTaskStartScheduler();

	/* This line should never be reached.  If it does execute then there was
	insufficient FreeRTOS heap memory available for the idle and/or timer
	tasks to be created. */
	for( ;; )
	{
		Sleep( ulLongTime_ms );
	}
}
/*-----------------------------------------------------------*/

static void prvCheckTimerCallback( xTimerHandle xTimer )
{
	/* The parameter is not used in this case. */
	( void ) xTimer;

	/* Check the standard demo tasks are running without error.   Latch the
	latest reported error in the pcStatusMessage character pointer.  The latched
	string can be viewed using the embedded web server and the command line
	interpreter.  This project is really to demonstrate the lwIP stack - so very
	few tasks are created - and those that are created are created purely so
	there is something to view. */
	if( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		pcStatusMessage = "Error: The GenQueue test reported an error.";
	}
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
const unsigned long ulMSToSleep = 5;

	/* Sleep to reduce CPU load, but don't sleep indefinitely in case there are
	tasks waiting to be terminated by the idle task. */
	Sleep( ulMSToSleep );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
const unsigned long ulLongSleep = 1000UL;

	/* Can be implemented if required, but probably not required in this 
	environment and running this demo. */
	taskDISABLE_INTERRUPTS();
	for( ;; )
	{
		Sleep( ulLongSleep );
	}
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( void )
{
const unsigned long ulLongSleep = 1000UL;

	/* Can be implemented if required, but probably not required in this 
	environment and running this demo. */
	taskDISABLE_INTERRUPTS();
	for( ;; )
	{
		Sleep( ulLongSleep );
	}
}
/*-----------------------------------------------------------*/

void vAssertCalled( void )
{
const unsigned long ulLongSleep = 1000UL;

	taskDISABLE_INTERRUPTS();
	for( ;; )
	{
		Sleep( ulLongSleep );
	}
}
/*-----------------------------------------------------------*/

char *pcMainGetTaskStatusMessage( void )
{
	return pcStatusMessage;
}
/*-----------------------------------------------------------*/

void vMainConfigureTimerForRunTimeStats( void )
{
LARGE_INTEGER liPerformanceCounterFrequency, liInitialRunTimeValue;

	/* Initialise the variables used to create the run time stats time base.
	Run time stats record how much time each task spends in the Running 
	state. */

	if( QueryPerformanceFrequency( &liPerformanceCounterFrequency ) == 0 )
	{
		llRunTimeStatsDivisor = 1;
	}
	else
	{
		/* How many times does the performance counter increment in 10ms? */
		llRunTimeStatsDivisor = liPerformanceCounterFrequency.QuadPart / 1000LL;

		/* What is the performance counter value now, this will be subtracted
		from readings taken at run time. */
		QueryPerformanceCounter( &liInitialRunTimeValue );
		llInitialRunTimeCounterValue = liInitialRunTimeValue.QuadPart;
	}
}
/*-----------------------------------------------------------*/

unsigned long ulMainGetRunTimeCounterValue( void )
{
LARGE_INTEGER liCurrentCount;
unsigned long ulReturn;

	/* What is the performance counter value now? */
	QueryPerformanceCounter( &liCurrentCount );

	/* Subtract the performance counter value reading taken when the 
	application started to get a count from that reference point, then
	scale to a 32 bit number. */
	ulReturn = ( unsigned long ) ( ( liCurrentCount.QuadPart - llInitialRunTimeCounterValue ) / llRunTimeStatsDivisor );

	return ulReturn;
}
/*-----------------------------------------------------------*/

static const signed char *prvTaskStatsCommand( void )
{
static signed char *pcReturn = NULL;
const char *const pcHeader = "Task          State  Priority  Stack	#\r\n************************************************\r\n";

	/* This is the callback function that is executed when the command line
	command defined by the xTaskStats structure is entered.  This function
	is called repeatedly until it returns NULL.  It is therefore not re-entrant
	and must not be called from more than one task - or at least - not from
	more than one task at the same time. */
	if( pcReturn == NULL )
	{
		/* Generate a table of task state. */
		pcReturn = pcLwipAppsBlockingGetTxBuffer();
		if( pcReturn != NULL )
		{
			strcpy( pcReturn, pcHeader );
			vTaskList( pcReturn + strlen( pcHeader ) );
		}
	}
	else
	{
		/* This command only returns one string, so the second time it is
		called it just resets itself and returns NULL to say no more strings
		are going to be generated. */
		pcReturn = NULL;
		vLwipAppsReleaseTxBuffer();
	}

	return pcReturn;
}
/*-----------------------------------------------------------*/

static const signed char *prvRunTimeStatsCommand( void )
{
static signed char *pcReturn = NULL;
const char * const pcHeader = "Task            Abs Time      % Time\r\n****************************************\r\n";

	/* This is the callback function that is executed when the command line
	command defined by the xRunTimeStats structure is entered.  This function
	is called repeatedly until it returns NULL.  It is therefore not re-entrant
	and must not be called from more than one task - or at least - not from
	more than one task at the same time. */

	if( pcReturn == NULL )
	{
		/* Generate a table of run time stats. */
		pcReturn = pcLwipAppsBlockingGetTxBuffer();
		if( pcReturn != NULL )
		{
			strcpy( pcReturn, pcHeader );
			vTaskGetRunTimeStats( pcReturn + strlen( pcHeader ) );
		}
	}
	else
	{
		/* This command only returns one string, so the second time it is
		called it just resets itself and returns NULL to say no more strings
		are going to be generated. */
		pcReturn = NULL;
		vLwipAppsReleaseTxBuffer();
	}

	return pcReturn;
}


