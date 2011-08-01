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
 *******************************************************************************
 *
 * main() creates all the demo application tasks, then starts the scheduler.  
 * The web documentation provides more details of the standard demo application 
 * tasks, which provide no particular functionality but do provide a good 
 * example of how to use the FreeRTOS API.
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "Check" task - This only executes every five seconds but has a high priority
 * to ensure it gets processor time.  Its main function is to check that all the
 * standard demo tasks are still operational.  While no errors have been
 * discovered the check task will print out "OK" and the current simulated tick
 * time.  If an error is discovered in the execution of a task then the check
 * task will print out an appropriate error message.
 *
 * lwIP - This project also includes a simple lwIP example.  The implements a
 * web server that includes Server Side Include (SSI) functionality.  The web
 * server serves a page that shows task statistics, and another page that shows
 * run time statistics (how much CPU time each task is consuming).  Following
 * are some notes on the web server functionality:
 * - Configuration parameters (IP address, etc.) are set at the bottom of
 *   FreeRTOSConfig.h.  In particular, the number of the WinPCap interface to
 *   open is set by the configNETWORK_INTERFACE_TO_USE parameter.
 * - A WinPCap driver is provided in 
 *   FreeRTOS\Demo\Common\ethernet\lwip-1.4.0\ports\win32\ethernetif.c.
 * - Currently, the files served by the web server are converted into C structs,
 *   and built into the executable image.  The html and image files are converted
 *   to C structs using the makefsdata.exe binary found in
 *   FreeRTOS\Demo\WIN32-MSVC\lwIP_Apps\apps\httpserver_raw\makefsdata.  A
 *   Microsoft Visual Studio Express 10 project file that builds the .exe is
 *   located in the same directory.
 * - Makefsdata.exe outputs a file called fsdata.c.  fsdata.c must be copied
 *   into FreeRTOS\Demo\WIN32-MSVC\lwIP_Apps\apps\httpserver_raw prior to the
 *   project being built.
 * - The SSI generator functions are located in 
 *   FreeRTOS\Demo\WIN32-MSVC\lwIP_Apps\lwIP_Apps.c
 *
 */


/* Standard includes. */
#include <stdio.h>

/* Kernel includes. */
#include <FreeRTOS.h>
#include "task.h"
#include "queue.h"

/* Standard demo includes. */
#include "BlockQ.h"
#include "integer.h"
#include "semtest.h"
#include "PollQ.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "recmutex.h"
#include "flop.h"
#include "TimerDemo.h"
#include "countsem.h"

/* lwIP includes. */
#include "lwip/tcpip.h"

/* Utils includes. */
#include "CommandInterpreter.h"

/* Priorities at which the tasks are created. */
#define mainCHECK_TASK_PRIORITY		( configMAX_PRIORITIES - 1 )
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY   ( tskIDLE_PRIORITY + 3 )
#define mainFLASH_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainuIP_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainINTEGER_TASK_PRIORITY   ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY	( tskIDLE_PRIORITY )
#define mainFLOP_TASK_PRIORITY		( tskIDLE_PRIORITY )

#define mainTIMER_TEST_PERIOD			( 50 )

/* Task function prototypes. */
static void prvCheckTask( void *pvParameters );

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

/* Structure that defines the "run-time-stats" command line command. */
static const xCommandLineInput xRunTimeStats =
{
	"run-time-stats",
	"run-time-stats: Displays a table showing how much processing time each FreeRTOS task has used\r\n",
	prvRunTimeStatsCommand,
	NULL
};

/* Structure that defines the "task-stats" command line command. */
static const xCommandLineInput xTaskStats =
{
	"task-stats",
	"task-stats: Displays a table showing the state of each FreeRTOS task\r\n",
	prvTaskStatsCommand,
	&xRunTimeStats
};

/*-----------------------------------------------------------*/

int main( void )
{
	/* This call creates the TCP/IP thread. */
	tcpip_init( lwIPAppsInit, NULL );

	#if configINCLUDE_STANDARD_DEMO_TASKS == 1
	{
		/* Start the check task as described at the top of this file. */
		xTaskCreate( prvCheckTask, ( signed char * ) "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

		/* Create the standard demo tasks. */
		vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
		vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
		vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
		vStartIntegerMathTasks( mainINTEGER_TASK_PRIORITY );
		vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
		vStartQueuePeekTasks();
		vStartMathTasks( mainFLOP_TASK_PRIORITY );
		vStartRecursiveMutexTasks();
		vStartTimerDemoTask( mainTIMER_TEST_PERIOD );
		vStartCountingSemaphoreTasks();
	}
	#endif

	/* Register two command line commands to show task stats and run time stats
	respectively. */
	vCmdIntRegisterCommand( &xTaskStats );
	vCmdIntRegisterCommand( &xRunTimeStats );

	/* Start the scheduler itself. */
	vTaskStartScheduler();

    /* Should never get here unless there was not enough heap space to create 
	the idle and other system tasks. */
    return 0;
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
portTickType xNextWakeTime;
const portTickType xCycleFrequency = 1000 / portTICK_RATE_MS;

	/* Just to remove compiler warning. */
	( void ) pvParameters;

	/* Initialise xNextWakeTime - this only needs to be done once. */
	xNextWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Place this task in the blocked state until it is time to run again. */
		vTaskDelayUntil( &xNextWakeTime, xCycleFrequency );

		/* Check the standard demo tasks are running without error. */
		if( xAreTimerDemoTasksStillRunning( xCycleFrequency ) != pdTRUE )
		{
			pcStatusMessage = "Error: TimerDemo";
		}
	    else if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	    {
			pcStatusMessage = "Error: IntMath";
	    }	
		else if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{			
			pcStatusMessage = "Error: GenQueue";
		}
		else if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error: QueuePeek";
		}
		else if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error: BlockQueue";
		}
	    else if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	    {
			pcStatusMessage = "Error: SemTest";
	    }
	    else if( xArePollingQueuesStillRunning() != pdTRUE )
	    {
			pcStatusMessage = "Error: PollQueue";
	    }
		else if( xAreMathsTaskStillRunning() != pdPASS )
		{
			pcStatusMessage = "Error: Flop";
		}
	    else if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	    {
			pcStatusMessage = "Error: RecMutex";
		}
		else if( xAreCountingSemaphoreTasksStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error: CountSem";
		}

		/* This is the only task that uses stdout so its ok to call printf() 
		directly. */
		printf( "%s - %d\r\n", pcStatusMessage, xTaskGetTickCount() );
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

void vApplicationTickHook( void )
{
	#if configINCLUDE_STANDARD_DEMO_TASKS == 1
	{
		/* Call the periodic timer test, which tests the timer API functions that
		can be called from an ISR. */
		vTimerPeriodicISRTests();
	}
	#endif
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

	/* This is the callback function that is executed when the command line
	command defined by the xTaskStats structure is entered.  This function
	is called repeatedly until it returns NULL.  It is therefore not re-entrant
	and must not be called from more than one task - or at least - not from
	more than one task at the same time. */
	if( pcReturn == NULL )
	{
		/* Generate a table of task state. */
		vTaskList( cTxBuffer );
		pcReturn = cTxBuffer;
	}
	else
	{
		/* This command only returns one string, so the second time it is
		called it just resets itself and returns NULL to say no more strings
		are going to be generated. */
		pcReturn = NULL;
	}

	return pcReturn;
}
/*-----------------------------------------------------------*/

static const signed char *prvRunTimeStatsCommand( void )
{
static signed char *pcReturn = NULL;

	/* This is the callback function that is executed when the command line
	command defined by the xRunTimeStats structure is entered.  This function
	is called repeatedly until it returns NULL.  It is therefore not re-entrant
	and must not be called from more than one task - or at least - not from
	more than one task at the same time. */

	if( pcReturn == NULL )
	{
		/* Generate a table of run time stats. */
		vTaskGetRunTimeStats( cTxBuffer );
		pcReturn = cTxBuffer;
	}
	else
	{
		/* This command only returns one string, so the second time it is
		called it just resets itself and returns NULL to say no more strings
		are going to be generated. */
		pcReturn = NULL;
	}

	return pcReturn;
}


