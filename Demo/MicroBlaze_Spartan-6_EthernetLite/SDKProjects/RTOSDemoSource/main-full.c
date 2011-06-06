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

/* ****************************************************************************
 * This project includes a lot of tasks and tests and is therefore complex.
 * If you would prefer a much simpler project to get started with then select
 * the 'Blinky' build configuration within the Embedded Workbench IDE.
 * ****************************************************************************
 *
 * Creates all the demo application tasks, then starts the scheduler.  The web
 * documentation provides more details of the standard demo application tasks,
 * which provide no particular functionality but do provide a good example of
 * how to use the FreeRTOS API.  The tasks defined in flop.c are included in the
 * set of standard demo tasks to ensure the floating point unit gets some
 * exercise.
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * Webserver ("uIP") task - This serves a number of dynamically generated WEB
 * pages to a standard WEB browser.  The IP and MAC addresses are configured by
 * constants defined at the bottom of FreeRTOSConfig.h.  Use either a standard
 * Ethernet cable to connect through a hug, or a cross over (point to point)
 * cable to connect directly.  Ensure the IP address used is compatible with the
 * IP address of the machine running the browser - the easiest way to achieve
 * this is to ensure the first three octets of the IP addresses are the same.
 *
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register still contains its expected value.  Each task uses
 * different values.  The tasks run with very low priority so get preempted
 * very frequently.  A check variable is incremented on each iteration of the
 * test loop.  A register containing an unexpected value is indicative of an
 * error in the context switching mechanism and will result in a branch to a
 * null loop - which in turn will prevent the check variable from incrementing
 * any further and allow the check task (described below) to determine that an
 * error has occurred.  The nature of the reg test tasks necessitates that they
 * are written in assembly code.
 *
 * "Check" task - This only executes every five seconds but has a high priority
 * to ensure it gets processor time.  Its main function is to check that all the
 * standard demo tasks are still operational.  While no errors have been
 * discovered the check task will toggle LED 5 every 5 seconds - the toggle
 * rate increasing to 200ms being a visual indication that at least one task has
 * reported unexpected behaviour.
 *
 * "High frequency timer test" - A high frequency periodic interrupt is
 * generated using a timer - the interrupt is assigned a priority above
 * configMAX_SYSCALL_INTERRUPT_PRIORITY so should not be effected by anything
 * the kernel is doing.  The frequency and priority of the interrupt, in
 * combination with other standard tests executed in this demo, should result
 * in interrupts nesting at least 3 and probably 4 deep.  This test is only
 * included in build configurations that have the optimiser switched on.  In
 * optimised builds the count of high frequency ticks is used as the time base
 * for the run time stats.
 *
 * *NOTE 1* If LED5 is toggling every 5 seconds then all the demo application
 * tasks are executing as expected and no errors have been reported in any
 * tasks.  The toggle rate increasing to 200ms indicates that at least one task
 * has reported unexpected behaviour.
 *
 * *NOTE 2* vApplicationSetupTimerInterrupt() is called by the kernel to let
 * the application set up a timer to generate the tick interrupt.  In this
 * example a compare match timer is used for this purpose.
 *
 * *NOTE 3* The CPU must be in Supervisor mode when the scheduler is started.
 * The PowerON_Reset_PC() supplied in resetprg.c with this demo has
 * Change_PSW_PM_to_UserMode() commented out to ensure this is the case.
 *
 * *NOTE 4* The IntQueue common demo tasks test interrupt nesting and make use
 * of all the 8bit timers (as two cascaded 16bit units).
*/

/* Standard includes. */
#include <string.h>
#include <stdio.h>

/* BSP includes. */
#include "xenv_standalone.h"
#include "xtmrctr.h"
#include "xil_exception.h"
#include "microblaze_exceptions_g.h"
#include "xgpio.h"

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard demo includes. */
#include "partest.h"
#include "flash.h"
#include "BlockQ.h"
#include "death.h"
#include "blocktim.h"
#include "semtest.h"
#include "PollQ.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "recmutex.h"
#include "flop.h"
#include "dynamic.h"

#define xPrintf( x )

/* Values that are passed into the reg test tasks using the task parameter.  The
tasks check that the values are passed in correctly. */
#define mainREG_TEST_1_PARAMETER	( 0x12121212UL )
#define mainREG_TEST_2_PARAMETER	( 0x12345678UL )

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

/* The WEB server uses string handling functions, which in turn use a bit more
stack than most of the other tasks. */
#define mainuIP_STACK_SIZE			( configMINIMAL_STACK_SIZE * 3 )

/* The LED toggled by the check task. */
#define mainCHECK_LED				( 5 )

/* The rate at which mainCHECK_LED will toggle when all the tasks are running
without error.  Controlled by the check task as described at the top of this
file. */
#define mainNO_ERROR_CYCLE_TIME		( 5000 / portTICK_RATE_MS )

/* The rate at which mainCHECK_LED will toggle when an error has been reported
by at least one task.  Controlled by the check task as described at the top of
this file. */
#define mainERROR_CYCLE_TIME		( 200 / portTICK_RATE_MS )

/*
 * vApplicationMallocFailedHook() will only be called if
 * configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
 * function that will execute if a call to pvPortMalloc() fails.
 * pvPortMalloc() is called internally by the kernel whenever a task, queue or
 * semaphore is created.  It is also called by various parts of the demo
 * application.
 */
void vApplicationMallocFailedHook( void );

/*
 * vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set to 1
 * in FreeRTOSConfig.h.  It is a hook function that is called on each iteration
 * of the idle task.  It is essential that code added to this hook function
 * never attempts to block in any way (for example, call xQueueReceive() with
 * a block time specified).  If the application makes use of the vTaskDelete()
 * API function (as this demo application does) then it is also important that
 * vApplicationIdleHook() is permitted to return to its calling function because
 * it is the responsibility of the idle task to clean up memory allocated by the
 * kernel to any task that has since been deleted.
 */
void vApplicationIdleHook( void );

/*
 * vApplicationStackOverflowHook() will only be called if
 * configCHECK_FOR_STACK_OVERFLOW is set to a non-zero value.  The handle and
 * name of the offending task should be passed in the function parameters, but
 * it is possible that the stack overflow will have corrupted these - in which
 * case pxCurrentTCB can be inspected to find the same information.
 */
void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName );

/*
 * The reg test tasks as described at the top of this file.
 */
static void prvRegTest1Task( void *pvParameters );
static void prvRegTest2Task( void *pvParameters );

/*
 * The check task as described at the top of this file.
 */
static void prvCheckTask( void *pvParameters );

static void prvSetupHardware( void );

/*
 * Contains the implementation of the WEB server.
 */
//_RB_extern void vuIP_Task( void *pvParameters );

/*-----------------------------------------------------------*/

/* Variables that are incremented on each iteration of the reg test tasks -
provided the tasks have not reported any errors.  The check task inspects these
variables to ensure they are still incrementing as expected.  If a variable
stops incrementing then it is likely that its associate task has stalled. */
unsigned long ulRegTest1CycleCount = 0UL, ulRegTest2CycleCount = 0UL;

/* The status message that is displayed at the bottom of the "task stats" web
page, which is served by the uIP task.  This will report any errors picked up
by the reg test task. */
static const char *pcStatusMessage = NULL;

static XTmrCtr xTimer0Instance;

/*-----------------------------------------------------------*/

int main(void)
{
	/* Configure the interrupt controller, LED outputs and button inputs. */
	prvSetupHardware();
	
	/* Start the reg test tasks which test the context switching mechanism. */
	xTaskCreate( prvRegTest1Task, ( const signed char * const ) "RegTst1", configMINIMAL_STACK_SIZE, ( void * ) mainREG_TEST_1_PARAMETER, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvRegTest2Task, ( const signed char * const ) "RegTst2", configMINIMAL_STACK_SIZE, ( void * ) mainREG_TEST_2_PARAMETER, tskIDLE_PRIORITY, NULL );

	/* The web server task. */
//_RB_	xTaskCreate( vuIP_Task, "uIP", mainuIP_STACK_SIZE, NULL, mainuIP_TASK_PRIORITY, NULL );

	/* Start the check task as described at the top of this file. */
	xTaskCreate( prvCheckTask, ( const signed char * const ) "Check", configMINIMAL_STACK_SIZE * 3, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Create the standard demo tasks. */
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vCreateBlockTimeTasks();
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartLEDFlashTasks( mainFLASH_TASK_PRIORITY );
	vStartQueuePeekTasks();
	vStartRecursiveMutexTasks();
	vStartMathTasks( mainFLOP_TASK_PRIORITY );

	/* The suicide tasks must be created last as they need to know how many
	tasks were running prior to their creation in order to ascertain whether
	or not the correct/expected number of tasks are running at any given time. */
	vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

	/* Start the tasks running. */
	vTaskStartScheduler();

	/* If all is well we will never reach here as the scheduler will now be
	running.  If we do reach here then it is likely that there was insufficient
	heap available for the idle task to be created. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
static volatile unsigned long ulLastRegTest1CycleCount = 0UL, ulLastRegTest2CycleCount = 0UL;
portTickType xNextWakeTime, xCycleFrequency = mainNO_ERROR_CYCLE_TIME;
extern void vSetupHighFrequencyTimer( void );

	/* Initialise xNextWakeTime - this only needs to be done once. */
	xNextWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Place this task in the blocked state until it is time to run again. */
		vTaskDelayUntil( &xNextWakeTime, xCycleFrequency );

		/* Check the standard demo tasks are running without error. */
		if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			/* Increase the rate at which this task cycles, which will increase the
			rate at which mainCHECK_LED flashes to give visual feedback that an error
			has occurred. */			
			pcStatusMessage = "Error: GenQueue";
			xPrintf( pcStatusMessage );
		}
		
		if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error: QueuePeek\r\n";
			xPrintf( pcStatusMessage );
		}
		
		if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error: BlockQueue\r\n";
			xPrintf( pcStatusMessage );
		}
		
		if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error: BlockTime\r\n";
			xPrintf( pcStatusMessage );
		}
		
		if( xAreSemaphoreTasksStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error: SemTest\r\n";
			xPrintf( pcStatusMessage );
		}
		
		if( xArePollingQueuesStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error: PollQueue\r\n";
			xPrintf( pcStatusMessage );
		}
		
		if( xIsCreateTaskStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error: Death\r\n";
			xPrintf( pcStatusMessage );
		}
		
		if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error: RecMutex\r\n";
			xPrintf( pcStatusMessage );
		}
		
		if( xAreMathsTaskStillRunning() != pdPASS )
		{
			pcStatusMessage = "Error: Flop\r\n";
			xPrintf( pcStatusMessage );
		}

		/* Check the reg test tasks are still cycling.  They will stop incrementing
		their loop counters if they encounter an error. */
		if( ulRegTest1CycleCount == ulLastRegTest1CycleCount )
		{
			pcStatusMessage = "Error: RegTest1\r\n";
			xPrintf( pcStatusMessage );
		}

		if( ulRegTest2CycleCount == ulLastRegTest2CycleCount )
		{
			pcStatusMessage = "Error: RegTest2\r\n";
			xPrintf( pcStatusMessage );
		}

		ulLastRegTest1CycleCount = ulRegTest1CycleCount;
		ulLastRegTest2CycleCount = ulRegTest2CycleCount;

		/* Toggle the check LED to give an indication of the system status.  If
		the LED toggles every 5 seconds then everything is ok.  A faster toggle
		indicates an error. */
		vParTestToggleLED( mainCHECK_LED );
		
		/* Ensure the LED toggles at a faster rate if an error has occurred. */
		if( pcStatusMessage != NULL )
		{
			xCycleFrequency = mainERROR_CYCLE_TIME;
		}
	}
}
/*-----------------------------------------------------------*/

void vApplicationSetupTimerInterrupt( void )
{
portBASE_TYPE xStatus;
const unsigned char ucTimerCounterNumber = ( unsigned char ) 0U;
const unsigned long ulCounterValue = ( ( XPAR_AXI_TIMER_0_CLOCK_FREQ_HZ / configTICK_RATE_HZ ) - 1UL );
extern void vTickISR( void *pvUnused );

	/* Initialise the timer/counter. */
	xStatus = XTmrCtr_Initialize( &xTimer0Instance, XPAR_AXI_TIMER_0_DEVICE_ID );

	if( xStatus == XST_SUCCESS )
	{
		/* Install the tick interrupt handler as the timer ISR. */
		xStatus = xPortInstallInterruptHandler( XPAR_MICROBLAZE_0_INTC_AXI_TIMER_0_INTERRUPT_INTR, vTickISR, NULL );
	}

	if( xStatus == pdPASS )
	{
		vPortEnableInterrupt( XPAR_MICROBLAZE_0_INTC_AXI_TIMER_0_INTERRUPT_INTR );

		/* Configure the timer interrupt handler. */
		XTmrCtr_SetHandler( &xTimer0Instance, ( void * ) vTickISR, NULL );

		/* Set the correct period for the timer. */
		XTmrCtr_SetResetValue( &xTimer0Instance, ucTimerCounterNumber, ulCounterValue );

		/* Enable the interrupts.  Auto-reload mode is used to generate a
		periodic tick.  Note that interrupts are disabled when this function is
		called, so interrupts will not start to be processed until the first
		task has started to run. */
		XTmrCtr_SetOptions( &xTimer0Instance, ucTimerCounterNumber, ( XTC_INT_MODE_OPTION | XTC_AUTO_RELOAD_OPTION | XTC_DOWN_COUNT_OPTION ) );

		/* Start the timer. */
		XTmrCtr_Start( &xTimer0Instance, ucTimerCounterNumber );
	}

	configASSERT( ( xStatus == pdPASS ) );
}
/*-----------------------------------------------------------*/

void vApplicationClearTimerInterrupt( void )
{
unsigned long ulCSR;

	/* Increment the RTOS tick - this might cause a task to unblock. */
	vTaskIncrementTick();

	/* Clear the timer interrupt */
	ulCSR = XTmrCtr_GetControlStatusReg( XPAR_AXI_TIMER_0_BASEADDR, 0 );
	XTmrCtr_SetControlStatusReg( XPAR_AXI_TIMER_0_BASEADDR, 0, ulCSR );
}
/*-----------------------------------------------------------*/

/* This function is explained by the comments above its prototype at the top
of this file. */
void vApplicationMallocFailedHook( void )
{
	for( ;; );
}
/*-----------------------------------------------------------*/

/* This function is explained by the comments above its prototype at the top
of this file. */
void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed char *pcTaskName )
{
	for( ;; );
}
/*-----------------------------------------------------------*/

/* This function is explained by the comments above its prototype at the top
of this file. */
void vApplicationIdleHook( void )
{
}
/*-----------------------------------------------------------*/

/* This function is explained in the comments at the top of this file. */
static void prvRegTest1Task( void *pvParameters )
{
	configASSERT( pvParameters == ( void * ) mainREG_TEST_1_PARAMETER );

	for( ;; )
	{
		vTaskDelay( 10000 );
	}
}
/*-----------------------------------------------------------*/

/* This function is explained in the comments at the top of this file. */
static void prvRegTest2Task( void *pvParameters )
{
	configASSERT( pvParameters == ( void * ) mainREG_TEST_2_PARAMETER );

	for( ;; )
	{
		vTaskDelay( 10000 );
	}
}
/*-----------------------------------------------------------*/

char *pcGetTaskStatusMessage( void )
{
	/* Not bothered about a critical section here although technically because of
	the task priorities the pointer could change it will be atomic if not near
	atomic and its not critical. */
	if( pcStatusMessage == NULL )
	{
		return "All tasks running without error";
	}
	else
	{
		return ( char * ) pcStatusMessage;
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
#if 0
portBASE_TYPE xStatus;
const unsigned char ucSetToOutput = 0U;

	/* Set up the GPIO port for the LED outputs. */
	vParTestInitialise();

	/* Initialise the GPIO for the button inputs. */
	if( xStatus == XST_SUCCESS )
	{
		xStatus = XGpio_Initialize( &xInputGPIOInstance, XPAR_PUSH_BUTTONS_4BITS_DEVICE_ID );
	}

	if( xStatus == XST_SUCCESS )
	{
		/* Install the handler defined in this task for the button input. */
		xStatus = xPortInstallInterruptHandler( XPAR_MICROBLAZE_0_INTC_PUSH_BUTTONS_4BITS_IP2INTC_IRPT_INTR, prvButtonInputInterruptHandler, NULL );

		if( xStatus == pdPASS )
		{
			/* Set buttons to input. */
			XGpio_SetDataDirection( &xInputGPIOInstance, uxGPIOInputChannel, ~( ucSetToOutput ) );


			vPortEnableInterrupt( XPAR_MICROBLAZE_0_INTC_PUSH_BUTTONS_4BITS_IP2INTC_IRPT_INTR );

			/* Enable GPIO channel interrupts. */
			XGpio_InterruptEnable( &xInputGPIOInstance, uxGPIOInputChannel ); //_RB_
			XGpio_InterruptGlobalEnable( &xInputGPIOInstance );
		}
	}

	configASSERT( ( xStatus == pdPASS ) );
#else
	vParTestInitialise();
#endif //_RB_

	#ifdef MICROBLAZE_EXCEPTIONS_ENABLED
		microblaze_enable_exceptions();
	#endif
}
/*-----------------------------------------------------------*/

