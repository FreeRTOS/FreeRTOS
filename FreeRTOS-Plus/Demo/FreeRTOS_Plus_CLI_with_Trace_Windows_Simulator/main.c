/*
    FreeRTOS V9.0.0 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*
 ******************************************************************************
 * -NOTE- The Win32 port is a simulation (or is that emulation?) only!  Do not
 * expect to get real time behaviour from the Win32 port or this demo
 * application.  It is provided as a convenient development and demonstration
 * test bed only.  This was tested using Windows XP on a dual core laptop.
 *
 * Windows will not be running the FreeRTOS simulator threads continuously, so
 * the timing information in the FreeRTOS+Trace logs have no meaningful units.
 * See the documentation page for the Windows simulator for an explanation of
 * the slow timing:
 * http://www.freertos.org/FreeRTOS-Windows-Simulator-Emulator-for-Visual-Studio-and-Eclipse-MingW.html
 * - READ THE WEB DOCUMENTATION FOR THIS PORT FOR MORE INFORMATION ON USING IT -
 *
 * Documentation for this demo can be found on:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_Trace/Free_RTOS_Plus_Trace_CLI_Example.shtml
 ******************************************************************************
 *
 * This is a simple FreeRTOS Windows simulator project that makes it easy to
 * evaluate FreeRTOS+CLI and FreeRTOS+Trace on a standard desktop PC, without
 * any external hardware or interfaces being required.
 *
 * To keep everything as simple as possible, the command line interface is
 * accessed through a UDP socket on the default Windows loopback IP address of
 * 127.0.0.1.  Full instructions are provided on the documentation page
 * referenced above.
 *
 * Commands are provided to both start and stop a FreeRTOS+Trace recording.
 * Stopping a recording will result in the recorded data being saved to the
 * hard disk, ready for viewing in the FreeRTOS+Trace graphical user interface.
 * Again, full instructions are provided on the documentation page referenced
 * above.
 *
 * A queue send task and a queue receive task are defined in this file.  The
 * queue receive task spends most of its time blocked on the queue waiting for
 * messages to arrive.  The queue send task periodically sends a message to the
 * queue, causing the queue receive task to exit the Blocked state.  The
 * priority of the queue receive task is above that of the queue send task, so
 * it pre-empts the queue send task as soon as it leaves the Blocked state.  It
 * then consumes the message from the queue and prints "message received" to
 * the screen before returning to block on the queue once again.  This
 * sequencing is clearly visible in the recorded FreeRTOS+Trace data.
 *
 */

/* Standard includes. */
#include <stdio.h>
#include <stdint.h>

/* FreeRTOS includes. */
#include <FreeRTOS.h>
#include "task.h"
#include "queue.h"

/* Priorities at which the tasks are created. */
#define mainQUEUE_RECEIVE_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define	mainQUEUE_SEND_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainUDP_CLI_TASK_PRIORITY			( tskIDLE_PRIORITY )

/* The rate at which data is sent to the queue.  The (simulated) 250ms value is
converted to ticks using the portTICK_RATE_MS constant. */
#define mainQUEUE_SEND_FREQUENCY_MS			( 250 / portTICK_RATE_MS )

/* The number of items the queue can hold.  This is 1 as the receive task
will remove items as they are added, meaning the send task should always find
the queue empty. */
#define mainQUEUE_LENGTH					( 1 )

/*-----------------------------------------------------------*/

/*
 * The queue send and receive tasks as described in the comments at the top of
 * this file.
 */
static void prvQueueReceiveTask( void *pvParameters );
static void prvQueueSendTask( void *pvParameters );

/*
 * The task that implements the UDP command interpreter using FreeRTOS+CLI.
 */
extern void vUDPCommandInterpreterTask( void *pvParameters );

/*
 * Register commands that can be used with FreeRTOS+CLI through the UDP socket.
 * The commands are defined in CLI-commands.c.
 */
extern void vRegisterCLICommands( void );

/* The queue used by both tasks. */
static xQueueHandle xQueue = NULL;

/*-----------------------------------------------------------*/

int main( void )
{
const uint32_t ulLongTime_ms = 250UL;

	/* Initialise the trace recorder and create the label used to post user
	events to the trace recording on each tick interrupt. */
	vTraceEnable( TRC_START );

	/* Create the queue used to pass messages from the queue send task to the
	queue receive task. */
	xQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( unsigned long ) );

	/* Give the queue a name for the FreeRTOS+Trace log. */
	vTraceSetQueueName( xQueue, "DemoQ" );

	/* Start the two tasks as described in the comments at the top of this
	file. */
	xTaskCreate( prvQueueReceiveTask,				/* The function that implements the task. */
				"Rx", 								/* The text name assigned to the task - for debug only as it is not used by the kernel. */
				configMINIMAL_STACK_SIZE, 			/* The size of the stack to allocate to the task.  Not actually used as a stack in the Win32 simulator port. */
				NULL,								/* The parameter passed to the task - not used in this example. */
				mainQUEUE_RECEIVE_TASK_PRIORITY, 	/* The priority assigned to the task. */
				NULL );								/* The task handle is not required, so NULL is passed. */

	xTaskCreate( prvQueueSendTask, "TX", configMINIMAL_STACK_SIZE, NULL, mainQUEUE_SEND_TASK_PRIORITY, NULL );

	/* Create the task that handles the CLI on a UDP port.  The port number
	is set using the configUDP_CLI_PORT_NUMBER setting in FreeRTOSConfig.h. */
	xTaskCreate( vUDPCommandInterpreterTask, "CLI", configMINIMAL_STACK_SIZE, NULL, mainUDP_CLI_TASK_PRIORITY, NULL );

	/* Register commands with the FreeRTOS+CLI command interpreter. */
	vRegisterCLICommands();

	/* Start the tasks and timer running. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following
	line will never be reached.  If the following line does execute, then
	there was insufficient FreeRTOS heap memory available for the idle and/or
	timer tasks	to be created.  See the memory management section on the
	FreeRTOS web site for more details (this is standard text that is not
	really applicable to the Win32 simulator port). */
	for( ;; )
	{
		Sleep( ulLongTime_ms );
	}
}
/*-----------------------------------------------------------*/

static void prvQueueSendTask( void *pvParameters )
{
TickType_t xNextWakeTime;
const unsigned long ulValueToSend = 100UL;

	/* Remove warning about unused parameters. */
	( void ) pvParameters;

	/* Initialise xNextWakeTime - this only needs to be done once. */
	xNextWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Place this task in the blocked state until it is time to run again.
		While in the Blocked state this task will not consume any CPU time. */
		vTaskDelayUntil( &xNextWakeTime, mainQUEUE_SEND_FREQUENCY_MS );

		/* Send to the queue - causing the queue receive task to unblock and
		write a message to the display.  0 is used as the block time so the
		sending operation will not block - it shouldn't need to block as the
		queue should always	be empty at this point in the code, and it is an
		error if it is not. */
		xQueueSend( xQueue, &ulValueToSend, 0U );
	}
}
/*-----------------------------------------------------------*/

static void prvQueueReceiveTask( void *pvParameters )
{
unsigned long ulReceivedValue;

	/* Remove warning about unused parameters. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Wait until something arrives in the queue - this task will block
		indefinitely provided INCLUDE_vTaskSuspend is set to 1 in
		FreeRTOSConfig.h. */
		xQueueReceive( xQueue, &ulReceivedValue, portMAX_DELAY );

		/*  To get here something must have been received from the queue, but
		is it the expected value?  If it is, write the message to the
		display before looping back to block on the queue again. */
		if( ulReceivedValue == 100UL )
		{
			printf( "Message received!\r\n" );
			ulReceivedValue = 0U;
		}
	}
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
const unsigned long ulMSToSleep = 5;

	/* This function is called on each cycle of the idle task if
	configUSE_IDLE_HOOK is set to 1 in FreeRTOSConfig.h.  Sleep to reduce CPU
	load. */
	Sleep( ulMSToSleep );
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


