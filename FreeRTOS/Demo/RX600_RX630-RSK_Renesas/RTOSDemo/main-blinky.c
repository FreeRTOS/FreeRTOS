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
 * This is a very simple demo that creates two tasks and one queue.  One task
 * (the queue receive task) blocks on the queue to wait for data to arrive, 
 * toggling an LED each time '100' is received.  The other task (the queue send
 * task) repeatedly blocks for a fixed period before sending '100' to the queue
 * (causing the first task to toggle the LED). 
 *
 * For a much more complete and complex example select either the Debug or
 * Debug_with_optimisation build configurations within the HEW IDE. 
*/

/* Hardware specific includes. */
#include "iodefine.h"

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Priorities at which the tasks are created. */
#define configQUEUE_RECEIVE_TASK_PRIORITY	( tskIDLE_PRIORITY + 1 )
#define	configQUEUE_SEND_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )

/* The rate at which data is sent to the queue, specified in milliseconds. */
#define mainQUEUE_SEND_FREQUENCY_MS			( 500 / portTICK_PERIOD_MS )

/* The number of items the queue can hold.  This is 1 as the receive task
will remove items as they are added so the send task should always find the
queue empty. */
#define mainQUEUE_LENGTH					( 1 )

/*
 * The tasks as defined at the top of this file.
 */
static void prvQueueReceiveTask( void *pvParameters );
static void prvQueueSendTask( void *pvParameters );

/* The queue used by both tasks. */
static QueueHandle_t xQueue = NULL;

/* This variable is not used by this simple Blinky example.  It is defined 
purely to allow the project to link as it is used by the full build 
configuration. */
volatile unsigned long ulHighFrequencyTickCount = 0UL;
/*-----------------------------------------------------------*/

void main(void)
{
extern void HardwareSetup( void );

	/* Renesas provided CPU configuration routine.  The clocks are configured in
	here. */
	HardwareSetup();
	
	/* Turn all LEDs off. */
	vParTestInitialise();
	
	/* Create the queue. */
	xQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( unsigned long ) );

	if( xQueue != NULL )
	{
		/* Start the two tasks as described at the top of this file. */
		xTaskCreate( prvQueueReceiveTask, "Rx", configMINIMAL_STACK_SIZE, NULL, configQUEUE_RECEIVE_TASK_PRIORITY, NULL );
		xTaskCreate( prvQueueSendTask, "TX", configMINIMAL_STACK_SIZE, NULL, configQUEUE_SEND_TASK_PRIORITY, NULL );

		/* Start the tasks running. */
		vTaskStartScheduler();
	}
	
	/* If all is well the next line of code will not be reached as the scheduler 
	will be	running.  If the next line is reached then it is likely that there was 
	insufficient heap available for the idle task to be created. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvQueueSendTask( void *pvParameters )
{
TickType_t xNextWakeTime;
const unsigned long ulValueToSend = 100UL;

	/* Initialise xNextWakeTime - this only needs to be done once. */
	xNextWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Place this task in the blocked state until it is time to run again. 
		The block state is specified in ticks, the constant used converts ticks
		to ms. */
		vTaskDelayUntil( &xNextWakeTime, mainQUEUE_SEND_FREQUENCY_MS );

		/* Send to the queue - causing the queue receive task to flash its LED.  0
		is used so the send does not block - it shouldn't need to as the queue
		should always be empty here (it should always be empty because the task
		removing items from the queue has a higher priority than the task adding
		things to the queue). */
		xQueueSend( xQueue, &ulValueToSend, 0UL );
	}
}
/*-----------------------------------------------------------*/

static void prvQueueReceiveTask( void *pvParameters )
{
unsigned long ulReceivedValue;

	for( ;; )
	{
		/* Wait until something arives in the queue - this will block 
		indefinitely provided INCLUDE_vTaskSuspend is set to 1 in
		FreeRTOSConfig.h. */
		xQueueReceive( xQueue, &ulReceivedValue, portMAX_DELAY );

		/*  To get here something must have arrived, but is it the expected
		value?  If it is, toggle the LED. */
		if( ulReceivedValue == 100UL )
		{
			vParTestToggleLED( 0 );
		}
	}
}
/*-----------------------------------------------------------*/

/* A callback function named vApplicationSetupTimerInterrupt() must be defined
to configure a tick interrupt source, and configTICK_VECTOR set in 
FreeRTOSConfig.h to install the tick interrupt handler in the correct position
in the vector table.  This example uses a compare match timer.  It can be
into any FreeRTOS project, provided the same compare match timer is available. */
void vApplicationSetupTimerInterrupt( void )
{
	/* Enable compare match timer 0. */
	MSTP( CMT0 ) = 0;
	
	/* Interrupt on compare match. */
	CMT0.CMCR.BIT.CMIE = 1;
	
	/* Set the compare match value. */
	CMT0.CMCOR = ( unsigned short ) ( ( ( configPERIPHERAL_CLOCK_HZ / configTICK_RATE_HZ ) -1 ) / 8 );
	
	/* Divide the PCLK by 8. */
	CMT0.CMCR.BIT.CKS = 0;
	
	/* Enable the interrupt... */
	_IEN( _CMT0_CMI0 ) = 1;
	
	/* ...and set its priority to the application defined kernel priority. */
	_IPR( _CMT0_CMI0 ) = configKERNEL_INTERRUPT_PRIORITY;
	
	/* Start the timer. */
	CMT.CMSTR0.BIT.STR0 = 1;
}
/*-----------------------------------------------------------*/

/* If configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h, then this
function will be called if pvPortMalloc() returns NULL because it has exhausted
the available FreeRTOS heap space.  See http://www.freertos.org/a00111.html. */
void vApplicationMallocFailedHook( void )
{
	for( ;; );
}
/*-----------------------------------------------------------*/

/* If configCHECK_FOR_STACK_OVERFLOW is set to either 1 or 2 in 
FreeRTOSConfig.h, then this function will be called if a task overflows its 
stack space.  See 
http://www.freertos.org/Stacks-and-stack-overflow-checking.html. */
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	for( ;; );
}
/*-----------------------------------------------------------*/

/* If configUSE_IDLE_HOOK is set to 1 in FreeRTOSConfig.h, then this function
will be called on each iteration of the idle task.  See 
http://www.freertos.org/a00016.html */
void vApplicationIdleHook( void )
{
	/* Just to prevent the variable getting optimised away. */
	( void ) ulHighFrequencyTickCount;
}
/*-----------------------------------------------------------*/
