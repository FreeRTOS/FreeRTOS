/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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
 * This is a very simple demo that creates two tasks, one queue, and one 
 * software timer.  For a much more complete and complex example select either 
 * the Debug or Debug_with_optimisation build configurations within the HEW,
 * which build main_full.c in place of this file.
 * 
 * One task (the queue receive task) blocks on the queue to wait for data to 
 * arrive, toggling LED0 each time '100' is received.  The other task (the 
 * queue send task) repeatedly blocks for a fixed period before sending '100' 
 * to the queue (causing the first task to toggle the LED). 
 *
 * The software timer is configured to auto-reload.  The timer callback 
 * function periodically toggles LED1.
 */

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "queue.h"

/* Priorities at which the tasks are created. */
#define configQUEUE_RECEIVE_TASK_PRIORITY	( tskIDLE_PRIORITY + 1 )
#define	configQUEUE_SEND_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )

/* The rate at which data is sent to the queue, specified in milliseconds. */
#define mainQUEUE_SEND_PERIOD_MS			( 500 / portTICK_PERIOD_MS )

/* The period of the software timer, specified in milliseconds. */
#define mainSOFTWARE_TIMER_PERIOD_MS		( 150 / portTICK_PERIOD_MS )

/* The number of items the queue can hold.  This is 1 as the receive task
will remove items as they are added so the send task should always find the
queue empty. */
#define mainQUEUE_LENGTH					( 1 )

/* The LEDs toggle by the task and timer respectively. */
#define mainTASK_LED						( 0 )
#define mainTIMER_LED						( 1 )

/*
 * The tasks as defined at the top of this file.
 */
static void prvQueueReceiveTask( void *pvParameters );
static void prvQueueSendTask( void *pvParameters );

/*
 * The callback function used by the software timer.
 */
static void prvBlinkyTimerCallback( TimerHandle_t xTimer );

/* The queue used by both tasks. */
static QueueHandle_t xQueue = NULL;

/* This variable is not used by this simple Blinky example.  It is defined 
purely to allow the project to link as it is used by the full project. */
volatile unsigned long ulHighFrequencyTickCount = 0UL;
/*-----------------------------------------------------------*/

void main(void)
{
TimerHandle_t xTimer;

	/* Turn all LEDs off. */
	vParTestInitialise();
	
	/* Create the queue. */
	xQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( unsigned long ) );

	/* Create the software timer, as described at the top of this file. */
	xTimer = xTimerCreate( "BlinkyTimer", 					/* Just a text name to make debugging easier - not used by the scheduler. */
							mainSOFTWARE_TIMER_PERIOD_MS, 	/* The timer period. */
							pdTRUE, 						/* Set to pdTRUE for periodic timer, or pdFALSE for one-shot timer. */
							NULL, 							/* The timer ID is not required. */
							prvBlinkyTimerCallback );		/* The function executed when the timer expires. */
							
	if( xTimer != NULL )
	{
		/* Start the timer - it will not actually start running until the
		scheduler has started.  The block time is set to 0, although, because
		xTimerStart() is being called before the scheduler has been started,
		the any block time specified would be ignored anyway. */
		xTimerStart( xTimer, 0UL );
	}
	
	if( xQueue != NULL )
	{
		/* Start the two tasks as described at the top of this file. */
		xTaskCreate( prvQueueReceiveTask, 					/* The function that implements the task. */
					 "Rx", 									/* Just a text name to make debugging easier - not used by the scheduler. */
					 configMINIMAL_STACK_SIZE, 				/* The size of the task stack, in words. */
					 NULL, 									/* The task parameter is not used. */
					 configQUEUE_RECEIVE_TASK_PRIORITY, 	/* The priority assigned to the task when it is created. */
					 NULL );								/* The task handle is not used. */
					 
		xTaskCreate( prvQueueSendTask, "TX", configMINIMAL_STACK_SIZE, NULL, configQUEUE_SEND_TASK_PRIORITY, NULL );

		/* Start the tasks running. */
		vTaskStartScheduler();
	}
	
	/* If all is well we will never reach here as the scheduler will now be
	running.  If we do reach here then it is likely that there was insufficient
	heap available for the idle task to be created. */
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
		vTaskDelayUntil( &xNextWakeTime, mainQUEUE_SEND_PERIOD_MS );

		/* Send to the queue - causing the queue receive task to flash its LED.  0
		is used so the send does not block - it shouldn't need to as the queue
		should always be empty here. */
		xQueueSend( xQueue, &ulValueToSend, 0 );
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
			vParTestToggleLED( mainTASK_LED );
		}
	}
}
/*-----------------------------------------------------------*/

static void prvBlinkyTimerCallback( TimerHandle_t xTimer )
{
	/* The software timer does nothing but toggle an LED. */
	vParTestToggleLED( mainTIMER_LED );
}
/*-----------------------------------------------------------*/

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

/* This function is explained by the comments above its prototype at the top
of this file. */
void vApplicationMallocFailedHook( void )
{
	for( ;; );
}
/*-----------------------------------------------------------*/

/* This function is explained by the comments above its prototype at the top
of this file. */
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	for( ;; );
}
/*-----------------------------------------------------------*/

/* This function is explained by the comments above its prototype at the top
of this file. */
void vApplicationIdleHook( void )
{
	/* Just to prevent the variable getting optimised away. */
	( void ) ulHighFrequencyTickCount;
}
/*-----------------------------------------------------------*/
