/*
    FreeRTOS V8.1.2 - Copyright (C) 2014 Real Time Engineers Ltd.
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

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

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
 * main-blinky.c is included when the "Blinky" build configuration is used.
 * main-full.c is included when the "Full" build configuration is used.
 *
 * main-blinky.c (this file) defines a very simple demo that creates two tasks,
 * one queue, and one timer.  It also demonstrates how Cortex-M3 interrupts can
 * interact with FreeRTOS tasks/timers.
 *
 * This simple demo project runs on the SK-FM3-64PMC1 evaluation board, which
 * is populated with an MB9A314 microcontroller.
 *
 * The idle hook function:
 * The idle hook function demonstrates how to query the amount of FreeRTOS heap
 * space that is remaining (see vApplicationIdleHook() defined in this file).
 *
 * The main() Function:
 * main() creates one software timer, one queue, and two tasks.  It then starts
 * the scheduler.
 *
 * The Queue Send Task:
 * The queue send task is implemented by the prvQueueSendTask() function in
 * this file.  prvQueueSendTask() sits in a loop that causes it to repeatedly
 * block for 200 milliseconds, before sending the value 100 to the queue that
 * was created within main().  Once the value is sent, the task loops back
 * around to block for another 200 milliseconds.
 *
 * The Queue Receive Task:
 * The queue receive task is implemented by the prvQueueReceiveTask() function
 * in this file.  prvQueueReceiveTask() sits in a loop that causes it to
 * repeatedly attempt to read data from the queue that was created within
 * main().  When data is received, the task checks the value of the data, and
 * if the value equals the expected 100, toggles an LED on the 7 segment
 * display.  The 'block time' parameter passed to the queue receive function
 * specifies that the task should be held in the Blocked state indefinitely to
 * wait for data to be available on the queue.  The queue receive task will only
 * leave the Blocked state when the queue send task writes to the queue.  As the
 * queue send task writes to the queue every 200 milliseconds, the queue receive
 * task leaves the Blocked state every 200 milliseconds, and therefore toggles
 * the LED every 200 milliseconds.
 *
 * The LED Software Timer and the Button Interrupt:
 * The user button SW2 is configured to generate an interrupt each time it is
 * pressed.  The interrupt service routine switches an LED in the 7 segment
 * display on, and resets the LED software timer.  The LED timer has a 5000
 * millisecond (5 second) period, and uses a callback function that is defined
 * to just turn the LED off again.  Therefore, pressing the user button will
 * turn the LED on, and the LED will remain on until a full five seconds pass
 * without the button being pressed.
 */

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"

/* Fujitsu drivers/libraries. */
#include "mcu.h"

/* Priorities at which the tasks are created. */
#define mainQUEUE_RECEIVE_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define	mainQUEUE_SEND_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )

/* The rate at which data is sent to the queue, specified in milliseconds, and
converted to ticks using the portTICK_PERIOD_MS constant. */
#define mainQUEUE_SEND_FREQUENCY_MS			( 200 / portTICK_PERIOD_MS )

/* The number of items the queue can hold.  This is 1 as the receive task
will remove items as they are added, meaning the send task should always find
the queue empty. */
#define mainQUEUE_LENGTH					( 1 )

/* The LED toggle by the queue receive task. */
#define mainTASK_CONTROLLED_LED				( 1UL << 3UL )

/* The LED turned on by the button interrupt, and turned off by the LED timer. */
#define mainTIMER_CONTROLLED_LED			( 1UL << 2UL )

/*-----------------------------------------------------------*/

/*
 * Setup the NVIC, LED outputs, and button inputs.
 */
static void prvSetupHardware( void );

/*
 * The tasks as described in the comments at the top of this file.
 */
static void prvQueueReceiveTask( void *pvParameters );
static void prvQueueSendTask( void *pvParameters );

/*
 * The LED timer callback function.  This does nothing but switch off the
 * LED defined by the mainTIMER_CONTROLLED_LED constant.
 */
static void vLEDTimerCallback( TimerHandle_t xTimer );

/*-----------------------------------------------------------*/

/* The queue used by both tasks. */
static QueueHandle_t xQueue = NULL;

/* The LED software timer.  This uses vLEDTimerCallback() as its callback
function. */
static TimerHandle_t xLEDTimer = NULL;

/*-----------------------------------------------------------*/

int main(void)
{
	/* Configure the NVIC, LED outputs and button inputs. */
	prvSetupHardware();

	/* Create the queue. */
	xQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( unsigned long ) );

	if( xQueue != NULL )
	{
		/* Start the two tasks as described in the comments at the top of this
		file. */
		xTaskCreate( prvQueueReceiveTask, "Rx", configMINIMAL_STACK_SIZE, NULL, mainQUEUE_RECEIVE_TASK_PRIORITY, NULL );
		xTaskCreate( prvQueueSendTask, "TX", configMINIMAL_STACK_SIZE, NULL, mainQUEUE_SEND_TASK_PRIORITY, NULL );

		/* Create the software timer that is responsible for turning off the LED
		if the button is not pushed within 5000ms, as described at the top of
		this file. */
		xLEDTimer = xTimerCreate( 	"LEDTimer", 					/* A text name, purely to help debugging. */
									( 5000 / portTICK_PERIOD_MS ),	/* The timer period, in this case 5000ms (5s). */
									pdFALSE,						/* This is a one shot timer, so xAutoReload is set to pdFALSE. */
									( void * ) 0,					/* The ID is not used, so can be set to anything. */
									vLEDTimerCallback				/* The callback function that switches the LED off. */
								);

		/* Start the tasks and timer running. */
		vTaskStartScheduler();
	}

	/* If all is well, the scheduler will now be running, and the following line
	will never be reached.  If the following line does execute, then there was
	insufficient FreeRTOS heap memory available for the idle and/or timer tasks
	to be created.  See the memory management section on the FreeRTOS web site
	for more details. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void vLEDTimerCallback( TimerHandle_t xTimer )
{
	/* The timer has expired - so no button pushes have occurred in the last
	five seconds - turn the LED off.  NOTE - accessing the LED port should use
	a critical section because it is accessed from multiple tasks, and the
	button interrupt - in this trivial case, for simplicity, the critical
	section is omitted. */
	FM3_GPIO->PDOR3 |= mainTIMER_CONTROLLED_LED;
}
/*-----------------------------------------------------------*/

/* The ISR executed when the user button is pushed. */
void INT0_7_Handler( void )
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* The button was pushed, so ensure the LED is on before resetting the
	LED timer.  The LED timer will turn the LED off if the button is not
	pushed within 5000ms. */
	FM3_GPIO->PDOR3 &= ~mainTIMER_CONTROLLED_LED;

	/* This interrupt safe FreeRTOS function can be called from this interrupt
	because the interrupt priority is below the
	configMAX_SYSCALL_INTERRUPT_PRIORITY setting in FreeRTOSConfig.h. */
	xTimerResetFromISR( xLEDTimer, &xHigherPriorityTaskWoken );

	/* Clear the interrupt before leaving.  This just clears all the interrupts
	for simplicity, as only one is actually used in this simple demo anyway. */
	FM3_EXTI->EICL = 0x0000;

	/* If calling xTimerResetFromISR() caused a task (in this case the timer
	service/daemon task) to unblock, and the unblocked task has a priority
	higher than or equal to the task that was interrupted, then
	xHigherPriorityTaskWoken will now be set to pdTRUE, and calling
	portEND_SWITCHING_ISR() will ensure the unblocked task runs next. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
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
		The block time is specified in ticks, the constant used converts ticks
		to ms.  While in the Blocked state this task will not consume any CPU
		time. */
		vTaskDelayUntil( &xNextWakeTime, mainQUEUE_SEND_FREQUENCY_MS );

		/* Send to the queue - causing the queue receive task to unblock and
		toggle an LED.  0 is used as the block time so the sending operation
		will not block - it shouldn't need to block as the queue should always
		be empty at this point in the code. */
		xQueueSend( xQueue, &ulValueToSend, 0 );
	}
}
/*-----------------------------------------------------------*/

static void prvQueueReceiveTask( void *pvParameters )
{
unsigned long ulReceivedValue;

	for( ;; )
	{
		/* Wait until something arrives in the queue - this task will block
		indefinitely provided INCLUDE_vTaskSuspend is set to 1 in
		FreeRTOSConfig.h. */
		xQueueReceive( xQueue, &ulReceivedValue, portMAX_DELAY );

		/*  To get here something must have been received from the queue, but
		is it the expected value?  If it is, toggle the LED. */
		if( ulReceivedValue == 100UL )
		{
			/* NOTE - accessing the LED port should use a critical section
			because it is accessed from multiple tasks, and the button interrupt
			- in this trivial case, for simplicity, the critical section is
			omitted. */
			if( ( FM3_GPIO->PDOR3 & mainTASK_CONTROLLED_LED ) != 0 )
			{
				FM3_GPIO->PDOR3 &= ~mainTASK_CONTROLLED_LED;
			}
			else
			{
				FM3_GPIO->PDOR3 |= mainTASK_CONTROLLED_LED;
			}
		}
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
const unsigned short usButtonInputBit = 0x01U;

	SystemInit();
	SystemCoreClockUpdate();

	/* Analog inputs are not used on the LED outputs. */
	FM3_GPIO->ADE  = 0x0000;

	/* Set to output. */
	FM3_GPIO->DDR1 |= 0xFFFF;
	FM3_GPIO->DDR3 |= 0xFFFF;

	/* Set as GPIO. */
	FM3_GPIO->PFR1 &= 0x0000;
	FM3_GPIO->PFR3 &= 0x0000;

	/* Start with all LEDs off. */
	FM3_GPIO->PDOR3 = 0xFFFF;
	FM3_GPIO->PDOR1 = 0xFFFF;

	/* Set the switches to input (P18->P1F). */
	FM3_GPIO->DDR5 = 0x0000;
	FM3_GPIO->PFR5 = 0x0000;

	/* Assign the button input as GPIO. */
	FM3_GPIO->PFR5 |= usButtonInputBit;

	/* Button interrupt on falling edge. */
	FM3_EXTI->ELVR  = 0x0003;

	/* Clear all external interrupts. */
	FM3_EXTI->EICL  = 0x0000;

	/* Enable the button interrupt. */
	FM3_EXTI->ENIR |= usButtonInputBit;

	/* Setup the GPIO and the NVIC for the switch used in this simple demo. */
	NVIC_SetPriority( EXINT0_7_IRQn, configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY );
    NVIC_EnableIRQ( EXINT0_7_IRQn );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* Called if a call to pvPortMalloc() fails because there is insufficient
	free memory available in the FreeRTOS heap.  pvPortMalloc() is called
	internally by FreeRTOS API functions that create tasks, queues, software
	timers, and semaphores.  The size of the FreeRTOS heap is set by the
	configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h. */
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configconfigCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
	/* A tick hook is used by the "Full" build configuration.  The Full and
	blinky build configurations share a FreeRTOSConfig.h header file, so this
	simple build configuration also has to define a tick hook - even though it
	does not actually use it for anything. */
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
volatile size_t xFreeHeapSpace;

	/* This function is called on each cycle of the idle task.  In this case it
	does nothing useful, other than report the amount of FreeRTOS heap that
	remains unallocated. */
	xFreeHeapSpace = xPortGetFreeHeapSize();

	if( xFreeHeapSpace > 100 )
	{
		/* By now, the kernel has allocated everything it is going to, so
		if there is a lot of heap remaining unallocated then
		the value of configTOTAL_HEAP_SIZE in FreeRTOSConfig.h can be
		reduced accordingly. */
	}
}
/*-----------------------------------------------------------*/




