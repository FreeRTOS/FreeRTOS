/*
    FreeRTOS V7.6.0 - Copyright (C) 2013 Real Time Engineers Ltd.
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

/* ****************************************************************************
 * When configCREATE_LOW_POWER_DEMO is set to 1 in FreeRTOSConfig.h main() will
 * call main_low_power(), which is defined in this file.  main_low_power()
 * demonstrates FreeRTOS tick suppression being used to allow the MCU to be
 * placed into the Retention low power mode.  When configCREATE_LOW_POWER_DEMO
 * is set to 0 main will instead call main_full(), which is a more comprehensive
 * RTOS demonstration.
 * ****************************************************************************
 *
 * This application demonstrates the FreeRTOS tickless idle mode (tick
 * suppression).  See http://www.freertos.org/low-power-tickless-rtos.html
 * The demo is configured to execute on the SAM4L-EK.
 *
 * Functionality:
 *
 *  + Two tasks are created, an Rx task and a Tx task.
 *
 *  + The Rx task blocks on a queue to wait for data, blipping an LED each time
 *    data is received (turning it on and then off again) before returning to
 *    block on the queue once more.
 *
 *  + The Tx task repeatedly enters the Blocked state for 500ms.  On exiting the
 *    blocked state the Tx task sends a value through the queue to the Rx task
 *    (causing the Rx task to exit the blocked state and blip the LED).
 *
 *    Blocking for a finite period allows the kernel to stop the tick interrupt
 *    and place the SAM4L into Retention mode - the lowest power mode possible
 *    that allows the CPU registers and RAM to retain their state.
 *
 * Observed behaviour:
 *
 * For correct results the SAM4L-EK must be connected (and powered) using only
 * the JTAG USB connector, but the debugger must not be connected (the
 * application must be executed 'stand alone').
 *
 * The MCU spends most of its time in the Retention low power state, during
 * which times the current monitor (built onto the SAM4L-EK) will show a low
 * current reading.
 *
 * Every 500ms the MCU will come out of the low power state to turn the LED on,
 * then return to the low power state for 20ms before leaving the low power
 * state again to turn the LED off.  This will be observed as a fast blipping
 * on the LED, and two very brief dots appearing on the current monitor graph
 * (often observed as a single dot).
 *
 * The RTOS tick is suppressed while the MCU is in its low power state.
 *
 */

/* ASF includes. */
#include <asf.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Common demo includes. */
#include "partest.h"

/* Priorities at which the Rx and Tx tasks are created. */
#define configQUEUE_RECEIVE_TASK_PRIORITY	( tskIDLE_PRIORITY + 1 )
#define	configQUEUE_SEND_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )

/* The number of items the queue can hold.  This is 1 as the Rx task will
remove items as they are added so the Tx task should always find the queue
empty. */
#define mainQUEUE_LENGTH					( 1 )

/* The LED used to indicate that a value has been received on the queue. */
#define mainQUEUE_LED						( 0 )

/* The rate at which the Tx task sends to the queue. */
#define mainTX_DELAY						( 500UL / portTICK_RATE_MS )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0 )

/* The value that is sent from the Tx task to the Rx task on the queue. */
#define mainQUEUED_VALUE					( 100UL )

/* The length of time the LED will remain on for.  It is on just long enough
to be able to see with the human eye so as not to distort the power readings too
much. */
#define mainLED_TOGGLE_DELAY				( 20 / portTICK_RATE_MS )

/*-----------------------------------------------------------*/

/*
 * The Rx and Tx tasks as described at the top of this file.
 */
static void prvQueueReceiveTask( void *pvParameters );
static void prvQueueSendTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* The queue to pass data from the Tx task to the Rx task. */
static xQueueHandle xQueue = NULL;

/*-----------------------------------------------------------*/

void main_low_power( void )
{
	/* Create the queue. */
	xQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( unsigned long ) );
	configASSERT( xQueue );

	/* Start the two tasks as described at the top of this file. */
	xTaskCreate( prvQueueReceiveTask, "Rx", configMINIMAL_STACK_SIZE, NULL, configQUEUE_RECEIVE_TASK_PRIORITY, NULL );
	xTaskCreate( prvQueueSendTask, "TX", configMINIMAL_STACK_SIZE, NULL, configQUEUE_SEND_TASK_PRIORITY, NULL );

	/* Start the scheduler running running. */
	vTaskStartScheduler();

	/* If all is well the next line of code will not be reached as the
	scheduler will be running.  If the next line is reached then it is likely
	there was insufficient FreeRTOS heap available for the idle task and/or
	timer task to be created.  See http://www.freertos.org/a00111.html. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvQueueSendTask( void *pvParameters )
{
const unsigned long ulValueToSend = mainQUEUED_VALUE;

	/* Remove compiler warning about unused parameter. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Place this task into the blocked state until it is time to run again.
		The kernel will place the MCU into the Retention low power sleep state
		when the idle task next runs. */
		vTaskDelay( mainTX_DELAY );

		/* Send to the queue - causing the queue receive task to flash its LED.
		It should not be necessary to block on the queue send because the Rx
		task will already have removed the last queued item. */
		xQueueSend( xQueue, &ulValueToSend, mainDONT_BLOCK );
	}
}
/*-----------------------------------------------------------*/

static void prvQueueReceiveTask( void *pvParameters )
{
unsigned long ulReceivedValue;

	/* Remove compiler warning about unused parameter. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Wait until something arrives in the queue. */
		xQueueReceive( xQueue, &ulReceivedValue, portMAX_DELAY );

		/*  To get here something must have arrived, but is it the expected
		value?  If it is, turn the LED on for a short while. */
		if( ulReceivedValue == mainQUEUED_VALUE )
		{
			vParTestSetLED( mainQUEUE_LED, pdTRUE );
			vTaskDelay( mainLED_TOGGLE_DELAY );
			vParTestSetLED( mainQUEUE_LED, pdFALSE );
		}
	}
}
/*-----------------------------------------------------------*/

void vPreSleepProcessing( unsigned long ulExpectedIdleTime )
{
	/* Called by the kernel before it places the MCU into a sleep mode because
	configPRE_SLEEP_PROCESSING() is #defined to vPreSleepProcessing().

	NOTE:  Additional actions can be taken here to get the power consumption
	even lower.  For example, peripherals can be turned	off here, and then back
	on again in the post sleep processing function.  For maximum power saving
	ensure all unused pins are in their lowest power state. */

	/* Avoid compiler warnings about the unused parameter. */
	( void ) ulExpectedIdleTime;
}
/*-----------------------------------------------------------*/

void vPostSleepProcessing( unsigned long ulExpectedIdleTime )
{
	/* Called by the kernel when the MCU exits a sleep mode because
	configPOST_SLEEP_PROCESSING is #defined to vPostSleepProcessing(). */

	/* Avoid compiler warnings about the unused parameter. */
	( void ) ulExpectedIdleTime;
}
/*-----------------------------------------------------------*/

