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

/* ****************************************************************************
 * When configCREATE_LOW_POWER_DEMO is set to 1 in FreeRTOSConfig.h main() will
 * call main_low_power(), which is defined in this file.  main_low_power()
 * demonstrates FreeRTOS tick suppression being used to allow the MCU to be
 * placed into both the low power deep sleep mode and the low power software
 * standby mode.  When configCREATE_LOW_POWER_DEMO is set to 0 main will
 * instead call main_full(), which is a more comprehensive RTOS demonstration.
 * ****************************************************************************
 *
 * This application demonstrates the FreeRTOS tickless idle mode (tick
 * suppression).  See http://www.freertos.org/low-power-tickless-rtos.html
 * The demo is configured to execute on the Renesas RX100 RSK.
 *
 *  Functionality:
 *
 *  + Two tasks are created, an Rx task and a Tx task.
 *
 *  + The Rx task repeatedly blocks on a queue to wait for data.  The Rx task
 *    toggles LED 0 each time is receives a value from the queue.
 *
 *  + The Tx task repeatedly enters the Blocked state for an amount of time
 *    that is set by the position of the potentiometer.  On exiting the blocked
 *    state the Tx task sends a value through the queue to the Rx task (causing
 *    the Rx task to exit the blocked state and toggle LED 0).
 *
 *    If the value read from the potentiometer is less than or equal to
 *    mainSOFTWARE_STANDBY_DELAY then the Tx task blocks for the equivalent
 *    number of milliseconds.  For example, if the sampled analog value is
 *    2000, then the Tx task blocks for 2000ms.  Blocking for a finite period
 *    allows the kernel to stop the tick interrupt and place the RX100 into
 *    deep sleep mode.
 *
 *    If the value read form the potentiometer is greater than
 *    mainSOFTWARE_STANDBY_DELAY then the Tx task blocks on a semaphore with
 *    an infinite timeout.  Blocking with an infinite timeout allows the kernel
 *    to stop the tick interrupt and place the RX100 into software standby
 *    mode.  Pressing a button will generate an interrupt that causes the RX100
 *    to exit software standby mode.  The interrupt service routine 'gives' the
 *    semaphore to unblock the Tx task.
 *
 *
 *  Using the Demo and Observed Behaviour:
 *
 *  1) Turn the potentiometer completely counter clockwise.
 *
 *  2) Program the RX100 with the application, then disconnect the programming/
 *   debugging hardware to ensure power readings are not effected by any
 *   connected interfaces.
 *
 *  3) Start the application running.  LED 0 will toggle quickly because the
 *   potentiometer is turned to its lowest value.  LED 1 will be illuminated
 *   when the RX100 is not in a power saving mode, but will appear to be off
 *   because most execution time is spent in a sleep mode.  Led 2 will be
 *   illuminated when the RX100 is in deep sleep mode, and will appear to be
 *   always on, again because most execution time is spent in deep sleep mode.
 *   The LEDs are turned on and off by the application defined pre and post
 *   sleep macros (see the definitions of configPRE_SLEEP_PROCESSING() and
 *   configPOST_SLEEP_PROCESSING() in FreeRTOSConfig.h).
 *
 *  4) Slowly turn the potentiometer in the clockwise direction.  This will
 *   increase the value read from the potentiometer, which will increase the
 *   time the Tx task spends in the Blocked state, which will therefore
 *   decrease the frequency at which the Tx task sends data to the queue (and
 *   the rate at which LED 0 is toggled).
 *
 *  5) Keep turning the potentiometer in the clockwise direction.  Eventually
 *   the value read from the potentiometer will go above
 *   mainSOFTWARE_STANDBY_DELAY, causing the Tx task to block on the semaphore
 *   with an infinite timeout.  LED 0 will stop toggling because the Tx task is
 *   no longer sending to the queue.  LED 1 and LED 2 will both be off because
 *   the RX100 is neither running or in deep sleep mode (it is in software
 *   standby mode).
 *
 *  6) Turn the potentiometer counter clockwise again to ensure its value goes
 *   back below mainSOFTWARE_STANDBY_DELAY.
 *
 *  7) Press any of the three buttons to generate an interrupt.  The interrupt
 *   will take the RX100 out of software standby mode, and the interrupt
 *   service routine will unblock the Tx task by 'giving' the semaphore.  LED 0
 *   will then start to toggle again.
 *
 */


/* Hardware specific includes. */
#include "platform.h"
#include "r_switches_if.h"

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

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

/* The LED used to indicate that full power is being used (the MCU is not in
deep sleep or software standby mode). */
#define mainFULL_POWER_LED					( 1 )

/* The LED used to indicate that deep sleep mode is being used. */
#define mainDEEP_SLEEP_LED					( 2 )

/* The Tx task sends to the queue with a frequency that is set by the value
read from the potentiometer until the value goes above that set by the
mainSOFTWARE_STANDBY_DELAY constant - at which time the Tx task instead blocks
indefinitely on a semaphore. */
#define mainSOFTWARE_STANDBY_DELAY			( 3000UL )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0 )

/* The value that is sent from the Tx task to the Rx task on the queue. */
#define mainQUEUED_VALUE					( 100UL )

/*-----------------------------------------------------------*/

/*
 * The Rx and Tx tasks as described at the top of this file.
 */
static void prvQueueReceiveTask( void *pvParameters );
static void prvQueueSendTask( void *pvParameters );

/*
 * Reads and returns the value of the ADC connected to the potentiometer built
 * onto the RSK.
 */
static unsigned short prvReadPOT( void );

/*
 * The handler for the interrupt generated when any of the buttons are pressed.
 */
void vButtonInterruptCallback( void );

/*-----------------------------------------------------------*/

/* The queue to pass data from the Tx task to the Rx task. */
static QueueHandle_t xQueue = NULL;

/* The semaphore that is 'given' by interrupts generated from button pushes. */
static SemaphoreHandle_t xSemaphore = NULL;

/*-----------------------------------------------------------*/

void main_low_power( void )
{
	/* Create the queue. */
	xQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( unsigned long ) );
	configASSERT( xQueue );

	/* Create the semaphore that is 'given' by an interrupt generated from a
	button push. */
	vSemaphoreCreateBinary( xSemaphore );
	configASSERT( xSemaphore );

	/* Make sure the semaphore starts in the expected state - no button pushes
	have yet occurred.  A block time of zero can be used as it is guaranteed
	that the semaphore will be available because it has just been created. */
	xSemaphoreTake( xSemaphore, mainDONT_BLOCK );

	/* Start the two tasks as described at the top of this file. */
	xTaskCreate( prvQueueReceiveTask, "Rx", configMINIMAL_STACK_SIZE, NULL, configQUEUE_RECEIVE_TASK_PRIORITY, NULL );
	xTaskCreate( prvQueueSendTask, "TX", configMINIMAL_STACK_SIZE, NULL, configQUEUE_SEND_TASK_PRIORITY, NULL );

	/* The CPU is currently running, not sleeping, so turn on the LED that
	shows the CPU is not in a sleep mode. */
	vParTestSetLED( mainFULL_POWER_LED, pdTRUE );

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
TickType_t xDelay;
const unsigned long ulValueToSend = mainQUEUED_VALUE;

	/* Remove compiler warning about unused parameter. */
	( void ) pvParameters;

	for( ;; )
	{
		/* The delay period between successive sends to the queue is set by
		the potentiometer reading. */
		xDelay = ( TickType_t ) prvReadPOT();

		/* If the block time is greater than 3000 milliseconds then block
		indefinitely waiting for a button push. */
		if( xDelay > mainSOFTWARE_STANDBY_DELAY )
		{
			/* As this is an indefinite delay the kernel will place the CPU
			into software standby mode the next time the idle task runs. */
			xSemaphoreTake( xSemaphore, portMAX_DELAY );
		}
		else
		{
			/* Convert a time in milliseconds to a time in ticks. */
			xDelay /= portTICK_PERIOD_MS;

			/* Place this task in the blocked state until it is time to run
			again.  As this is not an indefinite sleep the kernel will place
			the CPU into the deep sleep state when the idle task next runs. */
			vTaskDelay( xDelay );
		}

		/* Send to the queue - causing the queue receive task to flash its LED.
		It should not be necessary to block on the queue send because the Rx
		task will have removed the last queued item. */
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
		/* Wait until something arrives in the queue - this will block
		indefinitely provided INCLUDE_vTaskSuspend is set to 1 in
		FreeRTOSConfig.h. */
		xQueueReceive( xQueue, &ulReceivedValue, portMAX_DELAY );

		/*  To get here something must have arrived, but is it the expected
		value?  If it is, toggle the LED. */
		if( ulReceivedValue == mainQUEUED_VALUE )
		{
			vParTestToggleLED( mainQUEUE_LED );
		}
	}
}
/*-----------------------------------------------------------*/

void vPreSleepProcessing( unsigned long ulExpectedIdleTime )
{
	/* Called by the kernel before it places the MCU into a sleep mode because
	configPRE_SLEEP_PROCESSING() is #defined to vPreSleepProcessing().

	NOTE:  Additional actions can be taken here to get the power consumption
	even lower.  For example, the ADC input used by this demo could be turned
	off here, and then back on again in the power sleep processing function.
	For maximum power saving ensure all unused pins are in their lowest power
	state. */

	/* Avoid compiler warnings about the unused parameter. */
	( void ) ulExpectedIdleTime;

	/* Is the MCU about to enter deep sleep mode or software standby mode? */
	if( SYSTEM.SBYCR.BIT.SSBY == 0 )
	{
		/* Turn on the LED that indicates deep sleep mode is being entered. */
		vParTestSetLED( mainDEEP_SLEEP_LED, pdTRUE );
	}
	else
	{
		/* Software standby mode is being used, so no LEDs are illuminated to
		ensure minimum power readings are obtained.  Ensure the Queue LED is
		also off. */
		vParTestSetLED( mainQUEUE_LED, pdFALSE );
	}

	/* Turn off the LED that indicates full power is being used. */
	vParTestSetLED( mainFULL_POWER_LED, pdFALSE );
}
/*-----------------------------------------------------------*/

void vPostSleepProcessing( unsigned long ulExpectedIdleTime )
{
	/* Called by the kernel when the MCU exits a sleep mode because
	configPOST_SLEEP_PROCESSING is #defined to vPostSleepProcessing(). */

	/* Avoid compiler warnings about the unused parameter. */
	( void ) ulExpectedIdleTime;

	/* Turn off the LED that indicates deep sleep mode, and turn on the LED
	that indicates full power is being used. */
	vParTestSetLED( mainDEEP_SLEEP_LED, pdFALSE );
	vParTestSetLED( mainFULL_POWER_LED, pdTRUE );
}
/*-----------------------------------------------------------*/

static unsigned short prvReadPOT( void )
{
unsigned short usADCValue;
const unsigned short usMinADCValue = 128;

	/* Start an ADC scan. */
	S12AD.ADCSR.BIT.ADST = 1;
	while( S12AD.ADCSR.BIT.ADST == 1 )
	{
		/* Just waiting for the ADC scan to complete.  Inefficient
		polling! */
	}

	usADCValue = S12AD.ADDR4;

	/* Don't let the ADC value get too small as the LED behaviour will look
	erratic. */
	if( usADCValue < usMinADCValue )
	{
		usADCValue = usMinADCValue;
	}

	return usADCValue;
}
/*-----------------------------------------------------------*/

void vButtonInterruptCallback( void )
{
long lHigherPriorityTaskWoken = pdFALSE;

	/* The semaphore is only created when the build is configured to create the
	low power demo. */
	if( xSemaphore != NULL )
	{
		/* This interrupt will bring the CPU out of deep sleep and software
		standby	modes.  Give the semaphore that was used to place the Tx task
		into an indefinite sleep. */
		if( uxQueueMessagesWaitingFromISR( xSemaphore ) == 0 )
		{
			xSemaphoreGiveFromISR( xSemaphore, &lHigherPriorityTaskWoken );
		}
		else
		{
			/* The semaphore was already available, so the task is not blocked
			on it and there is no point giving it. */
		}

		/* If giving the semaphore caused a task to leave the Blocked state,
		and the task that left the Blocked state has a priority equal to or
		above the priority of the task that this interrupt interrupted, then
		lHigherPriorityTaskWoken will have been set to pdTRUE inside the call
		to xSemaphoreGiveFromISR(), and calling portYIELD_FROM_ISR() will cause
		a context switch to the unblocked task. */
		portYIELD_FROM_ISR( lHigherPriorityTaskWoken );
	}
}

