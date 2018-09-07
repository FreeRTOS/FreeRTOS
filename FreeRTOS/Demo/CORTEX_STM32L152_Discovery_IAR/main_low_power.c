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

/* ****************************************************************************
 * When configCREATE_LOW_POWER_DEMO is set to 1 in FreeRTOSConfig.h main() will
 * call main_low_power(), which is defined in this file.  main_low_power()
 * demonstrates FreeRTOS tick suppression being used to allow the MCU to be
 * placed into the Sleep, Low Power Sleep and Stop low power modes.  When
 * configCREATE_LOW_POWER_DEMO is set to 0 main will instead call main_full(),
 * which is a more comprehensive RTOS demonstration.
 * ****************************************************************************
 *
 * This application demonstrates the FreeRTOS tickless idle mode (tick
 * suppression) being used to allow the STM32L to enter various low power modes
 * during extended idle periods.  See
 * http://www.freertos.org/low-power-tickless-rtos.html for information on
 * tickless operation.
 *
 * Deeper low power modes have longer wake up periods that lighter low power
 * modes, and power is also used simply entering and especially exiting the low
 * power modes.  How the low power modes are used therefore requires careful
 * consideration to ensure power consumption is truly minimised and that the
 * embedded device meets its real time requirements.  This demo is configured to
 * select between four different modes depending on the anticipated idle period.
 * Note the time thresholds used to decide which low power mode to enter are
 * purely for convenience of demonstration and are not intended to represent
 * optimal values for any particular application.
 *
 * The STM32L specific part of the tickless operation is implemented in
 * STM32L_low_power_tick_management.c.
 *
 * The demo is configured to execute on the STM32L Discovery board.
 *
 * Functionality:
 *
 *  + Two tasks are created, an Rx task and a Tx task.  A queue is created to
 *	  pass a message from the Tx task to the Rx task.
 *
 *  + The Rx task blocks on a queue to wait for data, blipping an LED each time
 *    data is received (turning it on and then off again) before returning to
 *    block on the queue once more.
 *
 *  + The Tx task repeatedly blocks on an attempt to obtain a semaphore, and
 *	  unblocks if either the semaphore is received or its block time expires.
 *	  After leaving the blocked state the Tx task uses the queue to send a
 *	  value to the Rx task, which in turn causes the Rx task to exit the
 *	  Blocked state and blip the LED.  The rate at which the LED is seen to blip
 *	  is therefore dependent on the block time.
 *
 *  + The Tx task's block time is changed by the interrupt service routine that
 *	  executes when the USER button is pressed.  The low power mode entered
 *	  depends on the block time (as described in the Observed Behaviour section
 *	  below).  Four block times are used: short, medium, long and infinite.
 *
 * Observed behaviour:
 *
 * 1) The block time used by the Tx task is initialised to its 'short' value,
 * so when the Tx task blocks on the semaphore it times-out quickly, resulting
 * in the LED toggling rapidly.  The timeout period is less than the value of
 * configEXPECTED_IDLE_TIME_BEFORE_SLEEP (set in FreeRTOSConfig.h), so the
 * initial state does not suppress the tick interrupt or enter a low power mode.
 *
 * 2) When the button is pressed the block time used by the Tx task is increased
 * to its 'medium' value.  The longer block time results in a slowing of the
 * rate at which the LED toggles.  The time the Tx task spends in the blocked
 * state is now greater than configEXPECTED_IDLE_TIME_BEFORE_SLEEP, so the tick
 * is suppressed.  The MCU is placed into the 'Sleep' low power state while the
 * tick is suppressed.
 *
 * 3) When the button is pressed again the block time used by the Tx task is
 * increased to its 'long' value, so the rate at which the LED is observed to
 * blip gets even slow.  When the 'long' block time is used the MCU is placed
 * into its 'Low Power Sleep' low power state.
 *
 * 4) The next time the button is pressed the block time used by the Tx task is
 * set to infinite, so the Tx task does not time out when it attempts to obtain
 * the semaphore, and therefore the LED stops blipping completely.  Both tasks
 * are now blocked indefinitely and the MCU is placed into its 'Stop' low power
 * state.
 *
 * 5) Pressing the button one final time results in the semaphore being 'given'
 * to unblock the Tx task, the CPU clocks being returned to their pre-stop
 * state, and the block time being reset to its 'short' time.  The system is
 * then back to its initial condition with the LED blipping rapidly.
 *
 */

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* ST library functions. */
#include "stm32l1xx.h"
#include "discover_board.h"
#include "stm32l_discovery_lcd.h"

/* Priorities at which the Rx and Tx tasks are created. */
#define configQUEUE_RECEIVE_TASK_PRIORITY	( tskIDLE_PRIORITY + 1 )
#define	configQUEUE_SEND_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )

/* The number of items the queue can hold.  This is 1 as the Rx task will
remove items as they are added so the Tx task should always find the queue
empty. */
#define mainQUEUE_LENGTH					( 1 )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0 )

/* The value that is sent from the Tx task to the Rx task on the queue. */
#define mainQUEUED_VALUE					( 100UL )

/* The length of time the LED will remain on for. */
#define mainLED_TOGGLE_DELAY				( 10 / portTICK_PERIOD_MS )

/*-----------------------------------------------------------*/

/*
 * The Rx and Tx tasks as described at the top of this file.
 */
static void prvQueueReceiveTask( void *pvParameters );
static void prvQueueSendTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* The queue used to pass data from the Tx task to the Rx task. */
static QueueHandle_t xQueue = NULL;

/*-----------------------------------------------------------*/

/* Holds the block time used by the Tx task. */
TickType_t xSendBlockTime = ( 100UL / portTICK_PERIOD_MS );

/* The lower an upper limits of the block time.  An infinite block time is used
if xSendBlockTime is incremented past xMaxBlockTime. */
static const TickType_t xMaxBlockTime = ( 500L / portTICK_PERIOD_MS ), xMinBlockTime = ( 100L / portTICK_PERIOD_MS );

/* The semaphore on which the Tx task blocks. */
static SemaphoreHandle_t xTxSemaphore = NULL;

/*-----------------------------------------------------------*/

/* See the comments at the top of the file. */
void main_low_power( void )
{
	/* Create the semaphore as described at the top of this file. */
	xTxSemaphore = xSemaphoreCreateBinary();
	configASSERT( xTxSemaphore );

	/* Create the queue as described at the top of this file. */
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
		/* Enter the Blocked state to wait for the semaphore.  The task will
		leave the Blocked state if either the semaphore is received or
		xSendBlockTime ticks pass without the semaphore being received. */
		xSemaphoreTake( xTxSemaphore, xSendBlockTime );

		/* Send to the queue - causing the Tx task to flash its LED. */
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
			/* LED on... */
			GPIO_HIGH( LD_GPIO_PORT, LD_GREEN_GPIO_PIN );

			/* ... short delay ... */
			vTaskDelay( mainLED_TOGGLE_DELAY );

			/* ... LED off again. */
			GPIO_LOW( LD_GPIO_PORT, LD_GREEN_GPIO_PIN );
		}
	}
}
/*-----------------------------------------------------------*/

/* Handles interrupts generated by pressing the USER button. */
void EXTI0_IRQHandler(void)
{
static const TickType_t xIncrement = 200UL / portTICK_PERIOD_MS;

	/* If xSendBlockTime is already portMAX_DELAY then the Tx task was blocked
	indefinitely, and this interrupt is bringing the MCU out of STOP low power
	mode. */
	if( xSendBlockTime == portMAX_DELAY )
	{
		portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

		/* Unblock the Tx task. */
		xSemaphoreGiveFromISR( xTxSemaphore, &xHigherPriorityTaskWoken );

		/* Start over with the 'short' block time as described at the top of
		this file. */
		xSendBlockTime = xMinBlockTime;

		/* Request a yield if calling xSemaphoreGiveFromISR() caused a task to
		leave the Blocked state (which it will have done) and the task that left
		the Blocked state has a priority higher than the currently running task
		(which it will have). */
		portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
	}
	else
	{
		/* Increase the block time used by the Tx task, as described at the top
		of this file. */
		xSendBlockTime += xIncrement;

		/* If the block time has gone over the configured maximum then set it to
		an infinite block time to allow the MCU to go into its STOP low power
		mode. */
		if( xSendBlockTime > xMaxBlockTime )
		{
			xSendBlockTime = portMAX_DELAY;
		}
	}

	EXTI_ClearITPendingBit( EXTI_Line0 );
}
/*-----------------------------------------------------------*/

/* The configPOST_STOP_PROCESSING() macro is called when the MCU leaves its
STOP low power mode.  The macro is set in FreeRTOSConfig.h to call
vMainPostStopProcessing(). */
void vMainPostStopProcessing( void )
{
extern void SetSysClock( void );

	/* The STOP low power mode has been exited.  Reconfigure the system clocks
	ready for normally running again. */
	SetSysClock();
}
/*-----------------------------------------------------------*/
