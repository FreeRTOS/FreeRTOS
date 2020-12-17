/*
 * FreeRTOS V202012.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/******************************************************************************
 * NOTE 1:  This project provides two demo applications.  A simple blinky style
 * project, and a more comprehensive test and demo application.  The
 * configCREATE_SIMPLE_TICKLESS_DEMO setting in FreeRTOSConfig.h is used to
 * select between the two.  See the notes on using
 * configCREATE_SIMPLE_TICKLESS_DEMO in main.c.  This file implements the
 * simply blinky style version.
 *
 * The blinky demo uses FreeRTOS's tickless idle mode to reduce power 
 * consumption.  See the notes on the web page below regarding the difference
 * in power saving that can be achieved between using the generic tickless
 * implementation (as used by the blinky demo) and a tickless implementation
 * that is tailored specifically to the MSP432.
 * 
 * See http://www.FreeRTOS.org/TI_MSP432_Free_RTOS_Demo.html for instructions.
 *
 * NOTE 2:  This file only contains the source code that is specific to the
 * basic demo.  Generic functions, such FreeRTOS hook functions, and functions
 * required to configure the hardware, are defined in main.c.
 ******************************************************************************
 *
 * main_blinky() creates one queue, and two tasks.  It then starts the
 * scheduler.
 *
 * The Queue Send Task:
 * The queue send task is implemented by the prvQueueSendTask() function in
 * this file.  prvQueueSendTask() sits in a loop that causes it to repeatedly
 * block for 200 milliseconds, before sending the value 100 to the queue that
 * was created within main_blinky().  Once the value is sent, the task loops
 * back around to block for another 200 milliseconds.
 *
 * The Queue Receive Task:
 * The queue receive task is implemented by the prvQueueReceiveTask() function
 * in this file.  prvQueueReceiveTask() sits in a loop where it repeatedly
 * blocks on attempts to read data from the queue that was created within
 * main_blinky().  When data is received, the task checks the value of the
 * data, and if the value equals the expected 100, toggles the LED.  The 'block
 * time' parameter passed to the queue receive function specifies that the
 * task should be held in the Blocked state indefinitely to wait for data to
 * be available on the queue.  The queue receive task will only leave the
 * Blocked state when the queue send task writes to the queue.  As the queue
 * send task writes to the queue every 200 milliseconds, the queue receive
 * task leaves the Blocked state every 200 milliseconds, and therefore toggles
 * the LED every 200 milliseconds.
 */

/* Standard includes. */
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* TI includes. */
#include "gpio.h"

/* Priorities at which the tasks are created. */
#define mainQUEUE_RECEIVE_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define	mainQUEUE_SEND_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )

/* The rate at which data is sent to the queue.  The 200ms value is converted
to ticks using the portTICK_PERIOD_MS constant. */
#define mainQUEUE_SEND_FREQUENCY_MS			( pdMS_TO_TICKS( 1000UL ) )

/* The number of items the queue can hold.  This is 1 as the receive task
will remove items as they are added, meaning the send task should always find
the queue empty. */
#define mainQUEUE_LENGTH					( 1 )

/* Values passed to the two tasks just to check the task parameter
functionality. */
#define mainQUEUE_SEND_PARAMETER			( 0x1111UL )
#define mainQUEUE_RECEIVE_PARAMETER			( 0x22UL )

/*-----------------------------------------------------------*/

/*
 * The tasks as described in the comments at the top of this file.
 */
static void prvQueueReceiveTask( void *pvParameters );
static void prvQueueSendTask( void *pvParameters );

/*
 * Called by main() to create the simply blinky style application if
 * configCREATE_SIMPLE_TICKLESS_DEMO is set to 1.
 */
void main_blinky( void );

/*
 * The full demo configures the clocks for maximum frequency, wheras this blinky
 * demo uses a slower clock as it also uses low power features.
 */
static void prvConfigureClocks( void );

/* 
 * Configure a button to generate interrupts (for test purposes).  This is done
 * to test waking on an interrupt other than the systick interrupt in tickless
 * idle mode.
 */
static void prvConfigureButton( void );

/*-----------------------------------------------------------*/

/* The queue used by both tasks. */
static QueueHandle_t xQueue = NULL;

/*-----------------------------------------------------------*/

void main_blinky( void )
{
	/* See http://www.FreeRTOS.org/TI_MSP432_Free_RTOS_Demo.html for 
	instructions and notes regarding the difference in power saving that can be 
	achieved between using the generic tickless RTOS implementation (as used by 
	the blinky demo) and a tickless RTOS implementation that is tailored 
	specifically to the MSP432. */

	/* The full demo configures the clocks for maximum frequency, wheras this
	blinky demo uses a slower clock as it also uses low power features. */
	prvConfigureClocks();
	
	/* Configure a button to generate interrupts (for test purposes). */
	prvConfigureButton();

	/* Create the queue. */
	xQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( uint32_t ) );

	if( xQueue != NULL )
	{
		/* Start the two tasks as described in the comments at the top of this
		file. */
		xTaskCreate( prvQueueReceiveTask,					/* The function that implements the task. */
					"Rx", 									/* The text name assigned to the task - for debug only as it is not used by the kernel. */
					configMINIMAL_STACK_SIZE, 				/* The size of the stack to allocate to the task. */
					( void * ) mainQUEUE_RECEIVE_PARAMETER, /* The parameter passed to the task - just to check the functionality. */
					mainQUEUE_RECEIVE_TASK_PRIORITY, 		/* The priority assigned to the task. */
					NULL );									/* The task handle is not required, so NULL is passed. */

		xTaskCreate( prvQueueSendTask, "TX", configMINIMAL_STACK_SIZE, ( void * ) mainQUEUE_SEND_PARAMETER, mainQUEUE_SEND_TASK_PRIORITY, NULL );

		/* Start the tasks and timer running. */
		vTaskStartScheduler();
	}

	/* If all is well, the scheduler will now be running, and the following
	line will never be reached.  If the following line does execute, then
	there was insufficient FreeRTOS heap memory available for the idle and/or
	timer tasks	to be created.  See the memory management section on the
	FreeRTOS web site for more details. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvQueueSendTask( void *pvParameters )
{
TickType_t xNextWakeTime;
const unsigned long ulValueToSend = 100UL;

	/* Check the task parameter is as expected. */
	configASSERT( ( ( unsigned long ) pvParameters ) == mainQUEUE_SEND_PARAMETER );

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
		toggle the LED.  0 is used as the block time so the sending operation
		will not block - it shouldn't need to block as the queue should always
		be empty at this point in the code. */
		xQueueSend( xQueue, &ulValueToSend, 0U );
	}
}
/*-----------------------------------------------------------*/

static void prvQueueReceiveTask( void *pvParameters )
{
unsigned long ulReceivedValue;
static const TickType_t xShortBlock = pdMS_TO_TICKS( 50 );

	/* Check the task parameter is as expected. */
	configASSERT( ( ( unsigned long ) pvParameters ) == mainQUEUE_RECEIVE_PARAMETER );

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
			/* Blip the LED for a short while so as not to use too much
			power. */
			configTOGGLE_LED();
			vTaskDelay( xShortBlock );
			configTOGGLE_LED();
			ulReceivedValue = 0U;
		}
	}
}
/*-----------------------------------------------------------*/

static void prvConfigureClocks( void )
{
	/* The full demo configures the clocks for maximum frequency, wheras this
	blinky demo uses a slower clock as it also uses low power features.

	From the datasheet:  For AM_LDO_VCORE0 and AM_DCDC_VCORE0 modes, the maximum
	CPU operating frequency is 24 MHz and maximum input clock frequency for
	peripherals is 12 MHz. */
	FlashCtl_setWaitState( FLASH_BANK0, 2 );
	FlashCtl_setWaitState( FLASH_BANK1, 2 );
	CS_setDCOCenteredFrequency( CS_DCO_FREQUENCY_3 );
	CS_initClockSignal( CS_HSMCLK, CS_DCOCLK_SELECT, CS_CLOCK_DIVIDER_1 );
	CS_initClockSignal( CS_SMCLK, CS_DCOCLK_SELECT, CS_CLOCK_DIVIDER_1 );
	CS_initClockSignal( CS_MCLK, CS_DCOCLK_SELECT, CS_CLOCK_DIVIDER_1 );
	CS_initClockSignal( CS_ACLK, CS_REFOCLK_SELECT, CS_CLOCK_DIVIDER_1 );

	/* The lower frequency allows the use of CVORE level 0. */
	PCM_setCoreVoltageLevel( PCM_VCORE0 );
}
/*-----------------------------------------------------------*/

static void prvConfigureButton( void )
{
volatile uint8_t ucPin;

	/* Configure button S1 to generate interrupts.  This is done to test the
	code path were low power mode is exited for a reason other than a tick
	interrupt. */
	GPIO_setAsInputPinWithPullUpResistor( GPIO_PORT_P1, GPIO_PIN1 );
	GPIO_enableInterrupt( GPIO_PORT_P1, GPIO_PIN1 );
	Interrupt_enableInterrupt( INT_PORT1 );
}
/*-----------------------------------------------------------*/

void PORT1_IRQHandler( void )
{
static volatile uint32_t ux = 0;
	
	/* This is the handler for interrupt generated by the button.  The 
	interrupt is only used to bring the MCU out of low power mode.  It
	doesn't perform any other function.  The ux increment is just to
	have something to set breakpoints on and check the interrupt is
	executing. */
	ux++;
	
	/* Clear the interrupt. */
	( void ) P1->IV;
}
/*-----------------------------------------------------------*/

void vPreSleepProcessing( uint32_t ulExpectedIdleTime )
{
}
/*-----------------------------------------------------------*/

#if( configCREATE_SIMPLE_TICKLESS_DEMO == 1 )

	void vApplicationTickHook( void )
	{
		/* This function will be called by each tick interrupt if
		configUSE_TICK_HOOK is set to 1 in FreeRTOSConfig.h.  User code can be
		added here, but the tick hook is called from an interrupt context, so
		code must not attempt to block, and only the interrupt safe FreeRTOS API
		functions can be used (those that end in FromISR()). */

		/* Only the full demo uses the tick hook so there is no code is
		executed here. */
	}

#endif

