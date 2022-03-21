/*
 * FreeRTOS V202112.00
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/*
 * See https://www.freertos.org/STM32H7_Dual_Core_AMP_RTOS_demo.html for usage
 * instructions, and the following blog post for a more detailed explanation
 * https://www.freertos.org/articles/001_simple_freertos_core_to_core_communication/simple_freertos_core_to_core_communication_AMP.html
 *
 * Behavior
 * --------
 *
 * This example stress tests a simple Asymmetric Multi Processing (AMP) core to
 * core communication mechanism implemented using FreeRTOS message buffers:
 * https://www.freertos.org/RTOS-stream-message-buffers.html  Message buffers
 * are used to pass an ASCII representation of an incrementing number (so "0",
 * followed by "1", followed by "2", etc.) from a single 'sending' task that
 * runs on the Arm Cortex-M7 core (the M7 core) to two "receiving" tasks
 * running on the Arm Cortex-M4 core (the M4 core).  There are two data message
 * buffers, one for each receiving task.  To distinguish between the receiving
 * tasks one is assigned the task number 0, and the other task number 1.
 *
 * The M7 task sits in a loop sending the ascii strings to each M4 task.  If a
 * receiving task receives the next expected value in the sequence it prints its
 * task number to the UART.  If a receiving task receives anything else, or its
 * attempt to receive data times out, then it hits an assert() that prints an
 * error message to the UART before stopping all further processing on the M4
 * core.  If the example is running correctly you will see lots of "0"s (from
 * the receiving task assigned task number 0) and "1"s (from the receiving task
 * assigned task number 1) streaming from the UART.  The time taken to output
 * characters from the UART is the only thing throttling the speed of the core
 * to core communication as it causes the message buffers to become full - which
 * would probably happen anyway as the M7 core is executing at twice the
 * frequency of the M4 core.
 *
 *
 * Implementation of sbSEND_COMPLETED()
 * ------------------------------------
 *
 * sbSEND_COMPLETED is a macro called by FreeRTOS after data has been sent to a
 * message buffer in case there was a task blocked on the message buffer waiting
 * for data to become available - in which case the waiting task would be
 * unblocked:  https://www.freertos.org/RTOS-message-buffer-example.html
 * However, the default sbSEND_COMPLETED implementation assumes the sending task
 * (or interrupt) and the receiving task are under the control of the same
 * instance of the FreeRTOS kernel and run on the same MCU core.  In this AMP
 * example the sending task and the receiving tasks are under the control of two
 * different instances of the FreeRTOS kernel, and run on different MCU cores,
 * so the default sbSEND_COMPLETED implementation won't work (each FreeRTOS
 * kernel instance only knowns about the tasks under its control).  AMP
 * scenarios therefore require the sbSEND_COMPLETED macro (and potentially the
 * sbRECEIVE_COMPLETED macro, see below) to be overridden, which is done by
 * simply providing your own implementation in the project's FreeRTOSConfig.h
 * file.  Note this example has a FreeRTOSConfig.h file used by the application
 * that runs on the M7 core and a separate FreeRTOSConfig.h file used by the
 * application that runs on the M4 core.  The implementation of sbSEND_COMPLETED
 * used by the M7 core simply triggers an interrupt in the M4 core.  The
 * interrupt's handler (the ISR that was triggered by the M7 core but executes
 * on the M4 core) must then do the job that would otherwise be done by the
 * default implementation of sbSEND_COMPLETE - namely unblock a task if the task
 * was waiting to receive data from the message buffer that now contains data.
 * There are two data message buffers though, so first ISR must determine which
 * of the two contains data.
 *
 * This demo only has two data message buffers, so it would be reasonable to
 * have the ISR simply query both to see which contained data, but that solution
 * would not scale if there are many message buffers, or if the number of
 * message buffers was unknown.  Therefore, to demonstrate a more scalable
 * solution, this example introduced a third message buffer - a 'control'
 * message buffer as opposed to a 'data' message buffer.  After the task on the
 * M7 core writes to a data message buffer it writes the handle of the message
 * buffer that contains data to the control message buffer.  The ISR running on
 * the M4 core then reads from the control message buffer to know which data
 * message buffer contains data.
 *
 * The above described scenario contains many implementation decisions.
 * Alternative methods of enabling the M4 core to know data message buffer
 * contains data include:
 *
 *  1) Using a different interrupt for each data message buffer.
 *  2) Passing all data from the M7 core to the M4 core through a single message
 *     buffer, along with additional data that tells the ISR running on the M4
 *     core which task to forward the data to.
 *
 *
 * Implementation of sbRECEIVE_COMPLETED()
 * ---------------------------------------
 *
 * sbRECEIVE_COMPLETED is the complement of sbSEND_COMPLETED.  It is a macro
 * called by FreeRTOS after data has been read from a message buffer in case
 * there was a task blocked on the message buffer waiting for space to become
 * available - in which case the waiting task would be unblocked so it can
 * complete its write to the buffer.
 *
 * In this example the M7 task writes to the message buffers faster than the M4
 * tasks read from them (in part because the M7 is running faster, and in part
 * because the M4 cores write to the UART), so the buffers become full, and the
 * M7 task enters the Blocked state to wait for space to become available.  As
 * with the sbSEND_COMPLETED macro, the default implementation of the
 * sbRECEIVE_COMPLETED macro only works if the sender and receiver are under the
 * control of the same instance of FreeRTOS and execute on the same core.
 * Therefore, just as the application that executes on the M7 core overrides
 * the default implementation of sbSEND_COMPLETED(), the application that runs
 * on the M4 core overrides the default implementation of sbRECEIVE_COMPLETED()
 * to likewise generate an interrupt in the M7 core - so sbRECEIVE_COMPLETED()
 * executes on the M4 core and generates an interrupt on the M7 core.  To keep
 * things simple the ISR that runs on the M7 core does not use a control
 * message buffer to know which data message buffer contains space, and instead
 * simply sends a notification to both data message buffers.  Note however that
 * this overly simplistic implementation is only acceptable because it is
 * known that there is only one sending task, and that task cannot be blocked on
 * both message buffers at the same time.  Also, sending the notification to the
 * data message buffer updates the receiving task's direct to task notification
 * state: https://www.freertos.org/RTOS-task-notifications.html which is only ok
 * because it is known the task is not using its notification state for any
 * other purpose.
 *
 */

/* Standard includes. */
#include "stdio.h"
#include "string.h"

/* STM32 includes. */
#include "stm32h7xx_hal.h"
#include "stm32h745i_discovery.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "message_buffer.h"

/* Demo includes. */
#include "MessageBufferLocations.h"

/*-----------------------------------------------------------*/

/* Seen as an infinite block by the ST HAL. */
#define mainHAL_MAX_TIMEOUT 	0xFFFFFFFFUL

/* When the cores boot they very crudely wait for each other in a non chip
specific way by waiting for the other core to start incrementing a shared
variable within an array.  mainINDEX_TO_TEST sets the index within the array to
the variable this core tests to see if it is incrementing, and
mainINDEX_TO_INCREMENT sets the index within the array to the variable this core
increments to indicate to the other core that it is at the sync point.  Note
this is not a foolproof method and it is better to use a hardware specific
solution, such as having one core boot the other core when it was ready, or
using some kind of shared semaphore or interrupt. */
#define mainINDEX_TO_TEST		1
#define mainINDEX_TO_INCREMENT	0

/*-----------------------------------------------------------*/

/*
 * Implements the tasks that receive messages from the M7 core.
 */
static void prvM4CoreTasks( void *pvParameters );

/*
 * The interrupt triggered by the M7 core when there is data available in the
 * message buffer used for core to core communication.
 */
void HAL_GPIO_EXTI_Callback( uint16_t GPIO_Pin );

/*
 * Just waits to see a variable being incremented by the M7 core to know when
 * the M7 has created the message buffers used for core to core communication.
 */
static void prvWaitForOtherCoreToStart( uint32_t ulIndexToTest, uint32_t ulIndexToIncrement );

/*
 * Configures the hardware ready to run this demo.
 */
static void prvSetupHardware( void );

/*-----------------------------------------------------------*/

/* Handle to the UART used to output strings. */
static UART_HandleTypeDef xUARTHandle = { 0 };

/*-----------------------------------------------------------*/

int main( void )
{
static const uint8_t pucBootMessage[] = "\r\nM4 started and waiting for the M7 to run.\r\n";
static const uint8_t pucCreatingTasksMessage[] = "M4 core proceeding to create demo tasks.\r\n";
uint32_t x;

	/*** See the comments at the top of this page ***/


	/* Prep the hardware to run this demo. */
	prvSetupHardware();

	/* The M4 core task prints its status out at various places so you know what
	it is doing when debugging the M7 core.  This messages is just to indicate
	it has booted and is about to wait for the M7 core.  If the M7 is already
	running then reset the hardware so both cores start at once. */
	HAL_UART_Transmit( &xUARTHandle, ( uint8_t * ) pucBootMessage, sizeof( pucBootMessage ), mainHAL_MAX_TIMEOUT );
	prvWaitForOtherCoreToStart( mainINDEX_TO_TEST, mainINDEX_TO_INCREMENT );

	/* By this point the M7 should have initialized the message buffers used to
	send data from the M7 to the M4 core.  The message buffers are statically
	allocated at a known location so both cores know where they are.  See
	MessageBufferLocations.h. */
	configASSERT( ( xControlMessageBuffer != NULL ) && ( xDataMessageBuffers[ 0 ] != NULL ) && ( xDataMessageBuffers[ 1 ] != NULL ) );

	/* Everything seems as expected - print a message to say the M4 is about to
	create the tasks that receive data from the M7 core. */
	HAL_UART_Transmit( &xUARTHandle, ( uint8_t * ) pucCreatingTasksMessage, sizeof( pucCreatingTasksMessage ), mainHAL_MAX_TIMEOUT );

	for( x = 0; x < mbaNUMBER_OF_CORE_2_TASKS; x++ )
	{
		/* Pass the loop counter into the created task using the task's
		parameter.  The task then uses the value as an index into the
		xDataMessageBuffers arrays. */
		xTaskCreate( prvM4CoreTasks,			/* Function that implements the task. */
					"AMPM4Core",					/* Task name, for debugging only. */
					configMINIMAL_STACK_SIZE,	/* Size of stack to allocate for this task - in words. */
					( void * ) x,				/* Task parameter. */
					tskIDLE_PRIORITY + 1,		/* Task priority. */
					NULL );						/* Task handle.  Not used in this case. */
	}

	/* Start scheduler */
	vTaskStartScheduler();

	/* Will not get here if the scheduler starts successfully.  If you do end up
	here then there wasn't enough heap memory available to start either the idle
	task or the timer/daemon task.  https://www.freertos.org/a00111.html */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvM4CoreTasks( void *pvParameters )
{
static const uint8_t pucTaskStartedMessage[] = "M4 task started.\r\n";
BaseType_t xTaskNumber;
size_t xReceivedBytes;
uint32_t ulNextValue = 0;
char cExpectedString[ 15 ];
char cReceivedString[ 15 ];
char cMessage;
const TickType_t xShortBlockTime = pdMS_TO_TICKS( 200 );

	/* This task is created more than once so the task's parameter is used to
	pass in a task number, which is then used as an index into the message
	buffer array. */
	xTaskNumber = ( BaseType_t ) pvParameters;
	configASSERT( xTaskNumber < mbaNUMBER_OF_CORE_2_TASKS );

	vTaskSuspendAll();
	{
		/* Message transmitted to indicate the task has started. */
		HAL_UART_Transmit( &xUARTHandle, ( uint8_t * ) pucTaskStartedMessage, sizeof( pucTaskStartedMessage ), mainHAL_MAX_TIMEOUT );
	}
	xTaskResumeAll();

	/* The tasks print out a letter to indicate that the expected message was
	received from the other core. */
	if( xTaskNumber == 0 )
	{
		cMessage = '0';
	}
	else
	{
		cMessage = '1';
	}

	for( ;; )
	{
		/* The M7 core creates and sends to this core an ascii string of an
		incrementing number.  Create the string that is expected to be received
		this time round the loop. */
		sprintf( cExpectedString, "%lu", ( unsigned long ) ulNextValue );

		/* Wait to receive the next message from core 1. */
		memset( cReceivedString, 0x00, sizeof( cReceivedString ) );
		xReceivedBytes = xMessageBufferReceive( /* Handle of message buffer. */
												xDataMessageBuffers[ xTaskNumber ],
												/* Buffer into which received data is placed. */
												cReceivedString,
												/* Size of the receive buffer. */
												sizeof( cReceivedString ),
												/* Time to wait for data to arrive. */
												xShortBlockTime );

		/* Check the number of bytes received was as expected. */
		configASSERT( xReceivedBytes == strlen( cExpectedString ) );

		/* If the received string matches that expected then output the task
		number to give visible indication that the task is still running. */
		if( strcmp( cReceivedString, cExpectedString ) == 0 )
		{
			/* Also print out the task number to give a visual indication that
			the M4 core is receiving the expected data. */
			vTaskSuspendAll();
			{
				HAL_UART_Transmit( &xUARTHandle, ( uint8_t * ) &cMessage, sizeof( cMessage ), mainHAL_MAX_TIMEOUT );
			}
			xTaskResumeAll();
		}

		/* Expect the next string in sequence the next time around. */
		ulNextValue++;
	}
}
/*-----------------------------------------------------------*/

void vGenerateM4ToM7Interrupt( void * xUpdatedMessageBuffer )
{
	/* Called by the implementation of sbRECEIVE_COMPLETED() in FreeRTOSConfig.h.
	See the comments at the top of this file.  Write the handle of the data
	message buffer to which data was written to the control message buffer. */

	/* Generate interrupt in the M7 core. */
	HAL_EXTI_D2_EventInputConfig( EXTI_LINE1, EXTI_MODE_IT, DISABLE );
	HAL_EXTI_D1_EventInputConfig( EXTI_LINE1, EXTI_MODE_IT, ENABLE );
	HAL_EXTI_GenerateSWInterrupt( EXTI_LINE1 );
}
/*-----------------------------------------------------------*/

void HAL_GPIO_EXTI_Callback( uint16_t GPIO_Pin )
{
MessageBufferHandle_t xUpdatedMessageBuffer;
BaseType_t xHigherPriorityTaskWoken = pdFALSE;

	/* Avoid compiler warnings about unused parameters. */
	( void ) GPIO_Pin;

	/* Clear interrupt. */
	HAL_EXTI_D2_ClearFlag( EXTI_LINE0 );

	configASSERT( ( xControlMessageBuffer != NULL ) && ( xDataMessageBuffers[ 0 ] != NULL ) && ( xDataMessageBuffers[ 1 ] != NULL ) );

	/* In this example there are mbaNUMBER_OF_CORE_2_TASKS receiving tasks that
	run on the M4 core.  It would be possible for the M7 core to use a single
	message buffer to send to both tasks, but that would require additional data
	to be sent to the message buffer - namely an identifier to indicate which
	receiving task a message was intended for along with some arbitration in the
	ISR.  As an alternative, this example uses one message buffer per receiving
	task and a control message buffer.  The M7 core sends data to a receiving
	task using that task's dedicated message buffer, then sends the handle of
	the message buffer that it just sent data to to the control task.  This
	interrupt service routine receives the handle from the control task then
	uses the handle to signal the message buffer that contains the data.

	Receive the handle of the message buffer that contains data from the
	control message buffer. */
	while( xMessageBufferReceiveFromISR( 	xControlMessageBuffer,
											&xUpdatedMessageBuffer,
											sizeof( xUpdatedMessageBuffer ),
											&xHigherPriorityTaskWoken ) == sizeof( xUpdatedMessageBuffer ) )
	{
		/* Call the API function that sends a notification to any task that is
		blocked on the xUpdatedMessageBuffer message buffer waiting for data to
		arrive. */
		xMessageBufferSendCompletedFromISR( xUpdatedMessageBuffer, &xHigherPriorityTaskWoken );
	}

	/* Normal FreeRTOS "yield from interrupt" semantics, where
	xHigherPriorityTaskWoken is initialised to pdFALSE and will then get set to
	pdTRUE if the interrupt unblocks a task that has a priority above that of
	the currently executing task. */
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static void prvWaitForOtherCoreToStart( uint32_t ulIndexToTest, uint32_t ulIndexToIncrement )
{
volatile uint32_t ulInitialCount = ulStartSyncCounters[ ulIndexToTest ];

	/* When the cores boot they very crudely wait for each other in a non chip
	specific way by waiting for the other core to start incrementing a shared
	variable within an array.  mainINDEX_TO_TEST sets the index within the array
	to the variable this core tests to see if it is incrementing, and
	mainINDEX_TO_INCREMENT sets the index within the array to the variable this
	core increments to indicate to the other core that it is at the sync point.
	Note this is not a foolproof method and it is better to use a hardware
	specific solution, such as having one core boot the other core when it was
	ready, or using some kind of shared semaphore or interrupt. */

	for( ;; )
	{
		/* Indicate to the M7 core that this core is at the synchronisation
		point. */
		ulStartSyncCounters[ ulIndexToIncrement ]++;

		/* Has the counter incremented by the other core changed? */
		if( ulStartSyncCounters[ ulIndexToTest ] != ulInitialCount )
		{
			break;
		}
	}

	/* One more increment before exiting to avoid race. */
	ulStartSyncCounters[ ulIndexToIncrement ]++;
}
/*-----------------------------------------------------------*/

void vAssertCalled( const char *pcFile, const uint32_t ulLine )
{
char pcLine[ 10 ];
const uint8_t pucM4AssertFile[] = "M4 Assert hit in file ";
const uint8_t pucM4AssertLine[] = "on line number ";

	/* Assert disables interrupts so no other code can run, prints out the
	location of the offending assert(), then loops doing nothing waiting for
	the user to inspect or reset. */
	taskDISABLE_INTERRUPTS();
	HAL_UART_Transmit( &xUARTHandle, ( uint8_t * ) pucM4AssertFile, sizeof( pucM4AssertFile ), mainHAL_MAX_TIMEOUT );
	HAL_UART_Transmit( &xUARTHandle, ( uint8_t * ) pcFile, strlen( pcFile ), mainHAL_MAX_TIMEOUT );
	HAL_UART_Transmit( &xUARTHandle, ( uint8_t * ) pucM4AssertLine, sizeof( pucM4AssertLine ), mainHAL_MAX_TIMEOUT );
	sprintf( pcLine, "%u\r\n", ulLine );
	HAL_UART_Transmit( &xUARTHandle, ( uint8_t * ) pcLine, strlen( pcLine ), mainHAL_MAX_TIMEOUT );
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Prevent the HAL's initialisation of SysTick actually starting the systick
	interrupt as the kernel has not started yet. */
	taskDISABLE_INTERRUPTS();
	HAL_Init();
	BSP_LED_Init( LED2 );

	/* This core uses the UART, so initialise it. */
	xUARTHandle.Instance = USART3;
	xUARTHandle.Init.BaudRate = 115200;
	xUARTHandle.Init.WordLength = UART_WORDLENGTH_8B;
	xUARTHandle.Init.StopBits = UART_STOPBITS_1;
	xUARTHandle.Init.Parity = UART_PARITY_NONE;
	xUARTHandle.Init.HwFlowCtl = UART_HWCONTROL_NONE;
	xUARTHandle.Init.Mode = UART_MODE_TX_RX;
	xUARTHandle.Init.ClockPrescaler = UART_PRESCALER_DIV1;
	xUARTHandle.Init.OneBitSampling = UART_ONE_BIT_SAMPLE_DISABLE;
	xUARTHandle.Init.OverSampling = UART_OVERSAMPLING_16;
	HAL_UART_Init( &xUARTHandle );
	HAL_UARTEx_SetRxFifoThreshold( &xUARTHandle, UART_RXFIFO_THRESHOLD_1_4 );
	HAL_UARTEx_EnableFifoMode( &xUARTHandle );

	/* AIEC Common configuration: make CPU1 and CPU2 SWI line1 sensitive to
	rising edge. */
	HAL_EXTI_EdgeConfig( EXTI_LINE1, EXTI_RISING_EDGE );

	/* Interrupt used for M7 to M4 notifications. */
	HAL_NVIC_SetPriority( EXTI0_IRQn, 0xFU, 0U );
	HAL_NVIC_EnableIRQ( EXTI0_IRQn );
}
