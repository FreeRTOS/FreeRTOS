/*
 * FreeRTOS Kernel V10.2.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * See https://www.freertos.org/STM32H7_Dual_Core_AMP_RTOS_demo.html for usage
 * instructions (TBD, not available at the time of writing).
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
 * the default implementation of sbSEND_SOMPLETED(), the application that runs
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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "message_buffer.h"
#include "MessageBufferLocations.h"

/* ST includes. */
#include "stm32h7xx_hal.h"
#include "stm32h745i_discovery.h"

/* When the cores boot they very crudely wait for each other in a non chip
specific way by waiting for the other core to start incrementing a shared
variable within an array.  mainINDEX_TO_TEST sets the index within the array to
the variable this core tests to see if it is incrementing, and
mainINDEX_TO_INCREMENT sets the index within the array to the variable this core
increments to indicate to the other core that it is at the sync point.  Note
this is not a foolproof method and it is better to use a hardware specific
solution, such as having one core boot the other core when it was ready, or
using some kind of shared semaphore or interrupt. */
#define mainINDEX_TO_TEST		0
#define mainINDEX_TO_INCREMENT	1

/*-----------------------------------------------------------*/

/*
 * Implements the task that sends messages to the M7 core.
 */
static void prvM7CoreTasks( void *pvParameters );

/*
 * configSUPPORT_STATIC_ALLOCATION is set to 1, requiring this callback to
 * provide statically allocated data for use by the idle task, which is a task
 * created by the scheduler when it starts.
 */
void vApplicationGetIdleTaskMemory( StaticTask_t **ppxIdleTaskTCBBuffer, uint32_t **ppxIdleTaskStackBuffer, uint32_t *pulIdleTaskStackSize );

/*
 * Just waits to see a variable being incremented by the M4 core to know when
 * the M4 has created the message buffers used for core to core communication.
 */
static void prvWaitForOtherCoreToStart( uint32_t ulIndexToTest, uint32_t ulIndexToIncrement );

/*
 * Setup the hardware ready to run this demo.
 */
static void prvSetupHardware( void );

/*-----------------------------------------------------------*/

static TaskHandle_t xM7AMPTask = NULL;

int main( void )
{
BaseType_t x;

	/*** See the comments at the top of this page ***/

	prvSetupHardware();

	/* Create the control and data message buffers, as described at the top of
	this file.  The message buffers are statically allocated at a known location
	as both cores need to know where they are.  See MessageBufferLocations.h. */
	xControlMessageBuffer = xMessageBufferCreateStatic( /* The buffer size in bytes. */
														mbaCONTROL_MESSAGE_BUFFER_SIZE,
														/* Statically allocated buffer storage area. */
														ucControlBufferStorage,
														/* Message buffer handle. */
														&xControlMessageBufferStruct );
	for( x = 0; x < mbaNUMBER_OF_CORE_2_TASKS; x++ )
	{
		xDataMessageBuffers[ x ] = xMessageBufferCreateStatic( mbaTASK_MESSAGE_BUFFER_SIZE,
															   &( ucDataBufferStorage[ x ][ 0 ] ),
															   &( xDataMessageBufferStructs[ x ] ) );
	}

	/* The message buffers have been initialised so it is safe for both cores to
	synchronise their startup. */
	prvWaitForOtherCoreToStart( mainINDEX_TO_TEST, mainINDEX_TO_INCREMENT );

	/* Start the task that executes on the M7 core. */
	xTaskCreate( prvM7CoreTasks, 			/* Function that implements the task. */
				 "AMPM7Core", 				/* Task name, for debugging only. */
				 configMINIMAL_STACK_SIZE,  /* Size of stack (in words) to allocate for this task. */
				 NULL, 						/* Task parameter, not used in this case. */
				 tskIDLE_PRIORITY, 			/* Task priority. */
				 &xM7AMPTask );				/* Task handle, used to unblock task from interrupt. */

	/* Start scheduler */
	vTaskStartScheduler();

	/* Will not get here if the scheduler starts successfully.  If you do end up
	here then there wasn't enough heap memory available to start either the idle
	task or the timer/daemon task.  https://www.freertos.org/a00111.html */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvM7CoreTasks( void *pvParameters )
{
BaseType_t x;
uint32_t ulNextValue = 0;
const TickType_t xDelay = pdMS_TO_TICKS( 25 );
char cString[ 15 ];
size_t xStringLength;

	/* Remove warning about unused parameters. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Create the next string to send.  The value is incremented on each
		loop iteration, and the length of the string changes as the number of
		digits in the value increases. */
		sprintf( cString, "%lu", ( unsigned long ) ulNextValue );
		xStringLength = strlen( cString );

		/* This task runs on the M7 core, use the message buffers to send the
		strings to the tasks running on the M4 core.  This will result in
		sbSEND_COMPLETED() being executed, which in turn will write the handle
		of the message buffer written to into xControlMessageBuffer then
		generate an interrupt in M4 core. */
		for( x = 0; x < mbaNUMBER_OF_CORE_2_TASKS; x++ )
		{
			while( xMessageBufferSend( 	xDataMessageBuffers[ x ],
									  	( void * ) cString,
										xStringLength,
										portMAX_DELAY ) != xStringLength );

			/* Delay before repeating */
//			vTaskDelay( xDelay );
		}

		ulNextValue++;
	}
}
/*-----------------------------------------------------------*/

void vGenerateM7ToM4Interrupt( void * xUpdatedMessageBuffer )
{
MessageBufferHandle_t xUpdatedBuffer = ( MessageBufferHandle_t ) xUpdatedMessageBuffer;

	/* Called by the implementation of sbSEND_COMPLETED() in FreeRTOSConfig.h.
	See the comments at the top of this file.  Write the handle of the data
	message buffer to which data was written to the control message buffer. */
	if( xUpdatedBuffer != xControlMessageBuffer )
	{
		while( xMessageBufferSend( xControlMessageBuffer, &xUpdatedBuffer, sizeof( xUpdatedBuffer ), mbaDONT_BLOCK ) != sizeof( xUpdatedBuffer ) )
		{
			/* Nothing to do here.  Note it is very bad to loop in an interrupt
			service routine.  If a loop is really required then defer the
			routine to a task. */
		}

		/* Generate interrupt in the M4 core. */
		HAL_EXTI_D1_EventInputConfig( EXTI_LINE0, EXTI_MODE_IT, DISABLE );
		HAL_EXTI_D2_EventInputConfig( EXTI_LINE0, EXTI_MODE_IT, ENABLE );
		HAL_EXTI_GenerateSWInterrupt( EXTI_LINE0 );
	}
}
/*-----------------------------------------------------------*/

void vApplicationGetIdleTaskMemory( StaticTask_t **ppxIdleTaskTCBBuffer, uint32_t **ppxIdleTaskStackBuffer, uint32_t *pulIdleTaskStackSize )
{
/* If the buffers to be provided to the Idle task are declared inside this
function then they must be declared static - otherwise they will be allocated on
the stack and so not exists after this function exits. */
static StaticTask_t xIdleTaskTCB;
static uint32_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];

	/* configUSE_STATIC_ALLOCATION is set to 1, so the application must provide
	an implementation of vApplicationGetIdleTaskMemory() to provide the memory
	that is used by the Idle task.
	https://www.freertos.org/a00110.html#configSUPPORT_STATIC_ALLOCATION */

	/* Pass out a pointer to the StaticTask_t structure in which the Idle task's
	state will be stored. */
	*ppxIdleTaskTCBBuffer = &xIdleTaskTCB;

	/* Pass out the array that will be used as the Idle task's stack. */
	*ppxIdleTaskStackBuffer = uxIdleTaskStack;

	/* Pass out the size of the array pointed to by *ppxIdleTaskStackBuffer.
	Note that, as the array is necessarily of type StackType_t,
	configMINIMAL_STACK_SIZE is specified in words, not bytes. */
	*pulIdleTaskStackSize = configMINIMAL_STACK_SIZE;
}
/*-----------------------------------------------------------*/

static void prvWaitForOtherCoreToStart( uint32_t ulIndexToTest, uint32_t ulIndexToIncrement )
{
volatile uint32_t ulInitialCount = ulStartSyncCounters[ ulIndexToTest ], x;
const uint32_t ulCrudeLoopDelay = 0xfffffUL;

	/* When the cores boot they very crudely wait for each other in a non chip
	specific way by waiting for the other core to start incrementing a shared
	variable within an array.  mainINDEX_TO_TEST sets the index within the array
	to the variable this core tests to see if it is incrementing, and
	mainINDEX_TO_INCREMENT sets the index within the array to the variable this
	core increments to indicate to the other core that it is at the sync point.
	Note this is not a foolproof method and it is better to use a hardware
	specific solution, such as having one core boot the other core when it was
	ready, or using some kind of shared semaphore or interrupt. */

	/* Wait for the other core to reach the synchronisation point. */
	while( ulStartSyncCounters[ ulIndexToTest ] == ulInitialCount );
	ulInitialCount = ulStartSyncCounters[ ulIndexToTest ];

	for( ;; )
	{
		ulStartSyncCounters[ ulIndexToIncrement ]++;
		if( ulStartSyncCounters[ ulIndexToTest ] != ulInitialCount )
		{
			ulStartSyncCounters[ ulIndexToIncrement ]++;
			break;
		}

		/* Unlike the M4 core, this core does not have direct access to the UART,
		so simply toggle an LED to show its status. */
		for( x = 0; x < ulCrudeLoopDelay; x++ ) __asm volatile( "NOP" );
		BSP_LED_Off( LED2 );
		for( x = 0; x < ulCrudeLoopDelay; x++ ) __asm volatile( "NOP" );
		BSP_LED_On( LED2 );
	}
}
/*-----------------------------------------------------------*/

void HAL_GPIO_EXTI_Callback( uint16_t GPIO_Pin )
{
BaseType_t xHigherPriorityTaskWoken = pdFALSE;
uint32_t x;

	configASSERT( xM7AMPTask );

	HAL_EXTI_D1_ClearFlag( EXTI_LINE1 );

	/* Task can't be blocked on both so just send the notification to both. */
	for( x = 0; x < mbaNUMBER_OF_CORE_2_TASKS; x++ )
	{
		xMessageBufferReceiveCompletedFromISR( xDataMessageBuffers[ x ], &xHigherPriorityTaskWoken );
	}

	/* Normal FreeRTOS "yield from interrupt" semantics, where
	xHigherPriorityTaskWoken is initialzed to pdFALSE and will then get set to
	pdTRUE if the interrupt unblocks a task that has a priority above that of
	the currently executing task. */
	portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
MPU_Region_InitTypeDef MPU_InitStruct;
RCC_ClkInitTypeDef RCC_ClkInitStruct;
RCC_OscInitTypeDef RCC_OscInitStruct;

	/* Configure the MPU attributes as Not Cachable for Internal D3SRAM.  The
	Base Address is 0x38000000 (D3_SRAM_BASE), and the size is 64K. */
	HAL_MPU_Disable();
	MPU_InitStruct.Enable = MPU_REGION_ENABLE;
	MPU_InitStruct.BaseAddress = D3_SRAM_BASE;
	MPU_InitStruct.Size = MPU_REGION_SIZE_64KB;
	MPU_InitStruct.AccessPermission = MPU_REGION_FULL_ACCESS;
	MPU_InitStruct.IsBufferable = MPU_ACCESS_NOT_BUFFERABLE;
	MPU_InitStruct.IsCacheable = MPU_ACCESS_NOT_CACHEABLE;
	MPU_InitStruct.IsShareable = MPU_ACCESS_SHAREABLE;
	MPU_InitStruct.Number = MPU_REGION_NUMBER0;
	MPU_InitStruct.TypeExtField = MPU_TEX_LEVEL0;
	MPU_InitStruct.SubRegionDisable = 0x00;
	MPU_InitStruct.DisableExec = MPU_INSTRUCTION_ACCESS_ENABLE;
	HAL_MPU_ConfigRegion(&MPU_InitStruct);
	HAL_MPU_Enable(MPU_PRIVILEGED_DEFAULT);

	/* Enable I-Cache */
	SCB_EnableICache();

	/* Enable D-Cache */
	SCB_EnableDCache();

	HAL_Init();
	BSP_LED_Init(LED1);


	/*
	System Clock Configuration:
		System Clock source    = PLL (HSE)
		SYSCLK(Hz)             = 400000000 (Cortex-M7 CPU Clock)
		HCLK(Hz)               = 200000000 (Cortex-M4 CPU, Bus matrix Clocks)
		AHB Prescaler          = 2
		D1 APB3 Prescaler      = 2 (APB3 Clock  100MHz)
		D2 APB1 Prescaler      = 2 (APB1 Clock  100MHz)
		D2 APB2 Prescaler      = 2 (APB2 Clock  100MHz)
		D3 APB4 Prescaler      = 2 (APB4 Clock  100MHz)
		HSE Frequency(Hz)      = 25000000
		PLL_M                  = 5
		PLL_N                  = 160
		PLL_P                  = 2
		PLL_Q                  = 4
		PLL_R                  = 2
		VDD(V)                 = 3.3
		Flash Latency(WS)      = 4
	*/

	HAL_PWREx_ConfigSupply(PWR_DIRECT_SMPS_SUPPLY);

	/* The voltage scaling allows optimizing the power consumption when the
	device is clocked below the maximum system frequency, to update the voltage
	scaling value regarding system frequency refer to product datasheet. */
	__HAL_PWR_VOLTAGESCALING_CONFIG(PWR_REGULATOR_VOLTAGE_SCALE1);

	while( !__HAL_PWR_GET_FLAG( PWR_FLAG_VOSRDY ) )
	{
		__asm volatile ( "NOP" );
	}

	/* Enable HSE Oscillator and activate PLL with HSE as source */
	RCC_OscInitStruct.OscillatorType = RCC_OSCILLATORTYPE_HSE;
	RCC_OscInitStruct.HSEState = RCC_HSE_ON;
	RCC_OscInitStruct.HSIState = RCC_HSI_OFF;
	RCC_OscInitStruct.CSIState = RCC_CSI_OFF;
	RCC_OscInitStruct.PLL.PLLState = RCC_PLL_ON;
	RCC_OscInitStruct.PLL.PLLSource = RCC_PLLSOURCE_HSE;

	RCC_OscInitStruct.PLL.PLLM = 5;
	RCC_OscInitStruct.PLL.PLLN = 160;
	RCC_OscInitStruct.PLL.PLLFRACN = 0;
	RCC_OscInitStruct.PLL.PLLP = 2;
	RCC_OscInitStruct.PLL.PLLR = 2;
	RCC_OscInitStruct.PLL.PLLQ = 4;

	RCC_OscInitStruct.PLL.PLLVCOSEL = RCC_PLL1VCOWIDE;
	RCC_OscInitStruct.PLL.PLLRGE = RCC_PLL1VCIRANGE_2;
	configASSERT( HAL_RCC_OscConfig( &RCC_OscInitStruct ) == HAL_OK );

	/* Select PLL as system clock source and configure  bus clocks dividers */
	RCC_ClkInitStruct.ClockType = ( RCC_CLOCKTYPE_SYSCLK | RCC_CLOCKTYPE_HCLK | RCC_CLOCKTYPE_D1PCLK1 | RCC_CLOCKTYPE_PCLK1 | \
								    RCC_CLOCKTYPE_PCLK2  | RCC_CLOCKTYPE_D3PCLK1 );

	RCC_ClkInitStruct.SYSCLKSource = RCC_SYSCLKSOURCE_PLLCLK;
	RCC_ClkInitStruct.SYSCLKDivider = RCC_SYSCLK_DIV1;
	RCC_ClkInitStruct.AHBCLKDivider = RCC_HCLK_DIV2;
	RCC_ClkInitStruct.APB3CLKDivider = RCC_APB3_DIV2;
	RCC_ClkInitStruct.APB1CLKDivider = RCC_APB1_DIV2;
	RCC_ClkInitStruct.APB2CLKDivider = RCC_APB2_DIV2;
	RCC_ClkInitStruct.APB4CLKDivider = RCC_APB4_DIV2;
	configASSERT( HAL_RCC_ClockConfig( &RCC_ClkInitStruct, FLASH_LATENCY_4 ) == HAL_OK );

	/* AIEC Common configuration: make CPU1 and CPU2 SWI line0 sensitive to
	rising edge. */
	HAL_EXTI_EdgeConfig( EXTI_LINE0, EXTI_RISING_EDGE );

	/* Interrupt used for M4 to M7 notifications. */
	HAL_NVIC_SetPriority( EXTI1_IRQn, 0xFU, 0U );
	HAL_NVIC_EnableIRQ( EXTI1_IRQn );
}

