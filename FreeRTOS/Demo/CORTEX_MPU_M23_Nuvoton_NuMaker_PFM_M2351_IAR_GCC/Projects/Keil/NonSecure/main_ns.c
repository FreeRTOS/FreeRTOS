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

/* Device includes. */
#include <arm_cmse.h>
#include "NuMicro.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "tz_demo.h"
#include "mpu_demo.h"

/* Externs needed by the MPU setup code. These are defined in Scatter-Loading
 * description file (FreeRTOSDemo_ns.sct). */
extern uint32_t Image$$ER_IROM_NS_PRIVILEGED$$Base;
extern uint32_t Image$$ER_IROM_NS_PRIVILEGED_ALIGN$$Limit;
extern uint32_t Image$$ER_IROM_NS_FREERTOS_SYSTEM_CALLS$$Base;
extern uint32_t Image$$ER_IROM_NS_FREERTOS_SYSTEM_CALLS_ALIGN$$Limit;
extern uint32_t Image$$ER_IROM_NS_UNPRIVILEGED$$Base;
extern uint32_t Image$$ER_IROM_NS_UNPRIVILEGED_ALIGN$$Limit;

extern uint32_t Image$$ER_IRAM_NS_PRIVILEGED$$Base;
extern uint32_t Image$$ER_IRAM_NS_PRIVILEGED_ALIGN$$Limit;
extern uint32_t Image$$ER_IRAM_NS_UNPRIVILEGED$$Base;
extern uint32_t Image$$ER_IRAM_NS_UNPRIVILEGED_ALIGN$$Limit;

/* Privileged flash. */
const uint32_t * __privileged_functions_start__		= ( uint32_t * ) &( Image$$ER_IROM_NS_PRIVILEGED$$Base );
const uint32_t * __privileged_functions_end__		= ( uint32_t * ) ( ( uint32_t ) &( Image$$ER_IROM_NS_PRIVILEGED_ALIGN$$Limit ) - 0x1 ); /* Last address in privileged Flash region. */

/* Flash containing system calls. */
const uint32_t * __syscalls_flash_start__			= ( uint32_t * ) &( Image$$ER_IROM_NS_FREERTOS_SYSTEM_CALLS$$Base );
const uint32_t * __syscalls_flash_end__				= ( uint32_t * ) ( ( uint32_t ) &( Image$$ER_IROM_NS_FREERTOS_SYSTEM_CALLS_ALIGN$$Limit ) - 0x1 ); /* Last address in Flash region containing system calls. */

/* Unprivileged flash. Note that the section containing system calls is
 * unprivileged so that unprivileged tasks can make system calls. */
const uint32_t * __unprivileged_flash_start__		= ( uint32_t * ) &( Image$$ER_IROM_NS_UNPRIVILEGED$$Base );
const uint32_t * __unprivileged_flash_end__			= ( uint32_t * ) ( ( uint32_t ) &( Image$$ER_IROM_NS_UNPRIVILEGED_ALIGN$$Limit ) - 0x1 ); /* Last address in un-privileged Flash region. */

/* RAM with priviledged access only. This contains kernel data. */
const uint32_t * __privileged_sram_start__			= ( uint32_t * ) &( Image$$ER_IRAM_NS_PRIVILEGED$$Base );
const uint32_t * __privileged_sram_end__			= ( uint32_t * ) ( ( uint32_t ) &( Image$$ER_IRAM_NS_PRIVILEGED_ALIGN$$Limit ) - 0x1 ); /* Last address in privileged RAM. */

/* Unprivileged RAM. */
const uint32_t * __unprivileged_sram_start__		= ( uint32_t * ) &( Image$$ER_IRAM_NS_UNPRIVILEGED$$Base );
const uint32_t * __unprivileged_sram_end__			= ( uint32_t * ) ( ( uint32_t ) &( Image$$ER_IRAM_NS_UNPRIVILEGED_ALIGN$$Limit ) - 0x1 ); /* Last address in un-privileged RAM. */
/*-----------------------------------------------------------*/

/**
 * @brief Create all demo tasks.
 */
static void prvCreateTasks( void );

/**
 * @brief The hard fault handler.
 *
 * It calls a function called vHandleMemoryFault.
 */
void HardFault_Handler( void ) __attribute__ ( ( naked ) );
/*-----------------------------------------------------------*/

/* For instructions on how to build and run this demo, visit the following link:
 * https://www.freertos.org/RTOS-Cortex-M23-NuMaker-PFM-M2351-Keil.html
 */

/* Non-Secure main. */
int main( void )
{
	/* Initialize debug port. */
	DEBUG_PORT->BAUD = UART_BAUD_MODE2 | UART_BAUD_MODE2_DIVIDER( __HIRC, 115200 );
	DEBUG_PORT->LINE = UART_WORD_LEN_8 | UART_PARITY_NONE | UART_STOP_BIT_1;

	/* Print banner. */
	printf( "\n" );
	printf( "+---------------------------------------------+\n" );
	printf( "|           Nonsecure is running ...          |\n" );
	printf( "+---------------------------------------------+\n" );

	/* Create tasks. */
	prvCreateTasks();

	/* Start scheduler. */
	vTaskStartScheduler();

	/* Will not get here if the scheduler starts successfully.  If you do end up
	here then there wasn't enough heap memory available to start either the idle
	task or the timer/daemon task.  https://www.freertos.org/a00111.html */

	for( ; ; )
	{
	}
}
/*-----------------------------------------------------------*/

static void prvCreateTasks( void )
{
	/* Create tasks for the MPU Demo. */
	vStartMPUDemo();

	/* Create tasks for the TZ Demo. */
	vStartTZDemo();

}
/*-----------------------------------------------------------*/

/* Stack overflow hook. */
void vApplicationStackOverflowHook( TaskHandle_t xTask, char *pcTaskName )
{
	/* Force an assert. */
	configASSERT( pcTaskName == 0 );
}
/*-----------------------------------------------------------*/

/* configUSE_STATIC_ALLOCATION is set to 1, so the application must provide an
 * implementation of vApplicationGetIdleTaskMemory() to provide the memory that
 * is used by the Idle task. */
void vApplicationGetIdleTaskMemory(	StaticTask_t ** ppxIdleTaskTCBBuffer,
									StackType_t ** ppxIdleTaskStackBuffer,
									uint32_t * pulIdleTaskStackSize )
{
	/* If the buffers to be provided to the Idle task are declared inside this
	 * function then they must be declared static - otherwise they will be
	 * allocated on the stack and so not exists after this function exits. */
	static StaticTask_t xIdleTaskTCB;
	static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( 32 ) ) );

	/* Pass out a pointer to the StaticTask_t structure in which the Idle
	 * task's state will be stored. */
	*ppxIdleTaskTCBBuffer = &xIdleTaskTCB;

	/* Pass out the array that will be used as the Idle task's stack. */
	*ppxIdleTaskStackBuffer = uxIdleTaskStack;

	/* Pass out the size of the array pointed to by *ppxIdleTaskStackBuffer.
	 * Note that, as the array is necessarily of type StackType_t,
	 * configMINIMAL_STACK_SIZE is specified in words, not bytes. */
	*pulIdleTaskStackSize = configMINIMAL_STACK_SIZE;
}
/*-----------------------------------------------------------*/

/* configUSE_STATIC_ALLOCATION and configUSE_TIMERS are both set to 1, so the
 * application must provide an implementation of vApplicationGetTimerTaskMemory()
 * to provide the memory that is used by the Timer service task. */
void vApplicationGetTimerTaskMemory( StaticTask_t ** ppxTimerTaskTCBBuffer,
									 StackType_t ** ppxTimerTaskStackBuffer,
									 uint32_t * pulTimerTaskStackSize )
{
	/* If the buffers to be provided to the Timer task are declared inside this
	 * function then they must be declared static - otherwise they will be
	 * allocated on the stack and so not exists after this function exits. */
	static StaticTask_t xTimerTaskTCB;
	static StackType_t uxTimerTaskStack[ configTIMER_TASK_STACK_DEPTH ] __attribute__( ( aligned( 32 ) ) );

	/* Pass out a pointer to the StaticTask_t structure in which the Timer
	 * task's state will be stored. */
	*ppxTimerTaskTCBBuffer = &xTimerTaskTCB;

	/* Pass out the array that will be used as the Timer task's stack. */
	*ppxTimerTaskStackBuffer = uxTimerTaskStack;

	/* Pass out the size of the array pointed to by *ppxTimerTaskStackBuffer.
	 * Note that, as the array is necessarily of type StackType_t,
	 * configTIMER_TASK_STACK_DEPTH is specified in words, not bytes. */
	*pulTimerTaskStackSize = configTIMER_TASK_STACK_DEPTH;
}
/*-----------------------------------------------------------*/

void HardFault_Handler( void )
{
	__asm volatile
	(
		" movs r0, #4										\n"
		" mov r1, lr										\n"
		" tst r0, r1										\n"
		" beq msp_used_for_stacking							\n"
		" mrs r0, psp										\n"
		" ldr r2, handler_address_const						\n"
		" bx r2												\n"
		"msp_used_for_stacking:								\n"
		"	mrs r0, msp										\n"
		"	ldr r2, handler_address_const					\n"
		"	bx r2											\n"
		"													\n"
		" .align 4											\n"
		" handler_address_const: .word vHandleMemoryFault	\n"
	);
}
/*-----------------------------------------------------------*/
