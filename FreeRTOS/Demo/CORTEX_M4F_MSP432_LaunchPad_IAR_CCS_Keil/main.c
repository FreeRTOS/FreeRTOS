/*
 * FreeRTOS V202107.00
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
 * This project provides two demo applications.  A simple blinky style project,
 * and a more comprehensive test and demo application.  The
 * configCREATE_SIMPLE_TICKLESS_DEMO setting (defined in FreeRTOSConfig.h) is
 * used to select between the two.  The simply blinky demo is implemented and
 * described in main_blinky.c.  The more comprehensive test and demo application
 * is implemented and described in main_full.c.
 *
 * The comprehensive demo uses FreeRTOS+CLI to create a simple command line
 * interface through a UART.
 *
 * The blinky demo uses FreeRTOS's tickless idle mode to reduce power
 * consumption.  See the notes on the web page below regarding the difference
 * in power saving that can be achieved between using the generic tickless
 * implementation (as used by the blinky demo) and a tickless implementation
 * that is tailored specifically to the MSP432.
 *
 * This file implements the code that is not demo specific.
 *
 * See http://www.FreeRTOS.org/TI_MSP432_Free_RTOS_Demo.html for instructions.
 *
 */

/* Standard includes. */
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/*-----------------------------------------------------------*/

/* NOTE: If an IAR build results in an undefined "reference to __write" linker
error then set the printf formatter project option to "tiny" and the scanf
formatter project option to "small". */

/*
 * Set up the hardware ready to run this demo.
 */
static void prvSetupHardware( void );

/*
 * main_blinky() is used when configCREATE_SIMPLE_TICKLESS_DEMO is set to 1.
 * main_full() is used when configCREATE_SIMPLE_TICKLESS_DEMO is set to 0.
 */
extern void main_blinky( void );
extern void main_full( void );

/*-----------------------------------------------------------*/

int main( void )
{
	/* See http://www.FreeRTOS.org/TI_MSP432_Free_RTOS_Demo.html for instructions. */

	/* Prepare the hardware to run this demo. */
	prvSetupHardware();

	/* The configCREATE_SIMPLE_TICKLESS_DEMO setting is described at the top
	of this file. */
	#if( configCREATE_SIMPLE_TICKLESS_DEMO == 1 )
	{
		main_blinky();
	}
	#else
	{
		main_full();
	}
	#endif

	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
extern void FPU_enableModule( void );

	/* The clocks are not configured here, but inside main_full() and
	main_blinky() as the full demo uses a fast clock and the blinky demo uses
	a slow clock. */

	/* Stop the watchdog timer. */
	MAP_WDT_A_holdTimer();

	/* Ensure the FPU is enabled. */
	FPU_enableModule();

	/* Selecting P1.2 and P1.3 in UART mode and P1.0 as output (LED) */
	MAP_GPIO_setAsPeripheralModuleFunctionInputPin( GPIO_PORT_P1, GPIO_PIN2 | GPIO_PIN3, GPIO_PRIMARY_MODULE_FUNCTION );
	MAP_GPIO_setOutputLowOnPin( GPIO_PORT_P1, GPIO_PIN0 );
	MAP_GPIO_setAsOutputPin( GPIO_PORT_P1, GPIO_PIN0 );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* vApplicationMallocFailedHook() will only be called if
	configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
	function that will get called if a call to pvPortMalloc() fails.
	pvPortMalloc() is called internally by the kernel whenever a task, queue,
	timer or semaphore is created.  It is also called by various parts of the
	demo application.  If heap_1.c or heap_2.c are used, then the size of the
	heap available to pvPortMalloc() is defined by configTOTAL_HEAP_SIZE in
	FreeRTOSConfig.h, and the xPortGetFreeHeapSize() API function can be used
	to query the size of free heap space that remains (although it does not
	provide information on how the remaining heap might be fragmented). */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	/* vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set
	to 1 in FreeRTOSConfig.h.  It will be called on each iteration of the idle
	task.  It is essential that code added to this hook function never attempts
	to block in any way (for example, call xQueueReceive() with a block time
	specified, or call vTaskDelay()).  If the application makes use of the
	vTaskDelete() API function (as this demo application does) then it is also
	important that vApplicationIdleHook() is permitted to return to its calling
	function, because it is the responsibility of the idle task to clean up
	memory allocated by the kernel to any task that has since been deleted. */
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void *malloc( size_t xSize )
{
	/* There should not be a heap defined, so trap any attempts to call
	malloc. */
	Interrupt_disableMaster();
	for( ;; );
}
/*-----------------------------------------------------------*/


