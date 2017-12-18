/*
 * FreeRTOS Kernel V10.0.1
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
 * This project provides two demo applications.  A low power project that
 * demonstrates the FreeRTOS tickless mode, and a more comprehensive test and
 * demo application.  The configCREATE_LOW_POWER_DEMO setting (defined at the
 * top of FreeRTOSConfig.h) is used to select between the two.  The low power
 * demo is implemented and described in main_low_power.c.  The more
 * comprehensive test and demo application is implemented and described in
 * main_full.c.
 *
 * This file implements the code that is not demo specific, including the
 * hardware setup and FreeRTOS hook functions.
 */

/* Standard includes. */
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard demo includes - just needed for the LED (ParTest) initialisation
function. */
#include "partest.h"

/* Atmel library includes. */
#include <asf.h>

/*-----------------------------------------------------------*/

/*
 * Set up the hardware ready to run this demo.
 */
static void prvSetupHardware( void );

/*
 * main_low_power() is used when configCREATE_LOW_POWER_DEMO is set to 1.
 * main_full() is used when configCREATE_LOW_POWER_DEMO is set to 0.
 * configCREATE_LOW_POWER_DEMO is defined at the top of main.c.
 */
extern void main_low_power( void );
extern void main_full( void );

/* Prototypes for the standard FreeRTOS callback/hook functions implemented
within this file. */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );

/* A handler for a button interrupt.  The button's only purpose is to bring the
CPU out of sleep mode early. */
static void prvButtonISR( void );

/*-----------------------------------------------------------*/

/* See the documentation page for this demo on the FreeRTOS.org web site for
full information - including hardware setup requirements. */
int main( void )
{
	/* Prepare the hardware to run this demo. */
	prvSetupHardware();

	/* The configCREATE_LOW_POWER_DEMO setting is described at the top of
	this file. */
	#if( configCREATE_LOW_POWER_DEMO == 1 )
	{
		main_low_power();
	}
	#else
	{
		main_full();
	}
	#endif

	return 0;
}
/*-----------------------------------------------------------*/

static void prvButtonISR( void )
{
	/* The button doesn't do anything other than providing a means for brining
	the MCU out of sleep mode early. */
	if( eic_line_interrupt_is_pending( EIC, GPIO_PUSH_BUTTON_EIC_LINE ) ) 
	{
		eic_line_clear_interrupt( EIC, GPIO_PUSH_BUTTON_EIC_LINE );
	}		
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
extern void SystemCoreClockUpdate( void );
struct eic_line_config xEICLineConfiguration;

	/* Configure the external interrupt controller so button pushes can
	generate interrupts. */
	xEICLineConfiguration.eic_mode = EIC_MODE_EDGE_TRIGGERED;
	xEICLineConfiguration.eic_edge = EIC_EDGE_FALLING_EDGE;
	xEICLineConfiguration.eic_level = EIC_LEVEL_LOW_LEVEL;
	xEICLineConfiguration.eic_filter = EIC_FILTER_DISABLED;
	xEICLineConfiguration.eic_async = EIC_ASYNCH_MODE;
	eic_enable( EIC );
	eic_line_set_config( EIC, GPIO_PUSH_BUTTON_EIC_LINE, &xEICLineConfiguration );
	eic_line_set_callback( EIC, GPIO_PUSH_BUTTON_EIC_LINE, prvButtonISR, EIC_5_IRQn, 0 );
	eic_line_enable( EIC, GPIO_PUSH_BUTTON_EIC_LINE );

	/* ASF function to setup clocking. */
	sysclk_init();

	/* Ensure all priority bits are assigned as preemption priority bits. */
	NVIC_SetPriorityGrouping( 0 );

	/* Atmel library function to setup for the evaluation kit being used. */
	board_init();

	/* Initialise the sleep manager in case the low power demo is being used. */
	sleepmgr_init();
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

void vApplicationTickHook( void )
{
	/* This function will be called by each tick interrupt if
	configUSE_TICK_HOOK is set to 1 in FreeRTOSConfig.h.  User code can be
	added here, but the tick hook is called from an interrupt context, so
	code must not attempt to block, and only the interrupt safe FreeRTOS API
	functions can be used (those that end in FromISR()). */
}
/*-----------------------------------------------------------*/

void vAssertCalled( void )
{
volatile unsigned long ul = 0;

	taskENTER_CRITICAL();
	{
		/* Set ul to a non-zero value using the debugger to step out of this
		function. */
		while( ul == 0 )
		{
			__asm volatile( "NOP" );
		}
	}
	taskEXIT_CRITICAL();
}
