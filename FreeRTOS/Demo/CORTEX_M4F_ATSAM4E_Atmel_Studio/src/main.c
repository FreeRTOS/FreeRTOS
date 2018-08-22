/*
 * FreeRTOS Kernel V10.1.0
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

/******************************************************************************
 * This project provides two demo applications.  A simple blinky style project,
 * and a more comprehensive application that includes FreeRTOS+CLI, FreeRTOS+UDP
 * and FreeRTOS+FAT SL.  The mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting (defined
 * in this file) is used to select between the two.  The simply blinky demo is
 * implemented and described in main_blinky.c.  The more comprehensive demo
 * application is implemented and described in main_full.c and full user
 * instructions are provided on the following URL:
 * http://www.FreeRTOS.org/Atmel_SAM4E_RTOS_Demo.html
 *
 * This file implements the code that is not demo specific, including the
 * hardware setup and FreeRTOS hook functions.
 *
 */

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo application includes. */
#include "partest.h"

/* Set mainCREATE_SIMPLE_BLINKY_DEMO_ONLY to one to run the simple blinky demo,
or 0 to run the more comprehensive demo application that includes add-on
components. */
#define mainCREATE_SIMPLE_BLINKY_DEMO_ONLY	1

/*-----------------------------------------------------------*/

/*
 * Set up the hardware ready to run this demo.
 */
static void prvSetupHardware( void );

/*
 * main_blinky() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 1.
 * main_full() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0.
 */
extern void main_blinky( void );
extern void main_full( void );

/*-----------------------------------------------------------*/

int main( void )
{
	/* Prepare the hardware to run this demo. */
	prvSetupHardware();

	/* The mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting is described at the top
	of this file. */
	#if ( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 )
	{
		main_blinky();
	}
	#else
	{
		/* Full user instructions are provided on the following URL:
		http://www.FreeRTOS.org/Atmel_SAM4E_RTOS_Demo.html */
		main_full();
	}
	#endif /* mainCREATE_SIMPLE_BLINKY_DEMO_ONLY */

	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Call the ASF initialisation functions. */
	board_init();
	sysclk_init();
	pmc_enable_periph_clk( ID_GMAC );
	pmc_enable_periph_clk( ID_SMC );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
static volatile uint32_t ulCount = 0;

	/* vApplicationMallocFailedHook() will only be called if
	configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
	function that will get called if a call to pvPortMalloc() fails.
	pvPortMalloc() is called internally by the kernel whenever a task, queue,
	timer or semaphore is created.  It is also called by various parts of the
	demo application.  If heap_1.c or heap_2.c are used, then the size of the
	heap available to pvPortMalloc() is defined by configTOTAL_HEAP_SIZE in
	FreeRTOSConfig.h, and the xPortGetFreeHeapSize() API function can be used
	to query the size of free heap space that remains (although it does not
	provide information on how the remaining heap might be fragmented). 
	
	Just count the number of malloc fails as some failures may occur simply
	because the network load is very high, resulting in the consumption of a
	lot of network buffers. */
	ulCount++;	
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

	/* The simple blinky demo does not use the idle hook - the full demo does. */
	#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 0 )
	{
		extern void vFullDemoIdleHook( void );

		/* Implemented in main_full.c. */
		vFullDemoIdleHook();
	}
	#endif
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook	function is
	called if a stack overflow is detected. */
	vAssertCalled( __LINE__, __FILE__ );
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
	/* This function will be called by each tick interrupt if
	configUSE_TICK_HOOK is set to 1 in FreeRTOSConfig.h.  User code can be
	added here, but the tick hook is called from an interrupt context, so
	code must not attempt to block, and only the interrupt safe FreeRTOS API
	functions can be used (those that end in FromISR()). */

	/* The simple blinky demo does not use the tick hook - the full demo does. */
	#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 0 )
	{
		extern void vFullDemoTickHook( void );

		/* Implemented in main_full.c. */
		vFullDemoTickHook();
	}
	#endif
}
/*-----------------------------------------------------------*/

void vAssertCalled( uint32_t ulLine, const char *pcFile )
{
/* The following two variables are just to ensure the parameters are not
optimised away and therefore unavailable when viewed in the debugger. */
volatile uint32_t ulLineNumber = ulLine, ulSetNonZeroInDebuggerToReturn = 0;
volatile const char * const pcFileName = pcFile;

	taskENTER_CRITICAL();
	while( ulSetNonZeroInDebuggerToReturn == 0 )
	{
		/* If you want to set out of this function in the debugger to see the
		assert() location then set ulSetNonZeroInDebuggerToReturn to a non-zero
		value. */
	}
	taskEXIT_CRITICAL();

	( void ) pcFileName;
	( void ) ulLineNumber;
}
/*-----------------------------------------------------------*/

/* Provided to keep the linker happy. */
void _exit_( int status )
{
	( void ) status;
	vAssertCalled( __LINE__, __FILE__ );
	for( ;; );
}
/*-----------------------------------------------------------*/

/* Provided to keep the linker happy. */
int _read( void )
{
	return 0;
}
/*-----------------------------------------------------------*/

/* Provided to keep the linker happy. */
int _write( int x )
{
	( void ) x;
	return 0;
}
/*-----------------------------------------------------------*/



