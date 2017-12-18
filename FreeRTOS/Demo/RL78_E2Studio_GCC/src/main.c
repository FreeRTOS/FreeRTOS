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
 * This project provides two demo applications.  A simple blinky style project,
 * and a more comprehensive test and demo application.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting (defined in this file) is used to
 * select between the two.  The simply blinky demo is implemented and described
 * in main_blinky.c.  The more comprehensive test and demo application is
 * implemented and described in main_full.c.
 *
 * This file implements the code that is not demo specific, including the
 * hardware setup and FreeRTOS hook functions.
 *
 * This project does not provide an example of how to write an RTOS compatible
 * interrupt service routine (other than the tick interrupt itself), so this
 * file contains the function vAnExampleISR_C_Handler() as a dummy example (that
 * is not actually installed) that can be used as a reference.  Also see the
 * file ExampleISR.S, and the documentation page for this demo on the
 * FreeRTOS.org website for full instructions.
 *
 * ENSURE TO READ THE DOCUMENTATION PAGE FOR THIS PORT AND DEMO APPLICATION ON
 * THE http://www.FreeRTOS.org WEB SITE FOR FULL INFORMATION ON USING THIS DEMO
 * APPLICATION, AND ITS ASSOCIATE FreeRTOS ARCHITECTURE PORT!
 *
 */

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* Set mainCREATE_SIMPLE_BLINKY_DEMO_ONLY to one to run the simple blinky demo,
or 0 to run the more comprehensive test and demo application. */
#define mainCREATE_SIMPLE_BLINKY_DEMO_ONLY	0

/*-----------------------------------------------------------*/

/*
 * main_blinky() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 1.
 * main_full() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0.
 */
#if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1
	extern void main_blinky( void );
#else
    extern void main_full( void );
#endif

/* Prototypes for the standard FreeRTOS callback/hook functions implemented
within this file. */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );

/* This variable is not actually used, but provided to allow an example of how
to write an ISR to be included in this file. */
static SemaphoreHandle_t xSemaphore = NULL;
/*-----------------------------------------------------------*/

#define portPSW ( 0xc6UL )
volatile uint32_t *pulAddress;
volatile uint32_t ulValue, ulError = 0;

int main( void )
{
	/* Store an address below 0x8000 */
	pulAddress = ( uint32_t * ) 0x7fff;

	/* Cast and OR with a value that uses the two most significant
	bytes. */
	ulValue = ( ( uint32_t ) pulAddress ) | ( portPSW << 24UL );

	/* This test passes. */
	if( ulValue != 0xc6007fff )
	{
		/* This line of code is not executed. */
		ulError = 1;
	}

	/* Now do the same, but with an address above 0x7fff, but
	still slower than the max 16-bit value. */
	pulAddress = ( uint32_t * ) 0x8000;
	ulValue = ( ( uint32_t ) pulAddress ) | ( portPSW << 24UL );

	/* This test *fails*. */
	if( ulValue != 0xc6008000 )
	{
		/* This line of code *is* executed. */
		ulError = 1;
	}


	/* The mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting is
	described at the top of this file. */
	#if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1
	{
		main_blinky();
	}
	#else
	{
		main_full();
	}
	#endif

	/* Should not get here.  See the definitions of main_blinky() and
	main_full(). */
	return 0;
}
/*-----------------------------------------------------------*/

void vAnExampleISR_C_Handler( void )
{
	/*
	 * This demo does not include a functional interrupt service routine - so
	 * this dummy handler (which is not actually installed) is provided as an
	 * example of how an ISR that needs to cause a context switch needs to be
	 * implemented.  ISRs that do not cause a context switch have no special
	 * requirements and can be written as per the compiler documentation.
	 *
	 * This C function is called from a wrapper function that is implemented
	 * in assembly code.  See vANExampleISR_ASM_Wrapper() in ExampleISR.S.  Also
	 * see the documentation page for this demo on the FreeRTOS.org website for
	 * full instructions.
	 */
short sHigherPriorityTaskWoken = pdFALSE;

	/* Handler code goes here...*/

	/* For purposes of demonstration, assume at some point the hander calls
	xSemaphoreGiveFromISR().*/
	xSemaphoreGiveFromISR( xSemaphore, &sHigherPriorityTaskWoken );

	/* If giving the semaphore unblocked a task, and the unblocked task has a
	priority higher than or equal to the currently running task, then
	sHigherPriorityTaskWoken will have been set to pdTRUE internally within the
	xSemaphoreGiveFromISR() function.  Passing a pdTRUE	value to
	portYIELD_FROM_ISR() will cause this interrupt to return directly to the
	higher priority unblocked task. */
	portYIELD_FROM_ISR( sHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* Called if a call to pvPortMalloc() fails because there is insufficient
	free memory available in the FreeRTOS heap.  pvPortMalloc() is called
	internally by FreeRTOS API functions that create tasks, queues, software
	timers, and semaphores.  The size of the FreeRTOS heap is set by the
	configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
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

void vApplicationIdleHook( void )
{
volatile size_t xFreeHeapSpace;

	/* This is just a trivial example of an idle hook.  It is called on each
	cycle of the idle task.  It must *NOT* attempt to block.  In this case the
	idle task just queries the amount of FreeRTOS heap that remains.  See the
	memory management section on the http://www.FreeRTOS.org web site for memory
	management options.  If there is a lot of heap memory free then the
	configTOTAL_HEAP_SIZE value in FreeRTOSConfig.h can be reduced to free up
	RAM. */
	xFreeHeapSpace = xPortGetFreeHeapSize();

	/* Remove compiler warning about xFreeHeapSpace being set but never used. */
	( void ) xFreeHeapSpace;
}


