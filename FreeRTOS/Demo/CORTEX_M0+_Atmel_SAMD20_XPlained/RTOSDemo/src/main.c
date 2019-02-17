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

/******************************************************************************
 * This project provides two demo applications.  A simple blinky style project,
 * and a more comprehensive test and demo application.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting (defined in this file) is used to
 * select between the two.  The simply blinky demo is implemented and described
 * in main_blinky.c.  The more comprehensive test and demo application is
 * implemented and described in main_full.c.
 *
 * This file implements the code that is not demo specific, including the
 * hardware setup and FreeRTOS hook functions.  It also contains a dummy
 * interrupt service routine called Dummy_IRQHandler() that is provided as an
 * example of how to use interrupt safe FreeRTOS API functions (those that end
 * in "FromISR").
 *
 *****************************************************************************/

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo app includes. */
#include "UARTCommandConsole.h"

/* Demo application include. */
#include "QueueSet.h"

/* Library includes. */
#include <asf.h>

/* Set mainCREATE_SIMPLE_BLINKY_DEMO_ONLY to one to run the simple blinky demo,
or 0 to run the more comprehensive test and demo application. */
#define mainCREATE_SIMPLE_BLINKY_DEMO_ONLY	1

/*-----------------------------------------------------------*/

/*
 * Perform any application specific hardware configuration.  
 */
static void prvSetupHardware( void );

/* 
 * Prototypes for the FreeRTOS hook/callback functions.  See the comments in
 * the implementation of each function for more information.
 */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );

/*
 * main_blinky() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 1.
 * main_full() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0.
 */
extern void main_blinky( void );
extern void main_full( void );

/*-----------------------------------------------------------*/

/* Used in the run time stats calculations. */
static unsigned long ulClocksPer10thOfAMilliSecond = 0UL;

/*-----------------------------------------------------------*/

int main (void)
{
	/* Prepare the hardware for the demo. */
	prvSetupHardware();

	/* The mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting is described at the top
	of this file. */
	#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 )
	{
		main_blinky();
	}
	#else
	{
		main_full();
	}
	#endif
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Initialisation is performed by the Atmel board support package. */
	system_init();
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

	/* The semaphore and associated task are not created when the simple blinky
	demo is used. */
	#if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 0
	{
		/* Write to a queue that is in use as part of the queue set demo to
		demonstrate using queue sets from an ISR. */
		vQueueSetAccessQueueSetFromISR();
	}
	#endif /* mainCREATE_SIMPLE_BLINKY_DEMO_ONLY */
}
/*-----------------------------------------------------------*/

void vMainConfigureTimerForRunTimeStats( void )
{
	/* Used by the optional run-time stats gathering functionality. */
	
	/* How many clocks are there per tenth of a millisecond? */
	ulClocksPer10thOfAMilliSecond = configCPU_CLOCK_HZ / 10000UL;
}
/*-----------------------------------------------------------*/

unsigned long ulMainGetRunTimeCounterValue( void )
{
unsigned long ulSysTickCounts, ulTickCount, ulReturn;
const unsigned long ulSysTickReloadValue = ( configCPU_CLOCK_HZ / configTICK_RATE_HZ ) - 1UL;
volatile unsigned long * const pulCurrentSysTickCount = ( ( volatile unsigned long *) 0xe000e018 );
volatile unsigned long * const pulInterruptCTRLState = ( ( volatile unsigned long *) 0xe000ed04 );
const unsigned long ulSysTickPendingBit = 0x04000000UL;

	/* Used by the optional run-time stats gathering functionality. */


	/* NOTE: There are potentially race conditions here.  However, it is used
	anyway to keep the examples simple, and to avoid reliance on a separate
	timer peripheral. */


	/* The SysTick is a down counter.  How many clocks have passed since it was
	last reloaded? */
	ulSysTickCounts = ulSysTickReloadValue - *pulCurrentSysTickCount;
	
	/* How many times has it overflowed? */
	ulTickCount = xTaskGetTickCountFromISR();

	/* This is called from the context switch, so will be called from a
	critical section.  xTaskGetTickCountFromISR() contains its own critical
	section, and the ISR safe critical sections are not designed to nest,
	so reset the critical section. */
	portSET_INTERRUPT_MASK_FROM_ISR();
	
	/* Is there a SysTick interrupt pending? */
	if( ( *pulInterruptCTRLState & ulSysTickPendingBit ) != 0UL )
	{
		/* There is a SysTick interrupt pending, so the SysTick has overflowed
		but the tick count not yet incremented. */
		ulTickCount++;
		
		/* Read the SysTick again, as the overflow might have occurred since
		it was read last. */
		ulSysTickCounts = ulSysTickReloadValue - *pulCurrentSysTickCount;
	}	
	
	/* Convert the tick count into tenths of a millisecond.  THIS ASSUMES
	configTICK_RATE_HZ is 1000! */
	ulReturn = ( ulTickCount * 10UL ) ;
		
	/* Add on the number of tenths of a millisecond that have passed since the
	tick count last got updated. */
	ulReturn += ( ulSysTickCounts / ulClocksPer10thOfAMilliSecond );
	
	return ulReturn;	
}
/*-----------------------------------------------------------*/

#ifdef JUST_AN_EXAMPLE_ISR

void Dummy_IRQHandler(void)
{
long lHigherPriorityTaskWoken = pdFALSE;

	/* Clear the interrupt if necessary. */
	Dummy_ClearITPendingBit();

	/* This interrupt does nothing more than demonstrate how to synchronise a
	task with an interrupt.  A semaphore is used for this purpose.  Note
	lHigherPriorityTaskWoken is initialised to zero. Only FreeRTOS API functions
	that end in "FromISR" can be called from an ISR. */
	xSemaphoreGiveFromISR( xTestSemaphore, &lHigherPriorityTaskWoken );

	/* If there was a task that was blocked on the semaphore, and giving the
	semaphore caused the task to unblock, and the unblocked task has a priority
	higher than the current Running state task (the task that this interrupt
	interrupted), then lHigherPriorityTaskWoken will have been set to pdTRUE
	internally within xSemaphoreGiveFromISR().  Passing pdTRUE into the
	portEND_SWITCHING_ISR() macro will result in a context switch being pended to
	ensure this interrupt returns directly to the unblocked, higher priority,
	task.  Passing pdFALSE into portEND_SWITCHING_ISR() has no effect. */
	portEND_SWITCHING_ISR( lHigherPriorityTaskWoken );
}

#endif /* JUST_AN_EXAMPLE_ISR */

