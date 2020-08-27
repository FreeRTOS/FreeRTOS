/*
 * FreeRTOS Kernel V10.3.1
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
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting (defined in this file) is used to
 * select between the two.  The simply blinky demo is implemented and described
 * in main_blinky.c.  The more comprehensive test and demo application is
 * implemented and described in main_full.c.
 *
 * This file implements the code that is not demo specific, including the
 * hardware setup and FreeRTOS hook functions.
 *
 * ENSURE TO READ THE DOCUMENTATION PAGE FOR THIS PORT AND DEMO APPLICATION ON
 * THE http://www.FreeRTOS.org WEB SITE FOR FULL INFORMATION ON USING THIS DEMO
 * APPLICATION, AND ITS ASSOCIATE FreeRTOS ARCHITECTURE PORT!
 *
 */

/* Standard includes. */
#include <stdio.h>
#include <limits.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* Standard demo includes. */
#include "partest.h"
#include "TimerDemo.h"
#include "QueueOverwrite.h"
#include "EventGroupsDemo.h"
#include "IntSemTest.h"

/* Altera library includes. */
#include "alt_timers.h"
#include "alt_clock_manager.h"
#include "alt_interrupt.h"
#include "alt_globaltmr.h"
#include "alt_address_space.h"
#include "mmu_support.h"
#include "cache_support.h"

/* mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is used to select between two demo
 * applications, as described at the top of this file.
 *
 * When mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 1 the simple blinky example
 * will be run.
 *
 * When mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0 the comprehensive test
 * and demo application will be run.
 */
#define mainCREATE_SIMPLE_BLINKY_DEMO_ONLY	1

/*-----------------------------------------------------------*/

/*
 * Configure the hardware as necessary to run this demo.
 */
static void prvSetupHardware( void );

/*
 * See the comments at the top of this file and above the
 * mainSELECTED_APPLICATION definition.
 */
#if ( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 )
	extern void main_blinky( void );
#else
	extern void main_full( void );
#endif /* #if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 */

/* Prototypes for the standard FreeRTOS callback/hook functions implemented
within this file. */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );

/*-----------------------------------------------------------*/

/* configAPPLICATION_ALLOCATED_HEAP is set to 1 in FreeRTOSConfig.h so the
application can define the array used as the FreeRTOS heap.  This is done so the
heap can be forced into fast internal RAM - useful because the stacks used by
the tasks come from this space. */
uint8_t ucHeap[ configTOTAL_HEAP_SIZE ] __attribute__ ( ( section( ".oc_ram" ) ) );

/* FreeRTOS uses its own interrupt handler code.  This code cannot use the array
of handlers defined by the Altera drivers because the array is declared static,
and so not accessible outside of the dirver's source file.  Instead declare an
array for use by the FreeRTOS handler.  See:
http://www.freertos.org/Using-FreeRTOS-on-Cortex-A-Embedded-Processors.html. */
static INT_DISPATCH_t xISRHandlers[ ALT_INT_PROVISION_INT_COUNT ];

/*-----------------------------------------------------------*/

int main( void )
{
	/* Configure the hardware ready to run the demo. */
	prvSetupHardware();

	/* The mainSELECTED_APPLICATION setting is described at the top
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

	/* Don't expect to reach here. */
	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
extern uint8_t __cs3_interrupt_vector;
uint32_t ulSCTLR, ulVectorTable = ( uint32_t ) &__cs3_interrupt_vector;
const uint32_t ulVBit = 13U;

	alt_int_global_init();
	alt_int_cpu_binary_point_set( 0 );

	/* Clear SCTLR.V for low vectors and map the vector table to the beginning
	of the code. */
	__asm( "MRC p15, 0, %0, c1, c0, 0" : "=r" ( ulSCTLR ) );
	ulSCTLR &= ~( 1 << ulVBit );
	__asm( "MCR p15, 0, %0, c1, c0, 0" : : "r" ( ulSCTLR ) );
	__asm( "MCR p15, 0, %0, c12, c0, 0" : : "r" ( ulVectorTable ) );

	cache_init();
	mmu_init();

	/* GPIO for LEDs.  ParTest is a historic name which used to stand for
	parallel port test. */
	vParTestInitialise();
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
/*-----------------------------------------------------------*/

void vAssertCalled( const char * pcFile, unsigned long ulLine )
{
volatile unsigned long ul = 0;

	( void ) pcFile;
	( void ) ulLine;

	taskENTER_CRITICAL();
	{
		/* Set ul to a non-zero value using the debugger to step out of this
		function. */
		while( ul == 0 )
		{
			portNOP();
		}
	}
	taskEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
	#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 0 )
	{
		/* The full demo includes a software timer demo/test that requires
		prodding periodically from the tick interrupt. */
		vTimerPeriodicISRTests();

		/* Call the periodic queue overwrite from ISR demo. */
		vQueueOverwritePeriodicISRDemo();

		/* Call the periodic event group from ISR demo. */
		vPeriodicEventGroupsProcessing();

		/* Call the periodic test that uses mutexes form an interrupt. */
		vInterruptSemaphorePeriodicTest();
	}
	#endif
}
/*-----------------------------------------------------------*/

void vConfigureTickInterrupt( void )
{
alt_freq_t ulTempFrequency;
const alt_freq_t ulMicroSecondsPerSecond = 1000000UL;
void FreeRTOS_Tick_Handler( void );

	/* Interrupts are disabled when this function is called. */

	/* Initialise the general purpose timer modules. */
	alt_gpt_all_tmr_init();

	/* ALT_CLK_MPU_PERIPH = mpu_periph_clk */
	alt_clk_freq_get( ALT_CLK_MPU_PERIPH, &ulTempFrequency );

	/* Use the local private timer. */
	alt_gpt_counter_set( ALT_GPT_CPU_PRIVATE_TMR, ulTempFrequency / configTICK_RATE_HZ );

	/* Sanity check. */
	configASSERT( alt_gpt_time_microsecs_get( ALT_GPT_CPU_PRIVATE_TMR ) == ( ulMicroSecondsPerSecond / configTICK_RATE_HZ ) );

	/* Set to periodic mode. */
	alt_gpt_mode_set( ALT_GPT_CPU_PRIVATE_TMR, ALT_GPT_RESTART_MODE_PERIODIC );

	/* The timer can be started here as interrupts are disabled. */
	alt_gpt_tmr_start( ALT_GPT_CPU_PRIVATE_TMR );

	/* Register the standard FreeRTOS Cortex-A tick handler as the timer's
	interrupt handler.  The handler clears the interrupt using the
	configCLEAR_TICK_INTERRUPT() macro, which is defined in FreeRTOSConfig.h. */
	vRegisterIRQHandler( ALT_INT_INTERRUPT_PPI_TIMER_PRIVATE, ( alt_int_callback_t ) FreeRTOS_Tick_Handler, NULL );

	/* This tick interrupt must run at the lowest priority. */
	alt_int_dist_priority_set( ALT_INT_INTERRUPT_PPI_TIMER_PRIVATE, portLOWEST_USABLE_INTERRUPT_PRIORITY << portPRIORITY_SHIFT );

	/* Ensure the interrupt is forwarded to the CPU. */
    alt_int_dist_enable( ALT_INT_INTERRUPT_PPI_TIMER_PRIVATE );

    /* Finally, enable the interrupt. */
	alt_gpt_int_clear_pending( ALT_GPT_CPU_PRIVATE_TMR );
	alt_gpt_int_enable( ALT_GPT_CPU_PRIVATE_TMR );

}
/*-----------------------------------------------------------*/

void vRegisterIRQHandler( uint32_t ulID, alt_int_callback_t pxHandlerFunction, void *pvContext )
{
	if( ulID < ALT_INT_PROVISION_INT_COUNT )
	{
		xISRHandlers[ ulID ].pxISR = pxHandlerFunction;
		xISRHandlers[ ulID ].pvContext = pvContext;
	}
}
/*-----------------------------------------------------------*/

void vApplicationIRQHandler( uint32_t ulICCIAR )
{
uint32_t ulInterruptID;
void *pvContext;
alt_int_callback_t pxISR;

	/* Re-enable interrupts. */
    __asm ( "cpsie i" );

	/* The ID of the interrupt is obtained by bitwise anding the ICCIAR value
	with 0x3FF. */
	ulInterruptID = ulICCIAR & 0x3FFUL;

	if( ulInterruptID < ALT_INT_PROVISION_INT_COUNT )
	{
		/* Call the function installed in the array of installed handler
		functions. */
		pxISR = xISRHandlers[ ulInterruptID ].pxISR;
		pvContext = xISRHandlers[ ulInterruptID ].pvContext;
		pxISR( ulICCIAR, pvContext );
	}
}

