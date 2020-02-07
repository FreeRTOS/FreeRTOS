/*
 * FreeRTOS Kernel V10.3.0
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
 * hardware setup and standard FreeRTOS hook functions.
 *
 * When running on the HiFive Rev B hardware:
 * When executing correctly the blue LED will toggle every three seconds.  If
 * the blue LED toggles every 500ms then one of the self-monitoring test tasks
 * discovered a potential issue.  If the red led toggles rapidly then a hardware
 * exception occurred.
 *
 * ENSURE TO READ THE DOCUMENTATION PAGE FOR THIS PORT AND DEMO APPLICATION ON
 * THE http://www.FreeRTOS.org WEB SITE FOR FULL INFORMATION ON USING THIS DEMO
 * APPLICATION, AND ITS ASSOCIATE FreeRTOS ARCHITECTURE PORT!
 *
 */

/* FreeRTOS kernel includes. */
#include <FreeRTOS.h>
#include <task.h>

/* Freedom metal driver includes. */
#include <metal/cpu.h>
#include <metal/led.h>

/* Set mainCREATE_SIMPLE_BLINKY_DEMO_ONLY to one to run the simple blinky demo,
or 0 to run the more comprehensive test and demo application. */
#define mainCREATE_SIMPLE_BLINKY_DEMO_ONLY	0

/* Index to first HART (there is only one). */
#define mainHART_0 		0

/* Registers used to initialise the PLIC. */
#define mainPLIC_PENDING_0 ( * ( ( volatile uint32_t * ) 0x0C001000UL ) )
#define mainPLIC_PENDING_1 ( * ( ( volatile uint32_t * ) 0x0C001004UL ) )
#define mainPLIC_ENABLE_0  ( * ( ( volatile uint32_t * ) 0x0C002000UL ) )
#define mainPLIC_ENABLE_1  ( * ( ( volatile uint32_t * ) 0x0C002004UL ) )

/*-----------------------------------------------------------*/

/*
 * main_blinky() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 1.
 * main_full() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0.
 */
#if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1
	extern void main_blinky( void );
#else
	extern void main_full( void );
#endif /* #if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 */

/*
 * Prototypes for the standard FreeRTOS callback/hook functions implemented
 * within this file.  See https://www.freertos.org/a00016.html
 */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );

/*
 * Setup the hardware to run this demo.
 */
static void prvSetupHardware( void );

/*
 * Used by the Freedom Metal drivers.
 */
static struct metal_led *pxBlueLED = NULL;

/*-----------------------------------------------------------*/

int main( void )
{
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
struct metal_cpu *pxCPU;
struct metal_interrupt *pxInterruptController;

	/* Initialise the blue LED. */
	pxBlueLED = metal_led_get_rgb( "LD0", "blue" );
	configASSERT( pxBlueLED );
	metal_led_enable( pxBlueLED );
	metal_led_off( pxBlueLED );

	/* Initialise the interrupt controller. */
	pxCPU = metal_cpu_get( mainHART_0 );
	configASSERT( pxCPU );
	pxInterruptController = metal_cpu_interrupt_controller( pxCPU );
	configASSERT( pxInterruptController );
	metal_interrupt_init( pxInterruptController );

	/* Set all interrupt enable bits to 0. */
	mainPLIC_ENABLE_0 = 0UL;
	mainPLIC_ENABLE_1 = 0UL;

	/* Clear all pending interrupts. */
	mainPLIC_PENDING_0 = 0UL;
	mainPLIC_PENDING_1 = 0UL;
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
	/* The tests in the full demo expect some interaction with interrupts. */
	#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY != 1 )
	{
		extern void vFullDemoTickHook( void );
		vFullDemoTickHook();
	}
	#endif
}
/*-----------------------------------------------------------*/

void vAssertCalled( void )
{
static struct metal_led *pxRedLED = NULL;
volatile uint32_t ul;
const uint32_t ulNullLoopDelay = 0x1ffffUL;

	taskDISABLE_INTERRUPTS();

	/* Initialise the red LED. */
	pxRedLED = metal_led_get_rgb( "LD0", "red" );
	configASSERT( pxRedLED );
	metal_led_enable( pxRedLED );
	metal_led_off( pxRedLED );

	/* Flash the red LED to indicate that assert was hit - interrupts are off
	here to prevent any further tick interrupts or context switches, so the
	delay is implemented as a crude loop instead of a peripheral timer. */
	for( ;; )
	{
		for( ul = 0; ul < ulNullLoopDelay; ul++ )
		{
			__asm volatile( "nop" );
		}
		metal_led_toggle( pxRedLED );
	}
}
/*-----------------------------------------------------------*/

void handle_trap( void )
{
volatile uint32_t ulMEPC = 0UL, ulMCAUSE = 0UL, ulPLICPending0Register = 0UL, ulPLICPending1Register = 0UL;

	/* Store a few register values that might be useful when determining why this
	function was called. */
	__asm volatile( "csrr %0, mepc" : "=r"( ulMEPC ) );
	__asm volatile( "csrr %0, mcause" : "=r"( ulMCAUSE ) );
	ulPLICPending0Register = mainPLIC_PENDING_0;
	ulPLICPending1Register = mainPLIC_PENDING_1;

	/* Prevent compiler warnings about unused variables. */
	( void ) ulPLICPending0Register;
	( void ) ulPLICPending1Register;

	/* Force an assert as this function has not been implemented as the demo
	does not use external interrupts. */
	configASSERT( metal_cpu_get( mainHART_0 ) == 0x00 );
}
/*-----------------------------------------------------------*/

void vToggleLED( void )
{
	metal_led_toggle( pxBlueLED );
}
/*-----------------------------------------------------------*/

void *malloc( size_t xSize )
{
	/* The linker script does not define a heap so artificially force an assert()
	if something unexpectedly uses the C library heap.  See
	https://www.freertos.org/a00111.html for more information. */
	configASSERT( metal_cpu_get( mainHART_0 ) == 0x00 );

	/* Remove warnings about unused parameter. */
	( void ) xSize;
	return NULL;
}
/*-----------------------------------------------------------*/


