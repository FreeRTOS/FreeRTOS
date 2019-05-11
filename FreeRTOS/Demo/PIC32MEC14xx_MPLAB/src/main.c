/*
 * FreeRTOS Kernel V10.2.1
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
 * hardware setup and FreeRTOS hook functions.
 *****************************************************************************/

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"

/* Target includes. */
#include "appcfg.h"
#include "MEC14xx/mec14xx.h"
#include "MEC14xx/mec14xx_jtvic.h"
#include "MEC14xx/mec14xx_bbled.h"
#include "MEC14xx/mec14xx_girqs.h"

/* Set mainCREATE_SIMPLE_BLINKY_DEMO_ONLY to one to run the simple blinky demo,
or 0 to run the more comprehensive test and demo application. */
#define mainCREATE_SIMPLE_BLINKY_DEMO_ONLY	0

/*-----------------------------------------------------------*/

/*
 * main_blinky() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 1.
 * main_full() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0.
 */
extern void main_blinky( void );
extern void main_full( void );

/*
 * Performs any hardware setup necessary.
 */
 static void __attribute__((nomips16)) prvSetupHardware( void );

/*
 * Add some thread safety to the LED toggle function.
 */
void vToggleLED( uint8_t ucLED );

/*-----------------------------------------------------------*/

int main( void )
{
	/* Perform any hardware initialisation necessary. */
	prvSetupHardware();

	/* The mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting is described at the top
	of this file. */
	#if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1
	{
		main_blinky();
	}
	#else
	{
		main_full();
	}
	#endif

    /* Should never be reached. */
    return 0;
}
/*-----------------------------------------------------------*/

void vToggleLED( uint8_t ucLED )
{
	taskENTER_CRITICAL();
	{
		led_out_toggle( ucLED );
	}
	taskEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

static void __attribute__((nomips16)) prvSetupHardware( void )
{
volatile uint32_t ulTemp;

	/* Interrupts are automatically re-enabled when the scheduler is started. */
	__asm volatile( "di" );

	/* Enable M14K Vector Pre-fetch: CP0.IntCtl b[22]=1
	   IRET (interrupt chaining): b[21]=1
	   Enable Auto-Prolog: b[14]=1 */
	ulTemp = _CP0_GET_INTCTL();
	ulTemp |= ( 1ul << 22 ) + ( 1ul << 21 ) + ( 1ul << 14 );
	_CP0_SET_INTCTL( ulTemp );

	/* Configure 32KHz for Switched Clock Source always ON
	   b[ 0 ] = XOSEL                     = 1
	   b[ 1 ] = EXT_32K_OSC_EN            = 1
	   b[ 2 ] = INT_32K_OSC_EN            = 1
	   b[ 3 ] = INT_32K_VTR_PWR_WELL_EMUL = 0
	   b[ 4 ] = 32K_SWITCHER_CTRL         = 0 */
	VBAT_REGS->CLOCK_ENABLE = 0x07;

	ulTemp = 256;
	while (ulTemp--)
	{
		__asm volatile( "NOP" );
		__asm volatile( "NOP" );
		__asm volatile( "NOP" );
		__asm volatile( "NOP" );
	}

	/* Disaggregate GIRQ23 & GIRQ24 for FreeRTOS.  Second parameter is a bit-map
	for each GIRQ where
	  0 = Aggregated, 1 = Dis-aggregate
	  Bit position = GIRQ_Number - 8
	  Example: GIRQ23 ( 23 - 8 ) = 15
	  Dis-aggregate GIRQ23 & GIRQ24
	  The symbols JTVIC_DISAGR_BITMAP is generated in header file mec14xx_girqm.h

	  Each disaggregated interrupt handler is spaced 8-bytes apart starting at
	  base address for that GIRQ. */
	jtvic_init( dflt_ih_table, ( JTVIC_DISAGR_BITMAP ), ( JTVIC_FLAG_DISAGR_SPACING_8 ) );

	/* Initialise the LEDs. */
	for( ulTemp = 0; ulTemp < LED_ID_MAX; ulTemp++ )
	{
		led_sleep_en( ulTemp, ADISABLE );
		led_init( ulTemp );
		led_out_high( ulTemp );
	}
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

	/* Run time task stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook	function is
	called if a task stack overflow is detected.  Note the system/interrupt
	stack is not checked. */
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

void vAssertCalled( const char * pcFile, unsigned long ulLine )
{
volatile char *pcFileName;
volatile unsigned long ulLineNumber;

	/* Prevent things that are useful to view in the debugger from being
	optimised away. */
	pcFileName = ( char * ) pcFile;
	( void ) pcFileName;
	ulLineNumber = ulLine;

	/* Set ulLineNumber to 0 in the debugger to break out of this loop and
	return to the line that triggered the assert. */
	while( ulLineNumber != 0 )
	{
		__asm volatile( "NOP" );
		__asm volatile( "NOP" );
		__asm volatile( "NOP" );
		__asm volatile( "NOP" );
		__asm volatile( "NOP" );
	}
}

