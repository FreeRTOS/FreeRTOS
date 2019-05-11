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
 * This project provides three demo applications.  A simple blinky style
 * project, a more comprehensive test and demo application, and an lwIP example.
 * The mainSELECTED_APPLICATION setting (defined in this file) is used to
 * select between the three.  The simply blinky demo is implemented and
 * described in main_blinky.c.  The more comprehensive test and demo application
 * is implemented and described in main_full.c.  The lwIP example is implemented
 * and described in main_lwIP.c.
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

/* Demo app includes. */
#include "partest.h"

/* Xilinx includes. */
#include "xtmrctr.h"
#include "xil_cache.h"

/* mainSELECTED_APPLICATION is used to select between three demo applications,
 * as described at the top of this file.
 *
 * When mainSELECTED_APPLICATION is set to 0 the simple blinky example will
 * be run.
 *
 * When mainSELECTED_APPLICATION is set to 1 the comprehensive test and demo
 * application will be run.
 *
 * When mainSELECTED_APPLICATION is set to 2 the lwIP example will be run.
 */
#define mainSELECTED_APPLICATION	0

/*-----------------------------------------------------------*/

/*
 * Configure the hardware as necessary to run this demo.
 */
static void prvSetupHardware( void );

/*
* See the comments at the top of this file and above the
* mainSELECTED_APPLICATION definition.
*/
#if ( mainSELECTED_APPLICATION == 0 )
	extern void main_blinky( void );
#elif ( mainSELECTED_APPLICATION == 1 )
	extern void main_full( void );
#elif ( mainSELECTED_APPLICATION == 2 )
	extern void main_lwIP( void );
#else
	#error Invalid mainSELECTED_APPLICATION setting.  See the comments at the top of this file and above the mainSELECTED_APPLICATION definition.
#endif

/* Prototypes for the standard FreeRTOS callback/hook functions implemented
within this file. */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );

/* The dual timer is used to generate the RTOS tick interrupt and as a time base
for the run time stats. */
static XTmrCtr xTickTimerInstance;

/*-----------------------------------------------------------*/

int main( void )
{
	/* Configure the hardware ready to run the demo. */
	prvSetupHardware();

	/* The mainSELECTED_APPLICATION setting is described at the top
	of this file. */
	#if( mainSELECTED_APPLICATION == 0 )
	{
		main_blinky();
	}
	#elif( mainSELECTED_APPLICATION == 1 )
	{
		main_full();
	}
	#else
	{
		main_lwIP();
	}
	#endif

	/* Don't expect to reach here. */
	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	microblaze_disable_interrupts();

	#if defined( XPAR_MICROBLAZE_USE_ICACHE ) && ( XPAR_MICROBLAZE_USE_ICACHE != 0 )
	{
		Xil_ICacheInvalidate();
		Xil_ICacheEnable();
	}
	#endif

	#if defined( XPAR_MICROBLAZE_USE_DCACHE ) && ( XPAR_MICROBLAZE_USE_DCACHE != 0 )
	{
		Xil_DCacheInvalidate();
		Xil_DCacheEnable();
	}
	#endif

	/* Initialise the LEDs.  ParTest is a historic name which used to stand for
	PARallel port TEST. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
volatile uint32_t ulDummy = 0;

	/* Called if a call to pvPortMalloc() fails because there is insufficient
	free memory available in the FreeRTOS heap.  pvPortMalloc() is called
	internally by FreeRTOS API functions that create tasks, queues, software
	timers, and semaphores.  The size of the FreeRTOS heap is set by the
	configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h.  Force an
	assertion failure. */
	configASSERT( ulDummy != 0 );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected.  Force an assertion
	failure. */
	configASSERT( ( char * ) pxTask == pcTaskName );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	#if( mainSELECTED_APPLICATION == 1 )
	{
		extern void vFullDemoIdleHook( void );

		/* When the full demo is build the idle hook is used to create some
		timers to flash LEDs. */
		vFullDemoIdleHook();
	}
	#endif
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
	#if( mainSELECTED_APPLICATION == 1 )
	{
		extern void vFullDemoTickHook( void );

		/* When the full demo is build the tick hook is used to demonstrate
		functions being called from an interrupt and perform some tests. */
		vFullDemoTickHook();
	}
	#endif
}
/*-----------------------------------------------------------*/

/* This is an application defined callback function used to install the tick
interrupt handler.  It is provided as an application callback because the kernel
will run on lots of different MicroBlaze and FPGA configurations - not all of
which will have the same timer peripherals defined or available.  This example
uses the Dual Timer 0.  If that is available on your hardware platform then this
example callback implementation may not require modification.   The name of the
interrupt handler that must be installed is vPortTickISR(), which the function
below declares as an extern. */
void vApplicationSetupTimerInterrupt( void )
{
portBASE_TYPE xStatus;
const unsigned char ucTickTimerCounterNumber = ( unsigned char ) 0U;
const unsigned char ucRunTimeStatsCounterNumber = ( unsigned char ) 1U;
const unsigned long ulCounterValue = ( ( XPAR_TMRCTR_0_CLOCK_FREQ_HZ / configTICK_RATE_HZ ) - 1UL );
extern void vPortTickISR( void *pvUnused );

	/* Initialise the timer/counter. */
	xStatus = XTmrCtr_Initialize( &xTickTimerInstance, XPAR_TMRCTR_0_DEVICE_ID );

	if( xStatus == XST_SUCCESS )
	{
		/* Install the tick interrupt handler as the timer ISR.
		*NOTE* The xPortInstallInterruptHandler() API function must be used for
		this purpose. */
		xStatus = xPortInstallInterruptHandler( XPAR_INTC_0_TMRCTR_0_VEC_ID, vPortTickISR, NULL );
	}

	if( xStatus == pdPASS )
	{
		/* Enable the timer interrupt in the interrupt controller.
		*NOTE* The vPortEnableInterrupt() API function must be used for this
		purpose. */
		vPortEnableInterrupt( XPAR_INTC_0_TMRCTR_0_VEC_ID );

		/* Configure the timer interrupt handler.  This installs the handler
		directly, rather than through the Xilinx driver.  This is done for
		efficiency. */
		XTmrCtr_SetHandler( &xTickTimerInstance, ( void * ) vPortTickISR, NULL );

		/* Set the correct period for the timer. */
		XTmrCtr_SetResetValue( &xTickTimerInstance, ucTickTimerCounterNumber, ulCounterValue );

		/* Enable the interrupts.  Auto-reload mode is used to generate a
		periodic tick.  Note that interrupts are disabled when this function is
		called, so interrupts will not start to be processed until the first
		task has started to run. */
		XTmrCtr_SetOptions( &xTickTimerInstance, ucTickTimerCounterNumber, ( XTC_INT_MODE_OPTION | XTC_AUTO_RELOAD_OPTION | XTC_DOWN_COUNT_OPTION ) );

		/* Start the timer. */
		XTmrCtr_Start( &xTickTimerInstance, ucTickTimerCounterNumber );




		/* The second timer is used as the time base for the run time stats.
		Auto-reload mode is used to ensure the timer does not stop. */
		XTmrCtr_SetOptions( &xTickTimerInstance, ucRunTimeStatsCounterNumber, XTC_AUTO_RELOAD_OPTION );

		/* Start the timer. */
		XTmrCtr_Start( &xTickTimerInstance, ucRunTimeStatsCounterNumber );
	}

	/* Sanity check that the function executed as expected. */
	configASSERT( ( xStatus == pdPASS ) );
}
/*-----------------------------------------------------------*/

/* This is an application defined callback function used to clear whichever
interrupt was installed by the the vApplicationSetupTimerInterrupt() callback
function.  It is provided as an application callback because the kernel will run
on lots of different MicroBlaze and FPGA configurations - not all of which will
have the same timer peripherals defined or available.  This example uses the
dual timer 0.  If that is available on your hardware platform then this example
callback implementation will not require modification provided the example
definition of vApplicationSetupTimerInterrupt() is also not modified. */
void vApplicationClearTimerInterrupt( void )
{
unsigned long ulCSR;

	/* Clear the timer interrupt */
	ulCSR = XTmrCtr_GetControlStatusReg( XPAR_TMRCTR_0_BASEADDR, 0 );
	XTmrCtr_SetControlStatusReg( XPAR_TMRCTR_0_BASEADDR, 0, ulCSR );
}
/*-----------------------------------------------------------*/

void *malloc( size_t x )
{
	/* Just to check it never gets called as there is no heap defined (other
	than the FreeRTOS heap). */
	for( ;; );
}
/*-----------------------------------------------------------*/

uint32_t ulMainGetRunTimeCounterValue( void )
{
static uint32_t ulOverflows = 0, ulLastTime = 0;
uint32_t ulTimeNow, ulReturn;
const uint32_t ulPrescale = 10, ulTCR2Offset = 24UL;

	ulTimeNow = * ( ( uint32_t * ) ( XPAR_TMRCTR_0_BASEADDR + ulTCR2Offset ) );

	if( ulTimeNow < ulLastTime )
	{
		/* 32 as its a 32-bit number. */
		ulOverflows += ( 1UL << ( 32 - ulPrescale ) );
	}
	ulLastTime = ulTimeNow;

	ulReturn = ( ulTimeNow >> ulPrescale ) + ulOverflows;

	return ulReturn;
}
/*-----------------------------------------------------------*/


