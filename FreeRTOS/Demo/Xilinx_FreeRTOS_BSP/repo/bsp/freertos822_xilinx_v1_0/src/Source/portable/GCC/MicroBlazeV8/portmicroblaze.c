/*
    FreeRTOS V8.2.1 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Xilinx includes. */
#include "xil_printf.h"
#include "xparameters.h"

#if defined( XPAR_XTMRCTR_NUM_INSTANCES )
	#if( XPAR_XTMRCTR_NUM_INSTANCES > 0 )
		#include "xtmrctr.h"
		/* The timer is used to generate the RTOS tick interrupt. */
		static XTmrCtr xTickTimerInstance;
	#endif
#endif

/*
 * Some FreeRTOSConfig.h settings require the application writer to provide the
 * implementation of a callback function that has a specific name, and a linker
 * error will result if the application does not provide the required function.
 * To avoid the risk of a configuration file setting resulting in a linker error
 * this file provides default implementations of each callback that might be
 * required.  The default implementations are declared as weak symbols to allow
 * the application writer to override the default implementation by providing
 * their own implementation in the application itself.
 */
void vApplicationAssert( const char *pcFileName, uint32_t ulLine ) __attribute__((weak));
void vApplicationTickHook( void ) __attribute__((weak));
void vApplicationIdleHook( void ) __attribute__((weak));
void vApplicationMallocFailedHook( void ) __attribute((weak));
void vApplicationStackOverflowHook( TaskHandle_t xTask, char *pcTaskName ) __attribute__((weak));
void vApplicationSetupTimerInterrupt( void ) __attribute__((weak));
void vApplicationClearTimerInterrupt( void ) __attribute__((weak));

/*-----------------------------------------------------------*/


/* This version of vApplicationAssert() is declared as a weak symbol to allow it
to be overridden by a version implemented within the application that is using
this BSP. */
void vApplicationAssert( const char *pcFileName, uint32_t ulLine )
{
volatile uint32_t ul = 0;
volatile const char *pcLocalFileName = pcFileName; /* To prevent pcFileName being optimized away. */
volatile uint32_t ulLocalLine = ulLine; /* To prevent ulLine being optimized away. */

	/* Prevent compile warnings about the following two variables being set but
	not referenced.  They are intended for viewing in the debugger. */
	( void ) pcLocalFileName;
	( void ) ulLocalLine;

	xil_printf( "Assert failed in file %s, line %lu\r\n", pcLocalFileName, ulLocalLine );

	/* If this function is entered then a call to configASSERT() failed in the
	FreeRTOS code because of a fatal error.  The pcFileName and ulLine
	parameters hold the file name and line number in that file of the assert
	that failed.  Additionally, if using the debugger, the function call stack
	can be viewed to find which line failed its configASSERT() test.  Finally,
	the debugger can be used to set ul to a non-zero value, then step out of
	this function to find where the assert function was entered. */
	taskENTER_CRITICAL();
	{
		while( ul == 0 )
		{
			__asm volatile( "NOP" );
		}
	}
	taskEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

/* This default tick hook does nothing and is declared as a weak symbol to allow
the application writer to override this default by providing their own
implementation in the application code. */
void vApplicationTickHook( void )
{
}
/*-----------------------------------------------------------*/

/* This default idle hook does nothing and is declared as a weak symbol to allow
the application writer to override this default by providing their own
implementation in the application code. */
void vApplicationIdleHook( void )
{
}
/*-----------------------------------------------------------*/

/* This default malloc failed hook does nothing and is declared as a weak symbol
to allow the application writer to override this default by providing their own
implementation in the application code. */
void vApplicationMallocFailedHook( void )
{
	xil_printf( "vApplicationMallocFailedHook() called\n" );
}
/*-----------------------------------------------------------*/

/* This default stack overflow hook will stop the application for executing.  It
is declared as a weak symbol to allow the application writer to override this
default by providing their own implementation in the application code. */
void vApplicationStackOverflowHook( TaskHandle_t xTask, char *pcTaskName )
{
/* Attempt to prevent the handle and name of the task that overflowed its stack
from being optimised away because they are not used. */
volatile TaskHandle_t xOverflowingTaskHandle = xTask;
volatile char *pcOverflowingTaskName = pcTaskName;

	( void ) xOverflowingTaskHandle;
	( void ) pcOverflowingTaskName;

	xil_printf( "HALT: Task %s overflowed its stack.", pcOverflowingTaskName );
	portDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

#if defined( XPAR_XTMRCTR_NUM_INSTANCES )
	#if( XPAR_XTMRCTR_NUM_INSTANCES > 0 )
		/* This is a default implementation of what is otherwise an application defined
		callback function used to install the tick interrupt handler.  It is provided as
		an application callback because the kernel will run on lots of different
		MicroBlaze and FPGA configurations - not all of which will have the same timer
		peripherals defined or available.  vApplicationSetupTimerInterrupt() is declared
		as a weak symbol, allowing the application writer to provide their own
		implementation, if this default implementation is not suitable. */
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
	#endif /* XPAR_XTMRCTR_NUM_INSTANCES > 0 */
#endif /* XPAR_XTMRCTR_NUM_INSTANCES */
/*-----------------------------------------------------------*/

#if defined( XPAR_XTMRCTR_NUM_INSTANCES )
	#if( XPAR_XTMRCTR_NUM_INSTANCES > 0 )
		/* This is a default implementation of what is otherwise an application defined
		callback function used to clear whichever timer interrupt is used to generate
		the tick interrupt.  It is provided as an application callback because the
		kernel will run on lots of different MicroBlaze and FPGA configurations - not
		all of which will have the same timer peripherals defined or available.
		vApplicationSetupTimerInterrupt() is declared as a weak symbol, allowing the
		application writer to provide their own implementation, if this default
		implementation is not suitable. */
		void vApplicationClearTimerInterrupt( void )
		{
		unsigned long ulCSR;

			/* Clear the timer interrupt */
			ulCSR = XTmrCtr_GetControlStatusReg( XPAR_TMRCTR_0_BASEADDR, 0 );
			XTmrCtr_SetControlStatusReg( XPAR_TMRCTR_0_BASEADDR, 0, ulCSR );
		}
	#endif /* XPAR_XTMRCTR_NUM_INSTANCES > 0 */
#endif /* XPAR_XTMRCTR_NUM_INSTANCES */
