/*
    FreeRTOS V9.0.0rc1 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

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


/**
 * Creates eight tasks, each of which flash an LED at a different rate.  The first 
 * LED flashes every 125ms, the second every 250ms, the third every 375ms, etc.
 *
 * The LED flash tasks provide instant visual feedback.  They show that the scheduler 
 * is still operational.
 *
 * The PC port uses the standard parallel port for outputs, the Flashlite 186 port 
 * uses IO port F.
 *
 * \page flashC flash.c
 * \ingroup DemoFiles
 * <HR>
 */

/*
Changes from V2.0.0

	+ Delay periods are now specified using variables and constants of
	  TickType_t rather than unsigned long.

Changes from V2.1.1

	+ The stack size now uses configMINIMAL_STACK_SIZE.
	+ String constants made file scope to decrease stack depth on 8051 port.
*/

#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo program include files. */
#include "partest.h"
#include "flash.h"
#include "print.h"

#define ledSTACK_SIZE		configMINIMAL_STACK_SIZE

/* Structure used to pass parameters to the LED tasks. */
typedef struct LED_PARAMETERS
{
	unsigned portBASE_TYPE uxLED;		/*< The output the task should use. */
	TickType_t xFlashRate;	/*< The rate at which the LED should flash. */
} xLEDParameters;

/* The task that is created eight times - each time with a different xLEDParaemtes 
structure passed in as the parameter. */
static void vLEDFlashTask( void *pvParameters );

/* String to print if USE_STDIO is defined. */
const char * const pcTaskStartMsg = "LED flash task started.\r\n";

/*-----------------------------------------------------------*/

void vStartLEDFlashTasks( unsigned portBASE_TYPE uxPriority )
{
unsigned portBASE_TYPE uxLEDTask;
xLEDParameters *pxLEDParameters;
const unsigned portBASE_TYPE uxNumOfLEDs = 8;
const TickType_t xFlashRate = 125;

	/* Create the eight tasks. */
	for( uxLEDTask = 0; uxLEDTask < uxNumOfLEDs; ++uxLEDTask )
	{
		/* Create and complete the structure used to pass parameters to the next 
		created task. */
		pxLEDParameters = ( xLEDParameters * ) pvPortMalloc( sizeof( xLEDParameters ) );
		pxLEDParameters->uxLED = uxLEDTask;
		pxLEDParameters->xFlashRate = ( xFlashRate + ( xFlashRate * ( TickType_t ) uxLEDTask ) );
		pxLEDParameters->xFlashRate /= portTICK_PERIOD_MS;

		/* Spawn the task. */
		xTaskCreate( vLEDFlashTask, "LEDx", ledSTACK_SIZE, ( void * ) pxLEDParameters, uxPriority, ( TaskHandle_t * ) NULL );
	}
}
/*-----------------------------------------------------------*/

static void vLEDFlashTask( void *pvParameters )
{
xLEDParameters *pxParameters;

	/* Queue a message for printing to say the task has started. */
	vPrintDisplayMessage( &pcTaskStartMsg );

	pxParameters = ( xLEDParameters * ) pvParameters;

	for(;;)
	{
		/* Delay for half the flash period then turn the LED on. */
		vTaskDelay( pxParameters->xFlashRate / ( TickType_t ) 2 );
		vParTestToggleLED( pxParameters->uxLED );

		/* Delay for half the flash period then turn the LED off. */
		vTaskDelay( pxParameters->xFlashRate / ( TickType_t ) 2 );
		vParTestToggleLED( pxParameters->uxLED );
	}
}

