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

