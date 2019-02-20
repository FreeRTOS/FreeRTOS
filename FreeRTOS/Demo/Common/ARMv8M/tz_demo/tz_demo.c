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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Non-Secure callable functions. */
#include "nsc_functions.h"

/**
 * @brief Counter incremented in the callback which is called from the secure
 * side.
 *
 * The size of an MPU region must be a multiple of 32 bytes. Therefore we need
 * to declare an array of size 8 to ensure that the total size is 32 bytes -
 * even though we only need 4 bytes. If we do not do that, anything placed after
 * 4 bytes and upto 32 bytes will also fall in the same MPU region and the task
 * having access to ulNonSecureCounter will also have access to all those items.
 */
static uint32_t ulNonSecureCounter[8] __attribute__( ( aligned( 32 ) ) ) = { 0 };
/*-----------------------------------------------------------*/

/**
 * @brief Creates all the tasks for TZ demo.
 */
void vStartTZDemo( void );

/**
 * @brief Increments the ulNonSecureCounter.
 *
 * This function is called from the secure side.
 */
static void prvCallback( void );

/**
 * @brief Implements the task which calls the functions exported from the secure
 * side.
 *
 * @param pvParameters[in] Parameters as passed during task creation.
 */
static void prvSecureCallingTask( void * pvParameters );
/*-----------------------------------------------------------*/

void vStartTZDemo( void )
{
static StackType_t xSecureCallingTaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( 32 ) ) );
TaskParameters_t xSecureCallingTaskParameters =
{
	.pvTaskCode		= prvSecureCallingTask,
	.pcName			= "SecCalling",
	.usStackDepth	= configMINIMAL_STACK_SIZE,
	.pvParameters	= NULL,
	.uxPriority		= tskIDLE_PRIORITY,
	.puxStackBuffer	= xSecureCallingTaskStack,
	.xRegions		=	{
							{ ulNonSecureCounter,	32,	tskMPU_REGION_READ_WRITE | tskMPU_REGION_EXECUTE_NEVER	},
							{ 0,					0,	0														},
							{ 0,					0,	0														},
						}
};

	/* Create an unprivileged task which calls secure functions. */
	xTaskCreateRestricted( &( xSecureCallingTaskParameters ), NULL );
}
/*-----------------------------------------------------------*/

static void prvCallback( void )
{
	/* This function is called from the secure side. Just increment the counter
	 * here. The check that this counter keeps incrementing is performed in the
	 * prvSecureCallingTask. */
	ulNonSecureCounter[ 0 ] += 1;
}
/*-----------------------------------------------------------*/

static void prvSecureCallingTask( void * pvParameters )
{
uint32_t ulLastSecureCounter = 0, ulLastNonSecureCounter = 0;
uint32_t ulCurrentSecureCounter = 0;

	/* This task calls secure side functions. So allocate a secure context for
	 * it. */
	portALLOCATE_SECURE_CONTEXT( configMINIMAL_SECURE_STACK_SIZE );

	for( ; ; )
	{
		/* Call the secure side function. It does two things:
		 * - It calls the supplied function (prvCallback) which in turn
		 *   increments the non-secure counter.
		 * - It increments the secure counter and returns the incremented value.
		 * Therefore at the end of this function call both the secure and
		 * non-secure counters must have been incremented.
		 */
		ulCurrentSecureCounter = NSCFunction( prvCallback );

		/* Make sure that both the counters are incremented. */
		configASSERT( ulCurrentSecureCounter == ulLastSecureCounter + 1 );
		configASSERT( ulNonSecureCounter[ 0 ] == ulLastNonSecureCounter + 1 );

		/* Update the last values for both the counters. */
		ulLastSecureCounter = ulCurrentSecureCounter;
		ulLastNonSecureCounter = ulNonSecureCounter[ 0 ];

		/* Wait for a second. */
		vTaskDelay( pdMS_TO_TICKS( 1000 ) );
	}
}
/*-----------------------------------------------------------*/
