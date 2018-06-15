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

#ifndef FREERTOS_CONFIG_H
#define FREERTOS_CONFIG_H

#include <msp430x44x.h>

/*
Two interrupt examples are provided -

 + Method 1 does everything in C code.
 + Method 2 uses an assembly file wrapper.

Code size:
Method 1 uses assembly macros to save and restore the task context, whereas
method 2 uses functions. This means method 1 will be faster, but method 2 will
use less code space.

Simplicity:
Method 1 is very simplistic, whereas method 2 is more elaborate. This
elaboration results in the code space saving, but also requires a slightly more
complex procedure to define interrupt service routines.

Interrupt efficiency:
Method 1 uses the compiler generated function prologue and epilogue code to save
and restore the necessary registers within an interrupt service routine (other
than the RTOS tick ISR). Should a context switch be required from within the ISR
the entire processor context is saved. This can result in some registers being saved
twice - once by the compiler generated code, and then again by the FreeRTOS code.
Method 2 saves and restores all the processor registers within each interrupt service
routine, whether or not a context switch actually occurs. This means no registers
ever get saved twice, but imposes an overhead on the occasions that no context switch
occurs.
*/

#define configINTERRUPT_EXAMPLE_METHOD 1

/*-----------------------------------------------------------
 * Application specific definitions.
 *
 * These definitions should be adjusted for your particular hardware and
 * application requirements.
 *
 * THESE PARAMETERS ARE DESCRIBED WITHIN THE 'CONFIGURATION' SECTION OF THE
 * FreeRTOS API DOCUMENTATION AVAILABLE ON THE FreeRTOS.org WEB SITE.
 *
 * See http://www.freertos.org/a00110.html
 *----------------------------------------------------------*/

#define configUSE_PREEMPTION		1
#define configUSE_IDLE_HOOK			1
#define configUSE_TICK_HOOK			0
#define configCPU_CLOCK_HZ			( ( unsigned long ) 7995392 ) /* Clock setup from main.c in the demo application. */
#define configTICK_RATE_HZ			( ( TickType_t ) 1000 )
#define configMAX_PRIORITIES		( 4 )
#define configMINIMAL_STACK_SIZE	( ( unsigned short ) 50 )
#define configTOTAL_HEAP_SIZE		( ( size_t ) ( 1700 ) )
#define configMAX_TASK_NAME_LEN		( 8 )
#define configUSE_TRACE_FACILITY	0
#define configUSE_16_BIT_TICKS		1
#define configIDLE_SHOULD_YIELD		1

/* Co-routine definitions. */
#define configUSE_CO_ROUTINES 		0
#define configMAX_CO_ROUTINE_PRIORITIES ( 2 )

/* Set the following definitions to 1 to include the API function, or zero
to exclude the API function. */

#define INCLUDE_vTaskPrioritySet			0
#define INCLUDE_uxTaskPriorityGet			0
#define INCLUDE_vTaskDelete					1
#define INCLUDE_vTaskCleanUpResources		0
#define INCLUDE_vTaskSuspend				0
#define INCLUDE_vTaskDelayUntil				1
#define INCLUDE_vTaskDelay					1
#define INCLUDE_uxTaskGetStackHighWaterMark 0

#endif /* FREERTOS_CONFIG_H */
