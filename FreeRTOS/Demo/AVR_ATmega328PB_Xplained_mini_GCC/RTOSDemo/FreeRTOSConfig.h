/*
 * FreeRTOS V202012.00
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

#ifndef FREERTOS_CONFIG_H
#define FREERTOS_CONFIG_H

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
/* Clock setting. */
#define configCPU_CLOCK_HZ			( ( unsigned long ) 8000000 )
#define configTICK_RATE_HZ			( ( TickType_t ) 1000 )

/* FreeRTOS kernel tick data width. */
#define configUSE_16_BIT_TICKS			1

/* FreeRTOS task configuration. */
#define configMAX_PRIORITIES		( 4 )
#define configMAX_TASK_NAME_LEN		( 8 )

#define configUSE_PREEMPTION		1
#define configUSE_TIME_SLICING		0
#define configIDLE_SHOULD_YIELD		1

#define configUSE_IDLE_HOOK			1
#define configUSE_TICK_HOOK			0

/* FreeRTOS debugging and tracing. */
#define configQUEUE_REGISTRY_SIZE	0
#define configUSE_TRACE_FACILITY	0

/* FreeRTOS software timer. */
#define configUSE_TIMERS				1
#define configTIMER_TASK_PRIORITY		2
#define configTIMER_QUEUE_LENGTH		5 
#define configTIMER_TASK_STACK_DEPTH	configMINIMAL_STACK_SIZE

/* FreeRTOS memory allocation scheme. */
#define configSUPPORT_DYNAMIC_ALLOCATION	1
#define configSUPPORT_STATIC_ALLOCATION		1

/* FreeRTOS memory management. */
#define configMINIMAL_STACK_SIZE	( ( unsigned short ) 90 )
#define configTOTAL_HEAP_SIZE		( (size_t ) ( 1000 ) )

#define configCHECK_FOR_STACK_OVERFLOW		1

/* Set the following definitions to 1 to include the API function, or zero
to exclude the API function. */

#define INCLUDE_vTaskPrioritySet		0
#define INCLUDE_uxTaskPriorityGet		0
#define INCLUDE_vTaskDelete				1
#define INCLUDE_vTaskCleanUpResources	0
#define INCLUDE_vTaskSuspend			0
#define INCLUDE_vTaskDelayUntil			1
#define INCLUDE_vTaskDelay				1

#endif /* FREERTOS_CONFIG_H */
