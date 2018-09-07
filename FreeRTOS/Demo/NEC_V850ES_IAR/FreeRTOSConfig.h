/*
 * FreeRTOS Kernel V10.1.1
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* only include in C files */
#ifdef __IAR_SYSTEMS_ICC__
	#pragma language=extended
	#pragma system_include
	#include <intrinsics.h>
#endif  /* __IAR_SYSTEMS_ICC__ */

/* V850ES/Fx3 Memory Model
 * 1 = Tiny data model
 * 0 = Small/Large data model
 */
#define configDATA_MODE            0



/*
 * Application specific definitions.
 *
 * These definitions should be adjusted for your particular hardware and
 * application requirements.
 *
 * THESE PARAMETERS ARE DESCRIBED WITHIN THE 'CONFIGURATION' SECTION OF THE
 * FreeRTOS API DOCUMENTATION AVAILABLE ON THE FreeRTOS.org WEB SITE.
 */
#define configUSE_PREEMPTION		1
/* only include in C files */

#ifdef __IAR_SYSTEMS_ICC__

	#define configUSE_IDLE_HOOK				0
	#define configUSE_TICK_HOOK				0
	#define configTICK_RATE_HZ				( ( TickType_t ) 1000 )
	#define configMAX_PRIORITIES			( 4 )
	#define configMINIMAL_STACK_SIZE		( ( unsigned short ) 85 )
	#define configMAX_TASK_NAME_LEN			( 10 )
	#define configUSE_TRACE_FACILITY		0
	#define configUSE_16_BIT_TICKS			0
	#define configIDLE_SHOULD_YIELD			0
	#define configUSE_CO_ROUTINES 			0
	#define configUSE_MUTEXES				1
	#define configCHECK_FOR_STACK_OVERFLOW	2
	#define configUSE_RECURSIVE_MUTEXES		1
	#define configQUEUE_REGISTRY_SIZE		0
	#define configUSE_COUNTING_SEMAPHORES	0

	/* Co-routine definitions. */
	#define configUSE_CO_ROUTINES 			0
	#define configMAX_CO_ROUTINE_PRIORITIES ( 2 )

	/* Set the following definitions to 1 to include the API function, or zero
	to exclude the API function. */
	#define INCLUDE_vTaskPrioritySet		1
	#define INCLUDE_uxTaskPriorityGet		1
	#define INCLUDE_vTaskDelete				1
	#define INCLUDE_vTaskCleanUpResources	0
	#define INCLUDE_vTaskSuspend			1
	#define INCLUDE_vTaskDelayUntil			1
	#define INCLUDE_vTaskDelay				1

	/* This IAR workspace contains several different projects - each of which
	is targeted at a different device variant.  The definitions past this point
	are dependent on the variant being used. */
	#ifdef __IAR_V850ES_Fx3__
		#include "io70f3385.h"
		#define configTOTAL_HEAP_SIZE			( (size_t ) ( 20000 ) )
		#define configCPU_CLOCK_HZ				( ( unsigned long ) 48000000 )
	#endif

	#ifdef __IAR_V850ES_Jx3__
		#include "io70f3746.h"
		#define configTOTAL_HEAP_SIZE			( (size_t ) ( 9000 ) )
		#define configCPU_CLOCK_HZ				( ( unsigned long ) 16000000 )
	#endif

	#ifdef __IAR_V850ES_Jx3_L__
		#include "io70f3738.h"
		#define configTOTAL_HEAP_SIZE			( (size_t ) ( 9000 ) )
		#define configCPU_CLOCK_HZ				( ( unsigned long ) 20000000 )
	#endif

	#ifdef __IAR_V850ES_Jx2__
		#include "io70f3717.h"
		#define configTOTAL_HEAP_SIZE			( (size_t ) ( 9000 ) )
		#define configCPU_CLOCK_HZ				( ( unsigned long ) 20000000 )
	#endif

	#ifdef __IAR_V850ES_Hx2__
		#include "io70f3707.h"
		#define configTOTAL_HEAP_SIZE			( (size_t ) ( 9000 ) )
		#define configCPU_CLOCK_HZ				( ( unsigned long ) 20000000 )
	#endif

#endif /* __IAR_SYSTEMS_ICC__ */

#endif /* FREERTOS_CONFIG_H */
