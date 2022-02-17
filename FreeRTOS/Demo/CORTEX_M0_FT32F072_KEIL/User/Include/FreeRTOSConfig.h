/*
 * FreeRTOS V202104.00
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

/* Ensure stdint is only used by the compiler, and not the assembler. */
#if defined(__ICCARM__) || defined(__CC_ARM) || defined(__GNUC__)
  #include <stdint.h>
  extern uint32_t SystemCoreClock;
  void xPortSysTickHandler(void);
  #include <ft32f072x8.h>
#endif

#define mainCREATE_DEMO_ONLY	1


#define configUSE_TICK_HOOK 1
#define configTASK_NOTIFICATION_ARRAY_ENTRIES 3
#define configPRINTF( X ) printf X
#define configMAX_SYSCALL_INTERRUPT_PRIORITY  0
#define configUSE_QUEUE_SETS 1
#define INCLUDE_xTaskAbortDelay 1
#define INCLUDE_xTaskGetHandle 1
#define configUSE_MUTEXES 1
#define INCLUDE_xSemaphoreGetMutexHolder 1

#define configSTART_TASK_NOTIFY_TESTS             0
#define configSTART_TASK_NOTIFY_ARRAY_TESTS       0
#define configSTART_BLOCKING_QUEUE_TESTS          0
#define configSTART_SEMAPHORE_TESTS               0
#define configSTART_POLLED_QUEUE_TESTS            0		
#define configSTART_INTEGER_MATH_TESTS            0
#define configSTART_GENERIC_QUEUE_TESTS           0
#define configSTART_PEEK_QUEUE_TESTS              0
#define configSTART_MATH_TESTS                    0		//set configMINIMAL_STACK_SIZE ( ( unsigned short ) 128 )
#define configSTART_RECURSIVE_MUTEX_TESTS         0
#define configSTART_COUNTING_SEMAPHORE_TESTS      0
#define configSTART_QUEUE_SET_TESTS               0
#define configSTART_QUEUE_OVERWRITE_TESTS         0
#define configSTART_EVENT_GROUP_TESTS             0		//set configMINIMAL_STACK_SIZE ( ( unsigned short ) 128 )
#define configSTART_INTERRUPT_SEMAPHORE_TESTS     0
#define configSTART_QUEUE_SET_POLLING_TESTS       0
#define configSTART_BLOCK_TIME_TESTS              0		  
#define configSTART_ABORT_DELAY_TESTS             0     
#define configSTART_MESSAGE_BUFFER_TESTS          0		//  set configMINIMAL_STACK_SIZE ( ( unsigned short ) 64 );configTICK_RATE_HZ	( ( TickType_t ) 100 )
#define configSTART_STREAM_BUFFER_TESTS           0
#define configSTART_STREAM_BUFFER_INTERRUPT_TESTS 0
#define configSTART_TIMER_TESTS                   0		
#define configSTART_INTERRUPT_QUEUE_TESTS         0
#define configSTART_REGISTER_TESTS                0
#define configSTART_DELETE_SELF_TESTS             0

#define INCLUDE_eTaskGetState 1

#define configUSE_PREEMPTION			1
#define configUSE_IDLE_HOOK				0
#define configUSE_TICK_HOOK				1
#define configCPU_CLOCK_HZ				( SystemCoreClock )
#define tmrTIMER_0_FREQUENCY			( ( TickType_t ) 200 )

#define configTICK_RATE_HZ				( ( TickType_t ) 1000 )
#define configMAX_PRIORITIES			( 5 )
#define configMINIMAL_STACK_SIZE		( ( unsigned short ) 128 )
#define configTOTAL_HEAP_SIZE			( ( size_t ) ( 6144 ) )
#define configMAX_TASK_NAME_LEN			( 15 )
#define configUSE_TRACE_FACILITY		1
#define configUSE_16_BIT_TICKS			0

#define configUSE_MUTEXES				1
#define configQUEUE_REGISTRY_SIZE		8
#define configSUPPORT_DYNAMIC_ALLOCATION 1 
#define configCHECK_FOR_STACK_OVERFLOW	2
#define configUSE_RECURSIVE_MUTEXES		1
#define configUSE_MALLOC_FAILED_HOOK	1
#define configUSE_APPLICATION_TASK_TAG	0
#define configUSE_COUNTING_SEMAPHORES	1
#define configGENERATE_RUN_TIME_STATS	0

/* Co-routine definitions. */
#define configUSE_CO_ROUTINES 			0
#define configMAX_CO_ROUTINE_PRIORITIES ( 2 )

/* Software timer definitions. */
#define configUSE_TIMERS				1
#define configTIMER_TASK_PRIORITY		( 4 )
#define configTIMER_QUEUE_LENGTH		5
#define configTIMER_TASK_STACK_DEPTH	( 80 )
#define INCLUDE_xTimerPendFunctionCall  1
/* Set the following definitions to 1 to include the API function, or zero
to exclude the API function. */
#define INCLUDE_vTaskPrioritySet		1
#define INCLUDE_uxTaskPriorityGet		1
#define INCLUDE_vTaskDelete				1
#define INCLUDE_vTaskCleanUpResources	1
#define INCLUDE_vTaskSuspend			1
#define INCLUDE_vTaskDelayUntil			1
#define INCLUDE_vTaskDelay				1

/* Normal assert() semantics without relying on the provision of an assert.h
header file. */
//#define configASSERT( x ) if( ( x ) == 0 ) { taskDISABLE_INTERRUPTS(); for( ;; ); }

/* Definitions that map the FreeRTOS port interrupt handlers to their CMSIS
standard names - or at least those used in the unmodified vector table. */
#define vPortSVCHandler SVC_Handler
#define xPortPendSVHandler PendSV_Handler
#define xPortSysTickHandler SysTick_Handler

#endif /* FREERTOS_CONFIG_H */

