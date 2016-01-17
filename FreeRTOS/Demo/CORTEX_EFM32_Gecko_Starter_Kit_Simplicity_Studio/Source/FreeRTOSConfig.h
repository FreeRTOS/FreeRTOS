/*
 *  FreeRTOS V7.4.2 - Copyright (C) 2013 Real Time Engineers Ltd.
 *
 *  FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
 *  http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.
 *
 ***************************************************************************
 *                                                                       *
 *    FreeRTOS tutorial books are available in pdf and paperback.        *
 *    Complete, revised, and edited pdf reference manuals are also       *
 *    available.                                                         *
 *                                                                       *
 *    Purchasing FreeRTOS documentation will not only help you, by       *
 *    ensuring you get running as quickly as possible and with an        *
 *    in-depth knowledge of how to use FreeRTOS, it will also help       *
 *    the FreeRTOS project to continue with its mission of providing     *
 *    professional grade, cross platform, de facto standard solutions    *
 *    for microcontrollers - completely free of charge!                  *
 *                                                                       *
 *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
 *                                                                       *
 *    Thank you for using FreeRTOS, and thank you for your support!      *
 *                                                                       *
 ***************************************************************************
 *
 *
 *  This file is part of the FreeRTOS distribution.
 *
 *  FreeRTOS is free software; you can redistribute it and/or modify it under
 *  the terms of the GNU General Public License (version 2) as published by the
 *  Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
 *
 *  >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
 *  distribute a combined work that includes FreeRTOS without being obliged to
 *  provide the source code for proprietary components outside of the FreeRTOS
 *  kernel.
 *
 *  FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
 *  WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 *  FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
 *  details. You should have received a copy of the GNU General Public License
 *  and the FreeRTOS license exception along with FreeRTOS; if not it can be
 *  viewed here: http://www.freertos.org/a00114.html and also obtained by
 *  writing to Real Time Engineers Ltd., contact details for whom are available
 *  on the FreeRTOS WEB site.
 *
 *  1 tab == 4 spaces!
 *
 ***************************************************************************
 *                                                                       *
 *    Having a problem?  Start by reading the FAQ "My application does   *
 *    not run, what could be wrong?"                                     *
 *                                                                       *
 *    http://www.FreeRTOS.org/FAQHelp.html                               *
 *                                                                       *
 ***************************************************************************
 *
 *
 *  http://www.FreeRTOS.org - Documentation, books, training, latest versions,
 *  license and Real Time Engineers Ltd. contact details.
 *
 *  http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
 *  including FreeRTOS+Trace - an indispensable productivity tool, and our new
 *  fully thread aware and reentrant UDP/IP stack.
 *
 *  http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
 *  Integrity Systems, who sell the code with commercial support,
 *  indemnification and middleware, under the OpenRTOS brand.
 *
 *  http://www.SafeRTOS.com - High Integrity Systems also provide a safety
 *  engineered and independently SIL3 certified version for use in safety and
 *  mission critical applications that require provable dependability.
 */

#ifndef FREERTOS_CONFIG_H
#define FREERTOS_CONFIG_H

#include "em_assert.h"

#ifdef __cplusplus
extern "C" {
#endif

/********************** Configuration of FreeRTOS ****************************/

/* Implement FreeRTOS configASSERT as emlib assert */
#define configASSERT( x )       if( ( x ) == 0 ) { taskDISABLE_INTERRUPTS(); for( ;; ); }

/* Modes of operations of operation system*/
#define configUSE_PREEMPTION       ( 1 )

/* Energy saving modes */
#define configUSE_TICKLESS_IDLE    ( 0 )
/* Available options when configUSE_TICKLESS_IDLE set to 1
 * or configUSE_SLEEP_MODE_IN_IDLE set to 1 :
 * 1 - EM1, 2 - EM2, 3 - EM3, timer in EM3 is not very accurate*/
#define configSLEEP_MODE           ( 2 )

/* Definition used only if configUSE_TICKLESS_IDLE == 0 */
#define configUSE_SLEEP_MODE_IN_IDLE       ( 0 )


/* EM1 use systick as system clock*/
/* EM2 use crystal 32768Hz and RTC Component as system clock
 * We use 2 times divider of this clock to reduce energy consumtion
 * You can also in this mode choose crystal oscillator to get more preccision in
 * time measurement or RC oscillator for more energy reduction.*/
/* EM3 use 2kHz RC and BURTC Component as system clock*/
#if ( ( configSLEEP_MODE == 2 ) && ( configUSE_TICKLESS_IDLE == 1 || configUSE_SLEEP_MODE_IN_IDLE == 1 ) )
/* Choose source of clock for RTC (system tick)
 * if configCRYSTAL_IN_EM2 set to 1 then Crystal oscillator is used,
 * when 0 RC oscillator */
#define configCRYSTAL_IN_EM2    ( 1 )
#endif
#if (  (configSLEEP_MODE == 2 ) && ( configUSE_TICKLESS_IDLE == 1 || configUSE_SLEEP_MODE_IN_IDLE == 1 ) )
/* When we use EM2 or EM3 System clock has got low frequency,
 * so we reduce Tick rate to 100 Hz and 40 Hz, which give more clock cycles between ticks*/
#define configTICK_RATE_HZ    ( 100 )
#elif (  ( configSLEEP_MODE == 3 ) && ( configUSE_TICKLESS_IDLE == 1 || configUSE_SLEEP_MODE_IN_IDLE == 1 ) )
#define configTICK_RATE_HZ    ( 40 )
#else
#define configTICK_RATE_HZ    ( 1000 )
#endif

/* Definition used by Keil to replace default system clock source when we use EM2 or EM3 mode. */
#if ( ( configSLEEP_MODE == 2 || configSLEEP_MODE == 3 ) && ( configUSE_TICKLESS_IDLE == 1 || configUSE_SLEEP_MODE_IN_IDLE == 1 ) )
#define configOVERRIDE_DEFAULT_TICK_CONFIGURATION ( 1 )
#endif

/* Main functions*/
#define configMAX_PRIORITIES                      ( 6 )
#define configUSE_PORT_OPTIMISED_TASK_SELECTION	( 1 )
#define configMINIMAL_STACK_SIZE                  (( unsigned short ) 140)
#define configTOTAL_HEAP_SIZE                     (( size_t )(40000))
#define configMAX_TASK_NAME_LEN                   ( 10 )
#define configUSE_TRACE_FACILITY                  ( 0 )
#define configUSE_16_BIT_TICKS                    ( 0 )
#define configIDLE_SHOULD_YIELD                   ( 0 )
#define configUSE_MUTEXES                         ( 1 )
#define configUSE_RECURSIVE_MUTEXES               ( 1 )
#define configUSE_COUNTING_SEMAPHORES             ( 1 )
#define configUSE_ALTERNATIVE_API                 ( 0 )/* Deprecated! */
#define configQUEUE_REGISTRY_SIZE                 ( 10 )
#define configUSE_QUEUE_SETS                      ( 0 )

/* Hook function related definitions. */
#define configUSE_TICK_HOOK                       ( 1 )
#define configCHECK_FOR_STACK_OVERFLOW            ( 2 )
#define configUSE_MALLOC_FAILED_HOOK              ( 1 )

/* Run time stats gathering related definitions. */
#define configGENERATE_RUN_TIME_STATS             ( 0 )

/* Co-routine related definitions. */
#define configUSE_CO_ROUTINES                     ( 0 )
#define configMAX_CO_ROUTINE_PRIORITIES           ( 1 )

/* Software timer related definitions. */
#define configUSE_TIMERS                          ( 1 )
#define configTIMER_TASK_PRIORITY                 ( configMAX_PRIORITIES - 1 ) /* Highest priority */
#define configTIMER_QUEUE_LENGTH                  ( 10 )
#define configTIMER_TASK_STACK_DEPTH              ( configMINIMAL_STACK_SIZE )

/* Interrupt nesting behaviour configuration. */
#define configKERNEL_INTERRUPT_PRIORITY           ( 255 )
#define configMAX_SYSCALL_INTERRUPT_PRIORITY      ( 191 ) /* equivalent to 0xa0, or priority 5. */

/* Optional functions - most linkers will remove unused functions anyway. */
#define INCLUDE_vTaskPrioritySet                  ( 1 )
#define INCLUDE_uxTaskPriorityGet                 ( 1 )
#define INCLUDE_vTaskDelete                       ( 1 )
#define INCLUDE_vTaskSuspend                      ( 1 )
#define INCLUDE_xResumeFromISR                    ( 1 )
#define INCLUDE_vTaskDelayUntil                   ( 1 )
#define INCLUDE_vTaskDelay                        ( 1 )
#define INCLUDE_xTaskGetSchedulerState            ( 1 )
#define INCLUDE_xTaskGetCurrentTaskHandle         ( 1 )
#define INCLUDE_uxTaskGetStackHighWaterMark       ( 0 )
#define INCLUDE_xTaskGetIdleTaskHandle            ( 0 )
#define INCLUDE_xTimerGetTimerDaemonTaskHandle    ( 0 )
#define INCLUDE_pcTaskGetTaskName                 ( 0 )
#define INCLUDE_eTaskGetState                     ( 1 )
#define INCLUDE_xTimerPendFunctionCall            ( 1 )

/* Default value of CPU clock (RC)*/
#define configCPU_CLOCK_HZ                        (( unsigned long ) 14000000)

/* Defines used in energy modes */
#if ( ( configSLEEP_MODE == 2 )  && ( ( configUSE_SLEEP_MODE_IN_IDLE == 1 ) || ( configUSE_TICKLESS_IDLE == 1 ) ) )
        #define configSYSTICK_CLOCK_HZ    ( 16384 )
#endif

#if ( ( configSLEEP_MODE == 3 )  && ( ( configUSE_SLEEP_MODE_IN_IDLE == 1 ) || ( configUSE_TICKLESS_IDLE == 1 ) ) )
       #define configSYSTICK_CLOCK_HZ    ( 2000 )
#endif

#if ( ( configUSE_TICKLESS_IDLE == 0 ) && ( configUSE_SLEEP_MODE_IN_IDLE == 1 ) )
#define configUSE_IDLE_HOOK  ( 1 )
#else
#define configUSE_IDLE_HOOK  ( 0 )
#endif

/*-----------------------------------------------------------*/


/* Definitions that map the FreeRTOS port interrupt handlers to their CMSIS
 * standard names. */
#define vPortSVCHandler        SVC_Handler
#define xPortPendSVHandler     PendSV_Handler
#define xPortSysTickHandler    SysTick_Handler


#define fabs __builtin_fabs

#ifdef __cplusplus
}
#endif
#endif /* FREERTOS_CONFIG_H */

