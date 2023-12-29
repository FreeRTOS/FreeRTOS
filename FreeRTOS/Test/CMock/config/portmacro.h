/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/*
 *  Changes from V3.2.3
 *
 + Modified portENTER_SWITCHING_ISR() to allow use with GCC V4.0.1.
 +
 +  Changes from V3.2.4
 +
 + Removed the use of the %0 parameter within the assembler macros and
 +    replaced them with hard coded registers.  This will ensure the
 +    assembler does not select the link register as the temp register as
 +    was occasionally happening previously.
 +
 + The assembler statements are now included in a single asm block rather
 +    than each line having its own asm block.
 +
 +  Changes from V4.5.0
 +
 + Removed the portENTER_SWITCHING_ISR() and portEXIT_SWITCHING_ISR() macros
 +    and replaced them with portYield_FROM_ISR() macro.  Application code
 +    should now make use of the portSAVE_CONTEXT() and portRESTORE_CONTEXT()
 +    macros as per the V4.5.1 demo code.
 */

#ifndef PORTMACRO_H
#define PORTMACRO_H

/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/*-----------------------------------------------------------
 * Port specific definitions.
 *
 * The settings in this file configure FreeRTOS correctly for the
 * given hardware and compiler.
 *
 * These settings should not be altered.
 *-----------------------------------------------------------
 */

#include <stdint.h>

/* Type definitions. */
#define portCHAR          char
#define portFLOAT         float
#define portDOUBLE        double
#define portLONG          long
#define portSHORT         short
#define portSTACK_TYPE    uint32_t
#define portBASE_TYPE     long

typedef portSTACK_TYPE   StackType_t;
typedef long             BaseType_t;
typedef unsigned long    UBaseType_t;


#if ( configUSE_16_BIT_TICKS == 1 )
    typedef uint16_t     TickType_t;
    #define portMAX_DELAY        ( TickType_t ) 0xffff
#else
    typedef uint32_t     TickType_t;
    #define portMAX_DELAY        ( TickType_t ) 0xffffffffUL
#endif
#define portPOINTER_SIZE_TYPE    uint64_t
/*-----------------------------------------------------------*/

/* Requires definition of UBaseType_t */
#include "fake_port.h"
#include <FreeRTOS.h>

/* Hardware specifics. */
#define portTICK_PERIOD_MS    ( ( TickType_t ) 1000 / configTICK_RATE_HZ )
#define portBYTE_ALIGNMENT    8
#define portNOP()    __asm volatile ( "NOP" )

/*
 * These define the timer to use for generating the tick interrupt.
 * They are put in this file so they can be shared between "port.c"
 * and "portisr.c".
 */
#define portTIMER_REG_BASE_PTR
#define portTIMER_CLK_ENABLE_BIT
#define portTIMER_AIC_CHANNEL

/*-----------------------------------------------------------*/

/* Task utilities. */

/*
 * portRESTORE_CONTEXT, portRESTORE_CONTEXT, portENTER_SWITCHING_ISR
 * and portEXIT_SWITCHING_ISR can only be called from ARM mode, but
 * are included here for efficiency.  An attempt to call one from
 * THUMB mode code will result in a compile time error.
 */

#define portRESTORE_CONTEXT()
/*-----------------------------------------------------------*/

#define portSAVE_CONTEXT()
#define portYIELD()                      vFakePortYield()
#define portYIELD_WITHIN_API()           vFakePortYieldWithinAPI()
#define portYIELD_FROM_ISR()             vFakePortYieldFromISR()

/* Critical section handling. */
#define portDISABLE_INTERRUPTS()         vFakePortDisableInterrupts()
#define portENABLE_INTERRUPTS()          vFakePortEnableInterrupts()
#define portCLEAR_INTERRUPT_MASK_FROM_ISR( x ) \
    vFakePortClearInterruptMaskFromISR( x )
#define portSET_INTERRUPT_MASK_FROM_ISR() \
    ulFakePortSetInterruptMaskFromISR()
#define portSET_INTERRUPT_MASK()         ulFakePortSetInterruptMask()
#define portCLEAR_INTERRUPT_MASK( x )    vFakePortClearInterruptMask( x )
#define portASSERT_IF_INTERRUPT_PRIORITY_INVALID() \
    vFakePortAssertIfInterruptPriorityInvalid()
#define portENTER_CRITICAL()             vFakePortEnterCriticalSection()
#define portEXIT_CRITICAL()              vFakePortExitCriticalSection()
#define portGET_ISR_LOCK()               vFakePortGetISRLock()
#define portRELEASE_ISR_LOCK()           vFakePortReleaseISRLock()
#define portGET_TASK_LOCK()              vFakePortGetTaskLock()
#define portRELEASE_TASK_LOCK()          vFakePortReleaseTaskLock()

#define portCHECK_IF_IN_ISR()            vFakePortCheckIfInISR()
#define portRESTORE_INTERRUPTS( x )      vFakePortRestoreInterrupts( x )
#define portPRE_TASK_DELETE_HOOK( pvTaskToDelete, pxPendYield ) \
    vPortCurrentTaskDying( ( pvTaskToDelete ), ( pxPendYield ) )
#define portSETUP_TCB( pxTCB )           portSetupTCB_CB( pxTCB );
#define  portASSERT_IF_IN_ISR()          vFakePortAssertIfISR();

#define portGET_CORE_ID()                vFakePortGetCoreID()
#define portYIELD_CORE( x )              vFakePortYieldCore( x )

#define portENTER_CRITICAL_FROM_ISR    vFakePortEnterCriticalFromISR
#define portEXIT_CRITICAL_FROM_ISR     vFakePortExitCriticalFromISR

#if ( configNUMBER_OF_CORES > 1 )
    #define portTASK_FUNCTION_PROTO( vFunction, pvParameters )    void vFunction( void * pvParameters )
    #define portTASK_FUNCTION( vFunction, pvParameters )          void vFunction( void * pvParameters )
#else
    #define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) \
    volatile int fool_static = 0;                              \
    void vFunction( void * ( pvParameters ) )

    #define portTASK_FUNCTION( vFunction, pvParameters ) \
    volatile int fool_static2 = 0;                       \
    void vFunction( void * ( pvParameters ) )
#endif

#if ( configUSE_PORT_OPTIMISED_TASK_SELECTION == 1 )
    static uint8_t ucPortCountLeadingZeros( uint32_t ulBitmap )
    {
        uint8_t ucReturn;

        ucReturn = __builtin_clz( ulBitmap );
        return ucReturn;
    }

    #define portRECORD_READY_PRIORITY( uxPriority, uxReadyPriorities ) \
    ( uxReadyPriorities ) |= ( 1UL << ( uxPriority ) )
    #define portRESET_READY_PRIORITY( uxPriority, uxReadyPriorities ) \
    ( uxReadyPriorities ) &= ~( 1UL << ( uxPriority ) )
    #define portGET_HIGHEST_PRIORITY( uxTopPriority, uxReadyPriorities ) \
    uxTopPriority = ( 31UL - ( uint32_t ) ucPortCountLeadingZeros( ( uxReadyPriorities ) ) )
#endif /* if ( configUSE_PORT_OPTIMISED_TASK_SELECTION == 1 ) */

/* We need to define it here because CMock does not recognize the
 * #if ( portUSING_MPU_WRAPPERS == 1 ) guard around xTaskGetMPUSettings
 * and then complains about the missing xMPU_SETTINGS type in the
 * generated mocks. */
typedef struct MPU_SETTINGS
{
    uint32_t ulDummy;
} xMPU_SETTINGS;

/*-----------------------------------------------------------*/

/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */
#endif /* PORTMACRO_H */
