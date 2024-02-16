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

#ifndef PORTMACRO_H
#define PORTMACRO_H

/*
 * portmacro.h is an architecture specific file defining certain
 * constants and declaring certain functions.
 *
 * This portmacro file is defined in the CBMC directory and aims
 * to be architecture-independent, with all constants defined with '#ifndef'.
 * Hence, each proof can override the definitions they want to modify
 * in the proof-specific makefiles and the remaining constants will take
 * default values from the definitions in this file.
 *
 * The default values in this portmacro are a combination of the
 * values from the portmacros of FreeRTOSKernel/portable/MSVC-MingW
 * and FreeRTOSKernel/portable/IAR/ARM_CM33/non_secure.
 * They cover almost all the constants needed in the kernel.
 * If a specific proof needs some constant not available in this
 * file, one can directly define the constant in that proof's makefile.
 * To add additional constants to this file, use the '#ifndef' style
 * from below to ensure that the constants can be overridden in
 * specific proofs.
 */

/******************************************************************************
*   Defines
******************************************************************************/
/* Type definitions. */
#ifndef portCHAR
    #define portCHAR                 char
#endif
#ifndef portFLOAT
    #define portFLOAT                float
#endif
#ifndef portDOUBLE
    #define portDOUBLE               double
#endif
#ifndef portLONG
    #define portLONG                 long
#endif
#ifndef portSHORT
    #define portSHORT                short
#endif
#ifndef portSTACK_TYPE
    #define portSTACK_TYPE           size_t
#endif
#ifndef portBASE_TYPE
    #define portBASE_TYPE            long
#endif
#ifndef portPOINTER_SIZE_TYPE
    #define portPOINTER_SIZE_TYPE    size_t
#endif

typedef portSTACK_TYPE   StackType_t;
typedef long             BaseType_t;
typedef unsigned long    UBaseType_t;


#if ( configUSE_16_BIT_TICKS == 1 )
    typedef uint16_t     TickType_t;
    #define portMAX_DELAY              ( TickType_t ) 0xffff
#else
    typedef uint32_t     TickType_t;
    #define portMAX_DELAY              ( TickType_t ) 0xffffffffUL

/* 32/64-bit tick type on a 32/64-bit architecture, so reads of the tick
 * count do not need to be guarded with a critical section. */
    #define portTICK_TYPE_IS_ATOMIC    1
#endif

/* Hardware specifics. */
#ifndef portSTACK_GROWTH
    #define portSTACK_GROWTH      ( -1 )
#endif
#ifndef portTICK_PERIOD_MS
    #define portTICK_PERIOD_MS    ( ( TickType_t ) 1000 / configTICK_RATE_HZ )
#endif
#ifndef portINLINE
    #define portINLINE            __inline
#endif

#if defined( __x86_64__ ) || defined( _M_X64 )
    #define portBYTE_ALIGNMENT    8
#else
    #define portBYTE_ALIGNMENT    4
#endif

#define portYIELD()    vPortGenerateSimulatedInterrupt( portINTERRUPT_YIELD )

extern volatile BaseType_t xInsideInterrupt;
/*#define portSOFTWARE_BARRIER() while( xInsideInterrupt != pdFALSE ) */


/* Simulated interrupts return pdFALSE if no context switch should be performed,
 * or a non-zero number if a context switch should be performed. */
#define portYIELD_FROM_ISR( x )       ( void ) x
#define portEND_SWITCHING_ISR( x )    portYIELD_FROM_ISR( ( x ) )

void vPortCloseRunningThread( void * pvTaskToDelete,
                              volatile BaseType_t * pxPendYield );
void vPortDeleteThread( void * pvThreadToDelete );
#define portCLEAN_UP_TCB( pxTCB )                                  vPortDeleteThread( pxTCB )
#define portPRE_TASK_DELETE_HOOK( pvTaskToDelete, pxPendYield )    vPortCloseRunningThread( ( pvTaskToDelete ), ( pxPendYield ) )
#define portDISABLE_INTERRUPTS()                                   vPortEnterCritical()
#define portENABLE_INTERRUPTS()                                    vPortExitCritical()

/* Critical section handling. */
void vPortEnterCritical( void );
void vPortExitCritical( void );

#define portENTER_CRITICAL()    vPortEnterCritical()
#define portEXIT_CRITICAL()     vPortExitCritical()

#ifndef configUSE_PORT_OPTIMISED_TASK_SELECTION
    #define configUSE_PORT_OPTIMISED_TASK_SELECTION    1
#endif

#if configUSE_PORT_OPTIMISED_TASK_SELECTION == 1

/* Check the configuration. */
    #if ( configMAX_PRIORITIES > 32 )
        #error configUSE_PORT_OPTIMISED_TASK_SELECTION can only be set to 1 when configMAX_PRIORITIES is less than or equal to 32.  It is very rare that a system requires more than 10 to 15 difference priorities as tasks that share a priority will time slice.
    #endif

/* Store/clear the ready priorities in a bit map. */
    #define portRECORD_READY_PRIORITY( uxPriority, uxReadyPriorities )    ( uxReadyPriorities ) |= ( 1UL << ( uxPriority ) )
    #define portRESET_READY_PRIORITY( uxPriority, uxReadyPriorities )     ( uxReadyPriorities ) &= ~( 1UL << ( uxPriority ) )


/*-----------------------------------------------------------*/

    #ifdef __GNUC__
        #define portGET_HIGHEST_PRIORITY( uxTopPriority, uxReadyPriorities ) \
    __asm volatile ( "bsr %1, %0\n\t"                                        \
                     : "=r" ( uxTopPriority ) : "rm" ( uxReadyPriorities ) : "cc" )
    #else

/* BitScanReverse returns the bit position of the most significant '1'
 * in the word. */
        #define portGET_HIGHEST_PRIORITY( uxTopPriority, uxReadyPriorities )    _BitScanReverse( ( DWORD * ) &( uxTopPriority ), ( uxReadyPriorities ) )
    #endif /* __GNUC__ */

#endif /* taskRECORD_READY_PRIORITY */

#ifndef __GNUC__
    __pragma( warning( disable:4211 ) ) /* Nonstandard extension used, as extern is only nonstandard to MSVC. */
#endif


/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters )    void vFunction( void * pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters )          void vFunction( void * pvParameters )

#ifndef portINTERRUPT_YIELD
    #define portINTERRUPT_YIELD    ( 0UL )
#endif
#ifndef portINTERRUPT_TICK
    #define portINTERRUPT_TICK     ( 1UL )
#endif

/*
 * Raise a simulated interrupt represented by the bit mask in ulInterruptMask.
 * Each bit can be used to represent an individual interrupt - with the first
 * two bits being used for the Yield and Tick interrupts respectively.
 */
void vPortGenerateSimulatedInterrupt( uint32_t ulInterruptNumber );

/*
 * Install an interrupt handler to be called by the simulated interrupt handler
 * thread.  The interrupt number must be above any used by the kernel itself
 * (at the time of writing the kernel was using interrupt numbers 0, 1, and 2
 * as defined above).  The number must also be lower than 32.
 *
 * Interrupt handler functions must return a non-zero value if executing the
 * handler resulted in a task switch being required.
 */
void vPortSetInterruptHandler( uint32_t ulInterruptNumber,
                               uint32_t ( * pvHandler )( void ) );

/*
 * MPU regions Macros
 */
#ifndef configTOTAL_MPU_REGIONS
    #define configTOTAL_MPU_REGIONS             ( 10UL )
#endif
#ifndef portPRIVILEGED_FLASH_REGION
    #define portPRIVILEGED_FLASH_REGION         ( 0UL )
#endif
#ifndef portUNPRIVILEGED_FLASH_REGION
    #define portUNPRIVILEGED_FLASH_REGION       ( 1UL )
#endif
#ifndef portUNPRIVILEGED_SYSCALLS_REGION
    #define portUNPRIVILEGED_SYSCALLS_REGION    ( 2UL )
#endif
#ifndef portPRIVILEGED_RAM_REGION
    #define portPRIVILEGED_RAM_REGION           ( 3UL )
#endif
#ifndef portSTACK_REGION
    #define portSTACK_REGION                    ( 4UL )
#endif
#ifndef portFIRST_CONFIGURABLE_REGION
    #define portFIRST_CONFIGURABLE_REGION       ( 5UL )
#endif
#ifndef portLAST_CONFIGURABLE_REGION
    #define portLAST_CONFIGURABLE_REGION        ( configTOTAL_MPU_REGIONS - 1UL )
#endif
#ifndef portNUM_CONFIGURABLE_REGIONS
    #define portNUM_CONFIGURABLE_REGIONS        ( ( portLAST_CONFIGURABLE_REGION - portFIRST_CONFIGURABLE_REGION ) + 1 )
#endif
#ifndef portTOTAL_NUM_REGIONS
    #define portTOTAL_NUM_REGIONS               ( portNUM_CONFIGURABLE_REGIONS + 1 )             /* Plus one to make space for the stack region. */
#endif

#ifndef portUSING_MPU_WRAPPERS
    #define portUSING_MPU_WRAPPERS    0
#endif

typedef struct MPURegionSettings
{
    uint32_t ulRBAR; /**< RBAR for the region. */
    uint32_t ulRLAR; /**< RLAR for the region. */
} MPURegionSettings_t;
typedef struct MPU_SETTINGS
{
    uint32_t ulMAIR0;                                              /**< MAIR0 for the task containing attributes for all the 4 per task regions. */
    MPURegionSettings_t xRegionsSettings[ portTOTAL_NUM_REGIONS ]; /**< Settings for 4 per task regions. */
} xMPU_SETTINGS;

#endif /* closes #ifndef PORTMACRO_H */
