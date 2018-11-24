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


#ifndef PORTMACRO_H
#define PORTMACRO_H

#ifdef __cplusplus
extern "C" {
#endif

/*-----------------------------------------------------------
 * Port specific definitions.
 *
 * The settings in this file configure FreeRTOS correctly for the
 * given hardware and compiler.
 *
 * These settings should not be altered.
 *-----------------------------------------------------------
 */

#ifdef __riscv64
	#error This is the RV32 port that supports 32-bit cores only.
#endif

/* Type definitions. */
#define portSTACK_TYPE	uint32_t
#define portBASE_TYPE	long

typedef portSTACK_TYPE StackType_t;
typedef long BaseType_t;
typedef unsigned long UBaseType_t;
typedef uint32_t TickType_t;
#define portMAX_DELAY ( TickType_t ) 0xffffffffUL

/* 32-bit tick type on a 32-bit architecture, so reads of the tick count do
not need to be guarded with a critical section. */
#define portTICK_TYPE_IS_ATOMIC 1
/*-----------------------------------------------------------*/

/* Architecture specifics. */
#define portSTACK_GROWTH			( -1 )
#define portTICK_PERIOD_MS			( ( TickType_t ) 1000 / configTICK_RATE_HZ )
#define portBYTE_ALIGNMENT			16
/*-----------------------------------------------------------*/


/* Scheduler utilities. */
#define portYIELD() __asm volatile( "ecall" ); // software interrupt alternative *( ( uint32_t * ) configCLINT_BASE_ADDRESS ) |= 0x08UL
#define portEND_SWITCHING_ISR( xSwitchRequired ) if( xSwitchRequired ) vPortYield()
#define portYIELD_FROM_ISR( x ) portEND_SWITCHING_ISR( x )
/*-----------------------------------------------------------*/


/* Critical section management. */
#define portCRITICAL_NESTING_IN_TCB					1
extern int vPortSetInterruptMask( void );
extern void vPortClearInterruptMask( int );
extern void vTaskEnterCritical( void );
extern void vTaskExitCritical( void );

#define portSET_INTERRUPT_MASK_FROM_ISR() 0
#define portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedStatusValue )
#define portDISABLE_INTERRUPTS()	__asm volatile( "csrc mstatus, 8" )
#define portENABLE_INTERRUPTS()		__asm volatile( "csrs mstatus, 8" )
#define portENTER_CRITICAL()	vTaskEnterCritical()
#define portEXIT_CRITICAL()		vTaskExitCritical()

/*-----------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site.  These are
not necessary for to use this port.  They are defined so the common demo files
(which build with all the ports) will build. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) void vFunction( void *pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void *pvParameters )

/*-----------------------------------------------------------*/

#define portNOP() __asm volatile 	( " nop " )

#define portINLINE	__inline

#ifndef portFORCE_INLINE
	#define portFORCE_INLINE inline __attribute__(( always_inline))
#endif
portFORCE_INLINE static BaseType_t xPortIsInsideInterrupt( void ) {}

#ifdef __cplusplus
}
#endif

#endif /* PORTMACRO_H */

