/*
 * FreeRTOS Kernel
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

/* Type definitions. */
#define portCHAR		char
#define portFLOAT		float
#define portDOUBLE		double
#define portLONG		long
#define portSHORT		short
#define portSTACK_TYPE	uint32_t
#define portBASE_TYPE	long

typedef portSTACK_TYPE StackType_t;
typedef long BaseType_t;
typedef unsigned long UBaseType_t;

#if( configUSE_16_BIT_TICKS == 1 )
	typedef uint16_t TickType_t;
	#define portMAX_DELAY ( TickType_t ) 0xffff
#else
	typedef uint32_t TickType_t;
	#define portMAX_DELAY ( TickType_t ) 0xffffffffUL
#endif
/*-----------------------------------------------------------*/

/* Hardware specifics. */
#define portBYTE_ALIGNMENT			4
#define portSTACK_GROWTH			-1
#define portTICK_PERIOD_MS			( ( TickType_t ) 1000 / configTICK_RATE_HZ )
/*-----------------------------------------------------------*/
uint32_t ulPortSetIPL( uint32_t );
#define portDISABLE_INTERRUPTS()	ulPortSetIPL( configMAX_SYSCALL_INTERRUPT_PRIORITY )
#define portENABLE_INTERRUPTS()		ulPortSetIPL( 0 )


extern void vPortEnterCritical( void );
extern void vPortExitCritical( void );
#define portENTER_CRITICAL()		vPortEnterCritical()
#define portEXIT_CRITICAL()			vPortExitCritical()

extern UBaseType_t uxPortSetInterruptMaskFromISR( void );
extern void vPortClearInterruptMaskFromISR( UBaseType_t );
#define portSET_INTERRUPT_MASK_FROM_ISR()	ulPortSetIPL( configMAX_SYSCALL_INTERRUPT_PRIORITY )
#define portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedStatusRegister ) ulPortSetIPL( uxSavedStatusRegister )

/*-----------------------------------------------------------*/

/* Task utilities. */

#define portNOP()	asm volatile ( 	"nop" )

/* Note this will overwrite all other bits in the force register, it is done this way for speed. */
#define portYIELD()			MCF_INTC0_INTFRCL = ( 1UL << configYIELD_INTERRUPT_VECTOR ); portNOP(); portNOP() /* -32 as we are using the high word of the 64bit mask. */

/*-----------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) void vFunction( void *pvParameters ) __attribute__((noreturn))
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void *pvParameters )
/*-----------------------------------------------------------*/

#define portEND_SWITCHING_ISR( xSwitchRequired )	if( xSwitchRequired != pdFALSE )	\
													{									\
														portYIELD();					\
													}


#ifdef __cplusplus
}
#endif

#endif /* PORTMACRO_H */

