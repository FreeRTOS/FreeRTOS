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

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the RISC-V RV32 port.
 *----------------------------------------------------------*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "portmacro.h"

/*
 * Setup the timer to generate the tick interrupts.  The implementation in this
 * file is weak to allow application writers to change the timer used to
 * generate the tick interrupt.
 */
void vPortSetupTimerInterrupt( void );

/*
 * Used to catch tasks that attempt to return from their implementing function.
 */
static void prvTaskExitError( void );

/*-----------------------------------------------------------*/

void prvTaskExitError( void )
{
volatile uint32_t ulx = 0;

	/* A function that implements a task must not exit or attempt to return to
	its caller as there is nothing to return to.  If a task wants to exit it
	should instead call vTaskDelete( NULL ).

	Artificially force an assert() to be triggered if configASSERT() is
	defined, then stop here so application writers can catch the error. */
	configASSERT( ulx == ~0UL );
	portDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

/*
 * See header file for description.
 */
StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack, TaskFunction_t pxCode, void *pvParameters )
{
	/*
	   X1 to X31 integer registers for the 'I' profile, X1 to X15 for the 'E' profile.

		Register 	ABI Name 		Description 					Saver
		x0 			zero 			Hard-wired zero 				-
		x1 			ra 				Return address 					Caller
		x2 			sp 				Stack pointer 					Callee
		x3 			gp 				Global pointer 					-
		x4 			tp 				Thread pointer 					-
		x5-7 		t0-2 			Temporaries 					Caller
		x8 			s0/fp 			Saved register/Frame pointer 	Callee
		x9 			s1 				Saved register 					Callee
		x10-11 		a0-1 			Function Arguments/return values Caller
		x12-17 		a2-7 			Function arguments 				Caller
		x18-27 		s2-11 			Saved registers 				Callee
		x28-31 		t3-6 			Temporaries 					Caller
	*/

	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) pxCode; /* X1 */
	pxTopOfStack--;
//	*pxTopOfStack = ( StackType_t ) 2; /* Stack pointer is handled separately. */
//	pxTopOfStack--;
//	*pxTopOfStack = ( StackType_t ) 3; /* Global pointer is not manipulated. */
//	pxTopOfStack--;
//	*pxTopOfStack = ( StackType_t ) 4; /* Thread pointer is not manipulated. */
//	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 5;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 6;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 7;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 8;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 9;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) pvParameters;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 11;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 12;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 13;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 14;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 15;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 16;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 17;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 18;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 19;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 20;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 21;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 22;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 23;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 24;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 25;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 26;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 27;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 28;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 29;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 30;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 31;

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

BaseType_t xPortStartScheduler( void )
{
	__asm volatile
	(
		".extern pxCurrentTCB			\r\n"
		"lw		sp, pxCurrentTCB		\r\n" /* Load pxCurrentTCB. */
		"lw		sp, 0x00( sp )			\r\n" /* Read sp from first TCB member. */
		"lw		x31, 0( sp )			\r\n" /* X31 */
		"lw		x30, 4( sp )			\r\n" /* X30 */
		"lw		x29, 8( sp )			\r\n" /* X29 */
		"lw		x28, 12( sp )			\r\n" /* X28 */
		"lw		x27, 16( sp )			\r\n" /* X27 */
		"lw		x26, 20( sp )			\r\n" /* X26 */
		"lw		x25, 24( sp )			\r\n" /* X25 */
		"lw		x24, 28( sp )			\r\n" /* X24 */
		"lw		x23, 32( sp )			\r\n" /* X23 */
		"lw		x22, 36( sp )			\r\n" /* X22 */
		"lw		x21, 40( sp )			\r\n" /* X21 */
		"lw		x20, 44( sp )			\r\n" /* X20 */
		"lw		x19, 48( sp )			\r\n" /* X19 */
		"lw		x18, 52( sp )			\r\n" /* X18 */
		"lw		x17, 56( sp )			\r\n" /* X17 */
		"lw		x16, 60( sp )			\r\n" /* X16 */
		"lw		x15, 64( sp )			\r\n" /* X15 */
		"lw		x14, 68( sp )			\r\n" /* X14 */
		"lw		x13, 72( sp )			\r\n" /* X13 */
		"lw		x12, 76( sp )			\r\n" /* X12 */
		"lw		x11, 80( sp )			\r\n" /* X11 */
		"lw		x10, 84( sp )			\r\n" /* X10 */
		"lw		x9, 88( sp )			\r\n" /* X9 */
		"lw		x8, 92( sp )			\r\n" /* X8 */
		"lw		x7, 96( sp )			\r\n" /* X7 */
		"lw		x6, 100( sp )			\r\n" /* X6 */
		"lw		x5, 104( sp )			\r\n" /* X5 */
		"lw		x1, 108( sp )			\r\n" /* X1 */
		"csrs 	mstatus, 8				\r\n" /* Enable interrupts. */
		"ret								"
	);

	/*Should not get here*/
	return pdFALSE;
}
/*-----------------------------------------------------------*/

void vPortYield( void )
{
}


