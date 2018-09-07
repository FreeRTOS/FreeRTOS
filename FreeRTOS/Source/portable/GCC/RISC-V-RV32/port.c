/*
 * FreeRTOS Kernel V10.1.0
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
	*pxTopOfStack =


		return pxTopOfStack;
}
/*-----------------------------------------------------------*/

BaseType_t xPortStartScheduler( void )
{
	/*Should not get here*/
	return pdFALSE;
}
/*-----------------------------------------------------------*/


