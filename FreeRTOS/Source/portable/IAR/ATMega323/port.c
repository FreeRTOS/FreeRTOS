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

#include <stdlib.h>

#include "FreeRTOS.h"
#include "task.h"

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the AVR/IAR port.
 *----------------------------------------------------------*/

/* Start tasks with interrupts enables. */
#define portFLAGS_INT_ENABLED					( ( StackType_t ) 0x80 )

/* Hardware constants for timer 1. */
#define portCLEAR_COUNTER_ON_MATCH				( ( uint8_t ) 0x08 )
#define portPRESCALE_64							( ( uint8_t ) 0x03 )
#define portCLOCK_PRESCALER						( ( uint32_t ) 64 )
#define portCOMPARE_MATCH_A_INTERRUPT_ENABLE	( ( uint8_t ) 0x10 )

/* The number of bytes used on the hardware stack by the task start address. */
#define portBYTES_USED_BY_RETURN_ADDRESS		( 2 )
/*-----------------------------------------------------------*/

/* Stores the critical section nesting.  This must not be initialised to 0.
It will be initialised when a task starts. */
#define portNO_CRITICAL_NESTING					( ( UBaseType_t ) 0 )
UBaseType_t uxCriticalNesting = 0x50;


/*
 * Perform hardware setup to enable ticks from timer 1, compare match A.
 */
static void prvSetupTimerInterrupt( void );

/*
 * The IAR compiler does not have full support for inline assembler, so
 * these are defined in the portmacro assembler file.
 */
extern void vPortYieldFromTick( void );
extern void vPortStart( void );

/*-----------------------------------------------------------*/

/*
 * See header file for description.
 */
StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack, TaskFunction_t pxCode, void *pvParameters )
{
uint16_t usAddress;
StackType_t *pxTopOfHardwareStack;

	/* Place a few bytes of known values on the bottom of the stack.
	This is just useful for debugging. */

	*pxTopOfStack = 0x11;
	pxTopOfStack--;
	*pxTopOfStack = 0x22;
	pxTopOfStack--;
	*pxTopOfStack = 0x33;
	pxTopOfStack--;

	/* Remember where the top of the hardware stack is - this is required
	below. */
	pxTopOfHardwareStack = pxTopOfStack;


	/* Simulate how the stack would look after a call to vPortYield(). */

	/*lint -e950 -e611 -e923 Lint doesn't like this much - but nothing I can do about it. */



	/* The IAR compiler requires two stacks per task.  First there is the
	hardware call stack which uses the AVR stack pointer.  Second there is the
	software stack (local variables, parameter passing, etc.) which uses the
	AVR Y register.

	This function places both stacks within the memory block passed in as the
	first parameter.  The hardware stack is placed at the bottom of the memory
	block.  A gap is then left for the hardware stack to grow.  Next the software
	stack is placed.  The amount of space between the software and hardware
	stacks is defined by configCALL_STACK_SIZE.



	The first part of the stack is the hardware stack.  Place the start
	address of the task on the hardware stack. */
	usAddress = ( uint16_t ) pxCode;
	*pxTopOfStack = ( StackType_t ) ( usAddress & ( uint16_t ) 0x00ff );
	pxTopOfStack--;

	usAddress >>= 8;
	*pxTopOfStack = ( StackType_t ) ( usAddress & ( uint16_t ) 0x00ff );
	pxTopOfStack--;


	/* Leave enough space for the hardware stack before starting the software
	stack.  The '- 2' is because we have already used two spaces for the
	address of the start of the task. */
	pxTopOfStack -= ( configCALL_STACK_SIZE - 2 );



	/* Next simulate the stack as if after a call to portSAVE_CONTEXT().
	portSAVE_CONTEXT places the flags on the stack immediately after r0
	to ensure the interrupts get disabled as soon as possible, and so ensuring
	the stack use is minimal should a context switch interrupt occur. */
	*pxTopOfStack = ( StackType_t ) 0x00;	/* R0 */
	pxTopOfStack--;
	*pxTopOfStack = portFLAGS_INT_ENABLED;
	pxTopOfStack--;

	/* Next place the address of the hardware stack.  This is required so
	the AVR stack pointer can be restored to point to the hardware stack. */
	pxTopOfHardwareStack -= portBYTES_USED_BY_RETURN_ADDRESS;
	usAddress = ( uint16_t ) pxTopOfHardwareStack;

	/* SPL */
	*pxTopOfStack = ( StackType_t ) ( usAddress & ( uint16_t ) 0x00ff );
	pxTopOfStack--;

	/* SPH */
	usAddress >>= 8;
	*pxTopOfStack = ( StackType_t ) ( usAddress & ( uint16_t ) 0x00ff );
	pxTopOfStack--;




	/* Now the remaining registers. */
	*pxTopOfStack = ( StackType_t ) 0x01;	/* R1 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x02;	/* R2 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x03;	/* R3 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x04;	/* R4 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x05;	/* R5 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x06;	/* R6 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x07;	/* R7 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x08;	/* R8 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x09;	/* R9 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x10;	/* R10 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x11;	/* R11 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x12;	/* R12 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x13;	/* R13 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x14;	/* R14 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x15;	/* R15 */
	pxTopOfStack--;

	/* Place the parameter on the stack in the expected location. */
	usAddress = ( uint16_t ) pvParameters;
	*pxTopOfStack = ( StackType_t ) ( usAddress & ( uint16_t ) 0x00ff );
	pxTopOfStack--;

	usAddress >>= 8;
	*pxTopOfStack = ( StackType_t ) ( usAddress & ( uint16_t ) 0x00ff );
	pxTopOfStack--;

	*pxTopOfStack = ( StackType_t ) 0x18;	/* R18 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x19;	/* R19 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x20;	/* R20 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x21;	/* R21 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x22;	/* R22 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x23;	/* R23 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x24;	/* R24 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x25;	/* R25 */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x26;	/* R26 X */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x27;	/* R27 */
	pxTopOfStack--;

	/* The Y register is not stored as it is used as the software stack and
	gets saved into the task control block. */

	*pxTopOfStack = ( StackType_t ) 0x30;	/* R30 Z */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x031;	/* R31 */

	pxTopOfStack--;
	*pxTopOfStack = portNO_CRITICAL_NESTING;	/* Critical nesting is zero when the task starts. */

	/*lint +e950 +e611 +e923 */

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

BaseType_t xPortStartScheduler( void )
{
	/* Setup the hardware to generate the tick. */
	prvSetupTimerInterrupt();

	/* Restore the context of the first task that is going to run.
	Normally we would just call portRESTORE_CONTEXT() here, but as the IAR
	compiler does not fully support inline assembler we have to make a call.*/
	vPortStart();

	/* Should not get here! */
	return pdTRUE;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* It is unlikely that the AVR port will get stopped.  If required simply
	disable the tick interrupt here. */
}
/*-----------------------------------------------------------*/

/*
 * Setup timer 1 compare match A to generate a tick interrupt.
 */
static void prvSetupTimerInterrupt( void )
{
uint32_t ulCompareMatch;
uint8_t ucHighByte, ucLowByte;

	/* Using 16bit timer 1 to generate the tick.  Correct fuses must be
	selected for the configCPU_CLOCK_HZ clock. */

	ulCompareMatch = configCPU_CLOCK_HZ / configTICK_RATE_HZ;

	/* We only have 16 bits so have to scale to get our required tick rate. */
	ulCompareMatch /= portCLOCK_PRESCALER;

	/* Adjust for correct value. */
	ulCompareMatch -= ( uint32_t ) 1;

	/* Setup compare match value for compare match A.  Interrupts are disabled
	before this is called so we need not worry here. */
	ucLowByte = ( uint8_t ) ( ulCompareMatch & ( uint32_t ) 0xff );
	ulCompareMatch >>= 8;
	ucHighByte = ( uint8_t ) ( ulCompareMatch & ( uint32_t ) 0xff );
	OCR1AH = ucHighByte;
	OCR1AL = ucLowByte;

	/* Setup clock source and compare match behaviour. */
	ucLowByte = portCLEAR_COUNTER_ON_MATCH | portPRESCALE_64;
	TCCR1B = ucLowByte;

	/* Enable the interrupt - this is okay as interrupt are currently globally
	disabled. */
	TIMSK |= portCOMPARE_MATCH_A_INTERRUPT_ENABLE;
}
/*-----------------------------------------------------------*/

#if configUSE_PREEMPTION == 1

	/*
	 * Tick ISR for preemptive scheduler.  We can use a __task attribute as
	 * the context is saved at the start of vPortYieldFromTick().  The tick
	 * count is incremented after the context is saved.
	 */
	__task void SIG_OUTPUT_COMPARE1A( void )
	{
		vPortYieldFromTick();
		asm( "reti" );
	}

#else

	/*
	 * Tick ISR for the cooperative scheduler.  All this does is increment the
	 * tick count.  We don't need to switch context, this can only be done by
	 * manual calls to taskYIELD();
	 *
	 * THE INTERRUPT VECTOR IS POPULATED IN portmacro.s90.  DO NOT INSTALL
	 * IT HERE USING THE USUAL PRAGMA.
	 */
	__interrupt void SIG_OUTPUT_COMPARE1A( void )
	{
		xTaskIncrementTick();
	}
#endif
/*-----------------------------------------------------------*/

void vPortEnterCritical( void )
{
	portDISABLE_INTERRUPTS();
	uxCriticalNesting++;
}
/*-----------------------------------------------------------*/

void vPortExitCritical( void )
{
	uxCriticalNesting--;
	if( uxCriticalNesting == portNO_CRITICAL_NESTING )
	{
		portENABLE_INTERRUPTS();
	}
}


