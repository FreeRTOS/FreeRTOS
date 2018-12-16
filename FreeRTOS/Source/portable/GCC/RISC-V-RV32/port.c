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

#ifdef configISR_STACK_SIZE
	/* The stack used by interrupt service routines. */
	static __attribute__ ((aligned(16))) StackType_t xISRStack[ configISR_STACK_SIZE ] = { 0 };
	const StackType_t * const xISRStackTop = &( xISRStack[ ( configISR_STACK_SIZE & ~portBYTE_ALIGNMENT_MASK ) - 1 ] );
#else
	extern const uint32_t __freertos_irq_stack_top[];
	const uint32_t xISRStackTop = ( uint32_t ) __freertos_irq_stack_top;
#endif

/*
 * Setup the timer to generate the tick interrupts.  The implementation in this
 * file is weak to allow application writers to change the timer used to
 * generate the tick interrupt.
 */
void vPortSetupTimerInterrupt( void ) __attribute__(( weak ));

/*
 * Used to catch tasks that attempt to return from their implementing function.
 */
static void prvTaskExitError( void );

/*-----------------------------------------------------------*/

/* Used to program the machine timer compare register. */
uint64_t ullNextTime = 0ULL;
const uint64_t *pullNextTime = &ullNextTime;
const uint32_t ulTimerIncrementsForOneTick = ( uint32_t ) ( configCPU_CLOCK_HZ / configTICK_RATE_HZ ); /* Assumes increment won't go over 32-bits. */
volatile uint64_t * const pullMachineTimerCompareRegister = ( volatile uint64_t * const ) ( configCLINT_BASE_ADDRESS + 0x4000 );

/* Set configCHECK_FOR_STACK_OVERFLOW to 3 to add ISR stack checking to task
stack checking.  A problem in the ISR stack will trigger an assert, not call the
stack overflow hook function (because the stack overflow hook is specific to a
task stack, not the ISR stack). */
#if( configCHECK_FOR_STACK_OVERFLOW > 2 )
	#warning This path not tested, or even compiled yet.
	/* Don't use 0xa5 as the stack fill bytes as that is used by the kernerl for
	the task stacks, and so will legitimately appear in many positions within
	the ISR stack. */
	#define portISR_STACK_FILL_BYTE	0xee

	static const uint8_t ucExpectedStackBytes[] = {
									portISR_STACK_FILL_BYTE, portISR_STACK_FILL_BYTE, portISR_STACK_FILL_BYTE, portISR_STACK_FILL_BYTE,		\
									portISR_STACK_FILL_BYTE, portISR_STACK_FILL_BYTE, portISR_STACK_FILL_BYTE, portISR_STACK_FILL_BYTE,		\
									portISR_STACK_FILL_BYTE, portISR_STACK_FILL_BYTE, portISR_STACK_FILL_BYTE, portISR_STACK_FILL_BYTE,		\
									portISR_STACK_FILL_BYTE, portISR_STACK_FILL_BYTE, portISR_STACK_FILL_BYTE, portISR_STACK_FILL_BYTE,		\
									portISR_STACK_FILL_BYTE, portISR_STACK_FILL_BYTE, portISR_STACK_FILL_BYTE, portISR_STACK_FILL_BYTE };	\

	#define portCHECK_ISR_STACK() configASSERT( ( memcmp( ( void * ) xISRStack, ( void * ) ucExpectedStackBytes, sizeof( ucExpectedStackBytes ) ) == 0 ) )
#else
	/* Define the function away. */
	#define portCHECK_ISR_STACK()
#endif /* configCHECK_FOR_STACK_OVERFLOW > 2 */

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
uint32_t mstatus;
const uint32_t ulMPIE_Bit = 0x80, ulMPP_Bits = 0x1800;
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

	/* Start task with interrupt enabled. */
	__asm volatile ("csrr %0, mstatus" : "=r"(mstatus));
	mstatus |= ulMPIE_Bit | ulMPP_Bits;
	pxTopOfStack--;
	*pxTopOfStack = mstatus;

	/* Numbers correspond to the x register number. */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 31;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 30;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 29;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 28;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 27;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 26;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 25;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 24;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 23;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 22;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 21;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 20;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 19;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 18;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 17;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 16;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 15;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 14;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 13;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 12;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 11;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) pvParameters;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 9;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 8;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 7;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 6;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 5;
	pxTopOfStack--;
//	*pxTopOfStack = ( StackType_t ) 4;  /* Thread pointer. */
//	pxTopOfStack--;
//	*pxTopOfStack = ( StackType_t ) 3;  /* Global pointer. */
//	pxTopOfStack--;
//	*pxTopOfStack = ( StackType_t ) 2;  /* Stack pointer. */
//	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) prvTaskExitError;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) pxCode;

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

void vPortSetupTimerInterrupt( void )
{
uint32_t ulCurrentTimeHigh, ulCurrentTimeLow;
volatile uint32_t * const pulTimeHigh = ( volatile uint32_t * const ) ( configCLINT_BASE_ADDRESS + 0xBFFC );
volatile uint32_t * const pulTimeLow = ( volatile uint32_t * const ) ( configCLINT_BASE_ADDRESS + 0xBFF8 );

	do
	{
		ulCurrentTimeHigh = *pulTimeHigh;
		ulCurrentTimeLow = *pulTimeLow;
	} while( ulCurrentTimeHigh != *pulTimeHigh );

	ullNextTime = ( uint64_t ) ulCurrentTimeHigh;
	ullNextTime <<= 32ULL;
	ullNextTime |= ( uint64_t ) ulCurrentTimeLow;
	ullNextTime += ( uint64_t ) ulTimerIncrementsForOneTick;
	*pullMachineTimerCompareRegister = ullNextTime;

	/* Prepare the time to use after the next tick interrupt. */
	ullNextTime += ( uint64_t ) ulTimerIncrementsForOneTick;
}
/*-----------------------------------------------------------*/

BaseType_t xPortStartScheduler( void )
{
extern void xPortStartFirstTask( void );

	#if( configASSERT_DEFINED == 1 )
	{
		volatile uint32_t mtvec = 0;

		/* Check the least significant two bits of mtvec are 00 - indicating
		single vector mode. */
		__asm volatile( "csrr %0, mtvec" : "=r"( mtvec ) );
		configASSERT( ( mtvec & 0x03UL ) == 0 );

		/* Check alignment of the interrupt stack - which is the same as the
		stack that was being used by main() prior to the scheduler being
		started. */
		configASSERT( ( xISRStackTop & portBYTE_ALIGNMENT_MASK ) == 0 );
	}
	#endif

	vPortSetupTimerInterrupt();

	/* Enable mtime and external interrupts.  1<<7 for timer interrupt, 1<<11
	for external interrupt.  _RB_ What happens here when mtime is not present as
	with pulpino? */
	__asm volatile( "csrs mie, %0" :: "r"(0x880) );

	xPortStartFirstTask();

	/* Should not get here as after calling xPortStartFirstTask() only tasks
	should be executing. */
	return pdFAIL;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Not implemented. */
	for( ;; );
}





