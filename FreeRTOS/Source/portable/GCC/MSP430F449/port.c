/*
    FreeRTOS V7.5.1 - Copyright (C) 2013 Real Time Engineers Ltd.

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*
	Changes from V2.5.2
		
	+ usCriticalNesting now has a volatile qualifier.
*/

/* Standard includes. */
#include <stdlib.h>
#include <signal.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the MSP430 port.
 *----------------------------------------------------------*/

/* Constants required for hardware setup.  The tick ISR runs off the ACLK, 
not the MCLK. */
#define portACLK_FREQUENCY_HZ			( ( portTickType ) 32768 )
#define portINITIAL_CRITICAL_NESTING	( ( unsigned short ) 10 )
#define portFLAGS_INT_ENABLED	( ( portSTACK_TYPE ) 0x08 )

/* We require the address of the pxCurrentTCB variable, but don't want to know
any details of its type. */
typedef void tskTCB;
extern volatile tskTCB * volatile pxCurrentTCB;

/* Most ports implement critical sections by placing the interrupt flags on
the stack before disabling interrupts.  Exiting the critical section is then
simply a case of popping the flags from the stack.  As mspgcc does not use
a frame pointer this cannot be done as modifying the stack will clobber all
the stack variables.  Instead each task maintains a count of the critical
section nesting depth.  Each time a critical section is entered the count is
incremented.  Each time a critical section is left the count is decremented -
with interrupts only being re-enabled if the count is zero.

usCriticalNesting will get set to zero when the scheduler starts, but must
not be initialised to zero as this will cause problems during the startup
sequence. */
volatile unsigned short usCriticalNesting = portINITIAL_CRITICAL_NESTING;
/*-----------------------------------------------------------*/

/* 
 * Macro to save a task context to the task stack.  This simply pushes all the 
 * general purpose msp430 registers onto the stack, followed by the 
 * usCriticalNesting value used by the task.  Finally the resultant stack 
 * pointer value is saved into the task control block so it can be retrieved 
 * the next time the task executes.
 */
#define portSAVE_CONTEXT()									\
	asm volatile (	"push	r4						\n\t"	\
					"push	r5						\n\t"	\
					"push	r6						\n\t"	\
					"push	r7						\n\t"	\
					"push	r8						\n\t"	\
					"push	r9						\n\t"	\
					"push	r10						\n\t"	\
					"push	r11						\n\t"	\
					"push	r12						\n\t"	\
					"push	r13						\n\t"	\
					"push	r14						\n\t"	\
					"push	r15						\n\t"	\
					"mov.w	usCriticalNesting, r14	\n\t"	\
					"push	r14						\n\t"	\
					"mov.w	pxCurrentTCB, r12		\n\t"	\
					"mov.w	r1, @r12				\n\t"	\
				);

/* 
 * Macro to restore a task context from the task stack.  This is effectively
 * the reverse of portSAVE_CONTEXT().  First the stack pointer value is
 * loaded from the task control block.  Next the value for usCriticalNesting
 * used by the task is retrieved from the stack - followed by the value of all
 * the general purpose msp430 registers.
 *
 * The bic instruction ensures there are no low power bits set in the status
 * register that is about to be popped from the stack.
 */
#define portRESTORE_CONTEXT()								\
	asm volatile (	"mov.w	pxCurrentTCB, r12		\n\t"	\
					"mov.w	@r12, r1				\n\t"	\
					"pop	r15						\n\t"	\
					"mov.w	r15, usCriticalNesting	\n\t"	\
					"pop	r15						\n\t"	\
					"pop	r14						\n\t"	\
					"pop	r13						\n\t"	\
					"pop	r12						\n\t"	\
					"pop	r11						\n\t"	\
					"pop	r10						\n\t"	\
					"pop	r9						\n\t"	\
					"pop	r8						\n\t"	\
					"pop	r7						\n\t"	\
					"pop	r6						\n\t"	\
					"pop	r5						\n\t"	\
					"pop	r4						\n\t"	\
					"bic	#(0xf0),0(r1)			\n\t"	\
					"reti							\n\t"	\
				);
/*-----------------------------------------------------------*/

/*
 * Sets up the periodic ISR used for the RTOS tick.  This uses timer 0, but
 * could have alternatively used the watchdog timer or timer 1.
 */
static void prvSetupTimerInterrupt( void );
/*-----------------------------------------------------------*/

/* 
 * Initialise the stack of a task to look exactly as if a call to 
 * portSAVE_CONTEXT had been called.
 * 
 * See the header file portable.h.
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
	/* 
		Place a few bytes of known values on the bottom of the stack. 
		This is just useful for debugging and can be included if required.

		*pxTopOfStack = ( portSTACK_TYPE ) 0x1111;
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x2222;
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x3333;
		pxTopOfStack--; 
	*/

	/* The msp430 automatically pushes the PC then SR onto the stack before 
	executing an ISR.  We want the stack to look just as if this has happened
	so place a pointer to the start of the task on the stack first - followed
	by the flags we want the task to use when it starts up. */
	*pxTopOfStack = ( portSTACK_TYPE ) pxCode;
	pxTopOfStack--;
	*pxTopOfStack = portFLAGS_INT_ENABLED;
	pxTopOfStack--;

	/* Next the general purpose registers. */
	*pxTopOfStack = ( portSTACK_TYPE ) 0x4444;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x5555;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x6666;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x7777;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x8888;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x9999;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xaaaa;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xbbbb;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xcccc;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xdddd;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xeeee;
	pxTopOfStack--;

	/* When the task starts is will expect to find the function parameter in
	R15. */
	*pxTopOfStack = ( portSTACK_TYPE ) pvParameters;
	pxTopOfStack--;

	/* The code generated by the mspgcc compiler does not maintain separate
	stack and frame pointers. The portENTER_CRITICAL macro cannot therefore
	use the stack as per other ports.  Instead a variable is used to keep
	track of the critical section nesting.  This variable has to be stored
	as part of the task context and is initially set to zero. */
	*pxTopOfStack = ( portSTACK_TYPE ) portNO_CRITICAL_SECTION_NESTING;	

	/* Return a pointer to the top of the stack we have generated so this can
	be stored in the task control block for the task. */
	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
	/* Setup the hardware to generate the tick.  Interrupts are disabled when
	this function is called. */
	prvSetupTimerInterrupt();

	/* Restore the context of the first task that is going to run. */
	portRESTORE_CONTEXT();

	/* Should not get here as the tasks are now running! */
	return pdTRUE;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* It is unlikely that the MSP430 port will get stopped.  If required simply
	disable the tick interrupt here. */
}
/*-----------------------------------------------------------*/

/*
 * Manual context switch called by portYIELD or taskYIELD.  
 *
 * The first thing we do is save the registers so we can use a naked attribute.
 */
void vPortYield( void ) __attribute__ ( ( naked ) );
void vPortYield( void )
{
	/* We want the stack of the task being saved to look exactly as if the task
	was saved during a pre-emptive RTOS tick ISR.  Before calling an ISR the 
	msp430 places the status register onto the stack.  As this is a function 
	call and not an ISR we have to do this manually. */
	asm volatile ( "push	r2" );
	_DINT();

	/* Save the context of the current task. */
	portSAVE_CONTEXT();

	/* Switch to the highest priority task that is ready to run. */
	vTaskSwitchContext();

	/* Restore the context of the new task. */
	portRESTORE_CONTEXT();
}
/*-----------------------------------------------------------*/

/*
 * Hardware initialisation to generate the RTOS tick.  This uses timer 0
 * but could alternatively use the watchdog timer or timer 1. 
 */
static void prvSetupTimerInterrupt( void )
{
	/* Ensure the timer is stopped. */
	TACTL = 0;

	/* Run the timer of the ACLK. */
	TACTL = TASSEL_1;

	/* Clear everything to start with. */
	TACTL |= TACLR;

	/* Set the compare match value according to the tick rate we want. */
	TACCR0 = portACLK_FREQUENCY_HZ / configTICK_RATE_HZ;

	/* Enable the interrupts. */
	TACCTL0 = CCIE;

	/* Start up clean. */
	TACTL |= TACLR;

	/* Up mode. */
	TACTL |= MC_1;
}
/*-----------------------------------------------------------*/

/* 
 * The interrupt service routine used depends on whether the pre-emptive
 * scheduler is being used or not.
 */

#if configUSE_PREEMPTION == 1

	/*
	 * Tick ISR for preemptive scheduler.  We can use a naked attribute as
	 * the context is saved at the start of vPortYieldFromTick().  The tick
	 * count is incremented after the context is saved.
	 */
	interrupt (TIMERA0_VECTOR) prvTickISR( void ) __attribute__ ( ( naked ) );
	interrupt (TIMERA0_VECTOR) prvTickISR( void )
	{
		/* Save the context of the interrupted task. */
		portSAVE_CONTEXT();

		/* Increment the tick count then switch to the highest priority task
		that is ready to run. */
		if( xTaskIncrementTick() != pdFALSE )
		{
			vTaskSwitchContext();
		}

		/* Restore the context of the new task. */
		portRESTORE_CONTEXT();
	}

#else

	/*
	 * Tick ISR for the cooperative scheduler.  All this does is increment the
	 * tick count.  We don't need to switch context, this can only be done by
	 * manual calls to taskYIELD();
	 */
	interrupt (TIMERA0_VECTOR) prvTickISR( void );
	interrupt (TIMERA0_VECTOR) prvTickISR( void )
	{
		xTaskIncrementTick();
	}
#endif


	
