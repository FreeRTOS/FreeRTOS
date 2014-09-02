/*
    FreeRTOS V8.1.2 - Copyright (C) 2014 Real Time Engineers Ltd. 
    All rights reserved

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

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

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


/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the Tern EE 186
 * port.
 *----------------------------------------------------------*/

/* Library includes. */
#include <embedded.h>
#include <ae.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "portasm.h"

/* The timer increments every four clocks, hence the divide by 4. */
#define portPRESCALE_VALUE ( 16 )
#define portTIMER_COMPARE ( configCPU_CLOCK_HZ  / ( configTICK_RATE_HZ * 4UL ) )

/* From the RDC data sheet. */
#define portENABLE_TIMER_AND_INTERRUPT 	( uint16_t ) 0xe00b
#define portENABLE_TIMER				( uint16_t ) 0xC001

/* Interrupt control. */
#define portEIO_REGISTER 0xff22
#define portCLEAR_INTERRUPT 0x0008

/* Setup the hardware to generate the required tick frequency. */
static void prvSetupTimerInterrupt( void );

/* The ISR used depends on whether the preemptive or cooperative scheduler
is being used. */
#if( configUSE_PREEMPTION == 1 )
	/* Tick service routine used by the scheduler when preemptive scheduling is
	being used. */
	static void __interrupt __far prvPreemptiveTick( void );
#else
	/* Tick service routine used by the scheduler when cooperative scheduling is
	being used. */
	static void __interrupt __far prvNonPreemptiveTick( void );
#endif

/* Trap routine used by taskYIELD() to manually cause a context switch. */
static void __interrupt __far prvYieldProcessor( void );

/*-----------------------------------------------------------*/
/* See header file for description. */
StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack, TaskFunction_t pxCode, void *pvParameters )
{
StackType_t DS_Reg = 0;

	/* We need the true data segment. */
	__asm{	MOV DS_Reg, DS };

	/* Place a few bytes of known values on the bottom of the stack.
	This is just useful for debugging. */

	*pxTopOfStack = 0x1111;
	pxTopOfStack--;
	*pxTopOfStack = 0x2222;
	pxTopOfStack--;
	*pxTopOfStack = 0x3333;
	pxTopOfStack--;

	/* We are going to start the scheduler using a return from interrupt
	instruction to load the program counter, so first there would be the
	function call with parameters preamble. */
	
	*pxTopOfStack = FP_OFF( pvParameters );
	pxTopOfStack--;
	*pxTopOfStack = FP_OFF( pxCode );
	pxTopOfStack--;

	/* Next the status register and interrupt return address. */
	*pxTopOfStack = portINITIAL_SW;
	pxTopOfStack--;
	*pxTopOfStack = FP_SEG( pxCode );
	pxTopOfStack--;
	*pxTopOfStack = FP_OFF( pxCode );
	pxTopOfStack--;

	/* The remaining registers would be pushed on the stack by our context
	switch function.  These are loaded with values simply to make debugging
	easier. */
	*pxTopOfStack = ( StackType_t ) 0xAAAA;	/* AX */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0xBBBB;	/* BX */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0xCCCC;	/* CX */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0xDDDD;	/* DX */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0xEEEE;	/* ES */
	pxTopOfStack--;

	*pxTopOfStack = DS_Reg;						/* DS */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0x0123;	/* SI */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0xDDDD;	/* DI */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0xBBBB;	/* BP */

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

BaseType_t xPortStartScheduler( void )
{
	/* This is called with interrupts already disabled. */

	/* Put our manual switch (yield) function on a known
	vector. */
	setvect( portSWITCH_INT_NUMBER, prvYieldProcessor );

	/* Setup the tick interrupt. */
	prvSetupTimerInterrupt();

	/* Kick off the scheduler by setting up the context of the first task. */
	portFIRST_CONTEXT();

	/* Should not get here! */
	return pdFALSE;
}
/*-----------------------------------------------------------*/

/* The ISR used depends on whether the preemptive or cooperative scheduler
is being used. */
#if( configUSE_PREEMPTION == 1 )
	static void __interrupt __far prvPreemptiveTick( void )
	{
		/* Get the scheduler to update the task states following the tick. */
		if( xTaskIncrementTick() != pdFALSE )
		{
			/* Switch in the context of the next task to be run. */
			portEND_SWITCHING_ISR();
		}

		/* Reset interrupt. */
		outport( portEIO_REGISTER, portCLEAR_INTERRUPT );
	}
#else
	static void __interrupt __far prvNonPreemptiveTick( void )
	{
		/* Same as preemptive tick, but the cooperative scheduler is being used
		so we don't have to switch in the context of the next task. */
		xTaskIncrementTick();
		
		/* Reset interrupt. */
		outport( portEIO_REGISTER, portCLEAR_INTERRUPT );
	}
#endif
/*-----------------------------------------------------------*/

static void __interrupt __far prvYieldProcessor( void )
{
	/* Switch in the context of the next task to be run. */
	portEND_SWITCHING_ISR();
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Not implemented. */
}
/*-----------------------------------------------------------*/

static void prvSetupTimerInterrupt( void )
{
const uint32_t ulCompareValue = portTIMER_COMPARE;
uint16_t usTimerCompare;

	usTimerCompare = ( uint16_t ) ( ulCompareValue >> 4 );
    t2_init( portENABLE_TIMER, portPRESCALE_VALUE, NULL );

	#if( configUSE_PREEMPTION == 1 )
		/* Tick service routine used by the scheduler when preemptive scheduling is
		being used. */
		t1_init( portENABLE_TIMER_AND_INTERRUPT, usTimerCompare, usTimerCompare, prvPreemptiveTick );
	#else
		/* Tick service routine used by the scheduler when cooperative scheduling is
		being used. */
		t1_init( portENABLE_TIMER_AND_INTERRUPT, usTimerCompare, usTimerCompare, prvNonPreemptiveTick );
	#endif
}







