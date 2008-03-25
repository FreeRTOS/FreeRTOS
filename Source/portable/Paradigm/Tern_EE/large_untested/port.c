/*
	FreeRTOS.org V4.8.0 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************
	***************************************************************************
	*																		  *
	* SAVE TIME AND MONEY!  Why not get us to quote to get FreeRTOS.org		  *
	* running on your hardware - or even write all or part of your application*
	* for you?  See http://www.OpenRTOS.com for details.					  *
	*																		  *
	***************************************************************************
	***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and 
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety 
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting, 
	licensing and training services.
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
#define portTIMER_COMPARE ( unsigned portSHORT ) ( ( configCPU_CLOCK_HZ / configTICK_RATE_HZ ) / ( unsigned portLONG ) 4 )

/* From the RDC data sheet. */
#define portENABLE_TIMER_AND_INTERRUPT ( unsigned portSHORT ) 0xe001

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

/* The timer initialisation functions leave interrupts enabled,
which is not what we want.  This ISR is installed temporarily in case
the timer fires before we get a change to disable interrupts again. */
static void __interrupt __far prvDummyISR( void );

/*-----------------------------------------------------------*/
/* See header file for description. */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
portSTACK_TYPE DS_Reg = 0;

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
	
	*pxTopOfStack = FP_SEG( pvParameters );
	pxTopOfStack--;
	*pxTopOfStack = FP_OFF( pvParameters );
	pxTopOfStack--;
	*pxTopOfStack = FP_SEG( pxCode );
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
	*pxTopOfStack = ( portSTACK_TYPE ) 0xAAAA;	/* AX */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xBBBB;	/* BX */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xCCCC;	/* CX */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xDDDD;	/* DX */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xEEEE;	/* ES */
	pxTopOfStack--;

	/* We need the true data segment. */
	__asm{	MOV DS_Reg, DS };

	*pxTopOfStack = DS_Reg;						/* DS */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x0123;	/* SI */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xDDDD;	/* DI */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xBBBB;	/* BP */

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
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

static void __interrupt __far prvDummyISR( void )
{
	/* The timer initialisation functions leave interrupts enabled,
	which is not what we want.  This ISR is installed temporarily in case
	the timer fires before we get a change to disable interrupts again. */
	outport( portEIO_REGISTER, portCLEAR_INTERRUPT );
}
/*-----------------------------------------------------------*/

/* The ISR used depends on whether the preemptive or cooperative scheduler
is being used. */
#if( configUSE_PREEMPTION == 1 )
	static void __interrupt __far prvPreemptiveTick( void )
	{
		/* Get the scheduler to update the task states following the tick. */
		vTaskIncrementTick();

		/* Switch in the context of the next task to be run. */
		portSWITCH_CONTEXT();

		/* Reset interrupt. */
		outport( portEIO_REGISTER, portCLEAR_INTERRUPT );
	}
#else
	static void __interrupt __far prvNonPreemptiveTick( void )
	{
		/* Same as preemptive tick, but the cooperative scheduler is being used
		so we don't have to switch in the context of the next task. */
		vTaskIncrementTick();
		/* Reset interrupt. */
		outport( portEIO_REGISTER, portCLEAR_INTERRUPT );
	}
#endif
/*-----------------------------------------------------------*/

static void __interrupt __far prvYieldProcessor( void )
{
	/* Switch in the context of the next task to be run. */
	portSWITCH_CONTEXT();
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Not implemented. */
}
/*-----------------------------------------------------------*/

static void prvSetupTimerInterrupt( void )
{
const unsigned portSHORT usTimerACompare = portTIMER_COMPARE, usTimerAMode = portENABLE_TIMER_AND_INTERRUPT;
const unsigned portSHORT usT2_IRQ = 0x13;

	/* Configure the timer, the dummy handler is used here as the init
	function leaves interrupts enabled. */
	t2_init( usTimerAMode, usTimerACompare, prvDummyISR );

	/* Disable interrupts again before installing the real handlers. */
	portDISABLE_INTERRUPTS();

	#if( configUSE_PREEMPTION == 1 )
		/* Tick service routine used by the scheduler when preemptive scheduling is
		being used. */
		setvect( usT2_IRQ, prvPreemptiveTick );
	#else
		/* Tick service routine used by the scheduler when cooperative scheduling is
		being used. */
		setvect( usT2_IRQ, prvNonPreemptiveTick );
	#endif
}







