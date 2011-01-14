/*
    FreeRTOS V6.1.1 - Copyright (C) 2011 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS books - available as PDF or paperback  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public 
    License and the FreeRTOS license exception along with FreeRTOS; if not it 
    can be viewed here: http://www.freertos.org/a00114.html and also obtained 
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/

/* GCC/HCS12 port by Jefferson L Smith, 2005 */

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Port includes */
#include <sys/ports_def.h>

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the HCS12 port.
 *----------------------------------------------------------*/


/*
 * Configure a timer to generate the RTOS tick at the frequency specified 
 * within FreeRTOSConfig.h.
 */
static void prvSetupTimerInterrupt( void );

/* NOTE: Interrupt service routines must be in non-banked memory - as does the
scheduler startup function. */
#define ATTR_NEAR	__attribute__((near))

/* Manual context switch function.  This is the SWI ISR. */
// __attribute__((interrupt))
void ATTR_NEAR vPortYield( void );

/* Tick context switch function.  This is the timer ISR. */
// __attribute__((interrupt))
void ATTR_NEAR vPortTickInterrupt( void );

/* Function in non-banked memory which actually switches to first task. */
portBASE_TYPE ATTR_NEAR xStartSchedulerNear( void );

/* Calls to portENTER_CRITICAL() can be nested.  When they are nested the 
critical section should not be left (i.e. interrupts should not be re-enabled)
until the nesting depth reaches 0.  This variable simply tracks the nesting 
depth.  Each task maintains it's own critical nesting depth variable so 
uxCriticalNesting is saved and restored from the task stack during a context
switch. */
volatile unsigned portBASE_TYPE uxCriticalNesting = 0x80;  // un-initialized

/*-----------------------------------------------------------*/

/* 
 * See header file for description. 
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{


	/* Setup the initial stack of the task.  The stack is set exactly as 
	expected by the portRESTORE_CONTEXT() macro.  In this case the stack as
	expected by the HCS12 RTI instruction. */


	/* The address of the task function is placed in the stack byte at a time. */
	*pxTopOfStack   = ( portSTACK_TYPE ) *( ((portSTACK_TYPE *) (&pxCode) ) + 1 );
	*--pxTopOfStack = ( portSTACK_TYPE ) *( ((portSTACK_TYPE *) (&pxCode) ) + 0 );

	/* Next are all the registers that form part of the task context. */

	/* Y register */
	*--pxTopOfStack = ( portSTACK_TYPE ) 0xff;
	*--pxTopOfStack = ( portSTACK_TYPE ) 0xee;

	/* X register */
	*--pxTopOfStack = ( portSTACK_TYPE ) 0xdd;
	*--pxTopOfStack = ( portSTACK_TYPE ) 0xcc;
 
	/* A register contains parameter high byte. */
	*--pxTopOfStack = ( portSTACK_TYPE ) *( ((portSTACK_TYPE *) (&pvParameters) ) + 0 );

	/* B register contains parameter low byte. */
	*--pxTopOfStack = ( portSTACK_TYPE ) *( ((portSTACK_TYPE *) (&pvParameters) ) + 1 );

	/* CCR: Note that when the task starts interrupts will be enabled since
	"I" bit of CCR is cleared */
	*--pxTopOfStack = ( portSTACK_TYPE ) 0x80;		// keeps Stop disabled (MCU default)
	
	/* tmp softregs used by GCC. Values right now don't	matter. */
	__asm("\n\
		movw _.frame, 2,-%0							\n\
		movw _.tmp, 2,-%0							\n\
		movw _.z, 2,-%0								\n\
		movw _.xy, 2,-%0							\n\
		;movw _.d2, 2,-%0							\n\
		;movw _.d1, 2,-%0							\n\
	": "=A"(pxTopOfStack) : "0"(pxTopOfStack) );

	#ifdef BANKED_MODEL
		/* The page of the task. */
		*--pxTopOfStack = 0x30;      // can only directly start in PPAGE 0x30
	#endif
	
	/* The critical nesting depth is initialised with 0 (meaning not in
	a critical section). */
	*--pxTopOfStack = ( portSTACK_TYPE ) 0x00;


	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* It is unlikely that the HCS12 port will get stopped. */
}
/*-----------------------------------------------------------*/

static void prvSetupTimerInterrupt( void )
{
	/* Enable hardware RTI timer */
	/* Ignores configTICK_RATE_HZ */
	RTICTL = 0x50;			// 16 MHz xtal: 976.56 Hz, 1024mS 
	CRGINT |= 0x80;			// RTIE
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
	/* xPortStartScheduler() does not start the scheduler directly because 
	the header file containing the xPortStartScheduler() prototype is part 
	of the common kernel code, and therefore cannot use the CODE_SEG pragma. 
	Instead it simply calls the locally defined xNearStartScheduler() - 
	which does use the CODE_SEG pragma. */

	short register d;
	__asm ("jmp  xStartSchedulerNear		; will never return": "=d"(d));
	return d;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xStartSchedulerNear( void )
{
	/* Configure the timer that will generate the RTOS tick.  Interrupts are
	disabled when this function is called. */
	prvSetupTimerInterrupt();

	/* Restore the context of the first task. */
	portRESTORE_CONTEXT();

	portISR_TAIL();

	/* Should not get here! */
	return pdFALSE;
}
/*-----------------------------------------------------------*/

/*
 * Context switch functions.  These are interrupt service routines.
 */

/*
 * Manual context switch forced by calling portYIELD().  This is the SWI
 * handler.
 */
void vPortYield( void )
{
	portISR_HEAD();
	/* NOTE: This is the trap routine (swi) although not defined as a trap.
	   It will fill the stack the same way as an ISR in order to mix preemtion
	   and cooperative yield. */

	portSAVE_CONTEXT();
	vTaskSwitchContext();
	portRESTORE_CONTEXT();

	portISR_TAIL();
}
/*-----------------------------------------------------------*/

/*
 * RTOS tick interrupt service routine.  If the cooperative scheduler is 
 * being used then this simply increments the tick count.  If the 
 * preemptive scheduler is being used a context switch can occur.
 */
void vPortTickInterrupt( void )
{
	portISR_HEAD();

	/* Clear tick timer flag */
	CRGFLG = 0x80;

	#if configUSE_PREEMPTION == 1
	{
		/* A context switch might happen so save the context. */
		portSAVE_CONTEXT();

		/* Increment the tick ... */
		vTaskIncrementTick();

		/* ... then see if the new tick value has necessitated a
		context switch. */
		vTaskSwitchContext();

		/* Restore the context of a task - which may be a different task
		to that interrupted. */
		portRESTORE_CONTEXT();
	}
	#else
	{
		vTaskIncrementTick();
	}
	#endif

	portISR_TAIL();
}

