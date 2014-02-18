/*
    FreeRTOS V8.0.0 - Copyright (C) 2014 Real Time Engineers Ltd. 
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

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"


/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the HCS12 port.
 *----------------------------------------------------------*/


/*
 * Configure a timer to generate the RTOS tick at the frequency specified 
 * within FreeRTOSConfig.h.
 */
static void prvSetupTimerInterrupt( void );

/* Interrupt service routines have to be in non-banked memory - as does the
scheduler startup function. */
#pragma CODE_SEG __NEAR_SEG NON_BANKED

	/* Manual context switch function.  This is the SWI ISR. */
	void interrupt vPortYield( void );

	/* Tick context switch function.  This is the timer ISR. */
	void interrupt vPortTickInterrupt( void );
	
	/* Simply called by xPortStartScheduler().  xPortStartScheduler() does not
	start the scheduler directly because the header file containing the 
	xPortStartScheduler() prototype is part of the common kernel code, and 
	therefore cannot use the CODE_SEG pragma. */
	static BaseType_t xBankedStartScheduler( void );

#pragma CODE_SEG DEFAULT

/* Calls to portENTER_CRITICAL() can be nested.  When they are nested the 
critical section should not be left (i.e. interrupts should not be re-enabled)
until the nesting depth reaches 0.  This variable simply tracks the nesting 
depth.  Each task maintains it's own critical nesting depth variable so 
uxCriticalNesting is saved and restored from the task stack during a context
switch. */
volatile UBaseType_t uxCriticalNesting = 0xff;

/*-----------------------------------------------------------*/

/* 
 * See header file for description. 
 */
StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack, TaskFunction_t pxCode, void *pvParameters )
{
	/* 
		Place a few bytes of known values on the bottom of the stack.
		This can be uncommented to provide useful stack markers when debugging.

		*pxTopOfStack = ( StackType_t ) 0x11;
		pxTopOfStack--;
		*pxTopOfStack = ( StackType_t ) 0x22;
		pxTopOfStack--;
		*pxTopOfStack = ( StackType_t ) 0x33;
		pxTopOfStack--;
	*/



	/* Setup the initial stack of the task.  The stack is set exactly as 
	expected by the portRESTORE_CONTEXT() macro.  In this case the stack as
	expected by the HCS12 RTI instruction. */


	/* The address of the task function is placed in the stack byte at a time. */
	*pxTopOfStack = ( StackType_t ) *( ((StackType_t *) (&pxCode) ) + 1 );
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) *( ((StackType_t *) (&pxCode) ) + 0 );
	pxTopOfStack--;

	/* Next are all the registers that form part of the task context. */

	/* Y register */
	*pxTopOfStack = ( StackType_t ) 0xff;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0xee;
	pxTopOfStack--;

	/* X register */
	*pxTopOfStack = ( StackType_t ) 0xdd;
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) 0xcc;
	pxTopOfStack--;
 
	/* A register contains parameter high byte. */
	*pxTopOfStack = ( StackType_t ) *( ((StackType_t *) (&pvParameters) ) + 0 );
	pxTopOfStack--;

	/* B register contains parameter low byte. */
	*pxTopOfStack = ( StackType_t ) *( ((StackType_t *) (&pvParameters) ) + 1 );
	pxTopOfStack--;

	/* CCR: Note that when the task starts interrupts will be enabled since
	"I" bit of CCR is cleared */
	*pxTopOfStack = ( StackType_t ) 0x00;
	pxTopOfStack--;
	
	#ifdef BANKED_MODEL
		/* The page of the task. */
		*pxTopOfStack = ( StackType_t ) ( ( int ) pxCode );
		pxTopOfStack--;
	#endif
	
	/* Finally the critical nesting depth is initialised with 0 (not within
	a critical section). */
	*pxTopOfStack = ( StackType_t ) 0x00;

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
	TickTimer_SetFreqHz( configTICK_RATE_HZ );
	TickTimer_Enable();
}
/*-----------------------------------------------------------*/

BaseType_t xPortStartScheduler( void )
{
	/* xPortStartScheduler() does not start the scheduler directly because 
	the header file containing the xPortStartScheduler() prototype is part 
	of the common kernel code, and therefore cannot use the CODE_SEG pragma. 
	Instead it simply calls the locally defined xBankedStartScheduler() - 
	which does use the CODE_SEG pragma. */

	return xBankedStartScheduler();
}
/*-----------------------------------------------------------*/

#pragma CODE_SEG __NEAR_SEG NON_BANKED

static BaseType_t xBankedStartScheduler( void )
{
	/* Configure the timer that will generate the RTOS tick.  Interrupts are
	disabled when this function is called. */
	prvSetupTimerInterrupt();

	/* Restore the context of the first task. */
	portRESTORE_CONTEXT();

	/* Simulate the end of an interrupt to start the scheduler off. */
	__asm( "rti" );

	/* Should not get here! */
	return pdFALSE;
}
/*-----------------------------------------------------------*/

/*
 * Context switch functions.  These are both interrupt service routines.
 */

/*
 * Manual context switch forced by calling portYIELD().  This is the SWI
 * handler.
 */
void interrupt vPortYield( void )
{
	portSAVE_CONTEXT();
	vTaskSwitchContext();
	portRESTORE_CONTEXT();
}
/*-----------------------------------------------------------*/

/*
 * RTOS tick interrupt service routine.  If the cooperative scheduler is 
 * being used then this simply increments the tick count.  If the 
 * preemptive scheduler is being used a context switch can occur.
 */
void interrupt vPortTickInterrupt( void )
{
	#if configUSE_PREEMPTION == 1
	{
		/* A context switch might happen so save the context. */
		portSAVE_CONTEXT();

		/* Increment the tick ... */
		if( xTaskIncrementTick() != pdFALSE )
		{
			vTaskSwitchContext();
		}

		TFLG1 = 1;								   

		/* Restore the context of a task - which may be a different task
		to that interrupted. */
		portRESTORE_CONTEXT();	
	}
	#else
	{
		xTaskIncrementTick();
		TFLG1 = 1;
	}
	#endif
}

#pragma CODE_SEG DEFAULT


