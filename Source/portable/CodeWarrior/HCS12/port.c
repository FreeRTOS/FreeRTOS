/* 
	FreeRTOS.org V5.0.2 - Copyright (C) 2003-2008 Richard Barry.

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
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
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
	static portBASE_TYPE xBankedStartScheduler( void );

#pragma CODE_SEG DEFAULT

/* Calls to portENTER_CRITICAL() can be nested.  When they are nested the 
critical section should not be left (i.e. interrupts should not be re-enabled)
until the nesting depth reaches 0.  This variable simply tracks the nesting 
depth.  Each task maintains it's own critical nesting depth variable so 
uxCriticalNesting is saved and restored from the task stack during a context
switch. */
volatile unsigned portBASE_TYPE uxCriticalNesting = 0xff;

/*-----------------------------------------------------------*/

/* 
 * See header file for description. 
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
	/* 
		Place a few bytes of known values on the bottom of the stack.
		This can be uncommented to provide useful stack markers when debugging.

		*pxTopOfStack = ( portSTACK_TYPE ) 0x11;
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x22;
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0x33;
		pxTopOfStack--;
	*/



	/* Setup the initial stack of the task.  The stack is set exactly as 
	expected by the portRESTORE_CONTEXT() macro.  In this case the stack as
	expected by the HCS12 RTI instruction. */


	/* The address of the task function is placed in the stack byte at a time. */
	*pxTopOfStack = ( portSTACK_TYPE ) *( ((portSTACK_TYPE *) (&pxCode) ) + 1 );
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) *( ((portSTACK_TYPE *) (&pxCode) ) + 0 );
	pxTopOfStack--;

	/* Next are all the registers that form part of the task context. */

	/* Y register */
	*pxTopOfStack = ( portSTACK_TYPE ) 0xff;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xee;
	pxTopOfStack--;

	/* X register */
	*pxTopOfStack = ( portSTACK_TYPE ) 0xdd;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xcc;
	pxTopOfStack--;
 
	/* A register contains parameter high byte. */
	*pxTopOfStack = ( portSTACK_TYPE ) *( ((portSTACK_TYPE *) (&pvParameters) ) + 0 );
	pxTopOfStack--;

	/* B register contains parameter low byte. */
	*pxTopOfStack = ( portSTACK_TYPE ) *( ((portSTACK_TYPE *) (&pvParameters) ) + 1 );
	pxTopOfStack--;

	/* CCR: Note that when the task starts interrupts will be enabled since
	"I" bit of CCR is cleared */
	*pxTopOfStack = ( portSTACK_TYPE ) 0x00;
	pxTopOfStack--;
	
	#ifdef BANKED_MODEL
		/* The page of the task. */
		*pxTopOfStack = ( portSTACK_TYPE ) ( ( int ) pxCode );
		pxTopOfStack--;
	#endif
	
	/* Finally the critical nesting depth is initialised with 0 (not within
	a critical section). */
	*pxTopOfStack = ( portSTACK_TYPE ) 0x00;

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

portBASE_TYPE xPortStartScheduler( void )
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

static portBASE_TYPE xBankedStartScheduler( void )
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
		vTaskIncrementTick();

		/* ... then see if the new tick value has necessitated a
		context switch. */
		vTaskSwitchContext();

		TFLG1 = 1;								   

		/* Restore the context of a task - which may be a different task
		to that interrupted. */
		portRESTORE_CONTEXT();	
	}
	#else
	{
		vTaskIncrementTick();
		TFLG1 = 1;
	}
	#endif
}

#pragma CODE_SEG DEFAULT


