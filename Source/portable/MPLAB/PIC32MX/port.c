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

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the PIC32MX port.
  *----------------------------------------------------------*/

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Hardware specifics. */
#define portTIMER_PRESCALE 8

/* Bits within various registers. */
#define portIE_BIT					( 0x00000001 )
#define portEXL_BIT					( 0x00000002 )
#define portIPL_SHIFT				( 10 )
#define portALL_IPL_BITS			( 0x1f << portIPL_SHIFT )

/* The EXL bit is set to ensure interrupts do not occur while the context of
the first task is being restored. */
#define portINITIAL_SR				( portIE_BIT | portEXL_BIT )

/* Records the nesting depth of calls to portENTER_CRITICAL(). */
unsigned portBASE_TYPE uxCriticalNesting = 0x55555555;

/* The stack used by interrupt service routines that cause a context switch. */
portSTACK_TYPE xISRStack[ configISR_STACK_SIZE ] = { 0 };

/* The top of stack value ensures there is enough space to store 6 registers on 
the callers stack, as some functions seem to want to do this. */
const portBASE_TYPE * const xISRStackTop = &( xISRStack[ configISR_STACK_SIZE - 7 ] );

/* Place the prototype here to ensure the interrupt vector is correctly installed. */
extern void __attribute__( (interrupt(ipl1), vector(_TIMER_1_VECTOR))) vT1InterruptHandler( void );

/* 
 * General exception handler that will be called for all general exceptions
 * other than SYS.  This should be overridden by a user provided handler.
 */
void vApplicationGeneralExceptionHandler( unsigned portLONG ulCause, unsigned portLONG ulStatus ) __attribute__((weak));

/*-----------------------------------------------------------*/

/* 
 * See header file for description. 
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
	*pxTopOfStack = (portSTACK_TYPE) 0xDEADBEEF;
	pxTopOfStack--;

	*pxTopOfStack = (portSTACK_TYPE) 0x12345678;	/* Word to which the stack pointer will be left pointing after context restore. */
	pxTopOfStack--;

	*pxTopOfStack = (portSTACK_TYPE) _CP0_GET_CAUSE();
	pxTopOfStack--;

	*pxTopOfStack = (portSTACK_TYPE) portINITIAL_SR; /* CP0_STATUS */
	pxTopOfStack--;

	*pxTopOfStack = (portSTACK_TYPE) pxCode; 		/* CP0_EPC */
	pxTopOfStack--;

	*pxTopOfStack = (portSTACK_TYPE) NULL;  		/* ra */
	pxTopOfStack -= 15;

	*pxTopOfStack = (portSTACK_TYPE) pvParameters; /* Parameters to pass in */
	pxTopOfStack -= 14;

	*pxTopOfStack = (portSTACK_TYPE) 0x00000000; 	/* critical nesting level */
	pxTopOfStack--;
	
	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

/*
 * Setup a timer for a regular tick.
 */
void prvSetupTimerInterrupt( void )
{
const unsigned portLONG ulCompareMatch = (configPERIPHERAL_CLOCK_HZ / portTIMER_PRESCALE) / configTICK_RATE_HZ;

	OpenTimer1( ( T1_ON | T1_PS_1_8 | T1_SOURCE_INT ), ulCompareMatch );
	ConfigIntTimer1( T1_INT_ON | configKERNEL_INTERRUPT_PRIORITY );
}
/*-----------------------------------------------------------*/

void vPortEndScheduler(void)
{
	/* It is unlikely that the scheduler for the PIC port will get stopped
	once running.  If required disable the tick interrupt here, then return 
	to xPortStartScheduler(). */
	for( ;; );
}
/*-----------------------------------------------------------*/

void vPortEnterCritical(void)
{
unsigned portLONG ulStatus;

	/* Mask interrupts at and below the kernel interrupt priority. */
	ulStatus = _CP0_GET_STATUS();
	ulStatus |= ( configKERNEL_INTERRUPT_PRIORITY << portIPL_SHIFT );
	_CP0_SET_STATUS( ulStatus );

	/* Once interrupts are disabled we can access the nesting count directly. */
	uxCriticalNesting++;
}
/*-----------------------------------------------------------*/

void vPortExitCritical(void)
{
unsigned portLONG ulStatus;

	/* If we are in a critical section then we can access the nesting count
	directly. */
	uxCriticalNesting--;

	/* Has the nesting unwound? */
	if( uxCriticalNesting == 0 ) 
	{
		/* Unmask all interrupts. */
		ulStatus = _CP0_GET_STATUS();
		ulStatus &= ~portALL_IPL_BITS;
		_CP0_SET_STATUS( ulStatus );
	}
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
extern void vPortStartFirstTask( void );

	/* Setup the timer to generate the tick.  Interrupts will have been 
	disabled by the time we get here. */
	prvSetupTimerInterrupt();

	/* Kick off the highest priority task that has been created so far. */
	vPortStartFirstTask();

	/* Should never get here as the tasks will now be executing. */
	return pdFALSE;
}
/*-----------------------------------------------------------*/

void vApplicationGeneralExceptionHandler( unsigned portLONG ulCause, unsigned portLONG ulStatus )
{
	/* This function is declared weak and should be overridden by the users
	application. */
	while( 1 );
}





