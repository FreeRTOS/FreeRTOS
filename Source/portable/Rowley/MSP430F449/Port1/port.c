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

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the MSP430 port.
 *----------------------------------------------------------*/

/* Constants required for hardware setup.  The tick ISR runs off the ACLK, 
not the MCLK. */
#define portACLK_FREQUENCY_HZ			( ( portTickType ) 32768 )
#define portINITIAL_CRITICAL_NESTING	( ( unsigned portSHORT ) 10 )
#define portFLAGS_INT_ENABLED			( ( portSTACK_TYPE ) 0x08 )

/* We require the address of the pxCurrentTCB variable, but don't want to know
any details of its type. */
typedef void tskTCB;
extern volatile tskTCB * volatile pxCurrentTCB;

/* Each task maintains a count of the critical section nesting depth.  Each 
time a critical section is entered the count is incremented.  Each time a 
critical section is exited the count is decremented - with interrupts only 
being re-enabled if the count is zero.

usCriticalNesting will get set to zero when the scheduler starts, but must
not be initialised to zero as this will cause problems during the startup
sequence. */
volatile unsigned portSHORT usCriticalNesting = portINITIAL_CRITICAL_NESTING;
/*-----------------------------------------------------------*/


/*
 * Sets up the periodic ISR used for the RTOS tick.  This uses timer 0, but
 * could have alternatively used the watchdog timer or timer 1.
 */
void prvSetupTimerInterrupt( void );
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

	/* A variable is used to keep track of the critical section nesting.  
	This variable has to be stored as part of the task context and is 
	initially set to zero. */
	*pxTopOfStack = ( portSTACK_TYPE ) portNO_CRITICAL_SECTION_NESTING;	

	/* Return a pointer to the top of the stack we have generated so this can
	be stored in the task control block for the task. */
	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* It is unlikely that the MSP430 port will get stopped.  If required simply
	disable the tick interrupt here. */
}
/*-----------------------------------------------------------*/

/*
 * Hardware initialisation to generate the RTOS tick.  This uses timer 0
 * but could alternatively use the watchdog timer or timer 1. 
 */
void prvSetupTimerInterrupt( void )
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


	
