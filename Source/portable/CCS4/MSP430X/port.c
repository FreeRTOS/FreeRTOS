/*
    FreeRTOS V6.1.0 - Copyright (C) 2010 Real Time Engineers Ltd.

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

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the MSP430X port.
 *----------------------------------------------------------*/

/* Constants required for hardware setup.  The tick ISR runs off the ACLK,
not the MCLK. */
#define portACLK_FREQUENCY_HZ			( ( portTickType ) 32768 )
#define portINITIAL_CRITICAL_NESTING	( ( unsigned short ) 10 )
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
volatile unsigned short usCriticalNesting = portINITIAL_CRITICAL_NESTING;
/*-----------------------------------------------------------*/


/*
 * Sets up the periodic ISR used for the RTOS tick.  This uses timer 0, but
 * could have alternatively used the watchdog timer or timer 1.
 */
void vPortSetupTimerInterrupt( void );
/*-----------------------------------------------------------*/

/*
 * Initialise the stack of a task to look exactly as if a call to
 * portSAVE_CONTEXT had been called.
 *
 * See the header file portable.h.
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
unsigned short *pusTopOfStack;

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

	*pxTopOfStack = ( portSTACK_TYPE ) pxCode;
	pusTopOfStack = ( unsigned short * ) pxTopOfStack;
	pusTopOfStack--;
	*pusTopOfStack = portFLAGS_INT_ENABLED;
	pusTopOfStack -= 2;
	pxTopOfStack = ( portSTACK_TYPE * ) pusTopOfStack;

	/* Next the general purpose registers. */
	*pxTopOfStack = ( portSTACK_TYPE ) 0xffffff;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xeeeeee;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xdddddd;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) pvParameters;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xbbbbbb;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xaaaaaa;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x999999;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x888888;
	pxTopOfStack--;	
	*pxTopOfStack = ( portSTACK_TYPE ) 0x555555;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x666666;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x555555;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x444444;
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
 * Hardware initialisation to generate the RTOS tick.
 */
void vPortSetupTimerInterrupt( void )
{
	vApplicationSetupTimerInterrupt();
}
/*-----------------------------------------------------------*/

#pragma vector=configTICK_INTERRUPT_VECTOR
interrupt void vTickISREntry( void )
{
extern void vPortTickISR( void );

	#if configUSE_PREEMPTION == 1
		extern void vPortPreemptiveTickISR( void );
		vPortPreemptiveTickISR();
	#else
		extern void vPortCooperativeTickISR( void );
		vPortCooperativeTickISR();
	#endif
}

	
