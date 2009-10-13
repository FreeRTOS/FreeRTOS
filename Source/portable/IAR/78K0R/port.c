/*
    FreeRTOS V6.0.0 - Copyright (C) 2009 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
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

/* Standard includes. */
#include <stdlib.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* The critical nesting value is initialised to a non zero value to ensure
interrupts don't accidentally become enabled before the scheduler is started. */
#define portINITIAL_CRITICAL_NESTING  (( unsigned short ) 10)

/* Initial PSW value allocated to a newly created task.
 *   1100011000000000
 *   ||||||||-------------- Fill byte
 *   |||||||--------------- Carry Flag cleared
 *   |||||----------------- In-service priority Flags set to low level
 *   ||||------------------ Register bank Select 0 Flag cleared
 *   |||------------------- Auxiliary Carry Flag cleared
 *   ||-------------------- Register bank Select 1 Flag cleared
 *   |--------------------- Zero Flag set
 *   ---------------------- Global Interrupt Flag set (enabled)
 */
#define portPSW		  (0xc6UL)

/* We require the address of the pxCurrentTCB variable, but don't want to know
any details of its type. */
typedef void tskTCB;
extern volatile tskTCB * volatile pxCurrentTCB;

/* Most ports implement critical sections by placing the interrupt flags on
the stack before disabling interrupts.  Exiting the critical section is then
simply a case of popping the flags from the stack.  As 78K0 IAR does not use
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
 * Sets up the periodic ISR used for the RTOS tick.
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
unsigned long *pulLocal;

	#if configMEMORY_MODE == 1
	{
		/* Parameters are passed in on the stack, and written using a 32bit value
		hence a space is left for the second two bytes. */
		pxTopOfStack--;

		/* Write in the parameter value. */
		pulLocal =  ( unsigned long * ) pxTopOfStack;
		*pulLocal = ( unsigned long ) pvParameters;
		pxTopOfStack--;

		/* These values are just spacers.  The return address of the function
		would normally be written here. */
		*pxTopOfStack = ( portSTACK_TYPE ) 0xcdcd;
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0xcdcd;
		pxTopOfStack--;

		/* The start address / PSW value is also written in as a 32bit value,
		so leave a space for the second two bytes. */
		pxTopOfStack--;
	
		/* Task function start address combined with the PSW. */
		pulLocal = ( unsigned long * ) pxTopOfStack;
		*pulLocal = ( ( ( unsigned long ) pxCode ) | ( portPSW << 24UL ) );
		pxTopOfStack--;

		/* An initial value for the AX register. */
		*pxTopOfStack = ( portSTACK_TYPE ) 0x1111;
		pxTopOfStack--;
	}
	#else
	{
		/* Task function address is written to the stack first.  As it is
		written as a 32bit value a space is left on the stack for the second
		two bytes. */
		pxTopOfStack--;

		/* Task function start address combined with the PSW. */
		pulLocal = ( unsigned long * ) pxTopOfStack;
		*pulLocal = ( ( ( unsigned long ) pxCode ) | ( portPSW << 24UL ) );
		pxTopOfStack--;

		/* The parameter is passed in AX. */
		*pxTopOfStack = ( portSTACK_TYPE ) pvParameters;
		pxTopOfStack--;
	}
	#endif

	/* An initial value for the HL register. */
	*pxTopOfStack = ( portSTACK_TYPE ) 0x2222;
	pxTopOfStack--;

	/* CS and ES registers. */
	*pxTopOfStack = ( portSTACK_TYPE ) 0x0F00;
	pxTopOfStack--;

	/* Finally the remaining general purpose registers DE and BC */
	*pxTopOfStack = ( portSTACK_TYPE ) 0xDEDE;
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0xBCBC;
	pxTopOfStack--;

	/* Finally the critical section nesting count is set to zero when the task
	first starts. */
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
	vPortStart();

	/* Should not get here as the tasks are now running! */
	return pdTRUE;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* It is unlikely that the 78K0R port will get stopped.  If required simply
	disable the tick interrupt here. */
}
/*-----------------------------------------------------------*/

static void prvSetupTimerInterrupt( void )
{
	/* Setup channel 5 of the TAU to generate the tick interrupt. */

	/* First the Timer Array Unit has to be enabled. */
	TAU0EN = 1;

	/* To configure the Timer Array Unit all Channels have to first be stopped. */
	TT0 = 0xff;

	/* Interrupt of Timer Array Unit Channel 5 is disabled to set the interrupt
	priority. */
	TMMK05 = 1;

	/* Clear Timer Array Unit Channel 5 interrupt flag. */	
	TMIF05 = 0;

	/* Set Timer Array Unit Channel 5 interrupt priority */
	TMPR005 = 0;
	TMPR105 = 0;

	/* Set Timer Array Unit Channel 5 Mode as interval timer. */
	TMR05 = 0x0000;

	/* Set the compare match value according to the tick rate we want. */
	TDR05 = ( portTickType ) ( configCPU_CLOCK_HZ / configTICK_RATE_HZ );

	/* Set Timer Array Unit Channel 5 output mode */
	TOM0 &= ~0x0020;

	/* Set Timer Array Unit Channel 5 output level */	
	TOL0 &= ~0x0020;

	/* Set Timer Array Unit Channel 5 output enable */	
	TOE0 &= ~0x0020;

	/* Interrupt of Timer Array Unit Channel 5 enabled */
	TMMK05 = 0;

	/* Start Timer Array Unit Channel 5.*/
	TS0 |= 0x0020;
}
/*-----------------------------------------------------------*/

