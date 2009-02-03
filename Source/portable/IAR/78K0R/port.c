/*
	FreeRTOS.org V5.1.1 - Copyright (C) 2003-2009 Richard Barry.

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

/* Standard includes. */
#include <stdlib.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

#define portINITIAL_CRITICAL_NESTING  (( unsigned portSHORT ) 10)

/* default Initialization of the PSW for the task:
 *   1100011000000000
 *   ||||||||-------------- Fill byte
 *   |||||||--------------- Cary Flag cleared
 *   |||||----------------- In-service priority Flags set to low level
 *   ||||------------------ Register bank Select 0 Flag cleared
 *   |||------------------- Auxiliary Cary Flag cleared
 *   ||-------------------- Register bank Select 1 Flag cleared
 *   |--------------------- Zero Flag set
 *   ---------------------- Global Interrupt Flag set (enabled)
 */
#define portPSW		  (0xc6000000UL)

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
volatile unsigned portSHORT usCriticalNesting = portINITIAL_CRITICAL_NESTING;
/*-----------------------------------------------------------*/

/*
 * The tick interrupt handler.
 */
__interrupt void MD_INTTM05( void );

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
		/* Parameters are passed in on the stack. */
		pxTopOfStack--;
		pulLocal =  ( unsigned long * ) pxTopOfStack;
		*pulLocal = ( unsigned long ) pvParameters;
		pxTopOfStack--;

		/* Dummy values on the stack because there normaly the return address
		of the funtion is written. */
		*pxTopOfStack = ( portSTACK_TYPE ) 0xcdcd;
		pxTopOfStack--;
		*pxTopOfStack = ( portSTACK_TYPE ) 0xcdcd;
		pxTopOfStack--;

		/* Initial PSW value. */
//		*pxTopOfStack = portPSW;
		
		pxTopOfStack--;

	
		/* Task function start address. */
		pulLocal = ( unsigned long * ) pxTopOfStack;
		*pulLocal = ( ( ( unsigned long ) pxCode ) | portPSW );
		pxTopOfStack--;

		/* Next general purpose register AX. */
		*pxTopOfStack = ( portSTACK_TYPE ) 0x1111;
		pxTopOfStack--;
	}
	#else
	{
		pxTopOfStack--;

		/* Task function start address. */
		pulLocal =  (unsigned long*) pxTopOfStack;
		*pulLocal = (unsigned long) pxCode;
		pxTopOfStack--;

		/* Initial PSW value. */
		*pxTopOfStack = portPSW;
		pxTopOfStack--;

		/* The parameter is passed in AX. */
		*pxTopOfStack = ( portSTACK_TYPE ) pvParameters;
		pxTopOfStack--;
	}
	#endif

	/* HL. */
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
	*pxTopOfStack = ( portSTACK_TYPE ) portNO_CRITICAL_SECTION_NESTING;	

	/*
	 * Return a pointer to the top of the stack we have generated so this can
	 * be stored in the task control block for the task.
	 */
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
	/* It is unlikely that the 78K0R/Kx3 port will get stopped.  If required simply
	disable the tick interrupt here. */
}
/*-----------------------------------------------------------*/

/*
 * Hardware initialisation to generate the RTOS tick.  This uses Channel 5 of
 * the Timer Array Unit (TAU). Any other Channel could also be used.
 */
static void prvSetupTimerInterrupt( void )
{
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

