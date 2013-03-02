/*
    FreeRTOS V7.4.0 - Copyright (C) 2013 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not itcan be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

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
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems, who sell the code with commercial support,
    indemnification and middleware, under the OpenRTOS brand.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Hardware includes. */
#include "port_iodefine.h"
#include "port_iodefine_ext.h"

/* The critical nesting value is initialised to a non zero value to ensure
interrupts don't accidentally become enabled before the scheduler is started. */
#define portINITIAL_CRITICAL_NESTING  ( ( unsigned short ) 10 )

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
#define portPSW		  ( 0xc6UL )

/* The address of the pxCurrentTCB variable, but don't know or need to know its
type. */
typedef void tskTCB;
extern volatile tskTCB * volatile pxCurrentTCB;

/* Each task maintains a count of the critical section nesting depth.  Each time
a critical section is entered the count is incremented.  Each time a critical
section is exited the count is decremented - with interrupts only being
re-enabled if the count is zero.

usCriticalNesting will get set to zero when the scheduler starts, but must
not be initialised to zero as that could cause problems during the startup
sequence. */
volatile unsigned short usCriticalNesting = portINITIAL_CRITICAL_NESTING;

/*-----------------------------------------------------------*/

/*
 * Sets up the periodic ISR used for the RTOS tick.
 */
static void prvSetupTimerInterrupt( void );

/*
 * Starts the scheduler by loading the context of the first task to run.
 * (defined in portasm.S).
 */
extern void vPortStartFirstTask( void );

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

	#if __DATA_MODEL__ == __DATA_MODEL_FAR__
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

	/* Return a pointer to the top of the stack that has beene generated so it
	can	be stored in the task control block for the task. */
	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
	/* Setup the hardware to generate the tick.  Interrupts are disabled when
	this function is called. */
	prvSetupTimerInterrupt();

	/* Restore the context of the first task that is going to run. */
	vPortStartFirstTask();

	/* Execution should not reach here as the tasks are now running! */
	return pdTRUE;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* It is unlikely that the RL78 port will get stopped. */
}
/*-----------------------------------------------------------*/

static void prvSetupTimerInterrupt( void )
{
const unsigned short usClockHz = 15000UL; /* Internal clock. */
const unsigned short usCompareMatch = ( usClockHz / configTICK_RATE_HZ ) + 1UL;

	/* Use the internal 15K clock. */
	OSMC = ( unsigned char ) 0x16;

	/* Supply the RTC clock. */
	RTCEN = ( unsigned char ) 1U;

	/* Disable ITMC operation. */
	ITMC = ( unsigned char ) 0x0000;

	/* Disable INTIT interrupt. */
	ITMK = ( unsigned char ) 1;

	/* Set INTIT high priority */
	ITPR1 = ( unsigned char ) 1;
	ITPR0 = ( unsigned char ) 1;

	/* Clear INIT interrupt. */
	ITIF = ( unsigned char ) 0;

	/* Set interval and enable interrupt operation. */
	ITMC = usCompareMatch | 0x8000U;

	/* Enable INTIT interrupt. */
	ITMK = ( unsigned char ) 0;
}
/*-----------------------------------------------------------*/


