/*
    FreeRTOS V9.0.1 - Copyright (C) 2017 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* The critical nesting value is initialised to a non zero value to ensure
interrupts don't accidentally become enabled before the scheduler is started. */
#define portINITIAL_CRITICAL_NESTING  ( ( uint16_t ) 10 )

/* Initial PSW value allocated to a newly created task.
 *   11000110
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

/* Each task maintains a count of the critical section nesting depth.  Each time
a critical section is entered the count is incremented.  Each time a critical
section is exited the count is decremented - with interrupts only being
re-enabled if the count is zero.

usCriticalNesting will get set to zero when the scheduler starts, but must
not be initialised to zero as that could cause problems during the startup
sequence. */
volatile uint16_t usCriticalNesting = portINITIAL_CRITICAL_NESTING;

/*-----------------------------------------------------------*/

/*
 * Sets up the periodic ISR used for the RTOS tick.
 */
__attribute__((weak)) void vApplicationSetupTimerInterrupt( void );

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
StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack, TaskFunction_t pxCode, void *pvParameters )
{
uint32_t *pulLocal;

	/* Stack type and pointers to the stack type are both 2 bytes. */

	/* Parameters are passed in on the stack, and written using a 32bit value
	hence a space is left for the second two bytes. */
	pxTopOfStack--;

	/* Write in the parameter value. */
	pulLocal =  ( uint32_t * ) pxTopOfStack;
	*pulLocal = ( StackType_t ) pvParameters;
	pxTopOfStack--;

	/* The return address, leaving space for the first two bytes of	the
	32-bit value. */
	pxTopOfStack--;
	pulLocal = ( uint32_t * ) pxTopOfStack;
	*pulLocal = ( uint32_t ) 0;
	pxTopOfStack--;

	/* The start address / PSW value is also written in as a 32bit value,
	so leave a space for the second two bytes. */
	pxTopOfStack--;

	/* Task function start address combined with the PSW. */
	pulLocal = ( uint32_t * ) pxTopOfStack;
	*pulLocal = ( ( ( uint32_t ) pxCode ) | ( portPSW << 24UL ) );
	pxTopOfStack--;

	/* An initial value for the AX register. */
	*pxTopOfStack = ( StackType_t ) 0x1111;
	pxTopOfStack--;

	/* An initial value for the HL register. */
	*pxTopOfStack = ( StackType_t ) 0x2222;
	pxTopOfStack--;

	/* CS and ES registers. */
	*pxTopOfStack = ( StackType_t ) 0x0F00;
	pxTopOfStack--;

	/* The remaining general purpose registers bank 0 (DE and BC) and the other
	two register banks...register bank 3 is dedicated for use by interrupts so
	is not saved as part of the task context. */
	pxTopOfStack -= 10;

	/* Finally the critical section nesting count is set to zero when the task
	first starts. */
	*pxTopOfStack = ( StackType_t ) portNO_CRITICAL_SECTION_NESTING;

	/* Return a pointer to the top of the stack that has beene generated so it
	can	be stored in the task control block for the task. */
	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
	/* Setup the hardware to generate the tick.  Interrupts are disabled when
	this function is called. */
	vApplicationSetupTimerInterrupt();

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

__attribute__((weak)) void vApplicationSetupTimerInterrupt( void )
{
const uint16_t usClockHz = 15000UL; /* Internal clock. */
const uint16_t usCompareMatch = ( usClockHz / configTICK_RATE_HZ ) + 1UL;

	/* Use the internal 15K clock. */
	OSMC = ( unsigned char ) 0x16;

	#ifdef RTCEN
	{
		/* Supply the interval timer clock. */
		RTCEN = ( unsigned char ) 1U;

		/* Disable INTIT interrupt. */
		ITMK = ( unsigned char ) 1;

		/* Disable ITMC operation. */
		ITMC = ( unsigned char ) 0x0000;

		/* Clear INIT interrupt. */
		ITIF = ( unsigned char ) 0;

		/* Set interval and enable interrupt operation. */
		ITMC = usCompareMatch | 0x8000U;

		/* Enable INTIT interrupt. */
		ITMK = ( unsigned char ) 0;
	}
	#endif

	#ifdef TMKAEN
	{
		/* Supply the interval timer clock. */
		TMKAEN = ( unsigned char ) 1U;

		/* Disable INTIT interrupt. */
		TMKAMK = ( unsigned char ) 1;

		/* Disable ITMC operation. */
		ITMC = ( unsigned char ) 0x0000;

		/* Clear INIT interrupt. */
		TMKAIF = ( unsigned char ) 0;

		/* Set interval and enable interrupt operation. */
		ITMC = usCompareMatch | 0x8000U;

		/* Enable INTIT interrupt. */
		TMKAMK = ( unsigned char ) 0;
	}
	#endif
}
/*-----------------------------------------------------------*/

