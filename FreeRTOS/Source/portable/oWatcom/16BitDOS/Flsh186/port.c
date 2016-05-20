/*
    FreeRTOS V9.0.0 - Copyright (C) 2016 Real Time Engineers Ltd.
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

/*
Changes from V1.00:
	
	+ Call to taskYIELD() from within tick ISR has been replaced by the more
	  efficient portSWITCH_CONTEXT().
	+ ISR function definitions renamed to include the prv prefix.

Changes from V1.2.0:

	+ portRESET_PIC() is now called last thing before the end of the preemptive
	  tick routine.

Changes from V2.6.1

	+ Replaced the sUsingPreemption variable with the configUSE_PREEMPTION
	  macro to be consistent with the later ports.
*/

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the Flashlite 186
 * port.
 *----------------------------------------------------------*/

#include <stdlib.h>
#include <i86.h>
#include <dos.h>
#include <setjmp.h>

#include "FreeRTOS.h"
#include "task.h"
#include "portasm.h"

/*lint -e950 Non ANSI reserved words okay in this file only. */

#define portTIMER_EOI_TYPE		( 8 )
#define portRESET_PIC()			portOUTPUT_WORD( ( uint16_t ) 0xff22, portTIMER_EOI_TYPE )
#define portTIMER_INT_NUMBER	0x12

#define portTIMER_1_CONTROL_REGISTER	( ( uint16_t ) 0xff5e )
#define portTIMER_0_CONTROL_REGISTER	( ( uint16_t ) 0xff56 )
#define portTIMER_INTERRUPT_ENABLE		( ( uint16_t ) 0x2000 )

/* Setup the hardware to generate the required tick frequency. */
static void prvSetTickFrequency( uint32_t ulTickRateHz );

/* Set the hardware back to the state as per before the scheduler started. */
static void prvExitFunction( void );

#if configUSE_PREEMPTION == 1
	/* Tick service routine used by the scheduler when preemptive scheduling is
	being used. */
	static void __interrupt __far prvPreemptiveTick( void );
#else
	/* Tick service routine used by the scheduler when cooperative scheduling is 
	being used. */
	static void __interrupt __far prvNonPreemptiveTick( void );
#endif

/* Trap routine used by taskYIELD() to manually cause a context switch. */
static void __interrupt __far prvYieldProcessor( void );

/*lint -e956 File scopes necessary here. */

/* Set true when the vectors are set so the scheduler will service the tick. */
static int16_t sSchedulerRunning = pdFALSE;

/* Points to the original routine installed on the vector we use for manual context switches.  This is then used to restore the original routine during prvExitFunction(). */
static void ( __interrupt __far *pxOldSwitchISR )();

/* Used to restore the original DOS context when the scheduler is ended. */
static jmp_buf xJumpBuf;

/*lint +e956 */

/*-----------------------------------------------------------*/
BaseType_t xPortStartScheduler( void )
{
	/* This is called with interrupts already disabled. */

	/* Remember what was on the interrupts we are going to use
	so we can put them back later if required. */
	pxOldSwitchISR = _dos_getvect( portSWITCH_INT_NUMBER );

	/* Put our manual switch (yield) function on a known
	vector. */
	_dos_setvect( portSWITCH_INT_NUMBER, prvYieldProcessor );

	#if configUSE_PREEMPTION == 1
	{		
		/* Put our tick switch function on the timer interrupt. */
		_dos_setvect( portTIMER_INT_NUMBER, prvPreemptiveTick );
	}
	#else
	{
		/* We want the timer interrupt to just increment the tick count. */
		_dos_setvect( portTIMER_INT_NUMBER, prvNonPreemptiveTick );
	}
	#endif

	prvSetTickFrequency( configTICK_RATE_HZ );

	/* Clean up function if we want to return to DOS. */
	if( setjmp( xJumpBuf ) != 0 )
	{
		prvExitFunction();
		sSchedulerRunning = pdFALSE;
	}
	else
	{
		sSchedulerRunning = pdTRUE;

		/* Kick off the scheduler by setting up the context of the first task. */
		portFIRST_CONTEXT();
	}

	return sSchedulerRunning;
}
/*-----------------------------------------------------------*/

/* The tick ISR used depend on whether or not the preemptive or cooperative
kernel is being used. */
#if configUSE_PREEMPTION == 1
	static void __interrupt __far prvPreemptiveTick( void )
	{
		/* Get the scheduler to update the task states following the tick. */
		if( xTaskIncrementTick() != pdFALSE )
		{
			/* Switch in the context of the next task to be run. */
			portSWITCH_CONTEXT();
		}

		/* Reset the PIC ready for the next time. */
		portRESET_PIC();
	}
#else
	static void __interrupt __far prvNonPreemptiveTick( void )
	{
		/* Same as preemptive tick, but the cooperative scheduler is being used
		so we don't have to switch in the context of the next task. */
		xTaskIncrementTick();
		portRESET_PIC();
	}
#endif
/*-----------------------------------------------------------*/

static void __interrupt __far prvYieldProcessor( void )
{
	/* Switch in the context of the next task to be run. */
	portSWITCH_CONTEXT();
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Jump back to the processor state prior to starting the
	scheduler.  This means we are not going to be using a
	task stack frame so the task can be deleted. */
	longjmp( xJumpBuf, 1 );
}
/*-----------------------------------------------------------*/

static void prvExitFunction( void )
{
const uint16_t usTimerDisable = 0x0000;
uint16_t usTimer0Control;

	/* Interrupts should be disabled here anyway - but no 
	harm in making sure. */
	portDISABLE_INTERRUPTS();
	if( sSchedulerRunning == pdTRUE )
	{
		/* Put back the switch interrupt routines that was in place
		before the scheduler started. */
		_dos_setvect( portSWITCH_INT_NUMBER, pxOldSwitchISR );
	}

	/* Disable the timer used for the tick to ensure the scheduler is
	not called before restoring interrupts.  There was previously nothing
	on this timer so there is no old ISR to restore. */
	portOUTPUT_WORD( portTIMER_1_CONTROL_REGISTER, usTimerDisable );

	/* Restart the DOS tick. */
	usTimer0Control = portINPUT_WORD( portTIMER_0_CONTROL_REGISTER );
	usTimer0Control |= portTIMER_INTERRUPT_ENABLE;
	portOUTPUT_WORD( portTIMER_0_CONTROL_REGISTER, usTimer0Control );


	portENABLE_INTERRUPTS();
}
/*-----------------------------------------------------------*/

static void prvSetTickFrequency( uint32_t ulTickRateHz )
{
const uint16_t usMaxCountRegister = 0xff5a;
const uint16_t usTimerPriorityRegister = 0xff32;
const uint16_t usTimerEnable = 0xC000;
const uint16_t usRetrigger = 0x0001;
const uint16_t usTimerHighPriority = 0x0000;
uint16_t usTimer0Control;

/* ( CPU frequency / 4 ) / clock 2 max count [inpw( 0xff62 ) = 7] */

const uint32_t ulClockFrequency = 0x7f31a0;

uint32_t ulTimerCount = ulClockFrequency / ulTickRateHz;

	portOUTPUT_WORD( portTIMER_1_CONTROL_REGISTER, usTimerEnable | portTIMER_INTERRUPT_ENABLE | usRetrigger );
	portOUTPUT_WORD( usMaxCountRegister, ( uint16_t ) ulTimerCount );
	portOUTPUT_WORD( usTimerPriorityRegister, usTimerHighPriority );

	/* Stop the DOS tick - don't do this if you want to maintain a TOD clock. */
	usTimer0Control = portINPUT_WORD( portTIMER_0_CONTROL_REGISTER );
	usTimer0Control &= ~portTIMER_INTERRUPT_ENABLE;
	portOUTPUT_WORD( portTIMER_0_CONTROL_REGISTER, usTimer0Control );
}


/*lint +e950 */

