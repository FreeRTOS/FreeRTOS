/*
    FreeRTOS V7.1.0 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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

/*
Changes from V1.00:

	+ Call to taskYIELD() from within tick ISR has been replaced by the more
	  efficient portSWITCH_CONTEXT().
	+ ISR function definitions renamed to include the prv prefix.

Changes from V2.6.1

	+ Replaced the sUsingPreemption variable with the configUSE_PREEMPTION
	  macro to be consistent with the later ports.
*/

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the Flashlite 186
 * port.
 *----------------------------------------------------------*/

#include <dos.h>
#include <stdlib.h>
#include <setjmp.h>

#include "FreeRTOS.h"
#include "task.h"
#include "portasm.h"

/*lint -e950 Non ANSI reserved words okay in this file only. */

#define portTIMER_EOI_TYPE		( 8 )
#define portRESET_PIC()			portOUTPUT_WORD( ( unsigned short ) 0xff22, portTIMER_EOI_TYPE )
#define portTIMER_INT_NUMBER	0x12

#define portTIMER_1_CONTROL_REGISTER	( ( unsigned short ) 0xff5e )
#define portTIMER_0_CONTROL_REGISTER	( ( unsigned short ) 0xff56 )
#define portTIMER_INTERRUPT_ENABLE		( ( unsigned short ) 0x2000 )

/* Setup the hardware to generate the required tick frequency. */
static void prvSetTickFrequency( unsigned long ulTickRateHz );

/* Set the hardware back to the state as per before the scheduler started. */
static void prvExitFunction( void );

/* The ISR used depends on whether the preemptive or cooperative scheduler
is being used. */
#if( configUSE_PREEMPTION == 1 )
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
static portBASE_TYPE xSchedulerRunning = pdFALSE;

/* Points to the original routine installed on the vector we use for manual
context switches.  This is then used to restore the original routine during
prvExitFunction(). */
static void ( __interrupt __far *pxOldSwitchISR )();

/* Used to restore the original DOS context when the scheduler is ended. */
static jmp_buf xJumpBuf;

/*lint +e956 */

/*-----------------------------------------------------------*/
portBASE_TYPE xPortStartScheduler( void )
{
	/* This is called with interrupts already disabled. */

	/* Remember what was on the interrupts we are going to use
	so we can put them back later if required. */
	pxOldSwitchISR = _dos_getvect( portSWITCH_INT_NUMBER );

	/* Put our manual switch (yield) function on a known
	vector. */
	_dos_setvect( portSWITCH_INT_NUMBER, prvYieldProcessor );

	#if( configUSE_PREEMPTION == 1 )
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
		xSchedulerRunning = pdFALSE;
	}
	else
	{
		xSchedulerRunning = pdTRUE;

		/* Kick off the scheduler by setting up the context of the first task. */
		portFIRST_CONTEXT();
	}

	return xSchedulerRunning;
}
/*-----------------------------------------------------------*/

/* The ISR used depends on whether the preemptive or cooperative scheduler
is being used. */
#if( configUSE_PREEMPTION == 1 )
	static void __interrupt __far prvPreemptiveTick( void )
	{
		/* Get the scheduler to update the task states following the tick. */
		vTaskIncrementTick();

		/* Switch in the context of the next task to be run. */
		portSWITCH_CONTEXT();

		/* Reset the PIC ready for the next time. */
		portRESET_PIC();
	}
#else
	static void __interrupt __far prvNonPreemptiveTick( void )
	{
		/* Same as preemptive tick, but the cooperative scheduler is being used
		so we don't have to switch in the context of the next task. */
		vTaskIncrementTick();
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
const unsigned short usTimerDisable = 0x0000;
unsigned short usTimer0Control;

	/* Interrupts should be disabled here anyway - but no
	harm in making sure. */
	portDISABLE_INTERRUPTS();
	if( xSchedulerRunning == pdTRUE )
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

static void prvSetTickFrequency( unsigned long ulTickRateHz )
{
const unsigned short usMaxCountRegister = 0xff5a;
const unsigned short usTimerPriorityRegister = 0xff32;
const unsigned short usTimerEnable = 0xC000;
const unsigned short usRetrigger = 0x0001;
const unsigned short usTimerHighPriority = 0x0000;
unsigned short usTimer0Control;

/* ( CPU frequency / 4 ) / clock 2 max count [inpw( 0xff62 ) = 7] */

const unsigned long ulClockFrequency = ( unsigned long ) 0x7f31a0UL;

unsigned long ulTimerCount = ulClockFrequency / ulTickRateHz;

	portOUTPUT_WORD( portTIMER_1_CONTROL_REGISTER, usTimerEnable | portTIMER_INTERRUPT_ENABLE | usRetrigger );
	portOUTPUT_WORD( usMaxCountRegister, ( unsigned short ) ulTimerCount );
	portOUTPUT_WORD( usTimerPriorityRegister, usTimerHighPriority );

	/* Stop the DOS tick - don't do this if you want to maintain a TOD clock. */
	usTimer0Control = portINPUT_WORD( portTIMER_0_CONTROL_REGISTER );
	usTimer0Control &= ~portTIMER_INTERRUPT_ENABLE;
	portOUTPUT_WORD( portTIMER_0_CONTROL_REGISTER, usTimer0Control );
}


/*lint +e950 */

