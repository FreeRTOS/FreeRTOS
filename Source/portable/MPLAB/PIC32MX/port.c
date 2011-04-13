/*
    FreeRTOS V7.0.0 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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
#define portSW0_ENABLE				( 0x00000100 )

/* The EXL bit is set to ensure interrupts do not occur while the context of
the first task is being restored. */
#define portINITIAL_SR				( portIE_BIT | portEXL_BIT | portSW0_ENABLE )

/* Records the interrupt nesting depth.  This starts at one as it will be
decremented to 0 when the first task starts. */
volatile unsigned portBASE_TYPE uxInterruptNesting = 0x01;

/* Stores the task stack pointer when a switch is made to use the system stack. */
unsigned portBASE_TYPE uxSavedTaskStackPointer = 0;

/* The stack used by interrupt service routines that cause a context switch. */
portSTACK_TYPE xISRStack[ configISR_STACK_SIZE ] = { 0 };

/* The top of stack value ensures there is enough space to store 6 registers on 
the callers stack, as some functions seem to want to do this. */
const portBASE_TYPE * const xISRStackTop = &( xISRStack[ configISR_STACK_SIZE - 7 ] );

/* 
 * Place the prototype here to ensure the interrupt vector is correctly installed. 
 * Note that because the interrupt is written in assembly, the IPL setting in the
 * following line of code has no effect.  The interrupt priority is set by the
 * call to ConfigIntTimer1() in prvSetupTimerInterrupt(). 
 */
extern void __attribute__( (interrupt(ipl1), vector(_TIMER_1_VECTOR))) vT1InterruptHandler( void );

/*
 * The software interrupt handler that performs the yield.  Note that, because
 * the interrupt is written in assembly, the IPL setting in the following line of
 * code has no effect.  The interrupt priority is set by the call to 
 * mConfigIntCoreSW0() in xPortStartScheduler(). 
 */
void __attribute__( (interrupt(ipl1), vector(_CORE_SOFTWARE_0_VECTOR))) vPortYieldISR( void );

/*-----------------------------------------------------------*/

/* 
 * See header file for description. 
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
	/* Ensure byte alignment is maintained when leaving this function. */
	pxTopOfStack--;

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

	*pxTopOfStack = (portSTACK_TYPE) 0x00000000; 	/* critical nesting level - no longer used. */
	pxTopOfStack--;
	
	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

/*
 * Setup a timer for a regular tick.
 */
void prvSetupTimerInterrupt( void )
{
const unsigned long ulCompareMatch = ( (configPERIPHERAL_CLOCK_HZ / portTIMER_PRESCALE) / configTICK_RATE_HZ ) - 1;

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

portBASE_TYPE xPortStartScheduler( void )
{
extern void vPortStartFirstTask( void );
extern void *pxCurrentTCB;

	/* Setup the software interrupt. */
	mConfigIntCoreSW0( CSW_INT_ON | configKERNEL_INTERRUPT_PRIORITY | CSW_INT_SUB_PRIOR_0 );

	/* Setup the timer to generate the tick.  Interrupts will have been 
	disabled by the time we get here. */
	prvSetupTimerInterrupt();

	/* Kick off the highest priority task that has been created so far. 
	Its stack location is loaded into uxSavedTaskStackPointer. */
	uxSavedTaskStackPointer = *( unsigned portBASE_TYPE * ) pxCurrentTCB;
	vPortStartFirstTask();

	/* Should never get here as the tasks will now be executing. */
	return pdFALSE;
}
/*-----------------------------------------------------------*/

void vPortIncrementTick( void )
{
unsigned portBASE_TYPE uxSavedStatus;

	uxSavedStatus = uxPortSetInterruptMaskFromISR();
		vTaskIncrementTick();
	vPortClearInterruptMaskFromISR( uxSavedStatus );
	
	/* If we are using the preemptive scheduler then we might want to select
	a different task to execute. */
	#if configUSE_PREEMPTION == 1
		SetCoreSW0();
	#endif /* configUSE_PREEMPTION */

	/* Clear timer 0 interrupt. */
	mT1ClearIntFlag();
}
/*-----------------------------------------------------------*/

unsigned portBASE_TYPE uxPortSetInterruptMaskFromISR( void )
{
unsigned portBASE_TYPE uxSavedStatusRegister;

	asm volatile ( "di" );
	uxSavedStatusRegister = _CP0_GET_STATUS() | 0x01;
	/* This clears the IPL bits, then sets them to 
	configMAX_SYSCALL_INTERRUPT_PRIORITY.  This function should not be called
	from an interrupt that has a priority above 
	configMAX_SYSCALL_INTERRUPT_PRIORITY so, when used correctly, the action
	can only result in the IPL being unchanged or raised, and therefore never
	lowered. */
	_CP0_SET_STATUS( ( ( uxSavedStatusRegister & ( ~portALL_IPL_BITS ) ) ) | ( configMAX_SYSCALL_INTERRUPT_PRIORITY << portIPL_SHIFT ) );

	return uxSavedStatusRegister;
}
/*-----------------------------------------------------------*/

void vPortClearInterruptMaskFromISR( unsigned portBASE_TYPE uxSavedStatusRegister )
{
	_CP0_SET_STATUS( uxSavedStatusRegister );
}
/*-----------------------------------------------------------*/





