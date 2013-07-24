/*
    FreeRTOS V7.5.2 - Copyright (C) 2013 Real Time Engineers Ltd.

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

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
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the PIC32MX port.
  *----------------------------------------------------------*/

#ifndef __XC
    #error This port is designed to work with XC32.  Please update your C compiler version.
#endif

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Hardware specifics. */
#define portTIMER_PRESCALE	8
#define portPRESCALE_BITS	1

/* Bits within various registers. */
#define portIE_BIT						( 0x00000001 )
#define portEXL_BIT						( 0x00000002 )

/* Bits within the CAUSE register. */
#define portCORE_SW_0					( 0x00000100 )
#define portCORE_SW_1					( 0x00000200 )

/* The EXL bit is set to ensure interrupts do not occur while the context of
the first task is being restored. */
#define portINITIAL_SR					( portIE_BIT | portEXL_BIT )

#ifndef configTICK_INTERRUPT_VECTOR
	#define configTICK_INTERRUPT_VECTOR _TIMER_1_VECTOR
#endif

/* Records the interrupt nesting depth.  This starts at one as it will be
decremented to 0 when the first task starts. */
volatile unsigned portBASE_TYPE uxInterruptNesting = 0x01;

/* Stores the task stack pointer when a switch is made to use the system stack. */
unsigned portBASE_TYPE uxSavedTaskStackPointer = 0;

/* The stack used by interrupt service routines that cause a context switch. */
portSTACK_TYPE xISRStack[ configISR_STACK_SIZE ] = { 0 };

/* The top of stack value ensures there is enough space to store 6 registers on
the callers stack, as some functions seem to want to do this. */
const portSTACK_TYPE * const xISRStackTop = &( xISRStack[ configISR_STACK_SIZE - 7 ] );

/*
 * Place the prototype here to ensure the interrupt vector is correctly installed.
 * Note that because the interrupt is written in assembly, the IPL setting in the
 * following line of code has no effect.  The interrupt priority is set by the
 * call to ConfigIntTimer1() in vApplicationSetupTickTimerInterrupt().
 */
extern void __attribute__( (interrupt(ipl1), vector( configTICK_INTERRUPT_VECTOR ))) vPortTickInterruptHandler( void );

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
 * Setup a timer for a regular tick.  This function uses peripheral timer 1.
 * The function is declared weak so an application writer can use a different
 * timer by redefining this implementation.  If a different timer is used then
 * configTICK_INTERRUPT_VECTOR must also be defined in FreeRTOSConfig.h to
 * ensure the RTOS provided tick interrupt handler is installed on the correct
 * vector number.  When Timer 1 is used the vector number is defined as
 * _TIMER_1_VECTOR.
 */
__attribute__(( weak )) void vApplicationSetupTickTimerInterrupt( void )
{
const unsigned long ulCompareMatch = ( (configPERIPHERAL_CLOCK_HZ / portTIMER_PRESCALE) / configTICK_RATE_HZ ) - 1;

	T1CON = 0x0000;
	T1CONbits.TCKPS = portPRESCALE_BITS;
	PR1 = ulCompareMatch;
	IPC1bits.T1IP = configKERNEL_INTERRUPT_PRIORITY;

	/* Clear the interrupt as a starting condition. */
	IFS0bits.T1IF = 0;

	/* Enable the interrupt. */
	IEC0bits.T1IE = 1;

	/* Start the timer. */
	T1CONbits.TON = 1;
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

	/* Clear the software interrupt flag. */
	IFS0CLR = _IFS0_CS0IF_MASK;

	/* Set software timer priority. */
	IPC0CLR = _IPC0_CS0IP_MASK;
	IPC0SET = ( configKERNEL_INTERRUPT_PRIORITY << _IPC0_CS0IP_POSITION );

	/* Enable software interrupt. */
	IEC0CLR = _IEC0_CS0IE_MASK;
	IEC0SET = 1 << _IEC0_CS0IE_POSITION;

	/* Setup the timer to generate the tick.  Interrupts will have been
	disabled by the time we get here. */
	vApplicationSetupTickTimerInterrupt();

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
	{
		if( xTaskIncrementTick() != pdFALSE )
		{
			/* Pend a context switch. */
			_CP0_BIS_CAUSE( portCORE_SW_0 );
		}
	}
	vPortClearInterruptMaskFromISR( uxSavedStatus );

	/* Clear timer 1 interrupt. */
	IFS0CLR = _IFS0_T1IF_MASK;
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





