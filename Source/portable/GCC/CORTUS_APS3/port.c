/*
    FreeRTOS V7.0.2 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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

/* Standard includes. */
#include <stdlib.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Machine includes */
#include <machine/counter.h>
#include <machine/ic.h>
/*-----------------------------------------------------------*/

/* The initial PSR has the Previous Interrupt Enabled (PIEN) flag set. */
#define portINITIAL_PSR			( 0x00020000 )

/*-----------------------------------------------------------*/

/*
 * Perform any hardware configuration necessary to generate the tick interrupt.
 */
static void prvSetupTimerInterrupt( void );
/*-----------------------------------------------------------*/

portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE * pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
	/* Make space on the stack for the context - this leaves a couple of spaces
	empty.  */
	pxTopOfStack -= 20;

	/* Fill the registers with known values to assist debugging. */
	pxTopOfStack[ 16 ] = portKERNEL_INTERRUPT_PRIORITY_LEVEL;
	pxTopOfStack[ 15 ] = portINITIAL_PSR;
	pxTopOfStack[ 14 ] = ( unsigned long ) pxCode;
	pxTopOfStack[ 13 ] = 0x00000000UL; /* R15. */
	pxTopOfStack[ 12 ] = 0x00000000UL; /* R14. */
	pxTopOfStack[ 11 ] = 0x0d0d0d0dUL;
	pxTopOfStack[ 10 ] = 0x0c0c0c0cUL;
	pxTopOfStack[ 9 ] = 0x0b0b0b0bUL;
	pxTopOfStack[ 8 ] = 0x0a0a0a0aUL;
	pxTopOfStack[ 7 ] = 0x09090909UL;
	pxTopOfStack[ 6 ] = 0x08080808UL;
	pxTopOfStack[ 5 ] = 0x07070707UL;
	pxTopOfStack[ 4 ] = 0x06060606UL;
	pxTopOfStack[ 3 ] = 0x05050505UL;
	pxTopOfStack[ 2 ] = 0x04040404UL;
	pxTopOfStack[ 1 ] = 0x03030303UL;
	pxTopOfStack[ 0 ] = ( unsigned long ) pvParameters;

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
	/* Set-up the timer interrupt. */
	prvSetupTimerInterrupt();

	/* Enable the TRAP yield. */
	irq[ portIRQ_TRAP_YIELD ].ien = 1;
	irq[ portIRQ_TRAP_YIELD ].ipl = portKERNEL_INTERRUPT_PRIORITY_LEVEL;

	/* Integrated Interrupt Controller: Enable all interrupts. */
	ic->ien = 1;

	/* Restore callee saved registers. */
	portRESTORE_CONTEXT();

	/* Should not get here. */
	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupTimerInterrupt( void )
{
	/* Enable timer interrupts */
	counter1->reload = ( configCPU_CLOCK_HZ / configTICK_RATE_HZ ) - 1;
	counter1->value = counter1->reload;
	counter1->mask = 1;

	/* Set the IRQ Handler priority and enable it. */
	irq[ IRQ_COUNTER1 ].ien = 1;
	irq[ IRQ_COUNTER1 ].ipl = portKERNEL_INTERRUPT_PRIORITY_LEVEL;
}
/*-----------------------------------------------------------*/

/* Trap 31 handler. */
void interrupt31_handler( void ) __attribute__((naked));
void interrupt31_handler( void )
{
	portSAVE_CONTEXT();
	__asm volatile ( "call vTaskSwitchContext" );
	portRESTORE_CONTEXT();
}
/*-----------------------------------------------------------*/

static void prvProcessTick( void ) __attribute__((noinline));
static void prvProcessTick( void )
{
	vTaskIncrementTick();

	#if configUSE_PREEMPTION == 1
		vTaskSwitchContext();
	#endif

	/* Clear the Tick Interrupt. */
	counter1->expired = 0;
}
/*-----------------------------------------------------------*/

/* Timer 1 interrupt handler, used for tick interrupt. */
void interrupt7_handler( void ) __attribute__((naked));
void interrupt7_handler( void )
{
	portSAVE_CONTEXT();
	prvProcessTick();
	portRESTORE_CONTEXT();
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Nothing to do. Unlikely to want to end. */
}
/*-----------------------------------------------------------*/
