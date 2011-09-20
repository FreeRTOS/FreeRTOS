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

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the Philips ARM7 port.
 *----------------------------------------------------------*/

/*
	Changes from V3.2.2

	+ Bug fix - The prescale value for the timer setup is now written to T0PR
	  instead of T0PC.  This bug would have had no effect unless a prescale
	  value was actually used.
*/

/* Standard includes. */
#include <stdlib.h>
#include <intrinsics.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Constants required to setup the tick ISR. */
#define portENABLE_TIMER			( ( unsigned char ) 0x01 )
#define portPRESCALE_VALUE			0x00
#define portINTERRUPT_ON_MATCH		( ( unsigned long ) 0x01 )
#define portRESET_COUNT_ON_MATCH	( ( unsigned long ) 0x02 )

/* Constants required to setup the initial stack. */
#define portINITIAL_SPSR				( ( portSTACK_TYPE ) 0x1f ) /* System mode, ARM mode, interrupts enabled. */
#define portTHUMB_MODE_BIT				( ( portSTACK_TYPE ) 0x20 )
#define portINSTRUCTION_SIZE			( ( portSTACK_TYPE ) 4 )

/* Constants required to setup the PIT. */
#define portPIT_CLOCK_DIVISOR			( ( unsigned long ) 16 )
#define portPIT_COUNTER_VALUE			( ( ( configCPU_CLOCK_HZ / portPIT_CLOCK_DIVISOR ) / 1000UL ) * portTICK_RATE_MS )

/* Constants required to handle interrupts. */
#define portTIMER_MATCH_ISR_BIT		( ( unsigned char ) 0x01 )
#define portCLEAR_VIC_INTERRUPT		( ( unsigned long ) 0 )

/* Constants required to handle critical sections. */
#define portNO_CRITICAL_NESTING 		( ( unsigned long ) 0 )


#define portINT_LEVEL_SENSITIVE  0
#define portPIT_ENABLE      	( ( unsigned short ) 0x1 << 24 )
#define portPIT_INT_ENABLE     	( ( unsigned short ) 0x1 << 25 )

/* Constants required to setup the VIC for the tick ISR. */
#define portTIMER_VIC_CHANNEL		( ( unsigned long ) 0x0004 )
#define portTIMER_VIC_CHANNEL_BIT	( ( unsigned long ) 0x0010 )
#define portTIMER_VIC_ENABLE		( ( unsigned long ) 0x0020 )

/*-----------------------------------------------------------*/

/* Setup the PIT to generate the tick interrupts. */
static void prvSetupTimerInterrupt( void );

/* ulCriticalNesting will get set to zero when the first task starts.  It
cannot be initialised to 0 as this will cause interrupts to be enabled
during the kernel initialisation process. */
unsigned long ulCriticalNesting = ( unsigned long ) 9999;

/*-----------------------------------------------------------*/

/*
 * Initialise the stack of a task to look exactly as if a call to
 * portSAVE_CONTEXT had been called.
 *
 * See header file for description.
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
portSTACK_TYPE *pxOriginalTOS;

	pxOriginalTOS = pxTopOfStack;

	/* Setup the initial stack of the task.  The stack is set exactly as
	expected by the portRESTORE_CONTEXT() macro. */

	/* First on the stack is the return address - which in this case is the
	start of the task.  The offset is added to make the return address appear
	as it would within an IRQ ISR. */
	*pxTopOfStack = ( portSTACK_TYPE ) pxCode + portINSTRUCTION_SIZE;		
	pxTopOfStack--;

	*pxTopOfStack = ( portSTACK_TYPE ) 0xaaaaaaaa;	/* R14 */
	pxTopOfStack--;	
	*pxTopOfStack = ( portSTACK_TYPE ) pxOriginalTOS; /* Stack used when task starts goes in R13. */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) 0x12121212;	/* R12 */
	pxTopOfStack--;	
	*pxTopOfStack = ( portSTACK_TYPE ) 0x11111111;	/* R11 */
	pxTopOfStack--;	
	*pxTopOfStack = ( portSTACK_TYPE ) 0x10101010;	/* R10 */
	pxTopOfStack--;	
	*pxTopOfStack = ( portSTACK_TYPE ) 0x09090909;	/* R9 */
	pxTopOfStack--;	
	*pxTopOfStack = ( portSTACK_TYPE ) 0x08080808;	/* R8 */
	pxTopOfStack--;	
	*pxTopOfStack = ( portSTACK_TYPE ) 0x07070707;	/* R7 */
	pxTopOfStack--;	
	*pxTopOfStack = ( portSTACK_TYPE ) 0x06060606;	/* R6 */
	pxTopOfStack--;	
	*pxTopOfStack = ( portSTACK_TYPE ) 0x05050505;	/* R5 */
	pxTopOfStack--;	
	*pxTopOfStack = ( portSTACK_TYPE ) 0x04040404;	/* R4 */
	pxTopOfStack--;	
	*pxTopOfStack = ( portSTACK_TYPE ) 0x03030303;	/* R3 */
	pxTopOfStack--;	
	*pxTopOfStack = ( portSTACK_TYPE ) 0x02020202;	/* R2 */
	pxTopOfStack--;	
	*pxTopOfStack = ( portSTACK_TYPE ) 0x01010101;	/* R1 */
	pxTopOfStack--;	

	/* When the task starts is will expect to find the function parameter in
	R0. */
	*pxTopOfStack = ( portSTACK_TYPE ) pvParameters; /* R0 */
	pxTopOfStack--;

	/* The status register is set for system mode, with interrupts enabled. */
	*pxTopOfStack = ( portSTACK_TYPE ) portINITIAL_SPSR;
	
	if( ( ( unsigned long ) pxCode & 0x01UL ) != 0x00UL )
	{
		/* We want the task to start in thumb mode. */
		*pxTopOfStack |= portTHUMB_MODE_BIT;
	}
	
	pxTopOfStack--;

	/* Interrupt flags cannot always be stored on the stack and will
	instead be stored in a variable, which is then saved as part of the
	tasks context. */
	*pxTopOfStack = portNO_CRITICAL_NESTING;

	return pxTopOfStack;	
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
extern void vPortStartFirstTask( void );

	/* Start the timer that generates the tick ISR.  Interrupts are disabled
	here already. */
	prvSetupTimerInterrupt();

	/* Start the first task. */
	vPortStartFirstTask();	

	/* Should not get here! */
	return 0;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* It is unlikely that the ARM port will require this function as there
	is nothing to return to.  */
}
/*-----------------------------------------------------------*/

#if configUSE_PREEMPTION == 0

	/* The cooperative scheduler requires a normal IRQ service routine to
	simply increment the system tick. */
	static __arm __irq void vPortNonPreemptiveTick( void );
	static __arm __irq void vPortNonPreemptiveTick( void )
	{
		/* Increment the tick count - which may wake some tasks but as the
		preemptive scheduler is not being used any woken task is not given
		processor time no matter what its priority. */
		vTaskIncrementTick();
		
		/* Ready for the next interrupt. */
		T0IR = portTIMER_MATCH_ISR_BIT;
		VICVectAddr = portCLEAR_VIC_INTERRUPT;
	}

#else

	/* This function is called from an asm wrapper, so does not require the __irq
	keyword. */
	void vPortPreemptiveTick( void );
	void vPortPreemptiveTick( void )
	{
		/* Increment the tick counter. */
		vTaskIncrementTick();
	
		/* The new tick value might unblock a task.  Ensure the highest task that
		is ready to execute is the task that will execute when the tick ISR
		exits. */
		vTaskSwitchContext();
	
		/* Ready for the next interrupt. */
		T0IR = portTIMER_MATCH_ISR_BIT;
		VICVectAddr = portCLEAR_VIC_INTERRUPT;
	}

#endif

/*-----------------------------------------------------------*/

static void prvSetupTimerInterrupt( void )
{
unsigned long ulCompareMatch;

	/* A 1ms tick does not require the use of the timer prescale.  This is
	defaulted to zero but can be used if necessary. */
	T0PR = portPRESCALE_VALUE;

	/* Calculate the match value required for our wanted tick rate. */
	ulCompareMatch = configCPU_CLOCK_HZ / configTICK_RATE_HZ;

	/* Protect against divide by zero.  Using an if() statement still results
	in a warning - hence the #if. */
	#if portPRESCALE_VALUE != 0
	{
		ulCompareMatch /= ( portPRESCALE_VALUE + 1 );
	}
	#endif

	T0MR0 = ulCompareMatch;

	/* Generate tick with timer 0 compare match. */
	T0MCR = portRESET_COUNT_ON_MATCH | portINTERRUPT_ON_MATCH;

	/* Setup the VIC for the timer. */
	VICIntSelect &= ~( portTIMER_VIC_CHANNEL_BIT );
	VICIntEnable |= portTIMER_VIC_CHANNEL_BIT;
	
	/* The ISR installed depends on whether the preemptive or cooperative
	scheduler is being used. */
	#if configUSE_PREEMPTION == 1
	{	
		extern void ( vPortPreemptiveTickEntry )( void );

		VICVectAddr0 = ( unsigned long ) vPortPreemptiveTickEntry;
	}
	#else
	{
		extern void ( vNonPreemptiveTick )( void );

		VICVectAddr0 = ( long ) vPortNonPreemptiveTick;
	}
	#endif

	VICVectCntl0 = portTIMER_VIC_CHANNEL | portTIMER_VIC_ENABLE;

	/* Start the timer - interrupts are disabled when this function is called
	so it is okay to do this here. */
	T0TCR = portENABLE_TIMER;
}
/*-----------------------------------------------------------*/

void vPortEnterCritical( void )
{
	/* Disable interrupts first! */
	__disable_interrupt();

	/* Now interrupts are disabled ulCriticalNesting can be accessed
	directly.  Increment ulCriticalNesting to keep a count of how many times
	portENTER_CRITICAL() has been called. */
	ulCriticalNesting++;
}
/*-----------------------------------------------------------*/

void vPortExitCritical( void )
{
	if( ulCriticalNesting > portNO_CRITICAL_NESTING )
	{
		/* Decrement the nesting count as we are leaving a critical section. */
		ulCriticalNesting--;

		/* If the nesting level has reached zero then interrupts should be
		re-enabled. */
		if( ulCriticalNesting == portNO_CRITICAL_NESTING )
		{
			__enable_interrupt();
		}
	}
}
/*-----------------------------------------------------------*/






