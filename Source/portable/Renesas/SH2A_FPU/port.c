/*
    FreeRTOS V6.0.3 - Copyright (C) 2010 Real Time Engineers Ltd.

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

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the SH2A port.
 *----------------------------------------------------------*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Library includes. */
#include "string.h"

/*-----------------------------------------------------------*/

/* The SR assigned to a newly created task.  The only important thing in this
value is for all interrupts to be enabled. */
#define portINITIAL_SR				( 0UL )

/* Dimensions the array into which the floating point context is saved.  
Allocate enough space for FPR0 to FPR15, FPUL and FPSCR, each of which is 4
bytes big.  If this number is changed then the 72 in portasm.src also needs
changing. */
#define portFLOP_REGISTERS_TO_STORE	( 18 )
#define portFLOP_STORAGE_SIZE 		( portFLOP_REGISTERS_TO_STORE * 4 )

/*-----------------------------------------------------------*/

/*
 * The TRAPA handler used to force a context switch.
 */
void vPortYield( void );

/*
 * Function to start the first task executing - defined in portasm.src.
 */
extern void vPortStartFirstTask( void );

/*
 * Obtains the current GBR value - defined in portasm.src.
 */
extern unsigned long ulPortGetGBR( void );

/*-----------------------------------------------------------*/

/* 
 * See header file for description. 
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
*pxTopOfStack = 0x11111111UL;
pxTopOfStack--;
*pxTopOfStack = 0x22222222UL;
pxTopOfStack--;
*pxTopOfStack = 0x33333333UL;
pxTopOfStack--;

	/* SR. */
	*pxTopOfStack = portINITIAL_SR; 
	pxTopOfStack--;
	
	/* PC. */
	*pxTopOfStack = ( unsigned long ) pxCode;
	pxTopOfStack--;
	
	/* PR. */
	*pxTopOfStack = 15;
	pxTopOfStack--;
	
	/* 14. */
	*pxTopOfStack = 14;
	pxTopOfStack--;

	/* R13. */
	*pxTopOfStack = 13;
	pxTopOfStack--;

	/* R12. */
	*pxTopOfStack = 12;
	pxTopOfStack--;

	/* R11. */
	*pxTopOfStack = 11;
	pxTopOfStack--;

	/* R10. */
	*pxTopOfStack = 10;
	pxTopOfStack--;

	/* R9. */
	*pxTopOfStack = 9;
	pxTopOfStack--;

	/* R8. */
	*pxTopOfStack = 8;
	pxTopOfStack--;

	/* R7. */
	*pxTopOfStack = 7;
	pxTopOfStack--;

	/* R6. */
	*pxTopOfStack = 6;
	pxTopOfStack--;

	/* R5. */
	*pxTopOfStack = 5;
	pxTopOfStack--;

	/* R4. */
	*pxTopOfStack = ( unsigned long ) pvParameters;
	pxTopOfStack--;

	/* R3. */
	*pxTopOfStack = 3;
	pxTopOfStack--;

	/* R2. */
	*pxTopOfStack = 2;
	pxTopOfStack--;

	/* R1. */
	*pxTopOfStack = 1;
	pxTopOfStack--;
	
	/* R0 */
	*pxTopOfStack = 0;
	pxTopOfStack--;
	
	/* MACL. */
	*pxTopOfStack = 16;
	pxTopOfStack--;
	
	/* MACH. */
	*pxTopOfStack = 17;
	pxTopOfStack--;
	
	/* GBR. */
	*pxTopOfStack = ulPortGetGBR();
	
	/* GBR = global base register.
	   VBR = vector base register.
	   TBR = jump table base register.
	   R15 is the stack pointer. */

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
extern void vApplicationSetupTimerInterrupt( void );

	/* Call an application function to set up the timer that will generate the
	tick interrupt.  This way the application can decide which peripheral to 
	use.  A demo application is provided to show a suitable example. */
	vApplicationSetupTimerInterrupt();

	/* Start the first task.  This will only restore the standard registers and
	not the flop registers.  This does not really matter though because the only
	flop register that is initialised to a particular value is fpscr, and it is
	only initialised to the current value, which will still be the current value
	when the first task starts executing. */
	trapa( portSTART_SCHEDULER_TRAP_NO );

	/* Should not get here. */
	return pdFAIL;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Not implemented as there is nothing to return to. */
}
/*-----------------------------------------------------------*/

void vPortYield( void )
{
long lInterruptMask;

	/* Ensure the yield trap runs at the same priority as the other interrupts
	that can cause a context switch. */
	lInterruptMask = get_imask();

	/* taskYIELD() can only be called from a task, not an interrupt, so the
	current interrupt mask can only be 0 or portKERNEL_INTERRUPT_PRIORITY and
	the mask can be set without risk of accidentally lowering the mask value. */	
	set_imask( portKERNEL_INTERRUPT_PRIORITY );
	
	trapa( portYIELD_TRAP_NO );
	
	/* Restore the interrupt mask to whatever it was previously (when the
	function was entered). */
	set_imask( ( int ) lInterruptMask );
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortUsesFloatingPoint( xTaskHandle xTask )
{
unsigned long *pulFlopBuffer;
portBASE_TYPE xReturn;
extern void * volatile pxCurrentTCB;

	/* This function tells the kernel that the task referenced by xTask is
	going to use the floating point registers and therefore requires the
	floating point registers saved as part of its context. */

	/* Passing NULL as xTask is used to indicate that the calling task is the
	subject task - so pxCurrentTCB is the task handle. */
	if( xTask == NULL )
	{
		xTask = ( xTaskHandle ) pxCurrentTCB;
	}

	/* Allocate a buffer large enough to hold all the flop registers. */
	pulFlopBuffer = ( unsigned long * ) pvPortMalloc( portFLOP_STORAGE_SIZE );
	
	if( pulFlopBuffer != NULL )
	{
		/* Start with the registers in a benign state. */
		memset( ( void * ) pulFlopBuffer, 0x00, portFLOP_STORAGE_SIZE );
		
		/* The first thing to get saved in the buffer is the FPSCR value -
		initialise this to the current FPSCR value. */
		*pulFlopBuffer = get_fpscr();
		
		/* Use the task tag to point to the flop buffer.  Pass pointer to just 
		above the buffer because the flop save routine uses a pre-decrement. */
		vTaskSetApplicationTaskTag( xTask, ( void * ) ( pulFlopBuffer + portFLOP_REGISTERS_TO_STORE ) );		
		xReturn = pdPASS;
	}
	else
	{
		xReturn = pdFAIL;
	}
	
	return xReturn;
}
/*-----------------------------------------------------------*/


