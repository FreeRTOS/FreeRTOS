/*
    FreeRTOS V6.0.2 - Copyright (C) 2009 Real Time Engineers Ltd.

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

#define portINITIAL_SR		0UL /* No interrupts masked. */


/*-----------------------------------------------------------*/

/*
 * Setup a peripheral timer to generate the RTOS tick interrupt.
 */
static void prvSetupTimerInterrupt( void );

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
	/* Start the tick interrupt. */
	prvSetupTimerInterrupt();
	
	/* Start the first task. */
	trapa( 32 );

	/* Should not get here. */
	return pdFAIL;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Not implemented as there is nothing to return to. */
}
/*-----------------------------------------------------------*/

void vPortTickInterrupt( void )
{
	vTaskIncrementTick();
	#if configUSE_PREEMPTION == 1
		vTaskSwitchContext();
	#endif
}
/*-----------------------------------------------------------*/

static void prvSetupTimerInterrupt( void )
{
extern void vApplicationSetupTimerInterrupt( void );

	/* Call an application function to set up the timer.  This way the application
	can decide which peripheral to use.  A demo application is provided to show a
	suitable example. */
	vApplicationSetupTimerInterrupt();
}
/*-----------------------------------------------------------*/






