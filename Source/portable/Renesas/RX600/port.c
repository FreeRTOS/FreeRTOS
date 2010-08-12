/*
    FreeRTOS V6.0.5 - Copyright (C) 2010 Real Time Engineers Ltd.

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

/* Dimensions the array into which the floating point context is saved.  
Allocate enough space for FPR0 to FPR15, FPUL and FPSCR, each of which is 4
bytes big.  If this number is changed then the 72 in portasm.src also needs
changing. */
#define portFLOP_REGISTERS_TO_STORE	( 18 )
#define portFLOP_STORAGE_SIZE 		( portFLOP_REGISTERS_TO_STORE * 4 )

/*-----------------------------------------------------------*/

/*
 * 
 */
void vPortYield( void );

/*
 * Function to start the first task executing.
 */
void vPortStartFirstTask( void );

/*-----------------------------------------------------------*/

/* 
 * See header file for description. 
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
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
	//trapa( portSTART_SCHEDULER_TRAP_NO );

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
//_RB_		*pulFlopBuffer = get_fpscr();
		
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

void vPortSaveFlopRegisters( void *pvBuffer )
{
}
/*-----------------------------------------------------------*/

void vPortRestoreFlopRegisters( void *pvBuffer )
{
}
/*-----------------------------------------------------------*/

