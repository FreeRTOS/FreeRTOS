/*
    FreeRTOS V6.0.0 - Copyright (C) 2009 Real Time Engineers Ltd.

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

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

#define portINITIAL_FORMAT_VECTOR		( ( portSTACK_TYPE ) 0x4000 )

/* Supervisor mode set. */
#define portINITIAL_STATUS_REGISTER		( ( portSTACK_TYPE ) 0x2000)

/* Used to keep track of the number of nested calls to taskENTER_CRITICAL().  This
will be set to 0 prior to the first task being started. */
static unsigned long ulCriticalNesting = 0x9999UL;

/*-----------------------------------------------------------*/

portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE * pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
	*pxTopOfStack = ( portSTACK_TYPE ) pvParameters;
	pxTopOfStack--;

	*pxTopOfStack = (portSTACK_TYPE) 0xDEADBEEF;
	pxTopOfStack--;

	/* Exception stack frame starts with the return address. */
	*pxTopOfStack = ( portSTACK_TYPE ) pxCode;
	pxTopOfStack--;

	*pxTopOfStack = ( portINITIAL_FORMAT_VECTOR << 16UL ) | ( portINITIAL_STATUS_REGISTER );
	pxTopOfStack--;

	*pxTopOfStack = ( portSTACK_TYPE ) 0x0; /*FP*/
	pxTopOfStack -= 14; /* A5 to D0. */

    return pxTopOfStack;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
extern void vPortStartFirstTask( void );

	ulCriticalNesting = 0UL;

	/* Configure the interrupts used by this port. */
	vApplicationSetupInterrupts();

	/* Start the first task executing. */
	vPortStartFirstTask();

	return pdFALSE;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Not implemented as there is nothing to return to. */
}
/*-----------------------------------------------------------*/

void vPortEnterCritical( void )
{
	if( ulCriticalNesting == 0UL )
	{
		/* Guard against context switches being pended simultaneously with a
		critical section being entered. */
		do
		{
			portDISABLE_INTERRUPTS();
			if( MCF_INTC0_INTFRCL == 0UL )
			{
				break;
			}

			portENABLE_INTERRUPTS();

		} while( 1 );
	}
	ulCriticalNesting++;
}
/*-----------------------------------------------------------*/

void vPortExitCritical( void )
{
	ulCriticalNesting--;
	if( ulCriticalNesting == 0 )
	{
		portENABLE_INTERRUPTS();
	}
}
/*-----------------------------------------------------------*/

void vPortYieldHandler( void )
{
unsigned long ulSavedInterruptMask;

	ulSavedInterruptMask = portSET_INTERRUPT_MASK_FROM_ISR();
		/* Note this will clear all forced interrupts - this is done for speed. */
		MCF_INTC0_INTFRCL = 0;
		vTaskSwitchContext();
	portCLEAR_INTERRUPT_MASK_FROM_ISR( ulSavedInterruptMask );
}






