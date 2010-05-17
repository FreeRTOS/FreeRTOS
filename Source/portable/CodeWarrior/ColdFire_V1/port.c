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

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"


#define portINITIAL_FORMAT_VECTOR		( ( portSTACK_TYPE ) 0x4000 )

/* Supervisor mode set. */
#define portINITIAL_STATUS_REGISTER		( ( portSTACK_TYPE ) 0x2000)

/* The clock prescale into the timer peripheral. */
#define portPRESCALE_VALUE				( ( unsigned char ) 10 )

/* The clock frequency into the RTC. */
#define portRTC_CLOCK_HZ				( ( unsigned long ) 1000 )

asm void interrupt VectorNumber_VL1swi vPortYieldISR( void );
static void prvSetupTimerInterrupt( void );

/* Used to keep track of the number of nested calls to taskENTER_CRITICAL().  This
will be set to 0 prior to the first task being started. */
static unsigned long ulCriticalNesting = 0x9999UL;

/*-----------------------------------------------------------*/

portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE * pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{

unsigned long ulOriginalA5;

	__asm{ MOVE.L A5, ulOriginalA5 };


	*pxTopOfStack = (portSTACK_TYPE) 0xDEADBEEF;
	pxTopOfStack--;

	/* Exception stack frame starts with the return address. */
	*pxTopOfStack = ( portSTACK_TYPE ) pxCode;
	pxTopOfStack--;

	*pxTopOfStack = ( portINITIAL_FORMAT_VECTOR << 16UL ) | ( portINITIAL_STATUS_REGISTER );
	pxTopOfStack--;

	*pxTopOfStack = ( portSTACK_TYPE ) 0x0; /*FP*/
	pxTopOfStack -= 14; /* A5 to D0. */

	/* Parameter in A0. */
	*( pxTopOfStack + 8 ) = ( portSTACK_TYPE ) pvParameters;

	/* A5 must be maintained as it is resurved by the compiler. */
	*( pxTopOfStack + 13 ) = ulOriginalA5;

	return pxTopOfStack;  
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
extern void vPortStartFirstTask( void );

	ulCriticalNesting = 0UL;

	/* Configure a timer to generate the tick interrupt. */
	prvSetupTimerInterrupt();

	/* Start the first task executing. */
	vPortStartFirstTask();

	return pdFALSE;
}
/*-----------------------------------------------------------*/

static void prvSetupTimerInterrupt( void )
{				
	/* Prescale by 1 - ie no prescale. */
	RTCSC |= 8;
	
	/* Compare match value. */
	RTCMOD = portRTC_CLOCK_HZ / configTICK_RATE_HZ;
	
	/* Enable the RTC to generate interrupts - interrupts are already disabled
	when this code executes. */
	RTCSC_RTIE = 1;
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
			if( INTC_FRC == 0UL )
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
	{
		/* Note this will clear all forced interrupts - this is done for speed. */
		INTC_CFRC = 0x3E;
		vTaskSwitchContext();
	}
	portCLEAR_INTERRUPT_MASK_FROM_ISR( ulSavedInterruptMask );
}
/*-----------------------------------------------------------*/

void interrupt VectorNumber_Vrtc vPortTickISR( void )
{
unsigned long ulSavedInterruptMask;

	/* Clear the interrupt. */
	RTCSC |= RTCSC_RTIF_MASK;

	/* Increment the RTOS tick. */
	ulSavedInterruptMask = portSET_INTERRUPT_MASK_FROM_ISR();
	{
		vTaskIncrementTick();
	}
	portCLEAR_INTERRUPT_MASK_FROM_ISR( ulSavedInterruptMask );

	/* If we are using the pre-emptive scheduler then also request a
	context switch as incrementing the tick could have unblocked a task. */
	#if configUSE_PREEMPTION == 1
	{
		taskYIELD();
	}
	#endif
}

