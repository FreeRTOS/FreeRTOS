/*
	FreeRTOS.org V4.0.5 - Copyright (C) 2003-2006 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************
	See http://www.FreeRTOS.org for documentation, latest information, license 
	and contact details.  Please ensure to read the configuration and relevant 
	port sections of the online documentation.
	***************************************************************************
*/


/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the ARM CM3 port.
 *----------------------------------------------------------*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Constants required to manipulate the NVIC. */
#define portNVIC_SYSTICK_CTRL		( ( volatile unsigned portLONG *) 0xe000e010 )
#define portNVIC_SYSTICK_LOAD		( ( volatile unsigned portLONG *) 0xe000e014 )
#define portNVIC_INT_CTRL			( ( volatile unsigned portLONG *) 0xe000ed04 )
#define portNVIC_SYSPRI2			( ( volatile unsigned portLONG *) 0xe000ed20 )
#define portNVIC_SYSPRI1			( ( volatile unsigned portLONG *) 0xe000ed1c )
#define portNVIC_SYSTICK_CLK		0x00000004
#define portNVIC_SYSTICK_INT		0x00000002
#define portNVIC_SYSTICK_ENABLE		0x00000001
#define portNVIC_PENDSVSET			0x10000000
#define portNVIC_PENDSV_PRI			0x00ff0000
#define portNVIC_SVCALL_PRI			0xff000000
#define portNVIC_SYSTICK_PRI		0xff000000

/* Constants required to set up the initial stack. */
#define portINITIAL_XPSR			( 0x01000000 )

/* Each task maintains its own interrupt status in the critical nesting
variable. */
unsigned portBASE_TYPE uxCriticalNesting = 0xaaaaaaaa;

/* 
 * Setup the timer to generate the tick interrupts.
 */
static void prvSetupTimerInterrupt( void );

/*
 * Set the MSP/PSP to a known value.
 */
extern void vSetMSP( unsigned long ulValue );
extern void vSetPSP( unsigned long ulValue );

/*-----------------------------------------------------------*/

/* 
 * See header file for description. 
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
	/* Simulate the stack frame as it would be created by a context switch
	interrupt. */
	*pxTopOfStack = portINITIAL_XPSR;	/* xPSR */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) pxCode;	/* PC */
	pxTopOfStack--;
	*pxTopOfStack = 0xfffffffd;	/* LR */
	pxTopOfStack -= 5;	/* R12, R3, R2 and R1. */
	*pxTopOfStack = ( portSTACK_TYPE ) pvParameters;	/* R0 */
	pxTopOfStack -= 9;	/* R11, R10, R9, R8, R7, R6, R5 and R4. */
	*pxTopOfStack = 0x00000000; /* uxCriticalNesting. */

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

/* 
 * See header file for description. 
 */
portBASE_TYPE xPortStartScheduler( void )
{
	/* Make PendSV, CallSV and SysTick the lowest priority interrupts. */
	*(portNVIC_SYSPRI2) |= portNVIC_PENDSV_PRI;
	*(portNVIC_SYSPRI2) |= portNVIC_SYSTICK_PRI;

	/* Start the timer that generates the tick ISR.  Interrupts are disabled
	here already. */
	prvSetupTimerInterrupt();
	
	/* Start the first task. */
	vSetPSP( 0 );
	vSetMSP( *((unsigned portLONG *) 0 ) );
	*(portNVIC_INT_CTRL) |= portNVIC_PENDSVSET;

	/* Enable interrupts */
	portENABLE_INTERRUPTS();

	/* Should not get here! */
	return 0;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* It is unlikely that the CM3 port will require this function as there
	is nothing to return to.  */
}
/*-----------------------------------------------------------*/

void vPortYieldFromISR( void )
{
	/* Set a PendSV to request a context switch. */
	*(portNVIC_INT_CTRL) |= portNVIC_PENDSVSET;

	/* This function is also called in response to a Yield(), so we want
	the yield to occur immediately. */
	portENABLE_INTERRUPTS();
}
/*-----------------------------------------------------------*/

void vPortEnterCritical( void )
{
	portDISABLE_INTERRUPTS();
	uxCriticalNesting++;
}
/*-----------------------------------------------------------*/

void vPortExitCritical( void )
{
	uxCriticalNesting--;
	if( uxCriticalNesting == 0 )
	{
		portENABLE_INTERRUPTS();
	}
}
/*-----------------------------------------------------------*/


/*
 * Setup the systick timer to generate the tick interrupts at the required
 * frequency.
 */
void prvSetupTimerInterrupt( void )
{
	/* Configure SysTick to interrupt at the requested rate. */
	*(portNVIC_SYSTICK_LOAD) = configCPU_CLOCK_HZ / configTICK_RATE_HZ;
	*(portNVIC_SYSTICK_CTRL) = portNVIC_SYSTICK_CLK | portNVIC_SYSTICK_INT | portNVIC_SYSTICK_ENABLE;
}


