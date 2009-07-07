/*
	FreeRTOS.org V5.4.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the 
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

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
static unsigned portLONG ulCriticalNesting = 0x9999UL;


#define portSAVE_CONTEXT()				\
	lea.l		(-60, %sp), %sp;		\
	movem.l		%d0-%fp, (%sp);			\
	move.l		pxCurrentTCB, %a0;		\
	move.l		%sp, (%a0);

#define portRESTORE_CONTEXT()			\
	move.l		pxCurrentTCB, %a0;		\
	move.l		(%a0), %sp;				\
	movem.l		(%sp), %d0-%fp;			\
	lea.l		%sp@(60), %sp;			\
	rte



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
			if( MCF_INTC0_INTFRCH == 0UL )
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
unsigned portLONG ulSavedInterruptMask;

	ulSavedInterruptMask = portSET_INTERRUPT_MASK_FROM_ISR();
		/* Note this will clear all forced interrupts - this is done for speed. */
		MCF_INTC0_INTFRCL = 0;
		vTaskSwitchContext();
	portCLEAR_INTERRUPT_MASK_FROM_ISR( ulSavedInterruptMask );
}
/*-----------------------------------------------------------*/

