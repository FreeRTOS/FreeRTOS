/*
	FreeRTOS.org V5.0.3 - Copyright (C) 2003-2008 Richard Barry.

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
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

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

static unsigned portLONG ulCriticalNesting = 0x9999UL;


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
	pxTopOfStack--;

	*pxTopOfStack = ( portSTACK_TYPE ) 0xA5A5A5A5;
	pxTopOfStack--;

	*pxTopOfStack = ( portSTACK_TYPE ) 0xA4A4A4A4;
	pxTopOfStack--;

	*pxTopOfStack = ( portSTACK_TYPE ) 0xA3A3A3A3;
	pxTopOfStack--;

	*pxTopOfStack = ( portSTACK_TYPE ) 0xA2A2A2A2;
	pxTopOfStack--;

	*pxTopOfStack = ( portSTACK_TYPE ) 0xA1A1A1A1;
	pxTopOfStack--;

	*pxTopOfStack = ( portSTACK_TYPE ) 0xA0A0A0A0;
	pxTopOfStack--;

	*pxTopOfStack = ( portSTACK_TYPE ) 0xD7D7D7D7;
	pxTopOfStack--;

	*pxTopOfStack = ( portSTACK_TYPE ) 0xD6D6D6D6;
	pxTopOfStack--;

	*pxTopOfStack = ( portSTACK_TYPE ) 0xD5D5D5D5;
	pxTopOfStack--;

	*pxTopOfStack = ( portSTACK_TYPE ) 0xD4D4D4D4;
	pxTopOfStack--;

	*pxTopOfStack = ( portSTACK_TYPE ) 0xD3D3D3D3;
	pxTopOfStack--;

	*pxTopOfStack = ( portSTACK_TYPE ) 0xD2D2D2D2;
	pxTopOfStack--;

	*pxTopOfStack = ( portSTACK_TYPE ) 0xD1D1D1D1;
	pxTopOfStack--;

	*pxTopOfStack = ( portSTACK_TYPE ) 0xD0D0D0D0;

    return pxTopOfStack;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
extern void vPortStartFirstTask( void );

	ulCriticalNesting = 0UL;

	vApplicationSetupInterrupts();
	vPortStartFirstTask();

	return pdFALSE;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
}
/*-----------------------------------------------------------*/

void vPortEnterCritical( void )
{
	portDISABLE_INTERRUPTS();
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

unsigned portBASE_TYPE uxPortSetInterruptMaskFromISR( void )
{
	return 0;
}
/*-----------------------------------------------------------*/

void vPortClearInterruptMaskFromISR( unsigned portBASE_TYPE uxSavedInterruptMask )
{
}

void vPortClearYield( void )
{
	/* -32 as we are using the high word of the 64bit mask. */
	MCF_INTC0_INTFRCH &= ~( 1UL << ( configYIELD_INTERRUPT_VECTOR - 32UL ) );
}






