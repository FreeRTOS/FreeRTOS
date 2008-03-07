/*
	FreeRTOS.org V4.7.2 - Copyright (C) 2003-2008 Richard Barry.

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

	Please ensure to read the configuration and relevant port sections of the 
	online documentation.

	+++ http://www.FreeRTOS.org +++
	Documentation, latest information, license and contact details.  

	+++ http://www.SafeRTOS.com +++
	A version that is certified for use in safety critical systems.

	+++ http://www.OpenRTOS.com +++
	Commercial support, development, porting, licensing and training services.

	***************************************************************************
*/

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the PPC405 port.
 *----------------------------------------------------------*/


/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Library includes. */
#include "xtime_l.h"
#include "xintc.h"
#include "xintc_i.h"

/*-----------------------------------------------------------*/

/* Definitions to set the initial MSR of each task. */
#define portCRITICAL_INTERRUPT_ENABLE	( 1UL << 17UL )
#define portEXTERNAL_INTERRUPT_ENABLE	( 1UL << 15UL )
#define portMACHINE_CHECK_ENABLE		( 1UL << 12UL )
#define portINITIAL_MSR		( portCRITICAL_INTERRUPT_ENABLE | portEXTERNAL_INTERRUPT_ENABLE | portMACHINE_CHECK_ENABLE )

/*-----------------------------------------------------------*/

/*
 * Setup the system timer to generate the tick interrupt.
 */
static void prvSetupTimerInterrupt( void );

/*
 * The handler for the tick interrupt - defined in portasm.s.
 */
extern void vPortTickISR( void );

/*
 * The handler for the yield function - defined in portasm.s.
 */
extern void vPortYield( void );

/*
 * Function to start the scheduler running by starting the highest
 * priority task that has thus far been created.
 */
extern void vPortStartFirstTask( void );

/*-----------------------------------------------------------*/

/* Structure used to hold the state of the interrupt controller. */
static XIntc xInterruptController;

/*-----------------------------------------------------------*/

/* 
 * Initialise the stack of a task to look exactly as if the task had been
 * interrupted.
 * 
 * See the header file portable.h.
 */
portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE *pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
	/* Place a known value at the bottom of the stack for debugging. */
	*pxTopOfStack = 0xDEADBEEF;
	*pxTopOfStack--;

	/* EABI stack frame. */
	*pxTopOfStack = 0x31313131UL;	/* R31. */
	pxTopOfStack--;
	*pxTopOfStack = 0x30303030UL;	/* R30. */
	pxTopOfStack--;
	*pxTopOfStack = 0x29292929UL;	/* R29. */
	pxTopOfStack--;
	*pxTopOfStack = 0x28282828UL;	/* R28. */
	pxTopOfStack--;
	*pxTopOfStack = 0x27272727UL;	/* R27. */
	pxTopOfStack--;
	*pxTopOfStack = 0x26262626UL;	/* R26. */
	pxTopOfStack--;
	*pxTopOfStack = 0x25252525UL;	/* R25. */
	pxTopOfStack--;
	*pxTopOfStack = 0x24242424UL;	/* R24. */
	pxTopOfStack--;
	*pxTopOfStack = 0x23232323UL;	/* R23. */
	pxTopOfStack--;
	*pxTopOfStack = 0x22222222UL;	/* R22. */
	pxTopOfStack--;
	*pxTopOfStack = 0x21212121UL;	/* R21. */
	pxTopOfStack--;
	*pxTopOfStack = 0x20202020UL;	/* R20. */
	pxTopOfStack--;
	*pxTopOfStack = 0x19191919UL;	/* R19. */
	pxTopOfStack--;
	*pxTopOfStack = 0x18181818UL;	/* R18. */
	pxTopOfStack--;
	*pxTopOfStack = 0x17171717UL;	/* R17. */
	pxTopOfStack--;
	*pxTopOfStack = 0x16161616UL;	/* R16. */
	pxTopOfStack--;
	*pxTopOfStack = 0x15151515UL;	/* R15. */
	pxTopOfStack--;
	*pxTopOfStack = 0x14141414UL;	/* R14. */
	pxTopOfStack--;
	*pxTopOfStack = 0x13131313UL;	/* R13. */
	pxTopOfStack--;
	*pxTopOfStack = 0x12121212UL;	/* R12. */
	pxTopOfStack--;
	*pxTopOfStack = 0x11111111UL;	/* R11. */
	pxTopOfStack--;
	*pxTopOfStack = 0x10101010UL;	/* R10. */
	pxTopOfStack--;
	*pxTopOfStack = 0x09090909UL;	/* R9. */
	pxTopOfStack--;
	*pxTopOfStack = 0x08080808UL;	/* R8. */
	pxTopOfStack--;
	*pxTopOfStack = 0x07070707UL;	/* R7. */
	pxTopOfStack--;
	*pxTopOfStack = 0x06060606UL;	/* R6. */
	pxTopOfStack--;
	*pxTopOfStack = 0x05050505UL;	/* R5. */
	pxTopOfStack--;
	*pxTopOfStack = 0x04040404UL;	/* R4. */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) pvParameters;
	pxTopOfStack--;
	*pxTopOfStack = 0x02020202UL;	/* R2. */
	pxTopOfStack--;
	*pxTopOfStack = 0x10000001UL;;	/* R0. */
	pxTopOfStack--;
	*pxTopOfStack = 0x00000000UL;	/* USPRG0. */
	pxTopOfStack--;
	*pxTopOfStack = 0x00000000UL;	/* CR. */
	pxTopOfStack--;
	*pxTopOfStack = 0x00000000UL;	/* XER. */
	pxTopOfStack--;
	*pxTopOfStack = 0x00000000UL;	/* CTR. */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) vPortStartFirstTask;	/* LR. */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) pxCode; /* SRR0. */
	pxTopOfStack--;
	*pxTopOfStack = portINITIAL_MSR;/* SRR1. */
	pxTopOfStack--;
	*pxTopOfStack = ( portSTACK_TYPE ) vPortStartFirstTask;/* Next LR. */
	pxTopOfStack--;
	*pxTopOfStack = 0x00000000UL;;/* Backchain. */

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
	prvSetupTimerInterrupt();
	XExc_RegisterHandler( XEXC_ID_SYSTEM_CALL, ( XExceptionHandler ) vPortYield, ( void * ) 0 );
	vPortStartFirstTask();

	/* Should not get here as the tasks are now running! */
	return pdFALSE;
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Not implemented. */
}
/*-----------------------------------------------------------*/

/*
 * Hardware initialisation to generate the RTOS tick.   
 */
static void prvSetupTimerInterrupt( void )
{
const unsigned portLONG ulInterval = ( ( configCPU_CLOCK_HZ / configTICK_RATE_HZ ) - 1UL );

	XTime_PITClearInterrupt();
	XTime_FITClearInterrupt();
	XTime_WDTClearInterrupt();
	XTime_WDTDisableInterrupt();
	XTime_FITDisableInterrupt();

	XExc_RegisterHandler( XEXC_ID_PIT_INT, ( XExceptionHandler ) vPortTickISR, ( void * ) 0 );

	XTime_PITEnableAutoReload();
	XTime_PITSetInterval( ulInterval );
	XTime_PITEnableInterrupt();
}
/*-----------------------------------------------------------*/

void vPortISRHandler( void *vNullDoNotUse )
{
unsigned portLONG ulInterruptStatus, ulInterruptMask = 1UL;
portBASE_TYPE xInterruptNumber;
XIntc_Config *pxInterruptController;
XIntc_VectorTableEntry *pxTable;

	/* Get the configuration by using the device ID - in this case it is
	assumed that only one interrupt controller is being used. */
	pxInterruptController = &XIntc_ConfigTable[ XPAR_OPB_INTC_0_DEVICE_ID ];
  
	/* Which interrupts are pending? */
	ulInterruptStatus = XIntc_mGetIntrStatus( pxInterruptController->BaseAddress );
  
	for( xInterruptNumber = 0; xInterruptNumber < XPAR_INTC_MAX_NUM_INTR_INPUTS; xInterruptNumber++ )
	{
		if( ulInterruptStatus & 0x01UL )
		{
			/* Clear the pending interrupt. */
			XIntc_mAckIntr( pxInterruptController->BaseAddress, ulInterruptMask );

			/* Call the registered handler. */
			pxTable = &( pxInterruptController->HandlerTable[ xInterruptNumber ] );
			pxTable->Handler( pxTable->CallBackRef );
		}
        
		/* Check the next interrupt. */
		ulInterruptMask <<= 0x01UL;
		ulInterruptStatus >>= 0x01UL;

		/* Have we serviced all interrupts? */
		if( ulInterruptStatus == 0UL )
		{
			break;
		}
	}
}
/*-----------------------------------------------------------*/

void vPortSetupInterruptController( void )
{
extern void vPortISRWrapper( void );

	/* Perform all library calls necessary to initialise the exception table
	and interrupt controller.  This assumes only one interrupt controller is in
	use. */
	XExc_mDisableExceptions( XEXC_NON_CRITICAL );
	XExc_Init();

	/* The library functions save the context - we then jump to a wrapper to
	save the stack into the TCB.  The wrapper then calls the handler defined
	above. */
	XExc_RegisterHandler( XEXC_ID_NON_CRITICAL_INT, ( XExceptionHandler ) vPortISRWrapper, NULL );
	XIntc_Initialize( &xInterruptController, XPAR_OPB_INTC_0_DEVICE_ID );
	XIntc_Start( &xInterruptController, XIN_REAL_MODE );
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortInstallInterruptHandler( unsigned portCHAR ucInterruptID, XInterruptHandler pxHandler, void *pvCallBackRef )
{
portBASE_TYPE xReturn = pdFAIL;

	/* This function is defined here so the scope of xInterruptController can
	remain within this file. */

	if( XST_SUCCESS == XIntc_Connect( &xInterruptController, ucInterruptID, pxHandler, pvCallBackRef ) )
	{
		XIntc_Enable( &xInterruptController, ucInterruptID );
		xReturn = pdPASS;
	}

	return xReturn;		
}
