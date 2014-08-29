/*
    FreeRTOS V8.1.1 - Copyright (C) 2014 Real Time Engineers Ltd. 
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*-----------------------------------------------------------
 * Implementation of functions defined in portable.h for the PPC440 port.
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

#if configUSE_FPU == 1
	#define portAPU_PRESENT				( 1UL << 25UL )
	#define portFCM_FPU_PRESENT			( 1UL << 13UL )
#else
	#define portAPU_PRESENT				( 0UL )
	#define portFCM_FPU_PRESENT			( 0UL )
#endif

#define portINITIAL_MSR		( portCRITICAL_INTERRUPT_ENABLE | portEXTERNAL_INTERRUPT_ENABLE | portMACHINE_CHECK_ENABLE | portAPU_PRESENT | portFCM_FPU_PRESENT )


extern const unsigned _SDA_BASE_;
extern const unsigned _SDA2_BASE_;

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
StackType_t *pxPortInitialiseStack( StackType_t *pxTopOfStack, TaskFunction_t pxCode, void *pvParameters )
{
	/* Place a known value at the bottom of the stack for debugging. */
	*pxTopOfStack = 0xDEADBEEF;
	pxTopOfStack--;

	/* EABI stack frame. */
	pxTopOfStack -= 20;	/* Previous backchain and LR, R31 to R4 inclusive. */

	/* Parameters in R13. */
	*pxTopOfStack = ( StackType_t ) &_SDA_BASE_; /* address of the first small data area */
	pxTopOfStack -= 10;

	/* Parameters in R3. */
	*pxTopOfStack = ( StackType_t ) pvParameters;
	pxTopOfStack--;

	/* Parameters in R2. */
	*pxTopOfStack = ( StackType_t ) &_SDA2_BASE_;	/* address of the second small data area */
	pxTopOfStack--;

	/* R1 is the stack pointer so is omitted. */

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
	*pxTopOfStack = ( StackType_t ) vPortEndScheduler;	/* LR. */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) pxCode; /* SRR0. */
	pxTopOfStack--;
	*pxTopOfStack = portINITIAL_MSR;/* SRR1. */
	pxTopOfStack--;
	*pxTopOfStack = ( StackType_t ) vPortEndScheduler;/* Next LR. */
	pxTopOfStack--;
	*pxTopOfStack = 0x00000000UL;/* Backchain. */

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

BaseType_t xPortStartScheduler( void )
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
	for( ;; );
}
/*-----------------------------------------------------------*/

/*
 * Hardware initialisation to generate the RTOS tick.
 */
static void prvSetupTimerInterrupt( void )
{
const uint32_t ulInterval = ( ( configCPU_CLOCK_HZ / configTICK_RATE_HZ ) - 1UL );

	XTime_DECClearInterrupt();
	XTime_FITClearInterrupt();
	XTime_WDTClearInterrupt();
	XTime_WDTDisableInterrupt();
	XTime_FITDisableInterrupt();

	XExc_RegisterHandler( XEXC_ID_DEC_INT, ( XExceptionHandler ) vPortTickISR, ( void * ) 0 );

	XTime_DECEnableAutoReload();
	XTime_DECSetInterval( ulInterval );
	XTime_DECEnableInterrupt();
}
/*-----------------------------------------------------------*/

void vPortISRHandler( void *pvNullDoNotUse )
{
uint32_t ulInterruptStatus, ulInterruptMask = 1UL;
BaseType_t xInterruptNumber;
XIntc_Config *pxInterruptController;
XIntc_VectorTableEntry *pxTable;

	/* Just to remove compiler warning. */
	( void ) pvNullDoNotUse;

	/* Get the configuration by using the device ID - in this case it is
	assumed that only one interrupt controller is being used. */
	pxInterruptController = &XIntc_ConfigTable[ XPAR_XPS_INTC_0_DEVICE_ID ];

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
	XIntc_Initialize( &xInterruptController, XPAR_XPS_INTC_0_DEVICE_ID );
	XIntc_Start( &xInterruptController, XIN_REAL_MODE );
}
/*-----------------------------------------------------------*/

BaseType_t xPortInstallInterruptHandler( uint8_t ucInterruptID, XInterruptHandler pxHandler, void *pvCallBackRef )
{
BaseType_t xReturn = pdFAIL;

	/* This function is defined here so the scope of xInterruptController can
	remain within this file. */

	if( XST_SUCCESS == XIntc_Connect( &xInterruptController, ucInterruptID, pxHandler, pvCallBackRef ) )
	{
		XIntc_Enable( &xInterruptController, ucInterruptID );
		xReturn = pdPASS;
	}

	return xReturn;
}
