/*
    FreeRTOS V8.0.0:rc2 - Copyright (C) 2014 Real Time Engineers Ltd. 
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

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "Task.h"

/* Xilinx includes. */
#include "xscutimer.h"
#include "xscugic.h"

#define XSCUTIMER_CLOCK_HZ XPAR_CPU_CORTEXA9_0_CPU_CLK_FREQ_HZ/2

static XScuTimer Timer;						/* A9 timer counter */

/*
 * The application must provide a function that configures a peripheral to
 * create the FreeRTOS tick interrupt, then define configSETUP_TICK_INTERRUPT()
 * in FreeRTOSConfig.h to call the function.  This file contains a function
 * that is suitable for use on the Renesas RZ MPU.
 */
void vConfigureTickInterrupt( void )
{
static XScuGic InterruptController; 	/* Interrupt controller instance */
int Status;
extern void FreeRTOS_Tick_Handler( void );
XScuTimer_Config *ScuConfig;
XScuGic_Config *IntcConfig;

	IntcConfig = XScuGic_LookupConfig(XPAR_SCUGIC_SINGLE_DEVICE_ID);
	Status = XScuGic_CfgInitialize(&InterruptController, IntcConfig, IntcConfig->CpuBaseAddress );
	configASSERT( Status == XST_SUCCESS );

	/*
	 * Connect to the interrupt controller
	 */
	Status = XScuGic_Connect(&InterruptController, XPAR_SCUTIMER_INTR, (Xil_ExceptionHandler) FreeRTOS_Tick_Handler, (void *)&Timer);
	configASSERT( Status == XST_SUCCESS );

	/*
	 * Initialize the A9Timer driver.
	 */
	ScuConfig = XScuTimer_LookupConfig(XPAR_SCUTIMER_DEVICE_ID);

	Status = XScuTimer_CfgInitialize(&Timer, ScuConfig, ScuConfig->BaseAddr);

	configASSERT( Status == XST_SUCCESS );

	/*
	 * Enable Auto reload mode.
	 */
	XScuTimer_EnableAutoReload(&Timer);

	/*
	 * Load the timer counter register.
	 */
	XScuTimer_LoadTimer(&Timer, XSCUTIMER_CLOCK_HZ / configTICK_RATE_HZ);

	/*
	 * Start the timer counter and then wait for it
	 * to timeout a number of times.
	 */
	XScuTimer_Start(&Timer);

	/*
	 * Enable the interrupt for the Timer in the interrupt controller
	 */
	XScuGic_Enable(&InterruptController, XPAR_SCUTIMER_INTR);

	/*
	 * Enable the timer interrupts for timer mode.
	 */
	XScuTimer_EnableInterrupt(&Timer);

	/*
	 * Do NOT enable interrupts in the ARM processor here.
	 * This happens when the scheduler is started.
	 */
}
/*-----------------------------------------------------------*/

/*
 * Crude implementation of a run time counter used to measure how much time
 * each task spends in the Running state.
 */
unsigned long ulGetRunTimeCounterValue( void )
{
	return 0;
}
/*-----------------------------------------------------------*/

void vInitialiseRunTimeStats( void )
{
}
/*-----------------------------------------------------------*/

extern XScuGic_Config XScuGic_ConfigTable[];
static const XScuGic_Config *CfgPtr = &XScuGic_ConfigTable[ XPAR_SCUGIC_SINGLE_DEVICE_ID ];
void vApplicationIRQHandler( uint32_t ulICCIAR )
{
uint32_t ulInterruptID;
XScuGic_VectorTableEntry *TablePtr;
//XScuGic_Config *CfgPtr;
//extern XScuGic_Config XScuGic_ConfigTable[];

//	CfgPtr = &XScuGic_ConfigTable[ XPAR_SCUGIC_SINGLE_DEVICE_ID ];

	/* Re-enable interrupts. */
    __asm ( "cpsie i" );

	/* The ID of the interrupt can be obtained by bitwise anding the ICCIAR value
	with 0x3FF. */
	ulInterruptID = ulICCIAR & 0x3FFUL;

	configASSERT( ulInterruptID < XSCUGIC_MAX_NUM_INTR_INPUTS );
	/* Call the function installed in the array of installed handler functions. */
	TablePtr = &(CfgPtr->HandlerTable[ ulInterruptID ]);
	TablePtr->Handler(TablePtr->CallBackRef);

//	intc_func_table[ ulInterruptID ]( 0 );
}



