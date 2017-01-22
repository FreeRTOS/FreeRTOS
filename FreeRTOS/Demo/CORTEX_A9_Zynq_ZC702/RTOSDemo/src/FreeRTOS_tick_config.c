/*
    FreeRTOS V9.0.1 - Copyright (C) 2017 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Xilinx includes. */
#include "xscutimer.h"
#include "xscugic.h"

#define XSCUTIMER_CLOCK_HZ ( XPAR_CPU_CORTEXA9_0_CPU_CLK_FREQ_HZ / 2UL )

static XScuTimer xTimer;
XScuGic xInterruptController; 	/* Interrupt controller instance */

/*
 * The application must provide a function that configures a peripheral to
 * create the FreeRTOS tick interrupt, then define configSETUP_TICK_INTERRUPT()
 * in FreeRTOSConfig.h to call the function.  This file contains a function
 * that is suitable for use on the Zynq SoC.
 */
void vConfigureTickInterrupt( void )
{
BaseType_t xStatus;
extern void FreeRTOS_Tick_Handler( void );
XScuTimer_Config *pxTimerConfig;
XScuGic_Config *pxGICConfig;
const uint8_t ucRisingEdge = 3;

	/* This function is called with the IRQ interrupt disabled, and the IRQ
	interrupt should be left disabled.  It is enabled automatically when the
	scheduler is started. */

	/* Ensure XScuGic_CfgInitialize() has been called.  In this demo it has
	already been called from prvSetupHardware() in main(). */
	pxGICConfig = XScuGic_LookupConfig( XPAR_SCUGIC_SINGLE_DEVICE_ID );
	xStatus = XScuGic_CfgInitialize( &xInterruptController, pxGICConfig, pxGICConfig->CpuBaseAddress );
	configASSERT( xStatus == XST_SUCCESS );
	( void ) xStatus; /* Remove compiler warning if configASSERT() is not defined. */

	/* The priority must be the lowest possible. */
	XScuGic_SetPriorityTriggerType( &xInterruptController, XPAR_SCUTIMER_INTR, portLOWEST_USABLE_INTERRUPT_PRIORITY << portPRIORITY_SHIFT, ucRisingEdge );

	/* Install the FreeRTOS tick handler. */
	xStatus = XScuGic_Connect( &xInterruptController, XPAR_SCUTIMER_INTR, (Xil_ExceptionHandler) FreeRTOS_Tick_Handler, ( void * ) &xTimer );
	configASSERT( xStatus == XST_SUCCESS );
	( void ) xStatus; /* Remove compiler warning if configASSERT() is not defined. */

	/* Initialise the timer. */
	pxTimerConfig = XScuTimer_LookupConfig( XPAR_SCUTIMER_DEVICE_ID );
	xStatus = XScuTimer_CfgInitialize( &xTimer, pxTimerConfig, pxTimerConfig->BaseAddr );
	configASSERT( xStatus == XST_SUCCESS );
	( void ) xStatus; /* Remove compiler warning if configASSERT() is not defined. */

	/* Enable Auto reload mode. */
	XScuTimer_EnableAutoReload( &xTimer );

	/* Ensure there is no prescale. */
	XScuTimer_SetPrescaler( &xTimer, 0 );

	/* Load the timer counter register. */
	XScuTimer_LoadTimer( &xTimer, XSCUTIMER_CLOCK_HZ / configTICK_RATE_HZ );

	/* Start the timer counter and then wait for it to timeout a number of
	times. */
	XScuTimer_Start( &xTimer );

	/* Enable the interrupt for the xTimer in the interrupt controller. */
	XScuGic_Enable( &xInterruptController, XPAR_SCUTIMER_INTR );

	/* Enable the interrupt in the xTimer itself. */
	vClearTickInterrupt();
	XScuTimer_EnableInterrupt( &xTimer );
}
/*-----------------------------------------------------------*/

void vClearTickInterrupt( void )
{
	XScuTimer_ClearInterruptStatus( &xTimer );
}
/*-----------------------------------------------------------*/

/* This is the callback function which is called by the FreeRTOS Cortex-A port
layer in response to an interrupt.  If the function is called
vApplicationFPUSafeIRQHandler() then it is called after the floating point
registers have been saved.  If the function is called vApplicationIRQHandler()
then it will be called without first having saved the FPU registers.  See
http://www.freertos.org/Using-FreeRTOS-on-Cortex-A-Embedded-Processors.html for
more information */
void vApplicationFPUSafeIRQHandler( uint32_t ulICCIAR )
{
extern const XScuGic_Config XScuGic_ConfigTable[];
static const XScuGic_VectorTableEntry *pxVectorTable = XScuGic_ConfigTable[ XPAR_SCUGIC_SINGLE_DEVICE_ID ].HandlerTable;
uint32_t ulInterruptID;
const XScuGic_VectorTableEntry *pxVectorEntry;

	/* Re-enable interrupts. */
	__asm ( "cpsie i" );

	/* The ID of the interrupt is obtained by bitwise anding the ICCIAR value
	with 0x3FF. */
	ulInterruptID = ulICCIAR & 0x3FFUL;
	if( ulInterruptID < XSCUGIC_MAX_NUM_INTR_INPUTS )
	{
		/* Call the function installed in the array of installed handler functions. */
		pxVectorEntry = &( pxVectorTable[ ulInterruptID ] );
		pxVectorEntry->Handler( pxVectorEntry->CallBackRef );
	}
}



