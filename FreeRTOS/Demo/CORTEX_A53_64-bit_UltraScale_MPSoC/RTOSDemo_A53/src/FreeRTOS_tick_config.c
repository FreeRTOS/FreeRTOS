/*
 * FreeRTOS V202112.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Xilinx includes. */
#include "platform.h"
#include "xttcps.h"
#include "xscugic.h"

/* Timer used to generate the tick interrupt. */
static XTtcPs xRTOSTickTimerInstance;

/*-----------------------------------------------------------*/

void vConfigureTickInterrupt( void )
{
BaseType_t xStatus;
XTtcPs_Config *pxTimerConfiguration;
XInterval usInterval;
uint8_t ucPrescale;
const uint8_t ucLevelSensitive = 1;
extern XScuGic xInterruptController;

	pxTimerConfiguration = XTtcPs_LookupConfig( XPAR_XTTCPS_3_DEVICE_ID );

	/* Initialise the device. */
	xStatus = XTtcPs_CfgInitialize( &xRTOSTickTimerInstance, pxTimerConfiguration, pxTimerConfiguration->BaseAddress );

	if( xStatus != XST_SUCCESS )
	{
		/* Not sure how to do this before XTtcPs_CfgInitialize is called as
		*xRTOSTickTimerInstance is set within XTtcPs_CfgInitialize(). */
		XTtcPs_Stop( &xRTOSTickTimerInstance );
		xStatus = XTtcPs_CfgInitialize( &xRTOSTickTimerInstance, pxTimerConfiguration, pxTimerConfiguration->BaseAddress );
		configASSERT( xStatus == XST_SUCCESS );
	}

	/* Set the options. */
	XTtcPs_SetOptions( &xRTOSTickTimerInstance, ( XTTCPS_OPTION_INTERVAL_MODE | XTTCPS_OPTION_WAVE_DISABLE ) );

	/* Derive values from the tick rate. */
	XTtcPs_CalcIntervalFromFreq( &xRTOSTickTimerInstance, configTICK_RATE_HZ, &( usInterval ), &( ucPrescale ) );

	/* Set the interval and prescale. */
	XTtcPs_SetInterval( &xRTOSTickTimerInstance, usInterval );
	XTtcPs_SetPrescaler( &xRTOSTickTimerInstance, ucPrescale );

	/* The priority must be the lowest possible. */
	XScuGic_SetPriorityTriggerType( &xInterruptController, XPAR_XTTCPS_3_INTR, portLOWEST_USABLE_INTERRUPT_PRIORITY << portPRIORITY_SHIFT, ucLevelSensitive );

	/* Connect to the interrupt controller. */
	xStatus = XScuGic_Connect( &xInterruptController, XPAR_XTTCPS_3_INTR, (Xil_ExceptionHandler) FreeRTOS_Tick_Handler, ( void * ) &xRTOSTickTimerInstance );
	configASSERT( xStatus == XST_SUCCESS);

	/* Enable the interrupt in the GIC. */
	XScuGic_Enable( &xInterruptController, XPAR_XTTCPS_3_INTR );

	/* Enable the interrupts in the timer. */
	XTtcPs_EnableInterrupts( &xRTOSTickTimerInstance, XTTCPS_IXR_INTERVAL_MASK );

	/* Start the timer. */
	XTtcPs_Start( &xRTOSTickTimerInstance );
}
/*-----------------------------------------------------------*/

void vClearTickInterrupt( void )
{
volatile uint32_t ulInterruptStatus;

	/* Read the interrupt status, then write it back to clear the interrupt. */
	ulInterruptStatus = XTtcPs_GetInterruptStatus( &xRTOSTickTimerInstance );
	XTtcPs_ClearInterruptStatus( &xRTOSTickTimerInstance, ulInterruptStatus );
	__asm volatile( "DSB SY" );
	__asm volatile( "ISB SY" );
}
/*-----------------------------------------------------------*/

void vApplicationIRQHandler( uint32_t ulICCIAR )
{
extern const XScuGic_Config XScuGic_ConfigTable[];
static const XScuGic_VectorTableEntry *pxVectorTable = XScuGic_ConfigTable[ XPAR_SCUGIC_SINGLE_DEVICE_ID ].HandlerTable;
uint32_t ulInterruptID;
const XScuGic_VectorTableEntry *pxVectorEntry;

	/* Interrupts cannot be re-enabled until the source of the interrupt is
	cleared. The ID of the interrupt is obtained by bitwise ANDing the ICCIAR
	value with 0x3FF. */
	ulInterruptID = ulICCIAR & 0x3FFUL;
	if( ulInterruptID < XSCUGIC_MAX_NUM_INTR_INPUTS )
	{
		/* Call the function installed in the array of installed handler
		functions. */
		pxVectorEntry = &( pxVectorTable[ ulInterruptID ] );
		configASSERT( pxVectorEntry );
		pxVectorEntry->Handler( pxVectorEntry->CallBackRef );
	}
}



