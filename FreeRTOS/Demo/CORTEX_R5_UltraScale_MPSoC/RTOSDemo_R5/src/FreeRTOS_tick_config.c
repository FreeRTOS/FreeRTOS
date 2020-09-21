/*
 * FreeRTOS Kernel V10.3.0
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
#include "Task.h"

/* Xilinx includes. */
#include "xscugic.h"
#include "xttcps.h"

/* Settings to generate the tick from channel 0 of TTC 0. */
#define tickTTC_ID 			XPAR_PSU_TTC_0_DEVICE_ID
#define tickINTERRUPT_ID 	XPAR_XTTCPS_0_INTR

/* The timer used to generate the tick interrupt. */
static XTtcPs xTimerInstance;

/*
 * The application must provide a function that configures a peripheral to
 * create the FreeRTOS tick interrupt, then define configSETUP_TICK_INTERRUPT()
 * in FreeRTOSConfig.h to call the function.  This file contains a function
 * that is suitable for use on the Zynq SoC.
 */
void vConfigureTickInterrupt( void )
{
XTtcPs_Config *pxTimerConfig;
BaseType_t xStatus;
XScuGic_Config *pxGICConfig;
static XScuGic xInterruptController; 	/* Interrupt controller instance */
uint16_t usInterval;
uint8_t ucPrescale = 0;
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

	/* The interrupt priority must be the lowest possible. */
	XScuGic_SetPriorityTriggerType( &xInterruptController, tickINTERRUPT_ID, portLOWEST_USABLE_INTERRUPT_PRIORITY << portPRIORITY_SHIFT, ucRisingEdge );

	/* Install the FreeRTOS tick handler. */
	xStatus = XScuGic_Connect( &xInterruptController, tickINTERRUPT_ID, (Xil_ExceptionHandler) FreeRTOS_Tick_Handler, NULL );
	configASSERT( xStatus == XST_SUCCESS );
	( void ) xStatus; /* Remove compiler warning if configASSERT() is not defined. */

	/* Initialise the Triple Timer Counter (TTC) that is going to be used to
	generate the tick interrupt. */
	pxTimerConfig = XTtcPs_LookupConfig( tickTTC_ID );
	xStatus = XTtcPs_CfgInitialize( &xTimerInstance, pxTimerConfig, pxTimerConfig->BaseAddress );
	configASSERT( xStatus == XST_SUCCESS );
	( void ) xStatus; /* Remove compiler warning if configASSERT() is not defined. */

	/* Configure the interval to be the require tick rate. */
	XTtcPs_CalcIntervalFromFreq( &xTimerInstance, configTICK_RATE_HZ, &usInterval, &ucPrescale );
	XTtcPs_SetInterval( &xTimerInstance, usInterval );
	XTtcPs_SetPrescaler( &xTimerInstance, ucPrescale );

	/* Interval mode used. */
	XTtcPs_SetOptions( &xTimerInstance, XTTCPS_OPTION_INTERVAL_MODE | XTTCPS_OPTION_WAVE_DISABLE );

	/* Start the timer. */
	XTtcPs_Start( &xTimerInstance );

	/* Enable the interrupt in the interrupt controller. */
	XScuGic_Enable( &xInterruptController, tickINTERRUPT_ID );

	/* Enable the interrupt in the timer itself. */
	XTtcPs_EnableInterrupts( &xTimerInstance, XTTCPS_IXR_INTERVAL_MASK );
}
/*-----------------------------------------------------------*/

void vClearTickInterrupt( void )
{
volatile uint32_t ulStatus;

	ulStatus = XTtcPs_GetInterruptStatus( &xTimerInstance );
	( void ) ulStatus;
}
/*-----------------------------------------------------------*/

void vApplicationIRQHandler( uint32_t ulICCIAR )
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
		/* Call the function installed in the array of installed handler
		functions. */
		pxVectorEntry = &( pxVectorTable[ ulInterruptID ] );
		pxVectorEntry->Handler( pxVectorEntry->CallBackRef );
	}
}


