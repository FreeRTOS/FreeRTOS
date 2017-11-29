/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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

/*-----------------------------------------------------------
 * Simple IO routines to control the LEDs.
 * This file is called ParTest.c for historic reasons.  Originally it stood for
 * PARallel port TEST.
 *-----------------------------------------------------------*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "partest.h"

/* Xilinx includes. */
#include "xgpiops.h"

#define partstNUM_LEDS			( 1 )
#define partstDIRECTION_OUTPUT	( 1 )
#define partstOUTPUT_ENABLED	( 1 )
#define partstLED_OUTPUT		( 10 )

/*-----------------------------------------------------------*/

static XGpioPs xGpio;

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
XGpioPs_Config *pxConfigPtr;
BaseType_t xStatus;

	/* Initialise the GPIO driver. */
	pxConfigPtr = XGpioPs_LookupConfig( XPAR_XGPIOPS_0_DEVICE_ID );
	xStatus = XGpioPs_CfgInitialize( &xGpio, pxConfigPtr, pxConfigPtr->BaseAddr );
	configASSERT( xStatus == XST_SUCCESS );
	( void ) xStatus; /* Remove compiler warning if configASSERT() is not defined. */

	/* Enable outputs and set low. */
	XGpioPs_SetDirectionPin( &xGpio, partstLED_OUTPUT, partstDIRECTION_OUTPUT );
	XGpioPs_SetOutputEnablePin( &xGpio, partstLED_OUTPUT, partstOUTPUT_ENABLED );
	XGpioPs_WritePin( &xGpio, partstLED_OUTPUT, 0x0 );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( UBaseType_t uxLED, BaseType_t xValue )
{
	( void ) uxLED;
	XGpioPs_WritePin( &xGpio, partstLED_OUTPUT, xValue );
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
BaseType_t xLEDState;

	( void ) uxLED;

	xLEDState = XGpioPs_ReadPin( &xGpio, partstLED_OUTPUT );
	XGpioPs_WritePin( &xGpio, partstLED_OUTPUT, !xLEDState );
}



