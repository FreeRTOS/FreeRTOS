/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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


/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo application includes. */
#include "partest.h"

/* Library includes. */
#include "xparameters.h"
#include "xgpio_l.h"

/* Misc hardware specific definitions. */
#define partstALL_AS_OUTPUT	0x00
#define partstCHANNEL_1		0x01
#define partstMAX_8BIT_LED	0x07

/* The outputs are split into two IO sections, these variables maintain the 
current value of either section. */
static unsigned portBASE_TYPE uxCurrentOutput8Bit, uxCurrentOutput5Bit;

/*-----------------------------------------------------------*/
/*
 * Setup the IO for the LED outputs.
 */
void vParTestInitialise( void )
{
	/* Set both sets of LED's on the demo board to outputs. */
	XGpio_mSetDataDirection( XPAR_LEDS_8BIT_BASEADDR, partstCHANNEL_1, partstALL_AS_OUTPUT );
	XGpio_mSetDataDirection( XPAR_LEDS_POSITIONS_BASEADDR, partstCHANNEL_1, partstALL_AS_OUTPUT );

	/* Start with all outputs off. */
	uxCurrentOutput8Bit = 0;
	XGpio_mSetDataReg( XPAR_LEDS_8BIT_BASEADDR, partstCHANNEL_1, 0x00 );
	uxCurrentOutput5Bit = 0;
	XGpio_mSetDataReg( XPAR_LEDS_POSITIONS_BASEADDR, partstCHANNEL_1, 0x00 );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned portBASE_TYPE uxBaseAddress, *puxCurrentValue;

	portENTER_CRITICAL();
	{
		/* Which IO section does the LED being set/cleared belong to?  The
		4 bit or 5 bit outputs? */
		if( uxLED <= partstMAX_8BIT_LED )
		{
			uxBaseAddress = XPAR_LEDS_8BIT_BASEADDR;
			puxCurrentValue = &uxCurrentOutput5Bit;
		}	
		else
		{
			uxBaseAddress = XPAR_LEDS_POSITIONS_BASEADDR;
			puxCurrentValue = &uxCurrentOutput8Bit;
			uxLED -= partstMAX_8BIT_LED;
		}

		/* Setup the bit mask accordingly. */
		uxLED = 0x01 << uxLED;

		/* Maintain the current output value. */
		if( xValue )
		{
			*puxCurrentValue |= uxLED;
		}
		else
		{
			*puxCurrentValue &= ~uxLED;
		}

		/* Write the value to the port. */
		XGpio_mSetDataReg( uxBaseAddress, partstCHANNEL_1, *puxCurrentValue );
	}
	portEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned portBASE_TYPE uxBaseAddress, *puxCurrentValue;

	portENTER_CRITICAL();
	{
		/* Which IO section does the LED being toggled belong to?  The
		4 bit or 5 bit outputs? */
		if( uxLED <= partstMAX_8BIT_LED )
		{

			uxBaseAddress = XPAR_LEDS_8BIT_BASEADDR;
			puxCurrentValue = &uxCurrentOutput5Bit;
		}	
		else
		{
			uxBaseAddress = XPAR_LEDS_POSITIONS_BASEADDR;
			puxCurrentValue = &uxCurrentOutput8Bit;
			uxLED -= partstMAX_8BIT_LED;
		}

		/* Setup the bit mask accordingly. */
		uxLED = 0x01 << uxLED;

		/* Maintain the current output value. */
		if( *puxCurrentValue & uxLED )
		{
			*puxCurrentValue &= ~uxLED;
		}
		else
		{
			*puxCurrentValue |= uxLED;
		}

		/* Write the value to the port. */
		XGpio_mSetDataReg(uxBaseAddress, partstCHANNEL_1, *puxCurrentValue );
	}
	portEXIT_CRITICAL();
}


