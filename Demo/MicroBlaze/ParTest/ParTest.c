/*
	FreeRTOS.org V5.0.4 - Copyright (C) 2003-2008 Richard Barry.

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

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

/* Kernel includes. */
#include "FreeRTOS.h"

/* Demo application includes. */
#include "partest.h"

/* Library includes. */
#include "xgpio_l.h"

/* Misc hardware specific definitions. */
#define partstALL_AS_OUTPUT	0x00
#define partstCHANNEL_1		0x01
#define partstMAX_4BIT_LED	0x03

/* The outputs are split into two IO sections, these variables maintain the 
current value of either section. */
static unsigned portBASE_TYPE uxCurrentOutput4Bit, uxCurrentOutput5Bit;

/*-----------------------------------------------------------*/
/*
 * Setup the IO for the LED outputs.
 */
void vParTestInitialise( void )
{
	/* Set both sets of LED's on the demo board to outputs. */
	XGpio_mSetDataDirection( XPAR_LEDS_4BIT_BASEADDR, partstCHANNEL_1, partstALL_AS_OUTPUT );
	XGpio_mSetDataDirection( XPAR_LEDS_POSITIONS_BASEADDR, partstCHANNEL_1, partstALL_AS_OUTPUT );

	/* Start with all outputs off. */
	uxCurrentOutput4Bit = 0;
	XGpio_mSetDataReg( XPAR_LEDS_4BIT_BASEADDR, partstCHANNEL_1, 0x00 );
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
		if( uxLED <= partstMAX_4BIT_LED )
		{
			uxBaseAddress = XPAR_LEDS_4BIT_BASEADDR;
			puxCurrentValue = &uxCurrentOutput4Bit;
		}	
		else
		{
			uxBaseAddress = XPAR_LEDS_POSITIONS_BASEADDR;
			puxCurrentValue = &uxCurrentOutput5Bit;
			uxLED -= partstMAX_4BIT_LED;
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
		if( uxLED <= partstMAX_4BIT_LED )
		{
			uxBaseAddress = XPAR_LEDS_4BIT_BASEADDR;
			puxCurrentValue = &uxCurrentOutput4Bit;
		}	
		else
		{
			uxBaseAddress = XPAR_LEDS_POSITIONS_BASEADDR;
			puxCurrentValue = &uxCurrentOutput5Bit;
			uxLED -= partstMAX_4BIT_LED;
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


