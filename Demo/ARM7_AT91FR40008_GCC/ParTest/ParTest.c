/*
	FreeRTOS.org V5.2.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it 
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or 
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for 
	more details.

	You should have received a copy of the GNU General Public License along 
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59 
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.

	A special exception to the GPL is included to allow you to distribute a 
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "portable.h"

/* Demo app includes. */
#include "partest.h"

/* Hardware specific definitions. */
#include "AT91R40008.h"
#include "pio.h"
#include "aic.h"

#define partstNUM_LEDS			( 8 )
#define partstALL_OUTPUTS_OFF	( ( unsigned portLONG ) ~(0xFFFFFFFF << partstNUM_LEDS) )

static unsigned portLONG ulLEDReg;

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

static void SetLeds (unsigned int leds)
{
unsigned portLONG ulPIOSetReg, ulPIOClearReg;

	/* LEDs are grouped in different port bits: P3-P6 and P16-P19.
	A port bit set to '0' turns an LED on, '1' turns it off. */

	ulPIOSetReg = ( (leds & 0xF) << 16 ) | ( (leds & 0xF0) >> 1 );
	ulPIOClearReg = (~ulPIOSetReg) & 0x000F0078;

	AT91C_BASE_PIO->PIO_SODR = ulPIOSetReg;
	AT91C_BASE_PIO->PIO_CODR = ulPIOClearReg;
}
/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* This is performed from main() as the io bits are shared with other setup
	functions.  Ensure the outputs are off to start. */
	ulLEDReg = partstALL_OUTPUTS_OFF;  

	/* Enable clock to PIO... */
	AT91C_BASE_PS->PS_PCER = AT91C_PS_PIO;

	/* Enable all 8 LEDs and the four switches to be controlled by PIO... */
	AT91C_BASE_PIO->PIO_PER = P3 | P4 | P5 | P6 | P16 | P17 | P18 | P19 | P1 | P2 | P9 | P12;

	/* Configure all LED PIO lines for output... */
	AT91C_BASE_PIO->PIO_OER = P3 | P4 | P5 | P6 | P16 | P17 | P18 | P19;

	/* Configure all switch PIO lines for input... */
	AT91C_BASE_PIO->PIO_ODR = P1 | P2 | P9 | P12;

	/* Set initial state of LEDs. */
	SetLeds( ulLEDReg );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	/* Switch an LED on or off as requested. */
	if (uxLED < partstNUM_LEDS)
	{
		if( xValue )
		{
			ulLEDReg &= ~(1 << uxLED);
		}
		else
		{
			ulLEDReg |= (1 << uxLED);
		}

		SetLeds( ulLEDReg );
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	/* Toggle the state of the requested LED. */
	if (uxLED < partstNUM_LEDS)
	{
		ulLEDReg ^= ( 1 << uxLED );
		SetLeds( ulLEDReg );
	}
}

