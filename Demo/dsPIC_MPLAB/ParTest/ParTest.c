/*
	FreeRTOS V5.4.2 - Copyright (C) 2009 Real Time Engineers Ltd.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under 
	the terms of the GNU General Public License (version 2) as published by the 
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the 
	source code for proprietary components outside of the FreeRTOS kernel.  
	Alternative commercial license and support terms are also available upon 
	request.  See the licensing section of http://www.FreeRTOS.org for full 
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
	* See http://www.FreeRTOS.org/Documentation for details                   *
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

/* Demo app includes. */
#include "partest.h"

#define ptOUTPUT 	0
#define ptALL_OFF	0

unsigned portBASE_TYPE uxOutput;

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* The explorer 16 board has LED's on port A.  All bits are set as output
	so PORTA is read-modified-written directly.  Two pins have change 
	notification pullups that need disabling. */
	CNPU2bits.CN22PUE = 0;
	CNPU2bits.CN23PUE = 0;
	TRISA = ptOUTPUT;
	PORTA = ptALL_OFF;
	uxOutput = ptALL_OFF;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned portBASE_TYPE uxLEDBit;

	/* Which port A bit is being modified? */
	uxLEDBit = 1 << uxLED;

	if( xValue )
	{
		/* Turn the LED on. */
		portENTER_CRITICAL();
		{
			uxOutput |= uxLEDBit;
			PORTA = uxOutput;
		}
		portEXIT_CRITICAL();
	}
	else
	{
		/* Turn the LED off. */
		portENTER_CRITICAL();
		{
			uxOutput &= ~uxLEDBit;
			PORTA = uxOutput;
		}
		portEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned portBASE_TYPE uxLEDBit;

	uxLEDBit = 1 << uxLED;
	portENTER_CRITICAL();
	{
		/* If the LED is already on - turn it off.  If the LED is already
		off, turn it on. */
		if( uxOutput & uxLEDBit )
		{
			uxOutput &= ~uxLEDBit;
			PORTA = uxOutput;
		}
		else
		{
			uxOutput |= uxLEDBit;
			PORTA = uxOutput;
		}
	}
	portEXIT_CRITICAL();
}

