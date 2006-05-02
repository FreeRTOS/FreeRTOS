/*
	FreeRTOS V4.0.1 - Copyright (C) 2003-2006 Richard Barry.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************
	See http://www.FreeRTOS.org for documentation, latest information, license 
	and contact details.  Please ensure to read the configuration and relevant 
	port sections of the online documentation.
	***************************************************************************
*/

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

/*
*/

/* Kernel include files. */
#include "FreeRTOS.h"
#include "Task.h"
#include "partest.h"

/* Hardware specific include files. */
#include "DriverLib.h"

static const unsigned portLONG ulLEDs[] =
{
	GPIO_PIN_6, GPIO_PIN_1, GPIO_PIN_0
};

#define partstLED_PINS ( GPIO_PIN_0 | GPIO_PIN_1 | GPIO_PIN_6 )

#define partstMAX_OUTPUT_LED	( ( unsigned portCHAR ) 3 )

/*-----------------------------------------------------------*/
void vParTestInitialise( void )
{
portBASE_TYPE xLED;

	/* The LED's are on port B. */
    GPIODirModeSet( GPIO_PORTB_BASE, partstLED_PINS, GPIO_DIR_MODE_OUT );

	for( xLED = 0; xLED < partstMAX_OUTPUT_LED; xLED++ )
	{
		vParTestSetLED( xLED, pdFALSE );
	}
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	vTaskSuspendAll();
	{
		if( uxLED < partstMAX_OUTPUT_LED )
		{
			if( xValue == pdFALSE )
			{
				GPIOPinWrite( GPIO_PORTB_BASE, ulLEDs[ uxLED ], ulLEDs[ uxLED ] );
			}
			else
			{
				GPIOPinWrite( GPIO_PORTB_BASE, ulLEDs[ uxLED ], ~ulLEDs[ uxLED ] );
			}
		}	
	}
	xTaskResumeAll();
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
portBASE_TYPE xCurrentValue;

	vTaskSuspendAll();
	{
		if( uxLED < partstMAX_OUTPUT_LED )
		{
			xCurrentValue = GPIOPinRead( GPIO_PORTB_BASE, ulLEDs[ uxLED ] );
			if( xCurrentValue )
			{
				GPIOPinWrite( GPIO_PORTB_BASE, ulLEDs[ uxLED ], ~ulLEDs[ uxLED ] );
			}
			else
			{
				GPIOPinWrite( GPIO_PORTB_BASE, ulLEDs[ uxLED ], ulLEDs[ uxLED ] );
			}
		}
	}
	xTaskResumeAll();
}
