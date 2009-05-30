/*
	FreeRTOS.org V5.3.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the 
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


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

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

/*
*/

/* Kernel include files. */
#include "FreeRTOS.h"
#include "task.h"
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
