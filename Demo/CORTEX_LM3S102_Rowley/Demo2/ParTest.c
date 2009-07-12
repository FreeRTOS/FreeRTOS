/*
	FreeRTOS V5.4.0 - Copyright (C) 2003-2009 Richard Barry.

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

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

/*
*/


#include "FreeRTOS.h"
#include "task.h"
#include "partest.h"

#include "pdc.h"

#define partstPINS	(GPIO_PIN_0 | GPIO_PIN_1 | GPIO_PIN_2 | GPIO_PIN_3 Z | GPIO_PIN_4 | GPIO_PIN_5 | GPIO_PIN_6 | GPIO_PIN_7)

#define partstALL_OUTPUTS_OFF	( ( unsigned portCHAR ) 0x00 )
#define partstMAX_OUTPUT_LED	( ( unsigned portCHAR ) 8 )

static volatile unsigned portCHAR ucOutputValue = partstALL_OUTPUTS_OFF;

void vParTestInitialise( void )
{
	PDCInit();
	PDCWrite( PDC_LED, ucOutputValue );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned portCHAR ucBit = ( unsigned portCHAR ) 1;

	vTaskSuspendAll();
	{
		if( uxLED < partstMAX_OUTPUT_LED )
		{
			ucBit = ( ( unsigned portCHAR ) 1 ) << uxLED;

			if( xValue == pdFALSE )
			{
				ucBit ^= ( unsigned portCHAR ) 0xff;
				ucOutputValue &= ucBit;
			}
			else
			{
				ucOutputValue |= ucBit;
			}

			PDCWrite( PDC_LED, ucOutputValue );
		}	
	}
	xTaskResumeAll();
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned portCHAR ucBit;

	vTaskSuspendAll();
	{
		if( uxLED < partstMAX_OUTPUT_LED )
		{
			ucBit = ( ( unsigned portCHAR ) 1 ) << uxLED;

			if( ucOutputValue & ucBit )
			{
				ucOutputValue &= ~ucBit;
			}
			else
			{
				ucOutputValue |= ucBit;
			}

			PDCWrite( PDC_LED, ucOutputValue );
		}
	}
	xTaskResumeAll();
}

