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

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "partest.h"

#define partstTOTAL_NUM_LEDs		16
#define partstNUM_LEDs_PER_DISPLAY	8

volatile unsigned char *pucDisplayOutput[ 2 ] = { ( unsigned portCHAR * ) 3, ( unsigned portCHAR * ) 5 };

void vParTestInitialise( void )
{
	/* In this case all the initialisation is performed in prvSetupHardware()
	in main.c. */	
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned portBASE_TYPE uxLEDMask = 0x01;

	if( uxLED < partstNUM_LEDs_PER_DISPLAY )
	{
		uxLEDMask <<= uxLED;
		
		taskENTER_CRITICAL();
		{
			if( xValue )
			{
				*pucDisplayOutput[ 0 ] &= ~uxLEDMask;
			}
			else
			{
				*pucDisplayOutput[ 0 ] |= uxLEDMask;				
			}
		}
		taskEXIT_CRITICAL();
	}
	else if( uxLED < partstTOTAL_NUM_LEDs )
	{
		uxLED -= partstNUM_LEDs_PER_DISPLAY;

		uxLEDMask <<= uxLED;
		
		taskENTER_CRITICAL();
		{
			if( xValue )
			{
				*pucDisplayOutput[ 1 ] &= ~uxLEDMask;
			}
			else
			{
				*pucDisplayOutput[ 1 ] |= uxLEDMask;				
			}
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned portBASE_TYPE uxLEDMask = 0x01;

	if( uxLED < partstNUM_LEDs_PER_DISPLAY )
	{
		uxLEDMask <<= uxLED;
		
		taskENTER_CRITICAL();
		{
			if( *pucDisplayOutput[ 0 ] & uxLEDMask )
			{
				*pucDisplayOutput[ 0 ] &= ~uxLEDMask;
			}
			else
			{
				*pucDisplayOutput[ 0 ] |= uxLEDMask;
			}
		}
		taskEXIT_CRITICAL();
	}
	else if( uxLED < partstTOTAL_NUM_LEDs )
	{
		uxLED -= partstNUM_LEDs_PER_DISPLAY;

		uxLEDMask <<= uxLED;
		
		taskENTER_CRITICAL();
		{
			if( *pucDisplayOutput[ 1 ] & uxLEDMask )
			{
				*pucDisplayOutput[ 1 ] &= ~uxLEDMask;
			}
			else
			{
				*pucDisplayOutput[ 1 ] |= uxLEDMask;
			}
		}
		taskEXIT_CRITICAL();
	}
}




