/*
	FreeRTOS.org V4.2.0 - Copyright (C) 2003-2007 Richard Barry.

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

/* Library includes. */
#include  "91x_lib.h"

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo application includes. */
#include "partest.h"

#define partstMAX_LEDs		4
#define partstLED_PORT		*( ( unsigned portSHORT * ) 0x5800f3fc )

/*-----------------------------------------------------------*/

static GPIO_InitTypeDef GPIO9_InitStruct;

void vParTestInitialise( void )
{	
	/* Configure the bits used to flash LED's on port 9 as output. */
	GPIO_StructInit( &GPIO9_InitStruct );
	GPIO9_InitStruct.GPIO_Pin = GPIO_Pin_0 | GPIO_Pin_1 | GPIO_Pin_2 | GPIO_Pin_3;
	GPIO9_InitStruct.GPIO_Direction = GPIO_PinOutput;
	GPIO_Init( GPIO9, &GPIO9_InitStruct );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned portSHORT usLED = 0x0001;

	if( uxLED < partstMAX_LEDs )
	{
		usLED <<= uxLED;

		portENTER_CRITICAL();
		{
			if( xValue )
			{
				partstLED_PORT &= ~usLED;
			}
			else
			{
				partstLED_PORT |= usLED;				
			}		
		}
		portEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned portSHORT usLED = 0x0001;

	if( uxLED < partstMAX_LEDs )
	{
		usLED <<= uxLED;

		portENTER_CRITICAL();
		{
			if( partstLED_PORT & usLED )
			{
				partstLED_PORT &= ~usLED;
			}
			else
			{
				partstLED_PORT |= usLED;			
			}	
		}
		portEXIT_CRITICAL();
	}
}




