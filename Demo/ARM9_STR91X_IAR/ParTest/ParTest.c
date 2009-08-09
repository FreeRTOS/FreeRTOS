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




