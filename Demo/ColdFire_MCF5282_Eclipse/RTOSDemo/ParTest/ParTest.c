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

/*
	Changes from V2.5.2

	+ All LED's are turned off to start.
*/


#include "FreeRTOS.h"
#include "task.h"
#include "partest.h"

#define partstNUM_LEDs	4

#define LED0_POS		0x01
#define LED1_POS		0x04
#define LED2_POS		0x01
#define LED3_POS		0x04

static const unsigned portCHAR ucLEDDefinitions[ partstNUM_LEDs ] = { LED0_POS, LED1_POS, LED2_POS, LED3_POS };

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* Set the LEDs to outputs. */
	MCF_GPIO_DDRTD |= ( LED0_POS | LED1_POS );
	MCF_GPIO_DDRTC |= ( LED2_POS | LED3_POS );

	/* Turn LEDs off. */
	MCF_GPIO_SETTC |= ( LED0_POS | LED1_POS );
	MCF_GPIO_SETTD |= ( LED2_POS | LED3_POS );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED < 2 )
	{
		if( xValue != 0 )
		{
			taskENTER_CRITICAL();
				MCF_GPIO_PORTTD |= ucLEDDefinitions[ uxLED ];
			taskEXIT_CRITICAL();
		}
		else
		{
			taskENTER_CRITICAL();
				MCF_GPIO_PORTTD &= ~ucLEDDefinitions[ uxLED ];
			taskEXIT_CRITICAL();
		}
	}
	else if( uxLED < 4 )
	{
		if( xValue != 0 )
		{
			taskENTER_CRITICAL();
				MCF_GPIO_PORTTC |= ucLEDDefinitions[ uxLED ];
			taskEXIT_CRITICAL();
		}
		else
		{
			taskENTER_CRITICAL();
				MCF_GPIO_PORTTC &= ~ucLEDDefinitions[ uxLED ];
			taskEXIT_CRITICAL();
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < 2 )
	{
		taskENTER_CRITICAL();
		{
			if( ( MCF_GPIO_PORTTD & ucLEDDefinitions[ uxLED ] ) == ( unsigned portCHAR ) 0 )
			{
				MCF_GPIO_PORTTD |= ucLEDDefinitions[ uxLED ];
			}
			else
			{
				MCF_GPIO_PORTTD &= ~ucLEDDefinitions[ uxLED ];
			}
		}
		taskEXIT_CRITICAL();
	}
	else if( uxLED < 4 )
	{
		taskENTER_CRITICAL();
		{
			if( ( MCF_GPIO_PORTTC & ucLEDDefinitions[ uxLED ] ) == ( unsigned portCHAR ) 0 )
			{
				MCF_GPIO_PORTTC |= ucLEDDefinitions[ uxLED ];
			}
			else
			{
				MCF_GPIO_PORTTC &= ~ucLEDDefinitions[ uxLED ];
			}
		}
		taskEXIT_CRITICAL();
	}
}

