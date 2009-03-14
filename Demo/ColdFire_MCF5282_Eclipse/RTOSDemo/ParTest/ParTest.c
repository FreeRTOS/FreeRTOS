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

