/*
    FreeRTOS V6.0.5 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public 
    License and the FreeRTOS license exception along with FreeRTOS; if not it 
    can be viewed here: http://www.freertos.org/a00114.html and also obtained 
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

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
#define partstLED_PORT		*( ( unsigned short * ) 0x5800f3fc )

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
unsigned short usLED = 0x0001;

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
unsigned short usLED = 0x0001;

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




