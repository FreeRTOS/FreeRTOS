/*
	FreeRTOS.org V4.3.1 - Copyright (C) 2003-2007 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************
	See http://www.FreeRTOS.org for documentation, latest information, license
	and contact details.  Please ensure to read the configuration and relevant
	port sections of the online documentation.

	Also see http://www.SafeRTOS.com for an IEC 61508 compliant version along
	with commercial development and support options.
	***************************************************************************
*/

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

/* FreeRTOS.org includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "partest.h"

/* Library includes. */
#include "stm32f10x_lib.h"

#define partstMAX_OUTPUT_LED	( 4 )
#define partstFIRST_LED			GPIO_Pin_6

static unsigned portSHORT usOutputValue = 0;

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
GPIO_InitTypeDef GPIO_InitStructure;

	/* Configure PC.06, PC.07, PC.08 and PC.09 as output push-pull */
	GPIO_InitStructure.GPIO_Pin =  GPIO_Pin_6 | GPIO_Pin_7 | GPIO_Pin_8 | GPIO_Pin_9;
	GPIO_InitStructure.GPIO_Mode = GPIO_Mode_Out_PP;
	GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;
	GPIO_Init( GPIOC, &GPIO_InitStructure );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned portSHORT usBit;

	vTaskSuspendAll();
	{
		if( uxLED < partstMAX_OUTPUT_LED )
		{
			usBit = partstFIRST_LED << uxLED;

			if( xValue == pdFALSE )
			{
				usBit ^= ( unsigned portSHORT ) 0xffff;
				usOutputValue &= usBit;
			}
			else
			{
				usOutputValue |= usBit;
			}

			GPIO_Write( GPIOC, usOutputValue );
		}	
	}
	xTaskResumeAll();
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned portSHORT usBit;

	vTaskSuspendAll();
	{
		if( uxLED < partstMAX_OUTPUT_LED )
		{
			usBit = partstFIRST_LED << uxLED;

			if( usOutputValue & usBit )
			{
				usOutputValue &= ~usBit;
			}
			else
			{
				usOutputValue |= usBit;
			}

			GPIO_Write( GPIOC, usOutputValue );
		}
	}
	xTaskResumeAll();
}
/*-----------------------------------------------------------*/

