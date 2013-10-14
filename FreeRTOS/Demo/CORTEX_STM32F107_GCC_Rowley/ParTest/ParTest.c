/*
    FreeRTOS V7.5.3 - Copyright (C) 2013 Real Time Engineers Ltd. 
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

/* FreeRTOS.org includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "partest.h"

/* Standard includes. */
#include <string.h>

/* Library includes. */
#include "stm32f10x_lib.h"

#define partstNUM_LEDs		4

/* Holds the current output state for each of the LEDs. */
static unsigned char ucBitStates[ partstNUM_LEDs ];

/* Holds the port used by each of the LEDs. */
static GPIO_TypeDef * uxIO_Port[ partstNUM_LEDs ];

/* Holds the pin used by each of the LEDs. */
static const unsigned short uxIO_Pins[ partstNUM_LEDs ] = { GPIO_Pin_14, GPIO_Pin_13, GPIO_Pin_3, GPIO_Pin_4 };

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
GPIO_InitTypeDef GPIO_InitStructure;

	/* Configure PE14, PD13, PD3 and PD4 output push-pull */
	GPIO_InitStructure.GPIO_Pin =  GPIO_Pin_14;
	GPIO_InitStructure.GPIO_Mode = GPIO_Mode_Out_PP;
	GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;
	GPIO_Init( GPIOE, &GPIO_InitStructure );

	GPIO_InitStructure.GPIO_Pin =  GPIO_Pin_13;
	GPIO_InitStructure.GPIO_Mode = GPIO_Mode_Out_PP;
	GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;
	GPIO_Init( GPIOD, &GPIO_InitStructure );

	GPIO_InitStructure.GPIO_Pin =  GPIO_Pin_3 | GPIO_Pin_4;
	GPIO_InitStructure.GPIO_Mode = GPIO_Mode_Out_PP;
	GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;
	GPIO_Init( GPIOD, &GPIO_InitStructure );

	memset( ucBitStates, 0x00, sizeof( ucBitStates ) );

	uxIO_Port[ 0 ] =  GPIOE;
    uxIO_Port[ 1 ] =  GPIOD;
    uxIO_Port[ 2 ] =  GPIOD;
    uxIO_Port[ 3 ] =  GPIOD;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED < partstNUM_LEDs )
	{
		portENTER_CRITICAL();
		{
			if( xValue != pdFALSE )
			{
				ucBitStates[ uxLED ] = pdTRUE;
			}
			else
			{
				ucBitStates[ uxLED ] = pdFALSE;
			}

            GPIO_WriteBit( uxIO_Port[ uxLED ], uxIO_Pins[ uxLED ], ucBitStates[ uxLED ] );
		}
		portEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstNUM_LEDs )
	{
		portENTER_CRITICAL();
		{
			ucBitStates[ uxLED ] = !ucBitStates[ uxLED ];
            GPIO_WriteBit( uxIO_Port[ uxLED ], uxIO_Pins[ uxLED ], ucBitStates[ uxLED ] );
		}
		portEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

portBASE_TYPE xGetLEDState( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstNUM_LEDs )
	{
		return ( portBASE_TYPE ) ucBitStates[ uxLED ];
	}
	else
	{
		return 0;
	}
}
