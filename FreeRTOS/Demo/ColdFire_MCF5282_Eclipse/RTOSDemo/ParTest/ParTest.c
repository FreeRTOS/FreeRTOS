/*
    FreeRTOS V8.2.3 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
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

static const unsigned char ucLEDDefinitions[ partstNUM_LEDs ] = { LED0_POS, LED1_POS, LED2_POS, LED3_POS };

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
			if( ( MCF_GPIO_PORTTD & ucLEDDefinitions[ uxLED ] ) == ( unsigned char ) 0 )
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
			if( ( MCF_GPIO_PORTTC & ucLEDDefinitions[ uxLED ] ) == ( unsigned char ) 0 )
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

