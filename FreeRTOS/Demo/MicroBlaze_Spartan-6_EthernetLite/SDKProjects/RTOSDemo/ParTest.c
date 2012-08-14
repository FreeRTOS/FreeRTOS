/*
    FreeRTOS V7.2.0 - Copyright (C) 2012 Real Time Engineers Ltd.
	

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!
    
    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?                                      *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest information, 
    license and contact details.
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

/*-----------------------------------------------------------
 * Simple digital IO routines.
 *-----------------------------------------------------------*/

/* Kernel includes. */
#include "FreeRTOS.h"

/* Demo application includes. */
#include "partest.h"

/* Library includes. */
#include "xgpio.h"

/* The hardware design that accompanies this demo project has four LED 
outputs. */
#define partstMAX_LED	4

/*-----------------------------------------------------------*/

/* A hardware specific constant required to use the Xilinx driver library. */
static const unsigned portBASE_TYPE uxGPIOOutputChannel = 1UL;

/* The current state of the output port. */
static unsigned char ucGPIOState = 0U;

/* Structure that hold the state of the ouptut peripheral used by this demo.
This is used by the Xilinx peripheral driver API functions. */
static XGpio xOutputGPIOInstance;

/*
 * Setup the IO for the LED outputs.
 */
void vParTestInitialise( void )
{
portBASE_TYPE xStatus;
const unsigned char ucSetToOutput = 0U;

	/* Initialise the GPIO for the LEDs. */
	xStatus = XGpio_Initialize( &xOutputGPIOInstance, XPAR_LEDS_4BITS_DEVICE_ID );
	if( xStatus == XST_SUCCESS )
	{
		/* All bits on this channel are going to be outputs (LEDs). */
		XGpio_SetDataDirection( &xOutputGPIOInstance, uxGPIOOutputChannel, ucSetToOutput );

		/* Start with all LEDs off. */
		ucGPIOState = 0U;
		XGpio_DiscreteWrite( &xOutputGPIOInstance, uxGPIOOutputChannel, ucGPIOState );
	}
	
	configASSERT( xStatus == XST_SUCCESS );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned char ucLED = 1U;

	/* Only attempt to set the LED if it is in range. */
	if( uxLED < partstMAX_LED )
	{
		ucLED <<= ( unsigned char ) uxLED;

		portENTER_CRITICAL();
		{
			if( xValue == pdFALSE )
			{
				ucGPIOState &= ~ucLED;
			}
			else
			{
				ucGPIOState |= ucLED;
			}
			XGpio_DiscreteWrite( &xOutputGPIOInstance, uxGPIOOutputChannel, ucGPIOState );
		}
		portEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned char ucLED = 1U;

	/* Only attempt to toggle the LED if it is in range. */
	if( uxLED < partstMAX_LED )
	{
		ucLED <<= ( unsigned char ) uxLED;

		portENTER_CRITICAL();
		{
			if( ( ucGPIOState & ucLED ) != 0 )
			{
				ucGPIOState &= ~ucLED;
			}
			else
			{
				ucGPIOState |= ucLED;
			}

			XGpio_DiscreteWrite( &xOutputGPIOInstance, uxGPIOOutputChannel, ucGPIOState );
		}
		portEXIT_CRITICAL();
	}
}



