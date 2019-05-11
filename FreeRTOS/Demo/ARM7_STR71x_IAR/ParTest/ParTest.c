/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/* Library includes. */
#include "GPIO.h"

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo application includes. */
#include "partest.h"

/*-----------------------------------------------------------
 * Simple parallel port IO routines for the LED's - which are
 * connected to the second nibble of GPIO port 1.
 *-----------------------------------------------------------*/

#define partstLED_3		0x0080
#define partstLED_2		0x0040
#define partstLED_1		0x0020
#define partstLED_0		0x0010
#define partstON_BOARD	0x0100	/* The LED built onto the KickStart board. */

#define partstALL_LEDs	( partstLED_0 | partstLED_1 | partstLED_2 | partstLED_3 | partstON_BOARD )

#define partstFIRST_LED_BIT 4

/* This demo application uses files that are common to all port demo 
applications.  These files assume 6 LED's are available, whereas I have
only 5 (including the LED built onto the development board).  To prevent
two tasks trying to use the same LED a bit of remapping is performed. 
The ComTest tasks will try and use LED's 6 and 7.  LED 6 is ignored and
has no effect, LED 7 is mapped to LED3.   The LED usage is described in
the port documentation available from the FreeRTOS.org WEB site. */
#define partstCOM_TEST_LED	7
#define partstRX_CHAR_LED	3

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{	
    /* Configure the bits used to flash LED's on port 1 as output. */
    GPIO_Config(GPIO1, partstALL_LEDs, GPIO_OUT_OD);
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED == partstCOM_TEST_LED )
	{
		/* Remap as described above. */
		uxLED = partstRX_CHAR_LED;
	}

	/* Adjust the LED value to map to the port pins actually being used,
	then write the required value to the port. */
	uxLED += partstFIRST_LED_BIT;
    GPIO_BitWrite( GPIO1, uxLED, !xValue );
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED == partstCOM_TEST_LED )
	{
		/* Remap as described above. */
		uxLED = partstRX_CHAR_LED;
	}

	/* Adjust the LED value to map to the port pins actually being used,
	then write the opposite value to the current state to the port pin. */
	uxLED += partstFIRST_LED_BIT;
    GPIO_BitWrite(GPIO1, uxLED, ~GPIO_BitRead( GPIO1, uxLED ) );
}




