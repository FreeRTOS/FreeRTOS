/*
	FreeRTOS.org V4.1.2 - Copyright (C) 2003-2006 Richard Barry.

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
	***************************************************************************
*/

/* Library includes. */
#include "75x_GPIO.h"
#include "75x_map.h"

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

#define partstNUM_LEDS	4

typedef struct GPIOMAP
{
	GPIO_TypeDef	*pxPort;
	unsigned portLONG ulPin;
	unsigned portLONG ulValue;
} GPIO_MAP;

static GPIO_MAP xLEDMap[ partstNUM_LEDS ] =
{
	{ ( GPIO_TypeDef	* )GPIO1_BASE, GPIO_Pin_1, 0UL },
	{ ( GPIO_TypeDef	* )GPIO0_BASE, GPIO_Pin_16, 0UL },
	{ ( GPIO_TypeDef	* )GPIO2_BASE, GPIO_Pin_18, 0UL },	
	{ ( GPIO_TypeDef	* )GPIO2_BASE, GPIO_Pin_19, 0UL }
	
};

/*-----------------------------------------------------------*/
GPIO_InitTypeDef    GPIO_InitStructure ;

void vParTestInitialise( void )
{	
    /* Configure the bits used to flash LED's on port 1 as output. */
  /* Configure LED3 */
  GPIO_InitStructure.GPIO_Mode = GPIO_Mode_Out_PP;
  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_16;
  GPIO_Init(GPIO0,&GPIO_InitStructure);
  /* Configure LED2 */
  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_1;
  GPIO_Init(GPIO1, &GPIO_InitStructure);
  /* Configure LED4 and LED5 */
  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_18 | GPIO_Pin_19;
  GPIO_Init(GPIO2, &GPIO_InitStructure);

	vParTestSetLED( 0, 0 );
	vParTestSetLED( 1, 0 );
	vParTestSetLED( 2, 0 );
	vParTestSetLED( 3, 0 );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED < partstNUM_LEDS )
	{
		if( xValue )
		{
			GPIO_WriteBit( xLEDMap[ uxLED ].pxPort, xLEDMap[ uxLED ].ulPin, Bit_RESET );
			xLEDMap[ uxLED ].ulValue = 0;
		}
		else
		{
			GPIO_WriteBit( xLEDMap[ uxLED ].pxPort, xLEDMap[ uxLED ].ulPin, Bit_SET );
			xLEDMap[ uxLED ].ulValue = 1;			
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstNUM_LEDS )
	{
		if( xLEDMap[ uxLED ].ulValue == 1 )
		{
			GPIO_WriteBit( xLEDMap[ uxLED ].pxPort, xLEDMap[ uxLED ].ulPin, Bit_RESET );
			xLEDMap[ uxLED ].ulValue = 0;
		}
		else
		{
			GPIO_WriteBit( xLEDMap[ uxLED ].pxPort, xLEDMap[ uxLED ].ulPin, Bit_SET );
			xLEDMap[ uxLED ].ulValue = 1;			
		}
	}
}




