/*
	FreeRTOS.org V4.0.4 - Copyright (C) 2003-2006 Richard Barry.

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

/*-----------------------------------------------------------
 * Characters on the LCD are used to simulate LED's.  In this case the 'ParTest'
 * is really operating on the LCD display.
 *-----------------------------------------------------------*/

/*
 * This demo is configured to execute on the ES449 prototyping board from
 * SoftBaugh. The ES449 has a built in LCD display and a single built in user
 * LED.  Therefore, in place of flashing an LED, the 'flash' and 'check' tasks
 * toggle '*' characters on the LCD.  The left most '*' represents LED 0, the
 * next LED 1, etc.
 *
 * There is a single genuine on board LED referenced as LED 10.
 */

/* Standard includes. */
#include <signal.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo application includes. */
#include "partest.h"

/* Constants required to setup the LCD. */
#define LCD_DIV_64 5

/* Constants required to access the "LED's".  The LED segments are turned on
and off to generate '*' characters. */
#define partstNUM_LEDS			( ( unsigned portCHAR ) 6 )
#define partstSEGMENTS_ON		( ( unsigned portCHAR ) 0x0f )
#define partstSEGMENTS_OFF		( ( unsigned portCHAR ) 0x00 )

/* The LED number of the real on board LED, rather than a simulated LED. */
#define partstON_BOARD_LED		( ( unsigned portBASE_TYPE ) 10 )
#define mainON_BOARD_LED_BIT	( ( unsigned portCHAR ) 0x01 )

/* The LCD segments used to generate the '*' characters for LED's 0 to 5. */
unsigned portCHAR * const ucRHSSegments[ partstNUM_LEDS ] = {	( unsigned portCHAR * )0xa4, 
																( unsigned portCHAR * )0xa2, 
																( unsigned portCHAR * )0xa0, 
																( unsigned portCHAR * )0x9e,
																( unsigned portCHAR * )0x9c,
																( unsigned portCHAR * )0x9a };

unsigned portCHAR * const ucLHSSegments[ partstNUM_LEDS ] = {	( unsigned portCHAR * )0xa3, 
																( unsigned portCHAR * )0xa1, 
																( unsigned portCHAR * )0x9f, 
																( unsigned portCHAR * )0x9d,
																( unsigned portCHAR * )0x9b,
																( unsigned portCHAR * )0x99 };

/*
 * Toggle the single genuine built in LED.
 */
static void prvToggleOnBoardLED( void );

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* Initialise the LCD hardware. */

	/* Used for the onboard LED. */
	P1DIR = 0x01;

	// Setup Basic Timer for LCD operation
	BTCTL = (LCD_DIV_64+0x23);

	// Setup port functions
	P1SEL = 0x32;
	P2SEL = 0x00;
	P3SEL = 0x00;
	P4SEL = 0xFC;
	P5SEL = 0xFF;
	
	/* Initialise all segments to off. */
	LCDM1 = partstSEGMENTS_OFF;	
	LCDM2 = partstSEGMENTS_OFF;	
	LCDM3 = partstSEGMENTS_OFF;	
	LCDM4 = partstSEGMENTS_OFF;	
	LCDM5 = partstSEGMENTS_OFF;	
	LCDM6 = partstSEGMENTS_OFF;	
	LCDM7 = partstSEGMENTS_OFF;	
	LCDM8 = partstSEGMENTS_OFF;	
	LCDM9 = partstSEGMENTS_OFF;	
	LCDM10 = partstSEGMENTS_OFF;	
	LCDM11 = partstSEGMENTS_OFF;	
	LCDM12 = partstSEGMENTS_OFF;	
	LCDM13 = partstSEGMENTS_OFF;	
	LCDM14 = partstSEGMENTS_OFF;	
	LCDM15 = partstSEGMENTS_OFF;	
	LCDM16 = partstSEGMENTS_OFF;	
	LCDM17 = partstSEGMENTS_OFF;	
	LCDM18 = partstSEGMENTS_OFF;	
	LCDM19 = partstSEGMENTS_OFF;	
	LCDM20 = partstSEGMENTS_OFF;	

	/* Setup LCD control. */
	LCDCTL = (LCDSG0_7|LCD4MUX|LCDON);
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	/* Set or clear the output [in this case show or hide the '*' character. */
	if( uxLED < ( portBASE_TYPE ) partstNUM_LEDS )
	{
		vTaskSuspendAll();
		{
			if( xValue )
			{
				/* Turn on the segments required to show the '*'. */
				*( ucRHSSegments[ uxLED ] ) = partstSEGMENTS_ON;
				*( ucLHSSegments[ uxLED ] ) = partstSEGMENTS_ON;
			}
			else
			{
				/* Turn off all the segments. */
				*( ucRHSSegments[ uxLED ] ) = partstSEGMENTS_OFF;
				*( ucLHSSegments[ uxLED ] ) = partstSEGMENTS_OFF;
			}
		}
		xTaskResumeAll();
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < ( portBASE_TYPE ) partstNUM_LEDS )
	{
		vTaskSuspendAll();
		{
			/* If the '*' is already showing - hide it.  If it is not already
			showing then show it. */
			if( *( ucRHSSegments[ uxLED ] ) )
			{
				*( ucRHSSegments[ uxLED ] ) = partstSEGMENTS_OFF;
				*( ucLHSSegments[ uxLED ] ) = partstSEGMENTS_OFF;
			}
			else
			{
				*( ucRHSSegments[ uxLED ] ) = partstSEGMENTS_ON;
				*( ucLHSSegments[ uxLED ] ) = partstSEGMENTS_ON;
			}
		}
		xTaskResumeAll();
	}
	else
	{
		if( uxLED == partstON_BOARD_LED )
		{
			/* The request related to the genuine on board LED. */
			prvToggleOnBoardLED();
		}
	}	
}
/*-----------------------------------------------------------*/

static void prvToggleOnBoardLED( void )
{
static unsigned portSHORT sState = pdFALSE;

	/* Toggle the state of the single genuine on board LED. */
	if( sState )	
	{
		P1OUT |= mainON_BOARD_LED_BIT;
	}
	else
	{
		P1OUT &= ~mainON_BOARD_LED_BIT;
	}

	sState = !sState;
}
/*-----------------------------------------------------------*/


