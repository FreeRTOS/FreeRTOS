/*
    FreeRTOS V8.2.1 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

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
#define partstNUM_LEDS			( ( unsigned char ) 6 )
#define partstSEGMENTS_ON		( ( unsigned char ) 0x0f )
#define partstSEGMENTS_OFF		( ( unsigned char ) 0x00 )

/* The LED number of the real on board LED, rather than a simulated LED. */
#define partstON_BOARD_LED		( ( unsigned portBASE_TYPE ) 10 )
#define mainON_BOARD_LED_BIT	( ( unsigned char ) 0x01 )

/* The LCD segments used to generate the '*' characters for LED's 0 to 5. */
unsigned char * const ucRHSSegments[ partstNUM_LEDS ] = {	( unsigned char * )0xa4, 
																( unsigned char * )0xa2, 
																( unsigned char * )0xa0, 
																( unsigned char * )0x9e,
																( unsigned char * )0x9c,
																( unsigned char * )0x9a };

unsigned char * const ucLHSSegments[ partstNUM_LEDS ] = {	( unsigned char * )0xa3, 
																( unsigned char * )0xa1, 
																( unsigned char * )0x9f, 
																( unsigned char * )0x9d,
																( unsigned char * )0x9b,
																( unsigned char * )0x99 };

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
static unsigned short sState = pdFALSE;

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


