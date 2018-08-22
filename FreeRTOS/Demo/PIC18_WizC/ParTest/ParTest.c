/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* 
Changes from V3.0.0

Changes from V3.0.1
*/

/* Scheduler include files. */
#include "FreeRTOS.h"
#include <task.h>

#include "partest.h"

/*-----------------------------------------------------------
 * Simple parallel port IO routines for the FED 40pin demo board.
 * The four LED's are connected to D4 to D7.
 *-----------------------------------------------------------*/

#define partstBIT_AS_OUTPUT			( ( unsigned short ) 0 )
#define partstSET_OUTPUT			( ( unsigned short ) 1 )
#define partstCLEAR_OUTPUT			( ( unsigned short ) 0 )

#define partstENABLE_GENERAL_IO		( ( unsigned char ) 7 )

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* Set the top four bits of port D to output. */
	bTRD7		= partstBIT_AS_OUTPUT;
	bTRD6		= partstBIT_AS_OUTPUT;
	bTRD5		= partstBIT_AS_OUTPUT;
	bTRD4		= partstBIT_AS_OUTPUT;

	/* Start with all bits off. */
	bRD7		= partstCLEAR_OUTPUT;
	bRD6		= partstCLEAR_OUTPUT;
	bRD5		= partstCLEAR_OUTPUT;
	bRD4		= partstCLEAR_OUTPUT;

	/* Enable the driver. */
	ADCON1		= partstENABLE_GENERAL_IO;
	bTRE2		= partstBIT_AS_OUTPUT;
	bRE2		= partstSET_OUTPUT;	
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned char ucLED, char cValue )
{
	/* We are only using the top nibble, so LED 0 corresponds to bit 4. */	
	vTaskSuspendAll();
	{
		switch( ucLED )
		{
			case 3	:	bRD7 = ( short ) cValue;
						break;
			case 2	:	bRD6 = ( short ) cValue;
						break;
			case 1	:	bRD5 = ( short ) cValue;
						break;
			case 0	:	bRD4 = ( short ) cValue;
						break;
			default	:	/* There are only 4 LED's. */
						break;
		}
	}
	xTaskResumeAll();
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned char ucLED )
{
	/* We are only using the top nibble, so LED 0 corresponds to bit 4. */	
	vTaskSuspendAll();
	{
		switch( ucLED )
		{
			case 3	:	bRD7 = !bRD7;
						break;
			case 2	:	bRD6 = !bRD6;
						break;
			case 1	:	bRD5 = !bRD5;
						break;
			case 0	:	bRD4 = !bRD4 );
						break;
			default	:	/* There are only 4 LED's. */
						break;
		}
	}
	xTaskResumeAll();
}



