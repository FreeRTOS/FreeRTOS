/*
 * FreeRTOS Kernel V10.3.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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


#include "FreeRTOS.h"
#include "task.h"
#include "partest.h"

#define partstNUM_LEDs	4

/*-----------------------------------------------------------
 * Simple LED IO routines for the tower LEDs LED1 to LED4.
 *-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* Enable pull and output drive. */
	PTHPE_PTHPE3 = 1;
	PTHDD_PTHDD3 = 1;

	PTEPE_PTEPE5 = 1;
	PTEDD_PTEDD5 = 1;

	PTGPE_PTGPE5 = 1;
	PTGDD_PTGDD5 = 1;

	PTEPE_PTEPE3 = 1;
	PTEDD_PTEDD3 = 1;
	
	/* Enable clock to ports. */
	SCGC3_PTE = 1;
	SCGC3_PTF = 1;
	SCGC3_PTG = 1;

	/* Ensure the LEDs are off. */
	vParTestSetLED( 0, 0 );
	vParTestSetLED( 1, 0 );
	vParTestSetLED( 2, 0 );
	vParTestSetLED( 3, 0 );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	switch( uxLED )
	{
		case 0:	PTHD_PTHD3 = xValue;
				break;
		case 1:	PTED_PTED5 = xValue;
				break;
		case 2:	PTGD_PTGD5 = xValue;
				break;
		case 3:	PTED_PTED3 = xValue;
				break;
		default : /* There are no other LEDs. */
				break;
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	portENTER_CRITICAL();
	{
		switch( uxLED )
		{
			case 0:	PTHD_PTHD3 = !PTHD_PTHD3;
					break;
			case 1:	PTED_PTED5 = !PTED_PTED5;
					break;
			case 2:	PTGD_PTGD5 = !PTGD_PTGD5;
					break;
			case 3:	PTED_PTED3 = !!PTED_PTED3;
					break;
			default : /* There are no other LEDs. */
					break;
		}
	}
	portEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

unsigned portBASE_TYPE uxParTestGetLED( unsigned portBASE_TYPE uxLED )
{
	/* We ignore the parameter as in this simple example we simply return the
	state of LED3. */
	( void ) uxLED;
	
	return PTED_PTED3;
}


