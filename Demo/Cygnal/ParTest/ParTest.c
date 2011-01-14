/*
    FreeRTOS V6.1.1 - Copyright (C) 2011 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS books - available as PDF or paperback  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public 
    License and the FreeRTOS license exception along with FreeRTOS; if not it 
    can be viewed here: http://www.freertos.org/a00114.html and also obtained 
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/
#include <c8051f120.h>

#include "FreeRTOS.h"
#include "task.h"
#include "partest.h"

#define partstPUSH_PULL			( ( unsigned char ) 0xff )
#define partstALL_OUTPUTS_OFF	( ( unsigned char ) 0xff )

/* LED to output is dependent on how the LED's are wired. */
#define partstOUTPUT_0			( ( unsigned char ) 0x02 )
#define partstOUTPUT_1			( ( unsigned char ) 0x08 )
#define partstOUTPUT_2			( ( unsigned char ) 0x20 )
#define partstOUTPUT_3			( ( unsigned char ) 0x01 )
#define partstOUTPUT_4			( ( unsigned char ) 0x04 )
#define partstOUTPUT_5			( ( unsigned char ) 0x10 )
#define partstOUTPUT_6			( ( unsigned char ) 0x40 )
#define partstOUTPUT_7			( ( unsigned char ) 0x80 )

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

void vParTestInitialise( void )
{
unsigned char ucOriginalSFRPage;

	/* Remember the SFR page before it is changed so it can get set back
	before the function exits. */
	ucOriginalSFRPage = SFRPAGE;

	/* Setup the SFR page to access the config SFR's. */
	SFRPAGE = CONFIG_PAGE;

	/* Set the on board LED to push pull. */
	P3MDOUT |= partstPUSH_PULL;

	/* Return the SFR page. */
	SFRPAGE = ucOriginalSFRPage;

	P3 = partstALL_OUTPUTS_OFF;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, portBASE_TYPE xValue )
{
portBASE_TYPE xError = pdFALSE;

	vTaskSuspendAll();
	{
		if( xValue == pdFALSE )
		{
			switch( uxLED )
			{
				case 0	:	P3 |= partstOUTPUT_0;
							break;
				case 1	:	P3 |= partstOUTPUT_1;
							break;
				case 2	:	P3 |= partstOUTPUT_2;
							break;
				case 3	:	P3 |= partstOUTPUT_3;
							break;
				case 4	:	P3 |= partstOUTPUT_4;
							break;
				case 5	:	P3 |= partstOUTPUT_5;
							break;
				case 6	:	P3 |= partstOUTPUT_6;
							break;
				case 7	:	P3 |= partstOUTPUT_7;
							break;
				default	:	/* There are no other LED's wired in. */
							xError = pdTRUE;
							break;
			}
		}
		else
		{
			switch( uxLED )
			{
				case 0	:	P3 &= ~partstOUTPUT_0;
							break;
				case 1	:	P3 &= ~partstOUTPUT_1;
							break;
				case 2	:	P3 &= ~partstOUTPUT_2;
							break;
				case 3	:	P3 &= ~partstOUTPUT_3;
							break;
				case 4	:	P3 &= ~partstOUTPUT_4;
							break;
				case 5	:	P3 &= ~partstOUTPUT_5;
							break;
				case 6	:	P3 &= ~partstOUTPUT_6;
							break;
				case 7	:	P3 &= ~partstOUTPUT_7;
							break;
				default	:	/* There are no other LED's wired in. */
							break;
			}
		}
	}
	xTaskResumeAll();
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned char ucBit;
portBASE_TYPE xError = pdFALSE;

	vTaskSuspendAll();
	{
		switch( uxLED )
		{
			case 0	:	ucBit = partstOUTPUT_0;
						break;
			case 1	:	ucBit = partstOUTPUT_1;
						break;
			case 2	:	ucBit = partstOUTPUT_2;
						break;
			case 3	:	ucBit = partstOUTPUT_3;
						break;
			case 4	:	ucBit = partstOUTPUT_4;
						break;
			case 5	:	ucBit = partstOUTPUT_5;
						break;
			case 6	:	ucBit = partstOUTPUT_6;
						break;
			case 7	:	ucBit = partstOUTPUT_7;
						break;
			default	:	/* There are no other LED's wired in. */
						xError = pdTRUE;
						break;
		}

		if( xError != pdTRUE )
		{
			if( P3 & ucBit )
			{
				P3 &= ~ucBit;
			}
			else
			{
				P3 |= ucBit;
			}
		}
	}
	xTaskResumeAll();
}


