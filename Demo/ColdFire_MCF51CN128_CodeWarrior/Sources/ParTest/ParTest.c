/*
    FreeRTOS V6.0.2 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
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


