/*
	FreeRTOS.org V5.0.3 - Copyright (C) 2003-2008 Richard Barry.

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
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and 
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety 
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting, 
	licensing and training services.
*/

/* 
Changes from V2.0.0

	+ Use scheduler suspends in place of critical sections.
*/

#include "FreeRTOS.h"
#include "task.h"
#include "partest.h"

/*-----------------------------------------------------------
 * Simple parallel port IO routines for the FED 40pin demo board.
 * The four LED's are connected to D4 to D7.
 *-----------------------------------------------------------*/

#define partstBIT_AS_OUTPUT			( ( unsigned portSHORT ) 0 )
#define partstSET_OUTPUT			( ( unsigned portSHORT ) 1 )
#define partstCLEAR_OUTPUT			( ( unsigned portSHORT ) 0 )

#define partstENABLE_GENERAL_IO		( ( unsigned portCHAR ) 7 )

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* Set the top four bits of port D to output. */
	TRISDbits.TRISD7 = partstBIT_AS_OUTPUT;
	TRISDbits.TRISD6 = partstBIT_AS_OUTPUT;
	TRISDbits.TRISD5 = partstBIT_AS_OUTPUT;
	TRISDbits.TRISD4 = partstBIT_AS_OUTPUT;

	/* Start with all bits off. */
	PORTDbits.RD7 = partstCLEAR_OUTPUT;
	PORTDbits.RD6 = partstCLEAR_OUTPUT;
	PORTDbits.RD5 = partstCLEAR_OUTPUT;
	PORTDbits.RD4 = partstCLEAR_OUTPUT;

	/* Enable the driver. */
	ADCON1 = partstENABLE_GENERAL_IO;
	TRISEbits.TRISE2 = partstBIT_AS_OUTPUT;
	PORTEbits.RE2 = partstSET_OUTPUT;	
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, portBASE_TYPE xValue )
{
	/* We are only using the top nibble, so LED 0 corresponds to bit 4. */	
	vTaskSuspendAll();
	{
		switch( uxLED )
		{
			case 3	:	PORTDbits.RD7 = ( portSHORT ) xValue;
						break;
			case 2	:	PORTDbits.RD6 = ( portSHORT ) xValue;
						break;
			case 1	:	PORTDbits.RD5 = ( portSHORT ) xValue;
						break;
			case 0	:	PORTDbits.RD4 = ( portSHORT ) xValue;
						break;
			default	:	/* There are only 4 LED's. */
						break;
		}
	}
	xTaskResumeAll();
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	/* We are only using the top nibble, so LED 0 corresponds to bit 4. */	
	vTaskSuspendAll();
	{
		switch( uxLED )
		{
			case 3	:	PORTDbits.RD7 = !( PORTDbits.RD7 );
						break;
			case 2	:	PORTDbits.RD6 = !( PORTDbits.RD6 );
						break;
			case 1	:	PORTDbits.RD5 = !( PORTDbits.RD5 );
						break;
			case 0	:	PORTDbits.RD4 = !( PORTDbits.RD4 );
						break;
			default	:	/* There are only 4 LED's. */
						break;
		}
	}
	xTaskResumeAll();
}



