/*
    FreeRTOS V6.0.0 - Copyright (C) 2009 Real Time Engineers Ltd.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it    under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation and modified by the FreeRTOS exception.
    **NOTE** The exception to the GPL is included to allow you to distribute a
    combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    Alternative commercial license and support terms are also available upon
    request.  See the licensing section of http://www.FreeRTOS.org for full
    license details.

    FreeRTOS is distributed in the hope that it will be useful,    but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details.

    You should have received a copy of the GNU General Public License along
    with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
    Temple Place, Suite 330, Boston, MA  02111-1307  USA.


    ***************************************************************************
    *                                                                         *
    * The FreeRTOS eBook and reference manual are available to purchase for a *
    * small fee. Help yourself get started quickly while also helping the     *
    * FreeRTOS project! See http://www.FreeRTOS.org/Documentation for details *
    *                                                                         *
    ***************************************************************************

    1 tab == 4 spaces!

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

#define partstBIT_AS_OUTPUT			( ( unsigned short ) 0 )
#define partstSET_OUTPUT			( ( unsigned short ) 1 )
#define partstCLEAR_OUTPUT			( ( unsigned short ) 0 )

#define partstENABLE_GENERAL_IO		( ( unsigned char ) 7 )

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
			case 3	:	PORTDbits.RD7 = ( short ) xValue;
						break;
			case 2	:	PORTDbits.RD6 = ( short ) xValue;
						break;
			case 1	:	PORTDbits.RD5 = ( short ) xValue;
						break;
			case 0	:	PORTDbits.RD4 = ( short ) xValue;
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



