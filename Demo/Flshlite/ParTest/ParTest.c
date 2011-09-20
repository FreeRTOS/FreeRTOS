/*
    FreeRTOS V7.0.2 - Copyright (C) 2011 Real Time Engineers Ltd.
	

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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

/*
Changes from V1.01:

	+ Types used updated.
	+ Add vParTestToggleLED();

Changes from V2.0.0

	+ Use scheduler suspends in place of critical sections.
*/


#include "FreeRTOS.h"
#include "task.h"
#include "partest.h"

#define partstALL_OUTPUTS_OFF			( ( unsigned short) 0x00 )
#define partstMAX_OUTPUT_LED			( ( unsigned char ) 7 )
#define partstPORT_F_ADDR				( ( unsigned short ) 0x605 )
#define partstPORT_DIRECTION_REG		( ( unsigned short ) 0x606 )
#define partstPORT_F_DIR_BIT			( ( unsigned short ) 0x20 )

/*lint -e956 File scope parameters okay here. */
static volatile unsigned char ucCurrentOutputValue = partstALL_OUTPUTS_OFF;
/*lint +e956 */

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

void vParTestInitialise( void )
{
unsigned short usInput;

	ucCurrentOutputValue = partstALL_OUTPUTS_OFF;

	/* Set the direction to output for port F. */
	usInput = portINPUT_BYTE( partstPORT_DIRECTION_REG );
	usInput |= partstPORT_F_DIR_BIT;
	portOUTPUT_BYTE( partstPORT_DIRECTION_REG, usInput );

	/* Start with all outputs off. */
	portOUTPUT_BYTE( partstPORT_F_ADDR, partstALL_OUTPUTS_OFF );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, portBASE_TYPE xValue )
{
unsigned char ucBit = ( unsigned char ) 1;

	if( uxLED <= partstMAX_OUTPUT_LED )
	{
		ucBit <<= uxLED;
	}	

	vTaskSuspendAll();
	{
		if( xValue == pdTRUE )
		{
			ucBit ^= ( unsigned char ) 0xff;
			ucCurrentOutputValue &= ucBit;
		}
		else
		{
			ucCurrentOutputValue |= ucBit;
		}

		portOUTPUT_BYTE( partstPORT_F_ADDR, ( unsigned ) ucCurrentOutputValue );
	}
	xTaskResumeAll();
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned char ucBit;

	if( uxLED <= partstMAX_OUTPUT_LED )
	{
		ucBit = ( ( unsigned char ) 1 ) << uxLED;

		vTaskSuspendAll();
		{
			if( ucCurrentOutputValue & ucBit )
			{
				ucCurrentOutputValue &= ~ucBit;
			}
			else
			{
				ucCurrentOutputValue |= ucBit;
			}

			portOUTPUT_BYTE( partstPORT_F_ADDR, ( unsigned ) ucCurrentOutputValue );
		}
		xTaskResumeAll();			
	}
}

