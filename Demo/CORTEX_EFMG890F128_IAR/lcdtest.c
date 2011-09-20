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

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "lcdtest.h"

#define lcdSHORT_DELAY		( 60 / portTICK_RATE_MS )
#define lcdQUARTER_SECOND	( 250 / portTICK_RATE_MS )
#define lcdONE_SECOND		( 1000 / portTICK_RATE_MS )

void vLCDTask( void *pvParameters )
{
long x;
LCD_TypeDef *xLCD = LCD;
char *pcScrollText = "FreeRTOS Energy Micro       ";

	/* Loop through various different displays. */
	for( ;; )
	{
		/* Start by scrolling some text. */
		LCD_ScrollText( xLCD, pcScrollText );
		LCD_AllOff( xLCD );

		/* Count down from 100 on the number section of the LCD display. */
		for( x = 100; x > 0; x--)
		{
			LCD_Number( xLCD, x );
			vTaskDelay( 10 );
		}
		LCD_NumberOff( xLCD );

		/* Turn on gecko and EFM32 symbol. */
		LCD_Symbol( xLCD, LCD_SYMBOL_GECKO, 1 );
		LCD_Symbol( xLCD, LCD_SYMBOL_EFM32, 1 );
		LCD_Write( xLCD, " Gecko " );
		vTaskDelay( lcdONE_SECOND );

		LCD_AllOn( xLCD);
		vTaskDelay( lcdONE_SECOND );

		LCD_AllOff( xLCD);
		LCD_Write( xLCD, "OOOOOOO" );
		vTaskDelay( lcdSHORT_DELAY );
		LCD_Write( xLCD, "XXXXXXX" );
		vTaskDelay( lcdSHORT_DELAY );
		LCD_Write( xLCD, "+++++++" );
		vTaskDelay( lcdSHORT_DELAY );
		LCD_Write( xLCD, "@@@@@@@" );
		vTaskDelay( lcdSHORT_DELAY );
		LCD_Write( xLCD, "ENERGY " );
		vTaskDelay( lcdQUARTER_SECOND );
		LCD_Write( xLCD, "@@ERGY " );
		vTaskDelay( lcdSHORT_DELAY );
		LCD_Write( xLCD, " @@RGY " );
		vTaskDelay( lcdSHORT_DELAY );
		LCD_Write( xLCD, " M@@GY " );
		vTaskDelay( lcdSHORT_DELAY );
		LCD_Write( xLCD, " MI@@Y " );
		vTaskDelay( lcdSHORT_DELAY );
		LCD_Write( xLCD, " MIC@@ " );
		vTaskDelay( lcdSHORT_DELAY );
		LCD_Write( xLCD, " MICR@@" );
		vTaskDelay( lcdSHORT_DELAY );
		LCD_Write( xLCD, " MICRO@" );
		vTaskDelay( lcdSHORT_DELAY );
		LCD_Write( xLCD, " MICRO " );
		vTaskDelay( lcdQUARTER_SECOND );
		LCD_Write( xLCD, "-EFM32-" );
		vTaskDelay( lcdQUARTER_SECOND );
	}
}