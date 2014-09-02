/*
    FreeRTOS V8.1.2 - Copyright (C) 2014 Real Time Engineers Ltd. 
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "lcdtest.h"

#define lcdSHORT_DELAY		( 60 / portTICK_PERIOD_MS )
#define lcdQUARTER_SECOND	( 250 / portTICK_PERIOD_MS )
#define lcdONE_SECOND		( 1000 / portTICK_PERIOD_MS )

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