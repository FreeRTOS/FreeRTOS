/*
    FreeRTOS V9.0.0rc1 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

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