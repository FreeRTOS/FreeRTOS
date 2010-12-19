/*
    FreeRTOS V6.1.0 - Copyright (C) 2010 Real Time Engineers Ltd.

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

/* Standard includes. */
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo application includes. */
#include "partest.h"
#include "flash.h"

/* ST driver includes. */
#include "stm32l1xx_usart.h"

/* Eval board includes. */
#include "stm32_eval.h"
#include "stm32l152_eval_lcd.h"

#define mainFLASH_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainLCD_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )

#define mainLCD_TASK_STACK_SIZE			( configMINIMAL_STACK_SIZE * 2 )

#define mainQUEUE_LENGTH				( 5 )

#define mainMESSAGE_BUTTON_UP			( 1 )
#define mainMESSAGE_BUTTON_DOWN			( 2 )
#define mainMESSAGE_BUTTON_LEFT			( 3 )
#define mainMESSAGE_BUTTON_RIGHT		( 4 )
#define mainMESSAGE_BUTTON_SEL			( 5 )

/*
 * System configuration is performed prior to main() being called, this function
 * configures the peripherals used by the demo application.
 */
static void prvSetupHardware( void );
static void prvLCDTask( void *pvParameters );
static void vTempTask( void *pv );

static xQueueHandle xLCDQueue = NULL;

typedef struct
{
	char cMessageID;
	long lMessageValue;
} xQueueMessage;

void main( void )
{
	prvSetupHardware();
	
	/* Create the queue used by tasks and interrupts to send strings to the LCD
	task. */
	xLCDQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( xQueueMessage ) );
	
	if( xLCDQueue != NULL )
	{
		xTaskCreate( prvLCDTask, ( signed char * ) "LCD", mainLCD_TASK_STACK_SIZE, NULL, mainLCD_TASK_PRIORITY, NULL );
		xTaskCreate( vTempTask, ( signed char * ) "Temp", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	}
	
	vStartLEDFlashTasks( mainFLASH_TASK_PRIORITY );
	
	vTaskStartScheduler();
	
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvLCDTask( void *pvParameters )
{
xQueueMessage xReceivedMessage;
long lLine = Line1;
const long lFontHeight = (((sFONT *)LCD_GetFont())->Height);
static char cBuffer[ 32 ];

	for( ;; )
	{
		xQueueReceive( xLCDQueue, &xReceivedMessage, portMAX_DELAY );

		if( lLine >= Line9 )
		{
			LCD_Clear( Blue );
			lLine = 0;
		}
		
		switch( xReceivedMessage.cMessageID )
		{
			case mainMESSAGE_BUTTON_UP		:	sprintf( cBuffer, "Button up = %d", xReceivedMessage.lMessageValue );
												break;
			case mainMESSAGE_BUTTON_DOWN	:
												break;
			case mainMESSAGE_BUTTON_LEFT	:
												break;
			case mainMESSAGE_BUTTON_RIGHT	:
												break;
			case mainMESSAGE_BUTTON_SEL		:
												break;
			default							:	sprintf( cBuffer, "Unknown message" );
												break;
		}
		
		LCD_DisplayStringLine( lLine, ( uint8_t * ) cBuffer );
		lLine += lFontHeight;
	}
}
/*-----------------------------------------------------------*/

static void vTempTask( void *pv )
{
long lLastState = pdFALSE;
long lState;
xQueueMessage xMessage;

	for( ;; )
	{
		lState = STM_EVAL_PBGetState( BUTTON_UP );
		if( lState != lLastState )
		{
			xMessage.cMessageID = mainMESSAGE_BUTTON_UP;
			xMessage.lMessageValue = lState;
			lLastState = lState;
			xQueueSend( xLCDQueue, &xMessage, portMAX_DELAY );
			vTaskDelay( 10 );
		}
	}

}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Initialise the LEDs. */
	vParTestInitialise();

	//BUTTON_MODE_EXTI
	/* Initialise the joystick inputs. */
	STM_EVAL_PBInit( BUTTON_UP, BUTTON_MODE_GPIO );
	STM_EVAL_PBInit( BUTTON_DOWN, BUTTON_MODE_GPIO );
	STM_EVAL_PBInit( BUTTON_LEFT, BUTTON_MODE_GPIO );
	STM_EVAL_PBInit( BUTTON_RIGHT, BUTTON_MODE_GPIO );
	STM_EVAL_PBInit( BUTTON_SEL, BUTTON_MODE_GPIO );

#if 0	
USART_InitTypeDef USART_InitStructure;

	USART_InitStructure.USART_BaudRate = 115200;
	USART_InitStructure.USART_WordLength = USART_WordLength_8b;
	USART_InitStructure.USART_StopBits = USART_StopBits_1;
	USART_InitStructure.USART_Parity = USART_Parity_No;
	USART_InitStructure.USART_HardwareFlowControl = USART_HardwareFlowControl_None;
	USART_InitStructure.USART_Mode = USART_Mode_Rx | USART_Mode_Tx;
	
	STM_EVAL_COMInit( COM1, &USART_InitStructure );
#endif
	
	/* Initialize the LCD */
	STM32L152_LCD_Init();
	
	LCD_Clear(Blue);
	LCD_SetBackColor(Blue);
	LCD_SetTextColor(White);
	LCD_DisplayStringLine(Line0, "  www.FreeRTOS.org");
}
/*-----------------------------------------------------------*/

