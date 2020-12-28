/*
 * FreeRTOS V202012.00
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

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo includes. */
#include "lcd.h"

/*
 * The LCD is written to by more than one task so is controlled by this
 * 'gatekeeper' task.  This is the only task that is actually permitted to
 * access the LCD directly.  Other tasks wanting to display a message send
 * the message to the gatekeeper.
 */
static void vLCDTask( void *pvParameters );

/*
 * Setup the peripherals required to communicate with the LCD.
 */
static void prvSetupLCD( void );

/* 
 * Move to the first (0) or second (1) row of the LCD. 
 */
static void prvLCDGotoRow( unsigned short usRow );

/* 
 * Write a string of text to the LCD. 
 */
static void prvLCDPutString( char *pcString );

/* 
 * Clear the LCD. 
 */
static void prvLCDClear( void );

/*-----------------------------------------------------------*/

/* Brief delay to permit the LCD to catch up with commands. */
#define lcdSHORT_DELAY		3

/* SFR that seems to be missing from the standard header files. */
#define PMAEN				*( ( unsigned short * ) 0x60c )

/* LCD commands. */
#define lcdDEFAULT_FUNCTION	0x3c
#define lcdDISPLAY_CONTROL	0x0c
#define lcdCLEAR_DISPLAY	0x01
#define lcdENTRY_MODE		0x06

/* The length of the queue used to send messages to the LCD gatekeeper task. */
#define lcdQUEUE_SIZE		3
/*-----------------------------------------------------------*/

/* The queue used to send messages to the LCD task. */
QueueHandle_t xLCDQueue;


/*-----------------------------------------------------------*/

QueueHandle_t xStartLCDTask( void )
{
	/* Create the queue used by the LCD task.  Messages for display on the LCD
	are received via this queue. */
	xLCDQueue = xQueueCreate( lcdQUEUE_SIZE, sizeof( xLCDMessage ) );

	/* Start the task that will write to the LCD.  The LCD hardware is
	initialised from within the task itself so delays can be used. */
	xTaskCreate( vLCDTask, "LCD", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY + 1, NULL );

	return xLCDQueue;
}
/*-----------------------------------------------------------*/

static void prvLCDGotoRow( unsigned short usRow )
{
	if( usRow == 0 )
	{
		PMADDR = 0x0000;
		PMDIN1 = 0x02;
	}
	else
	{
		PMADDR = 0x0000;
		PMDIN1 = 0xc0;
	}

	vTaskDelay( lcdSHORT_DELAY );
}
/*-----------------------------------------------------------*/

static void prvLCDPutString( char *pcString )
{
	/* Write out each character with appropriate delay between each. */
	while( *pcString )
	{
		PMADDR = 0x0001;
		PMDIN1 = *pcString;
		pcString++;
		vTaskDelay( lcdSHORT_DELAY );
	}
}
/*-----------------------------------------------------------*/

static void prvLCDClear( void )
{
	/* Clear the display. */
	PMADDR = 0x0000;
	PMDIN1 = lcdCLEAR_DISPLAY;
	vTaskDelay( lcdSHORT_DELAY );	
}
/*-----------------------------------------------------------*/

static void prvSetupLCD( void )
{
	/* Setup the PMP. */
	PMCON = 0x83BF;
	PMMODE = 0x3FF;
	PMAEN = 1;
	PMADDR = 0x0000;
	vTaskDelay( lcdSHORT_DELAY );

	/* Set the default function. */
	PMDIN1 = lcdDEFAULT_FUNCTION;
	vTaskDelay( lcdSHORT_DELAY );

	/* Set the display control. */
	PMDIN1 = lcdDISPLAY_CONTROL;
	vTaskDelay( lcdSHORT_DELAY );

	/* Clear the display. */
	PMDIN1 = lcdCLEAR_DISPLAY;
	vTaskDelay( lcdSHORT_DELAY );

	/* Set the entry mode. */
	PMDIN1 = lcdENTRY_MODE;
	vTaskDelay( lcdSHORT_DELAY );
}
/*-----------------------------------------------------------*/

static void vLCDTask( void *pvParameters )
{
xLCDMessage xMessage;
unsigned short usRow = 0;

	/* Remove compiler warnigns. */
	( void ) pvParameters;

	/* Initialise the hardware.  This uses delays so must not be called prior
	to the scheduler being started. */
	prvSetupLCD();

	/* Welcome message. */
	prvLCDPutString( "www.FreeRTOS.org" );

	for( ;; )
	{
		/* Wait for a message to arrive that requires displaying. */
		while( xQueueReceive( xLCDQueue, &xMessage, portMAX_DELAY ) != pdPASS );

		/* Clear the current display value. */
		prvLCDClear();

		/* Switch rows each time so we can see that the display is still being
		updated. */
		prvLCDGotoRow( usRow & 0x01 );
		usRow++;
		prvLCDPutString( xMessage.pcMessage );

		/* Delay the requested amount of time to ensure the text just written 
		to the LCD is not overwritten. */
		vTaskDelay( xMessage.xMinDisplayTime );		
	}
}




