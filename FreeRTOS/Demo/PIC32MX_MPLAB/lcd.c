/*
    FreeRTOS V8.0.0:rc1 - Copyright (C) 2014 Real Time Engineers Ltd. 
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

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

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

/* peripheral library include */
#include <plib.h>

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
#define lcdVERY_SHORT_DELAY	( 1 )
#define lcdSHORT_DELAY		( 8 / portTICK_RATE_MS )
#define lcdLONG_DELAY		( 15 / portTICK_RATE_MS )

/* LCD specific definitions. */
#define LCD_CLEAR_DISPLAY_CMD			0x01
#define LCD_CURSOR_HOME_CMD				0x02
#define LCD_ENTRY_MODE_CMD				0x04
#define LCD_ENTRY_MODE_INCREASE			0x02
#define LCD_DISPLAY_CTRL_CMD			0x08
#define LCD_DISPLAY_CTRL_DISPLAY_ON		0x04
#define LCD_FUNCTION_SET_CMD			0x20
#define LCD_FUNCTION_SET_8_BITS			0x10
#define LCD_FUNCTION_SET_2_LINES		0x08
#define LCD_FUNCTION_SET_LRG_FONT		0x04
#define LCD_NEW_LINE					0xC0
#define LCD_COMMAND_ADDRESS				0x00
#define LCD_DATA_ADDRESS				0x01

/* The length of the queue used to send messages to the LCD gatekeeper task. */
#define lcdQUEUE_SIZE		3

/*-----------------------------------------------------------*/

/* The queue used to send messages to the LCD task. */
xQueueHandle xLCDQueue;

/* LCD access functions. */
static void prvLCDCommand( char cCommand );
static void prvLCDData( char cChar );

/*-----------------------------------------------------------*/

xQueueHandle xStartLCDTask( void )
{
	/* Create the queue used by the LCD task.  Messages for display on the LCD
	are received via this queue. */
	xLCDQueue = xQueueCreate( lcdQUEUE_SIZE, sizeof( xLCDMessage ));

	/* Start the task that will write to the LCD.  The LCD hardware is
	initialised from within the task itself so delays can be used. */
	xTaskCreate( vLCDTask, "LCD", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY + 1, NULL );

	return xLCDQueue;
}
/*-----------------------------------------------------------*/

static void prvLCDGotoRow( unsigned short usRow )
{
	if(usRow == 0) 
	{
		prvLCDCommand( LCD_CURSOR_HOME_CMD );
	} 
	else 
	{
		prvLCDCommand( LCD_NEW_LINE );
	}
}
/*-----------------------------------------------------------*/

static void prvLCDCommand( char cCommand ) 
{
	PMPSetAddress( LCD_COMMAND_ADDRESS );
	PMPMasterWrite( cCommand );
   	vTaskDelay( lcdSHORT_DELAY );
}
/*-----------------------------------------------------------*/

static void prvLCDData( char cChar )
{
	PMPSetAddress( LCD_DATA_ADDRESS );
	PMPMasterWrite( cChar );
	vTaskDelay( lcdVERY_SHORT_DELAY );
}
/*-----------------------------------------------------------*/

static void prvLCDPutString( char *pcString )
{
	/* Write out each character with appropriate delay between each. */
	while(*pcString)
	{
		prvLCDData(*pcString);
		pcString++;
		vTaskDelay(lcdSHORT_DELAY);
	}
}
/*-----------------------------------------------------------*/

static void prvLCDClear(void)
{
	prvLCDCommand(LCD_CLEAR_DISPLAY_CMD);
}
/*-----------------------------------------------------------*/

static void prvSetupLCD(void)
{
	/* Wait for proper power up. */
	vTaskDelay( lcdLONG_DELAY );
	
	/* Open the PMP port */
	mPMPOpen((PMP_ON | PMP_READ_WRITE_EN | PMP_CS2_CS1_EN |
			  PMP_LATCH_POL_HI | PMP_CS2_POL_HI | PMP_CS1_POL_HI |
			  PMP_WRITE_POL_HI | PMP_READ_POL_HI),
			 (PMP_MODE_MASTER1 | PMP_WAIT_BEG_4 | PMP_WAIT_MID_15 |
			  PMP_WAIT_END_4),
			  PMP_PEN_0, 0);
			 
	/* Wait for the LCD to power up correctly. */
	vTaskDelay( lcdLONG_DELAY );
	vTaskDelay( lcdLONG_DELAY );
	vTaskDelay( lcdLONG_DELAY );

	/* Set up the LCD function. */
	prvLCDCommand( LCD_FUNCTION_SET_CMD | LCD_FUNCTION_SET_8_BITS | LCD_FUNCTION_SET_2_LINES | LCD_FUNCTION_SET_LRG_FONT );
	
	/* Turn the display on. */
	prvLCDCommand( LCD_DISPLAY_CTRL_CMD | LCD_DISPLAY_CTRL_DISPLAY_ON );
	
	/* Clear the display. */
	prvLCDCommand( LCD_CLEAR_DISPLAY_CMD );
	vTaskDelay( lcdLONG_DELAY );	
	
	/* Increase the cursor. */
	prvLCDCommand( LCD_ENTRY_MODE_CMD | LCD_ENTRY_MODE_INCREASE );
	vTaskDelay( lcdLONG_DELAY );		  	
	vTaskDelay( lcdLONG_DELAY );		  	
	vTaskDelay( lcdLONG_DELAY );
}
/*-----------------------------------------------------------*/

static void vLCDTask(void *pvParameters)
{
xLCDMessage xMessage;
unsigned short usRow = 0;

	/* Initialise the hardware.  This uses delays so must not be called prior
	to the scheduler being started. */
	prvSetupLCD();

	/* Welcome message. */
	prvLCDPutString( "www.FreeRTOS.org" );

	for(;;)
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




