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

/*-----------------------------------------------------------
 * Normally, a demo application would define ParTest (parallel port test)
 * functions to write to an LED.  In this case, four '*' symbols that are
 * output to the debug printf() port are used to simulate LED outputs.
 *-----------------------------------------------------------*/

/* Standard includes. */
#include <stdio.h>
#include <string.h>

/* Library includes. */
#include "lpc43xx_i2c.h"

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Standard demo include. */
#include "partest.h"

/* The number of LED outputs. */
#define partstMAX_LEDS 4

/* Commands written to the PCA9502. */
#define partstIO_WRITE_COMMAND	( ( unsigned char ) ( 0x0BU << 3U ) )
#define partstIO_DIR_COMMAND	( ( unsigned char ) ( 0x0AU << 3U ) )
#define partstSLAVE_ADDRESS		( ( unsigned char ) ( 0x9AU >> 1U ) )

/* Just defines the length of the queue used to pass toggle commands to the I2C
gatekeeper task. */
#define partstLED_COMMAND_QUEUE_LENGTH	( 6 )
/*-----------------------------------------------------------*/

/*
 * The LEDs are connected to an I2C port expander.  Therefore, writing to an
 * LED takes longer than might be expected if the LED was connected directly
 * to a GPIO pin.  As several tasks, and a timer, toggle LEDs, it is convenient
 * to use a gatekeeper task to ensure access is both mutually exclusive and
 * serialised.  Tasks other than this gatekeeper task must not access the I2C
 * port directly.
 */
static void prvI2CGateKeeperTask( void *pvParameters );

/* The queue used to communicate toggle commands with the I2C gatekeeper
task. */
static QueueHandle_t xI2CCommandQueue = NULL;
/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
unsigned char ucBuffer[ 2 ];
I2C_M_SETUP_Type xI2CMessage;

	/* The LEDs are on an I2C IO expander.  Initialise the I2C interface. */
	I2C_Init( LPC_I2C0, 300000 );
	I2C_Cmd( LPC_I2C0, ENABLE );

	/* GPIO0-GPIO2 to output. */
	ucBuffer[ 0 ] = partstIO_DIR_COMMAND;
	ucBuffer[ 1 ] = 0x0f;
	xI2CMessage.sl_addr7bit = partstSLAVE_ADDRESS;
	xI2CMessage.tx_data = ucBuffer ;
	xI2CMessage.tx_length = sizeof( ucBuffer );
	xI2CMessage.rx_data = NULL;
	xI2CMessage.rx_length = 0;
	xI2CMessage.retransmissions_max = 3;
	I2C_MasterTransferData( LPC_I2C0, &xI2CMessage, I2C_TRANSFER_POLLING );

	/* Create the mutex used to guard access to the I2C bus. */
	xI2CCommandQueue = xQueueCreate( partstLED_COMMAND_QUEUE_LENGTH, sizeof( unsigned char ) );
	configASSERT( xI2CCommandQueue );

	/* Create the I2C gatekeeper task itself. */
	xTaskCreate( prvI2CGateKeeperTask, "I2C", configMINIMAL_STACK_SIZE, ( void * ) NULL, tskIDLE_PRIORITY, NULL );
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned long ulLED )
{
unsigned char ucLED = ( unsigned char ) ulLED;

	/* Only the gatekeeper task will actually access the I2C port, so send the
	toggle request to the gatekeeper task.  A block time of zero is used as
	this function is called by a software timer callback. */
	xQueueSend( xI2CCommandQueue, &ucLED, 0UL );
}
/*-----------------------------------------------------------*/

static void prvI2CGateKeeperTask( void *pvParameters )
{
unsigned char ucBuffer[ 2 ], ucLED;
static unsigned char ucLEDState = 0xffU;
static I2C_M_SETUP_Type xI2CMessage; /* Static so it is not on the stack as this is called from task code. */

	/* Just to remove compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Wait for the next command. */
		xQueueReceive( xI2CCommandQueue, &ucLED, portMAX_DELAY );

		/* Only this task is allowed to touch the I2C port, so there is no need
		for additional mutual exclusion. */
		if( ucLED < partstMAX_LEDS )
		{
			/* Which bit is being manipulated? */
			ucLED = 0x01 << ucLED;

			/* Is the bit currently set or clear? */
			if( ( ucLEDState & ucLED ) == 0U )
			{
				ucLEDState |= ucLED;
			}
			else
			{
				ucLEDState &= ~ucLED;
			}

			ucBuffer[ 0 ] = partstIO_WRITE_COMMAND;
			ucBuffer[ 1 ] = ucLEDState;

			xI2CMessage.sl_addr7bit = partstSLAVE_ADDRESS;
			xI2CMessage.tx_data = ucBuffer ;
			xI2CMessage.tx_length = sizeof( ucBuffer );
			xI2CMessage.rx_data = NULL;
			xI2CMessage.rx_length = 0;
			xI2CMessage.retransmissions_max = 3;
			I2C_MasterTransferData( LPC_I2C0, &xI2CMessage, I2C_TRANSFER_POLLING );
		}
	}
}
/*-----------------------------------------------------------*/

