/*
    FreeRTOS V9.0.1 - Copyright (C) 2017 Real Time Engineers Ltd.
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

