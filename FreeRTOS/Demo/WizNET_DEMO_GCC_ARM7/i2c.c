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


/* Standard includes. */
#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "queue.h"
#include "semphr.h"

/* Application includes. */
#include "i2c.h"

/*-----------------------------------------------------------*/

/* Constants to setup the microcontroller IO. */
#define mainSDA_ENABLE			( ( unsigned long ) 0x0040 )
#define mainSCL_ENABLE			( ( unsigned long ) 0x0010 )

/* Bit definitions within the I2CONCLR register. */
#define i2cSTA_BIT				( ( unsigned char ) 0x20 )
#define i2cSI_BIT				( ( unsigned char ) 0x08 )
#define i2cSTO_BIT				( ( unsigned char ) 0x10 )

/* Constants required to setup the VIC. */
#define i2cI2C_VIC_CHANNEL		( ( unsigned long ) 0x0009 )
#define i2cI2C_VIC_CHANNEL_BIT	( ( unsigned long ) 0x0200 )
#define i2cI2C_VIC_ENABLE		( ( unsigned long ) 0x0020 )

/* Misc constants. */
#define i2cNO_BLOCK				( ( TickType_t ) 0 )
#define i2cQUEUE_LENGTH			( ( unsigned char ) 5 )
#define i2cEXTRA_MESSAGES		( ( unsigned char ) 2 )
#define i2cREAD_TX_LEN			( ( unsigned long ) 2 )
#define i2cACTIVE_MASTER_MODE	( ( unsigned char ) 0x40 )
#define i2cTIMERL				( 200 )
#define i2cTIMERH				( 200 )

/* Array of message definitions.  See the header file for more information
on the structure members.  There are two more places in the queue than as
defined by i2cQUEUE_LENGTH.  This is to ensure that there is always a free
message available - one can be in the process of being transmitted and one
can be left free. */
static xI2CMessage xTxMessages[ i2cQUEUE_LENGTH + i2cEXTRA_MESSAGES ];

/* Function in the ARM part of the code used to create the queues. */
extern void vI2CISRCreateQueues( unsigned portBASE_TYPE uxQueueLength, QueueHandle_t *pxTxMessages, unsigned long **ppulBusFree );

/* Index to the next free message in the xTxMessages array. */
unsigned long ulNextFreeMessage = ( unsigned long ) 0;

/* Queue of messages that are waiting transmission. */
static QueueHandle_t xMessagesForTx;

/* Flag to indicate the state of the I2C ISR state machine. */
static unsigned long *pulBusFree;

/*-----------------------------------------------------------*/
void i2cMessage( const unsigned char * const pucMessage, long lMessageLength, unsigned char ucSlaveAddress, unsigned short usBufferAddress, unsigned long ulDirection, SemaphoreHandle_t xMessageCompleteSemaphore, TickType_t xBlockTime )
{
extern volatile xI2CMessage *pxCurrentMessage;
xI2CMessage *pxNextFreeMessage;
signed portBASE_TYPE xReturn;

	portENTER_CRITICAL();
	{
		/* This message is guaranteed to be free as there are two more messages
		than spaces in the queue allowing for one message to be in process of
		being transmitted and one to be left free. */
		pxNextFreeMessage = &( xTxMessages[ ulNextFreeMessage ] );

		/* Fill the message with the data to be sent. */

		/* Pointer to the actual data.  Only a pointer is stored (i.e. the 
		actual data is not copied, so the data being pointed to must still
		be valid when the message eventually gets sent (it may be queued for
		a while. */
		pxNextFreeMessage->pucBuffer = ( unsigned char * ) pucMessage;		

		/* This is the address of the I2C device we are going to transmit this
		message to. */
		pxNextFreeMessage->ucSlaveAddress = ucSlaveAddress | ( unsigned char ) ulDirection;

		/* A semaphore can be used to allow the I2C ISR to indicate that the
		message has been sent.  This can be NULL if you don't want to wait for
		the message transmission to complete. */
		pxNextFreeMessage->xMessageCompleteSemaphore = xMessageCompleteSemaphore;

		/* How many bytes are to be sent? */
		pxNextFreeMessage->lMessageLength = lMessageLength;

		/* The address within the WIZnet device to which the data will be 
		written.  This could be the address of a register, or alternatively
		a location within the WIZnet Tx buffer. */
		pxNextFreeMessage->ucBufferAddressLowByte = ( unsigned char ) ( usBufferAddress & 0xff );

		/* Second byte of the address. */
		usBufferAddress >>= 8;
		pxNextFreeMessage->ucBufferAddressHighByte = ( unsigned char ) ( usBufferAddress & 0xff );

		/* Increment to the next message in the array - with a wrap around check. */
		ulNextFreeMessage++;
		if( ulNextFreeMessage >= ( i2cQUEUE_LENGTH + i2cEXTRA_MESSAGES ) )
		{
			ulNextFreeMessage = ( unsigned long ) 0;
		}

		/* Is the I2C interrupt in the middle of transmitting a message? */
		if( *pulBusFree == ( unsigned long ) pdTRUE )
		{
			/* No message is currently being sent or queued to be sent.  We
			can start the ISR sending this message immediately. */
			pxCurrentMessage = pxNextFreeMessage;

			I2C_I2CONCLR = i2cSI_BIT;	
			I2C_I2CONSET = i2cSTA_BIT;
			
			*pulBusFree = ( unsigned long ) pdFALSE;
		}
		else
		{
			/* The I2C interrupt routine is mid sending a message.  Queue
			this message ready to be sent. */
			xReturn = xQueueSend( xMessagesForTx, &pxNextFreeMessage, xBlockTime );

			/* We may have blocked while trying to queue the message.  If this
			was the case then the interrupt would have been enabled and we may
			now find that the I2C interrupt routine is no longer sending a
			message. */
			if( ( *pulBusFree == ( unsigned long ) pdTRUE ) && ( xReturn == pdPASS ) )
			{
				/* Get the next message in the queue (this should be the 
				message we just posted) and start off the transmission
				again. */
				xQueueReceive( xMessagesForTx, &pxNextFreeMessage, i2cNO_BLOCK );
				pxCurrentMessage = pxNextFreeMessage;

				I2C_I2CONCLR = i2cSI_BIT;	
				I2C_I2CONSET = i2cSTA_BIT;
				
				*pulBusFree = ( unsigned long ) pdFALSE;
			}
		}
	}
	portEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

void i2cInit( void )
{
extern void ( vI2C_ISR_Wrapper )( void );

	/* Create the queue used to send messages to the ISR. */
	vI2CISRCreateQueues( i2cQUEUE_LENGTH, &xMessagesForTx, &pulBusFree );

	/* Configure the I2C hardware. */

	I2C_I2CONCLR = 0xff; 

	PCB_PINSEL0 |= mainSDA_ENABLE;
	PCB_PINSEL0 |= mainSCL_ENABLE;

	I2C_I2SCLL = i2cTIMERL;
	I2C_I2SCLH = i2cTIMERH;
	I2C_I2CONSET = i2cACTIVE_MASTER_MODE;

	portENTER_CRITICAL();
	{
		/* Setup the VIC for the i2c interrupt. */
		VICIntSelect &= ~( i2cI2C_VIC_CHANNEL_BIT );
		VICIntEnable |= i2cI2C_VIC_CHANNEL_BIT;
		VICVectAddr2 = ( long ) vI2C_ISR_Wrapper;

		VICVectCntl2 = i2cI2C_VIC_CHANNEL | i2cI2C_VIC_ENABLE;
	}
	portEXIT_CRITICAL();
}

