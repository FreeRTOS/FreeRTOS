/*
 * FreeRTOS Kernel V10.3.1
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
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Application includes. */
#include "i2c.h"

/*-----------------------------------------------------------*/

/* Bit definitions within the I2CONCLR register. */
#define i2cSTA_BIT		( ( unsigned char ) 0x20 )
#define i2cSI_BIT		( ( unsigned char ) 0x08 )
#define i2cSTO_BIT		( ( unsigned char ) 0x10 )
#define i2cAA_BIT		( ( unsigned char ) 0x04 )

/* Status codes for the I2STAT register. */
#define i2cSTATUS_START_TXED			( 0x08 )
#define i2cSTATUS_REP_START_TXED		( 0x10 )
#define i2cSTATUS_TX_ADDR_ACKED			( 0x18 )
#define i2cSTATUS_DATA_TXED				( 0x28 )
#define i2cSTATUS_RX_ADDR_ACKED			( 0x40 )
#define i2cSTATUS_DATA_RXED				( 0x50 )
#define i2cSTATUS_LAST_BYTE_RXED		( 0x58 )

/* Constants for operation of the VIC. */
#define i2cCLEAR_VIC_INTERRUPT	( 0 )

/* Misc constants. */
#define i2cJUST_ONE_BYTE_TO_RX	( 1 )
#define i2cBUFFER_ADDRESS_BYTES	( 2 )

/* End the current transmission and free the bus. */
#define i2cEND_TRANSMISSION( lStatus )					\
{														\
	I2C_I2CONCLR = i2cAA_BIT;							\
	I2C_I2CONSET = i2cSTO_BIT;							\
	eCurrentState = eSentStart;							\
	lTransactionCompleted = lStatus;					\
}
/*-----------------------------------------------------------*/

/* Valid i2c communication states. */
typedef enum
{
	eSentStart,				/*<< Last action was the transmission of a start bit. */
	eSentAddressForWrite,	/*<< Last action was the transmission of the slave address we are to write to. */
	eSentAddressForRead,	/*<< Last action was the transmission of the slave address we are to read from. */
	eSentData,				/*<< Last action was the transmission of a data byte. */
	eReceiveData			/*<< We expected data to be received. */
} I2C_STATE;
/*-----------------------------------------------------------*/

/* Points to the message currently being sent. */
volatile xI2CMessage *pxCurrentMessage = NULL;	

/* The queue of messages waiting to be transmitted. */
static QueueHandle_t xMessagesForTx;

/* Flag used to indicate whether or not the ISR is amid sending a message. */
unsigned long ulBusFree = ( unsigned long ) pdTRUE;

/* Setting this to true will cause the TCP task to think a message is 
complete and thus restart.  It can therefore be used under error states
to force a restart. */
volatile long lTransactionCompleted = pdTRUE;

/*-----------------------------------------------------------*/

void vI2CISRCreateQueues( unsigned portBASE_TYPE uxQueueLength, QueueHandle_t *pxTxMessages, unsigned long **ppulBusFree )
{
	/* Create the queues used to hold Rx and Tx characters. */
	xMessagesForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( xI2CMessage * ) );

	/* Pass back a reference to the queue and bus free flag so the I2C API file 
	can post messages. */
	*pxTxMessages = xMessagesForTx;
	*ppulBusFree = &ulBusFree;
}
/*-----------------------------------------------------------*/

/* The ISR entry point. */
void vI2C_ISR_Wrapper( void ) __attribute__ (( naked ));

/* The ISR function to perform the actual work.  This must be a separate
function from the wrapper to ensure the correct stack frame is set up. */
void vI2C_ISR_Handler( void );

/*-----------------------------------------------------------*/

void vI2C_ISR_Wrapper( void )
{
	/* Save the context of the interrupted task. */
	portSAVE_CONTEXT();

	/* Call the handler to perform the actual work.  This must be a
	separate function to ensure the correct stack frame is set up. */
	vI2C_ISR_Handler();

	/* Restore the context of whichever task is going to run next. */
	portRESTORE_CONTEXT();
}
/*-----------------------------------------------------------*/

void vI2C_ISR_Handler( void )
{
/* Holds the current transmission state. */							
static I2C_STATE eCurrentState = eSentStart;
static long lMessageIndex = -i2cBUFFER_ADDRESS_BYTES; /* There are two address bytes to send prior to the data. */
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
long lBytesLeft;

	/* The action taken for this interrupt depends on our current state. */
	switch( eCurrentState )
	{
		case eSentStart	:	

				/* We sent a start bit, if it was successful we can
				go on to send the slave address. */
				if( ( I2C_I2STAT == i2cSTATUS_START_TXED ) || ( I2C_I2STAT == i2cSTATUS_REP_START_TXED ) )
				{
					/* Send the slave address. */
					I2C_I2DAT = pxCurrentMessage->ucSlaveAddress;

					if( pxCurrentMessage->ucSlaveAddress & i2cREAD )
					{
						/* We are then going to read bytes back from the 
						slave. */
						eCurrentState = eSentAddressForRead;
						
						/* Initialise the buffer index so the first byte goes
						into the first buffer position. */
						lMessageIndex = 0;
					}
					else
					{
						/* We are then going to write some data to the slave. */
						eCurrentState = eSentAddressForWrite;

						/* When writing bytes we first have to send the two
						byte buffer address so lMessageIndex is set negative,
						when it reaches 0 it is time to send the actual data. */
						lMessageIndex = -i2cBUFFER_ADDRESS_BYTES;
					}
				}
				else
				{
					/* Could not send the start bit so give up. */
					i2cEND_TRANSMISSION( pdFAIL );					
				}

				I2C_I2CONCLR = i2cSTA_BIT;				

				break;

		case eSentAddressForWrite :

				/* We sent the address of the slave we are going to write to.
				If this was acknowledged we	can go on to send the data. */
				if( I2C_I2STAT == i2cSTATUS_TX_ADDR_ACKED )
				{
					/* Start the first byte transmitting which is the 
					first byte of the buffer address to which the data will 
					be sent. */
					I2C_I2DAT = pxCurrentMessage->ucBufferAddressHighByte;
					eCurrentState = eSentData;
				}
				else
				{
					/* Address was not acknowledged so give up. */
					i2cEND_TRANSMISSION( pdFAIL );					
				}					
				break;

		case eSentAddressForRead :

				/* We sent the address of the slave we are going to read from.
				If this was acknowledged we can go on to read the data. */
				if( I2C_I2STAT == i2cSTATUS_RX_ADDR_ACKED )
				{
					eCurrentState = eReceiveData;
					if( pxCurrentMessage->lMessageLength > i2cJUST_ONE_BYTE_TO_RX )
					{
						/* Don't ack the last byte of the message. */
						I2C_I2CONSET = i2cAA_BIT;
					}					
				}
				else
				{
					/* Something unexpected happened - give up. */
					i2cEND_TRANSMISSION( pdFAIL );					
				}
				break;

		case eReceiveData :
				
				/* We have just received a byte from the slave. */
				if( ( I2C_I2STAT == i2cSTATUS_DATA_RXED ) || ( I2C_I2STAT == i2cSTATUS_LAST_BYTE_RXED ) )
				{
					/* Buffer the byte just received then increment the index 
					so it points to the next free space. */
					pxCurrentMessage->pucBuffer[ lMessageIndex ] = I2C_I2DAT;
					lMessageIndex++;

					/* How many more bytes are we expecting to receive? */
					lBytesLeft = pxCurrentMessage->lMessageLength - lMessageIndex;
					if( lBytesLeft == ( unsigned long ) 0 )
					{
						/* This was the last byte in the message. */
						i2cEND_TRANSMISSION( pdPASS );

						/* If xMessageCompleteSemaphore is not null then there
						is a task waiting for this message to complete and we
						must 'give' the semaphore so the task is woken.*/
						if( pxCurrentMessage->xMessageCompleteSemaphore )
						{
							xSemaphoreGiveFromISR( pxCurrentMessage->xMessageCompleteSemaphore, &xHigherPriorityTaskWoken );
						}

						/* Are there any other messages to transact? */
						if( xQueueReceiveFromISR( xMessagesForTx, &pxCurrentMessage, &xHigherPriorityTaskWoken ) == pdTRUE )
						{
							/* Start the next message - which was
							retrieved from the queue. */
							I2C_I2CONSET = i2cSTA_BIT;
						}
						else
						{
							/* No more messages were found to be waiting for
							transaction so the bus is free. */
							ulBusFree = ( unsigned long ) pdTRUE;			
						}						
					}
					else
					{
						/* There are more bytes to receive but don't ack the 
						last byte. */
						if( lBytesLeft <= i2cJUST_ONE_BYTE_TO_RX )
						{
							I2C_I2CONCLR = i2cAA_BIT;
						}							 
					}
				}
				else
				{
					/* Something unexpected happened - give up. */
					i2cEND_TRANSMISSION( pdFAIL );					
				}

				break;
				
		case eSentData	:	

				/* We sent a data byte, if successful send the	next byte in 
				the message. */
				if( I2C_I2STAT == i2cSTATUS_DATA_TXED )
				{
					/* Index to the next byte to send. */
					lMessageIndex++;
					if( lMessageIndex < 0 )
					{
						/* lMessage index is still negative so we have so far 
						only sent the first byte of the buffer address.  Send 
						the second byte now, then initialise the buffer index
						to zero so the next byte sent comes from the actual 
						data buffer. */
						I2C_I2DAT = pxCurrentMessage->ucBufferAddressLowByte;
					}
					else if( lMessageIndex < pxCurrentMessage->lMessageLength )
					{
						/* Simply send the next byte in the tx buffer. */
						I2C_I2DAT = pxCurrentMessage->pucBuffer[ lMessageIndex ];										
					}
					else
					{
						/* No more bytes in this message to be send.  Finished 
						sending message - send a stop bit. */
						i2cEND_TRANSMISSION( pdPASS );

						/* If xMessageCompleteSemaphore is not null then there
						is a task waiting for this message to be sent and the
						semaphore must be 'given' to wake the task. */
						if( pxCurrentMessage->xMessageCompleteSemaphore )
						{
							xSemaphoreGiveFromISR( pxCurrentMessage->xMessageCompleteSemaphore, &xHigherPriorityTaskWoken );
						}

						/* Are there any other messages to transact? */
						if( xQueueReceiveFromISR( xMessagesForTx, &pxCurrentMessage, &xHigherPriorityTaskWoken ) == pdTRUE )
						{
							/* Start the next message from the Tx queue. */
							I2C_I2CONSET = i2cSTA_BIT;
						}
						else
						{
							/* No more message were queues for transaction so 
							the bus is free. */
							ulBusFree = ( unsigned long ) pdTRUE;			
						}
					}
				}
				else
				{
					/* Something unexpected happened, give up. */
					i2cEND_TRANSMISSION( pdFAIL );					
				}
				break;

		default	:	
		
				/* Should never get here. */
				eCurrentState = eSentStart;
				break;
	}	

	/* Clear the interrupt. */
	I2C_I2CONCLR = i2cSI_BIT;
	VICVectAddr = i2cCLEAR_VIC_INTERRUPT;

	if( xHigherPriorityTaskWoken )
	{
		portYIELD_FROM_ISR();
	}
}
/*-----------------------------------------------------------*/

