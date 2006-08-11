/*
	FreeRTOS.org V4.0.5 - copyright (C) 2003-2006 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************
	See http://www.FreeRTOS.org for documentation, latest information, license 
	and contact details.  Please ensure to read the configuration and relevant 
	port sections of the online documentation.
	***************************************************************************
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
#define i2cSTA_BIT		( ( unsigned portCHAR ) 0x20 )
#define i2cSI_BIT		( ( unsigned portCHAR ) 0x08 )
#define i2cSTO_BIT		( ( unsigned portCHAR ) 0x10 )
#define i2cAA_BIT		( ( unsigned portCHAR ) 0x04 )

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
static xQueueHandle xMessagesForTx;

/* Flag used to indicate whether or not the ISR is amid sending a message. */
unsigned portLONG ulBusFree = ( unsigned portLONG ) pdTRUE;

/* Setting this to true will cause the TCP task to think a message is 
complete and thus restart.  It can therefore be used under error states
to force a restart. */
volatile portLONG lTransactionCompleted = pdTRUE;

/*-----------------------------------------------------------*/

void vI2CISRCreateQueues( unsigned portBASE_TYPE uxQueueLength, xQueueHandle *pxTxMessages, unsigned portLONG **ppulBusFree )
{
	/* Create the queues used to hold Rx and Tx characters. */
	xMessagesForTx = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( xI2CMessage * ) );

	/* Pass back a reference to the queue and bus free flag so the I2C API file 
	can post messages. */
	*pxTxMessages = xMessagesForTx;
	*ppulBusFree = &ulBusFree;
}
/*-----------------------------------------------------------*/

void vI2C_ISR( void ) __attribute__ (( naked ));
void vI2C_ISR( void )
{
	portENTER_SWITCHING_ISR();

	/* Holds the current transmission state. */							
	static I2C_STATE eCurrentState = eSentStart;
	static portLONG lMessageIndex = -i2cBUFFER_ADDRESS_BYTES; /* There are two address bytes to send prior to the data. */
	portBASE_TYPE xTaskWokenByTx = pdFALSE;
	portLONG lBytesLeft;

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
					if( lBytesLeft == ( unsigned portLONG ) 0 )
					{
						/* This was the last byte in the message. */
						i2cEND_TRANSMISSION( pdPASS );

						/* If xMessageCompleteSemaphore is not null then there
						is a task waiting for this message to complete and we
						must 'give' the semaphore so the task is woken.*/
						if( pxCurrentMessage->xMessageCompleteSemaphore )
						{
							xTaskWokenByTx = xSemaphoreGiveFromISR( pxCurrentMessage->xMessageCompleteSemaphore, xTaskWokenByTx );
						}

						/* Are there any other messages to transact? */
						if( xQueueReceiveFromISR( xMessagesForTx, &pxCurrentMessage, &xTaskWokenByTx ) == pdTRUE )
						{
							/* Start the next message - which was
							retrieved from the queue. */
							I2C_I2CONSET = i2cSTA_BIT;
						}
						else
						{
							/* No more messages were found to be waiting for
							transaction so the bus is free. */
							ulBusFree = ( unsigned portLONG ) pdTRUE;			
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
							xTaskWokenByTx = xSemaphoreGiveFromISR( pxCurrentMessage->xMessageCompleteSemaphore, xTaskWokenByTx );
						}

						/* Are there any other messages to transact? */
						if( xQueueReceiveFromISR( xMessagesForTx, &pxCurrentMessage, &xTaskWokenByTx ) == pdTRUE )
						{
							/* Start the next message from the Tx queue. */
							I2C_I2CONSET = i2cSTA_BIT;
						}
						else
						{
							/* No more message were queues for transaction so 
							the bus is free. */
							ulBusFree = ( unsigned portLONG ) pdTRUE;			
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

	portEXIT_SWITCHING_ISR( ( xTaskWokenByTx ) );
}
/*-----------------------------------------------------------*/

