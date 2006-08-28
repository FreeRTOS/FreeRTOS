/*
	FreeRTOS.org V4.1.0 - copyright (C) 2003-2006 Richard Barry.

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

#ifndef I2C_H
#define I2C_H

/* Structure used to capture the I2C message details.  The structure is then
 * queued for processing by the I2C ISR. 
 */
typedef struct AN_I2C_MESSAGE
{
	portLONG lMessageLength;					/*< How many bytes of data to send or received - excluding the buffer address. */
	unsigned portCHAR ucSlaveAddress;			/*< The slave address of the WIZnet on the I2C bus. */
	unsigned portCHAR ucBufferAddressLowByte;	/*< The address within the WIZnet device to which data should be read from / written to. */
	unsigned portCHAR ucBufferAddressHighByte;	/*< As above, high byte. */
	xSemaphoreHandle xMessageCompleteSemaphore;	/*< Contains a reference to a semaphore if the application tasks wants notifying when the message has been transacted. */
	unsigned portCHAR *pucBuffer;				/*< Pointer to the buffer from where data will be read for transmission, or into which received data will be placed. */
} xI2CMessage;

/* Constants to use as the ulDirection parameter of i2cMessage(). */
#define i2cWRITE				( ( unsigned portLONG ) 0 )
#define i2cREAD					( ( unsigned portLONG ) 1 )

/**
 * Must be called once before any calls to i2cMessage.
 */
void i2cInit( void );

/**
 * Send or receive a message over the I2C bus.
 *
 * @param pucMessage	 The data to be transmitted or the buffer into which
 *						 received data will be placed. 
 *
 * @param lMessageLength The number of bytes to either transmit or receive.
 *
 * @param ucSlaveAddress The slave address of the WIZNet device on the I2C bus.
 *
 * @param usBufferAddress The address within the WIZNet device to which data is
 *						 either written to or read from.  The WIZnet has it's
 *						 own Rx and Tx buffers.
 *
 * @param ulDirection	 Must be either i2cWRITE or i2cREAD as #defined above.
 *
 * @param xMessageCompleteSemaphore
 *						 Can be used to pass a semaphore reference if the 
 *						 calling task want notification of when the message has
 *						 completed.  Otherwise NULL can be passed.
 * 
 * @param xBlockTime	 The time to wait for a space in the message queue to 
 *						 become available should one not be available 
 *						 immediately.
 */
void i2cMessage( const unsigned portCHAR * const pucMessage, portLONG lMessageLength, unsigned portCHAR ucSlaveAddress, unsigned portSHORT usBufferAddress, unsigned portLONG ulDirection, xSemaphoreHandle xMessageCompleteSemaphore, portTickType xBlockTime );

#endif

