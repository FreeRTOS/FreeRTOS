/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#ifndef I2C_H
#define I2C_H

/* Structure used to capture the I2C message details.  The structure is then
 * queued for processing by the I2C ISR. 
 */
typedef struct AN_I2C_MESSAGE
{
	long lMessageLength;					/*< How many bytes of data to send or received - excluding the buffer address. */
	unsigned char ucSlaveAddress;			/*< The slave address of the WIZnet on the I2C bus. */
	unsigned char ucBufferAddressLowByte;	/*< The address within the WIZnet device to which data should be read from / written to. */
	unsigned char ucBufferAddressHighByte;	/*< As above, high byte. */
	SemaphoreHandle_t xMessageCompleteSemaphore;	/*< Contains a reference to a semaphore if the application tasks wants notifying when the message has been transacted. */
	unsigned char *pucBuffer;				/*< Pointer to the buffer from where data will be read for transmission, or into which received data will be placed. */
} xI2CMessage;

/* Constants to use as the ulDirection parameter of i2cMessage(). */
#define i2cWRITE				( ( unsigned long ) 0 )
#define i2cREAD					( ( unsigned long ) 1 )

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
void i2cMessage( const unsigned char * const pucMessage, long lMessageLength, unsigned char ucSlaveAddress, unsigned short usBufferAddress, unsigned long ulDirection, SemaphoreHandle_t xMessageCompleteSemaphore, TickType_t xBlockTime );

#endif

