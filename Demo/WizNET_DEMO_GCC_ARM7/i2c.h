/*
    FreeRTOS V7.0.1 - Copyright (C) 2011 Real Time Engineers Ltd.
	

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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
	xSemaphoreHandle xMessageCompleteSemaphore;	/*< Contains a reference to a semaphore if the application tasks wants notifying when the message has been transacted. */
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
void i2cMessage( const unsigned char * const pucMessage, long lMessageLength, unsigned char ucSlaveAddress, unsigned short usBufferAddress, unsigned long ulDirection, xSemaphoreHandle xMessageCompleteSemaphore, portTickType xBlockTime );

#endif

