/*
    FreeRTOS V6.0.5 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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

#ifndef CIRCULAR_BUFFER_H
#define CIRCULAR_BUFFER_H

/* Structure that holds the state of the circular buffer. */
typedef struct
{
	unsigned char *pucDataBuffer;
	unsigned long ulBufferSizeInBytes;
	unsigned char *pucNextByteToRead;
	unsigned char *pucNextByteToWrite;
	unsigned long ulDataSizeInBytes;
	void *pvTag;
} xCircularBuffer;


/*
 * Setup a circular buffer ready for use.
 *
 * pxBuffer : The xCicularBuffer structure being initialised.
 *
 * pucDataBuffer : The buffer to be used by the xCicularBuffer object.
 *
 * ulBufferSizeInBytes : The dimention of pucDataBuffer in bytes.
 *
 * ulDataSizeInBytes : The size of the data that is to be stored in the
 *		circular buffer.  For example, 4 if the buffer is used to hold
 *		unsigned longs, 1 if the buffer is used to hold chars.
 *
 * pvTag : Can be used for anything, although normally used in conjunction with
 *         a DMA register.
 */
void vInitialiseCircularBuffer( xCircularBuffer *pxBuffer,
							   	unsigned char *pucDataBuffer,
								unsigned long ulBufferSizeInBytes,
								unsigned long ulDataSizeInBytes,
								void *pvTag
							  );
/*
 * Returns the number of bytes that are currently available within the
 * buffer.
 */
unsigned long ulBytesInCircularBuffer( const xCircularBuffer * const pxBuffer );

/*
 * Obtain bytes from the circular buffer.  Data may have been placed in
 * the circular buffer by a DMA transfer or simply written to the buffer by
 * the application code.
 *
 * pxBuffer : The circular buffer from which data is to be read.
 *
 * pucBuffer : The buffer into which the received bytes should be copied.
 *
 * ulWantedBytes : The number of bytes we are going to attempt to receive
 *		from the circular buffer.
 *
 * return : The actual number of bytes received from the circular buffer.
 *		This might be less than the number of bytes we attempted to receive.
 */
unsigned long ulCopyReceivedBytes( xCircularBuffer *pxBuffer, unsigned char * pucBuffer, unsigned long ulWantedBytes );

#endif

