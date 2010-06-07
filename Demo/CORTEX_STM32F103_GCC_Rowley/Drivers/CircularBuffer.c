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

#include <string.h>

#include "FreeRTOS.h"
#include "CircularBuffer.h"

/*-----------------------------------------------------------*/

/* See the header file for function information. */
void vInitialiseCircularBuffer( xCircularBuffer *pxBuffer,
							   	unsigned char *pucDataBuffer,
								unsigned long ulBufferSizeInBytes,
								unsigned long ulDataSizeInBytes,
								void *pvTag
							  )
{
	pxBuffer->pucDataBuffer = pucDataBuffer;
	pxBuffer->ulBufferSizeInBytes = ulBufferSizeInBytes;
	pxBuffer->pucNextByteToRead = pucDataBuffer;
	pxBuffer->pucNextByteToWrite = pucDataBuffer;
	pxBuffer->ulDataSizeInBytes = ulDataSizeInBytes;
	pxBuffer->pvTag = pvTag;
}
/*-----------------------------------------------------------*/

/* See the header file for function information. */
unsigned long ulBytesInCircularBuffer( const xCircularBuffer * const pxBuffer )
{
unsigned char *pucNextByteToWrite;
unsigned long ulReturn;

	if( pxBuffer->pvTag != NULL )
	{
		/* Locate the position that the DMA will next write to. */
		pucNextByteToWrite = ( unsigned char * ) *( ( unsigned long * ) pxBuffer->pvTag );
	}
	else
	{
		/* Locate the position the application will next write to. */
		pucNextByteToWrite = pxBuffer->pucNextByteToWrite;
	}
	
	/* Has the write pointer wrapped back to the start of the buffer
	compared to our read pointer? */
	if( ( unsigned long ) pucNextByteToWrite >= ( unsigned long ) pxBuffer->pucNextByteToRead )
	{
		/* The write pointer is still ahead of us in the buffer.  The amount of
		data available is simple the gap between the two pointers. */
		ulReturn = ( unsigned long ) pucNextByteToWrite - ( unsigned long ) pxBuffer->pucNextByteToRead;
	}
	else
	{
		/* The write pointer has wrapped back to the start.  The amount of data
		available is equal to the data between the read pointer and the end of
		the buffer...*/
		ulReturn = ( unsigned long ) &( pxBuffer->pucDataBuffer[ pxBuffer->ulBufferSizeInBytes ] ) - ( unsigned long ) pxBuffer->pucNextByteToRead;

		/*... plus the data between the start of the buffer and the write
		pointer. */
		ulReturn += ( unsigned long ) pucNextByteToWrite - ( unsigned long ) pxBuffer->pucDataBuffer;
	}

	return ulReturn;
}
/*-----------------------------------------------------------*/

unsigned long ulCopyReceivedBytes( xCircularBuffer *pxBuffer, unsigned char * pucBuffer, unsigned long ulWantedBytes )
{
unsigned char *pucNextByteToWrite;
unsigned long ulNumberOfBytesRead = 0, ulNumberOfBytesAvailable;

	if( pxBuffer->pvTag != NULL )
	{
		/* Locate the position that the DMA will next write to. */
		pucNextByteToWrite = ( unsigned char * ) *( ( unsigned long * ) pxBuffer->pvTag );
	}
	else
	{
		/* Locate the position that the application will next write to. */
		pucNextByteToWrite = pxBuffer->pucNextByteToWrite;
	}
	
	if( ( unsigned long ) pucNextByteToWrite >= ( unsigned long ) pxBuffer->pucNextByteToRead )
	{
		/* The write pointer has not wrapped around from our read pointer.
	
		Clip the number of bytes to read to the number available if the number
		available is less than that wanted. */
		ulNumberOfBytesAvailable = ( unsigned long ) pucNextByteToWrite - ( unsigned long ) ( pxBuffer->pucNextByteToRead );
		
		if( ulNumberOfBytesAvailable < ulWantedBytes )
		{
			ulWantedBytes = ulNumberOfBytesAvailable;
		}
		
		/* Copy the data from ulRxBuffer into the application buffer. */
		memcpy( pucBuffer, pxBuffer->pucNextByteToRead, ulWantedBytes );

		/* Move up our read buffer. */
		pxBuffer->pucNextByteToRead += ulWantedBytes;
		ulNumberOfBytesRead = ulWantedBytes;
	}
	else
	{
		/* The write pointer has wrapped around from our read pointer.  Is there
		enough space from our read pointer to the end of the buffer without the
		read pointer also wrapping around? */
		ulNumberOfBytesAvailable = ( unsigned long ) &( pxBuffer->pucDataBuffer[ pxBuffer->ulBufferSizeInBytes ] ) - ( unsigned long ) pxBuffer->pucNextByteToRead;
		
		if( ulNumberOfBytesAvailable >= ulWantedBytes )
		{
			/* There is enough space from our current read pointer up to the end
			of the buffer to obtain the number of bytes requested. */
			memcpy( pucBuffer, pxBuffer->pucNextByteToRead, ulWantedBytes );

			/* Move up our read buffer. */
			pxBuffer->pucNextByteToRead += ulWantedBytes;
			ulNumberOfBytesRead = ulWantedBytes;
		}
		else
		{
			/* There is not enough space up to the end of the buffer to obtain
			the number of bytes requested.  Copy up to the end of the buffer. */
			memcpy( pucBuffer, pxBuffer->pucNextByteToRead, ulNumberOfBytesAvailable );
			ulNumberOfBytesRead = ulNumberOfBytesAvailable;
			
			/* Then wrap back to the beginning of the buffer to attempt to
			read the remaining bytes. */
			pxBuffer->pucNextByteToRead = pxBuffer->pucDataBuffer;
			pucBuffer += ulNumberOfBytesAvailable;
			
			/* How many more bytes do we want to read? */
			ulWantedBytes -= ulNumberOfBytesAvailable;
			
			/* Clip the number of bytes we are going to read to the number
			available if this is less than the number we want. */
			ulNumberOfBytesAvailable = ( unsigned long ) pucNextByteToWrite - ( unsigned long ) pxBuffer->pucNextByteToRead;
			
			if( ulNumberOfBytesAvailable < ulWantedBytes )
			{
				ulWantedBytes = ulNumberOfBytesAvailable;
			}

			/* Copy these into the buffer. */
			memcpy( pucBuffer, pxBuffer->pucNextByteToRead, ulWantedBytes );

			/* Move up our read buffer. */
			pxBuffer->pucNextByteToRead += ulWantedBytes;
			ulNumberOfBytesRead += ulWantedBytes;
		}
	}
	
	/* Check we have not moved our read pointer off the end of the buffer. */
	if( ( unsigned long ) pxBuffer->pucNextByteToRead >= ( unsigned long ) &( pxBuffer->pucDataBuffer[ pxBuffer->ulBufferSizeInBytes ] ) )
	{
		pxBuffer->pucNextByteToRead = pxBuffer->pucDataBuffer;	
	}
	
	/* Return the number of bytes read. */
	return ulNumberOfBytesRead;
}

