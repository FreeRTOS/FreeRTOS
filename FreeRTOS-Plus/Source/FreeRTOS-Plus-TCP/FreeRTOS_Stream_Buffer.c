/*
 * FreeRTOS+TCP Labs Build 160919 (C) 2016 Real Time Engineers ltd.
 * Authors include Hein Tibosch and Richard Barry
 *
 *******************************************************************************
 ***** NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ***
 ***                                                                         ***
 ***                                                                         ***
 ***   FREERTOS+TCP IS STILL IN THE LAB (mainly because the FTP and HTTP     ***
 ***   demos have a dependency on FreeRTOS+FAT, which is only in the Labs    ***
 ***   download):                                                            ***
 ***                                                                         ***
 ***   FreeRTOS+TCP is functional and has been used in commercial products   ***
 ***   for some time.  Be aware however that we are still refining its       ***
 ***   design, the source code does not yet quite conform to the strict      ***
 ***   coding and style standards mandated by Real Time Engineers ltd., and  ***
 ***   the documentation and testing is not necessarily complete.            ***
 ***                                                                         ***
 ***   PLEASE REPORT EXPERIENCES USING THE SUPPORT RESOURCES FOUND ON THE    ***
 ***   URL: http://www.FreeRTOS.org/contact  Active early adopters may, at   ***
 ***   the sole discretion of Real Time Engineers Ltd., be offered versions  ***
 ***   under a license other than that described below.                      ***
 ***                                                                         ***
 ***                                                                         ***
 ***** NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ******* NOTE ***
 *******************************************************************************
 *
 * FreeRTOS+TCP can be used under two different free open source licenses.  The
 * license that applies is dependent on the processor on which FreeRTOS+TCP is
 * executed, as follows:
 *
 * If FreeRTOS+TCP is executed on one of the processors listed under the Special
 * License Arrangements heading of the FreeRTOS+TCP license information web
 * page, then it can be used under the terms of the FreeRTOS Open Source
 * License.  If FreeRTOS+TCP is used on any other processor, then it can be used
 * under the terms of the GNU General Public License V2.  Links to the relevant
 * licenses follow:
 *
 * The FreeRTOS+TCP License Information Page: http://www.FreeRTOS.org/tcp_license
 * The FreeRTOS Open Source License: http://www.FreeRTOS.org/license
 * The GNU General Public License Version 2: http://www.FreeRTOS.org/gpl-2.0.txt
 *
 * FreeRTOS+TCP is distributed in the hope that it will be useful.  You cannot
 * use FreeRTOS+TCP unless you agree that you use the software 'as is'.
 * FreeRTOS+TCP is provided WITHOUT ANY WARRANTY; without even the implied
 * warranties of NON-INFRINGEMENT, MERCHANTABILITY or FITNESS FOR A PARTICULAR
 * PURPOSE. Real Time Engineers Ltd. disclaims all conditions and terms, be they
 * implied, expressed, or statutory.
 *
 * 1 tab == 4 spaces!
 *
 * http://www.FreeRTOS.org
 * http://www.FreeRTOS.org/plus
 * http://www.FreeRTOS.org/labs
 *
 */

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"

/*
 * uxStreamBufferAdd( )
 * Adds data to a stream buffer.  If uxOffset > 0, data will be written at
 * an offset from uxHead while uxHead will not be moved yet.  This possibility
 * will be used when TCP data is received while earlier data is still missing.
 * If 'pucData' equals NULL, the function is called to advance 'uxHead' only.
 */
size_t uxStreamBufferAdd( StreamBuffer_t *pxBuffer, size_t uxOffset, const uint8_t *pucData, size_t uxCount )
{
size_t uxSpace, uxNextHead, uxFirst;

	uxSpace = uxStreamBufferGetSpace( pxBuffer );

	/* If uxOffset > 0, items can be placed in front of uxHead */
	if( uxSpace > uxOffset )
	{
		uxSpace -= uxOffset;
	}
	else
	{
		uxSpace = 0u;
	}

	/* The number of bytes that can be written is the minimum of the number of
	bytes requested and the number available. */
	uxCount = FreeRTOS_min_uint32( uxSpace, uxCount );

	if( uxCount != 0u )
	{
		uxNextHead = pxBuffer->uxHead;

		if( uxOffset != 0u )
		{
			/* ( uxOffset > 0 ) means: write in front if the uxHead marker */
			uxNextHead += uxOffset;
			if( uxNextHead >= pxBuffer->LENGTH )
			{
				uxNextHead -= pxBuffer->LENGTH;
			}
		}

		if( pucData != NULL )
		{
			/* Calculate the number of bytes that can be added in the first
			write - which may be less than the total number of bytes that need
			to be added if the buffer will wrap back to the beginning. */
			uxFirst = FreeRTOS_min_uint32( pxBuffer->LENGTH - uxNextHead, uxCount );

			/* Write as many bytes as can be written in the first write. */
			memcpy( ( void* ) ( pxBuffer->ucArray + uxNextHead ), pucData, uxFirst );

			/* If the number of bytes written was less than the number that
			could be written in the first write... */
			if( uxCount > uxFirst )
			{
				/* ...then write the remaining bytes to the start of the
				buffer. */
				memcpy( ( void * )pxBuffer->ucArray, pucData + uxFirst, uxCount - uxFirst );
			}
		}

		if( uxOffset == 0u )
		{
			/* ( uxOffset == 0 ) means: write at uxHead position */
			uxNextHead += uxCount;
			if( uxNextHead >= pxBuffer->LENGTH )
			{
				uxNextHead -= pxBuffer->LENGTH;
			}
			pxBuffer->uxHead = uxNextHead;
		}

		if( xStreamBufferLessThenEqual( pxBuffer, pxBuffer->uxFront, uxNextHead ) != pdFALSE )
		{
			/* Advance the front pointer */
			pxBuffer->uxFront = uxNextHead;
		}
	}

	return uxCount;
}
/*-----------------------------------------------------------*/

/*
 * uxStreamBufferGet( )
 * 'uxOffset' can be used to read data located at a certain offset from 'lTail'.
 * If 'pucData' equals NULL, the function is called to advance 'lTail' only.
 * if 'xPeek' is pdTRUE, or if 'uxOffset' is non-zero, the 'lTail' pointer will
 * not be advanced.
 */
size_t uxStreamBufferGet( StreamBuffer_t *pxBuffer, size_t uxOffset, uint8_t *pucData, size_t uxMaxCount, BaseType_t xPeek )
{
size_t uxSize, uxCount, uxFirst, uxNextTail;

	/* How much data is available? */
	uxSize = uxStreamBufferGetSize( pxBuffer );

	if( uxSize > uxOffset )
	{
		uxSize -= uxOffset;
	}
	else
	{
		uxSize = 0u;
	}

	/* Use the minimum of the wanted bytes and the available bytes. */
	uxCount = FreeRTOS_min_uint32( uxSize, uxMaxCount );

	if( uxCount > 0u )
	{
		uxNextTail = pxBuffer->uxTail;

		if( uxOffset != 0u )
		{
			uxNextTail += uxOffset;
			if( uxNextTail >= pxBuffer->LENGTH )
			{
				uxNextTail -= pxBuffer->LENGTH;
			}
		}

		if( pucData != NULL )
		{
			/* Calculate the number of bytes that can be read - which may be
			less than the number wanted if the data wraps around to the start of
			the buffer. */
			uxFirst = FreeRTOS_min_uint32( pxBuffer->LENGTH - uxNextTail, uxCount );

			/* Obtain the number of bytes it is possible to obtain in the first
			read. */
			memcpy( pucData, pxBuffer->ucArray + uxNextTail, uxFirst );

			/* If the total number of wanted bytes is greater than the number
			that could be read in the first read... */
			if( uxCount > uxFirst )
			{
				/*...then read the remaining bytes from the start of the buffer. */
				memcpy( pucData + uxFirst, pxBuffer->ucArray, uxCount - uxFirst );
			}
		}

		if( ( xPeek == pdFALSE ) && ( uxOffset == 0UL ) )
		{
			/* Move the tail pointer to effecively remove the data read from
			the buffer. */
			uxNextTail += uxCount;

			if( uxNextTail >= pxBuffer->LENGTH )
			{
				uxNextTail -= pxBuffer->LENGTH;
			}

			pxBuffer->uxTail = uxNextTail;
		}
	}

	return uxCount;
}

