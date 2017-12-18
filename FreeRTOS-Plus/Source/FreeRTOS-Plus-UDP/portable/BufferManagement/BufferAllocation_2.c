/*
 * FreeRTOS+UDP V1.0.4
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

/******************************************************************************
 *
 * See the following web page for essential buffer allocation scheme usage and 
 * configuration details:
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_UDP/Embedded_Ethernet_Buffer_Management.shtml
 *
 ******************************************************************************/

/* THIS FILE SHOULD NOT BE USED IF THE PROJECT INCLUDES A MEMORY ALLOCATOR
THAT WILL FRAGMENT THE HEAP MEMORY.  For example, heap_2 must not be used,
heap_4 can be used. */


/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+UDP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "NetworkInterface.h"

/* For an Ethernet interrupt to be able to obtain a network buffer there must
be at least this number of buffers available. */
#define ipINTERRUPT_BUFFER_GET_THRESHOLD	( 3 )

/* A list of free (available) xNetworkBufferDescriptor_t structures. */
static xList xFreeBuffersList;

/* Declares the pool of xNetworkBufferDescriptor_t structures that are available to the
system.  All the network buffers referenced from xFreeBuffersList exist in this
array.  The array is not accessed directly except during initialisation, when
the xFreeBuffersList is filled (as all the buffers are free when the system is
booted). */
static xNetworkBufferDescriptor_t xNetworkBuffers[ ipconfigNUM_NETWORK_BUFFERS ];

/* The semaphore used to obtain network buffers. */
static xSemaphoreHandle xNetworkBufferSemaphore = NULL;

/*-----------------------------------------------------------*/

BaseType_t xNetworkBuffersInitialise( void )
{
BaseType_t xReturn, x;

	/* Only initialise the buffers and their associated kernel objects if they
	have not been initialised before. */
	if( xNetworkBufferSemaphore == NULL )
	{
		xNetworkBufferSemaphore = xSemaphoreCreateCounting( ipconfigNUM_NETWORK_BUFFERS, ipconfigNUM_NETWORK_BUFFERS );
		configASSERT( xNetworkBufferSemaphore );
		vQueueAddToRegistry( xNetworkBufferSemaphore, "NetBufSem" );

		/* If the trace recorder code is included name the semaphore for viewing
		in FreeRTOS+Trace.  */
		#if ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS == 1
		{
			extern xQueueHandle xNetworkEventQueue;
			vTraceSetQueueName( xNetworkEventQueue, "IPStackEvent" );
			vTraceSetQueueName( xNetworkBufferSemaphore, "NetworkBufferCount" );
		}
		#endif /*  ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS == 1 */

		if( xNetworkBufferSemaphore != NULL )
		{
			vListInitialise( &xFreeBuffersList );

			/* Initialise all the network buffers.  No storage is allocated to
			the buffers yet. */
			for( x = 0; x < ipconfigNUM_NETWORK_BUFFERS; x++ )
			{
				/* Initialise and set the owner of the buffer list items. */
				xNetworkBuffers[ x ].pucEthernetBuffer = NULL;
				vListInitialiseItem( &( xNetworkBuffers[ x ].xBufferListItem ) );
				listSET_LIST_ITEM_OWNER( &( xNetworkBuffers[ x ].xBufferListItem ), &xNetworkBuffers[ x ] );

				/* Currently, all buffers are available for use. */
				vListInsert( &xFreeBuffersList, &( xNetworkBuffers[ x ].xBufferListItem ) );
			}
		}
	}

	if( xNetworkBufferSemaphore == NULL )
	{
		xReturn = pdFAIL;
	}
	else
	{
		xReturn = pdPASS;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

uint8_t *pucEthernetBufferGet( size_t *pxRequestedSizeBytes )
{
uint8_t *pucEthernetBuffer;

	if( *pxRequestedSizeBytes < sizeof( xARPPacket_t ) )
	{
		/* Buffers must be at least large enough to hold ARP packets, otherwise
		nothing can be done. */
		*pxRequestedSizeBytes = sizeof( xARPPacket_t );
	}

	/* Allocate a buffer large enough to store the requested Ethernet frame size
	and a pointer to a network buffer structure (hence the addition of
	ipBUFFER_PADDING bytes). */
	pucEthernetBuffer = ( uint8_t * ) pvPortMalloc( *pxRequestedSizeBytes + ipBUFFER_PADDING );

	/* Enough space is left at the start of the buffer to place a pointer to
	the network buffer structure that references this Ethernet buffer.  Return
	a pointer to the start of the Ethernet buffer itself. */
	pucEthernetBuffer += ipBUFFER_PADDING;

	return pucEthernetBuffer;
}
/*-----------------------------------------------------------*/

void vEthernetBufferRelease( uint8_t *pucEthernetBuffer )
{
	/* There is space before the Ethernet buffer in which a pointer to the
	network buffer that references this Ethernet buffer is stored.  Remove the
	space before freeing the buffer. */
	if( pucEthernetBuffer != NULL )
	{
		pucEthernetBuffer -= ipBUFFER_PADDING;
		vPortFree( ( void * ) pucEthernetBuffer );
	}
}
/*-----------------------------------------------------------*/

xNetworkBufferDescriptor_t *pxNetworkBufferGet( size_t xRequestedSizeBytes, TickType_t xBlockTimeTicks )
{
xNetworkBufferDescriptor_t *pxReturn = NULL;

	if( ( xRequestedSizeBytes != 0 ) && ( xRequestedSizeBytes < sizeof( xARPPacket_t ) ) )
	{
		/* ARP packets can replace application packets, so the storage must be
		at least large enough to hold an ARP. */
		xRequestedSizeBytes = sizeof( xARPPacket_t );
	}

	/* If there is a semaphore available, there is a network buffer available. */
	if( xSemaphoreTake( xNetworkBufferSemaphore, xBlockTimeTicks ) == pdPASS )
	{
		/* Protect the structure as it is accessed from tasks and interrupts. */
		taskENTER_CRITICAL();
		{
			pxReturn = ( xNetworkBufferDescriptor_t * ) listGET_OWNER_OF_HEAD_ENTRY( &xFreeBuffersList );
			uxListRemove( &( pxReturn->xBufferListItem ) );
		}
		taskEXIT_CRITICAL();

		/* Allocate storage of exactly the requested size to the buffer. */
		configASSERT( pxReturn->pucEthernetBuffer == NULL );
		if( xRequestedSizeBytes > 0 )
		{
			/* Extra space is obtained so a pointer to the network buffer can
			be stored at the beginning of the buffer. */
			pxReturn->pucEthernetBuffer = ( uint8_t * ) pvPortMalloc( xRequestedSizeBytes + ipBUFFER_PADDING );

			if( pxReturn->pucEthernetBuffer == NULL )
			{
				/* The attempt to allocate storage for the buffer payload failed,
				so the network buffer structure cannot be used and must be
				released. */
				vNetworkBufferRelease( pxReturn );
				pxReturn = NULL;
			}
			else
			{
				/* Store a pointer to the network buffer structure in the
				buffer storage area, then move the buffer pointer on past the
				stored pointer so the pointer value is not overwritten by the
				application when the buffer is used. */
				*( ( xNetworkBufferDescriptor_t ** ) ( pxReturn->pucEthernetBuffer ) ) = pxReturn;
				pxReturn->pucEthernetBuffer += ipBUFFER_PADDING;
				iptraceNETWORK_BUFFER_OBTAINED( pxReturn );

				/* Store the actual size of the allocated buffer, which may be
				greater than the requested size. */
				pxReturn->xDataLength = xRequestedSizeBytes;
			}
		}
		else
		{
			iptraceNETWORK_BUFFER_OBTAINED( pxReturn );
		}
	}

	if( pxReturn == NULL )
	{
		iptraceFAILED_TO_OBTAIN_NETWORK_BUFFER();
	}

	return pxReturn;
}
/*-----------------------------------------------------------*/

void vNetworkBufferRelease( xNetworkBufferDescriptor_t * const pxNetworkBuffer )
{
BaseType_t xListItemAlreadyInFreeList;

	/* Ensure the buffer is returned to the list of free buffers before the
	counting semaphore is 'given' to say a buffer is available.  Release the
	storage allocated to the buffer payload.  THIS FILE SHOULD NOT BE USED
	IF THE PROJECT INCLUDES A MEMORY ALLOCATOR THAT WILL FRAGMENT THE HEAP
	MEMORY.  For example, heap_2 must not be used, heap_4 can be used. */
	vEthernetBufferRelease( pxNetworkBuffer->pucEthernetBuffer );
	pxNetworkBuffer->pucEthernetBuffer = NULL;

	taskENTER_CRITICAL();
	{
		xListItemAlreadyInFreeList = listIS_CONTAINED_WITHIN( &xFreeBuffersList, &( pxNetworkBuffer->xBufferListItem ) );

		if( xListItemAlreadyInFreeList == pdFALSE )
		{
			vListInsertEnd( &xFreeBuffersList, &( pxNetworkBuffer->xBufferListItem ) );
		}

		configASSERT( xListItemAlreadyInFreeList == pdFALSE );
	}
	taskEXIT_CRITICAL();

	xSemaphoreGive( xNetworkBufferSemaphore );
	iptraceNETWORK_BUFFER_RELEASED( pxNetworkBuffer );
}
/*-----------------------------------------------------------*/

#if( ipconfigINCLUDE_TEST_CODE == 1 )

UBaseType_t uxGetNumberOfFreeNetworkBuffers( void )
{
	return listCURRENT_LIST_LENGTH( &xFreeBuffersList );
}

#endif /* ipconfigINCLUDE_TEST_CODE */
