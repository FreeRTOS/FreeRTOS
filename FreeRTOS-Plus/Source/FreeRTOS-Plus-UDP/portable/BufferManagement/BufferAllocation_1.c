/*
 * FreeRTOS+UDP V1.0.3 (C) 2014 Real Time Engineers ltd.
 * All rights reserved
 *
 * This file is part of the FreeRTOS+UDP distribution.  The FreeRTOS+UDP license
 * terms are different to the FreeRTOS license terms.
 *
 * FreeRTOS+UDP uses a dual license model that allows the software to be used 
 * under a standard GPL open source license, or a commercial license.  The 
 * standard GPL license (unlike the modified GPL license under which FreeRTOS 
 * itself is distributed) requires that all software statically linked with 
 * FreeRTOS+UDP is also distributed under the same GPL V2 license terms.  
 * Details of both license options follow:
 *
 * - Open source licensing -
 * FreeRTOS+UDP is a free download and may be used, modified, evaluated and
 * distributed without charge provided the user adheres to version two of the
 * GNU General Public License (GPL) and does not remove the copyright notice or
 * this text.  The GPL V2 text is available on the gnu.org web site, and on the
 * following URL: http://www.FreeRTOS.org/gpl-2.0.txt.
 *
 * - Commercial licensing -
 * Businesses and individuals that for commercial or other reasons cannot comply
 * with the terms of the GPL V2 license must obtain a commercial license before 
 * incorporating FreeRTOS+UDP into proprietary software for distribution in any 
 * form.  Commercial licenses can be purchased from http://shop.freertos.org/udp 
 * and do not require any source files to be changed.
 *
 * FreeRTOS+UDP is distributed in the hope that it will be useful.  You cannot
 * use FreeRTOS+UDP unless you agree that you use the software 'as is'.
 * FreeRTOS+UDP is provided WITHOUT ANY WARRANTY; without even the implied
 * warranties of NON-INFRINGEMENT, MERCHANTABILITY or FITNESS FOR A PARTICULAR
 * PURPOSE. Real Time Engineers Ltd. disclaims all conditions and terms, be they
 * implied, expressed, or statutory.
 *
 * 1 tab == 4 spaces!
 *
 * http://www.FreeRTOS.org
 * http://www.FreeRTOS.org/udp
 *
 */


/******************************************************************************
 *
 * See the following web page for essential buffer allocation scheme usage and
 * configuration details:
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_UDP/Embedded_Ethernet_Buffer_Management.shtml
 *
 ******************************************************************************/


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

portBASE_TYPE xNetworkBuffersInitialise( void )
{
portBASE_TYPE xReturn, x;

	/* Only initialise the buffers and their associated kernel objects if they
	have not been initialised before. */
	if( xNetworkBufferSemaphore == NULL )
	{
		xNetworkBufferSemaphore = xSemaphoreCreateCounting( ipconfigNUM_NETWORK_BUFFERS, ipconfigNUM_NETWORK_BUFFERS );
		configASSERT( xNetworkBufferSemaphore );

		if( xNetworkBufferSemaphore != NULL )
		{
			vListInitialise( &xFreeBuffersList );

			/* Initialise all the network buffers.  The buffer storage comes
			from the network interface, and different hardware has different
			requirements. */
			vNetworkInterfaceAllocateRAMToBuffers( xNetworkBuffers );
			for( x = 0; x < ipconfigNUM_NETWORK_BUFFERS; x++ )
			{
				/* Initialise and set the owner of the buffer list items. */
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

xNetworkBufferDescriptor_t *pxNetworkBufferGet( size_t xRequestedSizeBytes, portTickType xBlockTimeTicks )
{
xNetworkBufferDescriptor_t *pxReturn = NULL;

	/*_RB_ The current implementation only has a single size memory block, so
	the requested size parameter is not used (yet). */
	( void ) xRequestedSizeBytes;

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
		iptraceNETWORK_BUFFER_OBTAINED( pxReturn );
	}
	else
	{
		iptraceFAILED_TO_OBTAIN_NETWORK_BUFFER();
	}

	return pxReturn;
}
/*-----------------------------------------------------------*/

xNetworkBufferDescriptor_t *pxNetworkBufferGetFromISR( size_t xRequestedSizeBytes )
{
xNetworkBufferDescriptor_t *pxReturn = NULL;
unsigned portBASE_TYPE uxSavedInterruptStatus;

	/*_RB_ The current implementation only has a single size memory block, so
	the requested size parameter is not used (yet). */
	( void ) xRequestedSizeBytes;

	/* If there is a semaphore available then there is a buffer available, but,
	as this is called from an interrupt, only take a buffer if there are at
	least ipINTERRUPT_BUFFER_GET_THRESHOLD buffers remaining.  This prevents,
	to a certain degree at least, a rapidly executing interrupt exhausting
	buffer and in so doing preventing tasks from continuing. */
	if( uxQueueMessagesWaitingFromISR( ( xQueueHandle ) xNetworkBufferSemaphore ) > ipINTERRUPT_BUFFER_GET_THRESHOLD )
	{
		if( xSemaphoreTakeFromISR( xNetworkBufferSemaphore, NULL ) == pdPASS )
		{
			/* Protect the structure as it is accessed from tasks and interrupts. */
			uxSavedInterruptStatus = portSET_INTERRUPT_MASK_FROM_ISR();
			{
				pxReturn = ( xNetworkBufferDescriptor_t * ) listGET_OWNER_OF_HEAD_ENTRY( &xFreeBuffersList );
				uxListRemove( &( pxReturn->xBufferListItem ) );
			}
			portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedInterruptStatus );

			iptraceNETWORK_BUFFER_OBTAINED_FROM_ISR( pxReturn );
		}
	}

	if( pxReturn == NULL )
	{
		iptraceFAILED_TO_OBTAIN_NETWORK_BUFFER_FROM_ISR();
	}

	return pxReturn;
}
/*-----------------------------------------------------------*/

portBASE_TYPE vNetworkBufferReleaseFromISR( xNetworkBufferDescriptor_t * const pxNetworkBuffer )
{
unsigned portBASE_TYPE uxSavedInterruptStatus;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* Ensure the buffer is returned to the list of free buffers before the
	counting semaphore is 'given' to say a buffer is available. */
	uxSavedInterruptStatus = portSET_INTERRUPT_MASK_FROM_ISR();
	{
		vListInsertEnd( &xFreeBuffersList, &( pxNetworkBuffer->xBufferListItem ) );
	}
	portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedInterruptStatus );

	xSemaphoreGiveFromISR( xNetworkBufferSemaphore, &xHigherPriorityTaskWoken );
	iptraceNETWORK_BUFFER_RELEASED( pxNetworkBuffer );

	return xHigherPriorityTaskWoken;
}
/*-----------------------------------------------------------*/

void vNetworkBufferRelease( xNetworkBufferDescriptor_t * const pxNetworkBuffer )
{
portBASE_TYPE xListItemAlreadyInFreeList;

	/* Ensure the buffer is returned to the list of free buffers before the
	counting semaphore is 'given' to say a buffer is available. */
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

unsigned portBASE_TYPE uxGetNumberOfFreeNetworkBuffers( void )
{
	return listCURRENT_LIST_LENGTH( &xFreeBuffersList );
}

#endif /* ipconfigINCLUDE_TEST_CODE */
