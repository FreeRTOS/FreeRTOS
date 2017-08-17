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

/******************************************************************************
 *
 * See the following web page for essential buffer allocation scheme usage and
 * configuration details:
 * http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/Embedded_Ethernet_Buffer_Management.html
 *
 ******************************************************************************/

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"

/* For an Ethernet interrupt to be able to obtain a network buffer there must
be at least this number of buffers available. */
#define baINTERRUPT_BUFFER_GET_THRESHOLD	( 3 )

/* A list of free (available) NetworkBufferDescriptor_t structures. */
static List_t xFreeBuffersList;

/* Some statistics about the use of buffers. */
static UBaseType_t uxMinimumFreeNetworkBuffers = 0u;

/* Declares the pool of NetworkBufferDescriptor_t structures that are available
to the system.  All the network buffers referenced from xFreeBuffersList exist
in this array.  The array is not accessed directly except during initialisation,
when the xFreeBuffersList is filled (as all the buffers are free when the system
is booted). */
static NetworkBufferDescriptor_t xNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ];

/* This constant is defined as true to let FreeRTOS_TCP_IP.c know that the
network buffers have constant size, large enough to hold the biggest Ethernet
packet. No resizing will be done. */
const BaseType_t xBufferAllocFixedSize = pdTRUE;

/* The semaphore used to obtain network buffers. */
static SemaphoreHandle_t xNetworkBufferSemaphore = NULL;

#if( ipconfigTCP_IP_SANITY != 0 )
	static char cIsLow = pdFALSE;
	UBaseType_t bIsValidNetworkDescriptor( const NetworkBufferDescriptor_t * pxDesc );
#else
	static UBaseType_t bIsValidNetworkDescriptor( const NetworkBufferDescriptor_t * pxDesc );
#endif /* ipconfigTCP_IP_SANITY */

static void prvShowWarnings( void );

/* The user can define their own ipconfigBUFFER_ALLOC_LOCK() and
ipconfigBUFFER_ALLOC_UNLOCK() macros, especially for use form an ISR.  If these
are not defined then default them to call the normal enter/exit critical
section macros. */
#if !defined( ipconfigBUFFER_ALLOC_LOCK )

	#define ipconfigBUFFER_ALLOC_INIT( ) do {} while (0)
	#define ipconfigBUFFER_ALLOC_LOCK_FROM_ISR()		\
		UBaseType_t uxSavedInterruptStatus = ( UBaseType_t ) portSET_INTERRUPT_MASK_FROM_ISR(); \
		{

	#define ipconfigBUFFER_ALLOC_UNLOCK_FROM_ISR()		\
			portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedInterruptStatus ); \
		}

	#define ipconfigBUFFER_ALLOC_LOCK()					taskENTER_CRITICAL()
	#define ipconfigBUFFER_ALLOC_UNLOCK()				taskEXIT_CRITICAL()

#endif /* ipconfigBUFFER_ALLOC_LOCK */

/*-----------------------------------------------------------*/

#if( ipconfigTCP_IP_SANITY != 0 )

	/* HT: SANITY code will be removed as soon as the library is stable
	 * and and ready to become public
	 * Function below gives information about the use of buffers */
	#define WARN_LOW		( 2 )
	#define WARN_HIGH		( ( 5 * ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ) / 10 )

#endif /* ipconfigTCP_IP_SANITY */

/*-----------------------------------------------------------*/

#if( ipconfigTCP_IP_SANITY != 0 )

	BaseType_t prvIsFreeBuffer( const NetworkBufferDescriptor_t *pxDescr )
	{
		return ( bIsValidNetworkDescriptor( pxDescr ) != 0 ) &&
			( listIS_CONTAINED_WITHIN( &xFreeBuffersList, &( pxDescr->xBufferListItem ) ) != 0 );
	}
	/*-----------------------------------------------------------*/

	static void prvShowWarnings( void )
	{
		UBaseType_t uxCount = uxGetNumberOfFreeNetworkBuffers( );
		if( ( ( cIsLow == 0 ) && ( uxCount <= WARN_LOW ) ) || ( ( cIsLow != 0 ) && ( uxCount >= WARN_HIGH ) ) )
		{
			cIsLow = !cIsLow;
			FreeRTOS_debug_printf( ( "*** Warning *** %s %lu buffers left\n", cIsLow ? "only" : "now", uxCount ) );
		}
	}
	/*-----------------------------------------------------------*/

	UBaseType_t bIsValidNetworkDescriptor( const NetworkBufferDescriptor_t * pxDesc )
	{
		uint32_t offset = ( uint32_t ) ( ((const char *)pxDesc) - ((const char *)xNetworkBuffers) );
		if( ( offset >= sizeof( xNetworkBuffers ) ) ||
			( ( offset % sizeof( xNetworkBuffers[0] ) ) != 0 ) )
			return pdFALSE;
		return (UBaseType_t) (pxDesc - xNetworkBuffers) + 1;
	}
	/*-----------------------------------------------------------*/

#else
	static UBaseType_t bIsValidNetworkDescriptor (const NetworkBufferDescriptor_t * pxDesc)
	{
		( void ) pxDesc;
		return ( UBaseType_t ) pdTRUE;
	}
	/*-----------------------------------------------------------*/

	static void prvShowWarnings( void )
	{
	}
	/*-----------------------------------------------------------*/

#endif /* ipconfigTCP_IP_SANITY */

BaseType_t xNetworkBuffersInitialise( void )
{
BaseType_t xReturn, x;

	/* Only initialise the buffers and their associated kernel objects if they
	have not been initialised before. */
	if( xNetworkBufferSemaphore == NULL )
	{
		/* In case alternative locking is used, the mutexes can be initialised
		here */
		ipconfigBUFFER_ALLOC_INIT();

		xNetworkBufferSemaphore = xSemaphoreCreateCounting( ( UBaseType_t ) ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS, ( UBaseType_t ) ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS );
		configASSERT( xNetworkBufferSemaphore );

		if( xNetworkBufferSemaphore != NULL )
		{
			vListInitialise( &xFreeBuffersList );

			/* Initialise all the network buffers.  The buffer storage comes
			from the network interface, and different hardware has different
			requirements. */
			vNetworkInterfaceAllocateRAMToBuffers( xNetworkBuffers );
			for( x = 0; x < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; x++ )
			{
				/* Initialise and set the owner of the buffer list items. */
				vListInitialiseItem( &( xNetworkBuffers[ x ].xBufferListItem ) );
				listSET_LIST_ITEM_OWNER( &( xNetworkBuffers[ x ].xBufferListItem ), &xNetworkBuffers[ x ] );

				/* Currently, all buffers are available for use. */
				vListInsert( &xFreeBuffersList, &( xNetworkBuffers[ x ].xBufferListItem ) );
			}

			uxMinimumFreeNetworkBuffers = ( UBaseType_t ) ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS;
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

NetworkBufferDescriptor_t *pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes, TickType_t xBlockTimeTicks )
{
NetworkBufferDescriptor_t *pxReturn = NULL;
BaseType_t xInvalid = pdFALSE;
UBaseType_t uxCount;

	/* The current implementation only has a single size memory block, so
	the requested size parameter is not used (yet). */
	( void ) xRequestedSizeBytes;

	if( xNetworkBufferSemaphore != NULL )
	{
		/* If there is a semaphore available, there is a network buffer
		available. */
		if( xSemaphoreTake( xNetworkBufferSemaphore, xBlockTimeTicks ) == pdPASS )
		{
			/* Protect the structure as it is accessed from tasks and
			interrupts. */
			ipconfigBUFFER_ALLOC_LOCK();
			{
				pxReturn = ( NetworkBufferDescriptor_t * ) listGET_OWNER_OF_HEAD_ENTRY( &xFreeBuffersList );

				if( ( bIsValidNetworkDescriptor( pxReturn ) != pdFALSE_UNSIGNED ) &&
					listIS_CONTAINED_WITHIN( &xFreeBuffersList, &( pxReturn->xBufferListItem ) ) )
				{
					uxListRemove( &( pxReturn->xBufferListItem ) );
				}
				else
				{
					xInvalid = pdTRUE;
				}
			}
			ipconfigBUFFER_ALLOC_UNLOCK();

			if( xInvalid == pdTRUE )
			{
				/* _RB_ Can printf() be called from an interrupt?  (comment
				above says this can be called from an interrupt too) */
				/* _HT_ The function shall not be called from an ISR. Comment
				was indeed misleading. Hopefully clear now?
				So the printf()is OK here. */
				FreeRTOS_debug_printf( ( "pxGetNetworkBufferWithDescriptor: INVALID BUFFER: %p (valid %lu)\n",
					pxReturn, bIsValidNetworkDescriptor( pxReturn ) ) );
				pxReturn = NULL;
			}
			else
			{
				/* Reading UBaseType_t, no critical section needed. */
				uxCount = listCURRENT_LIST_LENGTH( &xFreeBuffersList );

				/* For stats, latch the lowest number of network buffers since
				booting. */
				if( uxMinimumFreeNetworkBuffers > uxCount )
				{
					uxMinimumFreeNetworkBuffers = uxCount;
				}

				pxReturn->xDataLength = xRequestedSizeBytes;

				#if( ipconfigTCP_IP_SANITY != 0 )
				{
					prvShowWarnings();
				}
				#endif /* ipconfigTCP_IP_SANITY */

				#if( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
				{
					/* make sure the buffer is not linked */
					pxReturn->pxNextBuffer = NULL;
				}
				#endif /* ipconfigUSE_LINKED_RX_MESSAGES */

				if( xTCPWindowLoggingLevel > 3 )
				{
					FreeRTOS_debug_printf( ( "BUF_GET[%ld]: %p (%p)\n",
						bIsValidNetworkDescriptor( pxReturn ),
						pxReturn, pxReturn->pucEthernetBuffer ) );
				}
			}
			iptraceNETWORK_BUFFER_OBTAINED( pxReturn );
		}
		else
		{
			iptraceFAILED_TO_OBTAIN_NETWORK_BUFFER();
		}
	}

	return pxReturn;
}
/*-----------------------------------------------------------*/

NetworkBufferDescriptor_t *pxNetworkBufferGetFromISR( size_t xRequestedSizeBytes )
{
NetworkBufferDescriptor_t *pxReturn = NULL;

	/* The current implementation only has a single size memory block, so
	the requested size parameter is not used (yet). */
	( void ) xRequestedSizeBytes;

	/* If there is a semaphore available then there is a buffer available, but,
	as this is called from an interrupt, only take a buffer if there are at
	least baINTERRUPT_BUFFER_GET_THRESHOLD buffers remaining.  This prevents,
	to a certain degree at least, a rapidly executing interrupt exhausting
	buffer and in so doing preventing tasks from continuing. */
	if( uxQueueMessagesWaitingFromISR( ( QueueHandle_t ) xNetworkBufferSemaphore ) > ( UBaseType_t ) baINTERRUPT_BUFFER_GET_THRESHOLD )
	{
		if( xSemaphoreTakeFromISR( xNetworkBufferSemaphore, NULL ) == pdPASS )
		{
			/* Protect the structure as it is accessed from tasks and interrupts. */
			ipconfigBUFFER_ALLOC_LOCK_FROM_ISR();
			{
				pxReturn = ( NetworkBufferDescriptor_t * ) listGET_OWNER_OF_HEAD_ENTRY( &xFreeBuffersList );
				uxListRemove( &( pxReturn->xBufferListItem ) );
			}
			ipconfigBUFFER_ALLOC_UNLOCK_FROM_ISR();

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

BaseType_t vNetworkBufferReleaseFromISR( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
BaseType_t xHigherPriorityTaskWoken = pdFALSE;

	/* Ensure the buffer is returned to the list of free buffers before the
	counting semaphore is 'given' to say a buffer is available. */
	ipconfigBUFFER_ALLOC_LOCK_FROM_ISR();
	{
		vListInsertEnd( &xFreeBuffersList, &( pxNetworkBuffer->xBufferListItem ) );
	}
	ipconfigBUFFER_ALLOC_UNLOCK_FROM_ISR();

	xSemaphoreGiveFromISR( xNetworkBufferSemaphore, &xHigherPriorityTaskWoken );
	iptraceNETWORK_BUFFER_RELEASED( pxNetworkBuffer );

	return xHigherPriorityTaskWoken;
}
/*-----------------------------------------------------------*/

void vReleaseNetworkBufferAndDescriptor( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
BaseType_t xListItemAlreadyInFreeList;

	if( bIsValidNetworkDescriptor( pxNetworkBuffer ) == pdFALSE_UNSIGNED )
	{
		FreeRTOS_debug_printf( ( "vReleaseNetworkBufferAndDescriptor: Invalid buffer %p\n", pxNetworkBuffer ) );
		return ;
	}
	/* Ensure the buffer is returned to the list of free buffers before the
	counting semaphore is 'given' to say a buffer is available. */
	ipconfigBUFFER_ALLOC_LOCK();
	{
		{
			xListItemAlreadyInFreeList = listIS_CONTAINED_WITHIN( &xFreeBuffersList, &( pxNetworkBuffer->xBufferListItem ) );

			if( xListItemAlreadyInFreeList == pdFALSE )
			{
				vListInsertEnd( &xFreeBuffersList, &( pxNetworkBuffer->xBufferListItem ) );
			}
		}
	}
	ipconfigBUFFER_ALLOC_UNLOCK();

	if( xListItemAlreadyInFreeList )
	{
		FreeRTOS_debug_printf( ( "vReleaseNetworkBufferAndDescriptor: %p ALREADY RELEASED (now %lu)\n",
			pxNetworkBuffer, uxGetNumberOfFreeNetworkBuffers( ) ) );
	}
	if( xListItemAlreadyInFreeList == pdFALSE )
	{
		xSemaphoreGive( xNetworkBufferSemaphore );
		prvShowWarnings();
		if( xTCPWindowLoggingLevel > 3 )
			FreeRTOS_debug_printf( ( "BUF_PUT[%ld]: %p (%p) (now %lu)\n",
				bIsValidNetworkDescriptor( pxNetworkBuffer ),
				pxNetworkBuffer, pxNetworkBuffer->pucEthernetBuffer,
				uxGetNumberOfFreeNetworkBuffers( ) ) );
	}
	iptraceNETWORK_BUFFER_RELEASED( pxNetworkBuffer );
}
/*-----------------------------------------------------------*/

UBaseType_t uxGetMinimumFreeNetworkBuffers( void )
{
	return uxMinimumFreeNetworkBuffers;
}
/*-----------------------------------------------------------*/

UBaseType_t uxGetNumberOfFreeNetworkBuffers( void )
{
	return listCURRENT_LIST_LENGTH( &xFreeBuffersList );
}

NetworkBufferDescriptor_t *pxResizeNetworkBufferWithDescriptor( NetworkBufferDescriptor_t * pxNetworkBuffer, size_t xNewSizeBytes )
{
	/* In BufferAllocation_1.c all network buffer are allocated with a
	maximum size of 'ipTOTAL_ETHERNET_FRAME_SIZE'.No need to resize the
	network buffer. */
	( void ) xNewSizeBytes;
	return pxNetworkBuffer;
}

/*#endif */ /* ipconfigINCLUDE_TEST_CODE */
