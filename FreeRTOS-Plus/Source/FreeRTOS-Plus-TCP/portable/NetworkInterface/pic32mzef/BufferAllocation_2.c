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

/* THIS FILE SHOULD NOT BE USED IF THE PROJECT INCLUDES A MEMORY ALLOCATOR
 * THAT WILL FRAGMENT THE HEAP MEMORY.  For example, heap_2 must not be used,
 * heap_4 can be used. */

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "NetworkInterface.h"
#include "NetworkBufferManagement.h"

#include "tcpip/tcpip.h"
#include "tcpip/src/tcpip_private.h"

#include "NetworkConfig.h"

/* The obtained network buffer must be large enough to hold a packet that might
 * replace the packet that was requested to be sent. */
#if ipconfigUSE_TCP == 1
    #define baMINIMAL_BUFFER_SIZE    sizeof( TCPPacket_t )
#else
    #define baMINIMAL_BUFFER_SIZE    sizeof( ARPPacket_t )
#endif /* ipconfigUSE_TCP == 1 */

/*_RB_ This is too complex not to have an explanation. */
#if defined( ipconfigETHERNET_MINIMUM_PACKET_BYTES )
    #define ASSERT_CONCAT_( a, b )    a ## b
    #define ASSERT_CONCAT( a, b )     ASSERT_CONCAT_( a, b )
    #define STATIC_ASSERT( e ) \
    ; enum { ASSERT_CONCAT( assert_line_, __LINE__ ) = 1 / ( !!( e ) ) }

    STATIC_ASSERT( ipconfigETHERNET_MINIMUM_PACKET_BYTES <= baMINIMAL_BUFFER_SIZE );
#endif

/* A list of free (available) NetworkBufferDescriptor_t structures. */
static List_t xFreeBuffersList;

/* Some statistics about the use of buffers. */
static size_t uxMinimumFreeNetworkBuffers;

/* Declares the pool of NetworkBufferDescriptor_t structures that are available
 * to the system.  All the network buffers referenced from xFreeBuffersList exist
 * in this array.  The array is not accessed directly except during initialisation,
 * when the xFreeBuffersList is filled (as all the buffers are free when the system
 * is booted). */
static NetworkBufferDescriptor_t xNetworkBufferDescriptors[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ];

/* This constant is defined as false to let FreeRTOS_TCP_IP.c know that the
 * network buffers have a variable size: resizing may be necessary */
const BaseType_t xBufferAllocFixedSize = pdFALSE;

/* The semaphore used to obtain network buffers. */
static SemaphoreHandle_t xNetworkBufferSemaphore = NULL;

/*-----------------------------------------------------------*/

#ifdef PIC32_USE_ETHERNET

    /* PIC32 specific stuff */
    /* */

    /* MAC packet acknowledgment, once MAC is done with it */
        static bool PIC32_MacPacketAcknowledge( TCPIP_MAC_PACKET * pPkt,
                                                const void * param );

    /* allocates a MAC packet that holds a data buffer that can be used by both: */
    /*  - the FreeRTOSIP (NetworkBufferDescriptor_t->pucEthernetBuffer) */
    /*  - the Harmony MAC driver: TCPIP_MAC_PACKET->pDSeg->segLoad */
    /* from the beginning of the buffer: */
    /*      - 4 bytes pointer to the network descriptor (FreeRTOS) */
    /*      - 4 bytes pointer to the MAC packet (pic32_NetworkInterface.c) */
    /*      - 2 bytes offset from the MAC packet (Harmony MAC driver: segLoadOffset) */
    /* */
    /* NOTE: segLoadLen should NOT include: */
    /*          - the TCPIP_MAC_FRAME_OFFSET (== ipBUFFER_PADDING which should be == 10!) */
    /*          - the sizeof(TCPIP_MAC_ETHERNET_HEADER) */
    /*       These are added by the MAC packet allocation! */
    /* */
    static uint8_t * PIC32_PktAlloc( uint16_t pktLen,
                                     uint16_t segLoadLen,
                                     TCPIP_MAC_PACKET_ACK_FUNC ackF,
                                     TCPIP_MAC_PACKET ** pPtrPkt )
    {
        uint8_t * pBuff = 0;

        /* allocate standard packet */
        TCPIP_MAC_PACKET * pPkt = TCPIP_PKT_PacketAlloc( pktLen, segLoadLen, 0 );

        /* set the MAC packet pointer in the packet */
        if( pPkt != 0 )
        {
            pBuff = pPkt->pDSeg->segLoad;
            TCPIP_MAC_PACKET ** ppkt = ( TCPIP_MAC_PACKET ** ) ( pBuff - PIC32_BUFFER_PKT_PTR_OSSET );
            configASSERT( ( ( uint32_t ) ppkt & ( sizeof( uint32_t ) - 1 ) ) == 0 );
            *ppkt = pPkt; /* store the packet it comes from */
            pPkt->ackFunc = ackF;
            pPkt->ackParam = 0;
        }

        if( pPtrPkt != 0 )
        {
            *pPtrPkt = pPkt;
        }

        return pBuff;
    }



    /* standard PIC32 MAC allocation function for a MAC packet */
    /* this packet saves room for the FreeRTOS network descriptor */
    /* at the beginning of the data buffer */
    /* see NetworkBufferAllocate */
    /* Note: flags parameter is ignored since that's used in the Harmony stack only */
    TCPIP_MAC_PACKET * PIC32_MacPacketAllocate( uint16_t pktLen,
                                                uint16_t segLoadLen,
                                                TCPIP_MAC_PACKET_FLAGS flags )
    {
        TCPIP_MAC_PACKET * pPkt;

        PIC32_PktAlloc( pktLen, segLoadLen, 0, &pPkt );

        return pPkt;
    }

    /* standard PIC32 MAC packet acknowledgment */
    /* function called once MAC is done with it */
    static bool PIC32_MacPacketAcknowledge( TCPIP_MAC_PACKET * pPkt,
                                            const void * param )
    {
        configASSERT( ( pPkt != 0 ) );

        TCPIP_PKT_PacketFree( pPkt );

        return false;
    }

    /* associates the current MAC packet with a network descriptor */
    /* mainly for RX packet */
    void PIC32_MacAssociate( TCPIP_MAC_PACKET * pRxPkt,
                             NetworkBufferDescriptor_t * pxBufferDescriptor,
                             size_t pktLength )
    {
        uint8_t * pPktBuff = pRxPkt->pDSeg->segLoad;

        pxBufferDescriptor->pucEthernetBuffer = pPktBuff;
        pxBufferDescriptor->xDataLength = pktLength;

        /* make sure this is a properly allocated packet */
        TCPIP_MAC_PACKET ** ppkt = ( TCPIP_MAC_PACKET ** ) ( pPktBuff - PIC32_BUFFER_PKT_PTR_OSSET );
        configASSERT( ( ( uint32_t ) ppkt & ( sizeof( uint32_t ) - 1 ) ) == 0 );

        if( *ppkt != pRxPkt )
        {
            configASSERT( false );
        }

        /* set the proper descriptor info */
        NetworkBufferDescriptor_t ** ppDcpt = ( NetworkBufferDescriptor_t ** ) ( pPktBuff - ipBUFFER_PADDING );
        configASSERT( ( ( uint32_t ) ppDcpt & ( sizeof( uint32_t ) - 1 ) ) == 0 );
        *ppDcpt = pxBufferDescriptor;
    }

    /* debug functionality */
    void PIC32_MacPacketOrphan( TCPIP_MAC_PACKET * pPkt )
    {
        TCPIP_PKT_PacketFree( pPkt );
        configASSERT( false );
    }

    /* FreeRTOS allocation functions */

    /* allocates a buffer that can be used by both: */
    /*  - the FreeRTOSIP (NetworkBufferDescriptor_t->pucEthernetBuffer) */
    /*  - the Harmony MAC driver: TCPIP_MAC_PACKET */
    /*  See PIC32_PktAlloc for details */
    /* */
    /* NOTE: reqLength should NOT include the ipBUFFER_PADDING (which should be == 10!) */
    /*       or the sizeof(TCPIP_MAC_ETHERNET_HEADER) */
    /*       These are added by the MAC packet allocation! */
    /* */
    uint8_t * NetworkBufferAllocate( size_t reqLength )
    {
        return PIC32_PktAlloc( sizeof( TCPIP_MAC_PACKET ), reqLength, PIC32_MacPacketAcknowledge, 0 );
    }

    /* deallocates a network buffer previously allocated */
    /* with NetworkBufferAllocate */
    void NetworkBufferFree( uint8_t * pNetworkBuffer )
    {
        if( pNetworkBuffer != 0 )
        {
            TCPIP_MAC_PACKET ** ppkt = ( TCPIP_MAC_PACKET ** ) ( pNetworkBuffer - PIC32_BUFFER_PKT_PTR_OSSET );
            configASSERT( ( ( uint32_t ) ppkt & ( sizeof( uint32_t ) - 1 ) ) == 0 );
            TCPIP_MAC_PACKET * pPkt = *ppkt;
            configASSERT( ( pPkt != 0 ) );

            if( pPkt->ackFunc != 0 )
            {
                ( *pPkt->ackFunc )( pPkt, pPkt->ackParam );
            }
            else
            { /* ??? */
                PIC32_MacPacketOrphan( pPkt );
            }
        }
    }

#endif /* #ifdef PIC32_USE_ETHERNET */

/*-----------------------------------------------------------*/

BaseType_t xNetworkBuffersInitialise( void )
{
    BaseType_t xReturn, x;

    /* Only initialise the buffers and their associated kernel objects if they
     * have not been initialised before. */
    if( xNetworkBufferSemaphore == NULL )
    {
        xNetworkBufferSemaphore = xSemaphoreCreateCounting( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS, ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS );
        configASSERT( xNetworkBufferSemaphore );

        if( xNetworkBufferSemaphore != NULL )
        {
            #if ( configQUEUE_REGISTRY_SIZE > 0 )
                {
                    vQueueAddToRegistry( xNetworkBufferSemaphore, "NetBufSem" );
                }
            #endif /* configQUEUE_REGISTRY_SIZE */

            /* If the trace recorder code is included name the semaphore for viewing
             * in FreeRTOS+Trace.  */
            #if ( ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS == 1 )
                {
                    extern QueueHandle_t xNetworkEventQueue;
                    vTraceSetQueueName( xNetworkEventQueue, "IPStackEvent" );
                    vTraceSetQueueName( xNetworkBufferSemaphore, "NetworkBufferCount" );
                }
            #endif /*  ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS == 1 */

            vListInitialise( &xFreeBuffersList );

            /* Initialise all the network buffers.  No storage is allocated to
             * the buffers yet. */
            for( x = 0; x < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; x++ )
            {
                /* Initialise and set the owner of the buffer list items. */
                xNetworkBufferDescriptors[ x ].pucEthernetBuffer = NULL;
                vListInitialiseItem( &( xNetworkBufferDescriptors[ x ].xBufferListItem ) );
                listSET_LIST_ITEM_OWNER( &( xNetworkBufferDescriptors[ x ].xBufferListItem ), &xNetworkBufferDescriptors[ x ] );

                /* Currently, all buffers are available for use. */
                vListInsert( &xFreeBuffersList, &( xNetworkBufferDescriptors[ x ].xBufferListItem ) );
            }

            uxMinimumFreeNetworkBuffers = ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS;
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

uint8_t * pucGetNetworkBuffer( size_t * pxRequestedSizeBytes )
{
    uint8_t * pucEthernetBuffer;
    size_t xSize = *pxRequestedSizeBytes;

    if( xSize < baMINIMAL_BUFFER_SIZE )
    {
        /* Buffers must be at least large enough to hold a TCP-packet with
         * headers, or an ARP packet, in case TCP is not included. */
        xSize = baMINIMAL_BUFFER_SIZE;
    }

    /* Round up xSize to the nearest multiple of N bytes,
     * where N equals 'sizeof( size_t )'. */
    if( ( xSize & ( sizeof( size_t ) - 1u ) ) != 0u )
    {
        xSize = ( xSize | ( sizeof( size_t ) - 1u ) ) + 1u;
    }

    *pxRequestedSizeBytes = xSize;

    /* Allocate a buffer large enough to store the requested Ethernet frame size
     * and a pointer to a network buffer structure (hence the addition of
     * ipBUFFER_PADDING bytes). */

    #ifdef PIC32_USE_ETHERNET
        pucEthernetBuffer = NetworkBufferAllocate( xSize - sizeof( TCPIP_MAC_ETHERNET_HEADER ) );
    #else
        pucEthernetBuffer = ( uint8_t * ) pvPortMalloc( xSize + ipBUFFER_PADDING );
    #endif /* #ifdef PIC32_USE_ETHERNET */

    configASSERT( pucEthernetBuffer );

    if( pucEthernetBuffer != NULL )
    {
        /* Enough space is left at the start of the buffer to place a pointer to
         * the network buffer structure that references this Ethernet buffer.
         * Return a pointer to the start of the Ethernet buffer itself. */
		#ifndef PIC32_USE_ETHERNET
        	pucEthernetBuffer += ipBUFFER_PADDING;
		#endif /* #ifndef PIC32_USE_ETHERNET */
    }

    return pucEthernetBuffer;
}
/*-----------------------------------------------------------*/

void vReleaseNetworkBuffer( uint8_t * pucEthernetBuffer )
{
    /* There is space before the Ethernet buffer in which a pointer to the
     * network buffer that references this Ethernet buffer is stored.  Remove the
     * space before freeing the buffer. */
    #ifdef PIC32_USE_ETHERNET
        NetworkBufferFree( pucEthernetBuffer );
    #else
        if( pucEthernetBuffer != NULL )
        {
            pucEthernetBuffer -= ipBUFFER_PADDING;
            vPortFree( ( void * ) pucEthernetBuffer );
        }
    #endif /* #ifdef PIC32_USE_ETHERNET */
}
/*-----------------------------------------------------------*/

NetworkBufferDescriptor_t * pxGetNetworkBufferWithDescriptor( size_t xRequestedSizeBytes,
                                                              TickType_t xBlockTimeTicks )
{
    NetworkBufferDescriptor_t * pxReturn = NULL;
    size_t uxCount;

    if( ( xRequestedSizeBytes != 0u ) && ( xRequestedSizeBytes < ( size_t ) baMINIMAL_BUFFER_SIZE ) )
    {
        /* ARP packets can replace application packets, so the storage must be
         * at least large enough to hold an ARP. */
        xRequestedSizeBytes = baMINIMAL_BUFFER_SIZE;
    }

	#ifdef PIC32_USE_ETHERNET
	if( xRequestedSizeBytes != 0u )
    {
	#endif /* #ifdef PIC32_USE_ETHERNET */
    	xRequestedSizeBytes += 2u;

    	if( ( xRequestedSizeBytes & ( sizeof( size_t ) - 1u ) ) != 0u )
    	{
        	xRequestedSizeBytes = ( xRequestedSizeBytes | ( sizeof( size_t ) - 1u ) ) + 1u;
    	}
	#ifdef PIC32_USE_ETHERNET
    }
	#endif /* #ifdef PIC32_USE_ETHERNET */

    /* If there is a semaphore available, there is a network buffer available. */
    if( xSemaphoreTake( xNetworkBufferSemaphore, xBlockTimeTicks ) == pdPASS )
    {
        /* Protect the structure as it is accessed from tasks and interrupts. */
        taskENTER_CRITICAL();
        {
            pxReturn = ( NetworkBufferDescriptor_t * ) listGET_OWNER_OF_HEAD_ENTRY( &xFreeBuffersList );
            uxListRemove( &( pxReturn->xBufferListItem ) );
        }
        taskEXIT_CRITICAL();

        /* Reading UBaseType_t, no critical section needed. */
        uxCount = listCURRENT_LIST_LENGTH( &xFreeBuffersList );

        if( uxMinimumFreeNetworkBuffers > uxCount )
        {
            uxMinimumFreeNetworkBuffers = uxCount;
        }

        /* Allocate storage of exactly the requested size to the buffer. */
        configASSERT( pxReturn->pucEthernetBuffer == NULL );

        if( xRequestedSizeBytes > 0 )
        {
            /* Extra space is obtained so a pointer to the network buffer can
             * be stored at the beginning of the buffer. */

            #ifdef PIC32_USE_ETHERNET
                pxReturn->pucEthernetBuffer = NetworkBufferAllocate( xRequestedSizeBytes - sizeof( TCPIP_MAC_ETHERNET_HEADER ) );
            #else
                pxReturn->pucEthernetBuffer = ( uint8_t * ) pvPortMalloc( xRequestedSizeBytes + ipBUFFER_PADDING );
            #endif /* #ifdef PIC32_USE_ETHERNET */

            if( pxReturn->pucEthernetBuffer == NULL )
            {
                /* The attempt to allocate storage for the buffer payload failed,
                 * so the network buffer structure cannot be used and must be
                 * released. */
                vReleaseNetworkBufferAndDescriptor( pxReturn );
                pxReturn = NULL;
            }
            else
            {
                /* Store a pointer to the network buffer structure in the
                 * buffer storage area, then move the buffer pointer on past the
                 * stored pointer so the pointer value is not overwritten by the
                 * application when the buffer is used. */
                #ifdef PIC32_USE_ETHERNET
                    *( ( NetworkBufferDescriptor_t ** ) ( pxReturn->pucEthernetBuffer - ipBUFFER_PADDING ) ) = pxReturn;
                #else
                    *( ( NetworkBufferDescriptor_t ** ) ( pxReturn->pucEthernetBuffer ) ) = pxReturn;
                    pxReturn->pucEthernetBuffer += ipBUFFER_PADDING;
                #endif /* #ifdef PIC32_USE_ETHERNET */

                /* Store the actual size of the allocated buffer, which may be
                 * greater than the original requested size. */
                pxReturn->xDataLength = xRequestedSizeBytes;

                #if ( ipconfigUSE_LINKED_RX_MESSAGES != 0 )
                    {
                        /* make sure the buffer is not linked */
                        pxReturn->pxNextBuffer = NULL;
                    }
                #endif /* ipconfigUSE_LINKED_RX_MESSAGES */
            }
        }
        else
        {
            /* A descriptor is being returned without an associated buffer being
             * allocated. */
        }
    }

    if( pxReturn == NULL )
    {
        iptraceFAILED_TO_OBTAIN_NETWORK_BUFFER();
    }
    else
    {
        iptraceNETWORK_BUFFER_OBTAINED( pxReturn );
    }

    return pxReturn;
}
/*-----------------------------------------------------------*/

void vReleaseNetworkBufferAndDescriptor( NetworkBufferDescriptor_t * const pxNetworkBuffer )
{
    BaseType_t xListItemAlreadyInFreeList;

    /* Ensure the buffer is returned to the list of free buffers before the
    * counting semaphore is 'given' to say a buffer is available.  Release the
    * storage allocated to the buffer payload.  THIS FILE SHOULD NOT BE USED
    * IF THE PROJECT INCLUDES A MEMORY ALLOCATOR THAT WILL FRAGMENT THE HEAP
    * MEMORY.  For example, heap_2 must not be used, heap_4 can be used. */
    vReleaseNetworkBuffer( pxNetworkBuffer->pucEthernetBuffer );
    pxNetworkBuffer->pucEthernetBuffer = NULL;

    taskENTER_CRITICAL();
    {
        xListItemAlreadyInFreeList = listIS_CONTAINED_WITHIN( &xFreeBuffersList, &( pxNetworkBuffer->xBufferListItem ) );

        if( xListItemAlreadyInFreeList == pdFALSE )
        {
            vListInsertEnd( &xFreeBuffersList, &( pxNetworkBuffer->xBufferListItem ) );
        }
    }
    taskEXIT_CRITICAL();

    /*
     * Update the network state machine, unless the program fails to release its 'xNetworkBufferSemaphore'.
     * The program should only try to release its semaphore if 'xListItemAlreadyInFreeList' is false.
     */
    if( xListItemAlreadyInFreeList == pdFALSE )
    {
        if ( xSemaphoreGive( xNetworkBufferSemaphore ) == pdTRUE )
        {
            iptraceNETWORK_BUFFER_RELEASED( pxNetworkBuffer );
        }
    }
    else
    {
        iptraceNETWORK_BUFFER_RELEASED( pxNetworkBuffer );
    }
}
/*-----------------------------------------------------------*/

/*
 * Returns the number of free network buffers
 */
UBaseType_t uxGetNumberOfFreeNetworkBuffers( void )
{
    return listCURRENT_LIST_LENGTH( &xFreeBuffersList );
}
/*-----------------------------------------------------------*/

UBaseType_t uxGetMinimumFreeNetworkBuffers( void )
{
    return uxMinimumFreeNetworkBuffers;
}
/*-----------------------------------------------------------*/

NetworkBufferDescriptor_t * pxResizeNetworkBufferWithDescriptor( NetworkBufferDescriptor_t * pxNetworkBuffer,
                                                                 size_t xNewSizeBytes )
{
    size_t xOriginalLength;
    uint8_t * pucBuffer;

    #ifdef PIC32_USE_ETHERNET
        xOriginalLength = pxNetworkBuffer->xDataLength;
    #else
        xOriginalLength = pxNetworkBuffer->xDataLength + ipBUFFER_PADDING;
		xNewSizeBytes = xNewSizeBytes + ipBUFFER_PADDING;
    #endif /* #ifdef PIC32_USE_ETHERNET */
	
    pucBuffer = pucGetNetworkBuffer( &( xNewSizeBytes ) );

    if( pucBuffer == NULL )
    {
        /* In case the allocation fails, return NULL. */
        pxNetworkBuffer = NULL;
    }
    else
    {
        pxNetworkBuffer->xDataLength = xNewSizeBytes;
        if( xNewSizeBytes > xOriginalLength )
        {
            xNewSizeBytes = xOriginalLength;
        }

        #ifdef PIC32_USE_ETHERNET
            memcpy( pucBuffer, pxNetworkBuffer->pucEthernetBuffer, xNewSizeBytes );
            *( ( NetworkBufferDescriptor_t ** ) ( pucBuffer - ipBUFFER_PADDING ) ) = pxNetworkBuffer;
        #else
            memcpy( pucBuffer - ipBUFFER_PADDING, pxNetworkBuffer->pucEthernetBuffer - ipBUFFER_PADDING, xNewSizeBytes );
        #endif /* #ifdef PIC32_USE_ETHERNET */

        vReleaseNetworkBuffer( pxNetworkBuffer->pucEthernetBuffer );
        pxNetworkBuffer->pucEthernetBuffer = pucBuffer;
    }

    return pxNetworkBuffer;
}
