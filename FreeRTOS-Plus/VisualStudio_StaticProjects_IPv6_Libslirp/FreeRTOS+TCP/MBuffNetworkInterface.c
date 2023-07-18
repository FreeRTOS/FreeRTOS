/*
 * FreeRTOS+TCP <DEVELOPMENT BRANCH>
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"
#include "task.h"
#include "message_buffer.h"

#if !defined( _WIN32 )
    #include "wait_for_event.h"
#endif

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"

/* If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 1, then the Ethernet
 * driver will filter incoming packets and only pass the stack those packets it
 * considers need processing. */
#if ( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 )
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eProcessBuffer
#else
    #define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif

#if ipconfigNETWORK_MTU < 1500U
    #error ipconfigNETWORK_MTU must be at least 1500
#endif

#define NETWORK_BUFFER_LEN    ( ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER )

#define xSEND_BUFFER_SIZE     ( 32U * NETWORK_BUFFER_LEN )
#define xRECV_BUFFER_SIZE     ( 32U * NETWORK_BUFFER_LEN )

typedef struct
{
    BaseType_t xInterfaceState;
    MessageBufferHandle_t xSendMsgBuffer;
    MessageBufferHandle_t xRecvMsgBuffer;
    TaskHandle_t xRecvTask;
    void * pvSendEvent;
    void * pvBackendContext;
} MBuffNetDriverContext_t;

extern void vMBuffNetifBackendInit( MessageBufferHandle_t * pxSendMsgBuffer,
                                    MessageBufferHandle_t * pxRecvMsgBuffer,
                                    void * pvSendEvent,
                                    void ** ppvBackendContext );

extern void vMBuffNetifBackendDeInit( void * pvBackendContext );

static void vNetifReceiveTask( void * pvParameters );

/**
 * @brief Initialize the MessageBuffer backed network interface.
 *
 * @return BaseType_t pdTRUE on success
 */
BaseType_t xNetworkInterfaceInitialise( NetworkInterface_t * pxNetif )
{
    BaseType_t xResult = pdTRUE;

    pxNetif->pvArgument = pvPortMalloc( sizeof( MBuffNetDriverContext_t ) );

    if( pxNetif->pvArgument == NULL )
    {
        FreeRTOS_printf( ( "Failed to allocate memory for pxNetif->pvArgument" ) );
        configASSERT( 0 );
    }

    MBuffNetDriverContext_t * pxDriverCtx = ( MBuffNetDriverContext_t * ) pxNetif->pvArgument;

    if( pxDriverCtx->xInterfaceState == pdFALSE )
    {
        pxDriverCtx->xInterfaceState = pdFALSE;

        #if defined( _WIN32 )
            pxDriverCtx->pvSendEvent = CreateEvent( NULL, FALSE, TRUE, NULL );
        #else
            pxDriverCtx->pvSendEvent = ( void * ) event_create();
        #endif

        if( pxDriverCtx->pvSendEvent == NULL )
        {
            xResult = pdFALSE;
        }
        else
        {
            vMBuffNetifBackendInit( &( pxDriverCtx->xSendMsgBuffer ),
                                    &( pxDriverCtx->xRecvMsgBuffer ),
                                    pxDriverCtx->pvSendEvent,
                                    &( pxDriverCtx->pvBackendContext ) );

            if( pxDriverCtx->pvBackendContext == NULL )
            {
                xResult = pdFALSE;
                #if defined( _WIN32 )
                    ( void ) CloseHandle( pxDriverCtx->pvSendEvent );
                #else
                    ( void ) event_delete( pxDriverCtx->pvSendEvent );
                #endif
            }
        }

        static BaseType_t xReceiveTaskCreated = pdFALSE;

        if( ( xResult == pdTRUE ) && ( xReceiveTaskCreated == pdFALSE ) )
        {
            xResult = xTaskCreate( vNetifReceiveTask, "NetRX",
                                   configMINIMAL_STACK_SIZE,
                                   pxNetif,
                                   tskIDLE_PRIORITY,
                                   &( pxDriverCtx->xRecvTask ) );

            if( xResult == pdPASS )
            {
                xReceiveTaskCreated = pdTRUE;
            }
        }

        /* Cleanup on failure */
        if( xResult != pdTRUE )
        {
            if( pxDriverCtx->pvSendEvent != NULL )
            {
                #if defined( _WIN32 )
                    ( void ) CloseHandle( pxDriverCtx->pvSendEvent );
                #else
                    event_delete( pxDriverCtx->pvSendEvent );
                #endif
            }

            if( pxDriverCtx->pvBackendContext != NULL )
            {
                vMBuffNetifBackendDeInit( pxDriverCtx->pvBackendContext );
            }
        }

        pxDriverCtx->xInterfaceState = xResult;
    }

    return xResult;
}

/**
 * @brief Deinitialize the message buffer backed network interface.
 *
 * @return BaseType_t pdTRUE
 */
BaseType_t xNetworkInterfaceDeInitialise( NetworkInterface_t * pxNetif )
{
    MBuffNetDriverContext_t * pxDriverCtx = ( MBuffNetDriverContext_t * ) pxNetif->pvArgument;

    #if defined( _WIN32 )
        ( void ) CloseHandle( pxDriverCtx->pvSendEvent );
    #else
        event_delete( pxDriverCtx->pvSendEvent );
    #endif

    vTaskDelete( pxDriverCtx->xRecvTask );

    vMBuffNetifBackendDeInit( pxDriverCtx->pvBackendContext );

    vPortFree( pxNetif->pvArgument );

    return pdTRUE;
}

/*!
 * @brief FreeRTOS task which reads from xRecvMsgBuffer and passes new frames to FreeRTOS+TCP.
 * @param [in] pvParameters not used
 */
static void vNetifReceiveTask( void * pvParameters )
{
    NetworkBufferDescriptor_t * pxDescriptor = NULL;
    NetworkInterface_t * pxNetif = ( NetworkInterface_t * ) pvParameters;

    MBuffNetDriverContext_t * pxDriverCtx = ( MBuffNetDriverContext_t * ) pxNetif->pvArgument;

    for( ; ; )
    {
        size_t uxMessageLen;

        while( pxDescriptor == NULL )
        {
            /* Wait for an MTU + header sized buffer */
            pxDescriptor = pxGetNetworkBufferWithDescriptor( NETWORK_BUFFER_LEN, portMAX_DELAY );
            configASSERT( pxDescriptor->xDataLength >= NETWORK_BUFFER_LEN );
        }

        /* Read an incoming frame */
        uxMessageLen = xMessageBufferReceive( pxDriverCtx->xRecvMsgBuffer,
                                              pxDescriptor->pucEthernetBuffer,
                                              pxDescriptor->xDataLength,
                                              portMAX_DELAY );

        if( uxMessageLen > 0 )
        {
            IPStackEvent_t xRxEvent;
            eFrameProcessingResult_t xFrameProcess;

            pxDescriptor->xDataLength = uxMessageLen;

            /* eConsiderFrameForProcessing is interrupt safe */
            xFrameProcess = ipCONSIDER_FRAME_FOR_PROCESSING( pxDescriptor->pucEthernetBuffer );

            if( xFrameProcess != eProcessBuffer )
            {
                FreeRTOS_debug_printf( ( "Dropping RX frame of length: %lu. eConsiderFrameForProcessing returned %lu.\n",
                                         uxMessageLen, xFrameProcess ) );
            }

            pxDescriptor->pxInterface = pxNetif;
            pxDescriptor->pxEndPoint = FreeRTOS_MatchingEndpoint( pxNetif, pxDescriptor->pucEthernetBuffer );

            xRxEvent.eEventType = eNetworkRxEvent;
            xRxEvent.pvData = ( void * ) pxDescriptor;

            if( xSendEventStructToIPTask( &xRxEvent, 0U ) == pdTRUE )
            {
                iptraceNETWORK_INTERFACE_RECEIVE();

                /* Clear pxDescriptor so that the task requests a new buffer */
                pxDescriptor = NULL;
            }
            else
            {
                FreeRTOS_debug_printf( ( "Dropping TX frame of length: %lu. FreeRTOS+TCP event queue is full.\n",
                                         pxDescriptor->xDataLength ) );
                /* Drop the frame and reuse the descriptor for the next incomming frame */
                iptraceETHERNET_RX_EVENT_LOST();
            }
        }
        else
        {
            /*
             * xMessageBufferReceive returned zero.
             */
        }
    }
}

/*!
 * @brief API call, called from FreeRTOS_IP.c to send a network packet over the
 *        selected interface
 * @return pdTRUE if successful else pdFALSE
 */
BaseType_t xNetworkInterfaceOutput( NetworkInterface_t * pxNetif,
                                    NetworkBufferDescriptor_t * const pxNetworkBuffer,
                                    BaseType_t xReleaseAfterSend )
{
    BaseType_t xResult = pdFALSE;

    MBuffNetDriverContext_t * pxDriverCtx = ( MBuffNetDriverContext_t * ) pxNetif->pvArgument;

    FreeRTOS_debug_printf( ( "xNetworkInterfaceOutput: %p:%p\n", pxNetworkBuffer, pxNetworkBuffer->pucEthernetBuffer ) );

    if( pxDriverCtx->xInterfaceState == pdTRUE )
    {
        configASSERT( pxNetworkBuffer != NULL );
        configASSERT( pxNetworkBuffer->pucEthernetBuffer != NULL );
        configASSERT( pxNetworkBuffer->xDataLength >= sizeof( EthernetHeader_t ) );

        if( xMessageBufferSpacesAvailable( pxDriverCtx->xSendMsgBuffer ) > pxNetworkBuffer->xDataLength + 4U )
        {
            size_t uxBytesSent;
            uxBytesSent = xMessageBufferSend( pxDriverCtx->xSendMsgBuffer,
                                              pxNetworkBuffer->pucEthernetBuffer,
                                              pxNetworkBuffer->xDataLength,
                                              0U );
            ( void ) uxBytesSent;
            configASSERT( uxBytesSent == pxNetworkBuffer->xDataLength );
            xResult = pdTRUE;
        }
        else
        {
            FreeRTOS_debug_printf( ( "Dropping TX frame of length: %lu. xSendMsgBuffer is full.\n",
                                     pxNetworkBuffer->xDataLength ) );
        }

        iptraceNETWORK_INTERFACE_TRANSMIT();

        if( xReleaseAfterSend != pdFALSE )
        {
            vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
        }

        if( xResult == pdTRUE )
        {
            #if defined( _WIN32 )
                SetEvent( pxDriverCtx->pvSendEvent );
            #else
                event_signal( pxDriverCtx->pvSendEvent );
            #endif
        }
    }

    return xResult;
}

#define BUFFER_SIZE               ( ipTOTAL_ETHERNET_FRAME_SIZE + ipBUFFER_PADDING )
#define BUFFER_SIZE_ROUNDED_UP    ( ( BUFFER_SIZE + 7 ) & ~0x07UL )

/*!
 * @brief Allocate RAM for packet buffers and set the pucEthernetBuffer field for each descriptor.
 *        Called when the BufferAllocation1 scheme is used.
 * @param [in,out] pxNetworkBuffers Pointer to an array of NetworkBufferDescriptor_t to populate.
 */
void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    static uint8_t * pucNetworkPacketBuffers = NULL;
    size_t uxIndex;

    if( pucNetworkPacketBuffers == NULL )
    {
        pucNetworkPacketBuffers = ( uint8_t * ) malloc( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS * BUFFER_SIZE_ROUNDED_UP );
    }

    if( pucNetworkPacketBuffers == NULL )
    {
        FreeRTOS_printf( ( "Failed to allocate memory for pxNetworkBuffers" ) );
        configASSERT( 0 );
    }
    else
    {
        for( uxIndex = 0; uxIndex < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; uxIndex++ )
        {
            size_t uxOffset = uxIndex * BUFFER_SIZE_ROUNDED_UP;
            NetworkBufferDescriptor_t ** ppDescriptor;

            /* At the beginning of each pbuff is a pointer to the relevant descriptor */
            ppDescriptor = ( NetworkBufferDescriptor_t ** ) &( pucNetworkPacketBuffers[ uxOffset ] );

            /* Set this pointer to the address of the correct descriptor */
            *ppDescriptor = &( pxNetworkBuffers[ uxIndex ] );

            /* pucEthernetBuffer is set to point ipBUFFER_PADDING bytes in from the
             * beginning of the allocated buffer. */
            pxNetworkBuffers[ uxIndex ].pucEthernetBuffer = &( pucNetworkPacketBuffers[ uxOffset + ipBUFFER_PADDING ] );
        }
    }
}

BaseType_t xGetPhyLinkStatus( NetworkInterface_t * pxNetif )
{
    BaseType_t xResult = pdFALSE;

    MBuffNetDriverContext_t * pxDriverCtx = ( MBuffNetDriverContext_t * ) pxNetif->pvArgument;

    if( pxDriverCtx->xInterfaceState == pdTRUE )
    {
        xResult = pdTRUE;
    }

    return xResult;
}

NetworkInterface_t * pxFillInterfaceDescriptor( BaseType_t xEMACIndex,
                                                NetworkInterface_t * pxInterface )
{
    configASSERT( pxInterface != NULL );
    static char pcName[ 17 ];

    snprintf( pcName, sizeof( pcName ), "eth%ld", xEMACIndex );

    memset( pxInterface, 0, sizeof( NetworkInterface_t ) );

    pxInterface->pcName = pcName;                    /* Just for logging, debugging. */
    pxInterface->pvArgument = ( void * ) xEMACIndex; /* Has only meaning for the driver functions. */
    pxInterface->pfInitialise = xNetworkInterfaceInitialise;
    pxInterface->pfOutput = xNetworkInterfaceOutput;
    pxInterface->pfGetPhyLinkStatus = xGetPhyLinkStatus;

    FreeRTOS_AddNetworkInterface( pxInterface );

    return pxInterface;
}
