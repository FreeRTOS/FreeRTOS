/*
FreeRTOS+TCP V2.0.11
Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

 http://aws.amazon.com/freertos
 http://www.FreeRTOS.org
*/

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"
#include "queue.h"
#include "semphr.h"
#include "task.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"


#include "m480_eth.h"

/* If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 1, then the Ethernet
driver will filter incoming packets and only pass the stack those packets it
considers need processing. */
#if( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 )
#define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer ) eProcessBuffer
#else
#define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer ) eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif

/* Default the size of the stack used by the EMAC deferred handler task to twice
the size of the stack used by the idle task - but allow this to be overridden in
FreeRTOSConfig.h as configMINIMAL_STACK_SIZE is a user definable constant. */
#ifndef configEMAC_TASK_STACK_SIZE
    #define configEMAC_TASK_STACK_SIZE ( 2 * configMINIMAL_STACK_SIZE )
#endif


static SemaphoreHandle_t xTXMutex = NULL;

/* The handle of the task that processes Rx packets.  The handle is required so
the task can be notified when new packets arrive. */
static TaskHandle_t xRxHanderTask = NULL;
static TimerHandle_t xPhyHandlerTask = NULL;
/*
 * A task that processes received frames.
 */
static void prvEMACHandlerTask( void *pvParameters );
static void prvPhyTmrCallback( TimerHandle_t xTimer );

/* The size of each buffer when BufferAllocation_1 is used:
http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/Embedded_Ethernet_Buffer_Management.html */

#define niBUFFER_1_PACKET_SIZE        1536
#ifdef __ICCARM__
#pragma data_alignment=4
static uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS * niBUFFER_1_PACKET_SIZE ]
#else
static uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS * niBUFFER_1_PACKET_SIZE ] __attribute__ ((aligned(4)));
#endif

BaseType_t xNetworkInterfaceInitialise( void )
{
    uint8_t hwaddr[6];
    BaseType_t xReturn = pdPASS;

    /* Init ETH */
    numaker_mac_address(hwaddr);
    FreeRTOS_UpdateMACAddress(hwaddr);
    FreeRTOS_printf( ("mac address %02x-%02x-%02x-%02x-%02x-%02x \r\n", hwaddr[0], hwaddr[1],hwaddr[2],hwaddr[3],hwaddr[4],hwaddr[5]) );
    /* Enable clock & set EMAC configuration         */
    /* Enable MAC and DMA transmission and reception */
    if( numaker_eth_init(hwaddr) < 0)
    {
        xReturn = pdFAIL;
    } else {
        xReturn = pdPASS;
        /* Guard against the task being created more than once and the
        descriptors being initialized more than once. */
        /* Timer task to monitor PHY Link status */
        if( xPhyHandlerTask == NULL )
        {
            xPhyHandlerTask = xTimerCreate( "TimerPhy",  pdMS_TO_TICKS( 1000 ), pdTRUE, 0, prvPhyTmrCallback );
            configASSERT(xPhyHandlerTask);
            xReturn = xTimerStart( xPhyHandlerTask, 0 ) ;
            configASSERT( xReturn );
        }
        /* Rx task */
        if( xRxHanderTask == NULL )
        {
            xReturn = xTaskCreate( prvEMACHandlerTask, "EMAC", configEMAC_TASK_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xRxHanderTask );
            configASSERT( xReturn );
        }
        
        if( xTXMutex == NULL )
        {
            xTXMutex = xSemaphoreCreateMutex();
            configASSERT( xTXMutex );
        }        
    }

        NVIC_SetPriority( EMAC_RX_IRQn, configMAC_INTERRUPT_PRIORITY );
        NVIC_SetPriority( EMAC_TX_IRQn, configMAC_INTERRUPT_PRIORITY );

        numaker_eth_enable_interrupts();

        FreeRTOS_printf( ("ETH-RX priority:%d\n",NVIC_GetPriority( EMAC_RX_IRQn)) );

    return xReturn;
}

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxDescriptor, BaseType_t xReleaseAfterSend )
{
    uint8_t *buffer=NULL;
//    FreeRTOS_printf(("<-- dataLength=%d\n",pxDescriptor->xDataLength));
    if( pxDescriptor->xDataLength >= PACKET_BUFFER_SIZE )
    {
        FreeRTOS_printf(("TX buffer length %d over %d\n", pxDescriptor->xDataLength, PACKET_BUFFER_SIZE));
        return pdFALSE;
    }
    
    buffer = numaker_eth_get_tx_buf();
    if( buffer == NULL )
    {
        NU_DEBUGF(("Eth TX slots are busy\n"));
        return pdFALSE;
    }    
    
    /* Get exclusive access */
    xSemaphoreTake(xTXMutex, portMAX_DELAY);
    NU_DEBUGF(("%s ... buffer=0x%x\r\n",__FUNCTION__, buffer));   
    //SendData: pt = pxDescriptor->pucBuffer, length = pxDescriptor->xDataLength
    memcpy(buffer, pxDescriptor->pucEthernetBuffer, pxDescriptor->xDataLength);
    numaker_eth_trigger_tx(pxDescriptor->xDataLength, NULL);
    /* Call the standard trace macro to log the send event. */
    iptraceNETWORK_INTERFACE_TRANSMIT();

    if( xReleaseAfterSend != pdFALSE )
    {
        /* It is assumed SendData() copies the data out of the FreeRTOS+TCP Ethernet
        buffer.  The Ethernet buffer is therefore no longer needed, and must be
        freed for re-use. */
        vReleaseNetworkBufferAndDescriptor( pxDescriptor );
    }

    xSemaphoreGive(xTXMutex);
    
    return pdTRUE;
}


void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{

    uint8_t *ucRAMBuffer = ucNetworkPackets;
    uint32_t ul;

    for( ul = 0; ul < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ul++ )
    {
        pxNetworkBuffers[ ul ].pucEthernetBuffer = ucRAMBuffer + ipBUFFER_PADDING;
        *( ( unsigned * ) ucRAMBuffer ) = ( unsigned ) ( &( pxNetworkBuffers[ ul ] ) );
        ucRAMBuffer += niBUFFER_1_PACKET_SIZE;
    }
}


BaseType_t xGetPhyLinkStatus( void )
{
    BaseType_t xReturn;

    if( numaker_eth_link_ok() )
    {
        xReturn = pdPASS;
    }
    else
    {
        xReturn = pdFAIL;
    }

    return xReturn;
}

static void prvPhyTmrCallback( TimerHandle_t xTimer )
{
    IPStackEvent_t xRxEvent;
    static BaseType_t lastLink = pdFAIL;
    BaseType_t currLink = xGetPhyLinkStatus();
    if( currLink != lastLink )
    {
        FreeRTOS_printf(("PHY Link %s\n", (currLink) ? "Up" : "Down"));
        if( !currLink )
        {
            xRxEvent.eEventType = eNetworkDownEvent;
            xSendEventStructToIPTask( &xRxEvent, 0 );
        }
        lastLink = currLink;
    }

}    

    
static void prvEMACHandlerTask( void *pvParameters )
{
    TimeOut_t xPhyTime;
    TickType_t xPhyRemTime;
    UBaseType_t uxLastMinBufferCount = 0;
    UBaseType_t uxCurrentCount;
    BaseType_t xResult = 0;
    uint32_t ulStatus;
    uint16_t dataLength = 0;
    uint8_t *buffer = NULL;
    NetworkBufferDescriptor_t *pxBufferDescriptor = NULL;
    IPStackEvent_t xRxEvent;
    const TickType_t xBlockTime = pdMS_TO_TICKS( 5000ul );
    
    /* Remove compiler warnings about unused parameters. */
    ( void ) pvParameters;
    /* A possibility to set some additional task properties. */
    
    for( ;; )
    {
        uxCurrentCount = uxGetMinimumFreeNetworkBuffers();
        if( uxLastMinBufferCount != uxCurrentCount )
        {
            /* The logging produced below may be helpful
            while tuning +TCP: see how many buffers are in use. */
            uxLastMinBufferCount = uxCurrentCount;
            FreeRTOS_printf( ( "Network buffers: %lu lowest %lu\n",
                uxGetNumberOfFreeNetworkBuffers(), uxCurrentCount ) );
        }
        
        /* No events to process now, wait for the next. */
        ulTaskNotifyTake( pdFALSE, portMAX_DELAY ); 
        while(1)
        {    
            /* get received frame */
            if ( numaker_eth_get_rx_buf(&dataLength, &buffer) != 0) {
            /* The event was lost because a network buffer was not available.
            Call the standard trace macro to log the occurrence. */
                iptraceETHERNET_RX_EVENT_LOST();
                break;
            }        

            /* Allocate a network buffer descriptor that points to a buffer
            large enough to hold the received frame.  As this is the simple
            rather than efficient example the received data will just be copied
            into this buffer. */

            pxBufferDescriptor = pxGetNetworkBufferWithDescriptor( PACKET_BUFFER_SIZE, 0 );

            if( pxBufferDescriptor != NULL )
            {        
                memcpy( pxBufferDescriptor->pucEthernetBuffer, buffer, dataLength );
//                          FreeRTOS_printf(("--> dataLength=%d\n",dataLength));
                pxBufferDescriptor->xDataLength = dataLength;            
            } else {
                numaker_eth_rx_next();
                iptraceETHERNET_RX_EVENT_LOST();
                break;
            }
            /* The event about to be sent to the TCP/IP is an Rx event. */
            xRxEvent.eEventType = eNetworkRxEvent;

            /* pvData is used to point to the network buffer descriptor that
                now references the received data. */
            xRxEvent.pvData = ( void * ) pxBufferDescriptor;

            /* Send the data to the TCP/IP stack. */
            if( xSendEventStructToIPTask( &xRxEvent, 0 ) == pdFALSE )
            {
                /* The buffer could not be sent to the IP task so the buffer
                 must be released. */
                vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );

                /* Make a call to the standard trace macro to log the
                        occurrence. */

                iptraceETHERNET_RX_EVENT_LOST();
            } else
            {
                /* The message was successfully sent to the TCP/IP stack.
                Call the standard trace macro to log the occurrence. */
                iptraceNETWORK_INTERFACE_RECEIVE();
            } 
                numaker_eth_rx_next();
        }    
        numaker_eth_trigger_rx();
    }
}

void xNetworkCallback(char event)
{
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    switch (event)
    {
      case 'R': //For RX event
    /* Wakeup the prvEMACHandlerTask. */
        if( xRxHanderTask != NULL )
        {
            vTaskNotifyGiveFromISR( xRxHanderTask, &xHigherPriorityTaskWoken );
            portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
        }
        break;
      case 'T': //For TX event
        // ack of tx done, no-op in this stage
        break;
      default:
        break;
    }
}
