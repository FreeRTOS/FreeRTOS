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

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_DNS.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

#include "wifi-decl.h"
#include "wmerrno.h"
#include "wifi.h"

#include <wmlog.h>

#define net_e(...)                             \
    wmlog_e("freertos_tcp", ##__VA_ARGS__)
#define net_w(...)                             \
    wmlog_w("freertos_tcp", ##__VA_ARGS__)
#define net_d(...)                             \
    wmlog("freertos_tcp", ##__VA_ARGS__)

#if 0 //this is lwip structure.
#define MAX_INTERFACES_SUPPORTED 3
static struct netif *netif_arr[MAX_INTERFACES_SUPPORTED];
#endif

/* If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 1, then the Ethernet
driver will filter incoming packets and only pass the stack those packets it
considers need processing. */
#if( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 )
#define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer ) eProcessBuffer
#else
#define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer ) eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif

#define IP_ADDR_ANY         ((ip_addr_t *)&ip_addr_any)
#define IP_ADDR_BROADCAST   ((ip_addr_t *)&ip_addr_broadcast)

/** 255.255.255.255 */
#define IPADDR_NONE         ((u32_t)0xffffffffUL)
/** 127.0.0.1 */
#define IPADDR_LOOPBACK     ((u32_t)0x7f000001UL)
/** 0.0.0.0 */
#define IPADDR_ANY          ((u32_t)0x00000000UL)
/** 255.255.255.255 */
#define IPADDR_BROADCAST    ((u32_t)0xffffffffUL)

/** 255.255.255.255 */
#define INADDR_NONE         IPADDR_NONE
/** 127.0.0.1 */
#define INADDR_LOOPBACK     IPADDR_LOOPBACK
/** 0.0.0.0 */
#define INADDR_ANY          IPADDR_ANY
/** 255.255.255.255 */
#define INADDR_BROADCAST    IPADDR_BROADCAST

enum if_state_t {
    INTERFACE_DOWN = 0,
    INTERFACE_UP,
};
struct ip_addr {
  u32_t addr;
};

#define MLAN_BSS_TYPE_STA 0

extern uint8_t outbuf[2048];
extern bool mlan_is_amsdu(const t_u8 *rcvdata);
extern t_u8 *mlan_get_payload(const t_u8 *rcvdata, t_u16 *payload_len, int *interface);
extern int wrapper_wlan_handle_amsdu_rx_packet(const t_u8 *rcvdata, const t_u16 datalen);
extern int wrapper_wlan_handle_rx_packet(const t_u16 datalen, const t_u8 *rcvdata,  NetworkBufferDescriptor_t *pxNetworkBuffer);
static volatile  uint32_t xInterfaceState = INTERFACE_DOWN;

static int process_data_packet(const t_u8 *databuf, const t_u16 datalen)
{
    int interface = BSS_TYPE_STA;
    t_u8 *payload = NULL;
    t_u16 payload_len = 0;
    const TickType_t xDescriptorWaitTime = pdMS_TO_TICKS( 250 );

    NetworkBufferDescriptor_t *pxNetworkBuffer;
    IPStackEvent_t xRxEvent = { eNetworkRxEvent, NULL };

    payload = (t_u8 *)mlan_get_payload(databuf, &payload_len, &interface);

    if( eConsiderFrameForProcessing( payload ) != eProcessBuffer ) {
	net_d("Dropping packet\r\n");
	return WM_SUCCESS;
    }

    pxNetworkBuffer = pxGetNetworkBufferWithDescriptor(/*payload_len*/datalen, xDescriptorWaitTime);

    if (pxNetworkBuffer != NULL) {
	/* Set the packet size, in case a larger buffer was returned. */
	pxNetworkBuffer->xDataLength = payload_len;

	/* Copy the packet data. */
	memcpy(pxNetworkBuffer->pucEthernetBuffer, payload, payload_len);

	xRxEvent.pvData = (void *) pxNetworkBuffer;
	if ( xSendEventStructToIPTask( &xRxEvent, xDescriptorWaitTime) == pdFAIL ) {
		wmprintf("Failed to enqueue packet to network stack %p, len %d", payload, payload_len);
		vReleaseNetworkBufferAndDescriptor(pxNetworkBuffer);
		return WM_FAIL;
	}
    }
    return WM_SUCCESS;
}

/* Callback function called from the wifi module */
void handle_data_packet(const t_u8 interface, const t_u8 *rcvdata,
                        const t_u16 datalen)
{
    if (interface == BSS_TYPE_STA)
	process_data_packet(rcvdata, datalen);
}

BaseType_t xNetworkInterfaceInitialise( void )
{
    uint8_t ret;
    mac_addr_t mac_addr;

	ret = wifi_get_device_mac_addr(&mac_addr);
	if (ret != WM_SUCCESS) {
		net_d("Failed to get mac address");
	}

	FreeRTOS_UpdateMACAddress(mac_addr.mac);

    return ( xInterfaceState == INTERFACE_UP && ret == WM_SUCCESS ) ? pdTRUE : pdFALSE;
}

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
    /* FIX ME. */
}

BaseType_t xGetPhyLinkStatus( void )
{
    /* FIX ME. */
    return pdFALSE;
}
void vNetworkNotifyIFDown()
{
    IPStackEvent_t xRxEvent = { eNetworkDownEvent, NULL };
    xInterfaceState = INTERFACE_DOWN;
    if( xSendEventStructToIPTask( &xRxEvent, 0 ) != pdPASS ) {
	/* Could not send the message, so it is still pending. */
        net_e("Could not send network down event");
    }
    else {
	/* Message was sent so it is not pending. */
        net_d("Sent network down event");
    }
}

void vNetworkNotifyIFUp()
{
    xInterfaceState = INTERFACE_UP;
}

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t *const pxNetworkBuffer, BaseType_t xReleaseAfterSend )
{
    uint8_t pkt_len;

    if (pxNetworkBuffer == NULL ||
	pxNetworkBuffer->pucEthernetBuffer == NULL ||
	pxNetworkBuffer->xDataLength == 0) {
	    net_d("Incorrect params");
            return pdFALSE;
    }
    memset(outbuf, 0x00, sizeof(outbuf));
    pkt_len = 22 + 4; /* sizeof(TxPD) + INTF_HEADER_LEN */
    memcpy((u8_t *) outbuf + pkt_len, (u8_t *) pxNetworkBuffer->pucEthernetBuffer,
		pxNetworkBuffer->xDataLength);
    int ret = wifi_low_level_output(BSS_TYPE_STA, outbuf + pkt_len, pxNetworkBuffer->xDataLength);
    if (ret != WM_SUCCESS) {
	net_e("Failed output %p, length %d, error %d \r\n", pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, ret);
    }

    if (xReleaseAfterSend != pdFALSE) {
        vReleaseNetworkBufferAndDescriptor(pxNetworkBuffer);
    }

    return ret == WM_SUCCESS ? pdTRUE : pdFALSE;
}
