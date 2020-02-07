// Copyright 2018 Espressif Systems (Shanghai) PTE LTD
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_DNS.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

#include "esp_log.h"
#include "esp_wifi.h"
#include "esp_wifi_internal.h"
#include "tcpip_adapter.h"

enum if_state_t {
    INTERFACE_DOWN = 0,
    INTERFACE_UP,
};

static const char *TAG = "NetInterface";
volatile static uint32_t xInterfaceState = INTERFACE_DOWN;

BaseType_t xNetworkInterfaceInitialise( void )
{
    static BaseType_t xMACAdrInitialized = pdFALSE;
    uint8_t ucMACAddress[ ipMAC_ADDRESS_LENGTH_BYTES ];

    if (xInterfaceState == INTERFACE_UP) {
        if (xMACAdrInitialized == pdFALSE) {
            esp_wifi_get_mac(ESP_IF_WIFI_STA, ucMACAddress);
            FreeRTOS_UpdateMACAddress(ucMACAddress);
            xMACAdrInitialized = pdTRUE;
        }
        return pdTRUE;
    }
    return pdFALSE;
}

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t *const pxNetworkBuffer, BaseType_t xReleaseAfterSend )
{
    if (pxNetworkBuffer == NULL || pxNetworkBuffer->pucEthernetBuffer == NULL || pxNetworkBuffer->xDataLength == 0) {
        ESP_LOGE(TAG, "Invalid params");
        return pdFALSE;
    }

    esp_err_t ret;
    if (xInterfaceState == INTERFACE_DOWN) {
        ESP_LOGD(TAG, "Interface down");
        ret = ESP_FAIL;
    } else {
        ret = esp_wifi_internal_tx(ESP_IF_WIFI_STA, pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength);
        if (ret != ESP_OK) {
            ESP_LOGE(TAG, "Failed to tx buffer %p, len %d, err %d", pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength, ret);
        }
    }

    if (xReleaseAfterSend == pdTRUE) {
        vReleaseNetworkBufferAndDescriptor(pxNetworkBuffer);
    }

    return ret == ESP_OK ? pdTRUE : pdFALSE;
}

void vNetworkNotifyIFDown()
{
    IPStackEvent_t xRxEvent = { eNetworkDownEvent, NULL };
    if (xInterfaceState != INTERFACE_DOWN) {
        xInterfaceState = INTERFACE_DOWN;
        xSendEventStructToIPTask( &xRxEvent, 0 );
    }
}

void vNetworkNotifyIFUp()
{
    xInterfaceState = INTERFACE_UP;
}

esp_err_t wlanif_input(void *netif, void *buffer, uint16_t len, void *eb)
{
    NetworkBufferDescriptor_t *pxNetworkBuffer;
    IPStackEvent_t xRxEvent = { eNetworkRxEvent, NULL };
    const TickType_t xDescriptorWaitTime = pdMS_TO_TICKS( 250 );

    if( eConsiderFrameForProcessing( buffer ) != eProcessBuffer ) {
        ESP_LOGD(TAG, "Dropping packet");
        esp_wifi_internal_free_rx_buffer(eb);
        return ESP_OK;
    }

    pxNetworkBuffer = pxGetNetworkBufferWithDescriptor(len, xDescriptorWaitTime);
    if (pxNetworkBuffer != NULL) {

	/* Set the packet size, in case a larger buffer was returned. */
	pxNetworkBuffer->xDataLength = len;

	/* Copy the packet data. */
        memcpy(pxNetworkBuffer->pucEthernetBuffer, buffer, len);
        xRxEvent.pvData = (void *) pxNetworkBuffer;

        if ( xSendEventStructToIPTask( &xRxEvent, xDescriptorWaitTime) == pdFAIL ) {
            ESP_LOGE(TAG, "Failed to enqueue packet to network stack %p, len %d", buffer, len);
            vReleaseNetworkBufferAndDescriptor(pxNetworkBuffer);
            return ESP_FAIL;
        }
        esp_wifi_internal_free_rx_buffer(eb);
        return ESP_OK;
    } else {
        ESP_LOGE(TAG, "Failed to get buffer descriptor");
        return ESP_FAIL;
    }
}
