/*
 * Some constants, hardware definitions and comments taken from ST's HAL driver
 * library, COPYRIGHT(c) 2015 STMicroelectronics.
 */

/*
FreeRTOS+TCP V2.0.11
Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.

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

/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

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

#include "phyHandling.h"

/* ST includes. */
#include "stm32h7xx_hal.h"

#define niEMAC_TASK_STACK_SIZE		1024
#define niEMAC_TASK_PRIORITY		( configMAX_PRIORITIES - 1 )
#define niEMAC_TASK_NAME			"eth_input"

/*
 * This is a Network Interface in its simplest form. It is still under development.
 * TODO: Use BufferAllocation_1
 * TODO: Implement zero-copy driver
 * TODO: Let the ETH interrupts wake-up the deferred interrupt handler task.
 * TODO: Use ../Common/phyHandler to initialise the PHY and check its Link Status
 */

extern ETH_HandleTypeDef	heth;
extern ETH_TxPacketConfig   TxConfig;

static TaskHandle_t xEMACTaskHandle;

typedef enum
{
	eMACInit,   /* Must initialise MAC. */
	eMACPass,   /* Initialisation was successful. */
	eMACFailed, /* Initialisation failed. */
} eMAC_INIT_STATUS_TYPE;

static eMAC_INIT_STATUS_TYPE xMacInitStatus = eMACInit;

/* _HT_ .TxArraySection is a section in RAM that is not cached. */
static uint8_t Tx_Buff[ ETH_MAX_PACKET_SIZE ] __attribute__( ( section( ".TxArraySection" ) ) );

static void prvEMACPoll( void );

/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceInitialise()
{
BaseType_t xReturn;

	if( xMacInitStatus == eMACInit )
	{
	BaseType xResult;

		xMacInitStatus = eMACFailed;

		if( HAL_ETH_Start( &( heth ) ) == HAL_OK )
		{
			/* The ETH peripheral is initialised. */
			xResult = xTaskCreate( prvEMACDeferredInterruptHandlerTask,
								   niEMAC_TASK_NAME,
								   niEMAC_TASK_STACK_SIZE,
								   NULL,	/* pvParameter. */
								   niEMAC_TASK_PRIORITY,
								   &( xEMACTaskHandle ) );

			/* Perform the hardware specific network initialisation here.  Typically
			that will involve using the Ethernet driver library to initialise the
			Ethernet (or other network) hardware, initialise DMA descriptors, and
			perform a PHY auto-negotiation to obtain a network link. */

			if( xResult == pdPASS )
			{
				/* The task was created successfully. */
				xMacInitStatus = eMACPass;
			}
		}
	}

	if( xMacInitStatus == eMACPass )
	{
		/* TODO here: Check if Link is up, making use of ../common/phyHandler.c
		Only return pdPASS when the LinkStatus is up. */
		if( xPhyObject.ulLinkStatusMask != 0uL )
		{
			xETH.Instance->DMAIER |= ETH_DMA_ALL_INTS;
			xReturn = pdPASS;
			FreeRTOS_printf( ( "Link Status is high\n" ) ) ;
		}
		else
		{
			/* For now pdFAIL will be returned. But prvEMACHandlerTask() is running
			and it will keep on checking the PHY and set 'ulLinkStatusMask' when necessary. */
			xReturn = pdFAIL;
		}
	}
	else
	{
		xReturn = pdFAIL;
	}
	return xReturn;
}
/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxDescriptor, BaseType_t bReleaseAfterSend )
{
/* Simple network interfaces (as opposed to more efficient zero copy network
interfaces) just use Ethernet peripheral driver library functions to copy
data from the FreeRTOS+TCP buffer into the peripheral driver's own buffer.
This example assumes SendData() is a peripheral driver library function that
takes a pointer to the start of the data to be sent and the length of the
data to be sent as two separate parameters.  The start of the data is located
by pxDescriptor->pucEthernetBuffer.  The length of the data is located
by pxDescriptor->xDataLength. */
BaseType_t xResult;

	memcpy( Tx_Buff, pxDescriptor->pucEthernetBuffer, pxDescriptor->xDataLength );

	/* TODO: Support for ipconfigUSE_LINKED_RX_MESSAGES */

	ETH_BufferTypeDef buf =
	{
		.buffer = Tx_Buff,
		.len  = pxDescriptor->xDataLength,
		.next = NULL
	};

	TxConfig.Length = pxDescriptor->xDataLength;
	TxConfig.TxBuffer = &buf;

	/* TODO: Use SCB_InvalidateDCache_by_Addr 'SCB_CleanInvalidateDCache()'. */

	HAL_StatusTypeDef status;
	status = HAL_ETH_Transmit( &heth, &TxConfig, HAL_MAX_DELAY );

	/* Call the standard trace macro to log the send event. */
	iptraceNETWORK_INTERFACE_TRANSMIT();

	if ( bReleaseAfterSend != pdFALSE )
	{
		/* It is assumed SendData() copies the data out of the FreeRTOS+TCP Ethernet
		buffer.  The Ethernet buffer is therefore no longer needed, and must be
		freed for re-use. */
		vReleaseNetworkBufferAndDescriptor( pxDescriptor );
	}

	if (status == HAL_OK)
	{
		xResult = pdPASS;
	}
	else
	{
		xResult = pdFAIL;
	}

	return xResult;
}
/*-----------------------------------------------------------*/

/* The deferred interrupt handler is a standard RTOS task.  FreeRTOS's centralised
deferred interrupt handling capabilities can also be used. */

static void prvEMACPoll()
{
NetworkBufferDescriptor_t *pxBufferDescriptor;

	if( HAL_ETH_IsRxDataAvailable( &heth ) == pdFALSE )
	{
		return;
	}

	ETH_BufferTypeDef	data_buffer;
	uint32_t			data_length = 0;

	HAL_ETH_GetRxDataBuffer( &heth, &data_buffer );
	HAL_ETH_GetRxDataLength( &heth, &data_length );

	/* Allocate a network buffer descriptor that points to a buffer
	large enough to hold the received frame.  As this is the simple
	rather than efficient example the received data will just be copied
	into this buffer. */
	pxBufferDescriptor = pxGetNetworkBufferWithDescriptor( data_length, 0u );

	if( pxBufferDescriptor == NULL )
	{
		/* The event was lost because a network buffer was not available.
		Call the standard trace macro to log the occurrence. */
		iptraceETHERNET_RX_EVENT_LOST();
		return;
	}

	/* pxBufferDescriptor->pucEthernetBuffer now points to an Ethernet
	buffer large enough to hold the received data.  Copy the
	received data into pcNetworkBuffer->pucEthernetBuffer.  Here it
	is assumed ReceiveData() is a peripheral driver function that
	copies the received data into a buffer passed in as the function's
	parameter.  Remember! While is is a simple robust technique -
	it is not efficient.  An example that uses a zero copy technique
	is provided further down this page. */

	memcpy( pxBufferDescriptor->pucEthernetBuffer, data_buffer.buffer, data_length );
	pxBufferDescriptor->xDataLength = data_length;

	HAL_ETH_BuildRxDescriptors( &( heth ) );

	/* See if the data contained in the received Ethernet frame needs
	to be processed.  NOTE! It is preferable to do this in
	the interrupt service routine itself, which would remove the need
	to unblock this task for packets that don't need processing. */

	if( eConsiderFrameForProcessing( pxBufferDescriptor->pucEthernetBuffer ) != eProcessBuffer )
	{
		/* The Ethernet frame can be dropped, but the Ethernet buffer must be released. */
		vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );
		return;
	}

	/* The event about to be sent to the TCP/IP is an Rx event.
	pvData is used to point to the network buffer descriptor that
	now references the received data. */

	IPStackEvent_t xRxEvent =
	{
		.eEventType = eNetworkRxEvent,
		.pvData	 = (void *)pxBufferDescriptor
	};

	/* Send the data to the TCP/IP stack. */
	if( xSendEventStructToIPTask(&xRxEvent, 0) != pdFALSE )
	{
		/* The message was successfully sent to the TCP/IP stack.
		Call the standard trace macro to log the occurrence. */
		iptraceNETWORK_INTERFACE_RECEIVE();
	}
	else
	{
		/* The buffer could not be sent to the IP task so the buffer
		must be released. */
		vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );

		/* Make a call to the standard trace macro to log the
		occurrence. */
		iptraceETHERNET_RX_EVENT_LOST();
	}
}
/*-----------------------------------------------------------*/

static void prvEMACDeferredInterruptHandlerTask( void *pvParameters )
{
TickType_t uxPollInterval = pdMS_TO_TICKS( 1u );

	( void ) pvParameters;

	if( uxPollInterval < 1u )
	{
		uxPollInterval = 1u;
	}

	for( ;; )
	{
		/* Wait for the Ethernet MAC interrupt to indicate that another packet
		has been received.  The task notification is used in a similar way to a
		counting semaphore to count Rx events, but is a lot more efficient than
		a semaphore. */

		/* ulTaskNotifyTake( pdFALSE, portMAX_DELAY ); */
		ulTaskNotifyTake( pdFALSE, uxPollInterval );

		/* TODO here: let the ETH interrupt wake-up this task. */
		prvEMACPoll();
	}
}
/*-----------------------------------------------------------*/
