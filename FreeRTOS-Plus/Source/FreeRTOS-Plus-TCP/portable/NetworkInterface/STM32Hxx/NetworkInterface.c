/*
 * Some constants, hardware definitions and comments taken from ST's HAL driver
 * library, COPYRIGHT(c) 2015 STMicroelectronics.
 */

/*
FreeRTOS+TCP V2.2.1
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

#include <string.h>

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

/* Interrupt events to process.  Currently only the Rx event is processed
although code for other events is included to allow for possible future
expansion. */
#define EMAC_IF_RX_EVENT		1UL
#define EMAC_IF_TX_EVENT		2UL
#define EMAC_IF_ERR_EVENT		4UL
#define EMAC_IF_ALL_EVENT		( EMAC_IF_RX_EVENT | EMAC_IF_TX_EVENT | EMAC_IF_ERR_EVENT )

#define niEMAC_HANDLER_TASK_NAME			"EMACDifferedInterruptHandlerTask"
#define niEMAC_HANDLER_TASK_STACK_SIZE		( 2 * configMINIMAL_STACK_SIZE )
#define niEMAC_HANDLER_TASK_PRIORITY		configMAX_PRIORITIES - 1

/* Bit map of outstanding ETH interrupt events for processing.  Currently only
the Rx interrupt is handled, although code is included for other events to
enable future expansion. */
static volatile uint32_t ulISREvents;

typedef enum
{
	eMACInit,   /* Must initialise MAC. */
	eMACPass,   /* Initialisation was successful. */
	eMACFailed, /* Initialisation failed. */
} eMAC_INIT_STATUS_TYPE;

static eMAC_INIT_STATUS_TYPE xMacInitStatus = eMACInit;

/* Global Ethernet handle */
static ETH_HandleTypeDef xEthHandle;
static ETH_TxPacketConfig TxConfig;

/* Ethernet Rx DMA Descriptors */
__attribute__ ((aligned (32)))
__attribute__ ((section(".first_data")))
ETH_DMADescTypeDef DMARxDscrTab[ETH_RX_DESC_CNT];
/* Ethernet Receive Buffer */
__ALIGN_BEGIN uint8_t Rx_Buff[ ETH_RX_DESC_CNT ][ ETH_RX_BUF_SIZE ] __ALIGN_END;

/* Ethernet Tx DMA Descriptors */
__attribute__ ((aligned (32)))
__attribute__ ((section(".first_data")))
ETH_DMADescTypeDef DMATxDscrTab[ETH_TX_DESC_CNT];
/* Ethernet Transmit Buffer */
__ALIGN_BEGIN uint8_t Tx_Buff[ ETH_TX_BUF_SIZE ] __ALIGN_END;

/* This function binds PHY IO functions, then inits and configures */
static void prvMACBProbePhy( void );

/* Force a negotiation with the Switch or Router and wait for LS. */
static void prvEthernetUpdateConfig( BaseType_t xForce );

/* Holds the handle of the task used as a deferred interrupt processor.  The
handle is used so direct notifications can be sent to the task for all EMAC/DMA
related interrupts. */
static TaskHandle_t xEMACTaskHandle = NULL;

/*
 * A deferred interrupt handler task that processes
 */
static void prvEMACHandlerTask( void *pvParameters );

/*
 * See if there is a new packet and forward it to the IP-task.
 */
static BaseType_t prvNetworkInterfaceInput( void );

/* Private PHY IO functions and properties */
static int32_t ETH_PHY_IO_ReadReg(uint32_t DevAddr, uint32_t RegAddr, uint32_t *pRegVal);
static int32_t ETH_PHY_IO_WriteReg(uint32_t DevAddr, uint32_t RegAddr, uint32_t RegVal);

static EthernetPhy_t xPhyObject;
/* For local use only: describe the PHY's properties: */
const PhyProperties_t xPHYProperties =
{
	.ucSpeed = PHY_SPEED_AUTO,
	.ucDuplex = PHY_DUPLEX_AUTO,
	.ucMDI_X = PHY_MDIX_DIRECT
};



/*******************************************************************************
			           Network Interface API Functions
*******************************************************************************/

BaseType_t xNetworkInterfaceInitialise( void )
{
BaseType_t xResult;
HAL_StatusTypeDef xHalEthInitStatus;
uint32_t idx = 0;

	if( xMacInitStatus == eMACInit )
	{
		/*
		 * Initialize ETH Handler
		 * It assumes that Ethernet GPIO and clock configuration
		 * are already done in the ETH_MspInit()
		 */
		xEthHandle.Instance = ETH;
		xEthHandle.Init.MACAddr = ( uint8_t *)FreeRTOS_GetMACAddress();
		xEthHandle.Init.MediaInterface = HAL_ETH_RMII_MODE;
		xEthHandle.Init.TxDesc = DMATxDscrTab;
		xEthHandle.Init.RxDesc = DMARxDscrTab;
		xEthHandle.Init.RxBuffLen = ETH_RX_BUF_SIZE;

		/* Make sure that all unused fields are cleared. */
		memset( &DMATxDscrTab, '\0', sizeof( DMATxDscrTab ) );
		memset( &DMARxDscrTab, '\0', sizeof( DMARxDscrTab ) );

		xHalEthInitStatus = HAL_ETH_Init(&xEthHandle);

		/* Only for inspection by debugger. */
		( void ) xHalEthInitStatus;

		/* Configuration for HAL_ETH_Transmit(_IT). */
		memset(&TxConfig, 0 , sizeof(ETH_TxPacketConfig));
		TxConfig.Attributes = ETH_TX_PACKETS_FEATURES_CSUM | ETH_TX_PACKETS_FEATURES_CRCPAD;
		TxConfig.ChecksumCtrl = ETH_CHECKSUM_IPHDR_PAYLOAD_INSERT_PHDR_CALC;
		TxConfig.CRCPadCtrl = ETH_CRC_PAD_INSERT;

		/* Assign Rx memory buffers to a DMA Rx descriptor */
		for(idx = 0; idx < ETH_RX_DESC_CNT; idx++)
		{
			HAL_ETH_DescAssignMemory(&xEthHandle, idx, Rx_Buff[idx], NULL);
		}

		/* Configure the MDIO Clock */
		HAL_ETH_SetMDIOClockRange(&xEthHandle);

		/* Initialize the MACB and set all PHY properties */
		prvMACBProbePhy();

		/* Force a negotiation with the Switch or Router and wait for LS. */
		prvEthernetUpdateConfig(pdTRUE);

		/* The deferred interrupt handler task is created at the highest
			possible priority to ensure the interrupt handler can return directly
			to it.  The task's handle is stored in xEMACTaskHandle so interrupts can
			notify the task when there is something to process. */
		if( xTaskCreate( prvEMACHandlerTask, niEMAC_HANDLER_TASK_NAME, niEMAC_HANDLER_TASK_STACK_SIZE, NULL, niEMAC_HANDLER_TASK_PRIORITY, &xEMACTaskHandle ) == pdPASS )
		{
			/* The task was created successfully. */
			xMacInitStatus = eMACPass;
		}
		else
		{
			xMacInitStatus = eMACFailed;
		}
	}/* ( xMacInitStatus == eMACInit ) */

	if( xMacInitStatus != eMACPass )
	{
		/* EMAC initialisation failed, return pdFAIL. */
		xResult = pdFAIL;
	}
	else
	{
		if( xPhyObject.ulLinkStatusMask != 0uL )
		{
			xResult = pdPASS;
			FreeRTOS_printf( ( "Link Status is high\n" ) ) ;
		}
		else
		{
			/* For now pdFAIL will be returned. But prvEMACHandlerTask() is running
			and it will keep on checking the PHY and set 'ulLinkStatusMask' when necessary. */
			xResult = pdFAIL;
		}
	}

	return xResult;
}

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxDescriptor, BaseType_t xReleaseAfterSend )
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
		.len = pxDescriptor->xDataLength,
		.next = NULL
	};

	TxConfig.Length = pxDescriptor->xDataLength;
	TxConfig.TxBuffer = &buf;

	/* TODO: Use SCB_InvalidateDCache_by_Addr 'SCB_CleanInvalidateDCache()'. */

	HAL_StatusTypeDef status;
	status = HAL_ETH_Transmit( &xEthHandle, &TxConfig, HAL_MAX_DELAY );

	/* Call the standard trace macro to log the send event. */
	iptraceNETWORK_INTERFACE_TRANSMIT();

	if ( xReleaseAfterSend != pdFALSE )
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


/*******************************************************************************
			           END Network Interface API Functions
*******************************************************************************/



/*******************************************************************************
			           Network Interface Static Functions
*******************************************************************************/

static void prvMACBProbePhy( void )
{
	/* Bind the write and read access functions. */
	vPhyInitialise( &xPhyObject,
					( xApplicationPhyReadHook_t ) ETH_PHY_IO_ReadReg,
					( xApplicationPhyWriteHook_t ) ETH_PHY_IO_WriteReg );
	/* Poll the bus for all connected PHY's. */
	xPhyDiscover( &xPhyObject );
	/* Configure them using the properties provided. */
	xPhyConfigure( &xPhyObject, &xPHYProperties );
}

static void prvEthernetUpdateConfig( BaseType_t xForce )
{
	ETH_MACConfigTypeDef MACConf;
	uint32_t speed = 0, duplex =0;

	FreeRTOS_printf( ( "prvEthernetUpdateConfig: LS mask %02lX Force %d\n",
			xPhyObject.ulLinkStatusMask,
			( int )xForce ) );

	if( ( xForce != pdFALSE ) || ( xPhyObject.ulLinkStatusMask != 0 ) )
	{
		/* Restart the auto-negotiation. */
		xPhyStartAutoNegotiation( &xPhyObject, xPhyGetMask( &xPhyObject ) );

		/* Configure the MAC with the Duplex Mode fixed by the
		   auto-negotiation process. */
		if( xPhyObject.xPhyProperties.ucDuplex == PHY_DUPLEX_FULL )
		{
			duplex = ETH_FULLDUPLEX_MODE;
		}
		else
		{
			duplex = ETH_HALFDUPLEX_MODE;
		}

		/* Configure the MAC with the speed fixed by the
		   auto-negotiation process. */
		if( xPhyObject.xPhyProperties.ucSpeed == PHY_SPEED_10 )
		{
			speed = ETH_SPEED_10M;
		}
		else
		{
			speed = ETH_SPEED_100M;
		}

		/* Get MAC and configure it */
		HAL_ETH_GetMACConfig(&xEthHandle, &MACConf);
		MACConf.DuplexMode = duplex;
		MACConf.Speed = speed;
		HAL_ETH_SetMACConfig(&xEthHandle, &MACConf);

		/* Restart MAC interface */
		HAL_ETH_Start_IT(&xEthHandle);
	}
	else
	{
		/* Stop MAC interface */
		HAL_ETH_Stop_IT( &xEthHandle );
	}
}

static void prvEMACHandlerTask( void *pvParameters )
{
BaseType_t xResult;
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

		if( ( ulISREvents & EMAC_IF_RX_EVENT ) != 0 )
		{
			ulISREvents &= ~EMAC_IF_RX_EVENT;

			xResult = prvNetworkInterfaceInput();
			if( xResult > 0 )
			{
				while( prvNetworkInterfaceInput() > 0 )
				{
				}
			}
		}

		if( xPhyCheckLinkStatus( &xPhyObject, xResult ) != 0 )
		{
			/* Something has changed to a Link Status, need re-check. */
			prvEthernetUpdateConfig( pdFALSE );
		}
	}
}

static BaseType_t prvNetworkInterfaceInput( void )
{

	NetworkBufferDescriptor_t *pxBufferDescriptor;

	ETH_BufferTypeDef	data_buffer;
	uint32_t			data_length = 0;

	HAL_ETH_GetRxDataBuffer( &xEthHandle, &data_buffer );
	HAL_ETH_GetRxDataLength( &xEthHandle, &data_length );

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
		return pdFALSE;
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

	HAL_ETH_BuildRxDescriptors( &( xEthHandle ) );

	/* See if the data contained in the received Ethernet frame needs
	to be processed.  NOTE! It is preferable to do this in
	the interrupt service routine itself, which would remove the need
	to unblock this task for packets that don't need processing. */

	if( eConsiderFrameForProcessing( pxBufferDescriptor->pucEthernetBuffer ) != eProcessBuffer )
	{
		/* The Ethernet frame can be dropped, but the Ethernet buffer must be released. */
		vReleaseNetworkBufferAndDescriptor( pxBufferDescriptor );
		return pdFALSE;
	}

	/* The event about to be sent to the TCP/IP is an Rx event.
	pvData is used to point to the network buffer descriptor that
	now references the received data. */

	IPStackEvent_t xRxEvent =
	{
		.eEventType = eNetworkRxEvent,
		.pvData = (void *)pxBufferDescriptor
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
		return pdFALSE;
	}

	return pdTRUE;
}

/*******************************************************************************
					END Network Interface Static Functions
*******************************************************************************/



/*******************************************************************************
					PHY IO Functions
*******************************************************************************/

/**
  * @brief  Read a PHY register through the MDIO interface.
  * @param  DevAddr: PHY port address
  * @param  RegAddr: PHY register address
  * @param  pRegVal: pointer to hold the register value
  * @retval 0 if OK -1 if Error
  */
static int32_t ETH_PHY_IO_ReadReg(uint32_t DevAddr, uint32_t RegAddr, uint32_t *pRegVal)
{
  if(HAL_ETH_ReadPHYRegister( &( xEthHandle ), DevAddr, RegAddr, pRegVal ) != HAL_OK )
  {
	return -1;
  }

  return 0;
}

/**
  * @brief  Write a value to a PHY register through the MDIO interface.
  * @param  DevAddr: PHY port address
  * @param  RegAddr: PHY register address
  * @param  RegVal: Value to be written
  * @retval 0 if OK -1 if Error
  */
static int32_t ETH_PHY_IO_WriteReg(uint32_t DevAddr, uint32_t RegAddr, uint32_t RegVal)
{
	if(HAL_ETH_WritePHYRegister(&( xEthHandle ), DevAddr, RegAddr, RegVal) != HAL_OK )
	{
		return -1;
	}

	return 0;
}

/*******************************************************************************
					END PHY IO Functions
*******************************************************************************/



/*******************************************************************************
					Ethernet Handling Functions
*******************************************************************************/

void ETH_IRQHandler(void)
{

	HAL_ETH_IRQHandler(&xEthHandle);
}

void HAL_ETH_RxCpltCallback( ETH_HandleTypeDef *heth )
{
BaseType_t xHigherPriorityTaskWoken = pdFALSE;

	( void ) heth;

	/* Ethernet RX-Complete callback function, elsewhere declared as weak. */
	ulISREvents |= EMAC_IF_RX_EVENT;
	/* Wakeup the prvEMACHandlerTask. */
	if( xEMACTaskHandle != NULL )
	{
		vTaskNotifyGiveFromISR( xEMACTaskHandle, &xHigherPriorityTaskWoken );
		portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
	}
}

/*******************************************************************************
					END Ethernet Handling Functions
*******************************************************************************/
