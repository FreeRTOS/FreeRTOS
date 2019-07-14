/*
 * FreeRTOS+TCP V2.0.11
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */


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
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

/* Some files from the Atmel Software Framework */
/*_RB_ The SAM4E portable layer has three different header files called gmac.h! */
#include "instance/gmac.h"
#include <sysclk.h>
#include <ethernet_phy.h>

#ifndef	BMSR_LINK_STATUS
	#define BMSR_LINK_STATUS            0x0004  //!< Link status
#endif

#ifndef	PHY_LS_HIGH_CHECK_TIME_MS
	/* Check if the LinkSStatus in the PHY is still high after 15 seconds of not
	receiving packets. */
	#define PHY_LS_HIGH_CHECK_TIME_MS	15000
#endif

#ifndef	PHY_LS_LOW_CHECK_TIME_MS
	/* Check if the LinkSStatus in the PHY is still low every second. */
	#define PHY_LS_LOW_CHECK_TIME_MS	1000
#endif

/* Interrupt events to process.  Currently only the Rx event is processed
although code for other events is included to allow for possible future
expansion. */
#define EMAC_IF_RX_EVENT        1UL
#define EMAC_IF_TX_EVENT        2UL
#define EMAC_IF_ERR_EVENT       4UL
#define EMAC_IF_ALL_EVENT       ( EMAC_IF_RX_EVENT | EMAC_IF_TX_EVENT | EMAC_IF_ERR_EVENT )

#define ETHERNET_CONF_PHY_ADDR  BOARD_GMAC_PHY_ADDR

#define HZ_PER_MHZ				( 1000000UL )

#ifndef	EMAC_MAX_BLOCK_TIME_MS
	#define	EMAC_MAX_BLOCK_TIME_MS	100ul
#endif

#if !defined( GMAC_USES_TX_CALLBACK ) || ( GMAC_USES_TX_CALLBACK != 1 )
	#error Please define GMAC_USES_TX_CALLBACK as 1
#endif

#if( ipconfigZERO_COPY_RX_DRIVER != 0 )
	#warning The EMAC of SAM4E has fixed-size RX buffers so ZERO_COPY_RX is not possible
#endif

/* Default the size of the stack used by the EMAC deferred handler task to 4x
the size of the stack used by the idle task - but allow this to be overridden in
FreeRTOSConfig.h as configMINIMAL_STACK_SIZE is a user definable constant. */
#ifndef configEMAC_TASK_STACK_SIZE
	#define configEMAC_TASK_STACK_SIZE ( 4 * configMINIMAL_STACK_SIZE )
#endif

/*-----------------------------------------------------------*/

/*
 * Wait a fixed time for the link status to indicate the network is up.
 */
static BaseType_t xGMACWaitLS( TickType_t xMaxTime );

#if( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 1 ) && ( ipconfigHAS_TX_CRC_OFFLOADING == 0 )
	void vGMACGenerateChecksum( uint8_t *apBuffer );
#endif

/*
 * Called from the ASF GMAC driver.
 */
static void prvRxCallback( uint32_t ulStatus );
static void prvTxCallback( uint32_t ulStatus, uint8_t *puc_buffer );

/*
 * A deferred interrupt handler task that processes GMAC interrupts.
 */
static void prvEMACHandlerTask( void *pvParameters );

/*
 * Initialise the ASF GMAC driver.
 */
static BaseType_t prvGMACInit( void );

/*
 * Try to obtain an Rx packet from the hardware.
 */
static uint32_t prvEMACRxPoll( void );

/*-----------------------------------------------------------*/

/* Bit map of outstanding ETH interrupt events for processing.  Currently only
the Rx interrupt is handled, although code is included for other events to
enable future expansion. */
static volatile uint32_t ulISREvents;

/* A copy of PHY register 1: 'PHY_REG_01_BMSR' */
static uint32_t ulPHYLinkStatus = 0;
static volatile BaseType_t xGMACSwitchRequired;

/* ethernet_phy_addr: the address of the PHY in use.
Atmel was a bit ambiguous about it so the address will be stored
in this variable, see ethernet_phy.c */
extern int ethernet_phy_addr;

/* LLMNR multicast address. */
static const uint8_t llmnr_mac_address[] = { 0x01, 0x00, 0x5E, 0x00, 0x00, 0xFC };

/* The GMAC object as defined by the ASF drivers. */
static gmac_device_t gs_gmac_dev;

/* MAC address to use. */
extern const uint8_t ucMACAddress[ 6 ];

/* Holds the handle of the task used as a deferred interrupt processor.  The
handle is used so direct notifications can be sent to the task for all EMAC/DMA
related interrupts. */
TaskHandle_t xEMACTaskHandle = NULL;

static QueueHandle_t xTxBufferQueue;
int tx_release_count[ 4 ];

/* xTXDescriptorSemaphore is a counting semaphore with
a maximum count of GMAC_TX_BUFFERS, which is the number of
DMA TX descriptors. */
static SemaphoreHandle_t xTXDescriptorSemaphore = NULL;

/*-----------------------------------------------------------*/

/*
 * GMAC interrupt handler.
 */
void GMAC_Handler(void)
{
	xGMACSwitchRequired = pdFALSE;

	/* gmac_handler() may call prvRxCallback() which may change
	the value of xGMACSwitchRequired. */
	gmac_handler( &gs_gmac_dev );

	if( xGMACSwitchRequired != pdFALSE )
	{
		portEND_SWITCHING_ISR( xGMACSwitchRequired );
	}
}
/*-----------------------------------------------------------*/

static void prvRxCallback( uint32_t ulStatus )
{
	if( ( ( ulStatus & GMAC_RSR_REC ) != 0 ) && ( xEMACTaskHandle != NULL ) )
	{
		/* let the prvEMACHandlerTask know that there was an RX event. */
		ulISREvents |= EMAC_IF_RX_EVENT;
		/* Only an RX interrupt can wakeup prvEMACHandlerTask. */
		vTaskNotifyGiveFromISR( xEMACTaskHandle, ( BaseType_t * ) &xGMACSwitchRequired );
	}
}
/*-----------------------------------------------------------*/

static void prvTxCallback( uint32_t ulStatus, uint8_t *puc_buffer )
{
	if( ( xTxBufferQueue != NULL ) && ( xEMACTaskHandle != NULL ) )
	{
		/* let the prvEMACHandlerTask know that there was an RX event. */
		ulISREvents |= EMAC_IF_TX_EVENT;

		vTaskNotifyGiveFromISR( xEMACTaskHandle, ( BaseType_t * ) &xGMACSwitchRequired );
		xQueueSendFromISR( xTxBufferQueue, &puc_buffer, ( BaseType_t * ) &xGMACSwitchRequired );
		tx_release_count[ 2 ]++;
	}
}
/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceInitialise( void )
{
const TickType_t x5_Seconds = 5000UL;

	if( xEMACTaskHandle == NULL )
	{
		prvGMACInit();

		/* Wait at most 5 seconds for a Link Status in the PHY. */
		xGMACWaitLS( pdMS_TO_TICKS( x5_Seconds ) );

		/* The handler task is created at the highest possible priority to
		ensure the interrupt handler can return directly to it. */
		xTaskCreate( prvEMACHandlerTask, "EMAC", configEMAC_TASK_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xEMACTaskHandle );
		configASSERT( xEMACTaskHandle );
	}

	if( xTxBufferQueue == NULL )
	{
		xTxBufferQueue = xQueueCreate( GMAC_TX_BUFFERS, sizeof( void * ) );
		configASSERT( xTxBufferQueue );
	}

	if( xTXDescriptorSemaphore == NULL )
	{
		xTXDescriptorSemaphore = xSemaphoreCreateCounting( ( UBaseType_t ) GMAC_TX_BUFFERS, ( UBaseType_t ) GMAC_TX_BUFFERS );
		configASSERT( xTXDescriptorSemaphore );
	}
	/* When returning non-zero, the stack will become active and
	start DHCP (in configured) */
	return ( ulPHYLinkStatus & BMSR_LINK_STATUS ) != 0;
}
/*-----------------------------------------------------------*/

BaseType_t xGetPhyLinkStatus( void )
{
BaseType_t xResult;

	/* This function returns true if the Link Status in the PHY is high. */
	if( ( ulPHYLinkStatus & BMSR_LINK_STATUS ) != 0 )
	{
		xResult = pdTRUE;
	}
	else
	{
		xResult = pdFALSE;
	}

	return xResult;
}
/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxDescriptor, BaseType_t bReleaseAfterSend )
{
/* Do not wait too long for a free TX DMA buffer. */
const TickType_t xBlockTimeTicks = pdMS_TO_TICKS( 50u );

	do {
		if( ( ulPHYLinkStatus & BMSR_LINK_STATUS ) == 0 )
		{
			/* Do not attempt to send packets as long as the Link Status is low. */
			break;
		}
		if( xTXDescriptorSemaphore == NULL )
		{
			/* Semaphore has not been created yet? */
			break;
		}
		if( xSemaphoreTake( xTXDescriptorSemaphore, xBlockTimeTicks ) != pdPASS )
		{
			/* Time-out waiting for a free TX descriptor. */
			tx_release_count[ 3 ]++;
			break;
		}
		#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
		{
			/* Confirm that the pxDescriptor may be kept by the driver. */
			configASSERT( bReleaseAfterSend != pdFALSE );
		}
		#endif /* ipconfigZERO_COPY_TX_DRIVER */

		gmac_dev_write( &gs_gmac_dev, (void *)pxDescriptor->pucEthernetBuffer, pxDescriptor->xDataLength, prvTxCallback );

		#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
		{
			/* Confirm that the pxDescriptor may be kept by the driver. */
			bReleaseAfterSend = pdFALSE;
		}
		#endif /* ipconfigZERO_COPY_TX_DRIVER */
		/* Not interested in a call-back after TX. */
		iptraceNETWORK_INTERFACE_TRANSMIT();
	} while( 0 );

	if( bReleaseAfterSend != pdFALSE )
	{
		vReleaseNetworkBufferAndDescriptor( pxDescriptor );
	}
	return pdTRUE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvGMACInit( void )
{
uint32_t ncfgr;

	gmac_options_t gmac_option;

	memset( &gmac_option, '\0', sizeof( gmac_option ) );
	gmac_option.uc_copy_all_frame = 0;
	gmac_option.uc_no_boardcast = 0;
	memcpy( gmac_option.uc_mac_addr, ucMACAddress, sizeof( gmac_option.uc_mac_addr ) );

	gs_gmac_dev.p_hw = GMAC;
	gmac_dev_init( GMAC, &gs_gmac_dev, &gmac_option );

	NVIC_SetPriority( GMAC_IRQn, configMAC_INTERRUPT_PRIORITY );
	NVIC_EnableIRQ( GMAC_IRQn );

	/* Contact the Ethernet PHY and store it's address in 'ethernet_phy_addr' */
	ethernet_phy_init( GMAC, ETHERNET_CONF_PHY_ADDR, sysclk_get_cpu_hz() );

	ethernet_phy_auto_negotiate( GMAC, ethernet_phy_addr );
	ethernet_phy_set_link( GMAC, ethernet_phy_addr, 1 );

	/* The GMAC driver will call a hook prvRxCallback(), which
	in turn will wake-up the task by calling vTaskNotifyGiveFromISR() */
	gmac_dev_set_rx_callback( &gs_gmac_dev, prvRxCallback );
	gmac_set_address( GMAC, 1, (uint8_t*)llmnr_mac_address );

	ncfgr = GMAC_NCFGR_SPD | GMAC_NCFGR_FD;

	GMAC->GMAC_NCFGR = ( GMAC->GMAC_NCFGR & ~( GMAC_NCFGR_SPD | GMAC_NCFGR_FD ) ) | ncfgr;

	return 1;
}
/*-----------------------------------------------------------*/

static inline unsigned long ulReadMDIO( unsigned /*short*/ usAddress )
{
uint32_t ulValue, ulReturn;
int rc;

	gmac_enable_management( GMAC, 1 );
	rc = gmac_phy_read( GMAC, ethernet_phy_addr, usAddress, &ulValue );
	gmac_enable_management( GMAC, 0 );
	if( rc == GMAC_OK )
	{
		ulReturn = ulValue;
	}
	else
	{
		ulReturn = 0UL;
	}

	return ulReturn;
}
/*-----------------------------------------------------------*/

static BaseType_t xGMACWaitLS( TickType_t xMaxTime )
{
TickType_t xStartTime = xTaskGetTickCount();
TickType_t xEndTime;
BaseType_t xReturn;
const TickType_t xShortTime = pdMS_TO_TICKS( 100UL );

	for( ;; )
	{
		xEndTime = xTaskGetTickCount();

		if( ( xEndTime - xStartTime ) > xMaxTime )
		{
			/* Wated more than xMaxTime, return. */
			xReturn = pdFALSE;
			break;
		}

		/* Check the link status again. */
		ulPHYLinkStatus = ulReadMDIO( PHY_REG_01_BMSR );

		if( ( ulPHYLinkStatus & BMSR_LINK_STATUS ) != 0 )
		{
			/* Link is up - return. */
			xReturn = pdTRUE;
			break;
		}

		/* Link is down - wait in the Blocked state for a short while (to allow
		other tasks to execute) before checking again. */
		vTaskDelay( xShortTime );
	}

	FreeRTOS_printf( ( "xGMACWaitLS: %ld (PHY %d) freq %lu Mz\n",
		xReturn,
		ethernet_phy_addr,
		sysclk_get_cpu_hz() / HZ_PER_MHZ ) );

	return xReturn;
}
/*-----------------------------------------------------------*/

//#if( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 1 ) && ( ipconfigHAS_TX_CRC_OFFLOADING == 0 )

	void vGMACGenerateChecksum( uint8_t *apBuffer )
	{
	ProtocolPacket_t *xProtPacket = (ProtocolPacket_t *)apBuffer;

		if ( xProtPacket->xTCPPacket.xEthernetHeader.usFrameType == ipIPv4_FRAME_TYPE )
		{
			IPHeader_t *pxIPHeader = &( xProtPacket->xTCPPacket.xIPHeader );

			/* Calculate the IP header checksum. */
			pxIPHeader->usHeaderChecksum = 0x00;
			pxIPHeader->usHeaderChecksum = usGenerateChecksum( 0u, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ipSIZE_OF_IPv4_HEADER );
			pxIPHeader->usHeaderChecksum = ~FreeRTOS_htons( pxIPHeader->usHeaderChecksum );

			/* Calculate the TCP checksum for an outgoing packet. */
			usGenerateProtocolChecksum( ( uint8_t * ) apBuffer, pdTRUE );
		}
	}

//#endif
/*-----------------------------------------------------------*/

static uint32_t prvEMACRxPoll( void )
{
unsigned char *pucUseBuffer;
uint32_t ulReceiveCount, ulResult, ulReturnValue = 0;
static NetworkBufferDescriptor_t *pxNextNetworkBufferDescriptor = NULL;
const UBaseType_t xMinDescriptorsToLeave = 2UL;
const TickType_t xBlockTime = pdMS_TO_TICKS( 100UL );
static IPStackEvent_t xRxEvent = { eNetworkRxEvent, NULL };

	for( ;; )
	{
		/* If pxNextNetworkBufferDescriptor was not left pointing at a valid
		descriptor then allocate one now. */
		if( ( pxNextNetworkBufferDescriptor == NULL ) && ( uxGetNumberOfFreeNetworkBuffers() > xMinDescriptorsToLeave ) )
		{
			pxNextNetworkBufferDescriptor = pxGetNetworkBufferWithDescriptor( ipTOTAL_ETHERNET_FRAME_SIZE, xBlockTime );
		}

		if( pxNextNetworkBufferDescriptor != NULL )
		{
			/* Point pucUseBuffer to the buffer pointed to by the descriptor. */
			pucUseBuffer = ( unsigned char* ) ( pxNextNetworkBufferDescriptor->pucEthernetBuffer - ipconfigPACKET_FILLER_SIZE );
		}
		else
		{
			/* As long as pxNextNetworkBufferDescriptor is NULL, the incoming
			messages will be flushed and ignored. */
			pucUseBuffer = NULL;
		}

		/* Read the next packet from the hardware into pucUseBuffer. */
		ulResult = gmac_dev_read( &gs_gmac_dev, pucUseBuffer, ipTOTAL_ETHERNET_FRAME_SIZE, &ulReceiveCount );

		if( ( ulResult != GMAC_OK ) || ( ulReceiveCount == 0 ) )
		{
			/* No data from the hardware. */
			break;
		}

		if( pxNextNetworkBufferDescriptor == NULL )
		{
			/* Data was read from the hardware, but no descriptor was available
			for it, so it will be dropped. */
			iptraceETHERNET_RX_EVENT_LOST();
			continue;
		}

		iptraceNETWORK_INTERFACE_RECEIVE();
		pxNextNetworkBufferDescriptor->xDataLength = ( size_t ) ulReceiveCount;
		xRxEvent.pvData = ( void * ) pxNextNetworkBufferDescriptor;

		/* Send the descriptor to the IP task for processing. */
		if( xSendEventStructToIPTask( &xRxEvent, xBlockTime ) != pdTRUE )
		{
			/* The buffer could not be sent to the stack so must be released
			again. */
			vReleaseNetworkBufferAndDescriptor( pxNextNetworkBufferDescriptor );
			iptraceETHERNET_RX_EVENT_LOST();
			FreeRTOS_printf( ( "prvEMACRxPoll: Can not queue return packet!\n" ) );
		}

		/* Now the buffer has either been passed to the IP-task,
		or it has been released in the code above. */
		pxNextNetworkBufferDescriptor = NULL;
		ulReturnValue++;
	}

	return ulReturnValue;
}
/*-----------------------------------------------------------*/

void vCheckBuffersAndQueue( void )
{
static UBaseType_t uxLastMinBufferCount = 0;
#if( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
	static UBaseType_t uxLastMinQueueSpace;
#endif
static UBaseType_t uxCurrentCount;

	#if( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
	{
		uxCurrentCount = uxGetMinimumIPQueueSpace();
		if( uxLastMinQueueSpace != uxCurrentCount )
		{
			/* The logging produced below may be helpful
			while tuning +TCP: see how many buffers are in use. */
			uxLastMinQueueSpace = uxCurrentCount;
			FreeRTOS_printf( ( "Queue space: lowest %lu\n", uxCurrentCount ) );
		}
	}
	#endif /* ipconfigCHECK_IP_QUEUE_SPACE */
	uxCurrentCount = uxGetMinimumFreeNetworkBuffers();
	if( uxLastMinBufferCount != uxCurrentCount )
	{
		/* The logging produced below may be helpful
		while tuning +TCP: see how many buffers are in use. */
		uxLastMinBufferCount = uxCurrentCount;
		FreeRTOS_printf( ( "Network buffers: %lu lowest %lu\n",
			uxGetNumberOfFreeNetworkBuffers(), uxCurrentCount ) );
	}

}

static void prvEMACHandlerTask( void *pvParameters )
{
TimeOut_t xPhyTime;
TickType_t xPhyRemTime;
UBaseType_t uxCount;
#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
	NetworkBufferDescriptor_t *pxBuffer;
#endif
uint8_t *pucBuffer;
BaseType_t xResult = 0;
uint32_t xStatus;
const TickType_t ulMaxBlockTime = pdMS_TO_TICKS( EMAC_MAX_BLOCK_TIME_MS );

	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	configASSERT( xEMACTaskHandle );

	vTaskSetTimeOutState( &xPhyTime );
	xPhyRemTime = pdMS_TO_TICKS( PHY_LS_LOW_CHECK_TIME_MS );

	for( ;; )
	{
		vCheckBuffersAndQueue();

		if( ( ulISREvents & EMAC_IF_ALL_EVENT ) == 0 )
		{
			/* No events to process now, wait for the next. */
			ulTaskNotifyTake( pdFALSE, ulMaxBlockTime );
		}

		if( ( ulISREvents & EMAC_IF_RX_EVENT ) != 0 )
		{
			ulISREvents &= ~EMAC_IF_RX_EVENT;

			/* Wait for the EMAC interrupt to indicate that another packet has been
			received. */
			xResult = prvEMACRxPoll();
		}

		if( ( ulISREvents & EMAC_IF_TX_EVENT ) != 0 )
		{
			/* Future extension: code to release TX buffers if zero-copy is used. */
			ulISREvents &= ~EMAC_IF_TX_EVENT;
			while( xQueueReceive( xTxBufferQueue, &pucBuffer, 0 ) != pdFALSE )
			{
				#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
				{
					pxBuffer = pxPacketBuffer_to_NetworkBuffer( pucBuffer );
					if( pxBuffer != NULL )
					{
						vReleaseNetworkBufferAndDescriptor( pxBuffer );
						tx_release_count[ 0 ]++;
					}
					else
					{
						tx_release_count[ 1 ]++;
					}
				}
				#else
				{
					tx_release_count[ 0 ]++;
				}
				#endif
				uxCount = uxQueueMessagesWaiting( ( QueueHandle_t ) xTXDescriptorSemaphore );
				if( uxCount < GMAC_TX_BUFFERS )
				{
					/* Tell the counting semaphore that one more TX descriptor is available. */
					xSemaphoreGive( xTXDescriptorSemaphore );
				}
			}
		}

		if( ( ulISREvents & EMAC_IF_ERR_EVENT ) != 0 )
		{
			/* Future extension: logging about errors that occurred. */
			ulISREvents &= ~EMAC_IF_ERR_EVENT;
		}

		if( xResult > 0 )
		{
			/* A packet was received. No need to check for the PHY status now,
			but set a timer to check it later on. */
			vTaskSetTimeOutState( &xPhyTime );
			xPhyRemTime = pdMS_TO_TICKS( PHY_LS_HIGH_CHECK_TIME_MS );
			xResult = 0;
		}
		else if( xTaskCheckForTimeOut( &xPhyTime, &xPhyRemTime ) != pdFALSE )
		{
			/* Check the link status again. */
			xStatus = ulReadMDIO( PHY_REG_01_BMSR );

			if( ( ulPHYLinkStatus & BMSR_LINK_STATUS ) != ( xStatus & BMSR_LINK_STATUS ) )
			{
				ulPHYLinkStatus = xStatus;
				FreeRTOS_printf( ( "prvEMACHandlerTask: PHY LS now %d\n", ( ulPHYLinkStatus & BMSR_LINK_STATUS ) != 0 ) );
			}

			vTaskSetTimeOutState( &xPhyTime );
			if( ( ulPHYLinkStatus & BMSR_LINK_STATUS ) != 0 )
			{
				xPhyRemTime = pdMS_TO_TICKS( PHY_LS_HIGH_CHECK_TIME_MS );
			}
			else
			{
				xPhyRemTime = pdMS_TO_TICKS( PHY_LS_LOW_CHECK_TIME_MS );
			}
		}
	}
}
/*-----------------------------------------------------------*/
