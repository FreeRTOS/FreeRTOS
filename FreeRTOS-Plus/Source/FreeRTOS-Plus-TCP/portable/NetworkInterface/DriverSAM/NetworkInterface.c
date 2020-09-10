/*
FreeRTOS+TCP V2.2.2
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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

/* Some files from the Atmel Software Framework */
/* gmac_SAM.[ch] is a combination of the gmac.[ch] for both SAM4E and SAME70. */
#include "gmac_SAM.h"
#include <sysclk.h>
#include "phyhandling.h"

/* This file is included to see if 'CONF_BOARD_ENABLE_CACHE' is defined. */
#include "conf_board.h"


/* Interrupt events to process.  Currently only the Rx event is processed
although code for other events is included to allow for possible future
expansion. */
#define EMAC_IF_RX_EVENT        1UL
#define EMAC_IF_TX_EVENT        2UL
#define EMAC_IF_ERR_EVENT       4UL
#define EMAC_IF_ALL_EVENT       ( EMAC_IF_RX_EVENT | EMAC_IF_TX_EVENT | EMAC_IF_ERR_EVENT )

/* 1536 bytes is more than needed, 1524 would be enough.
But 1536 is a multiple of 32, which gives a great alignment for
cached memories. */

#define NETWORK_BUFFER_SIZE		1536

#ifndef	EMAC_MAX_BLOCK_TIME_MS
	/* The task 'prvEMACHandlerTask()' will wake-up every 100 ms, to see
	if something has to be done, mostly checking if the PHY has a
	change in Link Status. */
	#define	EMAC_MAX_BLOCK_TIME_MS	100ul
#endif

#if( ipconfigZERO_COPY_RX_DRIVER == 0 )
	#error This driver works optimal if ipconfigZERO_COPY_RX_DRIVER is defined as 1
#endif

#if( ipconfigZERO_COPY_TX_DRIVER == 0 )
	#error This driver works optimal if ipconfigZERO_COPY_TX_DRIVER is defined as 1
#endif

/* Default the size of the stack used by the EMAC deferred handler task to 4x
the size of the stack used by the idle task - but allow this to be overridden in
FreeRTOSConfig.h as configMINIMAL_STACK_SIZE is a user definable constant. */
#ifndef configEMAC_TASK_STACK_SIZE
	#define configEMAC_TASK_STACK_SIZE ( 4 * configMINIMAL_STACK_SIZE )
#endif

#ifndef niEMAC_HANDLER_TASK_PRIORITY
	#define niEMAC_HANDLER_TASK_PRIORITY	configMAX_PRIORITIES - 1
#endif

#if( __DCACHE_PRESENT != 0 ) && defined( CONF_BOARD_ENABLE_CACHE )
	#include "core_cm7.h"
	#warning This driver assumes the presence of DCACHE
	#define		NETWORK_BUFFERS_CACHED							1
	#define		CACHE_LINE_SIZE									32
	#define		NETWORK_BUFFER_HEADER_SIZE						( ipconfigPACKET_FILLER_SIZE + 8 )

	static void cache_clean_invalidate()
	{
		/* If you application crashes here, make sure that SCB_EnableDCache() has been called. */
		SCB_CleanInvalidateDCache();
	}
	/*-----------------------------------------------------------*/

	static void cache_clean_invalidate_by_addr(uint32_t addr, uint32_t size)
	{
		/* SAME70 does not have clean/invalidate per area. */
		/* SCB_CleanInvalidateDCache_by_Addr( ( uint32_t * )addr, size); */
		SCB_CleanInvalidateDCache();
	}
	/*-----------------------------------------------------------*/

	static void cache_invalidate_by_addr(addr, size) \
	{
		/* SAME70 does not have clean/invalidate per area. */
		/* SCB_InvalidateDCache_by_Addr( ( uint32_t * )addr, size); */
		SCB_InvalidateDCache();
	}
	/*-----------------------------------------------------------*/

#else
	#warning Sure there is no caching?
	#define		cache_clean_invalidate()						do {} while( 0 )
	#define		cache_clean_invalidate_by_addr(addr, size)		do {} while( 0 )
	#define		cache_invalidate_by_addr(addr, size)			do {} while( 0 )
#endif

/*-----------------------------------------------------------*/

/*
 * Update settings in GMAC for speed and duplex.
 */
static void prvEthernetUpdateConfig( BaseType_t xForce );

/*
 * Access functions to the PHY's: read() and write() to be used by
 * phyHandling.c.
 */
static BaseType_t xPHY_Read( BaseType_t xAddress, BaseType_t xRegister, uint32_t *pulValue );
static BaseType_t xPHY_Write( BaseType_t xAddress, BaseType_t xRegister, uint32_t ulValue );

#if( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 1 ) && ( ipconfigHAS_TX_CRC_OFFLOADING == 0 )
	void vGMACGenerateChecksum( uint8_t *apBuffer, size_t uxLength );
#endif

/*
 * Called from the ASF GMAC driver.
 */
void xRxCallback( uint32_t ulStatus );
void xTxCallback( uint32_t ulStatus, uint8_t *puc_buffer );

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

/*
 * Handle transmission errors.
 */
static void hand_tx_errors( void );

/*-----------------------------------------------------------*/

/* Bit map of outstanding ETH interrupt events for processing.  Currently only
the Rx interrupt is handled, although code is included for other events to
enable future expansion. */
static volatile uint32_t ulISREvents;

/* A copy of PHY register 1: 'PHY_REG_01_BMSR' */
static volatile BaseType_t xGMACSwitchRequired;

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

/* For local use only: describe the PHY's properties: */
const PhyProperties_t xPHYProperties =
{
	#if( ipconfigETHERNET_AN_ENABLE != 0 )
		.ucSpeed = PHY_SPEED_AUTO,
		.ucDuplex = PHY_DUPLEX_AUTO,
	#else
		#if( ipconfigETHERNET_USE_100MB != 0 )
			.ucSpeed = PHY_SPEED_100,
		#else
			.ucSpeed = PHY_SPEED_10,
		#endif

		#if( ipconfigETHERNET_USE_FULL_DUPLEX != 0 )
			.ucDuplex = PHY_DUPLEX_FULL,
		#else
			.ucDuplex = PHY_DUPLEX_HALF,
		#endif
	#endif

	#if( ipconfigETHERNET_AN_ENABLE != 0 ) && ( ipconfigETHERNET_AUTO_CROSS_ENABLE != 0 )
		.ucMDI_X = PHY_MDIX_AUTO,
	#elif( ipconfigETHERNET_CROSSED_LINK != 0 )
		.ucMDI_X = PHY_MDIX_CROSSED,
	#else
		.ucMDI_X = PHY_MDIX_DIRECT,
	#endif
};

/* All PHY handling code has now been separated from the NetworkInterface.c,
see "../Common/phyHandling.c". */
static EthernetPhy_t xPhyObject;

/*-----------------------------------------------------------*/

/*
 * GMAC interrupt handler.
 */
void GMAC_Handler(void)
{
	xGMACSwitchRequired = pdFALSE;

	/* gmac_handler() may call xRxCallback() which may change
	the value of xGMACSwitchRequired. */
	gmac_handler( &gs_gmac_dev );

	if( xGMACSwitchRequired != pdFALSE )
	{
		portEND_SWITCHING_ISR( xGMACSwitchRequired );
	}
}
/*-----------------------------------------------------------*/

void xRxCallback( uint32_t ulStatus )
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

void returnTxBuffer(uint8_t *puc_buffer)
{
	/* Called from a non-ISR context. */
	if( xTxBufferQueue != NULL )
	{
		xQueueSend( xTxBufferQueue, &puc_buffer, 0 );
		xTaskNotifyGive( xEMACTaskHandle );
		ulISREvents |= EMAC_IF_TX_EVENT;
	}
}

void xTxCallback( uint32_t ulStatus, uint8_t *puc_buffer )
{
	if( ( xTxBufferQueue != NULL ) && ( xEMACTaskHandle != NULL ) )
	{
		/* let the prvEMACHandlerTask know that there was an TX event. */
		ulISREvents |= EMAC_IF_TX_EVENT;
		/* Wakeup prvEMACHandlerTask. */
		vTaskNotifyGiveFromISR( xEMACTaskHandle, ( BaseType_t * ) &xGMACSwitchRequired );
		xQueueSendFromISR( xTxBufferQueue, &puc_buffer, ( BaseType_t * ) &xGMACSwitchRequired );
		tx_release_count[ 2 ]++;
	}
}
/*-----------------------------------------------------------*/


/*
	The two standard defines 'GMAC_MAN_RW_TYPE' and 'GMAC_MAN_READ_ONLY'
	are incorrect.
	Therefore, use the following:
*/

#define GMAC_MAINTENANCE_READ_ACCESS       (2)
#define GMAC_MAINTENANCE_WRITE_ACCESS      (1)

static BaseType_t xPHY_Read( BaseType_t xAddress, BaseType_t xRegister, uint32_t *pulValue )
{
BaseType_t xReturn;
UBaseType_t uxWasEnabled;

	/* Wait until bus idle */
	while ((GMAC->GMAC_NSR & GMAC_NSR_IDLE) == 0);
	/* Write maintain register */
	/*
	 * OP: Operation: 10 is read. 01 is write.
	 */
	uxWasEnabled = ( GMAC->GMAC_NCR & GMAC_NCR_MPE ) != 0u;
	if( uxWasEnabled == 0u )
	{
		/* Enable further GMAC maintenance. */
		GMAC->GMAC_NCR |= GMAC_NCR_MPE;
	}
	GMAC->GMAC_MAN = GMAC_MAN_WTN(GMAC_MAN_CODE_VALUE)
			| GMAC_MAN_CLTTO
			| GMAC_MAN_PHYA(xAddress)
			| GMAC_MAN_REGA(xRegister)
			| GMAC_MAN_OP(GMAC_MAINTENANCE_READ_ACCESS)
			| GMAC_MAN_DATA( (uint16_t)0u );

	if (gmac_wait_phy(GMAC, MAC_PHY_RETRY_MAX) == GMAC_TIMEOUT)
	{
		*pulValue = (uint32_t)0xffffu;
		xReturn = -1;
	}
	else
	{
		/* Wait until bus idle */
		while ((GMAC->GMAC_NSR & GMAC_NSR_IDLE) == 0);

		/* Return data */
		*pulValue = (uint32_t)(GMAC->GMAC_MAN & GMAC_MAN_DATA_Msk);

		xReturn = 0;
	}
	if( uxWasEnabled == 0u )
	{
		/* Disable further GMAC maintenance. */
		GMAC->GMAC_NCR &= ~GMAC_NCR_MPE;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

static BaseType_t xPHY_Write( BaseType_t xAddress, BaseType_t xRegister, uint32_t ulValue )
{
BaseType_t xReturn;
UBaseType_t uxWasEnabled;

	/* Wait until bus idle */
	while ((GMAC->GMAC_NSR & GMAC_NSR_IDLE) == 0);
	/* Write maintain register */
	uxWasEnabled = ( GMAC->GMAC_NCR & GMAC_NCR_MPE ) != 0u;
	if( uxWasEnabled == 0u )
	{
		/* Enable further GMAC maintenance. */
		GMAC->GMAC_NCR |= GMAC_NCR_MPE;
	}
	GMAC->GMAC_MAN = GMAC_MAN_WTN(GMAC_MAN_CODE_VALUE)
			| GMAC_MAN_CLTTO
			| GMAC_MAN_PHYA(xAddress)
			| GMAC_MAN_REGA(xRegister)
			| GMAC_MAN_OP(GMAC_MAINTENANCE_WRITE_ACCESS)
			| GMAC_MAN_DATA( (uint16_t)ulValue );

	if (gmac_wait_phy(GMAC, MAC_PHY_RETRY_MAX) == GMAC_TIMEOUT )
	{
		xReturn = -1;
	}
	else
	{
		xReturn = 0;
	}
	if( uxWasEnabled == 0u )
	{
		/* Disable further GMAC maintenance. */
		GMAC->GMAC_NCR &= ~GMAC_NCR_MPE;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceInitialise( void )
{
const TickType_t x5_Seconds = 5000UL;

	if( xEMACTaskHandle == NULL )
	{
		prvGMACInit();

		cache_clean_invalidate();

		/* The handler task is created at the highest possible priority to
		ensure the interrupt handler can return directly to it. */
		xTaskCreate( prvEMACHandlerTask, "EMAC", configEMAC_TASK_STACK_SIZE, NULL, niEMAC_HANDLER_TASK_PRIORITY, &xEMACTaskHandle );
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
	return xGetPhyLinkStatus();
}
/*-----------------------------------------------------------*/

BaseType_t xGetPhyLinkStatus( void )
{
BaseType_t xReturn;

	if( xPhyObject.ulLinkStatusMask != 0 )
	{
		xReturn = pdPASS;
	}
	else
	{
		xReturn = pdFAIL;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

/** The GMAC TX errors to handle */
#define GMAC_TX_ERRORS (GMAC_TSR_TFC | GMAC_TSR_HRESP)

static void hand_tx_errors( void )
{
/* Handle GMAC underrun or AHB errors. */
	if (gmac_get_tx_status(GMAC) & GMAC_TX_ERRORS) {

		gmac_enable_transmit(GMAC, false);

		/* Reinit TX descriptors. */
//		gmac_tx_init(ps_gmac_dev);
		gmac_reset_tx_mem(&gs_gmac_dev);
		/* Clear error status. */
		gmac_clear_tx_status(GMAC, GMAC_TX_ERRORS);

		gmac_enable_transmit(GMAC, true);
	}
}

volatile IPPacket_t *pxSendPacket;

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxDescriptor, BaseType_t bReleaseAfterSend )
{
/* Do not wait too long for a free TX DMA buffer. */
const TickType_t xBlockTimeTicks = pdMS_TO_TICKS( 50u );
uint32_t ulTransmitSize;

	ulTransmitSize = pxDescriptor->xDataLength;

	pxSendPacket = (IPPacket_t *)pxDescriptor->pucEthernetBuffer;

	if( ulTransmitSize > NETWORK_BUFFER_SIZE )
	{
		ulTransmitSize = NETWORK_BUFFER_SIZE;
	}
	/* A do{}while(0) loop is introduced to allow the use of multiple break
	statement. */
	do {
		if( xPhyObject.ulLinkStatusMask == 0ul )
		{
			/* Do not attempt to send packets as long as the Link Status is low. */
			break;
		}
		if( xTXDescriptorSemaphore == NULL )
		{
			/* Semaphore has not been created yet? */
			break;
		}
		hand_tx_errors();
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

		#if( NETWORK_BUFFERS_CACHED	!= 0 )
		{
		uint32_t xlength = CACHE_LINE_SIZE * ( ( ulTransmitSize + NETWORK_BUFFER_HEADER_SIZE + CACHE_LINE_SIZE - 1 ) / CACHE_LINE_SIZE );
		uint32_t xAddress = ( uint32_t )( pxDescriptor->pucEthernetBuffer - NETWORK_BUFFER_HEADER_SIZE );
			cache_clean_invalidate_by_addr( xAddress, xlength );
		}
		#endif

		gmac_dev_write( &gs_gmac_dev, (void *)pxDescriptor->pucEthernetBuffer, pxDescriptor->xDataLength );

		#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
		{
			/* Confirm that the pxDescriptor may be kept by the driver. */
			bReleaseAfterSend = pdFALSE;
		}
		#endif /* ipconfigZERO_COPY_TX_DRIVER */
		/* Not interested in a call-back after TX. */
		iptraceNETWORK_INTERFACE_TRANSMIT();
	} while( ipFALSE_BOOL );

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

	gmac_enable_management(GMAC, true);
	/* Enable further GMAC maintenance. */
	GMAC->GMAC_NCR |= GMAC_NCR_MPE;

	memset( &gmac_option, '\0', sizeof( gmac_option ) );
	gmac_option.uc_copy_all_frame = 0;
	gmac_option.uc_no_boardcast = 0;
	memcpy( gmac_option.uc_mac_addr, ucMACAddress, sizeof( gmac_option.uc_mac_addr ) );

	gs_gmac_dev.p_hw = GMAC;
	gmac_dev_init( GMAC, &gs_gmac_dev, &gmac_option );

	NVIC_SetPriority( GMAC_IRQn, configMAC_INTERRUPT_PRIORITY );
	NVIC_EnableIRQ( GMAC_IRQn );

	{
		/* Set MDC clock divider. */
		gmac_set_mdc_clock( GMAC, sysclk_get_cpu_hz() );

		vPhyInitialise( &xPhyObject, xPHY_Read, xPHY_Write );
		xPhyDiscover( &xPhyObject );
		xPhyConfigure( &xPhyObject, &xPHYProperties );

		/* For a reset / reconfigure of the EMAC. */
		prvEthernetUpdateConfig( pdTRUE );

		/* Select Media Independent Interface type */
		#if( SAME70 != 0 )
		{
			/* Selecting RMII mode. */
			GMAC->GMAC_UR &= ~GMAC_UR_RMII;
		}
		#else
		{
			gmac_select_mii_mode(GMAC, ETH_PHY_MODE);
		}
		#endif

		gmac_enable_transmit(GMAC, true);
		gmac_enable_receive(GMAC, true);

	}

	gmac_enable_management(GMAC, true);

	gmac_set_address( GMAC, 1, (uint8_t*)llmnr_mac_address );

	gmac_enable_management(GMAC, false);
	/* Disable further GMAC maintenance. */
	GMAC->GMAC_NCR &= ~GMAC_NCR_MPE;

	return 1;
}
/*-----------------------------------------------------------*/

static void prvEthernetUpdateConfig( BaseType_t xForce )
{
	FreeRTOS_printf( ( "prvEthernetUpdateConfig: LS mask %02lX Force %d\n",
		xPhyObject.ulLinkStatusMask,
		( int )xForce ) );

	if( ( xForce != pdFALSE ) || ( xPhyObject.ulLinkStatusMask != 0 ) )
	{
		#if( ipconfigETHERNET_AN_ENABLE != 0 )
		{
		UBaseType_t uxWasEnabled;

			/* Restart the auto-negotiation. */
			uxWasEnabled = ( GMAC->GMAC_NCR & GMAC_NCR_MPE ) != 0u;
			if( uxWasEnabled == 0u )
			{
				/* Enable further GMAC maintenance. */
				GMAC->GMAC_NCR |= GMAC_NCR_MPE;
			}
			xPhyStartAutoNegotiation( &xPhyObject, xPhyGetMask( &xPhyObject ) );

			/* Configure the MAC with the Duplex Mode fixed by the
			auto-negotiation process. */
			if( xPhyObject.xPhyProperties.ucDuplex == PHY_DUPLEX_FULL )
			{
				gmac_enable_full_duplex(GMAC, pdTRUE);
			}
			else
			{
				gmac_enable_full_duplex(GMAC, pdFALSE);
			}

			/* Configure the MAC with the speed fixed by the
			auto-negotiation process. */
			if( xPhyObject.xPhyProperties.ucSpeed == PHY_SPEED_10 )
			{
				gmac_set_speed(GMAC, pdFALSE);
			}
			else
			{
				gmac_set_speed(GMAC, pdTRUE);
			}
			if( uxWasEnabled == 0u )
			{
				/* Enable further GMAC maintenance. */
				GMAC->GMAC_NCR &= ~GMAC_NCR_MPE;
			}
		}
		#else
		{
			if( xPHYProperties.ucDuplex == PHY_DUPLEX_FULL )
			{
				xPhyObject.xPhyPreferences.ucDuplex = PHY_DUPLEX_FULL;
				gmac_enable_full_duplex(GMAC, pdTRUE);
			}
			else
			{
				xPhyObject.xPhyPreferences.ucDuplex = PHY_DUPLEX_HALF;
				gmac_enable_full_duplex(GMAC, pdFALSE);
			}

			if( xPHYProperties.ucSpeed == PHY_SPEED_100 )
			{
				xPhyObject.xPhyPreferences.ucSpeed = PHY_SPEED_100;
				gmac_set_speed(GMAC, pdTRUE);
			}
			else
			{
				xPhyObject.xPhyPreferences.ucSpeed = PHY_SPEED_10;
				gmac_set_speed(GMAC, pdFALSE);
			}

			xPhyObject.xPhyPreferences.ucMDI_X = PHY_MDIX_AUTO;

			/* Use predefined (fixed) configuration. */
			xPhyFixedValue( &xPhyObject, xPhyGetMask( &xPhyObject ) );
		}
		#endif

	}
}
/*-----------------------------------------------------------*/

void vGMACGenerateChecksum( uint8_t *pucBuffer, size_t uxLength )
{
ProtocolPacket_t *xProtPacket = ( ProtocolPacket_t * ) pucBuffer;

	if ( xProtPacket->xTCPPacket.xEthernetHeader.usFrameType == ipIPv4_FRAME_TYPE )
	{
		IPHeader_t *pxIPHeader = &( xProtPacket->xTCPPacket.xIPHeader );

		/* Calculate the IP header checksum. */
		pxIPHeader->usHeaderChecksum = 0x00;
		pxIPHeader->usHeaderChecksum = usGenerateChecksum( 0U, ( uint8_t * ) &( pxIPHeader->ucVersionHeaderLength ), ipSIZE_OF_IPv4_HEADER );
		pxIPHeader->usHeaderChecksum = ~FreeRTOS_htons( pxIPHeader->usHeaderChecksum );

		/* Calculate the TCP checksum for an outgoing packet. */
		usGenerateProtocolChecksum( pucBuffer, uxLength, pdTRUE );
	}
}
/*-----------------------------------------------------------*/

static uint32_t prvEMACRxPoll( void )
{
unsigned char *pucUseBuffer;
uint32_t ulReceiveCount, ulResult, ulReturnValue = 0;
static NetworkBufferDescriptor_t *pxNextNetworkBufferDescriptor = NULL;
const UBaseType_t xMinDescriptorsToLeave = 2UL;
const TickType_t xBlockTime = pdMS_TO_TICKS( 100UL );
static IPStackEvent_t xRxEvent = { eNetworkRxEvent, NULL };
uint8_t *pucDMABuffer = NULL;

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
		ulResult = gmac_dev_read( &gs_gmac_dev, pucUseBuffer, ipTOTAL_ETHERNET_FRAME_SIZE, &ulReceiveCount, &pucDMABuffer );

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
		#if( ipconfigZERO_COPY_RX_DRIVER != 0 )
		{
			pxNextNetworkBufferDescriptor = pxPacketBuffer_to_NetworkBuffer( pucDMABuffer );
			if( pxNextNetworkBufferDescriptor == NULL )
			{
				/* STrange: can not translate from a DMA buffer to a Network Buffer. */
				break;
			}
		}
		#endif /* ipconfigZERO_COPY_RX_DRIVER */
 
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

volatile UBaseType_t uxLastMinBufferCount = 0;
#if( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
	volatile UBaseType_t uxLastMinQueueSpace;
#endif
volatile UBaseType_t uxCurrentSemCount;
volatile UBaseType_t uxLowestSemCount;

void vCheckBuffersAndQueue( void )
{
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
	if( xTXDescriptorSemaphore != NULL )
	{
		uxCurrentSemCount = uxSemaphoreGetCount( xTXDescriptorSemaphore );
		if( uxLowestSemCount > uxCurrentSemCount )
		{
			uxLowestSemCount = uxCurrentSemCount;
			FreeRTOS_printf( ( "TX DMA buffers: lowest %lu\n", uxLowestSemCount ) );
		}

	}

}
/*-----------------------------------------------------------*/

extern uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS * NETWORK_BUFFER_SIZE ];
void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
uint8_t *ucRAMBuffer = ucNetworkPackets;
uint32_t ulIndex;

	for( ulIndex = 0; ulIndex < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ulIndex++ )
	{
		pxNetworkBuffers[ ulIndex ].pucEthernetBuffer = ucRAMBuffer + ipBUFFER_PADDING;
		*( ( unsigned * ) ucRAMBuffer ) = ( unsigned ) ( &( pxNetworkBuffers[ ulIndex ] ) );
		ucRAMBuffer += NETWORK_BUFFER_SIZE;
	}
	cache_clean_invalidate();
}
/*-----------------------------------------------------------*/

static void prvEMACHandlerTask( void *pvParameters )
{
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

	for( ;; )
	{
		xResult = 0;
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
		gmac_enable_management(GMAC, true);
		if( xPhyCheckLinkStatus( &xPhyObject, xResult ) != 0 )
		{
			/* Something has changed to a Link Status, need re-check. */
			prvEthernetUpdateConfig( pdFALSE );
		}
		gmac_enable_management(GMAC, false);
	}
}
/*-----------------------------------------------------------*/
