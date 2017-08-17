/*
 * Some constants, hardware definitions and comments taken from ST's HAL driver
 * library, COPYRIGHT(c) 2015 STMicroelectronics.
 */

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

/* ST includes. */
#include "stm32f4xx_hal.h"

#ifndef	BMSR_LINK_STATUS
	#define BMSR_LINK_STATUS            0x0004UL
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

#define ETH_DMA_ALL_INTS \
	( ETH_DMA_IT_TST | ETH_DMA_IT_PMT | ETH_DMA_IT_MMC | ETH_DMA_IT_NIS | ETH_DMA_IT_ER | \
	  ETH_DMA_IT_FBE | ETH_DMA_IT_RWT | ETH_DMA_IT_RPS | ETH_DMA_IT_RBU | ETH_DMA_IT_R | \
	  ETH_DMA_IT_TU | ETH_DMA_IT_RO | ETH_DMA_IT_TJT | ETH_DMA_IT_TPS | ETH_DMA_IT_T )

/* Naming and numbering of PHY registers. */
#define PHY_REG_00_BMCR			0x00	/* Basic Mode Control Register. */
#define PHY_REG_01_BMSR			0x01	/* Basic Mode Status Register. */
#define PHY_REG_02_PHYSID1		0x02	/* PHYS ID 1 */
#define PHY_REG_03_PHYSID2		0x03	/* PHYS ID 2 */
#define PHY_REG_04_ADVERTISE	0x04	/* Advertisement control reg */

#define PHY_ID_LAN8720		0x0007c0f0
#define PHY_ID_DP83848I		0x20005C90

#ifndef USE_STM324xG_EVAL
	#define USE_STM324xG_EVAL	1
#endif

#if( USE_STM324xG_EVAL == 0 )
	#define EXPECTED_PHY_ID			PHY_ID_LAN8720
	#define	PHY_REG_1F_PHYSPCS		0x1F	/* 31 RW PHY Special Control Status */
	/* Use 3 bits in register 31 */
	#define PHYSPCS_SPEED_MASK		0x0C
	#define PHYSPCS_SPEED_10		0x04
	#define PHYSPCS_SPEED_100		0x08
	#define PHYSPCS_FULL_DUPLEX		0x10
#else
	#define EXPECTED_PHY_ID		PHY_ID_DP83848I

	#define PHY_REG_10_PHY_SR		0x10	/* PHY status register Offset */
	#define	PHY_REG_19_PHYCR		0x19	/* 25 RW PHY Control Register */
#endif

/* Some defines used internally here to indicate preferences about speed, MDIX
(wired direct or crossed), and duplex (half or full). */
#define	PHY_SPEED_10       1
#define	PHY_SPEED_100      2
#define	PHY_SPEED_AUTO     (PHY_SPEED_10|PHY_SPEED_100)

#define	PHY_MDIX_DIRECT    1
#define	PHY_MDIX_CROSSED   2
#define	PHY_MDIX_AUTO      (PHY_MDIX_CROSSED|PHY_MDIX_DIRECT)

#define	PHY_DUPLEX_HALF    1
#define	PHY_DUPLEX_FULL    2
#define	PHY_DUPLEX_AUTO    (PHY_DUPLEX_FULL|PHY_DUPLEX_HALF)

#define PHY_AUTONEGO_COMPLETE    ((uint16_t)0x0020)  /*!< Auto-Negotiation process completed   */

/*
 * Description of all capabilities that can be advertised to
 * the peer (usually a switch or router).
 */
#define ADVERTISE_CSMA			0x0001		/* Only selector supported. */
#define ADVERTISE_10HALF		0x0020		/* Try for 10mbps half-duplex. */
#define ADVERTISE_10FULL		0x0040		/* Try for 10mbps full-duplex. */
#define ADVERTISE_100HALF		0x0080		/* Try for 100mbps half-duplex. */
#define ADVERTISE_100FULL		0x0100		/* Try for 100mbps full-duplex. */

#define ADVERTISE_ALL			( ADVERTISE_10HALF | ADVERTISE_10FULL | \
								  ADVERTISE_100HALF | ADVERTISE_100FULL)

/*
 * Value for the 'PHY_REG_00_BMCR', the PHY's Basic Mode Control Register.
 */
#define BMCR_FULLDPLX			0x0100		/* Full duplex. */
#define BMCR_ANRESTART			0x0200		/* Auto negotiation restart. */
#define BMCR_ANENABLE			0x1000		/* Enable auto negotiation. */
#define BMCR_SPEED100			0x2000		/* Select 100Mbps. */
#define BMCR_RESET				0x8000		/* Reset the PHY. */

#define PHYCR_MDIX_EN			0x8000		/* Enable Auto MDIX. */
#define PHYCR_MDIX_FORCE		0x4000		/* Force MDIX crossed. */

#define ipFRAGMENT_OFFSET_BIT_MASK		( ( uint16_t ) 0x0fff ) /* The bits in the two byte IP header field that make up the fragment offset value. */

/*
 * Most users will want a PHY that negotiates about
 * the connection properties: speed, dmix and duplex.
 * On some rare cases, you want to select what is being
 * advertised, properties like MDIX and duplex.
 */

#if !defined( ipconfigETHERNET_AN_ENABLE )
	/* Enable auto-negotiation */
	#define ipconfigETHERNET_AN_ENABLE				1
#endif

#if !defined( ipconfigETHERNET_AUTO_CROSS_ENABLE )
	#define ipconfigETHERNET_AUTO_CROSS_ENABLE		1
#endif

#if( ipconfigETHERNET_AN_ENABLE == 0 )
	/*
	 * The following three defines are only used in case there
	 * is no auto-negotiation.
	 */
	#if !defined( ipconfigETHERNET_CROSSED_LINK )
		#define	ipconfigETHERNET_CROSSED_LINK			1
	#endif

	#if !defined( ipconfigETHERNET_USE_100MB )
		#define ipconfigETHERNET_USE_100MB				1
	#endif

	#if !defined( ipconfigETHERNET_USE_FULL_DUPLEX )
		#define ipconfigETHERNET_USE_FULL_DUPLEX		1
	#endif
#endif /* ipconfigETHERNET_AN_ENABLE == 0 */

/* Default the size of the stack used by the EMAC deferred handler task to twice
the size of the stack used by the idle task - but allow this to be overridden in
FreeRTOSConfig.h as configMINIMAL_STACK_SIZE is a user definable constant. */
#ifndef configEMAC_TASK_STACK_SIZE
	#define configEMAC_TASK_STACK_SIZE ( 2 * configMINIMAL_STACK_SIZE )
#endif

/*-----------------------------------------------------------*/

/*
 * A deferred interrupt handler task that processes
 */
static void prvEMACHandlerTask( void *pvParameters );

/*
 * Force a negotiation with the Switch or Router and wait for LS.
 */
static void prvEthernetUpdateConfig( BaseType_t xForce );

/*
 * See if there is a new packet and forward it to the IP-task.
 */
static BaseType_t prvNetworkInterfaceInput( void );

#if( ipconfigUSE_LLMNR != 0 )
	/*
	 * For LLMNR, an extra MAC-address must be configured to
	 * be able to receive the multicast messages.
	 */
	static void prvMACAddressConfig(ETH_HandleTypeDef *heth, uint32_t ulIndex, uint8_t *Addr);
#endif

/*
 * Check if a given packet should be accepted.
 */
static BaseType_t xMayAcceptPacket( uint8_t *pcBuffer );

/*
 * Initialise the TX descriptors.
 */
static void prvDMATxDescListInit( void );

/*
 * Initialise the RX descriptors.
 */
static void prvDMARxDescListInit( void );

#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
	/* After packets have been sent, the network
	buffers will be released. */
	static void vClearTXBuffers( void );
#endif /* ipconfigZERO_COPY_TX_DRIVER */

/*-----------------------------------------------------------*/

typedef struct _PhyProperties_t
{
	uint8_t speed;
	uint8_t mdix;
	uint8_t duplex;
	uint8_t spare;
} PhyProperties_t;

/* Bit map of outstanding ETH interrupt events for processing.  Currently only
the Rx interrupt is handled, although code is included for other events to
enable future expansion. */
static volatile uint32_t ulISREvents;

/* A copy of PHY register 1: 'PHY_REG_01_BMSR' */
static uint32_t ulPHYLinkStatus = 0;

#if( ipconfigUSE_LLMNR == 1 )
	static const uint8_t xLLMNR_MACAddress[] = { 0x01, 0x00, 0x5E, 0x00, 0x00, 0xFC };
#endif

/* Ethernet handle. */
static ETH_HandleTypeDef xETH;

#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
	/* xTXDescriptorSemaphore is a counting semaphore with
	a maximum count of ETH_TXBUFNB, which is the number of
	DMA TX descriptors. */
	static SemaphoreHandle_t xTXDescriptorSemaphore = NULL;
#endif /* ipconfigZERO_COPY_TX_DRIVER */

/*
 * Note: it is adviced to define both
 *
 *     #define  ipconfigZERO_COPY_RX_DRIVER   1
 *     #define  ipconfigZERO_COPY_TX_DRIVER   1
 *
 * The method using memcpy is slower and probaly uses more RAM memory.
 * The possibility is left in the code just for comparison.
 *
 * It is adviced to define ETH_TXBUFNB at least 4. Note that no
 * TX buffers are allocated in a zero-copy driver.
 */
/* MAC buffers: ---------------------------------------------------------*/
__ALIGN_BEGIN ETH_DMADescTypeDef  DMARxDscrTab[ ETH_RXBUFNB ] __ALIGN_END;/* Ethernet Rx MA Descriptor */
#if( ipconfigZERO_COPY_RX_DRIVER == 0 )
	__ALIGN_BEGIN uint8_t Rx_Buff[ ETH_RXBUFNB ][ ETH_RX_BUF_SIZE ] __ALIGN_END; /* Ethernet Receive Buffer */
#endif

__ALIGN_BEGIN ETH_DMADescTypeDef  DMATxDscrTab[ ETH_TXBUFNB ] __ALIGN_END;/* Ethernet Tx DMA Descriptor */
#if( ipconfigZERO_COPY_TX_DRIVER == 0 )
	__ALIGN_BEGIN uint8_t Tx_Buff[ ETH_TXBUFNB ][ ETH_TX_BUF_SIZE ] __ALIGN_END; /* Ethernet Transmit Buffer */
#endif

#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
	/* DMATxDescToClear points to the next TX DMA descriptor
	that must be cleared by vClearTXBuffers(). */
	static __IO ETH_DMADescTypeDef  *DMATxDescToClear;
#endif

/* Value to be written into the 'Basic mode Control Register'. */
static uint32_t ulBCRvalue;

/* Value to be written into the 'Advertisement Control Register'. */
static uint32_t ulACRValue;

/* ucMACAddress as it appears in main.c */
extern const uint8_t ucMACAddress[ 6 ];

/* Holds the handle of the task used as a deferred interrupt processor.  The
handle is used so direct notifications can be sent to the task for all EMAC/DMA
related interrupts. */
static TaskHandle_t xEMACTaskHandle = NULL;

/* For local use only: describe the PHY's properties: */
const PhyProperties_t xPHYProperties =
{
	#if( ipconfigETHERNET_AN_ENABLE != 0 )
		.speed = PHY_SPEED_AUTO,
		.duplex = PHY_DUPLEX_AUTO,
	#else
		#if( ipconfigETHERNET_USE_100MB != 0 )
			.speed = PHY_SPEED_100,
		#else
			.speed = PHY_SPEED_10,
		#endif

		#if( ipconfigETHERNET_USE_FULL_DUPLEX != 0 )
			.duplex = PHY_DUPLEX_FULL,
		#else
			.duplex = PHY_DUPLEX_HALF,
		#endif
	#endif

	#if( ipconfigETHERNET_AN_ENABLE != 0 ) && ( ipconfigETHERNET_AUTO_CROSS_ENABLE != 0 )
		.mdix = PHY_MDIX_AUTO,
	#elif( ipconfigETHERNET_CROSSED_LINK != 0 )
		.mdix = PHY_MDIX_CROSSED,
	#else
		.mdix = PHY_MDIX_DIRECT,
	#endif
};

/*-----------------------------------------------------------*/

void HAL_ETH_RxCpltCallback( ETH_HandleTypeDef *heth )
{
BaseType_t xHigherPriorityTaskWoken = pdFALSE;

	/* Ethernet RX-Complete callback function, elsewhere declared as weak. */
    ulISREvents |= EMAC_IF_RX_EVENT;
	/* Wakeup the prvEMACHandlerTask. */
	if( xEMACTaskHandle != NULL )
	{
		vTaskNotifyGiveFromISR( xEMACTaskHandle, &xHigherPriorityTaskWoken );
		portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
	}
}
/*-----------------------------------------------------------*/

#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
	void HAL_ETH_TxCpltCallback( ETH_HandleTypeDef *heth )
	{
	BaseType_t xHigherPriorityTaskWoken = pdFALSE;

		/* This call-back is only useful in case packets are being sent
		zero-copy.  Once they're sent, the buffers will be released
		by the function vClearTXBuffers(). */
		ulISREvents |= EMAC_IF_TX_EVENT;
		/* Wakeup the prvEMACHandlerTask. */
		if( xEMACTaskHandle != NULL )
		{
			vTaskNotifyGiveFromISR( xEMACTaskHandle, &xHigherPriorityTaskWoken );
			portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
		}

	}
#endif /* ipconfigZERO_COPY_TX_DRIVER */

/*-----------------------------------------------------------*/

#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
	static void vClearTXBuffers()
	{
	__IO ETH_DMADescTypeDef  *txLastDescriptor = xETH.TxDesc;
	NetworkBufferDescriptor_t *pxNetworkBuffer;
	uint8_t *ucPayLoad;
	size_t uxCount = ( ( UBaseType_t ) ETH_TXBUFNB ) - uxSemaphoreGetCount( xTXDescriptorSemaphore );

		/* This function is called after a TX-completion interrupt.
		It will release each Network Buffer used in xNetworkInterfaceOutput().
		'uxCount' represents the number of descriptors given to DMA for transmission.
		After sending a packet, the DMA will clear the 'ETH_DMATXDESC_OWN' bit. */
		while( ( uxCount > 0 ) && ( ( DMATxDescToClear->Status & ETH_DMATXDESC_OWN ) == 0 ) )
		{
			if( ( DMATxDescToClear == txLastDescriptor ) && ( uxCount != ETH_TXBUFNB ) )
			{
				break;
			}

			ucPayLoad = ( uint8_t * )DMATxDescToClear->Buffer1Addr;

			if( ucPayLoad != NULL )
			{
				pxNetworkBuffer = pxPacketBuffer_to_NetworkBuffer( ucPayLoad );
				if( pxNetworkBuffer != NULL )
				{
					vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer ) ;
				}
				DMATxDescToClear->Buffer1Addr = ( uint32_t )0u;
			}

			DMATxDescToClear = ( ETH_DMADescTypeDef * )( DMATxDescToClear->Buffer2NextDescAddr );

			uxCount--;
			/* Tell the counting semaphore that one more TX descriptor is available. */
			xSemaphoreGive( xTXDescriptorSemaphore );
		}
	}
#endif /* ipconfigZERO_COPY_TX_DRIVER */
/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceInitialise( void )
{
HAL_StatusTypeDef hal_eth_init_status;
BaseType_t xResult;

	if( xEMACTaskHandle == NULL )
	{
		#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
		{
			if( xTXDescriptorSemaphore == NULL )
			{
				xTXDescriptorSemaphore = xSemaphoreCreateCounting( ( UBaseType_t ) ETH_TXBUFNB, ( UBaseType_t ) ETH_TXBUFNB );
				configASSERT( xTXDescriptorSemaphore );
			}
		}
		#endif /* ipconfigZERO_COPY_TX_DRIVER */

		/* Initialise ETH */

		xETH.Instance = ETH;
		xETH.Init.AutoNegotiation = ETH_AUTONEGOTIATION_ENABLE;
		xETH.Init.Speed = ETH_SPEED_100M;
		xETH.Init.DuplexMode = ETH_MODE_FULLDUPLEX;
		xETH.Init.PhyAddress = 1;

		xETH.Init.MACAddr = ( uint8_t *) ucMACAddress;
		xETH.Init.RxMode = ETH_RXINTERRUPT_MODE;

		/* using the ETH_CHECKSUM_BY_HARDWARE option:
		both the IP and the protocol checksums will be calculated
		by the peripheral. */
		xETH.Init.ChecksumMode = ETH_CHECKSUM_BY_HARDWARE;

		xETH.Init.MediaInterface = ETH_MEDIA_INTERFACE_MII;
		hal_eth_init_status = HAL_ETH_Init( &xETH );

		/* Only for inspection by debugger. */
		( void ) hal_eth_init_status;

		/* Set the TxDesc and RxDesc pointers. */
		xETH.TxDesc = DMATxDscrTab;
		xETH.RxDesc = DMARxDscrTab;

		/* Make sure that all unused fields are cleared. */
		memset( &DMATxDscrTab, '\0', sizeof( DMATxDscrTab ) );
		memset( &DMARxDscrTab, '\0', sizeof( DMARxDscrTab ) );

		#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
		{
			/* Initialize Tx Descriptors list: Chain Mode */
			DMATxDescToClear = DMATxDscrTab;
		}
		#endif /* ipconfigZERO_COPY_TX_DRIVER */

		/* Initialise TX-descriptors. */
		prvDMATxDescListInit();

		/* Initialise RX-descriptors. */
		prvDMARxDescListInit();

		#if( ipconfigUSE_LLMNR != 0 )
		{
			/* Program the LLMNR address at index 1. */
			prvMACAddressConfig( &xETH, ETH_MAC_ADDRESS1, ( uint8_t *) xLLMNR_MACAddress );
		}
		#endif

		/* Force a negotiation with the Switch or Router and wait for LS. */
		prvEthernetUpdateConfig( pdTRUE );

		/* The deferred interrupt handler task is created at the highest
		possible priority to ensure the interrupt handler can return directly
		to it.  The task's handle is stored in xEMACTaskHandle so interrupts can
		notify the task when there is something to process. */
		xTaskCreate( prvEMACHandlerTask, "EMAC", configEMAC_TASK_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xEMACTaskHandle );
	} /* if( xEMACTaskHandle == NULL ) */

	if( ( ulPHYLinkStatus & BMSR_LINK_STATUS ) != 0 )
	{
		xETH.Instance->DMAIER |= ETH_DMA_ALL_INTS;
		xResult = pdPASS;
		FreeRTOS_printf( ( "Link Status is high\n" ) ) ;
	}
	else
	{
		/* For now pdFAIL will be returned. But prvEMACHandlerTask() is running
		and it will keep on checking the PHY and set ulPHYLinkStatus when necessary. */
		xResult = pdFAIL;
		FreeRTOS_printf( ( "Link Status still low\n" ) ) ;
	}
	/* When returning non-zero, the stack will become active and
    start DHCP (in configured) */
	return xResult;
}
/*-----------------------------------------------------------*/

static void prvDMATxDescListInit()
{
ETH_DMADescTypeDef *pxDMADescriptor;
BaseType_t xIndex;

	/* Get the pointer on the first member of the descriptor list */
	pxDMADescriptor = DMATxDscrTab;

	/* Fill each DMA descriptor with the right values */
	for( xIndex = 0; xIndex < ETH_TXBUFNB; xIndex++, pxDMADescriptor++ )
	{
		/* Set Second Address Chained bit */
		pxDMADescriptor->Status = ETH_DMATXDESC_TCH;

		#if( ipconfigZERO_COPY_TX_DRIVER == 0 )
		{
			/* Set Buffer1 address pointer */
			pxDMADescriptor->Buffer1Addr = ( uint32_t )( Tx_Buff[ xIndex ] );
		}
		#endif

		if( xETH.Init.ChecksumMode == ETH_CHECKSUM_BY_HARDWARE )
		{
			/* Set the DMA Tx descriptors checksum insertion for TCP, UDP, and ICMP */
			pxDMADescriptor->Status |= ETH_DMATXDESC_CHECKSUMTCPUDPICMPFULL;
		}

		/* Initialize the next descriptor with the Next Descriptor Polling Enable */
		if( xIndex < ETH_TXBUFNB - 1 )
		{
			/* Set next descriptor address register with next descriptor base address */
			pxDMADescriptor->Buffer2NextDescAddr = ( uint32_t ) ( pxDMADescriptor + 1 );
		}
		else
		{
			/* For last descriptor, set next descriptor address register equal to the first descriptor base address */
			pxDMADescriptor->Buffer2NextDescAddr = ( uint32_t ) DMATxDscrTab;
		}
	}

	/* Set Transmit Descriptor List Address Register */
	xETH.Instance->DMATDLAR = ( uint32_t ) DMATxDscrTab;
}
/*-----------------------------------------------------------*/

static void prvDMARxDescListInit()
{
ETH_DMADescTypeDef *pxDMADescriptor;
BaseType_t xIndex;
	/*
	 * RX-descriptors.
	 */

	/* Get the pointer on the first member of the descriptor list */
	pxDMADescriptor = DMARxDscrTab;

	/* Fill each DMA descriptor with the right values */
	for( xIndex = 0; xIndex < ETH_RXBUFNB; xIndex++, pxDMADescriptor++ )
	{

		/* Set Buffer1 size and Second Address Chained bit */
		pxDMADescriptor->ControlBufferSize = ETH_DMARXDESC_RCH | (uint32_t)ETH_RX_BUF_SIZE;  

		#if( ipconfigZERO_COPY_RX_DRIVER != 0 )
		{
		/* Set Buffer1 address pointer */
		NetworkBufferDescriptor_t *pxBuffer;

			pxBuffer = pxGetNetworkBufferWithDescriptor( ETH_RX_BUF_SIZE, 100ul );
			/* If the assert below fails, make sure that there are at least 'ETH_RXBUFNB'
			Network Buffers available during start-up ( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ) */
			configASSERT( pxBuffer != NULL );
			if( pxBuffer != NULL )
			{
				pxDMADescriptor->Buffer1Addr = (uint32_t)pxBuffer->pucEthernetBuffer;
				pxDMADescriptor->Status = ETH_DMARXDESC_OWN;
			}
		}
		#else
		{
			/* Set Buffer1 address pointer */
			pxDMADescriptor->Buffer1Addr = ( uint32_t )( Rx_Buff[ xIndex ] );
			/* Set Own bit of the Rx descriptor Status */
			pxDMADescriptor->Status = ETH_DMARXDESC_OWN;
		}
		#endif

		/* Initialize the next descriptor with the Next Descriptor Polling Enable */
		if( xIndex < ETH_RXBUFNB - 1 )
		{
			/* Set next descriptor address register with next descriptor base address */
			pxDMADescriptor->Buffer2NextDescAddr = ( uint32_t )( pxDMADescriptor + 1 );
		}
		else
		{
			/* For last descriptor, set next descriptor address register equal to the first descriptor base address */
			pxDMADescriptor->Buffer2NextDescAddr = ( uint32_t ) DMARxDscrTab;
		}

	}
	/* Set Receive Descriptor List Address Register */
	xETH.Instance->DMARDLAR = ( uint32_t ) DMARxDscrTab;
}
/*-----------------------------------------------------------*/

static void prvMACAddressConfig(ETH_HandleTypeDef *heth, uint32_t ulIndex, uint8_t *Addr)
{
uint32_t ulTempReg;

	/* Calculate the selected MAC address high register. */
	ulTempReg = 0x80000000ul | ( ( uint32_t ) Addr[ 5 ] << 8 ) | ( uint32_t ) Addr[ 4 ];

	/* Load the selected MAC address high register. */
	( *(__IO uint32_t *)( ( uint32_t ) ( ETH_MAC_ADDR_HBASE + ulIndex ) ) ) = ulTempReg;

	/* Calculate the selected MAC address low register. */
	ulTempReg = ( ( uint32_t ) Addr[ 3 ] << 24 ) | ( ( uint32_t ) Addr[ 2 ] << 16 ) | ( ( uint32_t ) Addr[ 1 ] << 8 ) | Addr[ 0 ];

	/* Load the selected MAC address low register */
	( *(__IO uint32_t *) ( ( uint32_t ) ( ETH_MAC_ADDR_LBASE + ulIndex ) ) ) = ulTempReg;
}
/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxDescriptor, BaseType_t bReleaseAfterSend )
{
BaseType_t xReturn = pdFAIL;
uint32_t ulTransmitSize = 0;
__IO ETH_DMADescTypeDef *pxDmaTxDesc;
/* Do not wait too long for a free TX DMA buffer. */
const TickType_t xBlockTimeTicks = pdMS_TO_TICKS( 50u );

	#if( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM != 0 )
	{
	ProtocolPacket_t *pxPacket;

		/* If the peripheral must calculate the checksum, it wants
		the protocol checksum to have a value of zero. */
		pxPacket = ( ProtocolPacket_t * ) ( pxDescriptor->pucEthernetBuffer );

		if( pxPacket->xICMPPacket.xIPHeader.ucProtocol == ipPROTOCOL_ICMP )
		{
			pxPacket->xICMPPacket.xICMPHeader.usChecksum = ( uint16_t )0u;
		}
	}
	#endif

	/* Open a do {} while ( 0 ) loop to be able to call break. */
	do
	{
		if( ( ulPHYLinkStatus & BMSR_LINK_STATUS ) != 0 )
		{
			#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
			{
				if( xTXDescriptorSemaphore == NULL )
				{
					break;
				}
				if( xSemaphoreTake( xTXDescriptorSemaphore, xBlockTimeTicks ) != pdPASS )
				{
					/* Time-out waiting for a free TX descriptor. */
					break;
				}
			}
			#endif /* ipconfigZERO_COPY_TX_DRIVER */

			/* This function does the actual transmission of the packet. The packet is
			contained in 'pxDescriptor' that is passed to the function. */
			pxDmaTxDesc = xETH.TxDesc;

			/* Is this buffer available? */
			if( ( pxDmaTxDesc->Status & ETH_DMATXDESC_OWN ) == 0 )
			{
				/* Is this buffer available? */
				/* Get bytes in current buffer. */
				ulTransmitSize = pxDescriptor->xDataLength;

				if( ulTransmitSize > ETH_TX_BUF_SIZE )
				{
					ulTransmitSize = ETH_TX_BUF_SIZE;
				}

				#if( ipconfigZERO_COPY_TX_DRIVER == 0 )
				{
					/* Copy the bytes. */
					memcpy( ( void * ) pxDmaTxDesc->Buffer1Addr, pxDescriptor->pucEthernetBuffer, ulTransmitSize );
					pxDmaTxDesc->Status |= ETH_DMATXDESC_CIC_TCPUDPICMP_FULL;
				}
				#else
				{
					/* Move the buffer. */
					pxDmaTxDesc->Buffer1Addr = ( uint32_t )pxDescriptor->pucEthernetBuffer;
					/* Ask to set the IPv4 checksum.
					Also need an Interrupt on Completion so that 'vClearTXBuffers()' will be called.. */
					pxDmaTxDesc->Status |= ETH_DMATXDESC_CIC_TCPUDPICMP_FULL | ETH_DMATXDESC_IC;
					/* The Network Buffer has been passed to DMA, no need to release it. */
					bReleaseAfterSend = pdFALSE_UNSIGNED;
				}
				#endif /* ipconfigZERO_COPY_TX_DRIVER */

				/* Prepare transmit descriptors to give to DMA. */

				/* Set LAST and FIRST segment */
				pxDmaTxDesc->Status |= ETH_DMATXDESC_FS | ETH_DMATXDESC_LS;
				/* Set frame size */
				pxDmaTxDesc->ControlBufferSize = ( ulTransmitSize & ETH_DMATXDESC_TBS1 );
				/* Set Own bit of the Tx descriptor Status: gives the buffer back to ETHERNET DMA */
				pxDmaTxDesc->Status |= ETH_DMATXDESC_OWN;

				/* Point to next descriptor */
				xETH.TxDesc = ( ETH_DMADescTypeDef * ) ( xETH.TxDesc->Buffer2NextDescAddr );
	
				/* Resume DMA transmission*/
				xETH.Instance->DMATPDR = 0;
				iptraceNETWORK_INTERFACE_TRANSMIT();
				xReturn = pdPASS;
			}
		}
		else
		{
			/* The PHY has no Link Status, packet shall be dropped. */
		}
	} while( 0 );
	/* The buffer has been sent so can be released. */
	if( bReleaseAfterSend != pdFALSE )
	{
		vReleaseNetworkBufferAndDescriptor( pxDescriptor );
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

static BaseType_t xMayAcceptPacket( uint8_t *pcBuffer )
{
const ProtocolPacket_t *pxProtPacket = ( const ProtocolPacket_t * )pcBuffer;

	switch( pxProtPacket->xTCPPacket.xEthernetHeader.usFrameType )
	{
	case ipARP_FRAME_TYPE:
		/* Check it later. */
		return pdTRUE;
	case ipIPv4_FRAME_TYPE:
		/* Check it here. */
		break;
	default:
		/* Refuse the packet. */
		return pdFALSE;
	}

	#if( ipconfigETHERNET_DRIVER_FILTERS_PACKETS == 1 )
	{
		const IPHeader_t *pxIPHeader = &(pxProtPacket->xTCPPacket.xIPHeader);
		uint32_t ulDestinationIPAddress;

		/* Ensure that the incoming packet is not fragmented (only outgoing packets
		 * can be fragmented) as these are the only handled IP frames currently. */
		if( ( pxIPHeader->usFragmentOffset & FreeRTOS_ntohs( ipFRAGMENT_OFFSET_BIT_MASK ) ) != 0U )
		{
			return pdFALSE;
		}
		/* HT: Might want to make the following configurable because
		 * most IP messages have a standard length of 20 bytes */

		/* 0x45 means: IPv4 with an IP header of 5 x 4 = 20 bytes
		 * 0x47 means: IPv4 with an IP header of 7 x 4 = 28 bytes */
		if( pxIPHeader->ucVersionHeaderLength < 0x45 || pxIPHeader->ucVersionHeaderLength > 0x4F )
		{
			return pdFALSE;
		}

		ulDestinationIPAddress = pxIPHeader->ulDestinationIPAddress;
		/* Is the packet for this node? */
		if( ( ulDestinationIPAddress != *ipLOCAL_IP_ADDRESS_POINTER ) &&
			/* Is it a broadcast address x.x.x.255 ? */
			( ( FreeRTOS_ntohl( ulDestinationIPAddress ) & 0xff ) != 0xff ) &&
		#if( ipconfigUSE_LLMNR == 1 )
			( ulDestinationIPAddress != ipLLMNR_IP_ADDR ) &&
		#endif
			( *ipLOCAL_IP_ADDRESS_POINTER != 0 ) ) {
			FreeRTOS_printf( ( "Drop IP %lxip\n", FreeRTOS_ntohl( ulDestinationIPAddress ) ) );
			return pdFALSE;
		}

		if( pxIPHeader->ucProtocol == ipPROTOCOL_UDP )
		{
			uint16_t port = pxProtPacket->xUDPPacket.xUDPHeader.usDestinationPort;

			if( ( xPortHasUDPSocket( port ) == pdFALSE )
			#if ipconfigUSE_LLMNR == 1
				&& ( port != FreeRTOS_ntohs( ipLLMNR_PORT ) )
			#endif
			#if ipconfigUSE_NBNS == 1
				&& ( port != FreeRTOS_ntohs( ipNBNS_PORT ) )
			#endif
			#if ipconfigUSE_DNS == 1
				&& ( pxProtPacket->xUDPPacket.xUDPHeader.usSourcePort != FreeRTOS_ntohs( ipDNS_PORT ) )
			#endif
				) {
				/* Drop this packet, not for this device. */
				return pdFALSE;
			}
		}
	}
	#endif	/* ipconfigETHERNET_DRIVER_FILTERS_PACKETS */
	return pdTRUE;
}
/*-----------------------------------------------------------*/

static BaseType_t prvNetworkInterfaceInput( void )
{
NetworkBufferDescriptor_t *pxCurDescriptor;
NetworkBufferDescriptor_t *pxNewDescriptor = NULL;
BaseType_t xReceivedLength, xAccepted;
__IO ETH_DMADescTypeDef *pxDMARxDescriptor;
xIPStackEvent_t xRxEvent = { eNetworkRxEvent, NULL };
const TickType_t xDescriptorWaitTime = pdMS_TO_TICKS( 250 );
uint8_t *pucBuffer;

	pxDMARxDescriptor = xETH.RxDesc;

	if( ( pxDMARxDescriptor->Status & ETH_DMARXDESC_OWN) == 0 )
	{
		/* Get the Frame Length of the received packet: substruct 4 bytes of the CRC */
		xReceivedLength = ( ( pxDMARxDescriptor->Status & ETH_DMARXDESC_FL ) >> ETH_DMARXDESC_FRAMELENGTHSHIFT ) - 4;

		pucBuffer = (uint8_t *) pxDMARxDescriptor->Buffer1Addr;

		/* Update the ETHERNET DMA global Rx descriptor with next Rx descriptor */
		/* Chained Mode */    
		/* Selects the next DMA Rx descriptor list for next buffer to read */ 
		xETH.RxDesc = ( ETH_DMADescTypeDef* )pxDMARxDescriptor->Buffer2NextDescAddr;
	}
	else
	{
		xReceivedLength = 0;
	}

	/* Obtain the size of the packet and put it into the "usReceivedLength" variable. */

	/* get received frame */
	if( xReceivedLength > 0ul )
	{
		/* In order to make the code easier and faster, only packets in a single buffer
		will be accepted.  This can be done by making the buffers large enough to
		hold a complete Ethernet packet (1536 bytes).
		Therefore, two sanity checks: */
		configASSERT( xReceivedLength <= ETH_RX_BUF_SIZE );

		if( ( pxDMARxDescriptor->Status & ( ETH_DMARXDESC_CE | ETH_DMARXDESC_IPV4HCE | ETH_DMARXDESC_FT ) ) != ETH_DMARXDESC_FT )
		{
			/* Not an Ethernet frame-type or a checmsum error. */
			xAccepted = pdFALSE;
		}
		else
		{
			/* See if this packet must be handled. */
			xAccepted = xMayAcceptPacket( pucBuffer );
		}

		if( xAccepted != pdFALSE )
		{
			/* The packet wil be accepted, but check first if a new Network Buffer can
			be obtained. If not, the packet will still be dropped. */
			pxNewDescriptor = pxGetNetworkBufferWithDescriptor( ETH_RX_BUF_SIZE, xDescriptorWaitTime );

			if( pxNewDescriptor == NULL )
			{
				/* A new descriptor can not be allocated now. This packet will be dropped. */
				xAccepted = pdFALSE;
			}
		}
		#if( ipconfigZERO_COPY_RX_DRIVER != 0 )
		{
			/* Find out which Network Buffer was originally passed to the descriptor. */
			pxCurDescriptor = pxPacketBuffer_to_NetworkBuffer( pucBuffer );
			configASSERT( pxCurDescriptor != NULL );
		}
		#else
		{
			/* In this mode, the two descriptors are the same. */
			pxCurDescriptor = pxNewDescriptor;
			if( pxNewDescriptor != NULL )
			{
				/* The packet is acepted and a new Network Buffer was created,
				copy data to the Network Bufffer. */
				memcpy( pxNewDescriptor->pucEthernetBuffer, pucBuffer, xReceivedLength );
			}
		}
		#endif

		if( xAccepted != pdFALSE )
		{
			pxCurDescriptor->xDataLength = xReceivedLength;
			xRxEvent.pvData = ( void * ) pxCurDescriptor;

			/* Pass the data to the TCP/IP task for processing. */
			if( xSendEventStructToIPTask( &xRxEvent, xDescriptorWaitTime ) == pdFALSE )
			{
				/* Could not send the descriptor into the TCP/IP stack, it
				must be released. */
				vReleaseNetworkBufferAndDescriptor( pxCurDescriptor );
				iptraceETHERNET_RX_EVENT_LOST();
			}
			else
			{
				iptraceNETWORK_INTERFACE_RECEIVE();
			}
		}

		/* Release descriptors to DMA */
		#if( ipconfigZERO_COPY_RX_DRIVER != 0 )
		{
			/* Set Buffer1 address pointer */
			if( pxNewDescriptor != NULL )
			{
				pxDMARxDescriptor->Buffer1Addr = (uint32_t)pxNewDescriptor->pucEthernetBuffer;
			}
			else
			{
				/* The packet was dropped and the same Network
				Buffer will be used to receive a new packet. */
			}
		}
		#endif /* ipconfigZERO_COPY_RX_DRIVER */

		/* Set Buffer1 size and Second Address Chained bit */
		pxDMARxDescriptor->ControlBufferSize = ETH_DMARXDESC_RCH | (uint32_t)ETH_RX_BUF_SIZE;  
		pxDMARxDescriptor->Status = ETH_DMARXDESC_OWN;

		/* When Rx Buffer unavailable flag is set clear it and resume
		reception. */
		if( ( xETH.Instance->DMASR & ETH_DMASR_RBUS ) != 0 )
		{
			/* Clear RBUS ETHERNET DMA flag. */
			xETH.Instance->DMASR = ETH_DMASR_RBUS;

			/* Resume DMA reception. */
			xETH.Instance->DMARPDR = 0;
		}
	}

	return ( xReceivedLength > 0 );
}
/*-----------------------------------------------------------*/

void vMACBProbePhy( void )
{
uint32_t ulConfig, ulAdvertise, ulLower, ulUpper, ulMACPhyID, ulValue;
TimeOut_t xPhyTime;
TickType_t xRemTime = 0;
#if( EXPECTED_PHY_ID == PHY_ID_DP83848I )
	uint32_t ulPhyControl;
#endif

	HAL_ETH_ReadPHYRegister(&xETH, PHY_REG_03_PHYSID2, &ulLower);
	HAL_ETH_ReadPHYRegister(&xETH, PHY_REG_02_PHYSID1, &ulUpper);

	ulMACPhyID = ( ( ulUpper << 16 ) & 0xFFFF0000 ) | ( ulLower & 0xFFF0 );

	/* The expected ID for the 'LAN8720' is 0x0007c0f0. */
	/* The expected ID for the 'DP83848I' is 0x20005C90. */

	FreeRTOS_printf( ( "PHY ID %lX (%s)\n", ulMACPhyID,
		( ulMACPhyID == EXPECTED_PHY_ID ) ? "OK" : "Unknown" ) );

	/* Remove compiler warning if FreeRTOS_printf() is not defined. */
	( void ) ulMACPhyID;

    /* Set advertise register. */
	if( ( xPHYProperties.speed == PHY_SPEED_AUTO ) && ( xPHYProperties.duplex == PHY_DUPLEX_AUTO ) )
	{
		ulAdvertise = ADVERTISE_CSMA | ADVERTISE_ALL;
		/* Reset auto-negotiation capability. */
	}
	else
	{
		ulAdvertise = ADVERTISE_CSMA;

		if( xPHYProperties.speed == PHY_SPEED_AUTO )
		{
			if( xPHYProperties.duplex == PHY_DUPLEX_FULL )
			{
				ulAdvertise |= ADVERTISE_10FULL | ADVERTISE_100FULL;
			}
			else
			{
				ulAdvertise |= ADVERTISE_10HALF | ADVERTISE_100HALF;
			}
		}
		else if( xPHYProperties.duplex == PHY_DUPLEX_AUTO )
		{
			if( xPHYProperties.speed == PHY_SPEED_10 )
			{
				ulAdvertise |= ADVERTISE_10FULL | ADVERTISE_10HALF;
			}
			else
			{
				ulAdvertise |= ADVERTISE_100FULL | ADVERTISE_100HALF;
			}
		}
		else if( xPHYProperties.speed == PHY_SPEED_100 )
		{
			if( xPHYProperties.duplex == PHY_DUPLEX_FULL )
			{
				ulAdvertise |= ADVERTISE_100FULL;
			}
			else
			{
				ulAdvertise |= ADVERTISE_100HALF;
			}
		}
		else
		{
			if( xPHYProperties.duplex == PHY_DUPLEX_FULL )
			{
				ulAdvertise |= ADVERTISE_10FULL;
			}
			else
			{
				ulAdvertise |= ADVERTISE_10HALF;
			}
		}
	}

	/* Read Control register. */
	HAL_ETH_ReadPHYRegister( &xETH, PHY_REG_00_BMCR, &ulConfig );

	HAL_ETH_WritePHYRegister( &xETH, PHY_REG_00_BMCR, ulConfig | BMCR_RESET );
	xRemTime = ( TickType_t ) pdMS_TO_TICKS( 1000UL );
	vTaskSetTimeOutState( &xPhyTime );

	for( ; ; )
	{
		HAL_ETH_ReadPHYRegister( &xETH, PHY_REG_00_BMCR, &ulValue );
		if( ( ulValue & BMCR_RESET ) == 0 )
		{
			FreeRTOS_printf( ( "BMCR_RESET ready\n" ) );
			break;
		}
		if( xTaskCheckForTimeOut( &xPhyTime, &xRemTime ) != pdFALSE )
		{
			FreeRTOS_printf( ( "BMCR_RESET timed out\n" ) );
			break;
		}
	}
	HAL_ETH_WritePHYRegister( &xETH, PHY_REG_00_BMCR, ulConfig & ~BMCR_RESET );

	vTaskDelay( pdMS_TO_TICKS( 50ul ) );

    /* Write advertise register. */
	HAL_ETH_WritePHYRegister( &xETH, PHY_REG_04_ADVERTISE, ulAdvertise );

	/*
			AN_EN        AN1         AN0       Forced Mode
			  0           0           0        10BASE-T, Half-Duplex
			  0           0           1        10BASE-T, Full-Duplex
			  0           1           0        100BASE-TX, Half-Duplex
			  0           1           1        100BASE-TX, Full-Duplex
			AN_EN        AN1         AN0       Advertised Mode
			  1           0           0        10BASE-T, Half/Full-Duplex
			  1           0           1        100BASE-TX, Half/Full-Duplex
			  1           1           0        10BASE-T Half-Duplex
											   100BASE-TX, Half-Duplex
			  1           1           1        10BASE-T, Half/Full-Duplex
											   100BASE-TX, Half/Full-Duplex
	*/

    /* Read Control register. */
	HAL_ETH_ReadPHYRegister( &xETH, PHY_REG_00_BMCR, &ulConfig );

	ulConfig &= ~( BMCR_ANRESTART | BMCR_ANENABLE | BMCR_SPEED100 | BMCR_FULLDPLX );

	/* HT 12/9/14: always set AN-restart and AN-enable, even though the choices
	are limited. */
	ulConfig |= (BMCR_ANRESTART | BMCR_ANENABLE);

	if( xPHYProperties.speed == PHY_SPEED_100 )
	{
		ulConfig |= BMCR_SPEED100;
	}
	else if( xPHYProperties.speed == PHY_SPEED_10 )
	{
		ulConfig &= ~BMCR_SPEED100;
	}

	if( xPHYProperties.duplex == PHY_DUPLEX_FULL )
	{
		ulConfig |= BMCR_FULLDPLX;
	}
	else if( xPHYProperties.duplex == PHY_DUPLEX_HALF )
	{
		ulConfig &= ~BMCR_FULLDPLX;
	}

	#if( EXPECTED_PHY_ID == PHY_ID_LAN8720 )
	{
	}
	#elif( EXPECTED_PHY_ID == PHY_ID_DP83848I )
	{
		/* Read PHY Control register. */
		HAL_ETH_ReadPHYRegister( &xETH, PHY_REG_19_PHYCR, &ulPhyControl );

		/* Clear bits which might get set: */
		ulPhyControl &= ~( PHYCR_MDIX_EN|PHYCR_MDIX_FORCE );

		if( xPHYProperties.mdix == PHY_MDIX_AUTO )
		{
			ulPhyControl |= PHYCR_MDIX_EN;
		}
		else if( xPHYProperties.mdix == PHY_MDIX_CROSSED )
		{
			/* Force direct link = Use crossed RJ45 cable. */
			ulPhyControl &= ~PHYCR_MDIX_FORCE;
		}
		else
		{
			/* Force crossed link = Use direct RJ45 cable. */
			ulPhyControl |= PHYCR_MDIX_FORCE;
		}
		/* update PHY Control Register. */
		HAL_ETH_WritePHYRegister( &xETH, PHY_REG_19_PHYCR, ulPhyControl );
	}
	#endif
	FreeRTOS_printf( ( "+TCP: advertise: %lX config %lX\n", ulAdvertise, ulConfig ) );

	/* Now the two values to global values for later use. */
	ulBCRvalue = ulConfig;
	ulACRValue = ulAdvertise;
}
/*-----------------------------------------------------------*/

static void prvEthernetUpdateConfig( BaseType_t xForce )
{
__IO uint32_t ulTimeout = 0;
uint32_t ulRegValue = 0;

	FreeRTOS_printf( ( "prvEthernetUpdateConfig: LS %d Force %d\n",
		( ulPHYLinkStatus & BMSR_LINK_STATUS ) != 0 ,
		xForce ) );

	if( ( xForce != pdFALSE ) || ( ( ulPHYLinkStatus & BMSR_LINK_STATUS ) != 0 ) )
	{
		/* Restart the auto-negotiation. */
		if( xETH.Init.AutoNegotiation != ETH_AUTONEGOTIATION_DISABLE )
		{
			/* Enable Auto-Negotiation. */
			HAL_ETH_WritePHYRegister( &xETH, PHY_REG_00_BMCR, ulBCRvalue | BMCR_ANRESTART );
			HAL_ETH_WritePHYRegister( &xETH, PHY_REG_04_ADVERTISE, ulACRValue);

			/* Wait until the auto-negotiation will be completed */
			do
			{
				ulTimeout++;
				HAL_ETH_ReadPHYRegister( &xETH, PHY_REG_01_BMSR, &ulRegValue );
			} while( ( ( ulRegValue & PHY_AUTONEGO_COMPLETE) == 0 ) && ( ulTimeout < PHY_READ_TO ) );

			HAL_ETH_WritePHYRegister( &xETH, PHY_REG_00_BMCR, ulBCRvalue & ~BMCR_ANRESTART );

			if( ulTimeout < PHY_READ_TO )
			{
				/* Reset Timeout counter. */
				ulTimeout = 0;

				HAL_ETH_ReadPHYRegister( &xETH, PHY_REG_01_BMSR, &ulRegValue);
				if( ( ulRegValue & BMSR_LINK_STATUS ) != 0 )
				{
					ulPHYLinkStatus |= BMSR_LINK_STATUS;
				}
				else
				{
					ulPHYLinkStatus &= ~( BMSR_LINK_STATUS );
				}

				#if( EXPECTED_PHY_ID == PHY_ID_LAN8720 )
				{
				/* 31 RW PHY Special Control Status */
				uint32_t ulControlStatus;

					HAL_ETH_ReadPHYRegister( &xETH, PHY_REG_1F_PHYSPCS, &ulControlStatus);
					ulRegValue = 0;
					if( ( ulControlStatus & PHYSPCS_FULL_DUPLEX ) != 0 )
					{
						ulRegValue |= PHY_DUPLEX_STATUS;
					}
					if( ( ulControlStatus & PHYSPCS_SPEED_MASK ) == PHYSPCS_SPEED_10 )
					{
						ulRegValue |= PHY_SPEED_STATUS;
					}

				}
				#elif( EXPECTED_PHY_ID == PHY_ID_DP83848I )
				{
					/* Read the result of the auto-negotiation. */
					HAL_ETH_ReadPHYRegister( &xETH, PHY_REG_10_PHY_SR, &ulRegValue);
				}
				#endif
				FreeRTOS_printf( ( ">> Autonego ready: %08lx: %s duplex %u mbit %s status\n",
					ulRegValue,
					(ulRegValue & PHY_DUPLEX_STATUS) ? "full" : "half",
					(ulRegValue & PHY_SPEED_STATUS) ? 10 : 100,
					((ulPHYLinkStatus |= BMSR_LINK_STATUS) != 0) ? "high" : "low" ) );

				/* Configure the MAC with the Duplex Mode fixed by the
				auto-negotiation process. */
				if( ( ulRegValue & PHY_DUPLEX_STATUS ) != ( uint32_t ) RESET )
				{
					/* Set Ethernet duplex mode to Full-duplex following the
					auto-negotiation. */
					xETH.Init.DuplexMode = ETH_MODE_FULLDUPLEX;
				}
				else
				{
					/* Set Ethernet duplex mode to Half-duplex following the
					auto-negotiation. */
					xETH.Init.DuplexMode = ETH_MODE_HALFDUPLEX;
				}

				/* Configure the MAC with the speed fixed by the
				auto-negotiation process. */
				if( ( ulRegValue & PHY_SPEED_STATUS) != 0 )
				{
					/* Set Ethernet speed to 10M following the
					auto-negotiation. */
					xETH.Init.Speed = ETH_SPEED_10M;
				}
				else
				{
					/* Set Ethernet speed to 100M following the
					auto-negotiation. */
					xETH.Init.Speed = ETH_SPEED_100M;
				}
			}	/* if( ulTimeout < PHY_READ_TO ) */
		}
		else /* AutoNegotiation Disable */
		{
		uint16_t usValue;

			/* Check parameters */
			assert_param( IS_ETH_SPEED( xETH.Init.Speed ) );
			assert_param( IS_ETH_DUPLEX_MODE( xETH.Init.DuplexMode ) );

			/* Set MAC Speed and Duplex Mode to PHY */
			usValue = ( uint16_t ) ( xETH.Init.DuplexMode >> 3 ) | ( uint16_t ) ( xETH.Init.Speed >> 1 );
			HAL_ETH_WritePHYRegister( &xETH, PHY_REG_00_BMCR, usValue );
		}

		/* ETHERNET MAC Re-Configuration */
		HAL_ETH_ConfigMAC( &xETH, (ETH_MACInitTypeDef *) NULL);

		/* Restart MAC interface */
		HAL_ETH_Start( &xETH);
	}
	else
	{
		/* Stop MAC interface */
		HAL_ETH_Stop( &xETH );
	}
}
/*-----------------------------------------------------------*/

BaseType_t xGetPhyLinkStatus( void )
{
BaseType_t xReturn;

	if( ( ulPHYLinkStatus & BMSR_LINK_STATUS ) != 0 )
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

static void prvEMACHandlerTask( void *pvParameters )
{
TimeOut_t xPhyTime;
TickType_t xPhyRemTime;
UBaseType_t uxLastMinBufferCount = 0;
#if( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
UBaseType_t uxLastMinQueueSpace = 0;
#endif
UBaseType_t uxCurrentCount;
BaseType_t xResult = 0;
uint32_t xStatus;
const TickType_t ulMaxBlockTime = pdMS_TO_TICKS( 100UL );

	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	vTaskSetTimeOutState( &xPhyTime );
	xPhyRemTime = pdMS_TO_TICKS( PHY_LS_LOW_CHECK_TIME_MS );

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

		#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
		if( xTXDescriptorSemaphore != NULL )
		{
		static UBaseType_t uxLowestSemCount = ( UBaseType_t ) ETH_TXBUFNB - 1;

			uxCurrentCount = uxSemaphoreGetCount( xTXDescriptorSemaphore );
			if( uxLowestSemCount > uxCurrentCount )
			{
				uxLowestSemCount = uxCurrentCount;
				FreeRTOS_printf( ( "TX DMA buffers: lowest %lu\n", uxLowestSemCount ) );
			}

		}
		#endif
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

		if( ( ulISREvents & EMAC_IF_ALL_EVENT ) == 0 )
		{
			/* No events to process now, wait for the next. */
			ulTaskNotifyTake( pdFALSE, ulMaxBlockTime );
		}

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

		if( ( ulISREvents & EMAC_IF_TX_EVENT ) != 0 )
		{
			/* Code to release TX buffers if zero-copy is used. */
			ulISREvents &= ~EMAC_IF_TX_EVENT;
			#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
			{
				/* Check if DMA packets have been delivered. */
				vClearTXBuffers();
			}
			#endif
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
			HAL_ETH_ReadPHYRegister( &xETH, PHY_REG_01_BMSR, &xStatus );
			if( ( ulPHYLinkStatus & BMSR_LINK_STATUS ) != ( xStatus & BMSR_LINK_STATUS ) )
			{
				ulPHYLinkStatus = xStatus;
				FreeRTOS_printf( ( "prvEMACHandlerTask: PHY LS now %d\n", ( ulPHYLinkStatus & BMSR_LINK_STATUS ) != 0 ) );
				prvEthernetUpdateConfig( pdFALSE );
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

void ETH_IRQHandler( void )
{
	HAL_ETH_IRQHandler( &xETH );
}
