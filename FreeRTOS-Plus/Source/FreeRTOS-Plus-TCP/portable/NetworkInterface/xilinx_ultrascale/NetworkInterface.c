/*
 * FreeRTOS+TCP V2.2.2
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
#include "FreeRTOS_ARP.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

/* Xilinx library files. */
#include <xemacps.h>
#include "x_topology.h"
#include "x_emacpsif.h"
#include "x_emacpsif_hw.h"

/* Provided memory configured as uncached. */
#include "uncached_memory.h"

#ifndef niEMAC_HANDLER_TASK_PRIORITY
	/* Define the priority of the task prvEMACHandlerTask(). */
	#define niEMAC_HANDLER_TASK_PRIORITY	configMAX_PRIORITIES - 1
#endif

#define niBMSR_LINK_STATUS         0x0004uL

#ifndef	PHY_LS_HIGH_CHECK_TIME_MS

	/* Check if the LinkSStatus in the PHY is still high after 15 seconds of not
	 * receiving packets. */
	#define PHY_LS_HIGH_CHECK_TIME_MS	15000
#endif

#ifndef	PHY_LS_LOW_CHECK_TIME_MS
	/* Check if the LinkSStatus in the PHY is still low every second. */
	#define PHY_LS_LOW_CHECK_TIME_MS	1000
#endif

/* The size of each buffer when BufferAllocation_1 is used:
 * http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/Embedded_Ethernet_Buffer_Management.html */
#define niBUFFER_1_PACKET_SIZE		1536

/* Naming and numbering of PHY registers. */
#define PHY_REG_01_BMSR			0x01	/* Basic mode status register */

#ifndef iptraceEMAC_TASK_STARTING
	#define iptraceEMAC_TASK_STARTING()	do { } while( 0 )
#endif

/* Default the size of the stack used by the EMAC deferred handler task to twice
 * the size of the stack used by the idle task - but allow this to be overridden in
 * FreeRTOSConfig.h as configMINIMAL_STACK_SIZE is a user definable constant. */
#ifndef configEMAC_TASK_STACK_SIZE
	#define configEMAC_TASK_STACK_SIZE ( 8 * configMINIMAL_STACK_SIZE )
#endif

#if( ipconfigZERO_COPY_RX_DRIVER == 0 || ipconfigZERO_COPY_TX_DRIVER == 0 )
	#error Please define both 'ipconfigZERO_COPY_RX_DRIVER' and 'ipconfigZERO_COPY_TX_DRIVER' as 1
#endif

#if( ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM == 0 || ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM == 0 )
	#warning Please define both 'ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM' and 'ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM' as 1
#endif

#ifndef nicUSE_UNCACHED_MEMORY
	/*
	 * Don't use cached memory for network buffer, which is more efficient than
	 * using cached memory.
	 */
	#define nicUSE_UNCACHED_MEMORY  0
#endif

/*-----------------------------------------------------------*/

/*
 * Look for the link to be up every few milliseconds until
 * xMaxTimeTicks has passed or a link is found.
 */
static BaseType_t prvGMACWaitLS( TickType_t xMaxTimeTicks );

/*
 * A deferred interrupt handler for all MAC/DMA interrupt sources.
 */
static void prvEMACHandlerTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* EMAC data/descriptions. */
static xemacpsif_s xEMACpsif;
struct xtopology_t xXTopology =
{
	.emac_baseaddr = XPAR_XEMACPS_0_BASEADDR,
	.emac_type = xemac_type_emacps,
	.intc_baseaddr = 0x0,
	.intc_emac_intr = 0x0,
	.scugic_baseaddr = XPAR_SCUGIC_0_CPU_BASEADDR,
	.scugic_emac_intr = XPAR_XEMACPS_3_INTR,
};

XEmacPs_Config mac_config =
{
	.DeviceId = XPAR_PSU_ETHERNET_3_DEVICE_ID,	/**< Unique ID  of device */
	.BaseAddress = XPAR_PSU_ETHERNET_3_BASEADDR, /**< Physical base address of IPIF registers */
	.IsCacheCoherent = XPAR_PSU_ETHERNET_3_IS_CACHE_COHERENT
};

/* A copy of PHY register 1: 'PHY_REG_01_BMSR' */
static uint32_t ulPHYLinkStatus = 0uL;

#if( ipconfigUSE_LLMNR == 1 )
	static const uint8_t xLLMNR_MACAddress[] = { 0x01, 0x00, 0x5E, 0x00, 0x00, 0xFC };
#endif

/* ucMACAddress as it appears in main.c */
extern const uint8_t ucMACAddress[ 6 ];

/* Holds the handle of the task used as a deferred interrupt processor.  The
 * handle is used so direct notifications can be sent to the task for all EMAC/DMA
 * related interrupts. */
TaskHandle_t xEMACTaskHandle = NULL;

/* The PHY index where a PHY was found. */
static u32 ulPHYIndex;

/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceInitialise( void )
{
uint32_t ulLinkSpeed, ulDMAReg;
BaseType_t xStatus, xLinkStatus;
XEmacPs *pxEMAC_PS;
const TickType_t xWaitLinkDelay = pdMS_TO_TICKS( 7000UL );
const TickType_t xWaitRelinkDelay = pdMS_TO_TICKS( 1000UL );

	/* Guard against the init function being called more than once. */
	if( xEMACTaskHandle == NULL )
	{		pxEMAC_PS = &( xEMACpsif.emacps );
		memset( &xEMACpsif, '\0', sizeof( xEMACpsif ) );

		xStatus = XEmacPs_CfgInitialize( pxEMAC_PS, &mac_config, mac_config.BaseAddress);
		if( xStatus != XST_SUCCESS )
		{
			FreeRTOS_printf( ( "xEMACInit: EmacPs Configuration Failed....\n" ) );
		}

/* _HT_ : disabled. the use of jumbo frames has not been tested yet. */
/*
		if (pxEMAC_PS->Version > 2 )
		{
			// Enable jumbo frames for zynqmp
			XEmacPs_SetOptions(pxEMAC_PS, XEMACPS_JUMBO_ENABLE_OPTION);
		}
*/
		/* Initialize the mac and set the MAC address. */
        XEmacPs_SetMacAddress( pxEMAC_PS, ( void * ) ucMACAddress, 1 );

		#if( ipconfigUSE_LLMNR == 1 )
		{
			/* Also add LLMNR multicast MAC address. */
			XEmacPs_SetMacAddress( pxEMAC_PS, ( void * )xLLMNR_MACAddress, 2 );
		}
		#endif	/* ipconfigUSE_LLMNR == 1 */

		XEmacPs_SetMdioDivisor( pxEMAC_PS, MDC_DIV_224 );
		ulPHYIndex = ulDetecPHY( pxEMAC_PS );
		ulLinkSpeed = Phy_Setup_US( pxEMAC_PS, ulPHYIndex );
		XEmacPs_SetOperatingSpeed( pxEMAC_PS, ulLinkSpeed );

		/* Setting the operating speed of the MAC needs a delay. */
		vTaskDelay( pdMS_TO_TICKS( 25UL ) );

		ulDMAReg = XEmacPs_ReadReg( pxEMAC_PS->Config.BaseAddress, XEMACPS_DMACR_OFFSET );
		/* Enable 16-bytes AHB bursts */
		ulDMAReg = ulDMAReg | XEMACPS_DMACR_INCR16_AHB_BURST;

		/* DISC_WHEN_NO_AHB: when set, the GEM DMA will automatically discard receive
		 * packets from the receiver packet buffer memory when no AHB resource is available. */
		XEmacPs_WriteReg( pxEMAC_PS->Config.BaseAddress, XEMACPS_DMACR_OFFSET,
			ulDMAReg /*| XEMACPS_DMACR_DISC_WHEN_NO_AHB_MASK*/);

		setup_isr( &xEMACpsif );
		init_dma( &xEMACpsif );
		start_emacps( &xEMACpsif );

		prvGMACWaitLS( xWaitLinkDelay );

		/* The deferred interrupt handler task is created at the highest
		 * possible priority to ensure the interrupt handler can return directly
		 * to it.  The task's handle is stored in xEMACTaskHandle so interrupts can
		 * notify the task when there is something to process. */
		xTaskCreate( prvEMACHandlerTask, "EMAC", configEMAC_TASK_STACK_SIZE, NULL, niEMAC_HANDLER_TASK_PRIORITY, &xEMACTaskHandle );
	}
	else
	{
		/* Initialisation was already performed, just wait for the link. */
		prvGMACWaitLS( xWaitRelinkDelay );
	}

	/* Only return pdTRUE when the Link Status of the PHY is high, otherwise the
	 * DHCP process and all other communication will fail. */
	xLinkStatus = xGetPhyLinkStatus();

	return ( xLinkStatus != pdFALSE );
}
/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxBuffer,
									BaseType_t bReleaseAfterSend )
{
	#if( ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM != 0 )
	{
	ProtocolPacket_t *pxPacket;

		/* If the peripheral must calculate the checksum, it wants
		 * the protocol checksum to have a value of zero. */
		pxPacket = ( ProtocolPacket_t * ) ( pxBuffer->pucEthernetBuffer );

        if( ( pxPacket->xICMPPacket.xEthernetHeader.usFrameType == ipIPv4_FRAME_TYPE ) &&
            ( pxPacket->xICMPPacket.xIPHeader.ucProtocol != ipPROTOCOL_UDP ) &&
			( pxPacket->xICMPPacket.xIPHeader.ucProtocol != ipPROTOCOL_TCP ) )
		{
			/* The EMAC will calculate the checksum of the IP-header.
			 * It can only calculate protocol checksums of UDP and TCP,
			 * so for ICMP and other protocols it must be done manually. */
			usGenerateProtocolChecksum( (uint8_t*)&( pxPacket->xUDPPacket ), pxBuffer->xDataLength, pdTRUE );
		}
	}
	#endif /* ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM */

	if( ( ulPHYLinkStatus & niBMSR_LINK_STATUS ) != 0UL )
	{
		iptraceNETWORK_INTERFACE_TRANSMIT();
		emacps_send_message( &xEMACpsif, pxBuffer, bReleaseAfterSend );
	}
	else if( bReleaseAfterSend != pdFALSE )
	{
		/* No link. */
		vReleaseNetworkBufferAndDescriptor( pxBuffer );
	}

	return pdTRUE;
}
/*-----------------------------------------------------------*/

static inline unsigned long ulReadMDIO( unsigned ulRegister )
{
uint16_t usValue;

	XEmacPs_PhyRead( &( xEMACpsif.emacps ), ulPHYIndex, ulRegister, &usValue );
	return usValue;
}
/*-----------------------------------------------------------*/

static BaseType_t prvGMACWaitLS( TickType_t xMaxTimeTicks )
{
TickType_t xStartTime, xEndTime;
const TickType_t xShortDelay = pdMS_TO_TICKS( 20UL );
BaseType_t xReturn;

	xStartTime = xTaskGetTickCount();

	for( ;; )
	{
		xEndTime = xTaskGetTickCount();

		if( xEndTime - xStartTime > xMaxTimeTicks )
		{
			xReturn = pdFALSE;
			break;
		}

		ulPHYLinkStatus = ulReadMDIO( PHY_REG_01_BMSR );

		if( ( ulPHYLinkStatus & niBMSR_LINK_STATUS ) != 0uL )
		{
			xReturn = pdTRUE;
			break;
		}

		vTaskDelay( xShortDelay );
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

#if( nicUSE_UNCACHED_MEMORY == 0 )
	void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
	{
		static uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS * niBUFFER_1_PACKET_SIZE ] __attribute__( ( aligned( 32 ) ) );
		uint8_t * ucRAMBuffer = ucNetworkPackets;
		uint32_t ul;

		for( ul = 0; ul < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ul++ )
		{
			pxNetworkBuffers[ ul ].pucEthernetBuffer = ucRAMBuffer + ipBUFFER_PADDING;
			*( ( uintptr_t * ) ucRAMBuffer ) = ( uintptr_t ) &( pxNetworkBuffers[ ul ] );
			ucRAMBuffer += niBUFFER_1_PACKET_SIZE;
		}
	}
#else
	void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
	{
	static uint8_t *pucNetworkPackets = NULL;
		if( pucNetworkPackets == NULL )
		{
			pucNetworkPackets = pucGetUncachedMemory( ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS * niBUFFER_1_PACKET_SIZE );
			if( pucNetworkPackets != NULL )
			{
			uint8_t *ucRAMBuffer = pucNetworkPackets;
			uint32_t ul;

				for( ul = 0; ul < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ul++ )
				{
					pxNetworkBuffers[ ul ].pucEthernetBuffer = ucRAMBuffer + ipBUFFER_PADDING;
					*( ( unsigned * ) ucRAMBuffer ) = ( unsigned ) ( &( pxNetworkBuffers[ ul ] ) );
					ucRAMBuffer += niBUFFER_1_PACKET_SIZE;
				}
			}
		}
	}
#endif	/* ( nicUSE_UNCACHED_MEMORY == 0 ) */
/*-----------------------------------------------------------*/

BaseType_t xGetPhyLinkStatus( void )
{
BaseType_t xReturn;

	if( ( ulPHYLinkStatus & niBMSR_LINK_STATUS ) == 0uL )
	{
		xReturn = pdFALSE;
	}
	else
	{
		xReturn = pdTRUE;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

static void prvEMACHandlerTask( void *pvParameters )
{
TimeOut_t xPhyTime;
TickType_t xPhyRemTime;
BaseType_t xResult = 0;
uint32_t xStatus;
const TickType_t ulMaxBlockTime = pdMS_TO_TICKS( 100UL );

	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	/* A possibility to set some additional task properties like calling
	 * portTASK_USES_FLOATING_POINT() */
	iptraceEMAC_TASK_STARTING();

	vTaskSetTimeOutState( &xPhyTime );
	xPhyRemTime = pdMS_TO_TICKS( PHY_LS_LOW_CHECK_TIME_MS );

	for( ;; )
	{
		#if ( ipconfigHAS_PRINTF != 0 )
			{
            /* Call a function that monitors resources: the amount of free network
             * buffers and the amount of free space on the heap.  See FreeRTOS_IP.c
             * for more detailed comments. */
            vPrintResourceStats();
			}
        #endif /* ( ipconfigHAS_PRINTF != 0 ) */

		if( ( xEMACpsif.isr_events & EMAC_IF_ALL_EVENT ) == 0 )
		{
			/* No events to process now, wait for the next. */
			ulTaskNotifyTake( pdFALSE, ulMaxBlockTime );
		}

		if( ( xEMACpsif.isr_events & EMAC_IF_RX_EVENT ) != 0 )
		{
			xEMACpsif.isr_events &= ~EMAC_IF_RX_EVENT;
			xResult = emacps_check_rx( &xEMACpsif );
		}

		if( ( xEMACpsif.isr_events & EMAC_IF_TX_EVENT ) != 0 )
		{
			xEMACpsif.isr_events &= ~EMAC_IF_TX_EVENT;
			emacps_check_tx( &xEMACpsif );
		}

		if( ( xEMACpsif.isr_events & EMAC_IF_ERR_EVENT ) != 0 )
		{
			xEMACpsif.isr_events &= ~EMAC_IF_ERR_EVENT;
			emacps_check_errors( &xEMACpsif );
		}

		if( xResult > 0 )
		{
			/* A packet was received. No need to check for the PHY status now,
			 * but set a timer to check it later on. */
			vTaskSetTimeOutState( &xPhyTime );
			xPhyRemTime = pdMS_TO_TICKS( PHY_LS_HIGH_CHECK_TIME_MS );
			xResult = 0;

			if( ( ulPHYLinkStatus & niBMSR_LINK_STATUS ) == 0uL )
			{
				/* Indicate that the Link Status is high, so that
				 * xNetworkInterfaceOutput() can send packets. */
				ulPHYLinkStatus |= niBMSR_LINK_STATUS;
				FreeRTOS_printf( ( "prvEMACHandlerTask: PHY LS assume 1\n" ) );
			}
		}
		else if( xTaskCheckForTimeOut( &xPhyTime, &xPhyRemTime ) != pdFALSE )
		{
			xStatus = ulReadMDIO( PHY_REG_01_BMSR );

			if( ( ulPHYLinkStatus & niBMSR_LINK_STATUS ) != ( xStatus & niBMSR_LINK_STATUS ) )
			{
				ulPHYLinkStatus = xStatus;
				FreeRTOS_printf( ( "prvEMACHandlerTask: PHY LS now %d\n", ( ulPHYLinkStatus & niBMSR_LINK_STATUS ) != 0uL ) );
			}

			vTaskSetTimeOutState( &xPhyTime );

			if( ( ulPHYLinkStatus & niBMSR_LINK_STATUS ) != 0uL )
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
