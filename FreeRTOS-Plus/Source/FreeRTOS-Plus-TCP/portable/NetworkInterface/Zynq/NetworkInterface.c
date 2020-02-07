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

/* Xilinx library files. */
#include <xemacps.h>
#include "Zynq/x_topology.h"
#include "Zynq/x_emacpsif.h"
#include "Zynq/x_emacpsif_hw.h"

/* Provided memory configured as uncached. */
#include "uncached_memory.h"

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

/* The size of each buffer when BufferAllocation_1 is used:
http://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/Embedded_Ethernet_Buffer_Management.html */
#define niBUFFER_1_PACKET_SIZE		1536

/* Naming and numbering of PHY registers. */
#define PHY_REG_01_BMSR			0x01	/* Basic mode status register */

#ifndef iptraceEMAC_TASK_STARTING
	#define iptraceEMAC_TASK_STARTING()	do { } while( 0 )
#endif

/* Default the size of the stack used by the EMAC deferred handler task to twice
the size of the stack used by the idle task - but allow this to be overridden in
FreeRTOSConfig.h as configMINIMAL_STACK_SIZE is a user definable constant. */
#ifndef configEMAC_TASK_STACK_SIZE
	#define configEMAC_TASK_STACK_SIZE ( 2 * configMINIMAL_STACK_SIZE )
#endif

/*-----------------------------------------------------------*/

/*
 * Look for the link to be up every few milliseconds until either xMaxTime time
 * has passed or a link is found.
 */
static BaseType_t prvGMACWaitLS( TickType_t xMaxTime );

/*
 * A deferred interrupt handler for all MAC/DMA interrupt sources.
 */
static void prvEMACHandlerTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* EMAC data/descriptions. */
static xemacpsif_s xEMACpsif;
struct xtopology_t xXTopology =
{
	.emac_baseaddr = XPAR_PS7_ETHERNET_0_BASEADDR,
	.emac_type = xemac_type_emacps,
	.intc_baseaddr = 0x0,
	.intc_emac_intr = 0x0,
	.scugic_baseaddr = XPAR_PS7_SCUGIC_0_BASEADDR,
	.scugic_emac_intr = 0x36,
};

XEmacPs_Config mac_config =
{
	.DeviceId = XPAR_PS7_ETHERNET_0_DEVICE_ID,	/**< Unique ID  of device */
	.BaseAddress = XPAR_PS7_ETHERNET_0_BASEADDR /**< Physical base address of IPIF registers */
};

extern int phy_detected;

/* A copy of PHY register 1: 'PHY_REG_01_BMSR' */
static uint32_t ulPHYLinkStatus = 0;

#if( ipconfigUSE_LLMNR == 1 )
	static const uint8_t xLLMNR_MACAddress[] = { 0x01, 0x00, 0x5E, 0x00, 0x00, 0xFC };
#endif

/* ucMACAddress as it appears in main.c */
extern const uint8_t ucMACAddress[ 6 ];

/* Holds the handle of the task used as a deferred interrupt processor.  The
handle is used so direct notifications can be sent to the task for all EMAC/DMA
related interrupts. */
TaskHandle_t xEMACTaskHandle = NULL;

/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceInitialise( void )
{
uint32_t ulLinkSpeed, ulDMAReg;
BaseType_t xStatus, xLinkStatus;
XEmacPs *pxEMAC_PS;
const TickType_t xWaitLinkDelay = pdMS_TO_TICKS( 7000UL ), xWaitRelinkDelay = pdMS_TO_TICKS( 1000UL );

	/* Guard against the init function being called more than once. */
	if( xEMACTaskHandle == NULL )
	{
		pxEMAC_PS = &( xEMACpsif.emacps );
		memset( &xEMACpsif, '\0', sizeof( xEMACpsif ) );

		xStatus = XEmacPs_CfgInitialize( pxEMAC_PS, &mac_config, mac_config.BaseAddress);
		if( xStatus != XST_SUCCESS )
		{
			FreeRTOS_printf( ( "xEMACInit: EmacPs Configuration Failed....\n" ) );
		}

		/* Initialize the mac and set the MAC address. */
		XEmacPs_SetMacAddress( pxEMAC_PS, ( void * ) ucMACAddress, 1 );

		#if( ipconfigUSE_LLMNR == 1 )
		{
			/* Also add LLMNR multicast MAC address. */
			XEmacPs_SetMacAddress( pxEMAC_PS, ( void * )xLLMNR_MACAddress, 2 );
		}
		#endif	/* ipconfigUSE_LLMNR == 1 */

		XEmacPs_SetMdioDivisor( pxEMAC_PS, MDC_DIV_224 );
		ulLinkSpeed = Phy_Setup( pxEMAC_PS );
		XEmacPs_SetOperatingSpeed( pxEMAC_PS, ulLinkSpeed);

		/* Setting the operating speed of the MAC needs a delay. */
		vTaskDelay( pdMS_TO_TICKS( 25UL ) );

		ulDMAReg = XEmacPs_ReadReg( pxEMAC_PS->Config.BaseAddress, XEMACPS_DMACR_OFFSET);

		/* DISC_WHEN_NO_AHB: when set, the GEM DMA will automatically discard receive
		packets from the receiver packet buffer memory when no AHB resource is available. */
		XEmacPs_WriteReg( pxEMAC_PS->Config.BaseAddress, XEMACPS_DMACR_OFFSET,
			ulDMAReg | XEMACPS_DMACR_DISC_WHEN_NO_AHB_MASK);

		setup_isr( &xEMACpsif );
		init_dma( &xEMACpsif );
		start_emacps( &xEMACpsif );

		prvGMACWaitLS( xWaitLinkDelay );

		/* The deferred interrupt handler task is created at the highest
		possible priority to ensure the interrupt handler can return directly
		to it.  The task's handle is stored in xEMACTaskHandle so interrupts can
		notify the task when there is something to process. */
		xTaskCreate( prvEMACHandlerTask, "EMAC", configEMAC_TASK_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, &xEMACTaskHandle );
	}
	else
	{
		/* Initialisation was already performed, just wait for the link. */
		prvGMACWaitLS( xWaitRelinkDelay );
	}

	/* Only return pdTRUE when the Link Status of the PHY is high, otherwise the
	DHCP process and all other communication will fail. */
	xLinkStatus = xGetPhyLinkStatus();

	return ( xLinkStatus != pdFALSE );
}
/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxBuffer, BaseType_t bReleaseAfterSend )
{
	if( ( ulPHYLinkStatus & BMSR_LINK_STATUS ) != 0 )
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

	XEmacPs_PhyRead( &( xEMACpsif.emacps ), phy_detected, ulRegister, &usValue );
	return usValue;
}
/*-----------------------------------------------------------*/

static BaseType_t prvGMACWaitLS( TickType_t xMaxTime )
{
TickType_t xStartTime, xEndTime;
const TickType_t xShortDelay = pdMS_TO_TICKS( 20UL );
BaseType_t xReturn;

	xStartTime = xTaskGetTickCount();

	for( ;; )
	{
		xEndTime = xTaskGetTickCount();

		if( xEndTime - xStartTime > xMaxTime )
		{
			xReturn = pdFALSE;
			break;
		}
		ulPHYLinkStatus = ulReadMDIO( PHY_REG_01_BMSR );

		if( ( ulPHYLinkStatus & BMSR_LINK_STATUS ) != 0 )
		{
			xReturn = pdTRUE;
			break;
		}

		vTaskDelay( xShortDelay );
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

void vNetworkInterfaceAllocateRAMToBuffers( NetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS ] )
{
static uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS * niBUFFER_1_PACKET_SIZE ] __attribute__ ( ( aligned( 32 ) ) );
uint8_t *ucRAMBuffer = ucNetworkPackets;
uint32_t ul;

	for( ul = 0; ul < ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS; ul++ )
	{
		pxNetworkBuffers[ ul ].pucEthernetBuffer = ucRAMBuffer + ipBUFFER_PADDING;
		*( ( unsigned * ) ucRAMBuffer ) = ( unsigned ) ( &( pxNetworkBuffers[ ul ] ) );
		ucRAMBuffer += niBUFFER_1_PACKET_SIZE;
	}
}
/*-----------------------------------------------------------*/

BaseType_t xGetPhyLinkStatus( void )
{
BaseType_t xReturn;

	if( ( ulPHYLinkStatus & BMSR_LINK_STATUS ) == 0 )
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
UBaseType_t uxLastMinBufferCount = 0;
UBaseType_t uxCurrentCount;
BaseType_t xResult = 0;
uint32_t xStatus;
const TickType_t ulMaxBlockTime = pdMS_TO_TICKS( 100UL );

	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	/* A possibility to set some additional task properties like calling
	portTASK_USES_FLOATING_POINT() */
	iptraceEMAC_TASK_STARTING();

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

		#if( ipconfigCHECK_IP_QUEUE_SPACE != 0 )
		{
		static UBaseType_t uxLastMinQueueSpace = 0;

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
			but set a timer to check it later on. */
			vTaskSetTimeOutState( &xPhyTime );
			xPhyRemTime = pdMS_TO_TICKS( PHY_LS_HIGH_CHECK_TIME_MS );
			xResult = 0;
		}
		else if( xTaskCheckForTimeOut( &xPhyTime, &xPhyRemTime ) != pdFALSE )
		{
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
