/*
 * FreeRTOS+UDP V1.0.3 (C) 2014 Real Time Engineers ltd.
 * All rights reserved
 *
 * This file is part of the FreeRTOS+UDP distribution.  The FreeRTOS+UDP license
 * terms are different to the FreeRTOS license terms.
 *
 * FreeRTOS+UDP uses a dual license model that allows the software to be used
 * under a pure GPL open source license (as opposed to the modified GPL license
 * under which FreeRTOS is distributed) or a commercial license.  Details of
 * both license options follow:
 *
 * - Open source licensing -
 * FreeRTOS+UDP is a free download and may be used, modified, evaluated and
 * distributed without charge provided the user adheres to version two of the
 * GNU General Public License (GPL) and does not remove the copyright notice or
 * this text.  The GPL V2 text is available on the gnu.org web site, and on the
 * following URL: http://www.FreeRTOS.org/gpl-2.0.txt.
 *
 * - Commercial licensing -
 * Businesses and individuals that for commercial or other reasons cannot comply
 * with the terms of the GPL V2 license must obtain a commercial license before
 * incorporating FreeRTOS+UDP into proprietary software for distribution in any
 * form.  Commercial licenses can be purchased from http://shop.freertos.org/udp
 * and do not require any source files to be changed.
 *
 * FreeRTOS+UDP is distributed in the hope that it will be useful.  You cannot
 * use FreeRTOS+UDP unless you agree that you use the software 'as is'.
 * FreeRTOS+UDP is provided WITHOUT ANY WARRANTY; without even the implied
 * warranties of NON-INFRINGEMENT, MERCHANTABILITY or FITNESS FOR A PARTICULAR
 * PURPOSE. Real Time Engineers Ltd. disclaims all conditions and terms, be they
 * implied, expressed, or statutory.
 *
 * 1 tab == 4 spaces!
 *
 * http://www.FreeRTOS.org
 * http://www.FreeRTOS.org/udp
 *
 */

/* Standard includes. */
#include <stdint.h>
#include <limits.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* FreeRTOS+UDP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_Sockets.h"
#include "NetworkBufferManagement.h"

/* Demo includes. */
#include "NetworkInterface.h"

/* If a packet cannot be sent immediately then the task performing the send
operation will be held in the Blocked state (so other tasks can execute) for
niTX_BUFFER_FREE_WAIT ticks.  It will do this a maximum of niMAX_TX_ATTEMPTS
before giving up. */
#define niTX_BUFFER_FREE_WAIT	( ( TickType_t ) 2UL / portTICK_RATE_MS )
#define niMAX_TX_ATTEMPTS		( 5 )

/*-----------------------------------------------------------*/

/*
 * A deferred interrupt handler task that processes received frames.
 */
static void prvGMACDeferredInterruptHandlerTask( void *pvParameters );

/*
 * Called by the ASF GMAC driver when a packet is received.
 */
static void prvGMACRxCallback( uint32_t ulStatus );

/*-----------------------------------------------------------*/

/* The queue used to communicate Ethernet events to the IP task. */
extern xQueueHandle xNetworkEventQueue;

/* The semaphore used to wake the deferred interrupt handler task when an Rx
interrupt is received. */
static xSemaphoreHandle xGMACRxEventSemaphore = NULL;

/* The GMAC driver instance. */
static gmac_device_t xGMACStruct;

/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceInitialise( void )
{
gmac_options_t xGMACOptions;
extern uint8_t ucMACAddress[ 6 ];
const TickType_t xPHYDelay_400ms = 400UL;
BaseType_t xReturn = pdFALSE;

	/* Ensure PHY is ready. */
	vTaskDelay( xPHYDelay_400ms / portTICK_RATE_MS );

	/* Enable GMAC clock. */
	pmc_enable_periph_clk( ID_GMAC );

	/* Fill in GMAC options */
	xGMACOptions.uc_copy_all_frame = 0;
	xGMACOptions.uc_no_boardcast = 0;
	memcpy( xGMACOptions.uc_mac_addr, ucMACAddress, sizeof( ucMACAddress ) );

	xGMACStruct.p_hw = GMAC;

	/* Init GMAC driver structure. */
	gmac_dev_init( GMAC, &xGMACStruct, &xGMACOptions );

	/* Init MAC PHY driver. */
	if( ethernet_phy_init( GMAC, BOARD_GMAC_PHY_ADDR, sysclk_get_cpu_hz() ) == GMAC_OK )
	{
		/* Auto Negotiate, work in RMII mode. */
		if( ethernet_phy_auto_negotiate( GMAC, BOARD_GMAC_PHY_ADDR ) == GMAC_OK )
		{
			/* Establish Ethernet link. */
			vTaskDelay( xPHYDelay_400ms * 2UL );
			if( ethernet_phy_set_link( GMAC, BOARD_GMAC_PHY_ADDR, 1 ) == GMAC_OK )
			{
				/* Create the event semaphore if it has not already been
				created. */
				if( xGMACRxEventSemaphore == NULL )
				{
					xGMACRxEventSemaphore = xSemaphoreCreateCounting( ULONG_MAX, 0 );
					#if ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS == 1
					{
						/* If the trace recorder code is included name the semaphore for
						viewing in FreeRTOS+Trace. */
						vTraceSetQueueName( xGMACRxEventSemaphore, "MAC_RX" );
					}
					#endif /*  ipconfigINCLUDE_EXAMPLE_FREERTOS_PLUS_TRACE_CALLS == 1 */
				}

				/* Register the callbacks. */
				gmac_dev_set_rx_callback( &xGMACStruct, prvGMACRxCallback );

				/* The Rx deferred interrupt handler task is created at the
				highest	possible priority to ensure the interrupt handler can
				return directly to it no matter which task was running when the
				interrupt occurred. */
				xTaskCreate( 	prvGMACDeferredInterruptHandlerTask,/* The function that implements the task. */
								"MACTsk",
								configMINIMAL_STACK_SIZE,	/* Stack allocated to the task (defined in words, not bytes). */
								NULL, 						/* The task parameter is not used. */
								configMAX_PRIORITIES - 1, 	/* The priority assigned to the task. */
								NULL );						/* The handle is not required, so NULL is passed. */

				/* Enable the interrupt and set its priority as configured.
				THIS DRIVER REQUIRES configMAC_INTERRUPT_PRIORITY TO BE DEFINED,
				PREFERABLY IN FreeRTOSConfig.h. */
				NVIC_SetPriority( GMAC_IRQn, configMAC_INTERRUPT_PRIORITY );
				NVIC_EnableIRQ( GMAC_IRQn );
				xReturn = pdPASS;
			}
		}
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

static void prvGMACRxCallback( uint32_t ulStatus )
{
BaseType_t xHigherPriorityTaskWoken = pdFALSE;

	/* Unblock the deferred interrupt handler task if the event was an Rx. */
	if( ulStatus == GMAC_RSR_REC )
	{
		xSemaphoreGiveFromISR( xGMACRxEventSemaphore, &xHigherPriorityTaskWoken );
	}

	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceOutput( xNetworkBufferDescriptor_t * const pxNetworkBuffer )
{
BaseType_t xReturn = pdFAIL;
int32_t x;

	/* Attempt to obtain access to a Tx descriptor. */
	for( x = 0; x < niMAX_TX_ATTEMPTS; x++ )
	{
		if( gmac_dev_write( &xGMACStruct, pxNetworkBuffer->pucEthernetBuffer, ( uint32_t ) pxNetworkBuffer->xDataLength, NULL ) == GMAC_OK )
		{
			/* The Tx has been initiated. */
			xReturn = pdPASS;
			break;
		}
		else
		{
			iptraceWAITING_FOR_TX_DMA_DESCRIPTOR();
			vTaskDelay( niTX_BUFFER_FREE_WAIT );
		}
	}

	/* Finished with the network buffer. */
	vNetworkBufferRelease( pxNetworkBuffer );

	return xReturn;
}
/*-----------------------------------------------------------*/

void GMAC_Handler( void )
{
	gmac_handler( &xGMACStruct );
}
/*-----------------------------------------------------------*/

static void prvGMACDeferredInterruptHandlerTask( void *pvParameters )
{
xNetworkBufferDescriptor_t *pxNetworkBuffer;
xIPStackEvent_t xRxEvent = { eEthernetRxEvent, NULL };
static const TickType_t xBufferWaitDelay = 1500UL / portTICK_RATE_MS;
uint32_t ulReturned;

	( void ) pvParameters;
	configASSERT( xGMACRxEventSemaphore );

	for( ;; )
	{
		/* Wait for the GMAC interrupt to indicate that another packet has been
		received.  The while() loop is only needed if INCLUDE_vTaskSuspend is
		set to 0 in FreeRTOSConfig.h.  If INCLUDE_vTaskSuspend is set to 1
		then portMAX_DELAY would be an indefinite block time and
		xSemaphoreTake() would only return when the semaphore was actually
		obtained. */
		while( xSemaphoreTake( xGMACRxEventSemaphore, portMAX_DELAY ) == pdFALSE );

		/* Allocate a buffer to hold the data. */
		pxNetworkBuffer = pxNetworkBufferGet( ipTOTAL_ETHERNET_FRAME_SIZE, xBufferWaitDelay );

		if( pxNetworkBuffer != NULL )
		{
			/* At least one packet has been received. */
			ulReturned = gmac_dev_read( &xGMACStruct, pxNetworkBuffer->pucEthernetBuffer, ipTOTAL_ETHERNET_FRAME_SIZE, ( uint32_t * ) &( pxNetworkBuffer->xDataLength ) );
			if( ulReturned == GMAC_OK )
			{
				#if ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 1
				{
					if( pxNetworkBuffer->xDataLength > 0 )
					{
						/* If the frame would not be processed by the IP stack then
						don't even bother sending it to the IP stack. */
						if( eConsiderFrameForProcessing( pxNetworkBuffer->pucEthernetBuffer ) != eProcessBuffer )
						{
							pxNetworkBuffer->xDataLength = 0;
						}
					}
				}
				#endif

				if( pxNetworkBuffer->xDataLength > 0 )
				{
					/* Store a pointer to the network buffer structure in the
					padding	space that was left in front of the Ethernet frame.
					The pointer	is needed to ensure the network buffer structure
					can be located when it is time for it to be freed if the
					Ethernet frame gets	used as a zero copy buffer. */
					*( ( xNetworkBufferDescriptor_t ** ) ( ( pxNetworkBuffer->pucEthernetBuffer - ipBUFFER_PADDING ) ) ) = pxNetworkBuffer;

					/* Data was received and stored.  Send it to the IP task
					for processing. */
					xRxEvent.pvData = ( void * ) pxNetworkBuffer;
					if( xQueueSendToBack( xNetworkEventQueue, &xRxEvent, ( TickType_t ) 0 ) == pdFALSE )
					{
						/* The buffer could not be sent to the IP task so the
						buffer must be released. */
						vNetworkBufferRelease( pxNetworkBuffer );
						iptraceETHERNET_RX_EVENT_LOST();
					}
					else
					{
						iptraceNETWORK_INTERFACE_RECEIVE();
					}
				}
				else
				{
					/* The buffer does not contain any data so there is no
					point sending it to the IP task.  Just release it. */
					vNetworkBufferRelease( pxNetworkBuffer );
					iptraceETHERNET_RX_EVENT_LOST();
				}
			}
			else
			{
				vNetworkBufferRelease( pxNetworkBuffer );
				iptraceETHERNET_RX_EVENT_LOST();
			}
		}
		else
		{
			/* Left a frame in the driver as a buffer was not available. */
			gmac_dev_reset( &xGMACStruct );
		}
	}
}
/*-----------------------------------------------------------*/

