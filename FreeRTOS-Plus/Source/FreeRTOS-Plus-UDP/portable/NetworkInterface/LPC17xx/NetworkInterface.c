/*
 * FreeRTOS+UDP V1.0.1 (C) 2013 Real Time Engineers ltd.
 * All rights reserved
 *
 * This file is part of the FreeRTOS+UDP distribution.  The FreeRTOS+UDP license
 * terms are different to the FreeRTOS license terms.
 *
 * FreeRTOS+UDP uses a dual license model that allows the software to be used 
 * under a standard GPL open source license, or a commercial license.  The 
 * standard GPL license (unlike the modified GPL license under which FreeRTOS 
 * itself is distributed) requires that all software statically linked with 
 * FreeRTOS+UDP is also distributed under the same GPL V2 license terms.  
 * Details of both license options follow:
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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Hardware abstraction. */
#include "FreeRTOS_IO.h"

/* FreeRTOS+UDP includes. */
#include "FreeRTOS_UDP_IP.h"
#include "FreeRTOS_Sockets.h"
#include "NetworkBufferManagement.h"

/* Driver includes. */
#include "lpc17xx_emac.h"
#include "lpc17xx_pinsel.h"

/* Demo includes. */
#include "NetworkInterface.h"

#if ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES != 1
	#define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer ) eProcessBuffer
#else
	#define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer ) eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif

/* When a packet is ready to be sent, if it cannot be sent immediately then the
task performing the transmit will block for niTX_BUFFER_FREE_WAIT
milliseconds.  It will do this a maximum of niMAX_TX_ATTEMPTS before giving
up. */
#define niTX_BUFFER_FREE_WAIT	( ( portTickType ) 2UL / portTICK_RATE_MS )
#define niMAX_TX_ATTEMPTS		( 5 )

/* The length of the queue used to send interrupt status words from the
interrupt handler to the deferred handler task. */
#define niINTERRUPT_QUEUE_LENGTH	( 10 )

/*-----------------------------------------------------------*/

/*
 * A deferred interrupt handler task that processes
 */
static void prvEMACHandlerTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* The queue used to communicate Ethernet events with the IP task. */
extern xQueueHandle xNetworkEventQueue;

/* The semaphore used to wake the deferred interrupt handler task when an Rx
interrupt is received. */
static xSemaphoreHandle xEMACRxEventSemaphore = NULL;
/*-----------------------------------------------------------*/

portBASE_TYPE xNetworkInterfaceInitialise( void )
{
EMAC_CFG_Type Emac_Config;
PINSEL_CFG_Type xPinConfig;
portBASE_TYPE xStatus, xReturn;
extern uint8_t ucMACAddress[ 6 ];

	/* Enable Ethernet Pins */
	boardCONFIGURE_ENET_PINS( xPinConfig );

	Emac_Config.Mode = EMAC_MODE_AUTO;
	Emac_Config.pbEMAC_Addr = ucMACAddress;
	xStatus = EMAC_Init( &Emac_Config );

	LPC_EMAC->IntEnable &= ~( EMAC_INT_TX_DONE );

	if( xStatus != ERROR )
	{
		vSemaphoreCreateBinary( xEMACRxEventSemaphore );
		configASSERT( xEMACRxEventSemaphore );

		/* The handler task is created at the highest possible priority to
		ensure the interrupt handler can return directly to it. */
		xTaskCreate( prvEMACHandlerTask, ( const signed char * const ) "EMAC", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, NULL );

		/* Enable the interrupt and set its priority to the minimum
		interrupt priority.  */
		NVIC_SetPriority( ENET_IRQn, configMAC_INTERRUPT_PRIORITY );
		NVIC_EnableIRQ( ENET_IRQn );

		xReturn = pdPASS;
	}
	else
	{
		xReturn = pdFAIL;
	}

	configASSERT( xStatus != ERROR );

	return xReturn;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xNetworkInterfaceOutput( xNetworkBufferDescriptor_t * const pxNetworkBuffer )
{
portBASE_TYPE xReturn = pdFAIL;
int32_t x;
extern void EMAC_StartTransmitNextBuffer( uint32_t ulLength );
extern void EMAC_SetNextPacketToSend( uint8_t * pucBuffer );


	/* Attempt to obtain access to a Tx buffer. */
	for( x = 0; x < niMAX_TX_ATTEMPTS; x++ )
	{
		if( EMAC_CheckTransmitIndex() == TRUE )
		{
			/* Will the data fit in the Tx buffer? */
			if( pxNetworkBuffer->xDataLength < EMAC_ETH_MAX_FLEN ) /*_RB_ The size needs to come from FreeRTOSIPConfig.h. */
			{
				/* Assign the buffer to the Tx descriptor that is now known to
				be free. */
				EMAC_SetNextPacketToSend( pxNetworkBuffer->pucBuffer );

				/* The EMAC now owns the buffer. */
				pxNetworkBuffer->pucBuffer = NULL;

				/* Initiate the Tx. */
				EMAC_StartTransmitNextBuffer( pxNetworkBuffer->xDataLength );
				iptraceNETWORK_INTERFACE_TRANSMIT();

				/* The Tx has been initiated. */
				xReturn = pdPASS;
			}
			break;
		}
		else
		{
			vTaskDelay( niTX_BUFFER_FREE_WAIT );
		}
	}

	/* Finished with the network buffer. */
	vNetworkBufferRelease( pxNetworkBuffer );

	return xReturn;
}
/*-----------------------------------------------------------*/

void ENET_IRQHandler( void )
{
uint32_t ulInterruptCause;

	while( ( ulInterruptCause = LPC_EMAC->IntStatus ) != 0 )
	{
		/* Clear the interrupt. */
		LPC_EMAC->IntClear = ulInterruptCause;

		/* Clear fatal error conditions.  NOTE:  The driver does not clear all
		errors, only those actually experienced.  For future reference, range
		errors are not actually errors so can be ignored. */
		if( ( ulInterruptCause & EMAC_INT_TX_UNDERRUN ) != 0U )
		{
			LPC_EMAC->Command |= EMAC_CR_TX_RES;
		}

		/* Unblock the deferred interrupt handler task if the event was an
		Rx. */
		if( ( ulInterruptCause & EMAC_INT_RX_DONE ) != 0UL )
		{
			xSemaphoreGiveFromISR( xEMACRxEventSemaphore, NULL );
		}
	}

	/* ulInterruptCause is used for convenience here.  A context switch is
	wanted, but coding portEND_SWITCHING_ISR( 1 ) would likely result in a
	compiler warning. */
	portEND_SWITCHING_ISR( ulInterruptCause );
}
/*-----------------------------------------------------------*/

static void prvEMACHandlerTask( void *pvParameters )
{
size_t xDataLength;
const uint16_t usCRCLength = 4;
xNetworkBufferDescriptor_t *pxNetworkBuffer;
xIPStackEvent_t xRxEvent = { eEthernetRxEvent, NULL };

/* This is not included in the header file for some reason. */
extern uint8_t *EMAC_NextPacketToRead( void );

	( void ) pvParameters;
	configASSERT( xEMACRxEventSemaphore );

	for( ;; )
	{
		/* Wait for the EMAC interrupt to indicate that another packet has been
		received.  The while() loop is only needed if INCLUDE_vTaskSuspend is
		set to 0 in FreeRTOSConfig.h. */
		while( xSemaphoreTake( xEMACRxEventSemaphore, portMAX_DELAY ) == pdFALSE );

		/* At least one packet has been received. */
		while( EMAC_CheckReceiveIndex() != FALSE )
		{
			/* Obtain the length, minus the CRC.  The CRC is four bytes
			but the length is already minus 1. */
			xDataLength = ( size_t ) EMAC_GetReceiveDataSize() - ( usCRCLength - 1U );

			if( xDataLength > 0U )
			{
				/* Obtain a network buffer to pass this data into the
				stack.  No storage is required as the network buffer
				will point directly to the buffer that already holds
				the	received data. */
				pxNetworkBuffer = pxNetworkBufferGet( 0, ( portTickType ) 0 );

				if( pxNetworkBuffer != NULL )
				{
					pxNetworkBuffer->pucBuffer = EMAC_NextPacketToRead();
					pxNetworkBuffer->xDataLength = xDataLength;
					xRxEvent.pvData = ( void * ) pxNetworkBuffer;

					/* Data was received and stored.  Send a message to the IP
					task to let it know. */
					if( xQueueSendToBack( xNetworkEventQueue, &xRxEvent, ( portTickType ) 0 ) == pdFALSE )
					{
						vNetworkBufferRelease( pxNetworkBuffer );
						iptraceETHERNET_RX_EVENT_LOST();
					}
				}
				else
				{
					iptraceETHERNET_RX_EVENT_LOST();
				}

				iptraceNETWORK_INTERFACE_RECEIVE();
			}

			/* Release the frame. */
			EMAC_UpdateRxConsumeIndex();
		}
	}
}
/*-----------------------------------------------------------*/

