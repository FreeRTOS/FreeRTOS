/*
 * FreeRTOS+UDP V1.0.4
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/* WinPCap includes. */
#define HAVE_REMOTE
#include "pcap.h"

/* Standard includes. */
#include <stdint.h>

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

/* If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 1, then the Ethernet
driver will filter incoming packets and only pass the stack those packets it
considers need processing.  In this case ipCONSIDER_FRAME_FOR_PROCESSING() can
be #defined away.  If ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES is set to 0
then the Ethernet driver will pass all received packets to the stack, and the
stack must do the filtering itself.  In this case ipCONSIDER_FRAME_FOR_PROCESSING
needs to call eConsiderFrameForProcessing. */
#if ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES != 1
	#define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer ) eProcessBuffer
#else
	#define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer ) eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif

/*-----------------------------------------------------------*/

/*
 * Print out a numbered list of network interfaces that are available on the
 * host computer.
 */
static pcap_if_t * prvPrintAvailableNetworkInterfaces( void );

/*
 * Open the network interface.  The number of the interface to be opened is set
 * by the configNETWORK_INTERFACE_TO_USE constant in FreeRTOSConfig.h.
 */
static void prvOpenSelectedNetworkInterface( pcap_if_t *pxAllNetworkInterfaces );

/*
 * Configure the capture filter to allow blocking reads, and to filter out
 * packets that are not of interest to this demo.
 */
static void prvConfigureCaptureBehaviour( void );

/*
 * A function that simulates Ethernet interrupts by periodically polling the
 * WinPCap interface for new data.
 */
static void prvInterruptSimulatorTask( void *pvParameters );

/* The interface being used by WinPCap. */
static pcap_t *pxOpenedInterfaceHandle = NULL;

/*-----------------------------------------------------------*/

/* Required by the WinPCap library. */
static char cErrorBuffer[ PCAP_ERRBUF_SIZE ];

/* When statically allocated network buffers are used (as opposed to having
the buffer payloads allocated and freed as required) the actual buffer storage
areas must be defined in the portable layer.  This is because different
microcontrollers have different location, size and alignment requirements.  In
this case the network buffers are declared in NetworkInterface.c because, as
this file is only used on Windows machines, wasting a few bytes in buffers that
never get used does not matter (the buffers will not get used if the dynamic
payload allocation file is included in the project). */
static uint8_t ucBuffers[ ipconfigNUM_NETWORK_BUFFERS ][ ipTOTAL_ETHERNET_FRAME_SIZE + ipBUFFER_PADDING ];

/* The queue used to communicate Ethernet events with the IP task. */
extern xQueueHandle xNetworkEventQueue;

/* Protect the PCAP interface as it is accessed from two tasks (an interrupt
simulator is used as real interrupts cannot be obtained from the Ethernet as
would normally be the case). */
xSemaphoreHandle xPCAPMutex = NULL;

/*-----------------------------------------------------------*/

BaseType_t xNetworkInterfaceInitialise( void )
{
BaseType_t xReturn = pdFALSE;
pcap_if_t *pxAllNetworkInterfaces;

	if( xPCAPMutex == NULL )
	{
		xPCAPMutex = xSemaphoreCreateMutex();
		configASSERT( xPCAPMutex );
	}

	/* Query the computer the simulation is being executed on to find the
	network interfaces it has installed. */
	pxAllNetworkInterfaces = prvPrintAvailableNetworkInterfaces();

	/* Open the network interface.  The number of the interface to be opened is
	set by the configNETWORK_INTERFACE_TO_USE constant in FreeRTOSConfig.h.
	Calling this function will set the pxOpenedInterfaceHandle variable.  If,
	after calling this function, pxOpenedInterfaceHandle is equal to NULL, then
	the interface could not be opened. */
	if( pxAllNetworkInterfaces != NULL )
	{
		prvOpenSelectedNetworkInterface( pxAllNetworkInterfaces );
	}

	if( pxOpenedInterfaceHandle != NULL )
	{
		xReturn = pdPASS;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

#if updconfigLOOPBACK_ETHERNET_PACKETS == 1

	BaseType_t xNetworkInterfaceOutput( xNetworkBufferDescriptor_t * const pxNetworkBuffer )
	{
	xEthernetHeader_t *pxEthernetHeader;
	xIPStackEvent_t xRxEvent = { eEthernetRxEvent, NULL };
	extern uint8_t xDefaultPartUDPPacketHeader[];
	static const xMACAddress_t xBroadcastMACAddress = { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff };
	BaseType_t xCanLoopback;

		pxEthernetHeader = ( xEthernetHeader_t * ) pxNetworkBuffer->pucEthernetBuffer;

		if( memcmp( ( void * ) &( pxEthernetHeader->xDestinationAddress ), ( void * ) &xBroadcastMACAddress, sizeof( xMACAddress_t ) ) == 0 )
		{
			/* This is a broadcast. */
			xCanLoopback = pdTRUE;
		}
		else if( memcmp( ( void * ) &( pxEthernetHeader->xDestinationAddress ), ( void * ) xDefaultPartUDPPacketHeader, sizeof( xMACAddress_t ) ) == 0 )
		{
			/* This is being sent to itself. */
			xCanLoopback = pdTRUE;
		}
		else
		{
			/* This is being sent externally. */
			xCanLoopback = pdFALSE;
		}

		iptraceNETWORK_INTERFACE_TRANSMIT();

		if( xCanLoopback == pdTRUE )
		{
			/* Just loop the frame back to the input queue.  Here the loopback
			is sending a message to itself, so a block time cannot be used for
			fear of deadlocking. */
			xRxEvent.pvData = ( void * ) pxNetworkBuffer;
			if( xQueueSendToBack( xNetworkEventQueue, &xRxEvent, ( TickType_t ) 0 ) == pdFALSE )
			{
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
			/* Send the packet. */
			xSemaphoreTake( xPCAPMutex, portMAX_DELAY );
			{
				pcap_sendpacket( pxOpenedInterfaceHandle, pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength );
			}
			xSemaphoreGive( xPCAPMutex );

			/* The buffer has been transmitted so can be released. */
			vNetworkBufferRelease( pxNetworkBuffer );
		}

		return pdPASS;
	}

#else /* updconfigLOOPBACK_ETHERNET_PACKETS == 1 */

	BaseType_t xNetworkInterfaceOutput( xNetworkBufferDescriptor_t * const pxNetworkBuffer )
	{
		xSemaphoreTake( xPCAPMutex, portMAX_DELAY );
		{
			iptraceNETWORK_INTERFACE_TRANSMIT();
			pcap_sendpacket( pxOpenedInterfaceHandle, pxNetworkBuffer->pucEthernetBuffer, pxNetworkBuffer->xDataLength );
		}
		xSemaphoreGive( xPCAPMutex );

		/* The buffer has been transmitted so can be released. */
		vNetworkBufferRelease( pxNetworkBuffer );

		return pdPASS;
	}

#endif /* updconfigLOOPBACK_ETHERNET_PACKETS == 1 */
/*-----------------------------------------------------------*/

static pcap_if_t * prvPrintAvailableNetworkInterfaces( void )
{
pcap_if_t * pxAllNetworkInterfaces = NULL, *xInterface;
long lInterfaceNumber = 1;

    if( pcap_findalldevs_ex( PCAP_SRC_IF_STRING, NULL, &pxAllNetworkInterfaces, cErrorBuffer ) == -1 )
    {
        printf( "\r\nCould not obtain a list of network interfaces\r\n%s\r\n", cErrorBuffer );
        pxAllNetworkInterfaces = NULL;
    }

	if( pxAllNetworkInterfaces != NULL )
	{
		/* Print out the list of network interfaces.  The first in the list
		is interface '1', not interface '0'. */
		for( xInterface = pxAllNetworkInterfaces; xInterface != NULL; xInterface = xInterface->next )
		{
			printf( "%d. %s", lInterfaceNumber, xInterface->name );

			if( xInterface->description != NULL )
			{
				printf( " (%s)\r\n", xInterface->description );
			}
			else
			{
				printf( " (No description available)\r\n") ;
			}

			lInterfaceNumber++;
		}
	}

    if( lInterfaceNumber == 1 )
    {
		/* The interface number was never incremented, so the above for() loop
		did not execute meaning no interfaces were found. */
        printf( " \r\nNo network interfaces were found.\r\n" );
        pxAllNetworkInterfaces = NULL;
    }

	printf( "\r\nThe interface that will be opened is set by configNETWORK_INTERFACE_TO_USE which should be defined in FreeRTOSConfig.h\r\n" );
	printf( "Attempting to open interface number %d.\r\n", configNETWORK_INTERFACE_TO_USE );

    if( ( configNETWORK_INTERFACE_TO_USE < 1L ) || ( configNETWORK_INTERFACE_TO_USE > lInterfaceNumber ) )
    {
        printf("\r\nconfigNETWORK_INTERFACE_TO_USE is not in the valid range.\r\n" );

		if( pxAllNetworkInterfaces != NULL )
		{
			/* Free the device list, as no devices are going to be opened. */
			pcap_freealldevs( pxAllNetworkInterfaces );
			pxAllNetworkInterfaces = NULL;
		}
    }

	return pxAllNetworkInterfaces;
}
/*-----------------------------------------------------------*/

static void prvOpenSelectedNetworkInterface( pcap_if_t *pxAllNetworkInterfaces )
{
pcap_if_t *xInterface;
long x;

    /* Walk the list of devices until the selected device is located. */
	xInterface = pxAllNetworkInterfaces;
    for( x = 0L; x < ( configNETWORK_INTERFACE_TO_USE - 1L ); x++ )
	{
		xInterface = xInterface->next;
	}

    /* Open the selected interface. */
	pxOpenedInterfaceHandle = pcap_open(	xInterface->name,          	/* The name of the selected interface. */
											ipTOTAL_ETHERNET_FRAME_SIZE, 	/* The size of the packet to capture. */
											PCAP_OPENFLAG_PROMISCUOUS,	/* Open in promiscious mode as the MAC and
																		IP address is going to be "simulated", and
																		not be the real MAC and IP address.  This allows
																		trafic to the simulated IP address to be routed
																		to uIP, and trafic to the real IP address to be
																		routed to the Windows TCP/IP stack. */
											0x00L,             			/* The read time out. */
											NULL,             			/* No authentication is required as this is
																		not a remote capture session. */
											cErrorBuffer
									   );

    if ( pxOpenedInterfaceHandle == NULL )
    {
        printf( "\r\n%s is not supported by WinPcap and cannot be opened\r\n", xInterface->name );
    }
	else
	{
		/* Configure the capture filter to allow blocking reads, and to filter
		out packets that are not of interest to this demo. */
		prvConfigureCaptureBehaviour();
	}

	/* The device list is no longer required. */
	pcap_freealldevs( pxAllNetworkInterfaces );
}
/*-----------------------------------------------------------*/

static void prvConfigureCaptureBehaviour( void )
{
struct bpf_program xFilterCode;
const long lMinBytesToCopy = 10L, lBlocking = 1L;
unsigned long ulNetMask;

	/* Unblock a read as soon as anything is received. */
	pcap_setmintocopy( pxOpenedInterfaceHandle, lMinBytesToCopy );

	/* Allow blocking. */
	pcap_setnonblock( pxOpenedInterfaceHandle, lBlocking, cErrorBuffer );

	/* Set up a filter so only the packets of interest are passed to the IP
	stack.  cErrorBuffer is used for convenience to create the string.  Don't
	confuse this with an error message. *//*_RB_ This should not use the #defined constants. *//*_RB_ Constants should not be used, but passed through a generic network API. */
	sprintf( cErrorBuffer, "broadcast or multicast or ether host %x:%x:%x:%x:%x:%x", configMAC_ADDR0, configMAC_ADDR1, configMAC_ADDR2, configMAC_ADDR3, configMAC_ADDR4, configMAC_ADDR5 );

	/*_RB_ Constants should not be used, but passed through a generic network API. */
	ulNetMask = ( configNET_MASK3 << 24UL ) | ( configNET_MASK2 << 16UL ) | ( configNET_MASK1 << 8L ) | configNET_MASK0;

	if( pcap_compile(pxOpenedInterfaceHandle, &xFilterCode, cErrorBuffer, 1, ulNetMask ) < 0 )
    {
        printf("\r\nThe packet filter string is invalid\r\n" );
    }
	else
	{
		if( pcap_setfilter( pxOpenedInterfaceHandle, &xFilterCode ) < 0 )
		{
			printf( "\r\nAn error occurred setting the packet filter.\r\n" );
		}
	}

	/* Create a task that simulates an interrupt in a real system.  This will
	block waiting for packets, then send a message to the uIP task when data
	is available. */
	xTaskCreate( prvInterruptSimulatorTask, "MAC_ISR", configMINIMAL_STACK_SIZE, NULL, configMAC_ISR_SIMULATOR_PRIORITY, NULL );
}
/*-----------------------------------------------------------*/

static void prvInterruptSimulatorTask( void *pvParameters )
{
static struct pcap_pkthdr *pxHeader;
const uint8_t *pucPacketData;
long lResult;
xNetworkBufferDescriptor_t *pxNetworkBuffer;
xIPStackEvent_t xRxEvent = { eEthernetRxEvent, NULL };
eFrameProcessingResult_t eResult;

	/* Just to kill the compiler warning. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Get the next packet. */
		xSemaphoreTake( xPCAPMutex, portMAX_DELAY );
		{
			lResult = pcap_next_ex( pxOpenedInterfaceHandle, &pxHeader, &pucPacketData );
		}
		xSemaphoreGive( xPCAPMutex );

		if( lResult == 1 )
		{
			eResult = ipCONSIDER_FRAME_FOR_PROCESSING( pucPacketData );
			if( eResult == eProcessBuffer )
			{
				/* Will the data fit into the frame buffer? */
				if( pxHeader->len <= ipTOTAL_ETHERNET_FRAME_SIZE )
				{
					/* Obtain a buffer into which the data can be placed.  This
					is only	an interrupt simulator, not a real interrupt, so it
					is ok to call the task level function here.  */
					xSemaphoreTake( xPCAPMutex, portMAX_DELAY );
					{
						pxNetworkBuffer = pxNetworkBufferGet( pxHeader->len, 0 );
					}
					xSemaphoreGive( xPCAPMutex );

					if( pxNetworkBuffer != NULL )
					{
						memcpy( pxNetworkBuffer->pucEthernetBuffer, pucPacketData, pxHeader->len );
						pxNetworkBuffer->xDataLength = ( size_t ) pxHeader->len;
						xRxEvent.pvData = ( void * ) pxNetworkBuffer;

						/* Data was received and stored.  Send a message to the IP
						task to let it know. */
						if( xQueueSendToBack( xNetworkEventQueue, &xRxEvent, ( TickType_t ) 0 ) == pdFALSE )
						{
							/* The buffer could not be sent to the stack so
							must be released again.  This is only an interrupt
							simulator, not a real interrupt, so it is ok to use
							the task level function here. */
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
						iptraceETHERNET_RX_EVENT_LOST();
					}
				}
				else
				{
					/* Log that a packet was dropped because it would have
					overflowed the buffer. */
				}
			}
		}
		else
		{
			/* There is no real way of simulating an interrupt.  Make sure
			other tasks can run. */
			vTaskDelay( configWINDOWS_MAC_INTERRUPT_SIMULATOR_DELAY );
		}
	}
}
/*-----------------------------------------------------------*/

#if configUSE_STATIC_BUFFERS == 1
	void vNetworkInterfaceAllocateRAMToBuffers( xNetworkBufferDescriptor_t pxNetworkBuffers[ ipconfigNUM_NETWORK_BUFFERS ] )
	{
	BaseType_t x;
	xNetworkBufferDescriptor_t **ppxStartOfBuffer;

		for( x = 0; x < ipconfigNUM_NETWORK_BUFFERS; x++ )
		{
			/* Place a pointer to the network buffer structure at the beginning
			of the buffer that will be allocated to the structure. */
			ppxStartOfBuffer = ( xNetworkBufferDescriptor_t ** ) &( ucBuffers[ x ][ 0 ] );
			*ppxStartOfBuffer = &( pxNetworkBuffers[ x ] );
			
			/* Allocate the buffer to the network buffer structure, jumping over
			the bytes where the pointer to the network buffer is now stored. */
			pxNetworkBuffers[ x ].pucEthernetBuffer = &( ucBuffers[ x ][ ipBUFFER_PADDING ] );
		}
	}
#endif
/*-----------------------------------------------------------*/
