/*
FreeRTOS+TCP V2.0.11
Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.

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

/* ========================= FreeRTOS includes ============================== */
#include "FreeRTOS.h"
#include "event_groups.h"
#include "task.h"
#include "semphr.h"

/* ========================= FreeRTOS+TCP includes ========================== */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_IP_Private.h"
#include "NetworkBufferManagement.h"
#include "FreeRTOS_Stream_Buffer.h"

/* ======================== Standard Library inludes ======================== */
#include <stdio.h>
#include <unistd.h>
#include <stdint.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <pthread.h>
#include <stdlib.h>
#include <ctype.h>
#include <signal.h>
#include <pcap.h>

/* ========================== Local includes =================================*/
#include <utils/wait_for_event.h>

/* ======================== Macro Definitions =============================== */
#if ( ipconfigETHERNET_DRIVER_FILTERS_FRAME_TYPES == 0 )
	#define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer )    eProcessBuffer
#else
	#define ipCONSIDER_FRAME_FOR_PROCESSING( pucEthernetBuffer ) \
	eConsiderFrameForProcessing( ( pucEthernetBuffer ) )
#endif

/* ============================== Definitions =============================== */
#define xSEND_BUFFER_SIZE	 32768
#define xRECV_BUFFER_SIZE	 32768
#define MAX_CAPTURE_LEN		 65535
#define IP_SIZE				 100

/* ================== Static Function Prototypes ============================ */
static int prvConfigureCaptureBehaviour( void );
static int prvCreateThreadSafeBuffers( void );
static void * prvLinuxPcapSendThread( void *pvParam );
static void * prvLinuxPcapRecvThread( void *pvParam );
static void prvInterruptSimulatorTask( void *pvParameters );
static void prvPrintAvailableNetworkInterfaces( pcap_if_t *  pxAllNetworkInterfaces );
static pcap_if_t * prvGetAvailableNetworkInterfaces( void );
static const char * prvRemoveSpaces( char *pcBuffer,
									 int aBuflen,
									 const char *pcMessage );
static int prvOpenSelectedNetworkInterface( pcap_if_t *pxAllNetworkInterfaces );
static int prvCreateWorkerThreads( void );
static int prvSetDeviceModes( void );
static void print_hex( unsigned const char * const bin_data,
					   size_t len );

/* ======================== Static Global Variables ========================= */
static StreamBuffer_t *xSendBuffer = NULL;
static StreamBuffer_t *xRecvBuffer = NULL;
extern uint8_t ucMACAddress[ 6 ];
static char errbuf[ PCAP_ERRBUF_SIZE ];
static pcap_t *pxOpenedInterfaceHandle = NULL;
static struct event *pvSendEvent = NULL;
static uint32_t ulPCAPSendFailures = 0;
static BaseType_t xConfigNetworkInterfaceToUse = configNETWORK_INTERFACE_TO_USE;
static BaseType_t xInvalidInterfaceDetected = pdFALSE;

/* ======================= API Function definitions ========================= */

/*!
 * @brief API call, called from reeRTOS_IP.c to initialize the capture device
 *        to be able to send and receive packets
 * @return pdPASS if successful else pdFAIL
 */
BaseType_t xNetworkInterfaceInitialise( void )
{
BaseType_t ret = pdFAIL;
pcap_if_t *pxAllNetworkInterfaces;

	/* Query the computer the simulation is being executed on to find the
	network interfaces it has installed. */
	pxAllNetworkInterfaces = prvGetAvailableNetworkInterfaces();

	if( pxAllNetworkInterfaces != NULL )
	{
		prvPrintAvailableNetworkInterfaces( pxAllNetworkInterfaces );
		ret = prvOpenSelectedNetworkInterface( pxAllNetworkInterfaces );

		if( ret == pdPASS )
		{
			ret = prvCreateThreadSafeBuffers();

			if( ret == pdPASS )
			{
				ret = prvCreateWorkerThreads();
			}
		}

		/* The device list is no longer required. */
		pcap_freealldevs( pxAllNetworkInterfaces );
	}

	if( ( pxOpenedInterfaceHandle != NULL ) && ( ret == pdPASS ) )
	{
		ret = pdPASS;
	}

	return ret;
}

/*!
 * @brief API call, called from reeRTOS_IP.c to send a network packet over the
 *        selected interface
 * @return pdTRUE if successful else pdFALSE
 */
BaseType_t xNetworkInterfaceOutput( NetworkBufferDescriptor_t * const pxNetworkBuffer,
									BaseType_t bReleaseAfterSend )
{
size_t xSpace;

	iptraceNETWORK_INTERFACE_TRANSMIT();
	configASSERT( xIsCallingFromIPTask() == pdTRUE );

	/* Both the length of the data being sent and the actual data being sent
	are placed in the thread safe buffer used to pass data between the FreeRTOS
	tasks and the pthread that sends data via the pcap library.  Drop
	the packet if there is insufficient space in the buffer to hold both. */
	xSpace = uxStreamBufferGetSpace( xSendBuffer );

	if( ( pxNetworkBuffer->xDataLength <=
		  ( ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER ) ) &&
		( xSpace >= ( pxNetworkBuffer->xDataLength +
					  sizeof( pxNetworkBuffer->xDataLength ) ) ) )
	{
		/* First write in the length of the data, then write in the data
		itself. */
		uxStreamBufferAdd( xSendBuffer,
						   0,
						   ( const uint8_t * ) &( pxNetworkBuffer->xDataLength ),
						   sizeof( pxNetworkBuffer->xDataLength ) );
		uxStreamBufferAdd( xSendBuffer,
						   0,
						   ( const uint8_t * ) pxNetworkBuffer->pucEthernetBuffer,
						   pxNetworkBuffer->xDataLength );
	}
	else
	{
		FreeRTOS_printf( ( "xNetworkInterfaceOutput: send buffers full to store %lu\n",
						   pxNetworkBuffer->xDataLength ) );
	}

	/* Kick the Tx task in either case in case it doesn't know the buffer is
	full. */
	event_signal( pvSendEvent );

	/* The buffer has been sent so can be released. */
	if( bReleaseAfterSend != pdFALSE )
	{
		vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
	}

	return pdPASS;
}

/* ====================== Static Function definitions ======================= */

/*!
 * @brief create thread safe buffers to send/receive packets between threads
 * @returns
 */
static int prvCreateThreadSafeBuffers( void )
{
int ret = pdFAIL;

	/* The buffer used to pass data to be transmitted from a FreeRTOS task to
	the linux thread that sends via the pcap library. */
	do
	{
		if( xSendBuffer == NULL )
		{
			xSendBuffer = ( StreamBuffer_t * ) malloc( sizeof( *xSendBuffer ) - sizeof( xSendBuffer->ucArray ) + xSEND_BUFFER_SIZE + 1 );

			if( xSendBuffer == NULL )
			{
				break;
			}

			configASSERT( xSendBuffer );
			memset( xSendBuffer, '\0', sizeof( *xSendBuffer ) - sizeof( xSendBuffer->ucArray ) );
			xSendBuffer->LENGTH = xSEND_BUFFER_SIZE + 1;
		}

		/* The buffer used to pass received data from the pthread that receives
		via the pcap library to the FreeRTOS task. */
		if( xRecvBuffer == NULL )
		{
			xRecvBuffer = ( StreamBuffer_t * ) malloc( sizeof( *xRecvBuffer ) - sizeof( xRecvBuffer->ucArray ) + xRECV_BUFFER_SIZE + 1 );

			if( xRecvBuffer == NULL )
			{
				break;
			}

			configASSERT( xRecvBuffer );
			memset( xRecvBuffer, '\0', sizeof( *xRecvBuffer ) - sizeof( xRecvBuffer->ucArray ) );
			xRecvBuffer->LENGTH = xRECV_BUFFER_SIZE + 1;
		}

		ret = pdPASS;
	} while( 0 );

	return ret;
}

/*!
 * @brief  print network interfaces available on the system
 * @param[in]   pxAllNetworkInterfaces interface structure list to print
 */
static void prvPrintAvailableNetworkInterfaces( pcap_if_t *  pxAllNetworkInterfaces )
{
pcap_if_t *xInterface;
int32_t lInterfaceNumber = 1;
char cBuffer[ 512 ];

	if( pxAllNetworkInterfaces != NULL )
	{
		/* Print out the list of network interfaces.  The first in the list
		is interface '1', not interface '0'. */
		for( xInterface = pxAllNetworkInterfaces;
			 xInterface != NULL; xInterface = xInterface->next )
		{
			/* The descriptions of the devices can be full of spaces, clean them
			a little.  printf() can only be used here because the network is not
			up yet - so no other network tasks will be running. */
			printf( "Interface %d - %s\n",
					lInterfaceNumber,
					prvRemoveSpaces( cBuffer, sizeof( cBuffer ), xInterface->name ) );
			printf( "              (%s)\n",
					prvRemoveSpaces( cBuffer,
									 sizeof( cBuffer ),
									 xInterface->description ? xInterface->description :
									 "No description" ) );
			printf( "\n" );
			lInterfaceNumber++;
		}
	}

	if( lInterfaceNumber == 1 )
	{
		/* The interface number was never incremented, so the above for() loop
		did not execute meaning no interfaces were found. */
		printf( " \nNo network interfaces were found.\n" );
		pxAllNetworkInterfaces = NULL;
	}

	printf( "\r\nThe interface that will be opened is set by " );
	printf( "\"configNETWORK_INTERFACE_TO_USE\", which\r\nshould be defined in FreeRTOSConfig.h\r\n" );

	if( ( xConfigNetworkInterfaceToUse < 1L ) || ( xConfigNetworkInterfaceToUse >= lInterfaceNumber ) )
	{
		printf( "\r\nERROR:  configNETWORK_INTERFACE_TO_USE is set to %ld, which is an invalid value.\r\n", xConfigNetworkInterfaceToUse );
		printf( "Please set configNETWORK_INTERFACE_TO_USE to one of the interface numbers listed above,\r\n" );
		printf( "then re-compile and re-start the application.  Only Ethernet (as opposed to WiFi)\r\n" );
		printf( "interfaces are supported.\r\n\r\nHALTING\r\n\r\n\r\n" );
		xInvalidInterfaceDetected = pdTRUE;

		if( pxAllNetworkInterfaces != NULL )
		{
			/* Free the device list, as no devices are going to be opened. */
			pcap_freealldevs( pxAllNetworkInterfaces );
			pxAllNetworkInterfaces = NULL;
		}
	}
	else
	{
		printf( "Attempting to open interface number %ld.\n", xConfigNetworkInterfaceToUse );
	}
}

/*!
 * @brief  get network interfaces from the system
 * @returns the structure list containing all found devices
 */
static pcap_if_t * prvGetAvailableNetworkInterfaces( void )
{
pcap_if_t * pxAllNetworkInterfaces = NULL;

	if( xInvalidInterfaceDetected == pdFALSE )
	{
	int ret;
		ret = pcap_findalldevs( &pxAllNetworkInterfaces, errbuf );

		if( ret == PCAP_ERROR )
		{
			FreeRTOS_printf( ( "Could not obtain a list of network interfaces\n%s\n",
							   errbuf ) );
			pxAllNetworkInterfaces = NULL;
		}
		else
		{
			printf( "\r\n\r\nThe following network interfaces are available:\r\n\r\n" );
		}
	}

	return pxAllNetworkInterfaces;
}

/*!
 * @brief  set device operation modes
 * @returns pdPASS on success pdFAIL on failure
 */
static int prvSetDeviceModes()
{
int ret = pdFAIL;

	/*
	  Open in promiscuous mode as the MAC and
	  IP address is going to be "simulated", and
	  not be the real MAC and IP address.  This allows
	  traffic to the simulated IP address to be routed
	  to uIP, and traffic to the real IP address to be
	  routed to the Linux TCP/IP stack.
	*/
	FreeRTOS_debug_printf( ( "setting device modes of operation...\n" ) );

	do
	{
		ret = pcap_set_promisc( pxOpenedInterfaceHandle, 1 );

		if( ( ret != 0 ) && ( ret != PCAP_ERROR_ACTIVATED ) )
		{
			FreeRTOS_printf( ( "coult not activate promisuous mode\n" ) );
			break;
		}

		ret = pcap_set_snaplen( pxOpenedInterfaceHandle,
								ipTOTAL_ETHERNET_FRAME_SIZE );

		if( ( ret != 0 ) && ( ret != PCAP_ERROR_ACTIVATED ) )
		{
			FreeRTOS_printf( ( "coult not set snaplen\n" ) );
			break;
		}

		ret = pcap_set_timeout( pxOpenedInterfaceHandle, 200 );

		if( ( ret != 0 ) && ( ret != PCAP_ERROR_ACTIVATED ) )
		{
			FreeRTOS_printf( ( "coult not set timeout\n" ) );
			break;
		}

		ret = pcap_set_buffer_size( pxOpenedInterfaceHandle,
									ipTOTAL_ETHERNET_FRAME_SIZE * 1100 );

		if( ( ret != 0 ) && ( ret != PCAP_ERROR_ACTIVATED ) )
		{
			FreeRTOS_printf( ( "coult not set buffer size\n" ) );
			break;
		}

		ret = pdPASS;
	} while( 0 );

	return ret;
}

/*!
 * @brief  open selected interface given its name
 * @param [in] pucName interface  name to pen
 * @returns pdPASS on success pdFAIL on failure
 */
static int prvOpenInterface( const char *pucName )
{
static char pucInterfaceName[ 256 ];
int ret = pdFAIL;

	if( pucName != NULL )
	{
		( void ) strncpy( pucInterfaceName, pucName, sizeof( pucInterfaceName ) );
		pucInterfaceName[ sizeof( pucInterfaceName ) - ( size_t ) 1 ] = '\0';

		FreeRTOS_debug_printf( ( "opening interface %s\n", pucInterfaceName ) );

		pxOpenedInterfaceHandle = pcap_create( pucInterfaceName, errbuf );

		if( pxOpenedInterfaceHandle != NULL )
		{
			ret = prvSetDeviceModes();

			if( ret == pdPASS )
			{
				if( pcap_activate( pxOpenedInterfaceHandle ) == 0 )
				{
					/* Configure the capture filter to allow blocking reads, and to filter
					out packets that are not of interest to this demo. */
					ret = prvConfigureCaptureBehaviour();
				}
				else
				{
					FreeRTOS_debug_printf( ( "pcap activate error %s\n",
											 pcap_geterr( pxOpenedInterfaceHandle ) ) );
					ret = pdFAIL;
				}
			}
		}
		else
		{
			FreeRTOS_printf( ( "\n%s is not supported by pcap and cannot be opened %s\n",
							   pucInterfaceName, errbuf ) );
		}
	}
	else
	{
		FreeRTOS_printf( ( "could not open interface: name is null\n" ) );
	}

	return ret;
}

/*!
 * @brief Open the network interface. The number of the interface to be opened is
 *	       set by the configNETWORK_INTERFACE_TO_USE constant in FreeRTOSConfig.h
 *	       Calling this function will set the pxOpenedInterfaceHandle variable
 *	       If, after calling this function, pxOpenedInterfaceHandle
 *	       is equal to NULL, then the interface could not be opened.
 * @param [in] pxAllNetworkInterfaces network interface list to choose from
 * @returns pdPASS on success or pdFAIL when something goes wrong
 */
static int prvOpenSelectedNetworkInterface( pcap_if_t *pxAllNetworkInterfaces )
{
pcap_if_t *pxInterface;
int32_t x;
int ret = pdFAIL;

	/* Walk the list of devices until the selected device is located. */
	pxInterface = pxAllNetworkInterfaces;

	for( x = 0L; x < ( xConfigNetworkInterfaceToUse - 1L ); x++ )
	{
		pxInterface = pxInterface->next;
	}

	/* Open the selected interface. */
	if( prvOpenInterface( pxInterface->name ) == pdPASS )
	{
		FreeRTOS_debug_printf( ( "Successfully opened interface number %d.\n", x + 1 ) );
		ret = pdPASS;
	}
	else
	{
		FreeRTOS_printf( ( "Failed to open interface number %d.\n", x + 1 ) );
	}

	return ret;
}

/*!
 * @brief launch 2 linux threads, one for Tx and one for Rx
 *        and one FreeRTOS thread that will simulate an interrupt
 *        and notify the tcp/ip stack of new data
 * @return pdPASS on success otherwise pdFAIL
 */
static int prvCreateWorkerThreads( void )
{
pthread_t vPcapRecvThreadHandle;
pthread_t vPcapSendThreadHandle;
int ret = pdPASS;

	if( pvSendEvent == NULL )
	{
		FreeRTOS_debug_printf( ( "Creating Threads ..\n" ) );
		ret = pdFAIL;
		/* Create event used to signal the  pcap Tx thread. */
		pvSendEvent = event_create();

		do
		{
			/* Create the thread that handles pcap  Rx. */
			ret = pthread_create( &vPcapRecvThreadHandle,
								  NULL,
								  prvLinuxPcapRecvThread,
								  NULL );

			if( ret != 0 )
			{
				FreeRTOS_printf( ( "pthread error %d", ret ) );
				break;
			}

			/* Create the thread that handles pcap  Tx. */
			ret = pthread_create( &vPcapSendThreadHandle,
								  NULL,
								  prvLinuxPcapSendThread,
								  NULL );

			if( ret != 0 )
			{
				FreeRTOS_printf( ( "pthread error %d", ret ) );
				break;
			}

			ret = pdPASS;
		} while( 0 );

		/* Create a task that simulates an interrupt in a real system.  This will
		block waiting for packets, then send a message to the IP task when data
		is available. */
		if( xTaskCreate( prvInterruptSimulatorTask,
						 "MAC_ISR",
						 configMINIMAL_STACK_SIZE,
						 NULL,
						 configMAC_ISR_SIMULATOR_PRIORITY,
						 NULL ) != pdPASS )
		{
			ret = pdFAIL;
			FreeRTOS_printf( ( "xTaskCreate could not create a new task\n" ) );
		}
	}

	return ret;
}

/*!
 * @brief Create the buffers used to pass packets between the FreeRTOS simulator
 *        and the pthreads that are handling pcap as well as the FreeRTOS task
 *        responsible of simulating an interrupt.
 * @returns pdPASS when successful and pdFAIL when there is a failure
 */
static int prvConfigureCaptureBehaviour( void )
{
	struct bpf_program xFilterCode;
	uint32_t ulNetMask;
	char pcap_filter[ 500 ];
	int ret = pdFAIL;

	FreeRTOS_debug_printf( ( "Configuring Capture behaviour\n" ) );

	/* Set up a filter so only the packets of interest are passed to the IP
	stack.  errbuf is used for convenience to create the string.  Don't
	confuse this with an error message. */
	sprintf( pcap_filter, "broadcast or multicast or ether host %x:%x:%x:%x:%x:%x",
			 ucMACAddress[ 0 ],
			 ucMACAddress[ 1 ],
			 ucMACAddress[ 2 ],
			 ucMACAddress[ 3 ],
			 ucMACAddress[ 4 ],
			 ucMACAddress[ 5 ] );
	FreeRTOS_debug_printf( ( "pcap filter to compile: %s\n", pcap_filter ) );

	ulNetMask = ( configNET_MASK3 << 24UL ) | ( configNET_MASK2 << 16UL ) | ( configNET_MASK1 << 8L ) | configNET_MASK0;

	ret = pcap_compile( pxOpenedInterfaceHandle,
						&xFilterCode,
						pcap_filter,
						1,
						ulNetMask );

	if( ret < 0 )
	{
		( void ) printf( "\nThe packet filter string is invalid %s\n",
						 pcap_geterr( pxOpenedInterfaceHandle ) );
	}
	else
	{
		ret = pcap_setfilter( pxOpenedInterfaceHandle, &xFilterCode );

		if( ret < 0 )
		{
			( void ) printf( "\nAn error occurred setting the packet filter. %s\n",
							 pcap_geterr( pxOpenedInterfaceHandle ) );
		}
		else
		{
			ret = pdPASS;
		}

		/* When pcap_compile() succeeds, it allocates memory for the memory pointed to by the bpf_program struct
		parameter.pcap_freecode() will free that memory. */
		pcap_freecode( &xFilterCode );
	}

	return ret;
}

/*!
 * @brief  callback function called from pcap_dispatch function when new
 *         data arrives on the interface
 * @param [in] user data sent to pcap_dispatch
 * @param [in] pkt_header received packet header
 * @param [in] pkt_data received packet data
 * @warning this is called from a Linux thread, do not attempt any FreeRTOS calls
 */
static void pcap_callback( unsigned char *user,
						   const struct pcap_pkthdr *pkt_header,
						   const u_char *pkt_data )
{
	FreeRTOS_debug_printf( ( "Receiving < ===========  network callback user: %s len: %d caplen: %d\n",
							 user,
							 pkt_header->len,
							 pkt_header->caplen ) );
	print_hex( pkt_data, pkt_header->len );

	/* Pass data to the FreeRTOS simulator on a thread safe circular buffer. */
	if( ( pkt_header->caplen <= ( ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER ) ) &&
		( uxStreamBufferGetSpace( xRecvBuffer ) >= ( ( ( size_t ) pkt_header->caplen ) + sizeof( *pkt_header ) ) ) )
	{
		uxStreamBufferAdd( xRecvBuffer, 0, ( const uint8_t * ) pkt_header, sizeof( *pkt_header ) );
		uxStreamBufferAdd( xRecvBuffer, 0, ( const uint8_t * ) pkt_data, ( size_t ) pkt_header->caplen );
	}
}

/*!
 * @brief infinite loop pthread to read from pcap
 * @param [in] pvParam not used
 * @returns NULL
 * @warning this is called from a Linux thread, do not attempt any FreeRTOS calls
 * @remarks This function disables signal, to prevent it from being put into
 *          sleep byt the posix port
 */
static void * prvLinuxPcapRecvThread( void *pvParam )
{
int ret;

	( void ) pvParam;

	/* Disable signals to this thread since this is a Linux pthread to be able to
	 * printf and other blocking operations without being interruped and put in
	 * suspension mode by the linux port signals
	 */
	sigset_t set;
	sigfillset( &set );
	pthread_sigmask( SIG_SETMASK, &set, NULL );

	for( ; ; )
	{
		ret = pcap_dispatch( pxOpenedInterfaceHandle, 1,
							 pcap_callback, ( u_char * ) "mydata" );

		if( ret == -1 )
		{
			FreeRTOS_printf( ( "pcap_dispatch error received: %s\n",
							   pcap_geterr( pxOpenedInterfaceHandle ) ) );
		}
	}

	return NULL;
}

/*!
 * @brief Infinite loop thread that waits for events when there is data
 *        available then sends the data on the interface
 * @param [in] pvParam not used
 * @returns NULL
 * @warning this is called from a Linux thread, do not attempt any FreeRTOS calls
 */
static void * prvLinuxPcapSendThread( void *pvParam )
{
size_t xLength;
uint8_t ucBuffer[ ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER ];
const time_t xMaxMSToWait = 1000;

	( void ) pvParam;

	/* disable signals to avoid treating this thread as a FreeRTOS task and puting
	 * it to sleep by the scheduler */
	sigset_t set;
	sigfillset( &set );
	pthread_sigmask( SIG_SETMASK, &set, NULL );

	for( ; ; )
	{
		/* Wait until notified of something to send. */
		event_wait_timed( pvSendEvent, xMaxMSToWait );

		/* Is there more than the length value stored in the circular buffer
		used to pass data from the FreeRTOS simulator into this pthread?*/
		while( uxStreamBufferGetSize( xSendBuffer ) > sizeof( xLength ) )
		{
			uxStreamBufferGet( xSendBuffer, 0, ( uint8_t * ) &xLength, sizeof( xLength ), pdFALSE );
			uxStreamBufferGet( xSendBuffer, 0, ( uint8_t * ) ucBuffer, xLength, pdFALSE );
			FreeRTOS_debug_printf( ( "Sending  ========== > data pcap_sendpadcket %lu\n", xLength ) );
			print_hex( ucBuffer, xLength );

			if( pcap_sendpacket( pxOpenedInterfaceHandle, ucBuffer, xLength ) != 0 )
			{
				FreeRTOS_printf( ( "pcap_sendpackeet: send failed %d\n", ulPCAPSendFailures ) );
				ulPCAPSendFailures++;
			}
		}
	}

	return NULL;
}

/*!
 * @brief FreeRTOS infinite loop thread that simulates a network interrupt to notify the
 *         network stack of the presence of new data
 * @param [in] pvParameters not used
 */
static void prvInterruptSimulatorTask( void *pvParameters )
{
	struct pcap_pkthdr xHeader;
	static struct pcap_pkthdr *pxHeader;
	const uint8_t *pucPacketData;
	uint8_t ucRecvBuffer[ ipconfigNETWORK_MTU + ipSIZE_OF_ETH_HEADER ];
	NetworkBufferDescriptor_t *pxNetworkBuffer;
	IPStackEvent_t xRxEvent = { eNetworkRxEvent, NULL };
	eFrameProcessingResult_t eResult;

	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	for( ; ; )
	{
		/* Does the circular buffer used to pass data from the pthread thread that
		handles pacap Rx into the FreeRTOS simulator contain another packet? */
		if( uxStreamBufferGetSize( xRecvBuffer ) > sizeof( xHeader ) )
		{
			/* Get the next packet. */
			uxStreamBufferGet( xRecvBuffer, 0, ( uint8_t * ) &xHeader, sizeof( xHeader ), pdFALSE );
			uxStreamBufferGet( xRecvBuffer, 0, ( uint8_t * ) ucRecvBuffer, ( size_t ) xHeader.len, pdFALSE );
			pucPacketData = ucRecvBuffer;
			pxHeader = &xHeader;

			iptraceNETWORK_INTERFACE_RECEIVE();

			/* Check for minimal size. */
			if( pxHeader->len >= sizeof( EthernetHeader_t ) )
			{
				eResult = ipCONSIDER_FRAME_FOR_PROCESSING( pucPacketData );
			}
			else
			{
				eResult = eReleaseBuffer;
			}

			if( eResult == eProcessBuffer )
			{
				/* Will the data fit into the frame buffer? */
				if( pxHeader->len <= ipTOTAL_ETHERNET_FRAME_SIZE )
				{
					/* Obtain a buffer into which the data can be placed.  This
					is only	an interrupt simulator, not a real interrupt, so it
					is ok to call the task level function here, but note that
					some buffer implementations cannot be called from a real
					interrupt. */
					pxNetworkBuffer = pxGetNetworkBufferWithDescriptor( pxHeader->len, 0 );

					if( pxNetworkBuffer != NULL )
					{
						memcpy( pxNetworkBuffer->pucEthernetBuffer, pucPacketData, pxHeader->len );
						pxNetworkBuffer->xDataLength = ( size_t ) pxHeader->len;

						#if ( niDISRUPT_PACKETS == 1 )
						{
							pxNetworkBuffer = vRxFaultInjection( pxNetworkBuffer, pucPacketData );
						}
						#endif /* niDISRUPT_PACKETS */

						if( pxNetworkBuffer != NULL )
						{
							xRxEvent.pvData = ( void * ) pxNetworkBuffer;

							/* Data was received and stored.  Send a message to
							the IP task to let it know. */
							if( xSendEventStructToIPTask( &xRxEvent, ( TickType_t ) 0 ) == pdFAIL )
							{
								/* The buffer could not be sent to the stack so
								must be released again.  This is only an
								interrupt simulator, not a real interrupt, so it
								is ok to use the task level function here, but
								note no all buffer implementations will allow
								this function to be executed from a real
								interrupt. */
								vReleaseNetworkBufferAndDescriptor( pxNetworkBuffer );
								iptraceETHERNET_RX_EVENT_LOST();
							}
						}
						else
						{
							/* The packet was already released or stored inside
							vRxFaultInjection().  Don't release it here. */
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
					overflowed the buffer, but there may be more buffers to
					process. */
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

/*!
 * @brief remove spacces from pcMessage into pcBuffer
 * @param [out] pcBuffer buffer to fill up
 * @param [in] aBuflen length of pcBuffer
 * @param [in] pcMessage original message
 * @returns
 */
static const char * prvRemoveSpaces( char *pcBuffer,
									 int aBuflen,
									 const char *pcMessage )
{
char *pcTarget = pcBuffer;

	/* Utility function used to formap messages being printed only. */
	while( ( *pcMessage != 0 ) && ( pcTarget < ( &pcBuffer[ aBuflen - 1 ] ) ) )
	{
		*( pcTarget++ ) = *pcMessage;

		if( isspace( *pcMessage ) != pdFALSE )
		{
			while( isspace( *pcMessage ) != pdFALSE )
			{
				pcMessage++;
			}
		}
		else
		{
			pcMessage++;
		}
	}

	*pcTarget = '\0';

	return pcBuffer;
}

/*!
 * @brief print binary packet in hex
 * @param [in] bin_daa data to print
 * @param [in] len length of the data
 */
static void print_hex( unsigned const char * const bin_data,
					   size_t len )
/*static void print_hex(unsigned char *bin_data, size_t len) */
{
size_t i;

	for( i = 0; i < len; ++i )
	{
		FreeRTOS_debug_printf( ( "%.2X ", bin_data[ i ] ) );
	}

	FreeRTOS_debug_printf( ( "\n" ) );
}
