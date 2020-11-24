/*
    FreeRTOS V7.3.0 - Copyright (C) 2012 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT 
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!
    
    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest versions, license 
    and contact details.  
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

/* WinPCap includes. */
#include "pcap.h"
#include "remote-ext.h"

/* uIP includes. */
#include "net/uip.h"
#include "net/uip_arp.h"
#include "net/clock-arch.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/*
 * Query the computer the simulation is being executed on to find the network
 * interfaces it has installed.
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

pcap_t *pxOpenedInterfaceHandle = NULL;
LARGE_INTEGER freq, sys_start_time;

#define archNUM_BUFFERS	5
#define archNUM_BUFFER_POINTERS ( archNUM_BUFFERS - 1 )

static void prvInterruptSimulator( void *pvParameters );

static unsigned char ucEthernetBuffer[ archNUM_BUFFERS ][ UIP_CONF_BUFFER_SIZE ];
static unsigned char *pucEthernetBufferPointers[ archNUM_BUFFER_POINTERS ];

static long lLengthOfDataInBuffer[ archNUM_BUFFER_POINTERS ] = { 0 };
static unsigned char ucNextBufferToFill = 0U, ucNextBufferToProcess = 0U;

unsigned char *uip_buf = NULL;
char cErrorBuffer[PCAP_ERRBUF_SIZE];

void vNetifTx( void )
{
	pcap_sendpacket( pxOpenedInterfaceHandle, uip_buf, uip_len );
	pcap_sendpacket( pxOpenedInterfaceHandle, uip_buf, uip_len );
}
/*-----------------------------------------------------------*/

unsigned portBASE_TYPE uxNetifRx( void )
{
unsigned portBASE_TYPE xDataLen;
unsigned char *pucTemp;

	/* Check there is really data available. */
	xDataLen = lLengthOfDataInBuffer[ ucNextBufferToProcess ];
	if( xDataLen != 0L )
	{

		/* The buffer pointed to by uip_buf is going to change.  Remember which
		buffer uip_buf is currently pointing to. */
		pucTemp = uip_buf;

		/* Point uip_buf at the next buffer that contains data. */
		uip_buf = pucEthernetBufferPointers[ ucNextBufferToProcess ];

		/* The buffer pointed to by 
		pucEthernetBufferPointeres[ ucNextBufferToProcess ] is now in use by
		uip_buf, but the buffer uip_buf was pointing to on entry to this
		function is free.  Set 
		pucEthernetBufferPointeres[ ucNextBufferToProcess ] to the free 
		buffer. */
		pucEthernetBufferPointers[ ucNextBufferToProcess ] = pucTemp;
		lLengthOfDataInBuffer[ ucNextBufferToProcess ] = 0L;

		ucNextBufferToProcess++;
		if( ucNextBufferToProcess >= archNUM_BUFFER_POINTERS )
		{
			ucNextBufferToProcess = 0L;
		}
	}

	return xDataLen;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xNetifInit( void )
{
portBASE_TYPE x;
pcap_if_t *pxAllNetworkInterfaces;

	/* Allocate a free buffer to each buffer pointer. */
	for( x = 0; x < sizeof( pucEthernetBufferPointers ) / sizeof( unsigned char * ); x++ )
	{
		pucEthernetBufferPointers[ x ] = &( ucEthernetBuffer[ x ][ 0 ] );
	}

	/* Start with uip_buf pointing to a buffer that is not referenced from the
	pucEthernetBufferPointers[] array. */
	uip_buf = &( ucEthernetBuffer[ archNUM_BUFFERS - 1 ][ 0 ] );

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
	

	return x;
}
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
											UIP_CONF_BUFFER_SIZE, 		/* The size of the packet to capture. */
											PCAP_OPENFLAG_PROMISCUOUS,	/* Open in promiscious mode as the MAC and 
																		IP address is going to be "simulated", and 
																		not be the real MAC and IP address.  This allows
																		trafic to the simulated IP address to be routed
																		to uIP, and trafic to the real IP address to be
																		routed to the Windows TCP/IP stack. */
											0xfffffffL,             	/* The read time out.  This is going to block
																		until data is available. */
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
const long lMinBytesToCopy = 10L, lBlocking = 0L;
unsigned long ulNetMask;

	/* Unblock a read as soon as anything is received. */
	pcap_setmintocopy( pxOpenedInterfaceHandle, lMinBytesToCopy );

	/* Allow blocking. */
	pcap_setnonblock( pxOpenedInterfaceHandle, lBlocking, cErrorBuffer );

	/* Set up a filter so only the packets of interest are passed to the uIP
	stack.  cErrorBuffer is used for convenience to create the string.  Don't
	confuse this with an error message. */
	sprintf( cErrorBuffer, "broadcast or multicast or host %d.%d.%d.%d", configIP_ADDR0, configIP_ADDR1, configIP_ADDR2, configIP_ADDR3 );

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
	xTaskCreate( prvInterruptSimulator, ( signed char * ) "MAC_ISR", configMINIMAL_STACK_SIZE, NULL, ( configuIP_TASK_PRIORITY - 1 ), NULL );
}
/*-----------------------------------------------------------*/

static void prvInterruptSimulator( void *pvParameters )
{
static struct pcap_pkthdr *pxHeader;
const unsigned char *pucPacketData;
extern xQueueHandle xEMACEventQueue;
const unsigned long ulRxEvent = uipETHERNET_RX_EVENT;
long lResult;

	/* Just to kill the compiler warning. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Get the next packet. */
		lResult = pcap_next_ex( pxOpenedInterfaceHandle, &pxHeader, &pucPacketData );
		if( lResult )
		{
			/* Is the next buffer into which data should be placed free? */
			if( lLengthOfDataInBuffer[ ucNextBufferToFill ] == 0L )
			{
				/* Copy the data from the captured packet into the buffer. */
				memcpy( pucEthernetBufferPointers[ ucNextBufferToFill ], pucPacketData, pxHeader->len );

				/* Note the amount of data that was copied. */
				lLengthOfDataInBuffer[ ucNextBufferToFill ] = pxHeader->len;

				/* Move onto the next buffer, wrapping around if necessary. */
				ucNextBufferToFill++;
				if( ucNextBufferToFill >= archNUM_BUFFER_POINTERS )
				{
					ucNextBufferToFill = 0U;
				}

				/* Data was received and stored.  Send a message to the uIP task
				to let it know. */
				xQueueSendToBack( xEMACEventQueue, &ulRxEvent, portMAX_DELAY );
			}
		}
	}
}

