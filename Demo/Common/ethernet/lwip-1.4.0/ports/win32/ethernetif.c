/*
    FreeRTOS V7.0.1 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/

/* WinPCap includes. */
#define HAVE_REMOTE
#include "pcap.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* lwIP includes. */
#include "lwip/opt.h"
#include "lwip/def.h"
#include "lwip/mem.h"
#include "lwip/pbuf.h"
#include "lwip/sys.h"
#include <lwip/stats.h>
#include <lwip/snmp.h>
#include "netif/etharp.h"
#include "netif/ppp_oe.h"

/* Define those to better describe your network interface. */
#define IFNAME0 'w'
#define IFNAME1 'p'

#define netifMAX_MTU 1500

struct ethernetif 
{
	struct eth_addr *ethaddr;
	/* Add whatever per-interface state that is needed here. */
};

/* Forward declarations. */
static void ethernetif_input( const unsigned char * const pucInputData, long lLength );
static struct pbuf *low_level_input( const unsigned char * const pucInputData, long lDataLength );

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
 * Interrupts cannot truely be simulated using WinPCap.  In reality this task
 * just polls the interface. 
 */
static void prvInterruptSimulator( void *pvParameters );
/*
 * Configure the capture filter to allow blocking reads, and to filter out
 * packets that are not of interest to this demo.
 */
static void prvConfigureCaptureBehaviour( void );

/* The WinPCap interface being used. */
static pcap_t *pxOpenedInterfaceHandle = NULL;

/* Parameter required for WinPCap API functions. */
static char cErrorBuffer[ PCAP_ERRBUF_SIZE ];

/* The network interface that was opened. */
static struct netif *xlwIPNetif = NULL;

/**
 * In this function, the hardware should be initialized.
 * Called from ethernetif_init().
 *
 * @param netif the already initialized lwip network interface structure
 *        for this ethernetif
 */
static void low_level_init(struct netif *netif)
{
pcap_if_t *pxAllNetworkInterfaces;
  
	/* set MAC hardware address length */
	netif->hwaddr_len = ETHARP_HWADDR_LEN;

	/* set MAC hardware address */
	netif->hwaddr[ 0 ] = configMAC_ADDR0;
	netif->hwaddr[ 1 ] = configMAC_ADDR1;
	netif->hwaddr[ 2 ] = configMAC_ADDR2;
	netif->hwaddr[ 3 ] = configMAC_ADDR3;
	netif->hwaddr[ 4 ] = configMAC_ADDR4;
	netif->hwaddr[ 5 ] = configMAC_ADDR5;

	/* device capabilities */
	/* don't set NETIF_FLAG_ETHARP if this device is not an ethernet one */
	netif->flags = NETIF_FLAG_BROADCAST | NETIF_FLAG_ETHARP | NETIF_FLAG_LINK_UP;
 
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

	/* Remember which interface was opened as it is used in the interrupt 
	simulator task. */
	xlwIPNetif = netif;
}

/**
 * This function should do the actual transmission of the packet. The packet is
 * contained in the pbuf that is passed to the function. This pbuf
 * might be chained.
 *
 * @param netif the lwip network interface structure for this ethernetif
 * @param p the MAC packet to send (e.g. IP packet including MAC addresses and type)
 * @return ERR_OK if the packet could be sent
 *         an err_t value if the packet couldn't be sent
 *
 * @note Returning ERR_MEM here if a DMA queue of your MAC is full can lead to
 *       strange results. You might consider waiting for space in the DMA queue
 *       to become availale since the stack doesn't retry to send a packet
 *       dropped because of memory failure (except for the TCP timers).
 */

static err_t low_level_output(struct netif *netif, struct pbuf *p)
{

	/* This is taken from lwIP example code and therefore does not conform
	to the FreeRTOS coding standard. */

struct pbuf *q;
static unsigned char buffer[ 1520 ];
unsigned char *buf = buffer;
unsigned char *ptr;
struct eth_hdr *ethhdr;
u16_t tot_len = p->tot_len - ETH_PAD_SIZE;

	#if defined(LWIP_DEBUG) && LWIP_NETIF_TX_SINGLE_PBUF
	  LWIP_ASSERT("p->next == NULL && p->len == p->tot_len", p->next == NULL && p->len == p->tot_len);
	#endif

	/* initiate transfer */
	if (p->len == p->tot_len) 
	{
		/* no pbuf chain, don't have to copy -> faster */
		buf = &((unsigned char*)p->payload)[ETH_PAD_SIZE];
	} 
	else 
	{
		/* pbuf chain, copy into contiguous buffer */
		if (p->tot_len >= sizeof(buffer)) 
		{
			LINK_STATS_INC(link.lenerr);
			LINK_STATS_INC(link.drop);
			snmp_inc_ifoutdiscards(netif);
			return ERR_BUF;
		}

		ptr = buffer;

		for( q = p; q != NULL; q = q->next ) 
		{
			/* Send the data from the pbuf to the interface, one pbuf at a
			time. The size of the data in each pbuf is kept in the ->len
			variable. */
			/* send data from(q->payload, q->len); */
			LWIP_DEBUGF(NETIF_DEBUG, ("netif: send ptr %p q->payload %p q->len %i q->next %p\n", ptr, q->payload, (int)q->len, (void*)q->next));
			if (q == p) 
			{
				memcpy(ptr, &((char*)q->payload)[ETH_PAD_SIZE], q->len - ETH_PAD_SIZE);
				ptr += q->len - ETH_PAD_SIZE;
			} 
			else 
			{
				memcpy(ptr, q->payload, q->len);
				ptr += q->len;
			}
		}
	}

	/* signal that packet should be sent */
	if( pcap_sendpacket( pxOpenedInterfaceHandle, buf, tot_len ) < 0 ) 
	{
		LINK_STATS_INC(link.memerr);
		LINK_STATS_INC(link.drop);
		snmp_inc_ifoutdiscards(netif);
		return ERR_BUF;
	}

	LINK_STATS_INC(link.xmit);
	snmp_add_ifoutoctets(netif, tot_len);
	ethhdr = (struct eth_hdr *)p->payload;

	if( ( ethhdr->dest.addr[ 0 ] & 1 ) != 0 ) 
	{
		/* broadcast or multicast packet*/
		snmp_inc_ifoutnucastpkts(netif);
	} 
	else 
	{
		/* unicast packet */
		snmp_inc_ifoutucastpkts( netif );
	}

	return ERR_OK;
}

/**
 * Should allocate a pbuf and transfer the bytes of the incoming
 * packet from the interface into the pbuf.
 *
 * @param netif the lwip network interface structure for this ethernetif
 * @return a pbuf filled with the received packet (including MAC header)
 *         NULL on memory error
 */
static struct pbuf *low_level_input( const unsigned char * const pucInputData, long lDataLength )
{
struct pbuf *p = NULL, *q;

	if( lDataLength > 0 )
	{
		#if ETH_PAD_SIZE
			len += ETH_PAD_SIZE; /* allow room for Ethernet padding */
		#endif

		/* We allocate a pbuf chain of pbufs from the pool. */
		p = pbuf_alloc( PBUF_RAW, lDataLength, PBUF_POOL );
  
		if( p != NULL ) 
		{
			#if ETH_PAD_SIZE
				pbuf_header(p, -ETH_PAD_SIZE); /* drop the padding word */
			#endif

			/* We iterate over the pbuf chain until we have read the entire
			* packet into the pbuf. */
			lDataLength = 0;
			for( q = p; q != NULL; q = q->next ) 
			{
				/* Read enough bytes to fill this pbuf in the chain. The
				* available data in the pbuf is given by the q->len
				* variable.
				* This does not necessarily have to be a memcpy, you can also preallocate
				* pbufs for a DMA-enabled MAC and after receiving truncate it to the
				* actually received size. In this case, ensure the tot_len member of the
				* pbuf is the sum of the chained pbuf len members.
				*/
				memcpy( q->payload, &( pucInputData[ lDataLength ] ), q->len );
				lDataLength += q->len;
			}

			#if ETH_PAD_SIZE
				pbuf_header( p, ETH_PAD_SIZE ); /* reclaim the padding word */
			#endif

			LINK_STATS_INC(link.recv);
		}
	}

	return p;  
}

/**
 * This function should be called when a packet is ready to be read
 * from the interface. It uses the function low_level_input() that
 * should handle the actual reception of bytes from the network
 * interface. Then the type of the received packet is determined and
 * the appropriate input function is called.
 *
 * @param netif the lwip network interface structure for this ethernetif
 */
static void ethernetif_input( const unsigned char * const pucInputData, long lInputLength )
{
	/* This is taken from lwIP example code and therefore does not conform
	to the FreeRTOS coding standard. */
	
struct eth_hdr *ethhdr;
struct pbuf *p;

	/* move received packet into a new pbuf */
	p = low_level_input( pucInputData, lInputLength );
	/* no packet could be read, silently ignore this */
	if( p == NULL ) 
	{
		return;
	}

	/* points to packet payload, which starts with an Ethernet header */
	ethhdr = p->payload;

	switch( htons( ethhdr->type ) ) 
	{
		/* IP or ARP packet? */
		case ETHTYPE_IP:
		case ETHTYPE_ARP:
							/* full packet send to tcpip_thread to process */
							if(xlwIPNetif->input( p, xlwIPNetif )!=ERR_OK )
							{ 
								LWIP_DEBUGF(NETIF_DEBUG, ("ethernetif_input: IP input error\n"));
								pbuf_free(p);
								p = NULL;
							}
							break;

		default:
							pbuf_free( p );
							p = NULL;
		break;
	}
}

/**
 * Should be called at the beginning of the program to set up the
 * network interface. It calls the function low_level_init() to do the
 * actual setup of the hardware.
 *
 * This function should be passed as a parameter to netif_add().
 *
 * @param netif the lwip network interface structure for this ethernetif
 * @return ERR_OK if the loopif is initialized
 *         ERR_MEM if private data couldn't be allocated
 *         any other err_t on error
 */
err_t ethernetif_init( struct netif *netif )
{
	/* This is taken from lwIP example code and therefore does not conform
	to the FreeRTOS coding standard. */
	
	struct ethernetif *ethernetif;

	LWIP_ASSERT( "netif != NULL", ( netif != NULL ) );
    
	ethernetif = mem_malloc( sizeof( struct ethernetif ) );
	if (ethernetif == NULL) 
	{
		LWIP_DEBUGF(NETIF_DEBUG, ("ethernetif_init: out of memory\n"));
		return ERR_MEM;
	}

	#if LWIP_NETIF_HOSTNAME
		/* Initialize interface hostname */
		netif->hostname = "lwip";
	#endif /* LWIP_NETIF_HOSTNAME */

	netif->state = ethernetif;
	netif->name[0] = IFNAME0;
	netif->name[1] = IFNAME1;

	/* We directly use etharp_output() here to save a function call.
	* You can instead declare your own function an call etharp_output()
	* from it if you have to do some checks before sending (e.g. if link
	* is available...) */
	netif->output = etharp_output;
	netif->flags = NETIF_FLAG_BROADCAST | NETIF_FLAG_ETHARP | NETIF_FLAG_IGMP;
	netif->hwaddr_len = ETHARP_HWADDR_LEN;
	netif->mtu = netifMAX_MTU;
	netif->linkoutput = low_level_output;

	ethernetif->ethaddr = ( struct eth_addr * ) &( netif->hwaddr[ 0 ] );
  
	/* initialize the hardware */
	low_level_init( netif );

	return ERR_OK;
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
											netifMAX_MTU, 				/* The size of the packet to capture. */
											PCAP_OPENFLAG_PROMISCUOUS,	/* Open in promiscious mode as the MAC and 
																		IP address is going to be "simulated", and 
																		not be the real MAC and IP address.  This allows
																		trafic to the simulated IP address to be routed
																		to uIP, and trafic to the real IP address to be
																		routed to the Windows TCP/IP stack. */
											0L,             			/* The read time out.  This is going to block
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

static void prvInterruptSimulator( void *pvParameters )
{
static struct pcap_pkthdr *pxHeader;
const unsigned char *pucPacketData;
extern xQueueHandle xEMACEventQueue;
long lResult;

	/* Just to kill the compiler warning. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Get the next packet. */
		lResult = pcap_next_ex( pxOpenedInterfaceHandle, &pxHeader, &pucPacketData );
		if( lResult == 1 )
		{
			if( xlwIPNetif != NULL )
			{
				ethernetif_input( pucPacketData, pxHeader->len );
			}
		}
		else
		{
			/* There is no real way of simulating an interrupt.  
			Make sure other tasks can run. */
			vTaskDelay( 5 );
		}
	}
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

	/* Set up a filter so only the packets of interest are passed to the lwIP
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
	xTaskCreate( prvInterruptSimulator, ( signed char * ) "MAC_ISR", configMINIMAL_STACK_SIZE, NULL, configMAC_ISR_SIMULATOR_PRIORITY, NULL );
}

