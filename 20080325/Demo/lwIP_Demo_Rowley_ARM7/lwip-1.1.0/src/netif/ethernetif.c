/*
 * Copyright (c) 2001-2004 Swedish Institute of Computer Science.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT
 * SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
 * OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
 * OF SUCH DAMAGE.
 *
 * This file is part of the lwIP TCP/IP stack.
 *
 * Author: Adam Dunkels <adam@sics.se>
 *
 */

/* lwIP includes. */
#include <string.h>
#include "lwip/opt.h"
#include "lwip/def.h"
#include "lwip/mem.h"
#include "lwip/pbuf.h"
#include "lwip/sys.h"
#include <lwip/stats.h>
#include "netif/etharp.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "SAM7_EMAC.h"
#include "Emac.h"

#define netifMTU							( 1500 )
#define netifINTERFACE_TASK_STACK_SIZE		( 350 )
#define netifINTERFACE_TASK_PRIORITY		( configMAX_PRIORITIES - 1 )
#define netifGUARD_BLOCK_TIME				( 250 )
#define IFNAME0 'e'
#define IFNAME1 'm'

/* lwIP definitions. */
struct ethernetif
{
	struct eth_addr *ethaddr;
};
static const struct eth_addr    ethbroadcast = { { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff } };
static struct netif *xNetIf = NULL;

/* Forward declarations. */
static void ethernetif_input( void * );
static err_t ethernetif_output( struct netif *netif, struct pbuf *p, struct ip_addr *ipaddr );
err_t ethernetif_init( struct netif *netif );


/*-----------------------------------------------------------*/

static void low_level_init( struct netif *netif )
{
unsigned portBASE_TYPE uxPriority;

	/* set MAC hardware address length */
	netif->hwaddr_len = 6;

	/* set MAC hardware address */
	netif->hwaddr[0] = emacETHADDR0;
	netif->hwaddr[1] = emacETHADDR1;
	netif->hwaddr[2] = emacETHADDR2;
	netif->hwaddr[3] = emacETHADDR3;
	netif->hwaddr[4] = emacETHADDR4;
	netif->hwaddr[5] = emacETHADDR5;

	/* maximum transfer unit */
	netif->mtu = netifMTU;

	/* broadcast capability */
	netif->flags = NETIF_FLAG_BROADCAST;

	xNetIf = netif;

	/* Initialise the EMAC.  This routine contains code that polls status bits.  
	If the Ethernet cable is not plugged in then this can take a considerable 
	time.  To prevent this starving lower priority tasks of processing time we
	lower our priority prior to the call, then raise it back again once the
	initialisation is complete. */
	uxPriority = uxTaskPriorityGet( NULL );
	vTaskPrioritySet( NULL, tskIDLE_PRIORITY );
	while( xEMACInit() == NULL )
	{
		__asm( "NOP" );
	}
	vTaskPrioritySet( NULL, uxPriority );

	/* Create the task that handles the EMAC. */
	xTaskCreate( ethernetif_input, ( signed portCHAR * ) "ETH_INT", netifINTERFACE_TASK_STACK_SIZE, NULL, netifINTERFACE_TASK_PRIORITY, NULL );
}
/*-----------------------------------------------------------*/

/*
 * low_level_output(): Should do the actual transmission of the packet. The 
 * packet is contained in the pbuf that is passed to the function. This pbuf 
 * might be chained.
 */
static err_t low_level_output( struct netif *netif, struct pbuf *p )
{
struct pbuf *q;
static xSemaphoreHandle xTxSemaphore = NULL;
err_t xReturn = ERR_OK;

	/* Parameter not used. */
	( void ) netif;

	if( xTxSemaphore == NULL )
	{
		vSemaphoreCreateBinary( xTxSemaphore );
	}

	#if ETH_PAD_SIZE
		pbuf_header( p, -ETH_PAD_SIZE );    /* drop the padding word */
	#endif

	/* Access to the EMAC is guarded using a semaphore. */
	if( xSemaphoreTake( xTxSemaphore, netifGUARD_BLOCK_TIME ) )
	{
		for( q = p; q != NULL; q = q->next )
		{
			/* Send the data from the pbuf to the interface, one pbuf at a 
			time. The size of the data in each pbuf is kept in the ->len 
			variable.  if q->next == NULL then this is the last pbuf in the
			chain. */
			if( !lEMACSend( q->payload, q->len, ( q->next == NULL ) ) )
			{
				xReturn = ~ERR_OK;
			}
		}

        xSemaphoreGive( xTxSemaphore );
	}
	

	#if ETH_PAD_SIZE
		pbuf_header( p, ETH_PAD_SIZE );     /* reclaim the padding word */
	#endif

	#if LINK_STATS
		lwip_stats.link.xmit++;
	#endif /* LINK_STATS */

    return xReturn;
}
/*-----------------------------------------------------------*/

/*
 * low_level_input(): Should allocate a pbuf and transfer the bytes of the 
 * incoming packet from the interface into the pbuf. 
 */
static struct pbuf *low_level_input( struct netif *netif )
{
struct pbuf         *p = NULL, *q;
u16_t               len = 0;
static xSemaphoreHandle xRxSemaphore = NULL;

	/* Parameter not used. */
	( void ) netif;

	if( xRxSemaphore == NULL )
	{
		vSemaphoreCreateBinary( xRxSemaphore );
	}

	/* Access to the emac is guarded using a semaphore. */
   	if( xSemaphoreTake( xRxSemaphore, netifGUARD_BLOCK_TIME ) )
	{
		/* Obtain the size of the packet. */
		len = ulEMACInputLength();
	
		if( len )
		{
			#if ETH_PAD_SIZE
				len += ETH_PAD_SIZE;    /* allow room for Ethernet padding */
			#endif
	
			/* We allocate a pbuf chain of pbufs from the pool. */
			p = pbuf_alloc( PBUF_RAW, len, PBUF_POOL );
		
			if( p != NULL )
			{
				#if ETH_PAD_SIZE
					pbuf_header( p, -ETH_PAD_SIZE );    /* drop the padding word */
				#endif
		
				/* Let the driver know we are going to read a new packet. */
				vEMACRead( NULL, 0, len );
					
				/* We iterate over the pbuf chain until we have read the entire
				packet into the pbuf. */				
				for( q = p; q != NULL; q = q->next )
				{
					/* Read enough bytes to fill this pbuf in the chain. The 
					available data in the pbuf is given by the q->len variable. */
					vEMACRead( q->payload, q->len, len );
				}
		
				#if ETH_PAD_SIZE
					pbuf_header( p, ETH_PAD_SIZE );     /* reclaim the padding word */
				#endif
				#if LINK_STATS
					lwip_stats.link.recv++;
				#endif /* LINK_STATS */
			}
			else
			{
				#if LINK_STATS
					lwip_stats.link.memerr++;
					lwip_stats.link.drop++;
				#endif /* LINK_STATS */
			}
		}

		xSemaphoreGive( xRxSemaphore );
	}

	return p;
}
/*-----------------------------------------------------------*/

/*
 * ethernetif_output(): This function is called by the TCP/IP stack when an 
 * IP packet should be sent. It calls the function called low_level_output() 
 * to do the actual transmission of the packet.
 */
static err_t ethernetif_output( struct netif *netif, struct pbuf *p, struct ip_addr *ipaddr )
{
    /* resolve hardware address, then send (or queue) packet */
    return etharp_output( netif, ipaddr, p );
}
/*-----------------------------------------------------------*/

/*
 * ethernetif_input(): This function should be called when a packet is ready to 
 * be read from the interface. It uses the function low_level_input() that 
 * should handle the actual reception of bytes from the network interface.
 */
static void ethernetif_input( void * pvParameters )
{
struct ethernetif   *ethernetif;
struct eth_hdr      *ethhdr;
struct pbuf         *p;

	( void ) pvParameters;

	for( ;; )
	{
		do
		{
			ethernetif = xNetIf->state;

			/* move received packet into a new pbuf */
			p = low_level_input( xNetIf );

			if( p == NULL )
			{
				/* No packet could be read.  Wait a for an interrupt to tell us 
				there is more data available. */
				vEMACWaitForInput();
			}

		} while( p == NULL );
	
		/* points to packet payload, which starts with an Ethernet header */
		ethhdr = p->payload;
	
		#if LINK_STATS
			lwip_stats.link.recv++;
		#endif /* LINK_STATS */
	
		ethhdr = p->payload;
	
		switch( htons( ethhdr->type ) )
		{
			/* IP packet? */
			case ETHTYPE_IP:
				/* update ARP table */
				etharp_ip_input( xNetIf, p );
		
				/* skip Ethernet header */
				pbuf_header( p, (s16_t)-sizeof(struct eth_hdr) );
		
				/* pass to network layer */
				xNetIf->input( p, xNetIf );
				break;
		
			case ETHTYPE_ARP:
				/* pass p to ARP module */
				etharp_arp_input( xNetIf, ethernetif->ethaddr, p );
				break;
		
			default:
				pbuf_free( p );
				p = NULL;
				break;
		}
	}
}
/*-----------------------------------------------------------*/

static void arp_timer( void *arg )
{
	( void ) arg;

    etharp_tmr();
    sys_timeout( ARP_TMR_INTERVAL, arp_timer, NULL );
}
/*-----------------------------------------------------------*/

err_t ethernetif_init( struct netif *netif )
{
struct ethernetif   *ethernetif;

	ethernetif = mem_malloc( sizeof(struct ethernetif) );

	if( ethernetif == NULL )
	{
		LWIP_DEBUGF( NETIF_DEBUG, ("ethernetif_init: out of memory\n") );
		return ERR_MEM;
	}

	netif->state = ethernetif;
	netif->name[0] = IFNAME0;
	netif->name[1] = IFNAME1;
	netif->output = ethernetif_output;
	netif->linkoutput = low_level_output;

	ethernetif->ethaddr = ( struct eth_addr * ) &( netif->hwaddr[0] );

	low_level_init( netif );
	etharp_init();
	sys_timeout( ARP_TMR_INTERVAL, arp_timer, NULL );

	return ERR_OK;
}
