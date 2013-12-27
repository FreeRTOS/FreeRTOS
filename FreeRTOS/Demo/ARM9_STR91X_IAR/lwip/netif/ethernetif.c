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

/*
 * This file is a skeleton for developing Ethernet network interface
 * drivers for lwIP. Add code to the low_level functions and do a
 * search-and-replace for the word "ethernetif" to replace it with
 * something that better describes your network interface.
 */

#include "lwip/opt.h"
#include "lwip/def.h"
#include "lwip/mem.h"
#include "lwip/pbuf.h"
#include "lwip/sys.h"
#include <lwip/stats.h>

#include "netif/etharp.h"
#include "91x_enet.h"

// Standard library include
#include <string.h>

#define netifMTU				( 1500 )
#define netifINTERFACE_TASK_STACK_SIZE		( 350 )
#define netifINTERFACE_TASK_PRIORITY		( configMAX_PRIORITIES - 1 )
#define netifGUARD_BLOCK_TIME			( 250 )
#define IFNAME0 'e'
#define IFNAME1 'm'

/* The time to block waiting for input. */
#define emacBLOCK_TIME_WAITING_FOR_INPUT	( ( portTickType ) 100 )

/* Interrupt status bit definition. */
#define DMI_RX_CURRENT_DONE 0x8000

extern u8 TxBuff[1520];

static u8_t s_rxBuff[1520];

/* The semaphore used by the ISR to wake the lwIP task. */
static xSemaphoreHandle s_xSemaphore = NULL;

struct ethernetif {
  struct eth_addr *ethaddr;
  /* Add whatever per-interface state that is needed here. */
};

static struct netif *s_pxNetIf = NULL;

/* Forward declarations. */
static err_t ethernetif_output(struct netif *netif, struct pbuf *p, struct ip_addr *ipaddr);
static void ethernetif_input( void * pvParameters );
static void vEMACWaitForInput( void );



static void low_level_init(struct netif *netif)
{
  /* set MAC hardware address length */
  netif->hwaddr_len = 6;

  /* set MAC hardware address */
  netif->hwaddr[0] = MAC_ADDR0;
  netif->hwaddr[1] = MAC_ADDR1;
  netif->hwaddr[2] = MAC_ADDR2;
  netif->hwaddr[3] = MAC_ADDR3;
  netif->hwaddr[4] = MAC_ADDR4;
  netif->hwaddr[5] = MAC_ADDR5;

  /* maximum transfer unit */
  netif->mtu = netifMTU;

  /* broadcast capability */
  netif->flags = NETIF_FLAG_BROADCAST;

  s_pxNetIf = netif;

  if( s_xSemaphore == NULL )
  {
      vSemaphoreCreateBinary( s_xSemaphore );
      xSemaphoreTake( s_xSemaphore,  0);
  }

  /* Do whatever else is needed to initialize interface. */
  /* Initialise the MAC. */
  ENET_InitClocksGPIO();
  ENET_Init();
  ENET_Start();

  portENTER_CRITICAL();
  {
      /*set MAC physical*/
      ENET_MAC->MAH = (MAC_ADDR5<<8) + MAC_ADDR4;
      ENET_MAC->MAL = (MAC_ADDR3<<24) + (MAC_ADDR2<<16) + (MAC_ADDR1<<8) + MAC_ADDR0;

      VIC_Config( ENET_ITLine, VIC_IRQ, 1 );
      VIC_ITCmd( ENET_ITLine, ENABLE );
      ENET_DMA->ISR = DMI_RX_CURRENT_DONE;
      ENET_DMA->IER = DMI_RX_CURRENT_DONE;
  }
  portEXIT_CRITICAL();

  /* Create the task that handles the EMAC. */
  xTaskCreate( ethernetif_input, "ETH_INT", netifINTERFACE_TASK_STACK_SIZE, NULL, netifINTERFACE_TASK_PRIORITY, NULL );
}


/*
 * low_level_output():
 *
 * Should do the actual transmission of the packet. The packet is
 * contained in the pbuf that is passed to the function. This pbuf
 * might be chained.
 *
 */

static err_t low_level_output(struct netif *netif, struct pbuf *p)
{
  static xSemaphoreHandle xTxSemaphore = NULL;
  struct pbuf *q;
  u32_t l = 0;

  if( xTxSemaphore == NULL )
  {
      vSemaphoreCreateBinary( xTxSemaphore );
  }


#if ETH_PAD_SIZE
  pbuf_header(p, -ETH_PAD_SIZE);			/* drop the padding word */
#endif


  /* Access to the EMAC is guarded using a semaphore. */
  if( xSemaphoreTake( xTxSemaphore, netifGUARD_BLOCK_TIME ) )
  {
      for(q = p; q != NULL; q = q->next) {
        /* Send the data from the pbuf to the interface, one pbuf at a
           time. The size of the data in each pbuf is kept in the ->len
           variable. */
        memcpy(&TxBuff[l], (u8_t*)q->payload, q->len);
        l += q->len;
      }

      ENET_TxPkt(0, l);

      #if ETH_PAD_SIZE
        pbuf_header(p, ETH_PAD_SIZE);			/* reclaim the padding word */
      #endif

      #if LINK_STATS
        lwip_stats.link.xmit++;
      #endif /* LINK_STATS */

      xSemaphoreGive( xTxSemaphore );
  }

  return ERR_OK;
}

/*
 * low_level_input():
 *
 * Should allocate a pbuf and transfer the bytes of the incoming
 * packet from the interface into the pbuf.
 *
 */

static struct pbuf *
low_level_input(struct netif *netif)
{
  static xSemaphoreHandle xRxSemaphore = NULL;
  struct pbuf *p, *q;
  u16_t len, l;

  l = 0;
  p = NULL;

  if( xRxSemaphore == NULL )
  {
    vSemaphoreCreateBinary( xRxSemaphore );
  }

  /* Access to the emac is guarded using a semaphore. */
  if( xSemaphoreTake( xRxSemaphore, netifGUARD_BLOCK_TIME ) )
  {
        /* Obtain the size of the packet and put it into the "len"
           variable. */
        len = ENET_HandleRxPkt(s_rxBuff);

        if(len)
        {
              #if ETH_PAD_SIZE
                len += ETH_PAD_SIZE;						/* allow room for Ethernet padding */
              #endif

                /* We allocate a pbuf chain of pbufs from the pool. */
                p = pbuf_alloc(PBUF_RAW, len, PBUF_POOL);

                if (p != NULL) {

              #if ETH_PAD_SIZE
                  pbuf_header(p, -ETH_PAD_SIZE);			/* drop the padding word */
              #endif

                  /* We iterate over the pbuf chain until we have read the entire
                   * packet into the pbuf. */
                  for(q = p; q != NULL; q = q->next) {
                    /* Read enough bytes to fill this pbuf in the chain. The
                     * available data in the pbuf is given by the q->len
                     * variable. */
                    memcpy((u8_t*)q->payload, &s_rxBuff[l], q->len);
                    l = l + q->len;
                  }


              #if ETH_PAD_SIZE
                  pbuf_header(p, ETH_PAD_SIZE);			/* reclaim the padding word */
              #endif

              #if LINK_STATS
                  lwip_stats.link.recv++;
              #endif /* LINK_STATS */
                } else {
              #if LINK_STATS
                  lwip_stats.link.memerr++;
                  lwip_stats.link.drop++;
              #endif /* LINK_STATS */
                } /* End else */
        } /* End if */

       xSemaphoreGive( xRxSemaphore );
  }

  return p;
}

/*
 * ethernetif_output():
 *
 * This function is called by the TCP/IP stack when an IP packet
 * should be sent. It calls the function called low_level_output() to
 * do the actual transmission of the packet.
 *
 */

static err_t ethernetif_output(struct netif *netif, struct pbuf *p,  struct ip_addr *ipaddr)
{

 /* resolve hardware address, then send (or queue) packet */
  return etharp_output(netif, ipaddr, p);

}

/*
 * ethernetif_input():
 *
 * This function should be called when a packet is ready to be read
 * from the interface. It uses the function low_level_input() that
 * should handle the actual reception of bytes from the network
 * interface.
 *
 */

static void ethernetif_input( void * pvParameters )
{
  struct ethernetif *ethernetif;
  struct eth_hdr *ethhdr;
  struct pbuf *p;

	for( ;; )
	{
		do
		{
			ethernetif = s_pxNetIf->state;

			/* move received packet into a new pbuf */
			p = low_level_input( s_pxNetIf );

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

		switch (htons(ethhdr->type))
		{
			/* IP packet? */
			case ETHTYPE_IP:
				/* update ARP table */
				etharp_ip_input(s_pxNetIf, p);
				/* skip Ethernet header */
				pbuf_header(p, (s16_t)-sizeof(struct eth_hdr));
				/* pass to network layer */
				s_pxNetIf->input(p, s_pxNetIf);
				break;

			case ETHTYPE_ARP:
				  /* pass p to ARP module  */
				  etharp_arp_input(s_pxNetIf, ethernetif->ethaddr, p);
				  break;

			default:
				  pbuf_free(p);
				  p = NULL;
				  break;
		}
	}
}

static void
arp_timer(void *arg)
{
  etharp_tmr();
  sys_timeout(ARP_TMR_INTERVAL, arp_timer, NULL);
}

/*
 * ethernetif_init():
 *
 * Should be called at the beginning of the program to set up the
 * network interface. It calls the function low_level_init() to do the
 * actual setup of the hardware.
 *
 */

err_t
ethernetif_init(struct netif *netif)
{
  struct ethernetif *ethernetif;

  ethernetif = mem_malloc(sizeof(struct ethernetif));

  if (ethernetif == NULL)
  {
  	LWIP_DEBUGF(NETIF_DEBUG, ("ethernetif_init: out of memory\n"));
  	return ERR_MEM;
  }

#if LWIP_SNMP
	/* ifType ethernetCsmacd(6) @see RFC1213 */
	netif->link_type = 6;
	/* your link speed here */
	netif->link_speed = ;
	netif->ts = 0;
	netif->ifinoctets = 0;
	netif->ifinucastpkts = 0;
	netif->ifinnucastpkts = 0;
	netif->ifindiscards = 0;
	netif->ifoutoctets = 0;
	netif->ifoutucastpkts = 0;
	netif->ifoutnucastpkts = 0;
	netif->ifoutdiscards = 0;
#endif

  netif->state = ethernetif;
  netif->name[0] = IFNAME0;
  netif->name[1] = IFNAME1;
  netif->output = ethernetif_output;
  netif->linkoutput = low_level_output;

  ethernetif->ethaddr = (struct eth_addr *)&(netif->hwaddr[0]);

  low_level_init(netif);

  etharp_init();

  sys_timeout(ARP_TMR_INTERVAL, arp_timer, NULL);

  return ERR_OK;
}
/*-----------------------------------------------------------*/

void ENET_IRQHandler(void)
{
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* Give the semaphore in case the lwIP task needs waking. */
	xSemaphoreGiveFromISR( s_xSemaphore, &xHigherPriorityTaskWoken );

	/* Clear the interrupt. */
	ENET_DMA->ISR = DMI_RX_CURRENT_DONE;

	/* Switch tasks if necessary. */
	portEND_SWITCHING_ISR( xHigherPriorityTaskWoken );
}
/*-----------------------------------------------------------*/

void vEMACWaitForInput( void )
{
	/* Just wait until we are signled from an ISR that data is available, or
	we simply time out. */
	xSemaphoreTake( s_xSemaphore, emacBLOCK_TIME_WAITING_FOR_INPUT );
}
