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
 * Copyright (c) 2007-2013 Xilinx, Inc.  All rights reserved.
 *
 * Xilinx, Inc.
 * XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION "AS IS" AS A
 * COURTESY TO YOU.  BY PROVIDING THIS DESIGN, CODE, OR INFORMATION AS
 * ONE POSSIBLE   IMPLEMENTATION OF THIS FEATURE, APPLICATION OR
 * STANDARD, XILINX IS MAKING NO REPRESENTATION THAT THIS IMPLEMENTATION
 * IS FREE FROM ANY CLAIMS OF INFRINGEMENT, AND YOU ARE RESPONSIBLE
 * FOR OBTAINING ANY RIGHTS YOU MAY REQUIRE FOR YOUR IMPLEMENTATION.
 * XILINX EXPRESSLY DISCLAIMS ANY WARRANTY WHATSOEVER WITH RESPECT TO
 * THE ADEQUACY OF THE IMPLEMENTATION, INCLUDING BUT NOT LIMITED TO
 * ANY WARRANTIES OR REPRESENTATIONS THAT THIS IMPLEMENTATION IS FREE
 * FROM CLAIMS OF INFRINGEMENT, IMPLIED WARRANTIES OF MERCHANTABILITY
 * AND FITNESS FOR A PARTICULAR PURPOSE.
 *
 */

#include "lwipopts.h"
#include "xlwipconfig.h"

#if !NO_SYS
	#include "FreeRTOS.h"
	#include "task.h"
#endif

#include <stdio.h>
#include <string.h>

#include "lwip/opt.h"
#include "lwip/def.h"
#include "lwip/mem.h"
#include "lwip/pbuf.h"
#include "lwip/sys.h"
#include "lwip/stats.h"
#include "lwip/timers.h"

#include "netif/etharp.h"
#include "netif/xadapter.h"
#include "netif/xemacliteif.h"
#include "xstatus.h"

#include "netif/xpqueue.h"

#include "xlwipconfig.h"
#include "xparameters.h"
#if XLWIP_CONFIG_INCLUDE_EMACLITE_ON_ZYNQ == 1
#include "xscugic.h"
#define INTC_DIST_BASE_ADDR	XPAR_SCUGIC_DIST_BASEADDR
#else
#include "xintc.h"
#endif

/* Define those to better describe your network interface. */
#define IFNAME0 'x'
#define IFNAME1 'e'


/* Advertisement control register. */
#define ADVERTISE_10HALF        0x0020  /* Try for 10mbps half-duplex  */
#define ADVERTISE_1000XFULL     0x0020  /* Try for 1000BASE-X full-duplex */
#define ADVERTISE_10FULL        0x0040  /* Try for 10mbps full-duplex  */
#define ADVERTISE_1000XHALF     0x0040  /* Try for 1000BASE-X half-duplex */
#define ADVERTISE_100HALF       0x0080  /* Try for 100mbps half-duplex */
#define ADVERTISE_1000XPAUSE    0x0080  /* Try for 1000BASE-X pause    */
#define ADVERTISE_100FULL       0x0100  /* Try for 100mbps full-duplex */
#define ADVERTISE_1000XPSE_ASYM 0x0100  /* Try for 1000BASE-X asym pause */
#define ADVERTISE_100BASE4      0x0200  /* Try for 100mbps 4k packets  */


#define ADVERTISE_100_AND_10	(ADVERTISE_10FULL | ADVERTISE_100FULL |  \
				ADVERTISE_10HALF | ADVERTISE_100HALF)
#define ADVERTISE_100		(ADVERTISE_100FULL | ADVERTISE_100HALF)
#define ADVERTISE_10		(ADVERTISE_10FULL | ADVERTISE_10HALF)

#if XLWIP_CONFIG_INCLUDE_EMACLITE_ON_ZYNQ == 1
#define EMACLITE_INTR_PRIORITY_SET_IN_GIC	0xA0
#define TRIG_TYPE_RISING_EDGE_SENSITIVE		0x3
#endif

#define IEEE_CONTROL_REG_OFFSET			0
#define IEEE_STATUS_REG_OFFSET			1
#define IEEE_AUTONEGO_ADVERTISE_REG		4
#define IEEE_PARTNER_ABILITIES_1_REG_OFFSET	5
#define IEEE_PARTNER_ABILITIES_2_REG_OFFSET	8
#define IEEE_PARTNER_ABILITIES_3_REG_OFFSET	10
#define IEEE_1000_ADVERTISE_REG_OFFSET		9
#define IEEE_CTRL_1GBPS_LINKSPEED_MASK		0x2040
#define IEEE_CTRL_LINKSPEED_MASK		0x0040
#define IEEE_CTRL_LINKSPEED_1000M		0x0040
#define IEEE_CTRL_LINKSPEED_100M		0x2000
#define IEEE_CTRL_LINKSPEED_10M			0x0000
#define IEEE_CTRL_RESET_MASK			0x8000
#define IEEE_CTRL_AUTONEGOTIATE_ENABLE		0x1000
#define IEEE_STAT_AUTONEGOTIATE_CAPABLE		0x0008
#define IEEE_STAT_AUTONEGOTIATE_COMPLETE	0x0020
#define IEEE_STAT_AUTONEGOTIATE_RESTART		0x0200
#define IEEE_STAT_1GBPS_EXTENSIONS		0x0100
#define IEEE_AN1_ABILITY_MASK			0x1FE0
#define IEEE_AN3_ABILITY_MASK_1GBPS		0x0C00
#define IEEE_AN1_ABILITY_MASK_100MBPS		0x0380
#define IEEE_AN1_ABILITY_MASK_10MBPS		0x0060

#define PHY_DETECT_REG		1
#define PHY_DETECT_MASK 	0x1808

/* Forward declarations. */
static err_t xemacliteif_output(struct netif *netif, struct pbuf *p,
		struct ip_addr *ipaddr);
unsigned get_IEEE_phy_speed_emaclite(XEmacLite *xemaclitep);
unsigned configure_IEEE_phy_speed_emaclite(XEmacLite *xemaclitep, unsigned speed);

/* The payload from multiple pbufs is assembled into a single contiguous
 * area for transmission. Currently this is a global variable (it should really
 * belong in the per netif structure), but that is ok since this can be used
 * only in a protected context
 */
unsigned char xemac_tx_frame[XEL_MAX_FRAME_SIZE] __attribute__((aligned(64)));

#ifndef XLWIP_CONFIG_INCLUDE_EMACLITE_ON_ZYNQ
#if XPAR_INTC_0_HAS_FAST == 1
/*********** Function Prototypes *********************************************/
/*
 *  Function prototypes of the functions used for registering Fast
 *  Interrupt Handlers
 */
static void XEmacLite_FastInterruptHandler(void)
					__attribute__ ((fast_interrupt));


/**************** Variable Declarations **************************************/

/** Variables for Fast Interrupt handlers ***/
XEmacLite *xemaclitep_fast;

#endif
#endif

static void
xemacif_recv_handler(void *arg) {
	struct xemac_s *xemac = (struct xemac_s *)(arg);
	xemacliteif_s *xemacliteif = (xemacliteif_s *)(xemac->state);
	XEmacLite *instance = xemacliteif->instance;
	struct pbuf *p;
	int len = 0;
	struct xtopology_t *xtopologyp = &xtopology[xemac->topology_index];

#if XLWIP_CONFIG_INCLUDE_EMACLITE_ON_ZYNQ == 1
#else
	XIntc_AckIntr(xtopologyp->intc_baseaddr, 1 << xtopologyp->intc_emac_intr);
#endif
	p = pbuf_alloc(PBUF_RAW, XEL_MAX_FRAME_SIZE, PBUF_POOL);
	if (!p) {
#if LINK_STATS
		lwip_stats.link.memerr++;
		lwip_stats.link.drop++;
#endif
		/* receive and just ignore the frame.
		 * we need to receive the frame because otherwise emaclite will
		 * not generate any other interrupts since it cannot receive,
		 * and we do not actively poll the emaclite
		 */
		XEmacLite_Recv(instance, xemac_tx_frame);
		return;
	}

	/* receive the packet */
	len = XEmacLite_Recv(instance, p->payload);

	if (len == 0) {
#if LINK_STATS
		lwip_stats.link.drop++;
#endif
		pbuf_free(p);
		return;
	}

	/* store it in the receive queue, where it'll be processed by xemacif input thread */
	if (pq_enqueue(xemacliteif->recv_q, (void*)p) < 0) {
#if LINK_STATS
		lwip_stats.link.memerr++;
		lwip_stats.link.drop++;
#endif
		pbuf_free(p);
		return;
	}

#if !NO_SYS
	sys_sem_signal(&xemac->sem_rx_data_available);
#endif

}

int transmit_packet(XEmacLite *instancep, void *packet, unsigned len)
{
	XStatus result = 0;

	/* there is space for a buffer, so transfer */
	result = XEmacLite_Send(instancep, packet, len);

        if (result != XST_SUCCESS) {
                return -1;
        }

	return 0;
}

/*
 * this function is always called with interrupts off
 * this function also assumes that there is space to send in the Emaclite buffer
 */
static err_t
_unbuffered_low_level_output(XEmacLite *instancep, struct pbuf *p)
{
	struct pbuf *q;
	int total_len = 0;

#if ETH_PAD_SIZE
	pbuf_header(p, -ETH_PAD_SIZE);			/* drop the padding word */
#endif

	for(q = p, total_len = 0; q != NULL; q = q->next) {
		/* Send the data from the pbuf to the interface, one pbuf at a
		   time. The size of the data in each pbuf is kept in the ->len
		   variable. */
		memcpy(xemac_tx_frame + total_len, q->payload, q->len);
		total_len += q->len;
	}

	if (transmit_packet(instancep, xemac_tx_frame, total_len) < 0) {
#if LINK_STATS
		lwip_stats.link.drop++;
#endif
	}

#if ETH_PAD_SIZE
	pbuf_header(p, ETH_PAD_SIZE);			/* reclaim the padding word */
#endif

#if LINK_STATS
	lwip_stats.link.xmit++;
#endif /* LINK_STATS */

	return ERR_OK;
}

/*
 * low_level_output():
 *
 * Should do the actual transmission of the packet. The packet is
 * contained in the pbuf that is passed to the function. This pbuf
 * might be chained.
 *
 */
static err_t
low_level_output(struct netif *netif, struct pbuf *p)
{
	SYS_ARCH_DECL_PROTECT(lev);
	struct xemac_s *xemac = (struct xemac_s *)(netif->state);
	xemacliteif_s *xemacliteif = (xemacliteif_s *)(xemac->state);
	XEmacLite *instance = xemacliteif->instance;
	struct pbuf *q;

	SYS_ARCH_PROTECT(lev);

	/* check if space is available to send */
        if (XEmacLite_TxBufferAvailable(instance) == TRUE) {
		if (pq_qlength(xemacliteif->send_q)) {  	/* send backlog */
			_unbuffered_low_level_output(instance, (struct pbuf *)pq_dequeue(xemacliteif->send_q));
		} else { 				/* send current */
			_unbuffered_low_level_output(instance, p);
			SYS_ARCH_UNPROTECT(lev);
			return ERR_OK;
		}
	}

	/* if we cannot send the packet immediately, then make a copy of the whole packet
	 * into a separate pbuf and store it in send_q. We cannot enqueue the pbuf as is
	 * since parts of the pbuf may be modified inside lwIP.
	 */
	q = pbuf_alloc(PBUF_RAW, p->tot_len, PBUF_POOL);
	if (!q) {
#if LINK_STATS
		lwip_stats.link.drop++;
#endif
		SYS_ARCH_UNPROTECT(lev);
		return ERR_MEM;
	}

	for (q->len = 0; p; p = p->next) {
		memcpy(q->payload + q->len, p->payload, p->len);
		q->len += p->len;
	}
	if (pq_enqueue(xemacliteif->send_q, (void *)q) < 0) {
#if LINK_STATS
		lwip_stats.link.drop++;
#endif
		SYS_ARCH_UNPROTECT(lev);
		return ERR_MEM;
	}

	SYS_ARCH_UNPROTECT(lev);

	return ERR_OK;
}

static void
xemacif_send_handler(void *arg) {
	struct xemac_s *xemac = (struct xemac_s *)(arg);
	xemacliteif_s *xemacliteif = (xemacliteif_s *)(xemac->state);
	XEmacLite *instance = xemacliteif->instance;
	struct xtopology_t *xtopologyp = &xtopology[xemac->topology_index];

#if XLWIP_CONFIG_INCLUDE_EMACLITE_ON_ZYNQ == 1
#else
	XIntc_AckIntr(xtopologyp->intc_baseaddr, 1 << xtopologyp->intc_emac_intr);
#endif

	if (pq_qlength(xemacliteif->send_q) && (XEmacLite_TxBufferAvailable(instance) == TRUE)) {
		struct pbuf *p = pq_dequeue(xemacliteif->send_q);
		_unbuffered_low_level_output(instance, p);
		pbuf_free(p);
	}
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
	struct xemac_s *xemac = (struct xemac_s *)(netif->state);
	xemacliteif_s *xemacliteif = (xemacliteif_s *)(xemac->state);

	/* see if there is data to process */
	if (pq_qlength(xemacliteif->recv_q) == 0)
		return NULL;

	/* return one packet from receive q */
	return (struct pbuf *)pq_dequeue(xemacliteif->recv_q);
}

/*
 * xemacliteif_output():
 *
 * This function is called by the TCP/IP stack when an IP packet
 * should be sent. It calls the function called low_level_output() to
 * do the actual transmission of the packet.
 *
 */

err_t
xemacliteif_output(struct netif *netif, struct pbuf *p,
		struct ip_addr *ipaddr)
{
	/* resolve hardware address, then send (or queue) packet */
	return etharp_output(netif, p, ipaddr);
}

/*
 * xemacliteif_input():
 *
 * This function should be called when a packet is ready to be read
 * from the interface. It uses the function low_level_input() that
 * should handle the actual reception of bytes from the network
 * interface.
 *
 * Returns the number of packets read (max 1 packet on success,
 * 0 if there are no packets)
 *
 */
int
xemacliteif_input(struct netif *netif)
{
	struct eth_hdr *ethhdr;
	struct pbuf *p;

	/* move received packet into a new pbuf */
	p = low_level_input(netif);

	/* no packet could be read, silently ignore this */
	if (p == NULL)
		return 0;

	/* points to packet payload, which starts with an Ethernet header */
	ethhdr = p->payload;

#if LINK_STATS
	lwip_stats.link.recv++;
#endif /* LINK_STATS */

	switch (htons(ethhdr->type)) {
		/* IP or ARP packet? */
		case ETHTYPE_IP:
		case ETHTYPE_ARP:
#if PPPOE_SUPPORT
			/* PPPoE packet? */
		case ETHTYPE_PPPOEDISC:
		case ETHTYPE_PPPOE:
#endif /* PPPOE_SUPPORT */
			/* full packet send to tcpip_thread to process */
			if (netif->input(p, netif) != ERR_OK) {
				LWIP_DEBUGF(NETIF_DEBUG, ("xlltemacif_input: IP input error\r\n"));
				pbuf_free(p);
				p = NULL;
			}
			break;

		default:
			pbuf_free(p);
			p = NULL;
			break;
	}

	return 1;
}

#if !NO_SYS
static void
arp_timer(void *arg)
{
	etharp_tmr();
	sys_timeout(ARP_TMR_INTERVAL, arp_timer, NULL);
}
#endif

static XEmacLite_Config *
xemaclite_lookup_config(unsigned base)
{
	XEmacLite_Config *CfgPtr = NULL;
	int i;

	for (i = 0; i < XPAR_XEMACLITE_NUM_INSTANCES; i++)
		if (XEmacLite_ConfigTable[i].BaseAddress == base) {
			CfgPtr = &XEmacLite_ConfigTable[i];
			break;
		}

	return CfgPtr;
}

void XEmacLite_InterruptWrapper( void *InstancePtr )
{
extern BaseType_t xInsideISR;

	xInsideISR++;
	XEmacLite_InterruptHandler( InstancePtr );
	xInsideISR--;
}

static err_t low_level_init(struct netif *netif)
{
	struct xemac_s *xemac;
	XEmacLite_Config *config;
	XEmacLite *xemaclitep;
	struct xtopology_t *xtopologyp;
	xemacliteif_s *xemacliteif;
	unsigned link_speed = 1000;

	xemaclitep = mem_malloc(sizeof *xemaclitep);
#ifndef XLWIP_CONFIG_INCLUDE_EMACLITE_ON_ZYNQ
#if XPAR_INTC_0_HAS_FAST == 1
	xemaclitep_fast = xemaclitep;
#endif
#endif
	if (xemaclitep == NULL) {
		LWIP_DEBUGF(NETIF_DEBUG, ("xemacliteif_init: out of memory\r\n"));
		return ERR_MEM;
	}

	xemac = mem_malloc(sizeof *xemac);
	if (xemac == NULL) {
		LWIP_DEBUGF(NETIF_DEBUG, ("xemacliteif_init: out of memory\r\n"));
		return ERR_MEM;
	}

	xemacliteif = mem_malloc(sizeof *xemacliteif);
	if (xemacliteif == NULL) {
		LWIP_DEBUGF(NETIF_DEBUG, ("xemacliteif_init: out of memory\r\n"));
		return ERR_MEM;
	}

	/* obtain pointer to topology structure for this emac */
	xemac->topology_index = xtopology_find_index((unsigned)(netif->state));
	xtopologyp = &xtopology[xemac->topology_index];

	/* obtain config of this emaclite */
	config = xemaclite_lookup_config((unsigned)(netif->state));

	/* maximum transfer unit */
	netif->mtu = XEL_MTU_SIZE;

	/* broadcast capability */
	netif->flags = NETIF_FLAG_BROADCAST | NETIF_FLAG_ETHARP | NETIF_FLAG_LINK_UP;

	/* initialize the mac */
	XEmacLite_Initialize(xemaclitep, config->DeviceId);
	xemaclitep->NextRxBufferToUse = 0;

#if XLWIP_CONFIG_INCLUDE_EMACLITE_ON_ZYNQ == 1
	XScuGic_RegisterHandler(xtopologyp->scugic_baseaddr,
				xtopologyp->intc_emac_intr,
				(Xil_ExceptionHandler)XEmacLite_InterruptHandler,
				xemaclitep);

	XScuGic_SetPriTrigTypeByDistAddr(INTC_DIST_BASE_ADDR,
				xtopologyp->intc_emac_intr,
				EMACLITE_INTR_PRIORITY_SET_IN_GIC,
				TRIG_TYPE_RISING_EDGE_SENSITIVE);

	XScuGic_EnableIntr(INTC_DIST_BASE_ADDR,
					xtopologyp->intc_emac_intr);
#else
#if NO_SYS

#if XPAR_INTC_0_HAS_FAST == 1
	XIntc_RegisterFastHandler(xtopologyp->intc_baseaddr,
		xtopologyp->intc_emac_intr,
		(XFastInterruptHandler)XEmacLite_FastInterruptHandler);
#else
	XIntc_RegisterHandler(xtopologyp->intc_baseaddr,
				xtopologyp->intc_emac_intr,
				(XInterruptHandler)XEmacLite_InterruptHandler,
				xemaclitep);
#endif

#else
	xPortInstallInterruptHandler( XPAR_INTC_0_EMACLITE_0_VEC_ID, ( XInterruptHandler ) XEmacLite_InterruptWrapper, xemaclitep );
	vPortEnableInterrupt( XPAR_INTC_0_EMACLITE_0_VEC_ID );
#endif
#endif

	/* set mac address */
	XEmacLite_SetMacAddress(xemaclitep, (unsigned char*)(netif->hwaddr));

	/* flush any frames already received */
	XEmacLite_FlushReceive(xemaclitep);

	/* set Rx, Tx interrupt handlers */
	XEmacLite_SetRecvHandler(xemaclitep, (void *)(xemac), xemacif_recv_handler);
	XEmacLite_SetSendHandler(xemaclitep, (void *)(xemac), xemacif_send_handler);

	/* enable Rx, Tx interrupts */
	XEmacLite_EnableInterrupts(xemaclitep);

#if !NO_SYS
	sys_sem_new(&xemac->sem_rx_data_available, 0);
#endif

	/* replace the state in netif (currently the base address of emaclite)
	 * with the xemacliteif instance pointer.
	 * this contains a pointer to the config table entry
	 */
	xemac->type = xemac_type_xps_emaclite;
	xemac->state = (void *)xemacliteif;
	netif->state = (void *)xemac;

	xemacliteif->instance = xemaclitep;
	xemacliteif->recv_q = pq_create_queue();
	if (!xemacliteif->recv_q)
		return ERR_MEM;

	xemacliteif->send_q = pq_create_queue();
	if (!xemacliteif->send_q)
		return ERR_MEM;

	/* Initialize PHY */


/* set PHY <--> MAC data clock */
#ifdef  CONFIG_LINKSPEED_AUTODETECT
	link_speed = get_IEEE_phy_speed_emaclite(xemaclitep);
	xil_printf("auto-negotiated link speed: %d\r\n", link_speed);
#elif	defined(CONFIG_LINKSPEED1000)
	xil_printf("Link speed of 1000 Mbps not possible\r\n");
#elif	defined(CONFIG_LINKSPEED100)
	link_speed = 100;
	configure_IEEE_phy_speed_emaclite(xemaclitep, link_speed);
	xil_printf("link speed: %d\r\n", link_speed);
#elif	defined(CONFIG_LINKSPEED10)
	link_speed = 10;
	configure_IEEE_phy_speed_emaclite(xemaclitep, link_speed);
	xil_printf("link speed: %d\r\n", link_speed);
#endif

	return ERR_OK;
}


static int detect_phy_emaclite(XEmacLite *xemaclitep)
{
	u16 phy_reg;
	u32 phy_addr;

	for (phy_addr = 31; phy_addr > 0; phy_addr--) {
		XEmacLite_PhyRead(xemaclitep, phy_addr, PHY_DETECT_REG, &phy_reg);

		if ((phy_reg != 0xFFFF) &&
			((phy_reg & PHY_DETECT_MASK) == PHY_DETECT_MASK)) {
			/* Found a valid PHY address */
			LWIP_DEBUGF(NETIF_DEBUG, ("XEMacLite detect_phy: PHY detected at address %d.\r\n", phy_addr));
			LWIP_DEBUGF(NETIF_DEBUG, ("XEMacLite detect_phy: PHY detected.\r\n"));
			return phy_addr;
		}
	}

	LWIP_DEBUGF(NETIF_DEBUG, ("XEMacLite detect_phy: No PHY detected.  Assuming a PHY at address 0\r\n"));

        /* default to zero */
	return 0;
}

unsigned get_IEEE_phy_speed_emaclite(XEmacLite *xemaclitep)
{
	u16 control;
	u16 status;
	u16 partner_capabilities;
	u16 partner_capabilities_1000;
	u16 phylinkspeed;
	u32 phy_addr = detect_phy_emaclite(xemaclitep);
	const TickType_t xSmallDelay = pdMS_TO_TICKS( 200UL );

	/* Dont advertise PHY speed of 1000 Mbps */
	XEmacLite_PhyWrite(xemaclitep, phy_addr,
				IEEE_1000_ADVERTISE_REG_OFFSET,
				0);
	/* Advertise PHY speed of 100 and 10 Mbps */
	XEmacLite_PhyWrite(xemaclitep, phy_addr,
				IEEE_AUTONEGO_ADVERTISE_REG,
				ADVERTISE_100_AND_10);

	XEmacLite_PhyRead(xemaclitep, phy_addr,
				     IEEE_CONTROL_REG_OFFSET,
				     &control);
	control |= (IEEE_CTRL_AUTONEGOTIATE_ENABLE |
					IEEE_STAT_AUTONEGOTIATE_RESTART);

	XEmacLite_PhyWrite(xemaclitep, phy_addr,
				IEEE_CONTROL_REG_OFFSET,
				control);

	/* Read PHY control and status registers is successful. */
	XEmacLite_PhyRead(xemaclitep, phy_addr,
				     IEEE_CONTROL_REG_OFFSET,
				     &control);
	XEmacLite_PhyRead(xemaclitep, phy_addr,
				     IEEE_STATUS_REG_OFFSET,
				     &status);

	if ((control & IEEE_CTRL_AUTONEGOTIATE_ENABLE) &&
			(status & IEEE_STAT_AUTONEGOTIATE_CAPABLE)) {

		while ( !(status & IEEE_STAT_AUTONEGOTIATE_COMPLETE) ) {
#if !NO_SYS
			vTaskDelay( xSmallDelay );
#endif
			XEmacLite_PhyRead(xemaclitep, phy_addr,
						     IEEE_STATUS_REG_OFFSET,
						     &status);
		}

		XEmacLite_PhyRead(xemaclitep, phy_addr,
					     IEEE_PARTNER_ABILITIES_1_REG_OFFSET,
					     &partner_capabilities);

		if (status & IEEE_STAT_1GBPS_EXTENSIONS) {
			XEmacLite_PhyRead(xemaclitep, phy_addr,
						     IEEE_PARTNER_ABILITIES_3_REG_OFFSET,
						     &partner_capabilities_1000);
			if (partner_capabilities_1000 & IEEE_AN3_ABILITY_MASK_1GBPS) return 1000;
		}

		if (partner_capabilities & IEEE_AN1_ABILITY_MASK_100MBPS) return 100;
		if (partner_capabilities & IEEE_AN1_ABILITY_MASK_10MBPS) return 10;

		xil_printf("%s: unknown PHY link speed, setting TEMAC speed to be 10 Mbps\r\n",
				__FUNCTION__);
		return 10;


	} else {

		/* Update TEMAC speed accordingly */
		if (status & IEEE_STAT_1GBPS_EXTENSIONS) {

			/* Get commanded link speed */
			phylinkspeed = control & IEEE_CTRL_1GBPS_LINKSPEED_MASK;

			switch (phylinkspeed) {
				case (IEEE_CTRL_LINKSPEED_1000M):
					return 1000;
				case (IEEE_CTRL_LINKSPEED_100M):
					return 100;
				case (IEEE_CTRL_LINKSPEED_10M):
					return 10;
				default:
					xil_printf("%s: unknown PHY link speed (%d), setting TEMAC speed to be 10 Mbps\r\n",
							__FUNCTION__, phylinkspeed);
					return 10;
			}

		} else {

			return (control & IEEE_CTRL_LINKSPEED_MASK) ? 100 : 10;

		}

	}
}

unsigned configure_IEEE_phy_speed_emaclite(XEmacLite *xemaclitep, unsigned speed)
{
	u16 control;
	u16 status;
	u16 phylinkspeed;
	u32 phy_addr = detect_phy_emaclite(xemaclitep);

	XEmacLite_PhyRead(xemaclitep, phy_addr,
				IEEE_CONTROL_REG_OFFSET,
				&control);
	control &= ~IEEE_CTRL_LINKSPEED_100M;
	control &= ~IEEE_CTRL_LINKSPEED_10M;
	if (speed == 100) {
		control |= IEEE_CTRL_LINKSPEED_100M;
		/* Dont advertise PHY speed of 1000 Mbps */
		XEmacLite_PhyWrite(xemaclitep, phy_addr,
					IEEE_1000_ADVERTISE_REG_OFFSET,
					0);
		/* Dont advertise PHY speed of 10 Mbps */
		XEmacLite_PhyWrite(xemaclitep, phy_addr,
				IEEE_AUTONEGO_ADVERTISE_REG,
				ADVERTISE_100);

	}
	else if (speed == 10) {
		control |= IEEE_CTRL_LINKSPEED_10M;
		/* Dont advertise PHY speed of 1000 Mbps */
		XEmacLite_PhyWrite(xemaclitep, phy_addr,
				IEEE_1000_ADVERTISE_REG_OFFSET,
					0);
		/* Dont advertise PHY speed of 100 Mbps */
		XEmacLite_PhyWrite(xemaclitep, phy_addr,
				IEEE_AUTONEGO_ADVERTISE_REG,
				ADVERTISE_10);
	}

	XEmacLite_PhyWrite(xemaclitep, phy_addr,
				IEEE_CONTROL_REG_OFFSET,
				control | IEEE_CTRL_RESET_MASK);
	{
		volatile int wait;
		for (wait=0; wait < 100000; wait++);
		for (wait=0; wait < 100000; wait++);
	}
	return 0;
}

/*
 * xemacliteif_init():
 *
 * Should be called at the beginning of the program to set up the
 * network interface. It calls the function low_level_init() to do the
 * actual setup of the hardware.
 *
 */

err_t
xemacliteif_init(struct netif *netif)
{
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

	netif->name[0] = IFNAME0;
	netif->name[1] = IFNAME1;
	netif->output = xemacliteif_output;
	netif->linkoutput = low_level_output;

	low_level_init(netif);

#if !NO_SYS
	sys_timeout(ARP_TMR_INTERVAL, arp_timer, NULL);
#endif

	return ERR_OK;
}

#ifndef XLWIP_CONFIG_INCLUDE_EMACLITE_ON_ZYNQ
#if XPAR_INTC_0_HAS_FAST == 1
/****************** Fast Interrupt Handler **********************************/

void XEmacLite_FastInterruptHandler (void)
{
	XEmacLite_InterruptHandler((void *)xemaclitep_fast);
}
#endif
#endif
