/*
 * Copyright (c) 2010-2013 Xilinx, Inc.  All rights reserved.
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

#ifndef __NETIF_XAXIEMACIF_H__
#define __NETIF_XAXIEMACIF_H__

#ifdef __cplusplus
extern "C" {
#endif

#include "xlwipconfig.h"
#include "lwip/netif.h"
#include "netif/etharp.h"
#include "netif/xadapter.h"

#include "xparameters.h"
#include "xstatus.h"

#include "xaxiethernet.h"
#ifdef XLWIP_CONFIG_INCLUDE_AXI_ETHERNET_FIFO
#include "xllfifo.h"
#else
#include "xaxidma.h"
#include "xaxidma_hw.h"
#endif

#include "netif/xpqueue.h"
#include "xlwipconfig.h"

void 	xaxiemacif_setmac(u32_t index, u8_t *addr);
u8_t*	xaxiemacif_getmac(u32_t index);
err_t 	xaxiemacif_init(struct netif *netif);
int 	xaxiemacif_input(struct netif *netif);

unsigned get_IEEE_phy_speed(XAxiEthernet *xaxiemacp);
unsigned configure_IEEE_phy_speed(XAxiEthernet *xaxiemacp, unsigned speed);
unsigned Phy_Setup (XAxiEthernet *xaxiemacp);

/* xaxiemacif_hw.c */
void 	xaxiemac_error_handler(XAxiEthernet * Temac);

/* structure within each netif, encapsulating all information required for
 * using a particular temac instance
 */
typedef struct {
#ifdef XLWIP_CONFIG_INCLUDE_AXI_ETHERNET_FIFO
	XLlFifo      axififo;
#else
	XAxiDma      axidma;
#endif
	XAxiEthernet axi_ethernet;

	/* queue to store overflow packets */
	pq_queue_t *recv_q;
	pq_queue_t *send_q;

	/* pointers to memory holding buffer descriptors (used only with SDMA) */
	void *rx_bdspace;
	void *tx_bdspace;
} xaxiemacif_s;

extern xaxiemacif_s xaxiemacif;

int	is_tx_space_available(xaxiemacif_s *emac);

/* xaxiemacif_dma.c */
#ifndef XLWIP_CONFIG_INCLUDE_AXI_ETHERNET_FIFO
XStatus init_axi_dma(struct xemac_s *xemac);
int  process_sent_bds(XAxiDma_BdRing *txring);

void axidma_send_handler(void *arg);
XStatus axidma_sgsend(xaxiemacif_s *xaxiemacif, struct pbuf *p);
#endif

#ifdef __cplusplus
}
#endif

#endif /* __NETIF_XAXIEMACIF_H__ */
