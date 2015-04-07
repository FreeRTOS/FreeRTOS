/******************************************************************************
*
* Copyright (C) 2010 - 2014 Xilinx, Inc.  All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
* XILINX CONSORTIUM BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/

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
