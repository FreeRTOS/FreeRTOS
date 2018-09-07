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

#ifndef __NETIF_XLLTEMACIF_H__
#define __NETIF_XLLTEMACIF_H__

#ifdef __cplusplus
extern "C" {
#endif

#include "lwip/netif.h"
#include "netif/etharp.h"
#include "netif/xadapter.h"

#include "xparameters.h"
#include "xstatus.h"
#include "xlltemac.h"
#include "xlldma.h"
#include "xllfifo.h"
#include "xlldma_bdring.h"

#include "netif/xpqueue.h"
#include "xlwipconfig.h"

void 	xlltemacif_setmac(u32_t index, u8_t *addr);
u8_t*	xlltemacif_getmac(u32_t index);
err_t 	xlltemacif_init(struct netif *netif);
int 	xlltemacif_input(struct netif *netif);
unsigned get_IEEE_phy_speed(XLlTemac *xlltemacp);
unsigned Phy_Setup (XLlTemac *xlltemacp);
unsigned configure_IEEE_phy_speed(XLlTemac *xlltemacp, unsigned speed);

/* xlltemacif_hw.c */
void 	xlltemac_error_handler(XLlTemac * Temac);

/* structure within each netif, encapsulating all information required for
 * using a particular temac instance
 */
typedef struct {
	XLlDma lldma;
	XLlFifo llfifo;
	XLlTemac lltemac;

	/* queue to store overflow packets */
	pq_queue_t *recv_q;
	pq_queue_t *send_q;

	/* pointers to memory holding buffer descriptors (used only with SDMA) */
	void *rx_bdspace;
	void *tx_bdspace;
} xlltemacif_s;

extern xlltemacif_s xlltemacif;

/* xlltemacif_sdma.c */
XStatus init_sdma(struct xemac_s *xemac);
int  process_sent_bds(XLlDma_BdRing *txring);
void lldma_send_handler(void *arg);
XStatus lldma_sgsend(xlltemacif_s *xlltemacif, struct pbuf *p);

#ifdef __cplusplus
}
#endif

#endif /* __NETIF_XLLTEMACIF_H__ */
