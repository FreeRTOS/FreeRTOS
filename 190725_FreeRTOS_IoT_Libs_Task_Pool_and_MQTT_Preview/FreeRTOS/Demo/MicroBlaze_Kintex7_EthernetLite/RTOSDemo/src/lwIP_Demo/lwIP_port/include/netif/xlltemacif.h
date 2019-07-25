/******************************************************************************
*
* Copyright (C) 2007 - 2014 Xilinx, Inc.  All rights reserved.
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
