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

#ifndef __NETIF_XEMACPSIF_H__
#define __NETIF_XEMACPSIF_H__

#ifdef __cplusplus
extern "C" {
#endif

#include "xlwipconfig.h"
#include "lwip/netif.h"
#include "netif/etharp.h"
#include "netif/xadapter.h"

#include "xstatus.h"
#include "sleep.h"
#include "xparameters.h"
#include "xparameters_ps.h"	/* defines XPAR values */
#include "xil_types.h"
#include "xil_assert.h"
#include "xil_io.h"
#include "xil_exception.h"
#include "xpseudo_asm.h"
#include "xil_cache.h"
#include "xil_printf.h"
#include "xuartps.h"
#include "xscugic.h"
#include "xemacps.h"		/* defines XEmacPs API */

#include "netif/xpqueue.h"
#include "xlwipconfig.h"

void 	xemacpsif_setmac(u32_t index, u8_t *addr);
u8_t*	xemacpsif_getmac(u32_t index);
err_t 	xemacpsif_init(struct netif *netif);
int 	xemacpsif_input(struct netif *netif);
#ifdef NOTNOW_BHILL
unsigned get_IEEE_phy_speed(XLlTemac *xlltemacp);
#endif

/* xaxiemacif_hw.c */
void 	xemacps_error_handler(XEmacPs * Temac);

/* structure within each netif, encapsulating all information required for
 * using a particular temac instance
 */
typedef struct {
	XEmacPs emacps;

	/* queue to store overflow packets */
	pq_queue_t *recv_q;
	pq_queue_t *send_q;

	/* pointers to memory holding buffer descriptors (used only with SDMA) */
	void *rx_bdspace;
	void *tx_bdspace;

	unsigned int last_rx_frms_cntr;

} xemacpsif_s;

extern xemacpsif_s xemacpsif;

int	is_tx_space_available(xemacpsif_s *emac);

/* xaxiemacif_dma.c */

XStatus init_axi_dma(struct xemac_s *xemac);
void  process_sent_bds(XEmacPs_BdRing *txring);
unsigned Phy_Setup (XEmacPs *xemacpsp);
void emacps_send_handler(void *arg);
XStatus emacps_sgsend(xemacpsif_s *xemacpsif, struct pbuf *p);
void emacps_recv_handler(void *arg);
void emacps_error_handler(void *arg,u8 Direction, u32 ErrorWord);
void setup_rx_bds(XEmacPs_BdRing *rxring);
void HandleTxErrors(struct xemac_s *xemac);
void HandleEmacPsError(struct xemac_s *xemac);
XEmacPs_Config *xemacps_lookup_config(unsigned mac_base);
void init_emacps(xemacpsif_s *xemacps, struct netif *netif);
void setup_isr (struct xemac_s *xemac);
XStatus init_dma(struct xemac_s *xemac);
void start_emacps (xemacpsif_s *xemacps);
void FreeTxRxPBufs(void);
void FreeOnlyTxPBufs(void);
void init_emacps_on_error (xemacpsif_s *xemacps, struct netif *netif);
void clean_dma_txdescs(struct xemac_s *xemac);
void resetrx_on_no_rxdata(xemacpsif_s *xemacpsif);

#ifdef __cplusplus
}
#endif

#endif /* __NETIF_XAXIEMACIF_H__ */
