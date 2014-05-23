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

#ifndef __NETIF_XEMACLITEIF_H__
#define __NETIF_XEMACLITEIF_H__

#ifdef __cplusplus
extern "C" {
#endif

#include "lwip/netif.h"
#include "netif/etharp.h"
#include "netif/xpqueue.h"
#include "xemaclite.h"
#include "xemaclite_i.h"
#include "xstatus.h"

/* structure within each netif, encapsulating all information required for 
 * using a particular emaclite instance
 */
typedef struct {
        XEmacLite *instance;

	/* queue to store overflow packets */
	pq_queue_t *recv_q;
	pq_queue_t *send_q;
} xemacliteif_s;

void 	xemacliteif_setmac(u32_t index, u8_t *addr);
u8_t*	xemacliteif_getmac(u32_t index);
err_t 	xemacliteif_init(struct netif *netif);
int 	xemacliteif_input(struct netif *netif);
   
#ifdef __cplusplus
}
#endif

#endif /* __NETIF_XEMACLITEIF_H__ */
