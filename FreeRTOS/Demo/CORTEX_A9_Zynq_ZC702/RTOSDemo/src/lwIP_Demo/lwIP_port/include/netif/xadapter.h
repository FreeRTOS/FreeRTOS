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

#ifndef __XADAPTER_H_
#define __XADAPTER_H_

#ifdef __cplusplus
extern "C" {
#endif

#include "lwipopts.h"

#if !NO_SYS
#ifdef OS_IS_XILKERNEL
#include "xmk.h"
#endif
#include "lwip/sys.h"
#endif

#include "lwip/netif.h"
#include "lwip/ip.h"

#include "netif/xtopology.h"

struct xemac_s {
	enum xemac_types type;
	int  topology_index;
	void *state;
#if !NO_SYS
        sys_sem_t sem_rx_data_available;
#endif
};

void 		lwip_raw_init();
int 		xemacif_input(struct netif *netif);
void 		xemacif_input_thread(struct netif *netif);
struct netif *	xemac_add(struct netif *netif,
	struct ip_addr *ipaddr, struct ip_addr *netmask, struct ip_addr *gw,
	unsigned char *mac_ethernet_address,
  	unsigned mac_baseaddr);
#ifdef __arm__
void xemacpsif_resetrx_on_no_rxdata(struct netif *netif);
#endif

/* global lwip debug variable used for debugging */
extern int lwip_runtime_debug;

#ifdef __cplusplus
}
#endif

#endif
