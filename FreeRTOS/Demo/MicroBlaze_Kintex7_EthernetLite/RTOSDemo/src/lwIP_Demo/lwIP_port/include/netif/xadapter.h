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
