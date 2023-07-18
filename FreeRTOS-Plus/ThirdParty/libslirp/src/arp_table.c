/* SPDX-License-Identifier: MIT */
/*
 * ARP table
 *
 * Copyright (c) 2011 AdaCore
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
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

#include "slirp.h"

#include <string.h>

void arp_table_add(Slirp *slirp, uint32_t ip_addr,
                   const uint8_t ethaddr[ETH_ALEN])
{
    const uint32_t broadcast_addr =
        ~slirp->vnetwork_mask.s_addr | slirp->vnetwork_addr.s_addr;
    ArpTable *arptbl = &slirp->arp_table;
    int i;
    char ethaddr_str[ETH_ADDRSTRLEN];
    char addr[INET_ADDRSTRLEN];

    DEBUG_CALL("arp_table_add");
    DEBUG_ARG("ip = %s", inet_ntop(AF_INET, &(struct in_addr){ .s_addr = ip_addr },
                                   addr, sizeof(addr)));
    DEBUG_ARG("hw addr = %s", slirp_ether_ntoa(ethaddr, ethaddr_str,
                                               sizeof(ethaddr_str)));

    if (ip_addr == 0 || ip_addr == 0xffffffff || ip_addr == broadcast_addr) {
        /* Do not register broadcast addresses */
        return;
    }

    /* Search for an entry */
    for (i = 0; i < ARP_TABLE_SIZE; i++) {
        if (arptbl->table[i].ar_sip == ip_addr) {
            /* Update the entry */
            memcpy(arptbl->table[i].ar_sha, ethaddr, ETH_ALEN);
            return;
        }
    }

    /* No entry found, create a new one */
    arptbl->table[arptbl->next_victim].ar_sip = ip_addr;
    memcpy(arptbl->table[arptbl->next_victim].ar_sha, ethaddr, ETH_ALEN);
    arptbl->next_victim = (arptbl->next_victim + 1) % ARP_TABLE_SIZE;
}

bool arp_table_search(Slirp *slirp, uint32_t ip_addr,
                      uint8_t out_ethaddr[ETH_ALEN])
{
    const uint32_t broadcast_addr =
        ~slirp->vnetwork_mask.s_addr | slirp->vnetwork_addr.s_addr;
    ArpTable *arptbl = &slirp->arp_table;
    int i;
    char ethaddr_str[ETH_ADDRSTRLEN];
    char addr[INET_ADDRSTRLEN];

    DEBUG_CALL("arp_table_search");
    DEBUG_ARG("ip = %s", inet_ntop(AF_INET, &(struct in_addr){ .s_addr = ip_addr },
                                   addr, sizeof(addr)));

    /* If broadcast address */
    if (ip_addr == 0 || ip_addr == 0xffffffff || ip_addr == broadcast_addr) {
        /* return Ethernet broadcast address */
        memset(out_ethaddr, 0xff, ETH_ALEN);
        return 1;
    }

    for (i = 0; i < ARP_TABLE_SIZE; i++) {
        if (arptbl->table[i].ar_sip == ip_addr) {
            memcpy(out_ethaddr, arptbl->table[i].ar_sha, ETH_ALEN);
            DEBUG_ARG("found hw addr = %s",
                      slirp_ether_ntoa(out_ethaddr, ethaddr_str,
                                       sizeof(ethaddr_str)));
            return 1;
        }
    }

    return 0;
}
