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
#ifndef __LWIP_IP_ADDR_H__
#define __LWIP_IP_ADDR_H__

#include "lwip/arch.h"

#define IP_ADDR_ANY 0

struct ip_addr {
  u32_t addr[4];
};

#define IP6_ADDR(ipaddr, a,b,c,d,e,f,g,h) do { (ipaddr)->addr[0] = htonl((u32_t)((a & 0xffff) << 16) | (b & 0xffff)); \
                                               (ipaddr)->addr[1] = htonl(((c & 0xffff) << 16) | (d & 0xffff)); \
                                               (ipaddr)->addr[2] = htonl(((e & 0xffff) << 16) | (f & 0xffff)); \
                                               (ipaddr)->addr[3] = htonl(((g & 0xffff) << 16) | (h & 0xffff)); } while(0)

u8_t ip_addr_netcmp(struct ip_addr *addr1, struct ip_addr *addr2,
        struct ip_addr *mask);
u8_t ip_addr_cmp(struct ip_addr *addr1, struct ip_addr *addr2);
void ip_addr_set(struct ip_addr *dest, struct ip_addr *src);
u8_t ip_addr_isany(struct ip_addr *addr);


#if IP_DEBUG
void ip_addr_debug_print(struct ip_addr *addr);
#endif /* IP_DEBUG */

#endif /* __LWIP_IP_ADDR_H__ */
