/**
 * @file
 * User Datagram Protocol module
 *
 */
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


/* udp.c
 *
 * The code for the User Datagram Protocol UDP.
 *
 */

#include <string.h>

#include "lwip/opt.h"

#include "lwip/def.h"
#include "lwip/memp.h"
#include "lwip/inet.h"
#include "lwip/ip_addr.h"
#include "lwip/netif.h"
#include "lwip/udp.h"
#include "lwip/icmp.h"

#include "lwip/stats.h"

#include "arch/perf.h"
#include "lwip/snmp.h"

/* The list of UDP PCBs */
#if LWIP_UDP
/* was static, but we may want to access this from a socket layer */
struct udp_pcb *udp_pcbs = NULL;

static struct udp_pcb *pcb_cache = NULL;


void
udp_init(void)
{
  udp_pcbs = pcb_cache = NULL;
}

/**
 * Process an incoming UDP datagram.
 *
 * Given an incoming UDP datagram (as a chain of pbufs) this function
 * finds a corresponding UDP PCB and
 *
 * @param pbuf pbuf to be demultiplexed to a UDP PCB.
 * @param netif network interface on which the datagram was received.
 *
 */
void
udp_input(struct pbuf *p, struct netif *inp)
{
  struct udp_hdr *udphdr;
  struct udp_pcb *pcb;
  struct ip_hdr *iphdr;
  u16_t src, dest;

#if SO_REUSE
  struct udp_pcb *pcb_temp;
  int reuse = 0;
  int reuse_port_1 = 0;
  int reuse_port_2 = 0;
#endif /* SO_REUSE */
  
  PERF_START;

  UDP_STATS_INC(udp.recv);

  iphdr = p->payload;

  if (pbuf_header(p, -((s16_t)(UDP_HLEN + IPH_HL(iphdr) * 4)))) {
    /* drop short packets */
    LWIP_DEBUGF(UDP_DEBUG, ("udp_input: short UDP datagram (%u bytes) discarded\n", p->tot_len));
    UDP_STATS_INC(udp.lenerr);
    UDP_STATS_INC(udp.drop);
    snmp_inc_udpinerrors();
    pbuf_free(p);
    goto end;
  }

  udphdr = (struct udp_hdr *)((u8_t *)p->payload - UDP_HLEN);

  LWIP_DEBUGF(UDP_DEBUG, ("udp_input: received datagram of length %u\n", p->tot_len));

  src = ntohs(udphdr->src);
  dest = ntohs(udphdr->dest);

  udp_debug_print(udphdr);

  /* print the UDP source and destination */
  LWIP_DEBUGF(UDP_DEBUG, ("udp (%u.%u.%u.%u, %u) <-- (%u.%u.%u.%u, %u)\n",
    ip4_addr1(&iphdr->dest), ip4_addr2(&iphdr->dest),
    ip4_addr3(&iphdr->dest), ip4_addr4(&iphdr->dest), ntohs(udphdr->dest),
    ip4_addr1(&iphdr->src), ip4_addr2(&iphdr->src),
    ip4_addr3(&iphdr->src), ip4_addr4(&iphdr->src), ntohs(udphdr->src)));

#if SO_REUSE
  pcb_temp = udp_pcbs;
  
 again_1:
  
  /* Iterate through the UDP pcb list for a fully matching pcb */
  for (pcb = pcb_temp; pcb != NULL; pcb = pcb->next) {
#else  /* SO_REUSE */ 
  /* Iterate through the UDP pcb list for a fully matching pcb */
  for (pcb = udp_pcbs; pcb != NULL; pcb = pcb->next) {
#endif  /* SO_REUSE */ 
    /* print the PCB local and remote address */
    LWIP_DEBUGF(UDP_DEBUG, ("pcb (%u.%u.%u.%u, %u) --- (%u.%u.%u.%u, %u)\n",
      ip4_addr1(&pcb->local_ip), ip4_addr2(&pcb->local_ip),
      ip4_addr3(&pcb->local_ip), ip4_addr4(&pcb->local_ip), pcb->local_port,
      ip4_addr1(&pcb->remote_ip), ip4_addr2(&pcb->remote_ip),
      ip4_addr3(&pcb->remote_ip), ip4_addr4(&pcb->remote_ip), pcb->remote_port));

       /* PCB remote port matches UDP source port? */
    if ((pcb->remote_port == src) &&
       /* PCB local port matches UDP destination port? */
       (pcb->local_port == dest) &&
       /* accepting from any remote (source) IP address? or... */
       (ip_addr_isany(&pcb->remote_ip) ||
       /* PCB remote IP address matches UDP source IP address? */
        ip_addr_cmp(&(pcb->remote_ip), &(iphdr->src))) &&
       /* accepting on any local (netif) IP address? or... */
       (ip_addr_isany(&pcb->local_ip) ||
       /* PCB local IP address matches UDP destination IP address? */
        ip_addr_cmp(&(pcb->local_ip), &(iphdr->dest)))) {
#if SO_REUSE
      if (pcb->so_options & SOF_REUSEPORT) {
        if(reuse) {
          /* We processed one PCB already */
          LWIP_DEBUGF(UDP_DEBUG, ("udp_input: second or later PCB and SOF_REUSEPORT set.\n"));
        } else {
          /* First PCB with this address */
          LWIP_DEBUGF(UDP_DEBUG, ("udp_input: first PCB and SOF_REUSEPORT set.\n"));
          reuse = 1;
        }
        
        reuse_port_1 = 1; 
        p->ref++;
        LWIP_DEBUGF(UDP_DEBUG, ("udp_input: reference counter on PBUF set to %i\n", p->ref));
      } else {
        if (reuse) {
          /* We processed one PCB already */
          LWIP_DEBUGF(UDP_DEBUG, ("udp_input: second or later PCB but SOF_REUSEPORT not set !\n"));
        }
      }
#endif /* SO_REUSE */
      break;
    }
  }
  /* no fully matching pcb found? then look for an unconnected pcb */
  if (pcb == NULL) {
    /* Iterate through the UDP PCB list for a pcb that matches
       the local address. */

#if SO_REUSE
    pcb_temp = udp_pcbs;
    
  again_2:

    for (pcb = pcb_temp; pcb != NULL; pcb = pcb->next) {
#else  /* SO_REUSE */ 
    for (pcb = udp_pcbs; pcb != NULL; pcb = pcb->next) {
#endif  /* SO_REUSE */ 
      LWIP_DEBUGF(UDP_DEBUG, ("pcb (%u.%u.%u.%u, %u) --- (%u.%u.%u.%u, %u)\n",
        ip4_addr1(&pcb->local_ip), ip4_addr2(&pcb->local_ip),
        ip4_addr3(&pcb->local_ip), ip4_addr4(&pcb->local_ip), pcb->local_port,
        ip4_addr1(&pcb->remote_ip), ip4_addr2(&pcb->remote_ip),
        ip4_addr3(&pcb->remote_ip), ip4_addr4(&pcb->remote_ip), pcb->remote_port));
      /* unconnected? */
      if (((pcb->flags & UDP_FLAGS_CONNECTED) == 0) &&
         /* destination port matches? */
        (pcb->local_port == dest) &&
        /* not bound to a specific (local) interface address? or... */
        (ip_addr_isany(&pcb->local_ip) ||
        /* ...matching interface address? */
        ip_addr_cmp(&(pcb->local_ip), &(iphdr->dest)))) {
#if SO_REUSE
        if (pcb->so_options & SOF_REUSEPORT) {
          if (reuse) {
            /* We processed one PCB already */
            LWIP_DEBUGF(UDP_DEBUG, ("udp_input: second or later PCB and SOF_REUSEPORT set.\n"));
          } else {
            /* First PCB with this address */
            LWIP_DEBUGF(UDP_DEBUG, ("udp_input: first PCB and SOF_REUSEPORT set.\n"));
            reuse = 1;
          }
          
          reuse_port_2 = 1; 
          p->ref++;
          LWIP_DEBUGF(UDP_DEBUG, ("udp_input: reference counter on PBUF set to %i\n", p->ref));
        } else {
          if (reuse) {
            /* We processed one PCB already */
            LWIP_DEBUGF(UDP_DEBUG, ("udp_input: second or later PCB but SOF_REUSEPORT not set !\n"));
          }
        }
#endif /* SO_REUSE */
        break;
      }
    }
  }

  /* Check checksum if this is a match or if it was directed at us. */
  if (pcb != NULL  || ip_addr_cmp(&inp->ip_addr, &iphdr->dest))
    {
    LWIP_DEBUGF(UDP_DEBUG | DBG_TRACE, ("udp_input: calculating checksum\n"));
    pbuf_header(p, UDP_HLEN);
#ifdef IPv6
    if (iphdr->nexthdr == IP_PROTO_UDPLITE) {
#else
    if (IPH_PROTO(iphdr) == IP_PROTO_UDPLITE) {
#endif /* IPv4 */
      /* Do the UDP Lite checksum */
#if CHECKSUM_CHECK_UDP
      if (inet_chksum_pseudo(p, (struct ip_addr *)&(iphdr->src),
         (struct ip_addr *)&(iphdr->dest),
         IP_PROTO_UDPLITE, ntohs(udphdr->len)) != 0) {
  LWIP_DEBUGF(UDP_DEBUG | 2, ("udp_input: UDP Lite datagram discarded due to failing checksum\n"));
  UDP_STATS_INC(udp.chkerr);
  UDP_STATS_INC(udp.drop);
  snmp_inc_udpinerrors();
  pbuf_free(p);
  goto end;
      }
#endif
    } else {
#if CHECKSUM_CHECK_UDP
      if (udphdr->chksum != 0) {
  if (inet_chksum_pseudo(p, (struct ip_addr *)&(iphdr->src),
       (struct ip_addr *)&(iphdr->dest),
        IP_PROTO_UDP, p->tot_len) != 0) {
    LWIP_DEBUGF(UDP_DEBUG | 2, ("udp_input: UDP datagram discarded due to failing checksum\n"));

    UDP_STATS_INC(udp.chkerr);
    UDP_STATS_INC(udp.drop);
    snmp_inc_udpinerrors();
    pbuf_free(p);
    goto end;
  }
      }
#endif
    }
    pbuf_header(p, -UDP_HLEN);
    if (pcb != NULL) {
      snmp_inc_udpindatagrams();
      pcb->recv(pcb->recv_arg, pcb, p, &(iphdr->src), src);
#if SO_REUSE
      /* First socket should receive now */
      if(reuse_port_1 || reuse_port_2) {
        /* We want to search on next socket after receiving */
        pcb_temp = pcb->next;
        
        if(reuse_port_1) {
          /* We are searching connected sockets */
          reuse_port_1 = 0;
          reuse_port_2 = 0;
          goto again_1;
        } else {
          /* We are searching unconnected sockets */
          reuse_port_1 = 0;
          reuse_port_2 = 0;
          goto again_2;
        }
      }
#endif /* SO_REUSE */ 
    } else {
#if SO_REUSE
      if(reuse) {
        LWIP_DEBUGF(UDP_DEBUG, ("udp_input: freeing PBUF with reference counter set to %i\n", p->ref));
        pbuf_free(p);
        goto end;
      }
#endif /* SO_REUSE */
      LWIP_DEBUGF(UDP_DEBUG | DBG_TRACE, ("udp_input: not for us.\n"));

      /* No match was found, send ICMP destination port unreachable unless
      destination address was broadcast/multicast. */

      if (!ip_addr_isbroadcast(&iphdr->dest, inp) &&
          !ip_addr_ismulticast(&iphdr->dest)) {

  /* adjust pbuf pointer */
  p->payload = iphdr;
  icmp_dest_unreach(p, ICMP_DUR_PORT);
      }
      UDP_STATS_INC(udp.proterr);
      UDP_STATS_INC(udp.drop);
    snmp_inc_udpnoports();
      pbuf_free(p);
    }
  } else {
    pbuf_free(p);
  }
  end:

  PERF_STOP("udp_input");
}

/**
 * Send data to a specified address using UDP.
 *
 * @param pcb UDP PCB used to send the data.
 * @param pbuf chain of pbuf's to be sent.
 * @param dst_ip Destination IP address.
 * @param dst_port Destination UDP port.
 *
 * If the PCB already has a remote address association, it will
 * be restored after the data is sent.
 * 
 * @return lwIP error code.
 * - ERR_OK. Successful. No error occured.
 * - ERR_MEM. Out of memory.
 * - ERR_RTE. Could not find route to destination address.
 *
 * @see udp_disconnect() udp_send()
 */
err_t
udp_sendto(struct udp_pcb *pcb, struct pbuf *p,
  struct ip_addr *dst_ip, u16_t dst_port)
{
  err_t err;
  /* temporary space for current PCB remote address */
  struct ip_addr pcb_remote_ip;
  u16_t pcb_remote_port;
  /* remember current remote peer address of PCB */
  pcb_remote_ip.addr = pcb->remote_ip.addr;
  pcb_remote_port = pcb->remote_port;
  /* copy packet destination address to PCB remote peer address */
  pcb->remote_ip.addr = dst_ip->addr;
  pcb->remote_port = dst_port;
  /* send to the packet destination address */
  err = udp_send(pcb, p);
  /* restore PCB remote peer address */
  pcb->remote_ip.addr = pcb_remote_ip.addr;
  pcb->remote_port = pcb_remote_port;
  return err;
}

/**
 * Send data using UDP.
 *
 * @param pcb UDP PCB used to send the data.
 * @param pbuf chain of pbuf's to be sent.
 *
 * @return lwIP error code.
 * - ERR_OK. Successful. No error occured.
 * - ERR_MEM. Out of memory.
 * - ERR_RTE. Could not find route to destination address.
 *
 * @see udp_disconnect() udp_sendto()
 */
err_t
udp_send(struct udp_pcb *pcb, struct pbuf *p)
{
  struct udp_hdr *udphdr;
  struct netif *netif;
  struct ip_addr *src_ip;
  err_t err;
  struct pbuf *q; /* q will be sent down the stack */

  LWIP_DEBUGF(UDP_DEBUG | DBG_TRACE | 3, ("udp_send\n"));

  /* if the PCB is not yet bound to a port, bind it here */
  if (pcb->local_port == 0) {
    LWIP_DEBUGF(UDP_DEBUG | DBG_TRACE | 2, ("udp_send: not yet bound to a port, binding now\n"));
    err = udp_bind(pcb, &pcb->local_ip, pcb->local_port);
    if (err != ERR_OK) {
      LWIP_DEBUGF(UDP_DEBUG | DBG_TRACE | 2, ("udp_send: forced port bind failed\n"));
      return err;
    }
  }

  /* not enough space to add an UDP header to first pbuf in given p chain? */
  if (pbuf_header(p, UDP_HLEN)) {
    /* allocate header in a seperate new pbuf */
    q = pbuf_alloc(PBUF_IP, UDP_HLEN, PBUF_RAM);
    /* new header pbuf could not be allocated? */
    if (q == NULL) {
      LWIP_DEBUGF(UDP_DEBUG | DBG_TRACE | 2, ("udp_send: could not allocate header\n"));
      return ERR_MEM;
    }
    /* chain header q in front of given pbuf p */
    pbuf_chain(q, p);
    /* { first pbuf q points to header pbuf } */
    LWIP_DEBUGF(UDP_DEBUG, ("udp_send: added header pbuf %p before given pbuf %p\n", (void *)q, (void *)p));
  /* adding a header within p succeeded */
  } else {
    /* first pbuf q equals given pbuf */
    q = p;
    LWIP_DEBUGF(UDP_DEBUG, ("udp_send: added header in given pbuf %p\n", (void *)p));
  }
  /* { q now represents the packet to be sent } */
  udphdr = q->payload;
  udphdr->src = htons(pcb->local_port);
  udphdr->dest = htons(pcb->remote_port);
  /* in UDP, 0 checksum means 'no checksum' */
  udphdr->chksum = 0x0000; 

  /* find the outgoing network interface for this packet */
  netif = ip_route(&(pcb->remote_ip));
  /* no outgoing network interface could be found? */
  if (netif == NULL) {
    LWIP_DEBUGF(UDP_DEBUG | 1, ("udp_send: No route to 0x%lx\n", pcb->remote_ip.addr));
    UDP_STATS_INC(udp.rterr);
    return ERR_RTE;
  }
  /* PCB local address is IP_ANY_ADDR? */
  if (ip_addr_isany(&pcb->local_ip)) {
    /* use outgoing network interface IP address as source address */
    src_ip = &(netif->ip_addr);
  } else {
    /* use UDP PCB local IP address as source address */
    src_ip = &(pcb->local_ip);
  }

  LWIP_DEBUGF(UDP_DEBUG, ("udp_send: sending datagram of length %u\n", q->tot_len));

  /* UDP Lite protocol? */
  if (pcb->flags & UDP_FLAGS_UDPLITE) {
    LWIP_DEBUGF(UDP_DEBUG, ("udp_send: UDP LITE packet length %u\n", q->tot_len));
    /* set UDP message length in UDP header */
    udphdr->len = htons(pcb->chksum_len);
    /* calculate checksum */
#if CHECKSUM_GEN_UDP
    udphdr->chksum = inet_chksum_pseudo(q, src_ip, &(pcb->remote_ip),
          IP_PROTO_UDP, pcb->chksum_len);
    /* chksum zero must become 0xffff, as zero means 'no checksum' */
    if (udphdr->chksum == 0x0000) udphdr->chksum = 0xffff;
#else
    udphdr->chksum = 0x0000;
#endif
    /* output to IP */
    LWIP_DEBUGF(UDP_DEBUG, ("udp_send: ip_output_if (,,,,IP_PROTO_UDPLITE,)\n"));
    err = ip_output_if (q, src_ip, &pcb->remote_ip, pcb->ttl, pcb->tos, IP_PROTO_UDPLITE, netif);    
  /* UDP */
  } else {
    LWIP_DEBUGF(UDP_DEBUG, ("udp_send: UDP packet length %u\n", q->tot_len));
    udphdr->len = htons(q->tot_len);
    /* calculate checksum */
#if CHECKSUM_GEN_UDP
    if ((pcb->flags & UDP_FLAGS_NOCHKSUM) == 0) {
      udphdr->chksum = inet_chksum_pseudo(q, src_ip, &pcb->remote_ip, IP_PROTO_UDP, q->tot_len);
      /* chksum zero must become 0xffff, as zero means 'no checksum' */
      if (udphdr->chksum == 0x0000) udphdr->chksum = 0xffff;
    }
#else
    udphdr->chksum = 0x0000;
#endif
    LWIP_DEBUGF(UDP_DEBUG, ("udp_send: UDP checksum 0x%04x\n", udphdr->chksum));
    LWIP_DEBUGF(UDP_DEBUG, ("udp_send: ip_output_if (,,,,IP_PROTO_UDP,)\n"));
    /* output to IP */
    err = ip_output_if(q, src_ip, &pcb->remote_ip, pcb->ttl, pcb->tos, IP_PROTO_UDP, netif);    
  }
  /* TODO: must this be increased even if error occured? */
  snmp_inc_udpoutdatagrams();

  /* did we chain a seperate header pbuf earlier? */
  if (q != p) {
    /* free the header pbuf */
    pbuf_free(q); q = NULL;
    /* { p is still referenced by the caller, and will live on } */
  }

  UDP_STATS_INC(udp.xmit);
  return err;
}

/**
 * Bind an UDP PCB.
 *
 * @param pcb UDP PCB to be bound with a local address ipaddr and port.
 * @param ipaddr local IP address to bind with. Use IP_ADDR_ANY to
 * bind to all local interfaces.
 * @param port local UDP port to bind with.
 *
 * @return lwIP error code.
 * - ERR_OK. Successful. No error occured.
 * - ERR_USE. The specified ipaddr and port are already bound to by
 * another UDP PCB.
 *
 * @see udp_disconnect()
 */
err_t
udp_bind(struct udp_pcb *pcb, struct ip_addr *ipaddr, u16_t port)
{
  struct udp_pcb *ipcb;
  u8_t rebind;
#if SO_REUSE
  int reuse_port_all_set = 1;
#endif /* SO_REUSE */
  LWIP_DEBUGF(UDP_DEBUG | DBG_TRACE | 3, ("udp_bind(ipaddr = "));
  ip_addr_debug_print(UDP_DEBUG, ipaddr);
  LWIP_DEBUGF(UDP_DEBUG | DBG_TRACE | 3, (", port = %u)\n", port));

  rebind = 0;
  /* Check for double bind and rebind of the same pcb */
  for (ipcb = udp_pcbs; ipcb != NULL; ipcb = ipcb->next) {
    /* is this UDP PCB already on active list? */
    if (pcb == ipcb) {
      /* pcb may occur at most once in active list */
      LWIP_ASSERT("rebind == 0", rebind == 0);
      /* pcb already in list, just rebind */
      rebind = 1;
    }

#if SO_REUSE == 0
/* this code does not allow upper layer to share a UDP port for
   listening to broadcast or multicast traffic (See SO_REUSE_ADDR and
   SO_REUSE_PORT under *BSD). TODO: See where it fits instead, OR
   combine with implementation of UDP PCB flags. Leon Woestenberg. */
#ifdef LWIP_UDP_TODO
    /* port matches that of PCB in list? */
    else if ((ipcb->local_port == port) &&
       /* IP address matches, or one is IP_ADDR_ANY? */
       (ip_addr_isany(&(ipcb->local_ip)) ||
       ip_addr_isany(ipaddr) ||
       ip_addr_cmp(&(ipcb->local_ip), ipaddr))) {
      /* other PCB already binds to this local IP and port */
      LWIP_DEBUGF(UDP_DEBUG, ("udp_bind: local port %u already bound by another pcb\n", port));
      return ERR_USE;
    }
#endif

#else /* SO_REUSE */
      /* Search through list of PCB's. 
         
      If there is a PCB bound to specified port and IP_ADDR_ANY another PCB can be bound to the interface IP
      or to the loopback address on the same port if SOF_REUSEADDR is set. Any combination of PCB's bound to 
      the same local port, but to one address out of {IP_ADDR_ANY, 127.0.0.1, interface IP} at a time is valid.
      But no two PCB's bound to same local port and same local address is valid.
      
      If SOF_REUSEPORT is set several PCB's can be bound to same local port and same local address also. But then 
      all PCB's must have the SOF_REUSEPORT option set.
      
      When the two options aren't set and specified port is already bound, ERR_USE is returned saying that 
      address is already in use. */
    else if (ipcb->local_port == port) {
      if(ip_addr_cmp(&(ipcb->local_ip), ipaddr)) {
        if(pcb->so_options & SOF_REUSEPORT) {
          LWIP_DEBUGF(UDP_DEBUG, ("udp_bind: in UDP PCB's SO_REUSEPORT set and same address.\n"));
          reuse_port_all_set = (reuse_port_all_set && (ipcb->so_options & SOF_REUSEPORT));
        }
        else {
          LWIP_DEBUGF(UDP_DEBUG, ("udp_bind: in UDP PCB's SO_REUSEPORT not set and same address.\n"));
          return ERR_USE;
        }
      }
      else if((ip_addr_isany(ipaddr) && !ip_addr_isany(&(ipcb->local_ip))) ||
              (!ip_addr_isany(ipaddr) && ip_addr_isany(&(ipcb->local_ip)))) {
        if(!(pcb->so_options & SOF_REUSEADDR) && !(pcb->so_options & SOF_REUSEPORT)) {
          LWIP_DEBUGF(UDP_DEBUG, ("udp_bind: in UDP PCB's SO_REUSEPORT or SO_REUSEADDR not set and not the same address.\n"));
          return ERR_USE;
        }           
      }
    }
#endif /* SO_REUSE */

  }

#if SO_REUSE
  /* If SOF_REUSEPORT isn't set in all PCB's bound to specified port and local address specified then 
     {IP, port} can't be reused. */
  if(!reuse_port_all_set) {
    LWIP_DEBUGF(UDP_DEBUG, ("udp_bind: not all sockets have SO_REUSEPORT set.\n"));
    return ERR_USE;
  }
#endif /* SO_REUSE */

  ip_addr_set(&pcb->local_ip, ipaddr);
  /* no port specified? */
  if (port == 0) {
#ifndef UDP_LOCAL_PORT_RANGE_START
#define UDP_LOCAL_PORT_RANGE_START 4096
#define UDP_LOCAL_PORT_RANGE_END   0x7fff
#endif
    port = UDP_LOCAL_PORT_RANGE_START;
    ipcb = udp_pcbs;
    while ((ipcb != NULL) && (port != UDP_LOCAL_PORT_RANGE_END)) {
      if (ipcb->local_port == port) {
        port++;
        ipcb = udp_pcbs;
      } else
        ipcb = ipcb->next;
    }
    if (ipcb != NULL) {
      /* no more ports available in local range */
      LWIP_DEBUGF(UDP_DEBUG, ("udp_bind: out of free UDP ports\n"));
      return ERR_USE;
    }
  }
  pcb->local_port = port;
  /* pcb not active yet? */
  if (rebind == 0) {
    /* place the PCB on the active list if not already there */
    pcb->next = udp_pcbs;
    udp_pcbs = pcb;
  }
  LWIP_DEBUGF(UDP_DEBUG | DBG_TRACE | DBG_STATE, ("udp_bind: bound to %u.%u.%u.%u, port %u\n",
   (unsigned int)(ntohl(pcb->local_ip.addr) >> 24 & 0xff),
   (unsigned int)(ntohl(pcb->local_ip.addr) >> 16 & 0xff),
   (unsigned int)(ntohl(pcb->local_ip.addr) >> 8 & 0xff),
   (unsigned int)(ntohl(pcb->local_ip.addr) & 0xff), pcb->local_port));
  return ERR_OK;
}
/**
 * Connect an UDP PCB.
 *
 * This will associate the UDP PCB with the remote address.
 *
 * @param pcb UDP PCB to be connected with remote address ipaddr and port.
 * @param ipaddr remote IP address to connect with.
 * @param port remote UDP port to connect with.
 *
 * @return lwIP error code
 *
 * @see udp_disconnect()
 */
err_t
udp_connect(struct udp_pcb *pcb, struct ip_addr *ipaddr, u16_t port)
{
  struct udp_pcb *ipcb;

  if (pcb->local_port == 0) {
    err_t err = udp_bind(pcb, &pcb->local_ip, pcb->local_port);
    if (err != ERR_OK)
      return err;
  }

  ip_addr_set(&pcb->remote_ip, ipaddr);
  pcb->remote_port = port;
  pcb->flags |= UDP_FLAGS_CONNECTED;
/** TODO: this functionality belongs in upper layers */
#ifdef LWIP_UDP_TODO
  /* Nail down local IP for netconn_addr()/getsockname() */
  if (ip_addr_isany(&pcb->local_ip) && !ip_addr_isany(&pcb->remote_ip)) {
    struct netif *netif;

    if ((netif = ip_route(&(pcb->remote_ip))) == NULL) {
      LWIP_DEBUGF(UDP_DEBUG, ("udp_connect: No route to 0x%lx\n", pcb->remote_ip.addr));
        UDP_STATS_INC(udp.rterr);
      return ERR_RTE;
    }
    /** TODO: this will bind the udp pcb locally, to the interface which
        is used to route output packets to the remote address. However, we
        might want to accept incoming packets on any interface! */
    pcb->local_ip = netif->ip_addr;
  } else if (ip_addr_isany(&pcb->remote_ip)) {
    pcb->local_ip.addr = 0;
  }
#endif
  LWIP_DEBUGF(UDP_DEBUG | DBG_TRACE | DBG_STATE, ("udp_connect: connected to %u.%u.%u.%u, port %u\n",
   (unsigned int)(ntohl(pcb->remote_ip.addr) >> 24 & 0xff),
   (unsigned int)(ntohl(pcb->remote_ip.addr) >> 16 & 0xff),
   (unsigned int)(ntohl(pcb->remote_ip.addr) >> 8 & 0xff),
   (unsigned int)(ntohl(pcb->remote_ip.addr) & 0xff), pcb->remote_port));

  /* Insert UDP PCB into the list of active UDP PCBs. */
  for(ipcb = udp_pcbs; ipcb != NULL; ipcb = ipcb->next) {
    if (pcb == ipcb) {
      /* already on the list, just return */
      return ERR_OK;
    }
  }
  /* PCB not yet on the list, add PCB now */
  pcb->next = udp_pcbs;
  udp_pcbs = pcb;
  return ERR_OK;
}

void
udp_disconnect(struct udp_pcb *pcb)
{
  /* reset remote address association */
  ip_addr_set(&pcb->remote_ip, IP_ADDR_ANY);
  pcb->remote_port = 0;
  /* mark PCB as unconnected */
  pcb->flags &= ~UDP_FLAGS_CONNECTED;
}

void
udp_recv(struct udp_pcb *pcb,
   void (* recv)(void *arg, struct udp_pcb *upcb, struct pbuf *p,
           struct ip_addr *addr, u16_t port),
   void *recv_arg)
{
  /* remember recv() callback and user data */
  pcb->recv = recv;
  pcb->recv_arg = recv_arg;
}
/**
 * Remove an UDP PCB.
 *
 * @param pcb UDP PCB to be removed. The PCB is removed from the list of
 * UDP PCB's and the data structure is freed from memory.
 *
 * @see udp_new()
 */
void
udp_remove(struct udp_pcb *pcb)
{
  struct udp_pcb *pcb2;
  /* pcb to be removed is first in list? */
  if (udp_pcbs == pcb) {
    /* make list start at 2nd pcb */
    udp_pcbs = udp_pcbs->next;
  /* pcb not 1st in list */
  } else for(pcb2 = udp_pcbs; pcb2 != NULL; pcb2 = pcb2->next) {
    /* find pcb in udp_pcbs list */
    if (pcb2->next != NULL && pcb2->next == pcb) {
      /* remove pcb from list */
      pcb2->next = pcb->next;
    }
  }
  memp_free(MEMP_UDP_PCB, pcb);
}
/**
 * Create a UDP PCB.
 *
 * @return The UDP PCB which was created. NULL if the PCB data structure
 * could not be allocated.
 *
 * @see udp_remove()
 */
struct udp_pcb *
udp_new(void) {
  struct udp_pcb *pcb;
  pcb = memp_malloc(MEMP_UDP_PCB);
  /* could allocate UDP PCB? */
  if (pcb != NULL) {
    /* initialize PCB to all zeroes */
    memset(pcb, 0, sizeof(struct udp_pcb));
    pcb->ttl = UDP_TTL;
  }
  
  
  return pcb;
}

#if UDP_DEBUG
int
udp_debug_print(struct udp_hdr *udphdr)
{
  LWIP_DEBUGF(UDP_DEBUG, ("UDP header:\n"));
  LWIP_DEBUGF(UDP_DEBUG, ("+-------------------------------+\n"));
  LWIP_DEBUGF(UDP_DEBUG, ("|     %5u     |     %5u     | (src port, dest port)\n",
         ntohs(udphdr->src), ntohs(udphdr->dest)));
  LWIP_DEBUGF(UDP_DEBUG, ("+-------------------------------+\n"));
  LWIP_DEBUGF(UDP_DEBUG, ("|     %5u     |     0x%04x    | (len, chksum)\n",
         ntohs(udphdr->len), ntohs(udphdr->chksum)));
  LWIP_DEBUGF(UDP_DEBUG, ("+-------------------------------+\n"));
  return 0;
}
#endif /* UDP_DEBUG */

#endif /* LWIP_UDP */









