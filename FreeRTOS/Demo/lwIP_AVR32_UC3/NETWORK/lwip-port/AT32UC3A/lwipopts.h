/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief lwIP configuration for AVR32 UC3.
 *
 * - Compiler:           GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices can be used.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support and FAQ: http://support.atmel.no/
 *
 *****************************************************************************/

/* Copyright (c) 2007, Atmel Corporation All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. The name of ATMEL may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE EXPRESSLY AND
 * SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */



#ifndef __LWIPOPTS_H__
#define __LWIPOPTS_H__

/* Include user defined options first */
#include "conf_eth.h"
// #include "lwip/debug.h"

/* Define default values for unconfigured parameters. */
#define LWIP_NOASSERT 1 // To suppress some errors for now (no debug output)

/* These two control is reclaimer functions should be compiled
   in. Should always be turned on (1). */
#define MEM_RECLAIM             1
#define MEMP_RECLAIM            1


/* Platform specific locking */

/*
 * enable SYS_LIGHTWEIGHT_PROT in lwipopts.h if you want inter-task protection
 * for certain critical regions during buffer allocation, deallocation and memory
 * allocation and deallocation.
 */
#define SYS_LIGHTWEIGHT_PROT            1

/* ---------- Memory options ---------- */
// #define MEM_LIBC_MALLOC                 0

/* MEM_ALIGNMENT: should be set to the alignment of the CPU for which
   lwIP is compiled. 4 byte alignment -> define MEM_ALIGNMENT to 4, 2
   byte alignment -> define MEM_ALIGNMENT to 2. */
#define MEM_ALIGNMENT           4

/* MEM_SIZE: the size of the heap memory. If the application will send
a lot of data that needs to be copied, this should be set high. */
#define MEM_SIZE                3 * 1024

// #define MEMP_SANITY_CHECK       1

/* MEMP_NUM_PBUF: the number of memp struct pbufs. If the application
   sends a lot of data out of ROM (or other static memory), this
   should be set high. */
#define MEMP_NUM_PBUF           6

/* Number of raw connection PCBs */
#define MEMP_NUM_RAW_PCB                1

#if (TFTP_USED == 1)
  /* ---------- UDP options ---------- */
  #define LWIP_UDP                1
  #define UDP_TTL                 255
  /* MEMP_NUM_UDP_PCB: the number of UDP protocol control blocks. One
     per active UDP "connection". */

  #define MEMP_NUM_UDP_PCB        1
#else
  /* ---------- UDP options ---------- */
  #define LWIP_UDP                0
  #define UDP_TTL                 0
  /* MEMP_NUM_UDP_PCB: the number of UDP protocol control blocks. One
     per active UDP "connection". */

  #define MEMP_NUM_UDP_PCB        0
#endif

/* MEMP_NUM_TCP_PCB: the number of simulatenously active TCP
   connections. */
#define MEMP_NUM_TCP_PCB        14
/* MEMP_NUM_TCP_PCB_LISTEN: the number of listening TCP
   connections. */
#define MEMP_NUM_TCP_PCB_LISTEN 2
/* MEMP_NUM_TCP_SEG: the number of simultaneously queued TCP
   segments. */
#define MEMP_NUM_TCP_SEG        6
/* MEMP_NUM_SYS_TIMEOUT: the number of simulateously active
   timeouts. */
#define MEMP_NUM_SYS_TIMEOUT    6

/* The following four are used only with the sequential API and can be
   set to 0 if the application only will use the raw API. */
/* MEMP_NUM_NETBUF: the number of struct netbufs. */
#define MEMP_NUM_NETBUF         3
/* MEMP_NUM_NETCONN: the number of struct netconns. */
#define MEMP_NUM_NETCONN        6
/* MEMP_NUM_APIMSG: the number of struct api_msg, used for
   communication between the TCP/IP stack and the sequential
   programs. */
#define MEMP_NUM_API_MSG        4
/* MEMP_NUM_TCPIPMSG: the number of struct tcpip_msg, which is used
   for sequential API communication and incoming packets. Used in
   src/api/tcpip.c. */
#define MEMP_NUM_TCPIP_MSG      4


/* ---------- Pbuf options ---------- */
/* PBUF_POOL_SIZE: the number of buffers in the pbuf pool. */

#define PBUF_POOL_SIZE          6

/* PBUF_POOL_BUFSIZE: the size of each pbuf in the pbuf pool. */

#define PBUF_POOL_BUFSIZE       500

/* PBUF_LINK_HLEN: the number of bytes that should be allocated for a
   link level header. */
#define PBUF_LINK_HLEN          16

/* ---------- TCP options ---------- */
#define LWIP_TCP                1
#define TCP_TTL                 255
/* TCP receive window. */
#define TCP_WND                 1500
/* Controls if TCP should queue segments that arrive out of
   order. Define to 0 if your device is low on memory. */
#define TCP_QUEUE_OOSEQ         1

/* TCP Maximum segment size. */
#define TCP_MSS                 1500

/* TCP sender buffer space (bytes). */
#define TCP_SND_BUF             2150

/* TCP sender buffer space (pbufs). This must be at least = 2 *
   TCP_SND_BUF/TCP_MSS for things to work. */
#define TCP_SND_QUEUELEN        6 * TCP_SND_BUF/TCP_MSS



/* Maximum number of retransmissions of data segments. */
#define TCP_MAXRTX              12

/* Maximum number of retransmissions of SYN segments. */
#define TCP_SYNMAXRTX           4

/* ---------- ARP options ---------- */
#define ARP_TABLE_SIZE 10
#define ARP_QUEUEING 0

/* ---------- IP options ---------- */
/* Define IP_FORWARD to 1 if you wish to have the ability to forward
   IP packets across network interfaces. If you are going to run lwIP
   on a device with only one network interface, define this to 0. */
#define IP_FORWARD              0

/* If defined to 1, IP options are allowed (but not parsed). If
   defined to 0, all packets with IP options are dropped. */
#define IP_OPTIONS              1

/* ---------- ICMP options ---------- */
#define ICMP_TTL                255


/* ---------- DHCP options ---------- */
/* Define LWIP_DHCP to 1 if you want DHCP configuration of
   interfaces. DHCP is not implemented in lwIP 0.5.1, however, so
   turning this on does currently not work. */
#define LWIP_DHCP               0

/* 1 if you want to do an ARP check on the offered address
   (recommended). */
#define DHCP_DOES_ARP_CHECK     1

#define TCPIP_THREAD_PRIO               lwipINTERFACE_TASK_PRIORITY

/* ---------- Statistics options ---------- */
#define LWIP_STATS 1

#define LWIP_STATS_DISPLAY 1

#if LWIP_STATS
#define LINK_STATS 1
#define IP_STATS   1
#define ICMP_STATS 1
#define UDP_STATS  1
#define TCP_STATS  1
#define MEM_STATS  1
#define MEMP_STATS 1
#define PBUF_STATS 1
#define SYS_STATS  1
#endif /* STATS */


#endif /* __LWIPOPTS_H__ */
