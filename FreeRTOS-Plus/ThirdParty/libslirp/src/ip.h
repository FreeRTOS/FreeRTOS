/* SPDX-License-Identifier: BSD-3-Clause */
/*
 * Copyright (c) 1982, 1986, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	@(#)ip.h	8.1 (Berkeley) 6/10/93
 * ip.h,v 1.3 1994/08/21 05:27:30 paul Exp
 */

#ifndef IP_H
#define IP_H

#include <glib.h>

#if G_BYTE_ORDER == G_BIG_ENDIAN
#undef NTOHL
#undef NTOHS
#undef HTONL
#undef HTONS
#define NTOHL(d)
#define NTOHS(d)
#define HTONL(d)
#define HTONS(d)
#else
#ifndef NTOHL
#define NTOHL(d) ((d) = ntohl((d)))
#endif
#ifndef NTOHS
#define NTOHS(d) ((d) = ntohs((uint16_t)(d)))
#endif
#ifndef HTONL
#define HTONL(d) ((d) = htonl((d)))
#endif
#ifndef HTONS
#define HTONS(d) ((d) = htons((uint16_t)(d)))
#endif
#endif

typedef uint32_t n_long; /* long as received from the net */

/*
 * Definitions for internet protocol version 4.
 * Per RFC 791, September 1981.
 */
#define IPVERSION 4

/*
 * Structure of an internet header, naked of options.
 */
SLIRP_PACKED_BEGIN
struct ip {
#if (G_BYTE_ORDER == G_BIG_ENDIAN) && !defined(_MSC_VER)
    uint8_t ip_v : 4, /* version */
        ip_hl : 4; /* header length */
#else
    uint8_t ip_hl : 4, /* header length */
        ip_v : 4; /* version */
#endif
    uint8_t ip_tos; /* type of service */
    uint16_t ip_len; /* total length */
    uint16_t ip_id; /* identification */
    uint16_t ip_off; /* fragment offset field */
#define IP_DF 0x4000 /* don't fragment flag */
#define IP_MF 0x2000 /* more fragments flag */
#define IP_OFFMASK 0x1fff /* mask for fragmenting bits */
    uint8_t ip_ttl; /* time to live */
    uint8_t ip_p; /* protocol */
    uint16_t ip_sum; /* checksum */
    struct in_addr ip_src, ip_dst; /* source and dest address */
} SLIRP_PACKED_END;

#define IP_MAXPACKET 65535 /* maximum packet size */

/*
 * Definitions for IP type of service (ip_tos)
 */
#define IPTOS_LOWDELAY 0x10
#define IPTOS_THROUGHPUT 0x08
#define IPTOS_RELIABILITY 0x04

/*
 * Definitions for options.
 */
#define IPOPT_COPIED(o) ((o)&0x80)
#define IPOPT_CLASS(o) ((o)&0x60)
#define IPOPT_NUMBER(o) ((o)&0x1f)

#define IPOPT_CONTROL 0x00
#define IPOPT_RESERVED1 0x20
#define IPOPT_DEBMEAS 0x40
#define IPOPT_RESERVED2 0x60

#define IPOPT_EOL 0 /* end of option list */
#define IPOPT_NOP 1 /* no operation */

#define IPOPT_RR 7 /* record packet route */
#define IPOPT_TS 68 /* timestamp */
#define IPOPT_SECURITY 130 /* provide s,c,h,tcc */
#define IPOPT_LSRR 131 /* loose source route */
#define IPOPT_SATID 136 /* satnet id */
#define IPOPT_SSRR 137 /* strict source route */

/*
 * Offsets to fields in options other than EOL and NOP.
 */
#define IPOPT_OPTVAL 0 /* option ID */
#define IPOPT_OLEN 1 /* option length */
#define IPOPT_OFFSET 2 /* offset within option */
#define IPOPT_MINOFF 4 /* min value of above */

/*
 * Time stamp option structure.
 */
SLIRP_PACKED_BEGIN
struct ip_timestamp {
    uint8_t ipt_code; /* IPOPT_TS */
    uint8_t ipt_len; /* size of structure (variable) */
    uint8_t ipt_ptr; /* index of current entry */
#if (G_BYTE_ORDER == G_BIG_ENDIAN) && !defined(_MSC_VER)
    uint8_t ipt_oflw : 4, /* overflow counter */
        ipt_flg : 4; /* flags, see below */
#else
    uint8_t ipt_flg : 4, /* flags, see below */
        ipt_oflw : 4; /* overflow counter */
#endif
    union ipt_timestamp {
        n_long ipt_time[1];
        struct ipt_ta {
            struct in_addr ipt_addr;
            n_long ipt_time;
        } ipt_ta[1];
    } ipt_timestamp;
} SLIRP_PACKED_END;

/* flag bits for ipt_flg */
#define IPOPT_TS_TSONLY 0 /* timestamps only */
#define IPOPT_TS_TSANDADDR 1 /* timestamps and addresses */
#define IPOPT_TS_PRESPEC 3 /* specified modules only */

/* bits for security (not byte swapped) */
#define IPOPT_SECUR_UNCLASS 0x0000
#define IPOPT_SECUR_CONFID 0xf135
#define IPOPT_SECUR_EFTO 0x789a
#define IPOPT_SECUR_MMMM 0xbc4d
#define IPOPT_SECUR_RESTR 0xaf13
#define IPOPT_SECUR_SECRET 0xd788
#define IPOPT_SECUR_TOPSECRET 0x6bc5

/*
 * Internet implementation parameters.
 */
#define MAXTTL 255 /* maximum time to live (seconds) */
#define IPDEFTTL 64 /* default ttl, from RFC 1340 */
#define IPFRAGTTL 60 /* time to live for frags, slowhz */
#define IPTTLDEC 1 /* subtracted when forwarding */

#define IP_MSS 576 /* default maximum segment size */

#if GLIB_SIZEOF_VOID_P == 4
SLIRP_PACKED_BEGIN
struct mbuf_ptr {
    struct mbuf *mptr;
    uint32_t dummy;
} SLIRP_PACKED_END;
#else
SLIRP_PACKED_BEGIN
struct mbuf_ptr {
    struct mbuf *mptr;
} SLIRP_PACKED_END;
#endif
struct qlink {
    void *next, *prev;
};

/*
 * Overlay for ip header used by other protocols (tcp, udp).
 */
SLIRP_PACKED_BEGIN
struct ipovly {
    struct mbuf_ptr ih_mbuf; /* backpointer to mbuf */
    uint8_t ih_x1; /* (unused) */
    uint8_t ih_pr; /* protocol */
    uint16_t ih_len; /* protocol length */
    struct in_addr ih_src; /* source internet address */
    struct in_addr ih_dst; /* destination internet address */
} SLIRP_PACKED_END;

/*
 * Ip reassembly queue structure.  Each fragment
 * being reassembled is attached to one of these structures.
 * They are timed out after ipq_ttl drops to 0, and may also
 * be reclaimed if memory becomes tight.
 */
struct ipq {
    struct qlink ip_link; /* to other reass headers */
    uint8_t ipq_ttl; /* time for reass q to live */
    uint8_t ipq_p; /* protocol of this fragment */
    uint16_t ipq_id; /* sequence id for reassembly */
    struct in_addr ipq_src, ipq_dst;
};

struct ipas {
    struct qlink link;
    union {
        struct ipq ipq;
        struct ip ipf_ip;
    };
};

#define ipf_off ipf_ip.ip_off
#define ipf_tos ipf_ip.ip_tos
#define ipf_len ipf_ip.ip_len

#endif
