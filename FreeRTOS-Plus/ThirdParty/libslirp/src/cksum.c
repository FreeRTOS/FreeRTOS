/* SPDX-License-Identifier: BSD-3-Clause */
/*
 * Copyright (c) 1988, 1992, 1993
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
 *	@(#)in_cksum.c	8.1 (Berkeley) 6/10/93
 * in_cksum.c,v 1.2 1994/08/02 07:48:16 davidg Exp
 */

#include "slirp.h"

/*
 * Checksum routine for Internet Protocol family headers (Portable Version).
 *
 * This routine is very heavily used in the network
 * code and should be modified for each CPU to be as fast as possible.
 *
 * XXX Since we will never span more than 1 mbuf, we can optimise this
 */

#define ADDCARRY(x) (x > 65535 ? x -= 65535 : x)
#define REDUCE                           \
    {                                    \
        l_util.l = sum;                  \
        sum = l_util.s[0] + l_util.s[1]; \
        ADDCARRY(sum);                   \
    }

int cksum(struct mbuf *m, int len)
{
    register uint16_t *w;
    register int sum = 0;
    register int mlen = 0;
    int byte_swapped = 0;

    union {
        uint8_t c[2];
        uint16_t s;
    } s_util;
    union {
        uint16_t s[2];
        uint32_t l;
    } l_util;

    if (m->m_len == 0)
        goto cont;
    w = mtod(m, uint16_t *);

    mlen = m->m_len;

    if (len < mlen)
        mlen = len;
    len -= mlen;
    /*
     * Force to even boundary.
     */
    if ((1 & (uintptr_t)w) && (mlen > 0)) {
        REDUCE;
        sum <<= 8;
        s_util.c[0] = *(uint8_t *)w;
        w = (uint16_t *)((int8_t *)w + 1);
        mlen--;
        byte_swapped = 1;
    }
    /*
     * Unroll the loop to make overhead from
     * branches &c small.
     */
    while ((mlen -= 32) >= 0) {
        sum += w[0];
        sum += w[1];
        sum += w[2];
        sum += w[3];
        sum += w[4];
        sum += w[5];
        sum += w[6];
        sum += w[7];
        sum += w[8];
        sum += w[9];
        sum += w[10];
        sum += w[11];
        sum += w[12];
        sum += w[13];
        sum += w[14];
        sum += w[15];
        w += 16;
    }
    mlen += 32;
    while ((mlen -= 8) >= 0) {
        sum += w[0];
        sum += w[1];
        sum += w[2];
        sum += w[3];
        w += 4;
    }
    mlen += 8;
    if (mlen == 0 && byte_swapped == 0)
        goto cont;
    REDUCE;
    while ((mlen -= 2) >= 0) {
        sum += *w++;
    }

    if (byte_swapped) {
        REDUCE;
        sum <<= 8;
        if (mlen == -1) {
            s_util.c[1] = *(uint8_t *)w;
            sum += s_util.s;
            mlen = 0;
        } else

            mlen = -1;
    } else if (mlen == -1)
        s_util.c[0] = *(uint8_t *)w;

cont:
    if (len) {
        DEBUG_ERROR("cksum: out of data");
        DEBUG_ERROR(" len = %d", len);
    }
    if (mlen == -1) {
        /* The last mbuf has odd # of bytes. Follow the
         standard (the odd byte may be shifted left by 8 bits
                   or not as determined by endian-ness of the machine) */
        s_util.c[1] = 0;
        sum += s_util.s;
    }
    REDUCE;
    return (~sum & 0xffff);
}

int ip6_cksum(struct mbuf *m)
{
    /* TODO: Optimize this by being able to pass the ip6_pseudohdr to cksum
     * separately from the mbuf */
    struct ip6 save_ip, *ip = mtod(m, struct ip6 *);
    struct ip6_pseudohdr *ih = mtod(m, struct ip6_pseudohdr *);
    int sum;

    save_ip = *ip;

    ih->ih_src = save_ip.ip_src;
    ih->ih_dst = save_ip.ip_dst;
    ih->ih_pl = htonl((uint32_t)ntohs(save_ip.ip_pl));
    ih->ih_zero_hi = 0;
    ih->ih_zero_lo = 0;
    ih->ih_nh = save_ip.ip_nh;

    sum = cksum(m, ((int)sizeof(struct ip6_pseudohdr)) + ntohl(ih->ih_pl));

    *ip = save_ip;

    return sum;
}
