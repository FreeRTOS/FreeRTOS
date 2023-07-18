/* SPDX-License-Identifier: BSD-3-Clause */
/*
 * Copyright (c) 1982, 1986, 1988, 1993
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
 *	@(#)ip_input.c	8.2 (Berkeley) 1/4/94
 * ip_input.c,v 1.11 1994/11/16 10:17:08 jkh Exp
 */

/*
 * Changes and additions relating to SLiRP are
 * Copyright (c) 1995 Danny Gasparovski.
 */

#include "slirp.h"
#include "ip_icmp.h"

static struct ip *ip_reass(Slirp *slirp, struct ip *ip, struct ipq *fp);
static void ip_freef(Slirp *slirp, struct ipq *fp);
static void ip_enq(register struct ipas *p, register struct ipas *prev);
static void ip_deq(register struct ipas *p);

/*
 * IP initialization: fill in IP protocol switch table.
 * All protocols not implemented in kernel go to raw IP protocol handler.
 */
void ip_init(Slirp *slirp)
{
    slirp->ipq.ip_link.next = slirp->ipq.ip_link.prev = &slirp->ipq.ip_link;
    udp_init(slirp);
    tcp_init(slirp);
    icmp_init(slirp);
}

void ip_cleanup(Slirp *slirp)
{
    udp_cleanup(slirp);
    tcp_cleanup(slirp);
    icmp_cleanup(slirp);
}

/*
 * Ip input routine.  Checksum and byte swap header.  If fragmented
 * try to reassemble.  Process options.  Pass to next level.
 */
void ip_input(struct mbuf *m)
{
    Slirp *slirp = m->slirp;
    M_DUP_DEBUG(slirp, m, 0, TCPIPHDR_DELTA);

    register struct ip *ip;
    int hlen;

    if (!slirp->in_enabled) {
        goto bad;
    }

    DEBUG_CALL("ip_input");
    DEBUG_ARG("m = %p", m);
    DEBUG_ARG("m_len = %d", m->m_len);

    if (m->m_len < sizeof(struct ip)) {
        goto bad;
    }

    ip = mtod(m, struct ip *);

    if (ip->ip_v != IPVERSION) {
        goto bad;
    }

    hlen = ip->ip_hl << 2;
    if (hlen < sizeof(struct ip) || hlen > m->m_len) { /* min header length */
        goto bad; /* or packet too short */
    }

    /* keep ip header intact for ICMP reply
     * ip->ip_sum = cksum(m, hlen);
     * if (ip->ip_sum) {
     */
    if (cksum(m, hlen)) {
        goto bad;
    }

    /*
     * Convert fields to host representation.
     */
    NTOHS(ip->ip_len);
    if (ip->ip_len < hlen) {
        goto bad;
    }
    NTOHS(ip->ip_id);
    NTOHS(ip->ip_off);

    /*
     * Check that the amount of data in the buffers
     * is as at least much as the IP header would have us expect.
     * Trim mbufs if longer than we expect.
     * Drop packet if shorter than we expect.
     */
    if (m->m_len < ip->ip_len) {
        goto bad;
    }

    /* Should drop packet if mbuf too long? hmmm... */
    if (m->m_len > ip->ip_len)
        m_adj(m, ip->ip_len - m->m_len);

    /* check ip_ttl for a correct ICMP reply */
    if (ip->ip_ttl == 0) {
        icmp_send_error(m, ICMP_TIMXCEED, ICMP_TIMXCEED_INTRANS, 0, "ttl");
        goto bad;
    }

    /*
     * If offset or IP_MF are set, must reassemble.
     * Otherwise, nothing need be done.
     * (We could look in the reassembly queue to see
     * if the packet was previously fragmented,
     * but it's not worth the time; just let them time out.)
     *
     * XXX This should fail, don't fragment yet
     */
    if (ip->ip_off & ~IP_DF) {
        register struct ipq *q;
        struct qlink *l;
        /*
         * Look for queue of fragments
         * of this datagram.
         */
        for (l = slirp->ipq.ip_link.next; l != &slirp->ipq.ip_link;
             l = l->next) {
            q = container_of(l, struct ipq, ip_link);
            if (ip->ip_id == q->ipq_id &&
                ip->ip_src.s_addr == q->ipq_src.s_addr &&
                ip->ip_dst.s_addr == q->ipq_dst.s_addr &&
                ip->ip_p == q->ipq_p)
                goto found;
        }
        q = NULL;
    found:

        /*
         * Adjust ip_len to not reflect header,
         * set ip_mff if more fragments are expected,
         * convert offset of this to bytes.
         */
        ip->ip_len -= hlen;
        if (ip->ip_off & IP_MF)
            ip->ip_tos |= 1;
        else
            ip->ip_tos &= ~1;

        ip->ip_off <<= 3;

        /*
         * If datagram marked as having more fragments
         * or if this is not the first fragment,
         * attempt reassembly; if it succeeds, proceed.
         */
        if (ip->ip_tos & 1 || ip->ip_off) {
            ip = ip_reass(slirp, ip, q);
            if (ip == NULL)
                return;
            m = dtom(slirp, ip);
        } else if (q)
            ip_freef(slirp, q);

    } else
        ip->ip_len -= hlen;

    /*
     * Switch out to protocol's input routine.
     */
    switch (ip->ip_p) {
    case IPPROTO_TCP:
        tcp_input(m, hlen, (struct socket *)NULL, AF_INET);
        break;
    case IPPROTO_UDP:
        udp_input(m, hlen);
        break;
    case IPPROTO_ICMP:
        icmp_input(m, hlen);
        break;
    default:
        m_free(m);
    }
    return;
bad:
    m_free(m);
}

#define iptoas(P) container_of((P), struct ipas, ipf_ip)
#define astoip(P) (&(P)->ipf_ip)
/*
 * Take incoming datagram fragment and try to
 * reassemble it into whole datagram.  If a chain for
 * reassembly of this datagram already exists, then it
 * is given as q; otherwise have to make a chain.
 */
static struct ip *ip_reass(Slirp *slirp, struct ip *ip, struct ipq *q)
{
    register struct mbuf *m = dtom(slirp, ip);
    struct ipas *first = container_of(q, struct ipas, ipq);
    register struct ipas *cursor;
    int hlen = ip->ip_hl << 2;
    int i, next;

    DEBUG_CALL("ip_reass");
    DEBUG_ARG("ip = %p", ip);
    DEBUG_ARG("q = %p", q);
    DEBUG_ARG("m = %p", m);

    /*
     * Presence of header sizes in mbufs
     * would confuse code below.
     * Fragment m_data is concatenated.
     */
    m->m_data += hlen;
    m->m_len -= hlen;

    /*
     * If first fragment to arrive, create a reassembly queue.
     */
    if (q == NULL) {
        struct mbuf *t = m_get(slirp);

        if (t == NULL) {
            goto dropfrag;
        }
        first = mtod(t, struct ipas *);
        q = &first->ipq;
        slirp_insque(&q->ip_link, &slirp->ipq.ip_link);
        q->ipq_ttl = IPFRAGTTL;
        q->ipq_p = ip->ip_p;
        q->ipq_id = ip->ip_id;
        first->link.next = first->link.prev = first;
        q->ipq_src = ip->ip_src;
        q->ipq_dst = ip->ip_dst;
        cursor = first;
        goto insert;
    }

    /*
     * Find a segment which begins after this one does.
     */
    for (cursor = first->link.next; cursor != first; cursor = cursor->link.next)
        if (cursor->ipf_off > ip->ip_off)
            break;

    /*
     * If there is a preceding segment, it may provide some of
     * our data already.  If so, drop the data from the incoming
     * segment.  If it provides all of our data, drop us.
     */
    if (cursor->link.prev != first) {
        struct ipas *pq = cursor->link.prev;
        i = pq->ipf_off + pq->ipf_len - ip->ip_off;
        if (i > 0) {
            if (i >= ip->ip_len)
                goto dropfrag;
            m_adj(dtom(slirp, ip), i);
            ip->ip_off += i;
            ip->ip_len -= i;
        }
    }

    /*
     * While we overlap succeeding segments trim them or,
     * if they are completely covered, dequeue them.
     */
    while (cursor != first && ip->ip_off + ip->ip_len > cursor->ipf_off) {
        struct ipas *prev;
        i = (ip->ip_off + ip->ip_len) - cursor->ipf_off;
        if (i < cursor->ipf_len) {
            cursor->ipf_len -= i;
            cursor->ipf_off += i;
            m_adj(dtom(slirp, cursor), i);
            break;
        }
        prev = cursor;
        cursor = cursor->link.next;
        ip_deq(prev);
        m_free(dtom(slirp, prev));
    }

insert:
    /*
     * Stick new segment in its place;
     * check for complete reassembly.
     */
    ip_enq(iptoas(ip), cursor->link.prev);
    next = 0;
    for (cursor = first->link.next; cursor != first; cursor = cursor->link.next) {
        if (cursor->ipf_off != next)
            return NULL;
        next += cursor->ipf_len;
    }
    if (((struct ipas *)(cursor->link.prev))->ipf_tos & 1)
        return NULL;

    /*
     * Reassembly is complete; concatenate fragments.
     */
    cursor = first->link.next;
    m = dtom(slirp, cursor);
    int delta = (char *)cursor - (m->m_flags & M_EXT ? m->m_ext : m->m_dat);

    cursor = cursor->link.next;
    while (cursor != first) {
        struct mbuf *t = dtom(slirp, cursor);
        cursor = cursor->link.next;
        m_cat(m, t);
    }

    /*
     * Create header for new ip packet by
     * modifying header of first packet;
     * dequeue and discard fragment reassembly header.
     * Make header visible.
     */
    cursor = first->link.next;

    /*
     * If the fragments concatenated to an mbuf that's bigger than the total
     * size of the fragment and the mbuf was not already using an m_ext buffer,
     * then an m_ext buffer was allocated. But q->ipq_next points to the old
     * buffer (in the mbuf), so we must point ip into the new buffer.
     */
    if (m->m_flags & M_EXT) {
        cursor = (struct ipas *)(m->m_ext + delta);
    }

    ip = astoip(cursor);
    ip->ip_len = next;
    ip->ip_tos &= ~1;
    ip->ip_src = q->ipq_src;
    ip->ip_dst = q->ipq_dst;
    slirp_remque(&q->ip_link);
    m_free(dtom(slirp, q));
    m->m_len += (ip->ip_hl << 2);
    m->m_data -= (ip->ip_hl << 2);

    return ip;

dropfrag:
    m_free(m);
    return NULL;
}

/*
 * Free a fragment reassembly header and all
 * associated datagrams.
 */
static void ip_freef(Slirp *slirp, struct ipq *q)
{
    struct ipas *first = container_of(q, struct ipas, ipq);
    register struct ipas *cursor, *next;

    for (cursor = first->link.next; cursor != first; cursor = next) {
        next = cursor->link.next;
        ip_deq(cursor);
        m_free(dtom(slirp, cursor));
    }
    slirp_remque(&q->ip_link);
    m_free(dtom(slirp, q));
}

/*
 * Put an ip fragment on a reassembly chain.
 * Like slirp_insque, but pointers in middle of structure.
 */
static void ip_enq(register struct ipas *p, register struct ipas *prev)
{
    DEBUG_CALL("ip_enq");
    DEBUG_ARG("prev = %p", prev);
    p->link.prev = prev;
    p->link.next = prev->link.next;
    ((struct ipas *)(prev->link.next))->link.prev = p;
    prev->link.next = p;
}

/*
 * To ip_enq as slirp_remque is to slirp_insque.
 */
static void ip_deq(register struct ipas *p)
{
    ((struct ipas *)(p->link.prev))->link.next = p->link.next;
    ((struct ipas *)(p->link.next))->link.prev = p->link.prev;
}

/*
 * IP timer processing;
 * if a timer expires on a reassembly
 * queue, discard it.
 */
void ip_slowtimo(Slirp *slirp)
{
    struct qlink *l;

    DEBUG_CALL("ip_slowtimo");

    l = slirp->ipq.ip_link.next;

    if (l == NULL)
        return;

    while (l != &slirp->ipq.ip_link) {
        struct ipq *q = container_of(l, struct ipq, ip_link);
        l = l->next;
        if (--q->ipq_ttl == 0) {
            ip_freef(slirp, q);
        }
    }
}

/*
 * Strip out IP options, at higher
 * level protocol in the kernel.
 * Second argument is buffer to which options
 * will be moved, and return value is their length.
 * (XXX) should be deleted; last arg currently ignored.
 */
void ip_stripoptions(register struct mbuf *m, struct mbuf *mopt)
{
    register int i;
    struct ip *ip = mtod(m, struct ip *);
    register char *opts;
    int olen;

    olen = (ip->ip_hl << 2) - sizeof(struct ip);
    opts = (char *)(ip + 1);
    i = m->m_len - (sizeof(struct ip) + olen);
    memmove(opts, opts + olen, (unsigned)i);
    m->m_len -= olen;

    ip->ip_hl = sizeof(struct ip) >> 2;
}
