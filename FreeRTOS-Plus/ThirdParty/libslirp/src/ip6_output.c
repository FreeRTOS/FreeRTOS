/* SPDX-License-Identifier: BSD-3-Clause */
/*
 * Copyright (c) 2013
 * Guillaume Subiron, Yann Bordenave, Serigne Modou Wagne.
 */

#include "slirp.h"

/* Number of packets queued before we start sending
 * (to prevent allocing too many mbufs) */
#define IF6_THRESH 10

/*
 * IPv6 output. The packet in mbuf chain m contains a IP header
 */
int ip6_output(struct socket *so, struct mbuf *m, int fast)
{
    Slirp *slirp = m->slirp;
    M_DUP_DEBUG(slirp, m, 0, 0);

    struct ip6 *ip = mtod(m, struct ip6 *);

    DEBUG_CALL("ip6_output");
    DEBUG_ARG("so = %p", so);
    DEBUG_ARG("m = %p", m);

    /* Fill IPv6 header */
    ip->ip_v = IP6VERSION;
    ip->ip_hl = IP6_HOP_LIMIT;
    ip->ip_tc_hi = 0;
    ip->ip_tc_lo = 0;
    ip->ip_fl_hi = 0;
    ip->ip_fl_lo = 0;

    if (fast) {
        /* We cannot fast-send non-multicast, we'd need a NDP NS */
        assert(IN6_IS_ADDR_MULTICAST(&ip->ip_dst));
        if_encap(m->slirp, m);
        m_free(m);
    } else {
        if_output(so, m);
    }

    return 0;
}
