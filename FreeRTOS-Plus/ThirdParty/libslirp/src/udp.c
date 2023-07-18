/* SPDX-License-Identifier: BSD-3-Clause */
/*
 * Copyright (c) 1982, 1986, 1988, 1990, 1993
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
 *	@(#)udp_usrreq.c	8.4 (Berkeley) 1/21/94
 * udp_usrreq.c,v 1.4 1994/10/02 17:48:45 phk Exp
 */

/*
 * Changes and additions relating to SLiRP
 * Copyright (c) 1995 Danny Gasparovski.
 *
 * Please read the file COPYRIGHT for the
 * terms and conditions of the copyright.
 */

#include "slirp.h"
#include "ip_icmp.h"

static uint8_t udp_tos(struct socket *so);

void udp_init(Slirp *slirp)
{
    slirp->udb.so_next = slirp->udb.so_prev = &slirp->udb;
    slirp->udp_last_so = &slirp->udb;
}

void udp_cleanup(Slirp *slirp)
{
    struct socket *so, *so_next;

    for (so = slirp->udb.so_next; so != &slirp->udb; so = so_next) {
        so_next = so->so_next;
        udp_detach(slirp->udb.so_next);
    }
}

/* m->m_data  points at ip packet header
 * m->m_len   length ip packet
 * ip->ip_len length data (IPDU)
 */
void udp_input(register struct mbuf *m, int iphlen)
{
    Slirp *slirp = m->slirp;
    M_DUP_DEBUG(slirp, m, 0, 0);

    register struct ip *ip;
    register struct udphdr *uh;
    int len;
    struct ip save_ip;
    struct socket *so;
    struct sockaddr_storage lhost;
    struct sockaddr_in *lhost4;
    int ttl;

    DEBUG_CALL("udp_input");
    DEBUG_ARG("m = %p", m);
    DEBUG_ARG("iphlen = %d", iphlen);

    /*
     * Strip IP options, if any; should skip this,
     * make available to user, and use on returned packets,
     * but we don't yet have a way to check the checksum
     * with options still present.
     */
    if (iphlen > sizeof(struct ip)) {
        ip_stripoptions(m, (struct mbuf *)0);
        iphlen = sizeof(struct ip);
    }

    /*
     * Get IP and UDP header together in first mbuf.
     */
    ip = mtod_check(m, iphlen + sizeof(struct udphdr));
    if (ip == NULL) {
        goto bad;
    }
    uh = (struct udphdr *)((char *)ip + iphlen);

    /*
     * Make mbuf data length reflect UDP length.
     * If not enough data to reflect UDP length, drop.
     */
    len = ntohs((uint16_t)uh->uh_ulen);

    if (ip->ip_len != len) {
        if (len > ip->ip_len) {
            goto bad;
        }
        m_adj(m, len - ip->ip_len);
        ip->ip_len = len;
    }

    /*
     * Save a copy of the IP header in case we want restore it
     * for sending an ICMP error message in response.
     */
    save_ip = *ip;
    save_ip.ip_len += iphlen; /* tcp_input subtracts this */

    /*
     * Checksum extended UDP header and data.
     */
    if (uh->uh_sum) {
        memset(&((struct ipovly *)ip)->ih_mbuf, 0, sizeof(struct mbuf_ptr));
        ((struct ipovly *)ip)->ih_x1 = 0;
        ((struct ipovly *)ip)->ih_len = uh->uh_ulen;
        if (cksum(m, len + sizeof(struct ip))) {
            goto bad;
        }
    }

    lhost.ss_family = AF_INET;
    lhost4 = (struct sockaddr_in *)&lhost;
    lhost4->sin_addr = ip->ip_src;
    lhost4->sin_port = uh->uh_sport;

    /*
     *  handle DHCP/BOOTP
     */
    if (ntohs(uh->uh_dport) == BOOTP_SERVER &&
        (ip->ip_dst.s_addr == slirp->vhost_addr.s_addr ||
         ip->ip_dst.s_addr == 0xffffffff)) {
        bootp_input(m);
        goto bad;
    }

    /*
     *  handle TFTP
     */
    if (ntohs(uh->uh_dport) == TFTP_SERVER &&
        ip->ip_dst.s_addr == slirp->vhost_addr.s_addr) {
        m->m_data += iphlen;
        m->m_len -= iphlen;
        tftp_input(&lhost, m);
        m->m_data -= iphlen;
        m->m_len += iphlen;
        goto bad;
    }

    if (slirp->restricted) {
        goto bad;
    }

    /*
     * Locate pcb for datagram.
     */
    so = solookup(&slirp->udp_last_so, &slirp->udb, &lhost, NULL);

    if (so == NULL) {
        /*
         * If there's no socket for this packet,
         * create one
         */
        so = socreate(slirp, IPPROTO_UDP);
        if (udp_attach(so, AF_INET) == -1) {
            DEBUG_MISC(" udp_attach errno = %d-%s", errno, strerror(errno));
            sofree(so);
            goto bad;
        }

        /*
         * Setup fields
         */
        so->so_lfamily = AF_INET;
        so->so_laddr = ip->ip_src;
        so->so_lport = uh->uh_sport;

        if ((so->so_iptos = udp_tos(so)) == 0)
            so->so_iptos = ip->ip_tos;

        /*
         * XXXXX Here, check if it's in udpexec_list,
         * and if it is, do the fork_exec() etc.
         */
    }

    so->so_ffamily = AF_INET;
    so->so_faddr = ip->ip_dst; /* XXX */
    so->so_fport = uh->uh_dport; /* XXX */

    iphlen += sizeof(struct udphdr);
    m->m_len -= iphlen;
    m->m_data += iphlen;

    /*
     * Check for TTL
     */
    ttl = save_ip.ip_ttl-1;
    if (ttl <= 0) {
        m->m_len += iphlen;
        m->m_data -= iphlen;
        *ip = save_ip;
        DEBUG_MISC("udp ttl exceeded");
        icmp_send_error(m, ICMP_TIMXCEED, ICMP_TIMXCEED_INTRANS, 0, NULL);
        goto bad;
    }
    setsockopt(so->s, IPPROTO_IP, IP_TTL, &ttl, sizeof(ttl));

    /*
     * Now we sendto() the packet.
     */
    if (sosendto(so, m) == -1) {
        m->m_len += iphlen;
        m->m_data -= iphlen;
        *ip = save_ip;
        DEBUG_MISC("udp tx errno = %d-%s", errno, strerror(errno));
        icmp_send_error(m, ICMP_UNREACH, ICMP_UNREACH_NET, 0, strerror(errno));
        goto bad;
    }

    m_free(so->so_m); /* used for ICMP if error on sorecvfrom */

    /* restore the orig mbuf packet */
    m->m_len += iphlen;
    m->m_data -= iphlen;
    *ip = save_ip;
    so->so_m = m; /* ICMP backup */

    return;
bad:
    m_free(m);
}

int udp_output(struct socket *so, struct mbuf *m, struct sockaddr_in *saddr,
               struct sockaddr_in *daddr, int iptos)
{
    Slirp *slirp = m->slirp;
    char addr[INET_ADDRSTRLEN];

    M_DUP_DEBUG(slirp, m, 0, sizeof(struct udpiphdr));

    register struct udpiphdr *ui;
    int error = 0;

    DEBUG_CALL("udp_output");
    DEBUG_ARG("so = %p", so);
    DEBUG_ARG("m = %p", m);
    DEBUG_ARG("saddr = %s", inet_ntop(AF_INET, &saddr->sin_addr, addr, sizeof(addr)));
    DEBUG_ARG("daddr = %s", inet_ntop(AF_INET, &daddr->sin_addr, addr, sizeof(addr)));

    /*
     * Adjust for header
     */
    m->m_data -= sizeof(struct udpiphdr);
    m->m_len += sizeof(struct udpiphdr);

    /*
     * Fill in mbuf with extended UDP header
     * and addresses and length put into network format.
     */
    ui = mtod(m, struct udpiphdr *);
    memset(&ui->ui_i.ih_mbuf, 0, sizeof(struct mbuf_ptr));
    ui->ui_x1 = 0;
    ui->ui_pr = IPPROTO_UDP;
    ui->ui_len = htons(m->m_len - sizeof(struct ip));
    /* XXXXX Check for from-one-location sockets, or from-any-location sockets
     */
    ui->ui_src = saddr->sin_addr;
    ui->ui_dst = daddr->sin_addr;
    ui->ui_sport = saddr->sin_port;
    ui->ui_dport = daddr->sin_port;
    ui->ui_ulen = ui->ui_len;

    /*
     * Stuff checksum and output datagram.
     */
    ui->ui_sum = 0;
    if ((ui->ui_sum = cksum(m, m->m_len)) == 0)
        ui->ui_sum = 0xffff;
    ((struct ip *)ui)->ip_len = m->m_len;

    ((struct ip *)ui)->ip_ttl = IPDEFTTL;
    ((struct ip *)ui)->ip_tos = iptos;

    error = ip_output(so, m);

    return (error);
}

int udp_attach(struct socket *so, unsigned short af)
{
    so->s = slirp_socket(af, SOCK_DGRAM, 0);
    if (so->s != -1) {
        if (slirp_bind_outbound(so, af) != 0) {
            // bind failed - close socket
            closesocket(so->s);
            so->s = -1;
            return -1;
        }

#ifdef __linux__
        {
            int opt = 1;
            switch (af) {
            case AF_INET:
                setsockopt(so->s, IPPROTO_IP, IP_RECVERR, &opt, sizeof(opt));
                break;
            case AF_INET6:
                setsockopt(so->s, IPPROTO_IPV6, IPV6_RECVERR, &opt, sizeof(opt));
                break;
            default:
                g_assert_not_reached();
            }
        }
#endif

        so->so_expire = curtime + SO_EXPIRE;
        slirp_insque(so, &so->slirp->udb);
    }
    so->slirp->cb->register_poll_fd(so->s, so->slirp->opaque);
    return (so->s);
}

void udp_detach(struct socket *so)
{
    so->slirp->cb->unregister_poll_fd(so->s, so->slirp->opaque);
    closesocket(so->s);
    sofree(so);
}

static const struct tos_t udptos[] = { { 0, 53, IPTOS_LOWDELAY, 0 }, /* DNS */
                                       { 0, 0, 0, 0 } };

static uint8_t udp_tos(struct socket *so)
{
    int i = 0;

    while (udptos[i].tos) {
        if ((udptos[i].fport && ntohs(so->so_fport) == udptos[i].fport) ||
            (udptos[i].lport && ntohs(so->so_lport) == udptos[i].lport)) {
            if (so->slirp->enable_emu)
                so->so_emu = udptos[i].emu;
            return udptos[i].tos;
        }
        i++;
    }

    return 0;
}

struct socket *udpx_listen(Slirp *slirp,
                           const struct sockaddr *haddr, socklen_t haddrlen,
                           const struct sockaddr *laddr, socklen_t laddrlen,
                           int flags)
{
    struct socket *so;
    socklen_t addrlen;
    int save_errno;

    so = socreate(slirp, IPPROTO_UDP);
    so->s = slirp_socket(haddr->sa_family, SOCK_DGRAM, 0);
    if (so->s < 0) {
        save_errno = errno;
        sofree(so);
        errno = save_errno;
        return NULL;
    }
    if (haddr->sa_family == AF_INET6)
        slirp_socket_set_v6only(so->s, (flags & SS_HOSTFWD_V6ONLY) != 0);
    so->so_expire = curtime + SO_EXPIRE;
    slirp_insque(so, &slirp->udb);

    if (bind(so->s, haddr, haddrlen) < 0) {
        save_errno = errno;
        udp_detach(so);
        errno = save_errno;
        return NULL;
    }
    slirp_socket_set_fast_reuse(so->s);

    addrlen = sizeof(so->fhost);
    getsockname(so->s, &so->fhost.sa, &addrlen);
    sotranslate_accept(so);

    sockaddr_copy(&so->lhost.sa, sizeof(so->lhost), laddr, laddrlen);

    if (flags != SS_FACCEPTONCE)
        so->so_expire = 0;
    so->so_state &= SS_PERSISTENT_MASK;
    so->so_state |= SS_ISFCONNECTED | flags;

    return so;
}

struct socket *udp_listen(Slirp *slirp, uint32_t haddr, unsigned hport,
                          uint32_t laddr, unsigned lport, int flags)
{
    struct sockaddr_in hsa, lsa;

    memset(&hsa, 0, sizeof(hsa));
    hsa.sin_family = AF_INET;
    hsa.sin_addr.s_addr = haddr;
    hsa.sin_port = hport;

    memset(&lsa, 0, sizeof(lsa));
    lsa.sin_family = AF_INET;
    lsa.sin_addr.s_addr = laddr;
    lsa.sin_port = lport;

    return udpx_listen(slirp, (const struct sockaddr *) &hsa, sizeof(hsa), (struct sockaddr *) &lsa, sizeof(lsa), flags);
}
