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
 *	@(#)tcp_subr.c	8.1 (Berkeley) 6/10/93
 * tcp_subr.c,v 1.5 1994/10/08 22:39:58 phk Exp
 */

/*
 * Changes and additions relating to SLiRP
 * Copyright (c) 1995 Danny Gasparovski.
 */

#include "slirp.h"

/* patchable/settable parameters for tcp */
/* Don't do rfc1323 performance enhancements */
#define TCP_DO_RFC1323 0

/*
 * Tcp initialization
 */
void tcp_init(Slirp *slirp)
{
    slirp->tcp_iss = 1; /* wrong */
    slirp->tcb.so_next = slirp->tcb.so_prev = &slirp->tcb;
    slirp->tcp_last_so = &slirp->tcb;
}

void tcp_cleanup(Slirp *slirp)
{
    while (slirp->tcb.so_next != &slirp->tcb) {
        tcp_close(sototcpcb(slirp->tcb.so_next));
    }
}

/*
 * Create template to be used to send tcp packets on a connection.
 * Call after host entry created, fills
 * in a skeletal tcp/ip header, minimizing the amount of work
 * necessary when the connection is used.
 */
void tcp_template(struct tcpcb *tp)
{
    struct socket *so = tp->t_socket;
    register struct tcpiphdr *n = &tp->t_template;

    n->ti_mbuf = NULL;
    memset(&n->ti, 0, sizeof(n->ti));
    n->ti_x0 = 0;
    switch (so->so_ffamily) {
    case AF_INET:
        n->ti_pr = IPPROTO_TCP;
        n->ti_len = htons(sizeof(struct tcphdr));
        n->ti_src = so->so_faddr;
        n->ti_dst = so->so_laddr;
        n->ti_sport = so->so_fport;
        n->ti_dport = so->so_lport;
        break;

    case AF_INET6:
        n->ti_nh6 = IPPROTO_TCP;
        n->ti_len = htons(sizeof(struct tcphdr));
        n->ti_src6 = so->so_faddr6;
        n->ti_dst6 = so->so_laddr6;
        n->ti_sport = so->so_fport6;
        n->ti_dport = so->so_lport6;
        break;

    default:
        g_assert_not_reached();
    }

    n->ti_seq = 0;
    n->ti_ack = 0;
    n->ti_x2 = 0;
    n->ti_off = 5;
    n->ti_flags = 0;
    n->ti_win = 0;
    n->ti_sum = 0;
    n->ti_urp = 0;
}

/*
 * Send a single message to the TCP at address specified by
 * the given TCP/IP header.  If m == 0, then we make a copy
 * of the tcpiphdr at ti and send directly to the addressed host.
 * This is used to force keep alive messages out using the TCP
 * template for a connection tp->t_template.  If flags are given
 * then we send a message back to the TCP which originated the
 * segment ti, and discard the mbuf containing it and any other
 * attached mbufs.
 *
 * In any case the ack and sequence number of the transmitted
 * segment are as specified by the parameters.
 */
void tcp_respond(struct tcpcb *tp, struct tcpiphdr *ti, struct mbuf *m,
                 tcp_seq ack, tcp_seq seq, int flags, unsigned short af)
{
    register int tlen;
    int win = 0;

    DEBUG_CALL("tcp_respond");
    DEBUG_ARG("tp = %p", tp);
    DEBUG_ARG("ti = %p", ti);
    DEBUG_ARG("m = %p", m);
    DEBUG_ARG("ack = %u", ack);
    DEBUG_ARG("seq = %u", seq);
    DEBUG_ARG("flags = %x", flags);

    if (tp)
        win = sbspace(&tp->t_socket->so_rcv);
    if (m == NULL) {
        if (!tp || (m = m_get(tp->t_socket->slirp)) == NULL)
            return;
        tlen = 0;
        m->m_data += IF_MAXLINKHDR;
        *mtod(m, struct tcpiphdr *) = *ti;
        ti = mtod(m, struct tcpiphdr *);
        switch (af) {
        case AF_INET:
            ti->ti.ti_i4.ih_x1 = 0;
            break;
        case AF_INET6:
            ti->ti.ti_i6.ih_x1 = 0;
            break;
        default:
            g_assert_not_reached();
        }
        flags = TH_ACK;
    } else {
        /*
         * ti points into m so the next line is just making
         * the mbuf point to ti
         */
        m->m_data = (char *)ti;

        m->m_len = sizeof(struct tcpiphdr);
        tlen = 0;
#define xchg(a, b, type) \
    {                    \
        type t;          \
        t = a;           \
        a = b;           \
        b = t;           \
    }
        switch (af) {
        case AF_INET:
            xchg(ti->ti_dst.s_addr, ti->ti_src.s_addr, uint32_t);
            xchg(ti->ti_dport, ti->ti_sport, uint16_t);
            break;
        case AF_INET6:
            xchg(ti->ti_dst6, ti->ti_src6, struct in6_addr);
            xchg(ti->ti_dport, ti->ti_sport, uint16_t);
            break;
        default:
            g_assert_not_reached();
        }
#undef xchg
    }
    ti->ti_len = htons((uint16_t)(sizeof(struct tcphdr) + tlen));
    tlen += sizeof(struct tcpiphdr);
    m->m_len = tlen;

    ti->ti_mbuf = NULL;
    ti->ti_x0 = 0;
    ti->ti_seq = htonl(seq);
    ti->ti_ack = htonl(ack);
    ti->ti_x2 = 0;
    ti->ti_off = sizeof(struct tcphdr) >> 2;
    ti->ti_flags = flags;
    if (tp)
        ti->ti_win = htons((uint16_t)(win >> tp->rcv_scale));
    else
        ti->ti_win = htons((uint16_t)win);
    ti->ti_urp = 0;
    ti->ti_sum = 0;
    ti->ti_sum = cksum(m, tlen);

    struct tcpiphdr tcpiph_save = *(mtod(m, struct tcpiphdr *));
    struct ip *ip;
    struct ip6 *ip6;

    switch (af) {
    case AF_INET:
        m->m_data +=
            sizeof(struct tcpiphdr) - sizeof(struct tcphdr) - sizeof(struct ip);
        m->m_len -=
            sizeof(struct tcpiphdr) - sizeof(struct tcphdr) - sizeof(struct ip);
        ip = mtod(m, struct ip *);
        ip->ip_len = m->m_len;
        ip->ip_dst = tcpiph_save.ti_dst;
        ip->ip_src = tcpiph_save.ti_src;
        ip->ip_p = tcpiph_save.ti_pr;

        if (flags & TH_RST) {
            ip->ip_ttl = MAXTTL;
        } else {
            ip->ip_ttl = IPDEFTTL;
        }

        ip_output(NULL, m);
        break;

    case AF_INET6:
        m->m_data += sizeof(struct tcpiphdr) - sizeof(struct tcphdr) -
                     sizeof(struct ip6);
        m->m_len -= sizeof(struct tcpiphdr) - sizeof(struct tcphdr) -
                    sizeof(struct ip6);
        ip6 = mtod(m, struct ip6 *);
        ip6->ip_pl = tcpiph_save.ti_len;
        ip6->ip_dst = tcpiph_save.ti_dst6;
        ip6->ip_src = tcpiph_save.ti_src6;
        ip6->ip_nh = tcpiph_save.ti_nh6;

        ip6_output(NULL, m, 0);
        break;

    default:
        g_assert_not_reached();
    }
}

/*
 * Create a new TCP control block, making an
 * empty reassembly queue and hooking it to the argument
 * protocol control block.
 */
struct tcpcb *tcp_newtcpcb(struct socket *so)
{
    register struct tcpcb *tp;

    tp = g_new0(struct tcpcb, 1);
    tp->seg_next = tp->seg_prev = (struct tcpiphdr *)tp;
    /*
     * 40: length of IPv4 header (20) + TCP header (20)
     * 60: length of IPv6 header (40) + TCP header (20)
     */
    tp->t_maxseg =
        MIN(so->slirp->if_mtu - ((so->so_ffamily == AF_INET) ? 40 : 60),
            TCP_MAXSEG_MAX);

    tp->t_flags = TCP_DO_RFC1323 ? (TF_REQ_SCALE | TF_REQ_TSTMP) : 0;
    tp->t_socket = so;

    /*
     * Init srtt to TCPTV_SRTTBASE (0), so we can tell that we have no
     * rtt estimate.  Set rttvar so that srtt + 2 * rttvar gives
     * reasonable initial retransmit time.
     */
    tp->t_srtt = TCPTV_SRTTBASE;
    tp->t_rttvar = TCPTV_SRTTDFLT << 2;
    tp->t_rttmin = TCPTV_MIN;

    TCPT_RANGESET(tp->t_rxtcur,
                  ((TCPTV_SRTTBASE >> 2) + (TCPTV_SRTTDFLT << 2)) >> 1,
                  TCPTV_MIN, TCPTV_REXMTMAX);

    tp->snd_cwnd = TCP_MAXWIN << TCP_MAX_WINSHIFT;
    tp->snd_ssthresh = TCP_MAXWIN << TCP_MAX_WINSHIFT;
    tp->t_state = TCPS_CLOSED;

    so->so_tcpcb = tp;

    return (tp);
}

/*
 * Drop a TCP connection, reporting
 * the specified error.  If connection is synchronized,
 * then send a RST to peer.
 */
struct tcpcb *tcp_drop(struct tcpcb *tp, int err)
{
    DEBUG_CALL("tcp_drop");
    DEBUG_ARG("tp = %p", tp);
    DEBUG_ARG("errno = %d", errno);

    if (TCPS_HAVERCVDSYN(tp->t_state)) {
        tp->t_state = TCPS_CLOSED;
        tcp_output(tp);
    }
    return (tcp_close(tp));
}

/*
 * Close a TCP control block:
 *	discard all space held by the tcp
 *	discard internet protocol block
 *	wake up any sleepers
 */
struct tcpcb *tcp_close(struct tcpcb *tp)
{
    register struct tcpiphdr *t;
    struct socket *so = tp->t_socket;
    Slirp *slirp = so->slirp;
    register struct mbuf *m;

    DEBUG_CALL("tcp_close");
    DEBUG_ARG("tp = %p", tp);

    /* free the reassembly queue, if any */
    t = tcpfrag_list_first(tp);
    while (!tcpfrag_list_end(t, tp)) {
        t = tcpiphdr_next(t);
        m = tcpiphdr_prev(t)->ti_mbuf;
        slirp_remque(tcpiphdr2qlink(tcpiphdr_prev(t)));
        m_free(m);
    }
    g_free(tp);
    so->so_tcpcb = NULL;
    /* clobber input socket cache if we're closing the cached connection */
    if (so == slirp->tcp_last_so)
        slirp->tcp_last_so = &slirp->tcb;
    so->slirp->cb->unregister_poll_fd(so->s, so->slirp->opaque);
    closesocket(so->s);
    sbfree(&so->so_rcv);
    sbfree(&so->so_snd);
    sofree(so);
    return ((struct tcpcb *)0);
}

/*
 * TCP protocol interface to socket abstraction.
 */

/*
 * User issued close, and wish to trail through shutdown states:
 * if never received SYN, just forget it.  If got a SYN from peer,
 * but haven't sent FIN, then go to FIN_WAIT_1 state to send peer a FIN.
 * If already got a FIN from peer, then almost done; go to LAST_ACK
 * state.  In all other cases, have already sent FIN to peer (e.g.
 * after PRU_SHUTDOWN), and just have to play tedious game waiting
 * for peer to send FIN or not respond to keep-alives, etc.
 * We can let the user exit from the close as soon as the FIN is acked.
 */
void tcp_sockclosed(struct tcpcb *tp)
{
    DEBUG_CALL("tcp_sockclosed");
    DEBUG_ARG("tp = %p", tp);

    if (!tp) {
        return;
    }

    switch (tp->t_state) {
    case TCPS_CLOSED:
    case TCPS_LISTEN:
    case TCPS_SYN_SENT:
        tp->t_state = TCPS_CLOSED;
        tcp_close(tp);
        return;

    case TCPS_SYN_RECEIVED:
    case TCPS_ESTABLISHED:
        tp->t_state = TCPS_FIN_WAIT_1;
        break;

    case TCPS_CLOSE_WAIT:
        tp->t_state = TCPS_LAST_ACK;
        break;
    }
    tcp_output(tp);
}

/*
 * Connect to a host on the Internet
 * Called by tcp_input
 * Only do a connect, the tcp fields will be set in tcp_input
 * return 0 if there's a result of the connect,
 * else return -1 means we're still connecting
 * The return value is almost always -1 since the socket is
 * nonblocking.  Connect returns after the SYN is sent, and does
 * not wait for ACK+SYN.
 */
int tcp_fconnect(struct socket *so, unsigned short af)
{
    int ret = 0;

    DEBUG_CALL("tcp_fconnect");
    DEBUG_ARG("so = %p", so);

    ret = so->s = slirp_socket(af, SOCK_STREAM, 0);
    if (ret >= 0) {
        ret = slirp_bind_outbound(so, af);
        if (ret < 0) {
            // bind failed - close socket
            closesocket(so->s);
            so->s = -1;
            return (ret);
        }
    }

    if (ret >= 0) {
        int opt, s = so->s;
        struct sockaddr_storage addr;

        slirp_set_nonblock(s);
        so->slirp->cb->register_poll_fd(s, so->slirp->opaque);
        slirp_socket_set_fast_reuse(s);
        opt = 1;
        setsockopt(s, SOL_SOCKET, SO_OOBINLINE, &opt, sizeof(opt));
        opt = 1;
        setsockopt(s, IPPROTO_TCP, TCP_NODELAY, &opt, sizeof(opt));

        addr = so->fhost.ss;
        DEBUG_CALL(" connect()ing");
        if (sotranslate_out(so, &addr) < 0) {
            return -1;
        }

        /* We don't care what port we get */
        ret = connect(s, (struct sockaddr *)&addr, sockaddr_size(&addr));

        /*
         * If it's not in progress, it failed, so we just return 0,
         * without clearing SS_NOFDREF
         */
        soisfconnecting(so);
    }

    return (ret);
}

/*
 * Accept the socket and connect to the local-host
 *
 * We have a problem. The correct thing to do would be
 * to first connect to the local-host, and only if the
 * connection is accepted, then do an accept() here.
 * But, a) we need to know who's trying to connect
 * to the socket to be able to SYN the local-host, and
 * b) we are already connected to the foreign host by
 * the time it gets to accept(), so... We simply accept
 * here and SYN the local-host.
 */
void tcp_connect(struct socket *inso)
{
    Slirp *slirp = inso->slirp;
    struct socket *so;
    struct sockaddr_storage addr;
    socklen_t addrlen;
    struct tcpcb *tp;
    int s, opt, ret;
    /* AF_INET6 addresses are bigger than AF_INET, so this is big enough. */
    char addrstr[INET6_ADDRSTRLEN];
    char portstr[6];

    DEBUG_CALL("tcp_connect");
    DEBUG_ARG("inso = %p", inso);
    switch (inso->lhost.ss.ss_family) {
    case AF_INET:
        addrlen = sizeof(struct sockaddr_in);
        break;
    case AF_INET6:
        addrlen = sizeof(struct sockaddr_in6);
        break;
    default:
        g_assert_not_reached();
    }
    ret = getnameinfo((const struct sockaddr *) &inso->lhost.ss, addrlen, addrstr, sizeof(addrstr), portstr, sizeof(portstr), NI_NUMERICHOST|NI_NUMERICSERV);
    g_assert(ret == 0);
    DEBUG_ARG("ip = [%s]:%s", addrstr, portstr);
    DEBUG_ARG("so_state = 0x%x", inso->so_state);

    /* Perform lazy guest IP address resolution if needed. */
    if (inso->so_state & SS_HOSTFWD) {
        /*
         * We can only reject the connection request by accepting it and
         * then immediately closing it. Note that SS_FACCEPTONCE sockets can't
         * get here.
         */
        if (soassign_guest_addr_if_needed(inso) < 0) {
            /*
             * Guest address isn't available yet. We could either try to defer
             * completing this connection request until the guest address is
             * available, or punt. It's easier to punt. Otherwise we need to
             * complicate the mechanism by which we're called to defer calling
             * us again until the guest address is available.
             */
            DEBUG_MISC(" guest address not available yet");
            addrlen = sizeof(addr);
            s = accept(inso->s, (struct sockaddr *)&addr, &addrlen);
            if (s >= 0) {
                close(s);
            }
            return;
        }
    }

    /*
     * If it's an SS_ACCEPTONCE socket, no need to socreate()
     * another socket, just use the accept() socket.
     */
    if (inso->so_state & SS_FACCEPTONCE) {
        /* FACCEPTONCE already have a tcpcb */
        so = inso;
    } else {
        so = socreate(slirp, IPPROTO_TCP);
        tcp_attach(so);
        so->lhost = inso->lhost;
        so->so_ffamily = inso->so_ffamily;
    }

    tcp_mss(sototcpcb(so), 0);

    addrlen = sizeof(addr);
    s = accept(inso->s, (struct sockaddr *)&addr, &addrlen);
    if (s < 0) {
        tcp_close(sototcpcb(so)); /* This will sofree() as well */
        return;
    }
    slirp_set_nonblock(s);
    so->slirp->cb->register_poll_fd(s, so->slirp->opaque);
    slirp_socket_set_fast_reuse(s);
    opt = 1;
    setsockopt(s, SOL_SOCKET, SO_OOBINLINE, &opt, sizeof(int));
    slirp_socket_set_nodelay(s);

    so->fhost.ss = addr;
    sotranslate_accept(so);

    /* Close the accept() socket, set right state */
    if (inso->so_state & SS_FACCEPTONCE) {
        /* If we only accept once, close the accept() socket */
        so->slirp->cb->unregister_poll_fd(so->s, so->slirp->opaque);
        closesocket(so->s);

        /* Don't select it yet, even though we have an FD */
        /* if it's not FACCEPTONCE, it's already NOFDREF */
        so->so_state = SS_NOFDREF;
    }
    so->s = s;
    so->so_state |= SS_INCOMING;

    so->so_iptos = tcp_tos(so);
    tp = sototcpcb(so);

    tcp_template(tp);

    tp->t_state = TCPS_SYN_SENT;
    tp->t_timer[TCPT_KEEP] = TCPTV_KEEP_INIT;
    tp->iss = slirp->tcp_iss;
    slirp->tcp_iss += TCP_ISSINCR / 2;
    tcp_sendseqinit(tp);
    tcp_output(tp);
}

/*
 * Attach a TCPCB to a socket.
 */
void tcp_attach(struct socket *so)
{
    so->so_tcpcb = tcp_newtcpcb(so);
    slirp_insque(so, &so->slirp->tcb);
}

/*
 * Set the socket's type of service field
 */
static const struct tos_t tcptos[] = {
    { 0, 20, IPTOS_THROUGHPUT, 0 }, /* ftp data */
    { 21, 21, IPTOS_LOWDELAY, EMU_FTP }, /* ftp control */
    { 0, 23, IPTOS_LOWDELAY, 0 }, /* telnet */
    { 0, 80, IPTOS_THROUGHPUT, 0 }, /* WWW */
    { 0, 513, IPTOS_LOWDELAY, EMU_RLOGIN | EMU_NOCONNECT }, /* rlogin */
    { 0, 544, IPTOS_LOWDELAY, EMU_KSH }, /* kshell */
    { 0, 543, IPTOS_LOWDELAY, 0 }, /* klogin */
    { 0, 6667, IPTOS_THROUGHPUT, EMU_IRC }, /* IRC */
    { 0, 6668, IPTOS_THROUGHPUT, EMU_IRC }, /* IRC undernet */
    { 0, 7070, IPTOS_LOWDELAY, EMU_REALAUDIO }, /* RealAudio control */
    { 0, 113, IPTOS_LOWDELAY, EMU_IDENT }, /* identd protocol */
    { 0, 0, 0, 0 }
};

/*
 * Return TOS according to the above table
 */
uint8_t tcp_tos(struct socket *so)
{
    int i = 0;

    while (tcptos[i].tos) {
        if ((tcptos[i].fport && (ntohs(so->so_fport) == tcptos[i].fport)) ||
            (tcptos[i].lport && (ntohs(so->so_lport) == tcptos[i].lport))) {
            if (so->slirp->enable_emu)
                so->so_emu = tcptos[i].emu;
            return tcptos[i].tos;
        }
        i++;
    }
    return 0;
}

/*
 * Emulate programs that try and connect to us
 * This includes ftp (the data connection is
 * initiated by the server) and IRC (DCC CHAT and
 * DCC SEND) for now
 *
 * NOTE: It's possible to crash SLiRP by sending it
 * unstandard strings to emulate... if this is a problem,
 * more checks are needed here
 *
 * XXX Assumes the whole command came in one packet
 * XXX If there is more than one command in the packet, the others may
 * be truncated.
 * XXX If the command is too long, it may be truncated.
 *
 * XXX Some ftp clients will have their TOS set to
 * LOWDELAY and so Nagel will kick in.  Because of this,
 * we'll get the first letter, followed by the rest, so
 * we simply scan for ORT instead of PORT...
 * DCC doesn't have this problem because there's other stuff
 * in the packet before the DCC command.
 *
 * Return 1 if the mbuf m is still valid and should be
 * sbappend()ed
 *
 * NOTE: if you return 0 you MUST m_free() the mbuf!
 */
int tcp_emu(struct socket *so, struct mbuf *m)
{
    Slirp *slirp = so->slirp;
    unsigned n1, n2, n3, n4, n5, n6;
    char buff[257];
    uint32_t laddr;
    unsigned lport;
    char *bptr;

    DEBUG_CALL("tcp_emu");
    DEBUG_ARG("so = %p", so);
    DEBUG_ARG("m = %p", m);

    switch (so->so_emu) {
        int x, i;

        /* TODO: IPv6 */
    case EMU_IDENT:
        /*
         * Identification protocol as per rfc-1413
         */

        {
            struct socket *tmpso;
            struct sockaddr_in addr;
            socklen_t addrlen = sizeof(struct sockaddr_in);
            char *eol = g_strstr_len(m->m_data, m->m_len, "\r\n");

            if (!eol) {
                return 1;
            }

            *eol = '\0';
            if (sscanf(m->m_data, "%u%*[ ,]%u", &n1, &n2) == 2) {
                HTONS(n1);
                HTONS(n2);
                /* n2 is the one on our host */
                for (tmpso = slirp->tcb.so_next; tmpso != &slirp->tcb;
                     tmpso = tmpso->so_next) {
                    if (tmpso->so_laddr.s_addr == so->so_laddr.s_addr &&
                        tmpso->so_lport == n2 &&
                        tmpso->so_faddr.s_addr == so->so_faddr.s_addr &&
                        tmpso->so_fport == n1) {
                        if (getsockname(tmpso->s, (struct sockaddr *)&addr,
                                        &addrlen) == 0)
                            n2 = addr.sin_port;
                        break;
                    }
                }
                NTOHS(n1);
                NTOHS(n2);
                m_inc(m, g_snprintf(NULL, 0, "%d,%d\r\n", n1, n2) + 1);
                m->m_len = slirp_fmt(m->m_data, M_ROOM(m), "%d,%d\r\n", n1, n2);
            } else {
                *eol = '\r';
            }

            return 1;
        }

    case EMU_FTP: /* ftp */
        m_inc(m, m->m_len + 1);
        *(m->m_data + m->m_len) = 0; /* NUL terminate for strstr */
        if ((bptr = (char *)strstr(m->m_data, "ORT")) != NULL) {
            /*
             * Need to emulate the PORT command
             */
            x = sscanf(bptr, "ORT %u,%u,%u,%u,%u,%u\r\n%256[^\177]", &n1, &n2,
                       &n3, &n4, &n5, &n6, buff);
            if (x < 6)
                return 1;

            laddr = htonl((n1 << 24) | (n2 << 16) | (n3 << 8) | (n4));
            lport = htons((n5 << 8) | (n6));

            if ((so = tcp_listen(slirp, INADDR_ANY, 0, laddr, lport,
                                 SS_FACCEPTONCE)) == NULL) {
                return 1;
            }
            n6 = ntohs(so->so_fport);

            n5 = (n6 >> 8) & 0xff;
            n6 &= 0xff;

            laddr = ntohl(so->so_faddr.s_addr);

            n1 = ((laddr >> 24) & 0xff);
            n2 = ((laddr >> 16) & 0xff);
            n3 = ((laddr >> 8) & 0xff);
            n4 = (laddr & 0xff);

            m->m_len = bptr - m->m_data; /* Adjust length */
            m->m_len += slirp_fmt(bptr, M_FREEROOM(m),
                                  "ORT %d,%d,%d,%d,%d,%d\r\n%s",
                                  n1, n2, n3, n4, n5, n6, x == 7 ? buff : "");
            return 1;
        } else if ((bptr = (char *)strstr(m->m_data, "27 Entering")) != NULL) {
            /*
             * Need to emulate the PASV response
             */
            x = sscanf(
                bptr,
                "27 Entering Passive Mode (%u,%u,%u,%u,%u,%u)\r\n%256[^\177]",
                &n1, &n2, &n3, &n4, &n5, &n6, buff);
            if (x < 6)
                return 1;

            laddr = htonl((n1 << 24) | (n2 << 16) | (n3 << 8) | (n4));
            lport = htons((n5 << 8) | (n6));

            if ((so = tcp_listen(slirp, INADDR_ANY, 0, laddr, lport,
                                 SS_FACCEPTONCE)) == NULL) {
                return 1;
            }
            n6 = ntohs(so->so_fport);

            n5 = (n6 >> 8) & 0xff;
            n6 &= 0xff;

            laddr = ntohl(so->so_faddr.s_addr);

            n1 = ((laddr >> 24) & 0xff);
            n2 = ((laddr >> 16) & 0xff);
            n3 = ((laddr >> 8) & 0xff);
            n4 = (laddr & 0xff);

            m->m_len = bptr - m->m_data; /* Adjust length */
            m->m_len += slirp_fmt(bptr, M_FREEROOM(m),
                                  "27 Entering Passive Mode (%d,%d,%d,%d,%d,%d)\r\n%s",
                                  n1, n2, n3, n4, n5, n6, x == 7 ? buff : "");
            return 1;
        }

        return 1;

    case EMU_KSH:
        /*
         * The kshell (Kerberos rsh) and shell services both pass
         * a local port port number to carry signals to the server
         * and stderr to the client.  It is passed at the beginning
         * of the connection as a NUL-terminated decimal ASCII string.
         */
        so->so_emu = 0;
        for (lport = 0, i = 0; i < m->m_len - 1; ++i) {
            if (m->m_data[i] < '0' || m->m_data[i] > '9')
                return 1; /* invalid number */
            lport *= 10;
            lport += m->m_data[i] - '0';
        }
        if (m->m_data[m->m_len - 1] == '\0' && lport != 0 &&
            (so = tcp_listen(slirp, INADDR_ANY, 0, so->so_laddr.s_addr,
                             htons(lport), SS_FACCEPTONCE)) != NULL)
            m->m_len = slirp_fmt0(m->m_data, M_ROOM(m),
                                  "%d", ntohs(so->so_fport));
        return 1;

    case EMU_IRC:
        /*
         * Need to emulate DCC CHAT, DCC SEND and DCC MOVE
         */
        m_inc(m, m->m_len + 1);
        *(m->m_data + m->m_len) = 0; /* NULL terminate the string for strstr */
        if ((bptr = (char *)strstr(m->m_data, "DCC")) == NULL)
            return 1;

        /* The %256s is for the broken mIRC */
        if (sscanf(bptr, "DCC CHAT %256s %u %u", buff, &laddr, &lport) == 3) {
            if ((so = tcp_listen(slirp, INADDR_ANY, 0, htonl(laddr),
                                 htons(lport), SS_FACCEPTONCE)) == NULL) {
                return 1;
            }
            m->m_len = bptr - m->m_data; /* Adjust length */
            m->m_len += slirp_fmt(bptr, M_FREEROOM(m),
                                  "DCC CHAT chat %lu %u%c\n",
                                  (unsigned long)ntohl(so->so_faddr.s_addr),
                                  ntohs(so->so_fport), 1);
        } else if (sscanf(bptr, "DCC SEND %256s %u %u %u", buff, &laddr, &lport,
                          &n1) == 4) {
            if ((so = tcp_listen(slirp, INADDR_ANY, 0, htonl(laddr),
                                 htons(lport), SS_FACCEPTONCE)) == NULL) {
                return 1;
            }
            m->m_len = bptr - m->m_data; /* Adjust length */
            m->m_len += slirp_fmt(bptr, M_FREEROOM(m),
                                  "DCC SEND %s %lu %u %u%c\n", buff,
                                  (unsigned long)ntohl(so->so_faddr.s_addr),
                                  ntohs(so->so_fport), n1, 1);
        } else if (sscanf(bptr, "DCC MOVE %256s %u %u %u", buff, &laddr, &lport,
                          &n1) == 4) {
            if ((so = tcp_listen(slirp, INADDR_ANY, 0, htonl(laddr),
                                 htons(lport), SS_FACCEPTONCE)) == NULL) {
                return 1;
            }
            m->m_len = bptr - m->m_data; /* Adjust length */
            m->m_len += slirp_fmt(bptr, M_FREEROOM(m),
                                  "DCC MOVE %s %lu %u %u%c\n", buff,
                                  (unsigned long)ntohl(so->so_faddr.s_addr),
                                  ntohs(so->so_fport), n1, 1);
        }
        return 1;

    case EMU_REALAUDIO:
        /*
         * RealAudio emulation - JP. We must try to parse the incoming
         * data and try to find the two characters that contain the
         * port number. Then we redirect an udp port and replace the
         * number with the real port we got.
         *
         * The 1.0 beta versions of the player are not supported
         * any more.
         *
         * A typical packet for player version 1.0 (release version):
         *
         * 0000:50 4E 41 00 05
         * 0000:00 01 00 02 1B D7 00 00 67 E6 6C DC 63 00 12 50 ........g.l.c..P
         * 0010:4E 43 4C 49 45 4E 54 20 31 30 31 20 41 4C 50 48 NCLIENT 101 ALPH
         * 0020:41 6C 00 00 52 00 17 72 61 66 69 6C 65 73 2F 76 Al..R..rafiles/v
         * 0030:6F 61 2F 65 6E 67 6C 69 73 68 5F 2E 72 61 79 42 oa/english_.rayB
         *
         * Now the port number 0x1BD7 is found at offset 0x04 of the
         * Now the port number 0x1BD7 is found at offset 0x04 of the
         * second packet. This time we received five bytes first and
         * then the rest. You never know how many bytes you get.
         *
         * A typical packet for player version 2.0 (beta):
         *
         * 0000:50 4E 41 00 06 00 02 00 00 00 01 00 02 1B C1 00 PNA.............
         * 0010:00 67 75 78 F5 63 00 0A 57 69 6E 32 2E 30 2E 30 .gux.c..Win2.0.0
         * 0020:2E 35 6C 00 00 52 00 1C 72 61 66 69 6C 65 73 2F .5l..R..rafiles/
         * 0030:77 65 62 73 69 74 65 2F 32 30 72 65 6C 65 61 73 website/20releas
         * 0040:65 2E 72 61 79 53 00 00 06 36 42                e.rayS...6B
         *
         * Port number 0x1BC1 is found at offset 0x0d.
         *
         * This is just a horrible switch statement. Variable ra tells
         * us where we're going.
         */

        bptr = m->m_data;
        while (bptr < m->m_data + m->m_len) {
            uint16_t p;
            static int ra = 0;
            char ra_tbl[4];

            ra_tbl[0] = 0x50;
            ra_tbl[1] = 0x4e;
            ra_tbl[2] = 0x41;
            ra_tbl[3] = 0;

            switch (ra) {
            case 0:
            case 2:
            case 3:
                if (*bptr++ != ra_tbl[ra]) {
                    ra = 0;
                    continue;
                }
                break;

            case 1:
                /*
                 * We may get 0x50 several times, ignore them
                 */
                if (*bptr == 0x50) {
                    ra = 1;
                    bptr++;
                    continue;
                } else if (*bptr++ != ra_tbl[ra]) {
                    ra = 0;
                    continue;
                }
                break;

            case 4:
                /*
                 * skip version number
                 */
                bptr++;
                break;

            case 5:
                if (bptr == m->m_data + m->m_len - 1)
                        return 1; /* We need two bytes */

                /*
                 * The difference between versions 1.0 and
                 * 2.0 is here. For future versions of
                 * the player this may need to be modified.
                 */
                if (*(bptr + 1) == 0x02)
                    bptr += 8;
                else
                    bptr += 4;
                break;

            case 6:
                /* This is the field containing the port
                 * number that RA-player is listening to.
                 */

                if (bptr == m->m_data + m->m_len - 1)
                        return 1; /* We need two bytes */

                lport = (((uint8_t *)bptr)[0] << 8) + ((uint8_t *)bptr)[1];
                if (lport < 6970)
                    lport += 256; /* don't know why */
                if (lport < 6970 || lport > 7170)
                    return 1; /* failed */

                /* try to get udp port between 6970 - 7170 */
                for (p = 6970; p < 7071; p++) {
                    if (udp_listen(slirp, INADDR_ANY, htons(p),
                                   so->so_laddr.s_addr, htons(lport),
                                   SS_FACCEPTONCE)) {
                        break;
                    }
                }
                if (p == 7071)
                    p = 0;
                *(uint8_t *)bptr++ = (p >> 8) & 0xff;
                *(uint8_t *)bptr = p & 0xff;
                ra = 0;
                return 1; /* port redirected, we're done */
                break;

            default:
                ra = 0;
            }
            ra++;
        }
        return 1;

    default:
        /* Ooops, not emulated, won't call tcp_emu again */
        so->so_emu = 0;
        return 1;
    }
}

/*
 * Do misc. config of SLiRP while its running.
 * Return 0 if this connections is to be closed, 1 otherwise,
 * return 2 if this is a command-line connection
 */
int tcp_ctl(struct socket *so)
{
    Slirp *slirp = so->slirp;
    struct sbuf *sb = &so->so_snd;
    struct gfwd_list *ex_ptr;

    DEBUG_CALL("tcp_ctl");
    DEBUG_ARG("so = %p", so);

    /* TODO: IPv6 */
    if (so->so_faddr.s_addr != slirp->vhost_addr.s_addr) {
        /* Check if it's pty_exec */
        for (ex_ptr = slirp->guestfwd_list; ex_ptr; ex_ptr = ex_ptr->ex_next) {
            if (ex_ptr->ex_fport == so->so_fport &&
                so->so_faddr.s_addr == ex_ptr->ex_addr.s_addr) {
                if (ex_ptr->write_cb) {
                    so->s = -1;
                    so->guestfwd = ex_ptr;
                    return 1;
                }
                DEBUG_MISC(" executing %s", ex_ptr->ex_exec);
                if (ex_ptr->ex_unix)
                    return open_unix(so, ex_ptr->ex_unix);
                else
                    return fork_exec(so, ex_ptr->ex_exec);
            }
        }
    }
    sb->sb_cc = slirp_fmt(sb->sb_wptr, sb->sb_datalen - (sb->sb_wptr - sb->sb_data),
                          "Error: No application configured.\r\n");
    sb->sb_wptr += sb->sb_cc;
    return 0;
}
