/* SPDX-License-Identifier: BSD-3-Clause */
/*
 * Copyright (c) 1995 Danny Gasparovski.
 */

#include "slirp.h"
#include "ip_icmp.h"
#ifdef __sun__
#include <sys/filio.h>
#endif
#ifdef __linux__
#include <linux/errqueue.h>
#endif

static void sofcantrcvmore(struct socket *so);
static void sofcantsendmore(struct socket *so);

struct socket *solookup(struct socket **last, struct socket *head,
                        struct sockaddr_storage *lhost,
                        struct sockaddr_storage *fhost)
{
    struct socket *so = *last;

    /* Optimisation */
    if (so != head && sockaddr_equal(&(so->lhost.ss), lhost) &&
        (!fhost || sockaddr_equal(&so->fhost.ss, fhost))) {
        return so;
    }

    for (so = head->so_next; so != head; so = so->so_next) {
        if (sockaddr_equal(&(so->lhost.ss), lhost) &&
            (!fhost || sockaddr_equal(&so->fhost.ss, fhost))) {
            *last = so;
            return so;
        }
    }

    return (struct socket *)NULL;
}

/*
 * Create a new socket, initialise the fields
 * It is the responsibility of the caller to
 * slirp_insque() it into the correct linked-list
 */
struct socket *socreate(Slirp *slirp, int type)
{
    struct socket *so = g_new(struct socket, 1);

    memset(so, 0, sizeof(struct socket));
    so->so_type = type;
    so->so_state = SS_NOFDREF;
    so->s = -1;
    so->s_aux = -1;
    so->slirp = slirp;
    so->pollfds_idx = -1;

    return so;
}

/*
 * Remove references to so from the given message queue.
 */
static void soqfree(struct socket *so, struct slirp_quehead *qh)
{
    struct mbuf *ifq;

    for (ifq = (struct mbuf *)qh->qh_link; (struct slirp_quehead *)ifq != qh;
         ifq = ifq->ifq_next) {
        if (ifq->ifq_so == so) {
            struct mbuf *ifm;
            ifq->ifq_so = NULL;
            for (ifm = ifq->ifs_next; ifm != ifq; ifm = ifm->ifs_next) {
                ifm->ifq_so = NULL;
            }
        }
    }
}

/*
 * slirp_remque and free a socket, clobber cache
 */
void sofree(struct socket *so)
{
    Slirp *slirp = so->slirp;

    if (so->s_aux != -1) {
        closesocket(so->s_aux);
    }

    soqfree(so, &slirp->if_fastq);
    soqfree(so, &slirp->if_batchq);

    if (so == slirp->tcp_last_so) {
        slirp->tcp_last_so = &slirp->tcb;
    } else if (so == slirp->udp_last_so) {
        slirp->udp_last_so = &slirp->udb;
    } else if (so == slirp->icmp_last_so) {
        slirp->icmp_last_so = &slirp->icmp;
    }
    m_free(so->so_m);

    if (so->so_next && so->so_prev)
        slirp_remque(so); /* crashes if so is not in a queue */

    if (so->so_tcpcb) {
        g_free(so->so_tcpcb);
    }
    g_free(so);
}

size_t sopreprbuf(struct socket *so, struct iovec *iov, int *np)
{
    int n, lss, total;
    struct sbuf *sb = &so->so_snd;
    int len = sb->sb_datalen - sb->sb_cc;
    int mss = so->so_tcpcb->t_maxseg;

    DEBUG_CALL("sopreprbuf");
    DEBUG_ARG("so = %p", so);

    if (len <= 0)
        return 0;

    iov[0].iov_base = sb->sb_wptr;
    iov[1].iov_base = NULL;
    iov[1].iov_len = 0;
    if (sb->sb_wptr < sb->sb_rptr) {
        iov[0].iov_len = sb->sb_rptr - sb->sb_wptr;
        /* Should never succeed, but... */
        if (iov[0].iov_len > len)
            iov[0].iov_len = len;
        if (iov[0].iov_len > mss)
            iov[0].iov_len -= iov[0].iov_len % mss;
        n = 1;
    } else {
        iov[0].iov_len = (sb->sb_data + sb->sb_datalen) - sb->sb_wptr;
        /* Should never succeed, but... */
        if (iov[0].iov_len > len)
            iov[0].iov_len = len;
        len -= iov[0].iov_len;
        if (len) {
            iov[1].iov_base = sb->sb_data;
            iov[1].iov_len = sb->sb_rptr - sb->sb_data;
            if (iov[1].iov_len > len)
                iov[1].iov_len = len;
            total = iov[0].iov_len + iov[1].iov_len;
            if (total > mss) {
                lss = total % mss;
                if (iov[1].iov_len > lss) {
                    iov[1].iov_len -= lss;
                    n = 2;
                } else {
                    lss -= iov[1].iov_len;
                    iov[0].iov_len -= lss;
                    n = 1;
                }
            } else
                n = 2;
        } else {
            if (iov[0].iov_len > mss)
                iov[0].iov_len -= iov[0].iov_len % mss;
            n = 1;
        }
    }
    if (np)
        *np = n;

    return iov[0].iov_len + (n - 1) * iov[1].iov_len;
}

/*
 * Read from so's socket into sb_snd, updating all relevant sbuf fields
 * NOTE: This will only be called if it is select()ed for reading, so
 * a read() of 0 (or less) means it's disconnected
 */
int soread(struct socket *so)
{
    int n, nn;
    size_t buf_len;
    struct sbuf *sb = &so->so_snd;
    struct iovec iov[2];

    DEBUG_CALL("soread");
    DEBUG_ARG("so = %p", so);

    /*
     * No need to check if there's enough room to read.
     * soread wouldn't have been called if there weren't
     */
    buf_len = sopreprbuf(so, iov, &n);
    assert(buf_len != 0);

    nn = recv(so->s, iov[0].iov_base, iov[0].iov_len, 0);
    if (nn <= 0) {
        if (nn < 0 && (errno == EINTR || errno == EAGAIN))
            return 0;
        else {
            int err;
            socklen_t elen = sizeof err;
            struct sockaddr_storage addr;
            struct sockaddr *paddr = (struct sockaddr *)&addr;
            socklen_t alen = sizeof addr;

            err = errno;
            if (nn == 0) {
                int shutdown_wr = so->so_state & SS_FCANTSENDMORE;

                if (!shutdown_wr && getpeername(so->s, paddr, &alen) < 0) {
                    err = errno;
                } else {
                    getsockopt(so->s, SOL_SOCKET, SO_ERROR, &err, &elen);
                }
            }

            DEBUG_MISC(" --- soread() disconnected, nn = %d, errno = %d-%s", nn,
                       errno, strerror(errno));
            sofcantrcvmore(so);

            if (err == ECONNABORTED || err == ECONNRESET || err == ECONNREFUSED ||
                err == ENOTCONN || err == EPIPE) {
                tcp_drop(sototcpcb(so), err);
            } else {
                tcp_sockclosed(sototcpcb(so));
            }
            return -1;
        }
    }

    /*
     * If there was no error, try and read the second time round
     * We read again if n = 2 (ie, there's another part of the buffer)
     * and we read as much as we could in the first read
     * We don't test for <= 0 this time, because there legitimately
     * might not be any more data (since the socket is non-blocking),
     * a close will be detected on next iteration.
     * A return of -1 won't (shouldn't) happen, since it didn't happen above
     */
    if (n == 2 && nn == iov[0].iov_len) {
        int ret;
        ret = recv(so->s, iov[1].iov_base, iov[1].iov_len, 0);
        if (ret > 0)
            nn += ret;
    }

    DEBUG_MISC(" ... read nn = %d bytes", nn);

    /* Update fields */
    sb->sb_cc += nn;
    sb->sb_wptr += nn;
    if (sb->sb_wptr >= (sb->sb_data + sb->sb_datalen))
        sb->sb_wptr -= sb->sb_datalen;
    return nn;
}

int soreadbuf(struct socket *so, const char *buf, int size)
{
    int n, nn, copy = size;
    struct sbuf *sb = &so->so_snd;
    struct iovec iov[2];

    DEBUG_CALL("soreadbuf");
    DEBUG_ARG("so = %p", so);

    /*
     * No need to check if there's enough room to read.
     * soread wouldn't have been called if there weren't
     */
    assert(size > 0);
    if (sopreprbuf(so, iov, &n) < size)
        goto err;

    nn = MIN(iov[0].iov_len, copy);
    memcpy(iov[0].iov_base, buf, nn);

    copy -= nn;
    buf += nn;

    if (copy == 0)
        goto done;

    memcpy(iov[1].iov_base, buf, copy);

done:
    /* Update fields */
    sb->sb_cc += size;
    sb->sb_wptr += size;
    if (sb->sb_wptr >= (sb->sb_data + sb->sb_datalen))
        sb->sb_wptr -= sb->sb_datalen;
    return size;
err:

    sofcantrcvmore(so);
    tcp_sockclosed(sototcpcb(so));
    g_critical("soreadbuf buffer too small");
    return -1;
}

/*
 * Get urgent data
 *
 * When the socket is created, we set it SO_OOBINLINE,
 * so when OOB data arrives, we soread() it and everything
 * in the send buffer is sent as urgent data
 */
int sorecvoob(struct socket *so)
{
    struct tcpcb *tp = sototcpcb(so);
    int ret;

    DEBUG_CALL("sorecvoob");
    DEBUG_ARG("so = %p", so);

    /*
     * We take a guess at how much urgent data has arrived.
     * In most situations, when urgent data arrives, the next
     * read() should get all the urgent data.  This guess will
     * be wrong however if more data arrives just after the
     * urgent data, or the read() doesn't return all the
     * urgent data.
     */
    ret = soread(so);
    if (ret > 0) {
        tp->snd_up = tp->snd_una + so->so_snd.sb_cc;
        tp->t_force = 1;
        tcp_output(tp);
        tp->t_force = 0;
    }

    return ret;
}

/*
 * Send urgent data
 * There's a lot duplicated code here, but...
 */
int sosendoob(struct socket *so)
{
    struct sbuf *sb = &so->so_rcv;
    char buff[2048]; /* XXX Shouldn't be sending more oob data than this */

    int n;

    DEBUG_CALL("sosendoob");
    DEBUG_ARG("so = %p", so);
    DEBUG_ARG("sb->sb_cc = %d", sb->sb_cc);

    if (so->so_urgc > sizeof(buff))
        so->so_urgc = sizeof(buff); /* XXXX */

    if (sb->sb_rptr < sb->sb_wptr) {
        /* We can send it directly */
        n = slirp_send(so, sb->sb_rptr, so->so_urgc,
                       (MSG_OOB)); /* |MSG_DONTWAIT)); */
    } else {
        /*
         * Since there's no sendv or sendtov like writev,
         * we must copy all data to a linear buffer then
         * send it all
         */
        uint32_t urgc = so->so_urgc; /* Amount of room left in buff */
        int len = (sb->sb_data + sb->sb_datalen) - sb->sb_rptr;
        if (len > urgc) {
            len = urgc;
        }
        memcpy(buff, sb->sb_rptr, len);
        urgc -= len;
        if (urgc) {
            /* We still have some room for the rest */
            n = sb->sb_wptr - sb->sb_data;
            if (n > urgc) {
                n = urgc;
            }
            memcpy((buff + len), sb->sb_data, n);
            len += n;
        }
        n = slirp_send(so, buff, len, (MSG_OOB)); /* |MSG_DONTWAIT)); */
#ifdef SLIRP_DEBUG
        if (n != len) {
            DEBUG_ERROR("Didn't send all data urgently XXXXX");
        }
#endif
    }

    if (n < 0) {
        return n;
    }
    so->so_urgc -= n;
    DEBUG_MISC(" ---2 sent %d bytes urgent data, %d urgent bytes left", n,
               so->so_urgc);

    sb->sb_cc -= n;
    sb->sb_rptr += n;
    if (sb->sb_rptr >= (sb->sb_data + sb->sb_datalen))
        sb->sb_rptr -= sb->sb_datalen;

    return n;
}

/*
 * Write data from so_rcv to so's socket,
 * updating all sbuf field as necessary
 */
int sowrite(struct socket *so)
{
    int n, nn;
    struct sbuf *sb = &so->so_rcv;
    int len = sb->sb_cc;
    struct iovec iov[2];

    DEBUG_CALL("sowrite");
    DEBUG_ARG("so = %p", so);

    if (so->so_urgc) {
        uint32_t expected = so->so_urgc;
        if (sosendoob(so) < expected) {
            /* Treat a short write as a fatal error too,
             * rather than continuing on and sending the urgent
             * data as if it were non-urgent and leaving the
             * so_urgc count wrong.
             */
            goto err_disconnected;
        }
        if (sb->sb_cc == 0)
            return 0;
    }

    /*
     * No need to check if there's something to write,
     * sowrite wouldn't have been called otherwise
     */

    iov[0].iov_base = sb->sb_rptr;
    iov[1].iov_base = NULL;
    iov[1].iov_len = 0;
    if (sb->sb_rptr < sb->sb_wptr) {
        iov[0].iov_len = sb->sb_wptr - sb->sb_rptr;
        /* Should never succeed, but... */
        if (iov[0].iov_len > len)
            iov[0].iov_len = len;
        n = 1;
    } else {
        iov[0].iov_len = (sb->sb_data + sb->sb_datalen) - sb->sb_rptr;
        if (iov[0].iov_len > len)
            iov[0].iov_len = len;
        len -= iov[0].iov_len;
        if (len) {
            iov[1].iov_base = sb->sb_data;
            iov[1].iov_len = sb->sb_wptr - sb->sb_data;
            if (iov[1].iov_len > len)
                iov[1].iov_len = len;
            n = 2;
        } else
            n = 1;
    }
    /* Check if there's urgent data to send, and if so, send it */

    nn = slirp_send(so, iov[0].iov_base, iov[0].iov_len, 0);
    /* This should never happen, but people tell me it does *shrug* */
    if (nn < 0 && (errno == EAGAIN || errno == EINTR))
        return 0;

    if (nn <= 0) {
        goto err_disconnected;
    }

    if (n == 2 && nn == iov[0].iov_len) {
        int ret;
        ret = slirp_send(so, iov[1].iov_base, iov[1].iov_len, 0);
        if (ret > 0)
            nn += ret;
    }
    DEBUG_MISC("  ... wrote nn = %d bytes", nn);

    /* Update sbuf */
    sb->sb_cc -= nn;
    sb->sb_rptr += nn;
    if (sb->sb_rptr >= (sb->sb_data + sb->sb_datalen))
        sb->sb_rptr -= sb->sb_datalen;

    /*
     * If in DRAIN mode, and there's no more data, set
     * it CANTSENDMORE
     */
    if ((so->so_state & SS_FWDRAIN) && sb->sb_cc == 0)
        sofcantsendmore(so);

    return nn;

err_disconnected:
    DEBUG_MISC(" --- sowrite disconnected, so->so_state = %x, errno = %d",
               so->so_state, errno);
    sofcantsendmore(so);
    tcp_sockclosed(sototcpcb(so));
    return -1;
}

/*
 * recvfrom() a UDP socket
 */
void sorecvfrom(struct socket *so)
{
    struct sockaddr_storage addr;
    struct sockaddr_storage saddr, daddr;
    socklen_t addrlen = sizeof(struct sockaddr_storage);
    char buff[256];

#ifdef __linux__
    ssize_t size;
    struct msghdr msg;
    struct iovec iov;
    char control[1024];

    /* First look for errors */
    memset(&msg, 0, sizeof(msg));
    msg.msg_name = &saddr;
    msg.msg_namelen = sizeof(saddr);
    msg.msg_control = control;
    msg.msg_controllen = sizeof(control);
    iov.iov_base = buff;
    iov.iov_len = sizeof(buff);
    msg.msg_iov = &iov;
    msg.msg_iovlen = 1;

    size = recvmsg(so->s, &msg, MSG_ERRQUEUE);
    if (size >= 0) {
        struct cmsghdr *cmsg;
        for (cmsg = CMSG_FIRSTHDR(&msg); cmsg; cmsg = CMSG_NXTHDR(&msg, cmsg)) {

            if (cmsg->cmsg_level == IPPROTO_IP &&
                cmsg->cmsg_type == IP_RECVERR) {
                struct sock_extended_err *ee =
                    (struct sock_extended_err *) CMSG_DATA(cmsg);

                if (ee->ee_origin == SO_EE_ORIGIN_ICMP) {
                    /* Got an ICMP error, forward it */
                    struct sockaddr_in *sin;

                    sin = (struct sockaddr_in *) SO_EE_OFFENDER(ee);
                    icmp_forward_error(so->so_m, ee->ee_type, ee->ee_code,
                                       0, NULL, &sin->sin_addr);
                }
            }
            else if (cmsg->cmsg_level == IPPROTO_IPV6 &&
                     cmsg->cmsg_type == IPV6_RECVERR) {
                struct sock_extended_err *ee =
                    (struct sock_extended_err *) CMSG_DATA(cmsg);

                if (ee->ee_origin == SO_EE_ORIGIN_ICMP6) {
                    /* Got an ICMPv6 error, forward it */
                    struct sockaddr_in6 *sin6;

                    sin6 = (struct sockaddr_in6 *) SO_EE_OFFENDER(ee);
                    icmp6_forward_error(so->so_m, ee->ee_type, ee->ee_code,
                                        &sin6->sin6_addr);
                }
            }
        }
        return;
    }
#endif

    DEBUG_CALL("sorecvfrom");
    DEBUG_ARG("so = %p", so);

    if (so->so_type == IPPROTO_ICMP) { /* This is a "ping" reply */
        int len;

        len = recvfrom(so->s, buff, 256, 0, (struct sockaddr *)&addr, &addrlen);
        /* XXX Check if reply is "correct"? */

        if (len == -1 || len == 0) {
            uint8_t code = ICMP_UNREACH_PORT;

            if (errno == EHOSTUNREACH)
                code = ICMP_UNREACH_HOST;
            else if (errno == ENETUNREACH)
                code = ICMP_UNREACH_NET;

            DEBUG_MISC(" udp icmp rx errno = %d-%s", errno, strerror(errno));
            icmp_send_error(so->so_m, ICMP_UNREACH, code, 0, strerror(errno));
        } else {
            icmp_reflect(so->so_m);
            so->so_m = NULL; /* Don't m_free() it again! */
        }
        /* No need for this socket anymore, udp_detach it */
        udp_detach(so);
    } else { /* A "normal" UDP packet */
        struct mbuf *m;
        int len;
#ifdef _WIN32
        unsigned long n;
#else
        int n;
#endif

        if (ioctlsocket(so->s, FIONREAD, &n) != 0) {
            DEBUG_MISC(" ioctlsocket errno = %d-%s\n", errno, strerror(errno));
            return;
        }

        m = m_get(so->slirp);
        if (!m) {
            return;
        }
        switch (so->so_ffamily) {
        case AF_INET:
            m->m_data += IF_MAXLINKHDR + sizeof(struct udpiphdr);
            break;
        case AF_INET6:
            m->m_data +=
                IF_MAXLINKHDR + sizeof(struct ip6) + sizeof(struct udphdr);
            break;
        default:
            g_assert_not_reached();
        }

        /*
         * XXX Shouldn't FIONREAD packets destined for port 53,
         * but I don't know the max packet size for DNS lookups
         */
        len = M_FREEROOM(m);
        /* if (so->so_fport != htons(53)) { */

        if (n > len) {
            n = (m->m_data - m->m_dat) + m->m_len + n + 1;
            m_inc(m, n);
            len = M_FREEROOM(m);
        }
        /* } */

        m->m_len = recvfrom(so->s, m->m_data, len, 0, (struct sockaddr *)&addr,
                            &addrlen);
        DEBUG_MISC(" did recvfrom %d, errno = %d-%s", m->m_len, errno,
                   strerror(errno));
        if (m->m_len < 0) {    	
            if (errno == ENOTCONN) {
                /*
                 * UDP socket got burnt, e.g. by suspend on iOS. Tear it down
                 * and let it get re-created if the guest still needs it
                 */
                udp_detach(so);
            } else {
                /* Report error as ICMP */
                switch (so->so_lfamily) {
                    uint8_t code;
                case AF_INET:
                    code = ICMP_UNREACH_PORT;

                    if (errno == EHOSTUNREACH) {
                        code = ICMP_UNREACH_HOST;
                    } else if (errno == ENETUNREACH) {
                        code = ICMP_UNREACH_NET;
                    }

                    DEBUG_MISC(" rx error, tx icmp ICMP_UNREACH:%i", code);
                    icmp_send_error(so->so_m, ICMP_UNREACH, code, 0,
                                    strerror(errno));
                    break;
                case AF_INET6:
                    code = ICMP6_UNREACH_PORT;

                    if (errno == EHOSTUNREACH) {
                        code = ICMP6_UNREACH_ADDRESS;
                    } else if (errno == ENETUNREACH) {
                        code = ICMP6_UNREACH_NO_ROUTE;
                    }

                    DEBUG_MISC(" rx error, tx icmp6 ICMP_UNREACH:%i", code);
                    icmp6_send_error(so->so_m, ICMP6_UNREACH, code);
                    break;
                default:
                    g_assert_not_reached();
                }
                m_free(m);
            }
        } else {
            /*
             * Hack: domain name lookup will be used the most for UDP,
             * and since they'll only be used once there's no need
             * for the 4 minute (or whatever) timeout... So we time them
             * out much quicker (10 seconds  for now...)
             */
            if (so->so_expire) {
                if (so->so_fport == htons(53))
                    so->so_expire = curtime + SO_EXPIREFAST;
                else
                    so->so_expire = curtime + SO_EXPIRE;
            }

            /*
             * If this packet was destined for CTL_ADDR,
             * make it look like that's where it came from
             */
            saddr = addr;
            sotranslate_in(so, &saddr);

            /* Perform lazy guest IP address resolution if needed. */
            if (so->so_state & SS_HOSTFWD) {
                if (soassign_guest_addr_if_needed(so) < 0) {
                    DEBUG_MISC(" guest address not available yet");
                    switch (so->so_lfamily) {
                    case AF_INET:
                        icmp_send_error(so->so_m, ICMP_UNREACH,
                                        ICMP_UNREACH_HOST, 0,
                                        "guest address not available yet");
                        break;
                    case AF_INET6:
                        icmp6_send_error(so->so_m, ICMP6_UNREACH,
                                         ICMP6_UNREACH_ADDRESS);
                        break;
                    default:
                        g_assert_not_reached();
                    }
                    m_free(m);
                    return;
                }
            }
            daddr = so->lhost.ss;

            switch (so->so_ffamily) {
            case AF_INET:
                udp_output(so, m, (struct sockaddr_in *)&saddr,
                           (struct sockaddr_in *)&daddr, so->so_iptos);
                break;
            case AF_INET6:
                udp6_output(so, m, (struct sockaddr_in6 *)&saddr,
                            (struct sockaddr_in6 *)&daddr);
                break;
            default:
                g_assert_not_reached();
            }
        } /* rx error */
    } /* if ping packet */
}

/*
 * sendto() a socket
 */
int sosendto(struct socket *so, struct mbuf *m)
{
    int ret;
    struct sockaddr_storage addr;

    DEBUG_CALL("sosendto");
    DEBUG_ARG("so = %p", so);
    DEBUG_ARG("m = %p", m);

    addr = so->fhost.ss;
    DEBUG_CALL(" sendto()ing)");
    if (sotranslate_out(so, &addr) < 0) {
        return -1;
    }

    /* Don't care what port we get */
    ret = sendto(so->s, m->m_data, m->m_len, 0, (struct sockaddr *)&addr,
                 sockaddr_size(&addr));
    if (ret < 0)
        return -1;

    /*
     * Kill the socket if there's no reply in 4 minutes,
     * but only if it's an expirable socket
     */
    if (so->so_expire)
        so->so_expire = curtime + SO_EXPIRE;
    so->so_state &= SS_PERSISTENT_MASK;
    so->so_state |= SS_ISFCONNECTED; /* So that it gets select()ed */
    return 0;
}

/*
 * Listen for incoming TCP connections
 * On failure errno contains the reason.
 */
struct socket *tcpx_listen(Slirp *slirp,
                           const struct sockaddr *haddr, socklen_t haddrlen,
                           const struct sockaddr *laddr, socklen_t laddrlen,
                           int flags)
{
    struct socket *so;
    int s, opt = 1;
    socklen_t addrlen;

    DEBUG_CALL("tcpx_listen");
    /* AF_INET6 addresses are bigger than AF_INET, so this is big enough. */
    char addrstr[INET6_ADDRSTRLEN];
    char portstr[6];
    int ret;
    switch (haddr->sa_family) {
    case AF_INET:
    case AF_INET6:
        ret = getnameinfo(haddr, haddrlen, addrstr, sizeof(addrstr), portstr, sizeof(portstr), NI_NUMERICHOST|NI_NUMERICSERV);
        g_assert(ret == 0);
        DEBUG_ARG("hfamily = INET");
        DEBUG_ARG("haddr = %s", addrstr);
        DEBUG_ARG("hport = %s", portstr);
        break;
#ifndef _WIN32
    case AF_UNIX:
        DEBUG_ARG("hfamily = UNIX");
        DEBUG_ARG("hpath = %s", ((struct sockaddr_un *) haddr)->sun_path);
        break;
#endif
    default:
        g_assert_not_reached();
    }
    switch (laddr->sa_family) {
    case AF_INET:
    case AF_INET6:
        ret = getnameinfo(laddr, laddrlen, addrstr, sizeof(addrstr), portstr, sizeof(portstr), NI_NUMERICHOST|NI_NUMERICSERV);
        g_assert(ret == 0);
        DEBUG_ARG("laddr = %s", addrstr);
        DEBUG_ARG("lport = %s", portstr);
        break;
    default:
        g_assert_not_reached();
    }
    DEBUG_ARG("flags = %x", flags);

    /*
     * SS_HOSTFWD sockets can be accepted multiple times, so they can't be
     * SS_FACCEPTONCE. Also, SS_HOSTFWD connections can be accepted and
     * immediately closed if the guest address isn't available yet, which is
     * incompatible with the "accept once" concept. Correct code will never
     * request both, so disallow their combination by assertion.
     */
    g_assert(!((flags & SS_HOSTFWD) && (flags & SS_FACCEPTONCE)));

    so = socreate(slirp, IPPROTO_TCP);

    /* Don't tcp_attach... we don't need so_snd nor so_rcv */
    so->so_tcpcb = tcp_newtcpcb(so);
    slirp_insque(so, &slirp->tcb);

    /*
     * SS_FACCEPTONCE sockets must time out.
     */
    if (flags & SS_FACCEPTONCE)
        so->so_tcpcb->t_timer[TCPT_KEEP] = TCPTV_KEEP_INIT * 2;

    so->so_state &= SS_PERSISTENT_MASK;
    so->so_state |= (SS_FACCEPTCONN | flags);

    sockaddr_copy(&so->lhost.sa, sizeof(so->lhost), laddr, laddrlen);

    s = slirp_socket(haddr->sa_family, SOCK_STREAM, 0);
    if ((s < 0) ||
        (haddr->sa_family == AF_INET6 && slirp_socket_set_v6only(s, (flags & SS_HOSTFWD_V6ONLY) != 0) < 0) ||
        (slirp_socket_set_fast_reuse(s) < 0) ||
        (bind(s, haddr, haddrlen) < 0) ||
        (listen(s, 1) < 0)) {
        int tmperrno = errno; /* Don't clobber the real reason we failed */
        if (s >= 0) {
            closesocket(s);
        }
        sofree(so);
        /* Restore the real errno */
#ifdef _WIN32
        WSASetLastError(tmperrno);
#else
        errno = tmperrno;
#endif
        return NULL;
    }
    setsockopt(s, SOL_SOCKET, SO_OOBINLINE, &opt, sizeof(int));
    slirp_socket_set_nodelay(s);

    addrlen = sizeof(so->fhost);
    getsockname(s, &so->fhost.sa, &addrlen);
    sotranslate_accept(so);

    so->s = s;
    return so;
}

struct socket *tcp_listen(Slirp *slirp, uint32_t haddr, unsigned hport,
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

    return tcpx_listen(slirp, (const struct sockaddr *) &hsa, sizeof(hsa), (struct sockaddr *) &lsa, sizeof(lsa), flags);
}

/*
 * Various session state calls
 * XXX Should be #define's
 * The socket state stuff needs work, these often get call 2 or 3
 * times each when only 1 was needed
 */
void soisfconnecting(struct socket *so)
{
    so->so_state &= ~(SS_NOFDREF | SS_ISFCONNECTED | SS_FCANTRCVMORE |
                      SS_FCANTSENDMORE | SS_FWDRAIN);
    so->so_state |= SS_ISFCONNECTING; /* Clobber other states */
}

void soisfconnected(struct socket *so)
{
    so->so_state &= ~(SS_ISFCONNECTING | SS_FWDRAIN | SS_NOFDREF);
    so->so_state |= SS_ISFCONNECTED; /* Clobber other states */
}

static void sofcantrcvmore(struct socket *so)
{
    if ((so->so_state & SS_NOFDREF) == 0) {
        shutdown(so->s, 0);
    }
    so->so_state &= ~(SS_ISFCONNECTING);
    if (so->so_state & SS_FCANTSENDMORE) {
        so->so_state &= SS_PERSISTENT_MASK;
        so->so_state |= SS_NOFDREF; /* Don't select it */
    } else {
        so->so_state |= SS_FCANTRCVMORE;
    }
}

static void sofcantsendmore(struct socket *so)
{
    if ((so->so_state & SS_NOFDREF) == 0) {
        shutdown(so->s, 1); /* send FIN to fhost */
    }
    so->so_state &= ~(SS_ISFCONNECTING);
    if (so->so_state & SS_FCANTRCVMORE) {
        so->so_state &= SS_PERSISTENT_MASK;
        so->so_state |= SS_NOFDREF; /* as above */
    } else {
        so->so_state |= SS_FCANTSENDMORE;
    }
}

/*
 * Set write drain mode
 * Set CANTSENDMORE once all data has been write()n
 */
void sofwdrain(struct socket *so)
{
    if (so->so_rcv.sb_cc)
        so->so_state |= SS_FWDRAIN;
    else
        sofcantsendmore(so);
}

static bool sotranslate_out4(Slirp *s, struct socket *so, struct sockaddr_in *sin)
{
    if (!s->disable_dns && so->so_faddr.s_addr == s->vnameserver_addr.s_addr) {
        return so->so_fport == htons(53) && get_dns_addr(&sin->sin_addr) >= 0;
    }

    if (so->so_faddr.s_addr == s->vhost_addr.s_addr ||
        so->so_faddr.s_addr == 0xffffffff) {
        if (s->disable_host_loopback) {
            return false;
        }

        sin->sin_addr = loopback_addr;
    }

    return true;
}

static bool sotranslate_out6(Slirp *s, struct socket *so, struct sockaddr_in6 *sin)
{
    if (!s->disable_dns && in6_equal(&so->so_faddr6, &s->vnameserver_addr6)) {
        uint32_t scope_id;
        if (so->so_fport == htons(53) && get_dns6_addr(&sin->sin6_addr, &scope_id) >= 0) {
            sin->sin6_scope_id = scope_id;
            return true;
        }
        return false;
    }

    if (in6_equal_net(&so->so_faddr6, &s->vprefix_addr6, s->vprefix_len) ||
        in6_equal(&so->so_faddr6, &(struct in6_addr)ALLNODES_MULTICAST)) {
        if (s->disable_host_loopback) {
            return false;
        }

        sin->sin6_addr = in6addr_loopback;
    }

    return true;
}


/*
 * Translate addr in host addr when it is a virtual address
 */
int sotranslate_out(struct socket *so, struct sockaddr_storage *addr)
{
    bool ok = true;

    switch (addr->ss_family) {
    case AF_INET:
        ok = sotranslate_out4(so->slirp, so, (struct sockaddr_in *)addr);
        break;
    case AF_INET6:
        ok = sotranslate_out6(so->slirp, so, (struct sockaddr_in6 *)addr);
        break;
    }

    if (!ok) {
        errno = EPERM;
        return -1;
    }

    return 0;
}

void sotranslate_in(struct socket *so, struct sockaddr_storage *addr)
{
    Slirp *slirp = so->slirp;
    struct sockaddr_in *sin = (struct sockaddr_in *)addr;
    struct sockaddr_in6 *sin6 = (struct sockaddr_in6 *)addr;

    switch (addr->ss_family) {
    case AF_INET:
        if ((so->so_faddr.s_addr & slirp->vnetwork_mask.s_addr) ==
            slirp->vnetwork_addr.s_addr) {
            uint32_t inv_mask = ~slirp->vnetwork_mask.s_addr;

            if ((so->so_faddr.s_addr & inv_mask) == inv_mask) {
                sin->sin_addr = slirp->vhost_addr;
            } else if (sin->sin_addr.s_addr == loopback_addr.s_addr ||
                       so->so_faddr.s_addr != slirp->vhost_addr.s_addr) {
                sin->sin_addr = so->so_faddr;
            }
        }
        break;

    case AF_INET6:
        if (in6_equal_net(&so->so_faddr6, &slirp->vprefix_addr6,
                          slirp->vprefix_len)) {
            if (in6_equal(&sin6->sin6_addr, &in6addr_loopback) ||
                !in6_equal(&so->so_faddr6, &slirp->vhost_addr6)) {
                sin6->sin6_addr = so->so_faddr6;
            }
        }
        break;

    default:
        break;
    }
}

/*
 * Translate connections from localhost to the real hostname
 */
void sotranslate_accept(struct socket *so)
{
    Slirp *slirp = so->slirp;

    switch (so->so_ffamily) {
    case AF_INET:
        if (so->so_faddr.s_addr == INADDR_ANY ||
            (so->so_faddr.s_addr & loopback_mask) ==
                (loopback_addr.s_addr & loopback_mask)) {
            so->so_faddr = slirp->vhost_addr;
        }
        break;

    case AF_INET6:
        if (in6_equal(&so->so_faddr6, &in6addr_any) ||
            in6_equal(&so->so_faddr6, &in6addr_loopback)) {
            so->so_faddr6 = slirp->vhost_addr6;
        }
        break;

    case AF_UNIX: {
        /* Translate Unix socket to random ephemeral source port. We obtain
         * this source port by binding to port 0 so that the OS allocates a
         * port for us. If this fails, we fall back to choosing a random port
         * with a random number generator. */
        int s;
        struct sockaddr_in in_addr;
        struct sockaddr_in6 in6_addr;
        socklen_t in_addr_len;

        if (so->slirp->in_enabled) {
            so->so_ffamily = AF_INET;
            so->so_faddr = slirp->vhost_addr;
            so->so_fport = 0;

            switch (so->so_type) {
            case IPPROTO_TCP:
                s = slirp_socket(PF_INET, SOCK_STREAM, 0);
                break;
            case IPPROTO_UDP:
                s = slirp_socket(PF_INET, SOCK_DGRAM, 0);
                break;
            default:
                g_assert_not_reached();
                break;
            }
            if (s < 0) {
                g_error("Ephemeral slirp_socket() allocation failed");
                goto unix2inet_cont;
            }
            memset(&in_addr, 0, sizeof(in_addr));
            in_addr.sin_family = AF_INET;
            in_addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
            in_addr.sin_port = htons(0);
            if (bind(s, (struct sockaddr *) &in_addr, sizeof(in_addr))) {
                g_error("Ephemeral bind() failed");
                closesocket(s);
                goto unix2inet_cont;
            }
            in_addr_len = sizeof(in_addr);
            if (getsockname(s, (struct sockaddr *) &in_addr, &in_addr_len)) {
                g_error("Ephemeral getsockname() failed");
                closesocket(s);
                goto unix2inet_cont;
            }
            so->s_aux = s;
            so->so_fport = in_addr.sin_port;

unix2inet_cont:
            if (!so->so_fport) {
                g_warning("Falling back to random port allocation");
                so->so_fport = htons(g_rand_int_range(slirp->grand, 49152, 65536));
            }
        } else if (so->slirp->in6_enabled) {
            so->so_ffamily = AF_INET6;
            so->so_faddr6 = slirp->vhost_addr6;
            so->so_fport6 = 0;

            switch (so->so_type) {
            case IPPROTO_TCP:
                s = slirp_socket(PF_INET6, SOCK_STREAM, 0);
                break;
            case IPPROTO_UDP:
                s = slirp_socket(PF_INET6, SOCK_DGRAM, 0);
                break;
            default:
                g_assert_not_reached();
                break;
            }
            if (s < 0) {
                g_error("Ephemeral slirp_socket() allocation failed");
                goto unix2inet6_cont;
            }
            memset(&in6_addr, 0, sizeof(in6_addr));
            in6_addr.sin6_family = AF_INET6;
            in6_addr.sin6_addr = in6addr_loopback;
            in6_addr.sin6_port = htons(0);
            if (bind(s, (struct sockaddr *) &in6_addr, sizeof(in6_addr))) {
                g_error("Ephemeral bind() failed");
                closesocket(s);
                goto unix2inet6_cont;
            }
            in_addr_len = sizeof(in6_addr);
            if (getsockname(s, (struct sockaddr *) &in6_addr, &in_addr_len)) {
                g_error("Ephemeral getsockname() failed");
                closesocket(s);
                goto unix2inet6_cont;
            }
            so->s_aux = s;
            so->so_fport6 = in6_addr.sin6_port;

unix2inet6_cont:
            if (!so->so_fport6) {
                g_warning("Falling back to random port allocation");
                so->so_fport6 = htons(g_rand_int_range(slirp->grand, 49152, 65536));
            }
        } else {
            g_assert_not_reached();
        }
        break;
    } /* case AF_UNIX */

    default:
        break;
    }
}

void sodrop(struct socket *s, int num)
{
    if (sbdrop(&s->so_snd, num)) {
        s->slirp->cb->notify(s->slirp->opaque);
    }
}

/*
 * Translate "addr-any" in so->lhost to the guest's actual address.
 * Returns 0 for success, or -1 if the guest doesn't have an address yet
 * with errno set to EHOSTUNREACH.
 *
 * The guest address is taken from the first entry in the ARP table for IPv4
 * and the first entry in the NDP table for IPv6.
 * Note: The IPv4 path isn't exercised yet as all hostfwd "" guest translations
 * are handled immediately by using slirp->vdhcp_startaddr.
 */
int soassign_guest_addr_if_needed(struct socket *so)
{
    Slirp *slirp = so->slirp;
    /* AF_INET6 addresses are bigger than AF_INET, so this is big enough. */
    char addrstr[INET6_ADDRSTRLEN];
    char portstr[6];

    g_assert(so->so_state & SS_HOSTFWD);

    switch (so->so_ffamily) {
    case AF_INET:
        if (so->so_laddr.s_addr == INADDR_ANY) {
            g_assert_not_reached();
        }
        break;

    case AF_INET6:
        if (in6_zero(&so->so_laddr6)) {
            int ret;
            if (in6_zero(&slirp->ndp_table.guest_in6_addr)) {
                errno = EHOSTUNREACH;
                return -1;
            }
            so->so_laddr6 = slirp->ndp_table.guest_in6_addr;
            ret = getnameinfo((const struct sockaddr *) &so->lhost.ss,
                              sizeof(so->lhost.ss), addrstr, sizeof(addrstr),
                              portstr, sizeof(portstr),
                              NI_NUMERICHOST|NI_NUMERICSERV);
            g_assert(ret == 0);
            DEBUG_MISC("%s: new ip = [%s]:%s", __func__, addrstr, portstr);
        }
        break;

    default:
        break;
    }

    return 0;
}
