/* SPDX-License-Identifier: MIT */
/*
 * QEMU BOOTP/DHCP server
 *
 * Copyright (c) 2004 Fabrice Bellard
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
#include "slirp.h"

#if defined(_WIN32)
/* Windows ntohl() returns an u_long value.
 * Add a type cast to match the format strings. */
#define ntohl(n) ((uint32_t)ntohl(n))
#endif

/* XXX: only DHCP is supported */

#define LEASE_TIME (24 * 3600)

#define UEFI_HTTP_VENDOR_CLASS_ID "HTTPClient"

static const uint8_t rfc1533_cookie[] = { RFC1533_COOKIE };

#define DPRINTF(...) DEBUG_RAW_CALL(__VA_ARGS__)

static BOOTPClient *get_new_addr(Slirp *slirp, struct in_addr *paddr,
                                 const uint8_t *macaddr)
{
    BOOTPClient *bc;
    int i;

    for (i = 0; i < NB_BOOTP_CLIENTS; i++) {
        bc = &slirp->bootp_clients[i];
        if (!bc->allocated || !memcmp(macaddr, bc->macaddr, 6))
            goto found;
    }
    return NULL;
found:
    bc = &slirp->bootp_clients[i];
    bc->allocated = 1;
    paddr->s_addr = slirp->vdhcp_startaddr.s_addr + htonl(i);
    return bc;
}

static BOOTPClient *request_addr(Slirp *slirp, const struct in_addr *paddr,
                                 const uint8_t *macaddr)
{
    uint32_t req_addr = ntohl(paddr->s_addr);
    uint32_t dhcp_addr = ntohl(slirp->vdhcp_startaddr.s_addr);
    BOOTPClient *bc;

    if (req_addr >= dhcp_addr && req_addr < (dhcp_addr + NB_BOOTP_CLIENTS)) {
        bc = &slirp->bootp_clients[req_addr - dhcp_addr];
        if (!bc->allocated || !memcmp(macaddr, bc->macaddr, 6)) {
            bc->allocated = 1;
            return bc;
        }
    }
    return NULL;
}

static BOOTPClient *find_addr(Slirp *slirp, struct in_addr *paddr,
                              const uint8_t *macaddr)
{
    BOOTPClient *bc;
    int i;

    for (i = 0; i < NB_BOOTP_CLIENTS; i++) {
        if (!memcmp(macaddr, slirp->bootp_clients[i].macaddr, 6))
            goto found;
    }
    return NULL;
found:
    bc = &slirp->bootp_clients[i];
    bc->allocated = 1;
    paddr->s_addr = slirp->vdhcp_startaddr.s_addr + htonl(i);
    return bc;
}

static void dhcp_decode(const struct bootp_t *bp,
                        const uint8_t *bp_end,
                        int *pmsg_type,
                        struct in_addr *preq_addr)
{
    const uint8_t *p;
    int len, tag;

    *pmsg_type = 0;
    preq_addr->s_addr = htonl(0L);

    p = bp->bp_vend;
    if (memcmp(p, rfc1533_cookie, 4) != 0)
        return;
    p += 4;
    while (p < bp_end) {
        tag = p[0];
        if (tag == RFC1533_PAD) {
            p++;
        } else if (tag == RFC1533_END) {
            break;
        } else {
            p++;
            if (p >= bp_end)
                break;
            len = *p++;
            if (p + len > bp_end) {
                break;
            }
            DPRINTF("dhcp: tag=%d len=%d\n", tag, len);

            switch (tag) {
            case RFC2132_MSG_TYPE:
                if (len >= 1)
                    *pmsg_type = p[0];
                break;
            case RFC2132_REQ_ADDR:
                if (len >= 4) {
                    memcpy(&(preq_addr->s_addr), p, 4);
                }
                break;
            default:
                break;
            }
            p += len;
        }
    }
    if (*pmsg_type == DHCPREQUEST && preq_addr->s_addr == htonl(0L) &&
        bp->bp_ciaddr.s_addr) {
        memcpy(&(preq_addr->s_addr), &bp->bp_ciaddr, 4);
    }
}

static void bootp_reply(Slirp *slirp,
                        const struct bootp_t *bp,
                        const uint8_t *bp_end)
{
    BOOTPClient *bc = NULL;
    struct mbuf *m;
    struct bootp_t *rbp;
    struct sockaddr_in saddr, daddr;
    struct in_addr preq_addr;
    int dhcp_msg_type, val;
    uint8_t *q;
    uint8_t *end;
    uint8_t client_ethaddr[ETH_ALEN];

    /* extract exact DHCP msg type */
    dhcp_decode(bp, bp_end, &dhcp_msg_type, &preq_addr);
    DPRINTF("bootp packet op=%d msgtype=%d", bp->bp_op, dhcp_msg_type);
    if (preq_addr.s_addr != htonl(0L))
        DPRINTF(" req_addr=%08" PRIx32 "\n", ntohl(preq_addr.s_addr));
    else {
        DPRINTF("\n");
    }

    if (dhcp_msg_type == 0)
        dhcp_msg_type = DHCPREQUEST; /* Force reply for old BOOTP clients */

    if (dhcp_msg_type != DHCPDISCOVER && dhcp_msg_type != DHCPREQUEST)
        return;

    /* Get client's hardware address from bootp request */
    memcpy(client_ethaddr, bp->bp_hwaddr, ETH_ALEN);

    m = m_get(slirp);
    if (!m) {
        return;
    }
    m->m_data += IF_MAXLINKHDR;
    m_inc(m, sizeof(struct bootp_t) + DHCP_OPT_LEN);
    rbp = (struct bootp_t *)m->m_data;
    m->m_data += sizeof(struct udpiphdr);
    memset(rbp, 0, sizeof(struct bootp_t) + DHCP_OPT_LEN);

    if (dhcp_msg_type == DHCPDISCOVER) {
        if (preq_addr.s_addr != htonl(0L)) {
            bc = request_addr(slirp, &preq_addr, client_ethaddr);
            if (bc) {
                daddr.sin_addr = preq_addr;
            }
        }
        if (!bc) {
        new_addr:
            bc = get_new_addr(slirp, &daddr.sin_addr, client_ethaddr);
            if (!bc) {
                DPRINTF("no address left\n");
                return;
            }
        }
        memcpy(bc->macaddr, client_ethaddr, ETH_ALEN);
    } else if (preq_addr.s_addr != htonl(0L)) {
        bc = request_addr(slirp, &preq_addr, client_ethaddr);
        if (bc) {
            daddr.sin_addr = preq_addr;
            memcpy(bc->macaddr, client_ethaddr, ETH_ALEN);
        } else {
            /* DHCPNAKs should be sent to broadcast */
            daddr.sin_addr.s_addr = 0xffffffff;
        }
    } else {
        bc = find_addr(slirp, &daddr.sin_addr, bp->bp_hwaddr);
        if (!bc) {
            /* if never assigned, behaves as if it was already
               assigned (windows fix because it remembers its address) */
            goto new_addr;
        }
    }

    /* Update ARP table for this IP address */
    arp_table_add(slirp, daddr.sin_addr.s_addr, client_ethaddr);

    saddr.sin_addr = slirp->vhost_addr;
    saddr.sin_port = htons(BOOTP_SERVER);

    daddr.sin_port = htons(BOOTP_CLIENT);

    rbp->bp_op = BOOTP_REPLY;
    rbp->bp_xid = bp->bp_xid;
    rbp->bp_htype = 1;
    rbp->bp_hlen = 6;
    memcpy(rbp->bp_hwaddr, bp->bp_hwaddr, ETH_ALEN);

    rbp->bp_yiaddr = daddr.sin_addr; /* Client IP address */
    rbp->bp_siaddr = saddr.sin_addr; /* Server IP address */

    q = rbp->bp_vend;
    end = rbp->bp_vend + DHCP_OPT_LEN;
    memcpy(q, rfc1533_cookie, 4);
    q += 4;

    if (bc) {
        DPRINTF("%s addr=%08" PRIx32 "\n",
                (dhcp_msg_type == DHCPDISCOVER) ? "offered" : "ack'ed",
                ntohl(daddr.sin_addr.s_addr));

        if (dhcp_msg_type == DHCPDISCOVER) {
            *q++ = RFC2132_MSG_TYPE;
            *q++ = 1;
            *q++ = DHCPOFFER;
        } else /* DHCPREQUEST */ {
            *q++ = RFC2132_MSG_TYPE;
            *q++ = 1;
            *q++ = DHCPACK;
        }

        if (slirp->bootp_filename) {
            g_assert(strlen(slirp->bootp_filename) < sizeof(rbp->bp_file));
            strcpy(rbp->bp_file, slirp->bootp_filename);
        }

        *q++ = RFC2132_SRV_ID;
        *q++ = 4;
        memcpy(q, &saddr.sin_addr, 4);
        q += 4;

        *q++ = RFC1533_NETMASK;
        *q++ = 4;
        memcpy(q, &slirp->vnetwork_mask, 4);
        q += 4;

        if (!slirp->restricted) {
            *q++ = RFC1533_GATEWAY;
            *q++ = 4;
            memcpy(q, &saddr.sin_addr, 4);
            q += 4;

            *q++ = RFC1533_DNS;
            *q++ = 4;
            memcpy(q, &slirp->vnameserver_addr, 4);
            q += 4;
        }

        *q++ = RFC2132_LEASE_TIME;
        *q++ = 4;
        val = htonl(LEASE_TIME);
        memcpy(q, &val, 4);
        q += 4;

        if (*slirp->client_hostname) {
            val = strlen(slirp->client_hostname);
            if (q + val + 2 >= end) {
                g_warning("DHCP packet size exceeded, "
                          "omitting host name option.");
            } else {
                *q++ = RFC1533_HOSTNAME;
                *q++ = val;
                memcpy(q, slirp->client_hostname, val);
                q += val;
            }
        }

        if (slirp->vdomainname) {
            val = strlen(slirp->vdomainname);
            if (q + val + 2 >= end) {
                g_warning("DHCP packet size exceeded, "
                          "omitting domain name option.");
            } else {
                *q++ = RFC1533_DOMAINNAME;
                *q++ = val;
                memcpy(q, slirp->vdomainname, val);
                q += val;
            }
        }

        if (slirp->tftp_server_name) {
            val = strlen(slirp->tftp_server_name);
            if (q + val + 2 >= end) {
                g_warning("DHCP packet size exceeded, "
                          "omitting tftp-server-name option.");
            } else {
                *q++ = RFC2132_TFTP_SERVER_NAME;
                *q++ = val;
                memcpy(q, slirp->tftp_server_name, val);
                q += val;
            }
        }

        if (slirp->vdnssearch) {
            val = slirp->vdnssearch_len;
            if (q + val >= end) {
                g_warning("DHCP packet size exceeded, "
                          "omitting domain-search option.");
            } else {
                memcpy(q, slirp->vdnssearch, val);
                q += val;
            }
        }

        /* this allows to support UEFI HTTP boot: according to the UEFI
           specification, DHCP server must send vendor class identifier option
           set to "HTTPClient" string, when responding to DHCP requests as part
           of the UEFI HTTP boot

           we assume that, if the bootfile parameter was configured as an http
           URL, the user intends to perform UEFI HTTP boot, so send this option
           automatically */
        if (slirp->bootp_filename && g_str_has_prefix(slirp->bootp_filename, "http://")) {
            val = strlen(UEFI_HTTP_VENDOR_CLASS_ID);
            if (q + val + 2 >= end) {
                g_warning("DHCP packet size exceeded, "
                          "omitting vendor class id option.");
            } else {
                *q++ = RFC2132_VENDOR_CLASS_ID;
                *q++ = val;
                memcpy(q, UEFI_HTTP_VENDOR_CLASS_ID, val);
                q += val;
            }
        }
    } else {
        static const char nak_msg[] = "requested address not available";

        DPRINTF("nak'ed addr=%08" PRIx32 "\n", ntohl(preq_addr.s_addr));

        *q++ = RFC2132_MSG_TYPE;
        *q++ = 1;
        *q++ = DHCPNAK;

        *q++ = RFC2132_MESSAGE;
        *q++ = sizeof(nak_msg) - 1;
        memcpy(q, nak_msg, sizeof(nak_msg) - 1);
        q += sizeof(nak_msg) - 1;
    }
    assert(q < end);
    *q++ = RFC1533_END;

    daddr.sin_addr.s_addr = 0xffffffffu;

    assert(q <= end);

    m->m_len = sizeof(struct bootp_t) + (end - rbp->bp_vend) - sizeof(struct ip) - sizeof(struct udphdr);
    udp_output(NULL, m, &saddr, &daddr, IPTOS_LOWDELAY);
}

void bootp_input(struct mbuf *m)
{
    struct bootp_t *bp = mtod_check(m, sizeof(struct bootp_t));

    if (!m->slirp->disable_dhcp && bp && bp->bp_op == BOOTP_REQUEST) {
        bootp_reply(m->slirp, bp, m_end(m));
    }
}
