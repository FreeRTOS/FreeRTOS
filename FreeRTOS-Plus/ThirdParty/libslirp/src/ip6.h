/* SPDX-License-Identifier: BSD-3-Clause */
/*
 * Copyright (c) 2013
 * Guillaume Subiron, Yann Bordenave, Serigne Modou Wagne.
 */

#ifndef SLIRP_IP6_H
#define SLIRP_IP6_H

#include <glib.h>
#include <string.h>

#define ALLNODES_MULTICAST \
    {                      \
        .s6_addr = {       \
            0xff,          \
            0x02,          \
            0x00,          \
            0x00,          \
            0x00,          \
            0x00,          \
            0x00,          \
            0x00,          \
            0x00,          \
            0x00,          \
            0x00,          \
            0x00,          \
            0x00,          \
            0x00,          \
            0x00,          \
            0x01           \
        }                  \
    }

#define SOLICITED_NODE_PREFIX \
    {                         \
        .s6_addr = {          \
            0xff,             \
            0x02,             \
            0x00,             \
            0x00,             \
            0x00,             \
            0x00,             \
            0x00,             \
            0x00,             \
            0x00,             \
            0x00,             \
            0x00,             \
            0x01,             \
            0xff,             \
            0x00,             \
            0x00,             \
            0x00              \
        }                     \
    }

#define LINKLOCAL_ADDR \
    {                  \
        .s6_addr = {   \
            0xfe,      \
            0x80,      \
            0x00,      \
            0x00,      \
            0x00,      \
            0x00,      \
            0x00,      \
            0x00,      \
            0x00,      \
            0x00,      \
            0x00,      \
            0x00,      \
            0x00,      \
            0x00,      \
            0x00,      \
            0x02       \
        }              \
    }

#define ZERO_ADDR    \
    {                \
        .s6_addr = { \
            0x00,    \
            0x00,    \
            0x00,    \
            0x00,    \
            0x00,    \
            0x00,    \
            0x00,    \
            0x00,    \
            0x00,    \
            0x00,    \
            0x00,    \
            0x00,    \
            0x00,    \
            0x00,    \
            0x00,    \
            0x00     \
        }            \
    }

static inline bool in6_equal(const struct in6_addr *a, const struct in6_addr *b)
{
    return memcmp(a, b, sizeof(*a)) == 0;
}

static inline bool in6_equal_net(const struct in6_addr *a,
                                 const struct in6_addr *b, int prefix_len)
{
    if (memcmp(a, b, prefix_len / 8) != 0) {
        return 0;
    }

    if (prefix_len % 8 == 0) {
        return 1;
    }

    return a->s6_addr[prefix_len / 8] >> (8 - (prefix_len % 8)) ==
           b->s6_addr[prefix_len / 8] >> (8 - (prefix_len % 8));
}

static inline bool in6_equal_mach(const struct in6_addr *a,
                                  const struct in6_addr *b, int prefix_len)
{
    if (memcmp(&(a->s6_addr[DIV_ROUND_UP(prefix_len, 8)]),
               &(b->s6_addr[DIV_ROUND_UP(prefix_len, 8)]),
               16 - DIV_ROUND_UP(prefix_len, 8)) != 0) {
        return 0;
    }

    if (prefix_len % 8 == 0) {
        return 1;
    }

    return (a->s6_addr[prefix_len / 8] &
            ((1U << (8 - (prefix_len % 8))) - 1)) ==
           (b->s6_addr[prefix_len / 8] & ((1U << (8 - (prefix_len % 8))) - 1));
}


#define in6_equal_router(a)                                          \
    ((in6_equal_net(a, &slirp->vprefix_addr6, slirp->vprefix_len) && \
      in6_equal_mach(a, &slirp->vhost_addr6, slirp->vprefix_len)) || \
     (in6_equal_net(a, &(struct in6_addr)LINKLOCAL_ADDR, 64) &&      \
      in6_equal_mach(a, &slirp->vhost_addr6, 64)))

#define in6_equal_dns(a)                                                   \
    ((in6_equal_net(a, &slirp->vprefix_addr6, slirp->vprefix_len) &&       \
      in6_equal_mach(a, &slirp->vnameserver_addr6, slirp->vprefix_len)) || \
     (in6_equal_net(a, &(struct in6_addr)LINKLOCAL_ADDR, 64) &&            \
      in6_equal_mach(a, &slirp->vnameserver_addr6, 64)))

#define in6_equal_host(a) (in6_equal_router(a) || in6_equal_dns(a))

#define in6_solicitednode_multicast(a) \
    (in6_equal_net(a, &(struct in6_addr)SOLICITED_NODE_PREFIX, 104))

#define in6_zero(a) (in6_equal(a, &(struct in6_addr)ZERO_ADDR))

/* Compute emulated host MAC address from its ipv6 address */
static inline void in6_compute_ethaddr(struct in6_addr ip,
                                       uint8_t eth[ETH_ALEN])
{
    eth[0] = 0x52;
    eth[1] = 0x56;
    memcpy(&eth[2], &ip.s6_addr[16 - (ETH_ALEN - 2)], ETH_ALEN - 2);
}

/*
 * Definitions for internet protocol version 6.
 * Per RFC 2460, December 1998.
 */
#define IP6VERSION 6
#define IP6_HOP_LIMIT 255

/*
 * Structure of an internet header, naked of options.
 */
struct ip6 {
#if (G_BYTE_ORDER == G_BIG_ENDIAN) && !defined(_MSC_VER)
    uint8_t ip_v : 4, /* version */
         ip_tc_hi : 4; /* traffic class */
    uint8_t ip_tc_lo : 4, ip_fl_hi : 4; /* flow label */
#else
    uint8_t ip_tc_hi : 4, ip_v : 4;
    uint8_t ip_fl_hi : 4, ip_tc_lo : 4;
#endif
    uint16_t ip_fl_lo;
    uint16_t ip_pl; /* payload length */
    uint8_t ip_nh; /* next header */
    uint8_t ip_hl; /* hop limit */
    struct in6_addr ip_src, ip_dst; /* source and dest address */
};

/*
 * IPv6 pseudo-header used by upper-layer protocols
 */
struct ip6_pseudohdr {
    struct in6_addr ih_src; /* source internet address */
    struct in6_addr ih_dst; /* destination internet address */
    uint32_t ih_pl; /* upper-layer packet length */
    uint16_t ih_zero_hi; /* zero */
    uint8_t ih_zero_lo; /* zero */
    uint8_t ih_nh; /* next header */
};

/*
 * We don't want to mark these ip6 structs as packed as they are naturally
 * correctly aligned; instead assert that there is no stray padding.
 * If we marked the struct as packed then we would be unable to take
 * the address of any of the fields in it.
 */
G_STATIC_ASSERT(sizeof(struct ip6) == 40);
G_STATIC_ASSERT(sizeof(struct ip6_pseudohdr) == 40);

#endif
