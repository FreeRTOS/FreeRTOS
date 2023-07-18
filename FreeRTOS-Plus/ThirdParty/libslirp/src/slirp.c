/* SPDX-License-Identifier: MIT */
/*
 * libslirp glue
 *
 * Copyright (c) 2004-2008 Fabrice Bellard
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


#ifndef _WIN32
#include <net/if.h>
#endif

/* https://gitlab.freedesktop.org/slirp/libslirp/issues/18 */
#if defined(__NetBSD__) && defined(if_mtu)
#undef if_mtu
#endif

#if defined(_WIN32)

#define INITIAL_DNS_ADDR_BUF_SIZE 32 * 1024
#define REALLOC_RETRIES 5

// Broadcast site local DNS resolvers. We do not use these because they are
// highly unlikely to be valid.
// https://www.ietf.org/proceedings/52/I-D/draft-ietf-ipngwg-dns-discovery-03.txt
static const struct in6_addr SITE_LOCAL_DNS_BROADCAST_ADDRS[] = {
    {
        {{
            0xfe, 0xc0, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01
        }}
    },
    {
        {{
            0xfe, 0xc0, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02
        }}
    },
    {
        {{
            0xfe, 0xc0, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03,
        }}
    },
};

#endif

int slirp_debug;

/* Define to 1 if you want KEEPALIVE timers */
bool slirp_do_keepalive;

/* host loopback address */
struct in_addr loopback_addr;
/* host loopback network mask */
unsigned long loopback_mask;

/* emulated hosts use the MAC addr 52:55:IP:IP:IP:IP */
static const uint8_t special_ethaddr[ETH_ALEN] = { 0x52, 0x55, 0x00,
                                                   0x00, 0x00, 0x00 };

unsigned curtime;

static struct in_addr dns_addr;
static struct in6_addr dns6_addr;
static uint32_t dns6_scope_id;
static unsigned dns_addr_time;
static unsigned dns6_addr_time;

#define TIMEOUT_FAST 2 /* milliseconds */
#define TIMEOUT_SLOW 499 /* milliseconds */
/* for the aging of certain requests like DNS */
#define TIMEOUT_DEFAULT 1000 /* milliseconds */

#if defined(_WIN32)

int get_dns_addr(struct in_addr *pdns_addr)
{
    FIXED_INFO *FixedInfo = NULL;
    ULONG BufLen;
    DWORD ret;
    IP_ADDR_STRING *pIPAddr;
    struct in_addr tmp_addr;

    if (dns_addr.s_addr != 0 && (curtime - dns_addr_time) < TIMEOUT_DEFAULT) {
        *pdns_addr = dns_addr;
        return 0;
    }

    FixedInfo = (FIXED_INFO *)GlobalAlloc(GPTR, sizeof(FIXED_INFO));
    BufLen = sizeof(FIXED_INFO);

    if (ERROR_BUFFER_OVERFLOW == GetNetworkParams(FixedInfo, &BufLen)) {
        if (FixedInfo) {
            GlobalFree(FixedInfo);
            FixedInfo = NULL;
        }
        FixedInfo = GlobalAlloc(GPTR, BufLen);
    }

    if ((ret = GetNetworkParams(FixedInfo, &BufLen)) != ERROR_SUCCESS) {
        printf("GetNetworkParams failed. ret = %08x\n", (unsigned)ret);
        if (FixedInfo) {
            GlobalFree(FixedInfo);
            FixedInfo = NULL;
        }
        return -1;
    }

    pIPAddr = &(FixedInfo->DnsServerList);
    inet_aton(pIPAddr->IpAddress.String, &tmp_addr);
    *pdns_addr = tmp_addr;
    dns_addr = tmp_addr;
    dns_addr_time = curtime;
    if (FixedInfo) {
        GlobalFree(FixedInfo);
        FixedInfo = NULL;
    }
    return 0;
}

static int is_site_local_dns_broadcast(struct in6_addr *address)
{
    int i;
    for (i = 0; i < G_N_ELEMENTS(SITE_LOCAL_DNS_BROADCAST_ADDRS); i++) {
        if (in6_equal(address, &SITE_LOCAL_DNS_BROADCAST_ADDRS[i])) {
            return 1;
        }
    }
    return 0;
}

static void print_dns_v6_address(struct in6_addr address)
{
    char address_str[INET6_ADDRSTRLEN] = "";
    if (inet_ntop(AF_INET6, &address, address_str, INET6_ADDRSTRLEN)
        == NULL) {
        DEBUG_ERROR("Failed to stringify IPv6 address for logging.");
        return;
    }
    DEBUG_RAW_CALL("IPv6 DNS server found: %s", address_str);
}

// Gets the first valid DNS resolver with an IPv6 address.
// Ignores any site local broadcast DNS servers, as these
// are on deprecated addresses and not generally expected
// to work. Further details at:
// https://www.ietf.org/proceedings/52/I-D/draft-ietf-ipngwg-dns-discovery-03.txt
static int get_ipv6_dns_server(struct in6_addr *dns_server_address, uint32_t *scope_id)
{
    PIP_ADAPTER_ADDRESSES addresses = NULL;
    PIP_ADAPTER_ADDRESSES address = NULL;
    IP_ADAPTER_DNS_SERVER_ADDRESS *dns_server = NULL;
    struct sockaddr_in6 *dns_v6_addr = NULL;

    ULONG buf_size = INITIAL_DNS_ADDR_BUF_SIZE;
    DWORD res = ERROR_BUFFER_OVERFLOW;
    int i;

    for (i = 0; i < REALLOC_RETRIES; i++) {
        // If non null, we hit buffer overflow, free it so we can try again.
        if (addresses != NULL) {
            g_free(addresses);
        }

        addresses = g_malloc(buf_size);
        res = GetAdaptersAddresses(AF_UNSPEC, GAA_FLAG_INCLUDE_PREFIX, NULL,
                                   addresses, &buf_size);

        if (res != ERROR_BUFFER_OVERFLOW) {
            break;
        }
    }

    if (res != NO_ERROR) {
        DEBUG_ERROR("Failed to get IPv6 DNS addresses due to error %lX", res);
        goto failure;
    }

    address = addresses;
    for (address = addresses; address != NULL; address = address->Next) {
        for (dns_server = address->FirstDnsServerAddress;
             dns_server != NULL;
             dns_server = dns_server->Next) {

            if (dns_server->Address.lpSockaddr->sa_family != AF_INET6) {
                continue;
            }

            dns_v6_addr = (struct sockaddr_in6 *)dns_server->Address.lpSockaddr;
            if (is_site_local_dns_broadcast(&dns_v6_addr->sin6_addr) == 0) {
                print_dns_v6_address(dns_v6_addr->sin6_addr);
                *dns_server_address = dns_v6_addr->sin6_addr;
                *scope_id = dns_v6_addr->sin6_scope_id;

                g_free(addresses);
                return 0;
            }
        }
    }

    DEBUG_ERROR("No IPv6 DNS servers found.\n");

failure:
    g_free(addresses);
    return -1;
}

int get_dns6_addr(struct in6_addr *pdns6_addr, uint32_t *scope_id)
{
    if (!in6_zero(&dns6_addr) && (curtime - dns6_addr_time) < TIMEOUT_DEFAULT) {
        *pdns6_addr = dns6_addr;
        *scope_id = dns6_scope_id;
        return 0;
    }

    if (get_ipv6_dns_server(pdns6_addr, scope_id) == 0) {
        dns6_addr = *pdns6_addr;
        dns6_addr_time = curtime;
        dns6_scope_id = *scope_id;
        return 0;
    }

    return -1;
}

static void winsock_cleanup(void)
{
    WSACleanup();
}

#elif defined(__APPLE__)

#include <resolv.h>

static int get_dns_addr_cached(void *pdns_addr, void *cached_addr,
                               socklen_t addrlen, unsigned *cached_time)
{
    if (curtime - *cached_time < TIMEOUT_DEFAULT) {
        memcpy(pdns_addr, cached_addr, addrlen);
        return 0;
    }
    return 1;
}

static int get_dns_addr_libresolv(int af, void *pdns_addr, void *cached_addr,
                                  socklen_t addrlen,
                                  uint32_t *scope_id, uint32_t *cached_scope_id,
                                  unsigned *cached_time)
{
    struct __res_state state;
    union res_sockaddr_union servers[NI_MAXSERV];
    int count;
    int found;
    void *addr;

    // we only support IPv4 and IPv4, we assume it's one or the other
    assert(af == AF_INET || af == AF_INET6);

    if (res_ninit(&state) != 0) {
        return -1;
    }

    count = res_getservers(&state, servers, NI_MAXSERV);
    found = 0;
    DEBUG_MISC("IP address of your DNS(s):");
    for (int i = 0; i < count; i++) {
        if (af == servers[i].sin.sin_family) {
            found++;
        }
        if (af == AF_INET) {
            addr = &servers[i].sin.sin_addr;
        } else { // af == AF_INET6
            addr = &servers[i].sin6.sin6_addr;
        }

        // we use the first found entry
        if (found == 1) {
            memcpy(pdns_addr, addr, addrlen);
            memcpy(cached_addr, addr, addrlen);
            if (scope_id) {
                *scope_id = 0;
            }
            if (cached_scope_id) {
                *cached_scope_id = 0;
            }
            *cached_time = curtime;
        }

        if (found > 3) {
            DEBUG_MISC("  (more)");
            break;
        } else if (slirp_debug & DBG_MISC) {
            char s[INET6_ADDRSTRLEN];
            const char *res = inet_ntop(af, addr, s, sizeof(s));
            if (!res) {
                res = "  (string conversion error)";
            }
            DEBUG_MISC("  %s", res);
        }
    }

    res_ndestroy(&state);
    if (!found)
        return -1;
    return 0;
}

int get_dns_addr(struct in_addr *pdns_addr)
{
    if (dns_addr.s_addr != 0) {
        int ret;
        ret = get_dns_addr_cached(pdns_addr, &dns_addr, sizeof(dns_addr),
                                  &dns_addr_time);
        if (ret <= 0) {
            return ret;
        }
    }
    return get_dns_addr_libresolv(AF_INET, pdns_addr, &dns_addr,
                                  sizeof(dns_addr), NULL, NULL, &dns_addr_time);
}

int get_dns6_addr(struct in6_addr *pdns6_addr, uint32_t *scope_id)
{
    if (!in6_zero(&dns6_addr)) {
        int ret;
        ret = get_dns_addr_cached(pdns6_addr, &dns6_addr, sizeof(dns6_addr),
                                  &dns6_addr_time);
        if (ret == 0) {
            *scope_id = dns6_scope_id;
        }
        if (ret <= 0) {
            return ret;
        }
    }
    return get_dns_addr_libresolv(AF_INET6, pdns6_addr, &dns6_addr,
                                  sizeof(dns6_addr),
                                  scope_id, &dns6_scope_id, &dns6_addr_time);
}

#else // !defined(_WIN32) && !defined(__APPLE__)

#if defined(__HAIKU__)
#define RESOLV_CONF_PATH "/boot/system/settings/network/resolv.conf"
#else
#define RESOLV_CONF_PATH "/etc/resolv.conf"
#endif

static int get_dns_addr_cached(void *pdns_addr, void *cached_addr,
                               socklen_t addrlen, struct stat *cached_stat,
                               unsigned *cached_time)
{
    struct stat old_stat;
    if (curtime - *cached_time < TIMEOUT_DEFAULT) {
        memcpy(pdns_addr, cached_addr, addrlen);
        return 0;
    }
    old_stat = *cached_stat;
    if (stat(RESOLV_CONF_PATH, cached_stat) != 0) {
        return -1;
    }
    if (cached_stat->st_dev == old_stat.st_dev &&
        cached_stat->st_ino == old_stat.st_ino &&
        cached_stat->st_size == old_stat.st_size &&
        cached_stat->st_mtime == old_stat.st_mtime) {
        memcpy(pdns_addr, cached_addr, addrlen);
        return 0;
    }
    return 1;
}

static bool try_and_setdns_server(int af, unsigned found, unsigned if_index,
	const char *buff2, void *pdns_addr, void *cached_addr,
	socklen_t addrlen, uint32_t *scope_id, uint32_t *cached_scope_id,
	unsigned *cached_time)
{
    union {
        struct in_addr dns_addr;
        struct in6_addr dns6_addr;
    } tmp_addr;

    assert(sizeof(tmp_addr) >= addrlen);

    if (!inet_pton(af, buff2, &tmp_addr))
	return false;

    /* If it's the first one, set it to dns_addr */
    if (!found) {
	memcpy(pdns_addr, &tmp_addr, addrlen);
	memcpy(cached_addr, &tmp_addr, addrlen);
	if (scope_id) {
	    *scope_id = if_index;
	}
	if (cached_scope_id) {
	    *cached_scope_id = if_index;
	}
	*cached_time = curtime;
    }

    if (found > 2) {
	DEBUG_MISC("  (more)");
    } else if (slirp_debug & DBG_MISC) {
	char s[INET6_ADDRSTRLEN];
	const char *res = inet_ntop(af, &tmp_addr, s, sizeof(s));
	if (!res) {
	    res = "  (string conversion error)";
	}
	DEBUG_MISC("  %s", res);
    }

    return true;
}

static int get_dns_addr_resolv_conf(int af, void *pdns_addr, void *cached_addr,
                                    socklen_t addrlen,
                                    uint32_t *scope_id, uint32_t *cached_scope_id,
                                    unsigned *cached_time)
{
    char buff[512];
    char buff2[257];
    FILE *f;
    int found = 0;
    unsigned if_index;
    unsigned nameservers = 0;

    f = fopen(RESOLV_CONF_PATH, "r");
    if (!f)
        return -1;

    DEBUG_MISC("IP address of your DNS(s):");
    while (fgets(buff, 512, f) != NULL) {
        if (sscanf(buff, "nameserver%*[ \t]%256s", buff2) == 1) {
            char *c = strchr(buff2, '%');
            if (c) {
                if_index = if_nametoindex(c + 1);
                *c = '\0';
            } else {
                if_index = 0;
            }

	    nameservers++;

	    if (!try_and_setdns_server(af, found, if_index, buff2, pdns_addr,
				    cached_addr, addrlen, scope_id,
				    cached_scope_id, cached_time))
		    continue;

	    if (++found > 3)
		break;
        }
    }
    fclose(f);
    if (nameservers && !found)
        return -1;
    if (!nameservers) {
	found += try_and_setdns_server(af, found, 0, "127.0.0.1",
			pdns_addr, cached_addr, addrlen, scope_id,
			cached_scope_id, cached_time);
	found += try_and_setdns_server(af, found, 0, "::1",
			pdns_addr, cached_addr, addrlen, scope_id,
			cached_scope_id, cached_time);
    }

    return found ? 0 : -1;
}

int get_dns_addr(struct in_addr *pdns_addr)
{
    static struct stat dns_addr_stat;

    if (dns_addr.s_addr != 0) {
        int ret;
        ret = get_dns_addr_cached(pdns_addr, &dns_addr, sizeof(dns_addr),
                                  &dns_addr_stat, &dns_addr_time);
        if (ret <= 0) {
            return ret;
        }
    }
    return get_dns_addr_resolv_conf(AF_INET, pdns_addr, &dns_addr,
                                    sizeof(dns_addr),
                                    NULL, NULL, &dns_addr_time);
}

int get_dns6_addr(struct in6_addr *pdns6_addr, uint32_t *scope_id)
{
    static struct stat dns6_addr_stat;

    if (!in6_zero(&dns6_addr)) {
        int ret;
        ret = get_dns_addr_cached(pdns6_addr, &dns6_addr, sizeof(dns6_addr),
                                  &dns6_addr_stat, &dns6_addr_time);
        if (ret == 0) {
            *scope_id = dns6_scope_id;
        }
        if (ret <= 0) {
            return ret;
        }
    }
    return get_dns_addr_resolv_conf(AF_INET6, pdns6_addr, &dns6_addr,
                                    sizeof(dns6_addr),
                                    scope_id, &dns6_scope_id, &dns6_addr_time);
}

#endif

static void slirp_init_once(void)
{
    static int initialized;
    const char *debug;
#ifdef _WIN32
    WSADATA Data;
#endif

    if (initialized) {
        return;
    }
    initialized = 1;

#ifdef _WIN32
    WSAStartup(MAKEWORD(2, 0), &Data);
    atexit(winsock_cleanup);
#endif

    loopback_addr.s_addr = htonl(INADDR_LOOPBACK);
    loopback_mask = htonl(IN_CLASSA_NET);

    debug = g_getenv("SLIRP_DEBUG");
    if (debug) {
        const GDebugKey keys[] = {
            { "call", DBG_CALL },
            { "misc", DBG_MISC },
            { "error", DBG_ERROR },
            { "tftp", DBG_TFTP },
            { "verbose_call", DBG_VERBOSE_CALL },
        };
        slirp_debug = g_parse_debug_string(debug, keys, G_N_ELEMENTS(keys));
    }
}

static void ra_timer_handler_cb(void *opaque)
{
    Slirp *slirp = opaque;

    ra_timer_handler(slirp, NULL);
}

void slirp_handle_timer(Slirp *slirp, SlirpTimerId id, void *cb_opaque)
{
    g_return_if_fail(id >= 0 && id < SLIRP_TIMER_NUM);

    switch (id) {
    case SLIRP_TIMER_RA:
        ra_timer_handler(slirp, cb_opaque);
        return;
    default:
        abort();
    }
}

void *slirp_timer_new(Slirp *slirp, SlirpTimerId id, void *cb_opaque)
{
    g_return_val_if_fail(id >= 0 && id < SLIRP_TIMER_NUM, NULL);

    if (slirp->cfg_version >= 4 && slirp->cb->timer_new_opaque) {
        return slirp->cb->timer_new_opaque(id, cb_opaque, slirp->opaque);
    }

    switch (id) {
    case SLIRP_TIMER_RA:
        g_return_val_if_fail(cb_opaque == NULL, NULL);
        return slirp->cb->timer_new(ra_timer_handler_cb, slirp, slirp->opaque);

    default:
	abort();
    }
}

Slirp *slirp_new(const SlirpConfig *cfg, const SlirpCb *callbacks, void *opaque)
{
    Slirp *slirp;

    g_return_val_if_fail(cfg != NULL, NULL);
    g_return_val_if_fail(cfg->version >= SLIRP_CONFIG_VERSION_MIN, NULL);
    g_return_val_if_fail(cfg->version <= SLIRP_CONFIG_VERSION_MAX, NULL);
    g_return_val_if_fail(cfg->if_mtu >= IF_MTU_MIN || cfg->if_mtu == 0, NULL);
    g_return_val_if_fail(cfg->if_mtu <= IF_MTU_MAX, NULL);
    g_return_val_if_fail(cfg->if_mru >= IF_MRU_MIN || cfg->if_mru == 0, NULL);
    g_return_val_if_fail(cfg->if_mru <= IF_MRU_MAX, NULL);
    g_return_val_if_fail(!cfg->bootfile ||
                         (strlen(cfg->bootfile) <
                          G_SIZEOF_MEMBER(struct bootp_t, bp_file)), NULL);

    slirp = g_malloc0(sizeof(Slirp));

    slirp_init_once();

    slirp->cfg_version = cfg->version;
    slirp->opaque = opaque;
    slirp->cb = callbacks;
    slirp->grand = g_rand_new();
    slirp->restricted = cfg->restricted;

    slirp->in_enabled = cfg->in_enabled;
    slirp->in6_enabled = cfg->in6_enabled;

    if_init(slirp);
    ip_init(slirp);

    m_init(slirp);

    slirp->vnetwork_addr = cfg->vnetwork;
    slirp->vnetwork_mask = cfg->vnetmask;
    slirp->vhost_addr = cfg->vhost;
    slirp->vprefix_addr6 = cfg->vprefix_addr6;
    slirp->vprefix_len = cfg->vprefix_len;
    slirp->vhost_addr6 = cfg->vhost6;
    if (cfg->vhostname) {
        slirp_pstrcpy(slirp->client_hostname, sizeof(slirp->client_hostname),
                      cfg->vhostname);
    }
    slirp->tftp_prefix = g_strdup(cfg->tftp_path);
    slirp->bootp_filename = g_strdup(cfg->bootfile);
    slirp->vdomainname = g_strdup(cfg->vdomainname);
    slirp->vdhcp_startaddr = cfg->vdhcp_start;
    slirp->vnameserver_addr = cfg->vnameserver;
    slirp->vnameserver_addr6 = cfg->vnameserver6;
    slirp->tftp_server_name = g_strdup(cfg->tftp_server_name);

    if (cfg->vdnssearch) {
        translate_dnssearch(slirp, cfg->vdnssearch);
    }
    slirp->if_mtu = cfg->if_mtu == 0 ? IF_MTU_DEFAULT : cfg->if_mtu;
    slirp->if_mru = cfg->if_mru == 0 ? IF_MRU_DEFAULT : cfg->if_mru;
    slirp->disable_host_loopback = cfg->disable_host_loopback;
    slirp->enable_emu = cfg->enable_emu;

    if (cfg->version >= 2) {
        slirp->outbound_addr = cfg->outbound_addr;
        slirp->outbound_addr6 = cfg->outbound_addr6;
    } else {
        slirp->outbound_addr = NULL;
        slirp->outbound_addr6 = NULL;
    }

    if (cfg->version >= 3) {
        slirp->disable_dns = cfg->disable_dns;
    } else {
        slirp->disable_dns = false;
    }

    if (cfg->version >= 4) {
        slirp->disable_dhcp = cfg->disable_dhcp;
    } else {
        slirp->disable_dhcp = false;
    }

    if (slirp->cfg_version >= 4 && slirp->cb->init_completed) {
        slirp->cb->init_completed(slirp, slirp->opaque);
    }

    if (cfg->version >= 5) {
        slirp->mfr_id = cfg->mfr_id;
        memcpy(slirp->oob_eth_addr, cfg->oob_eth_addr, ETH_ALEN);
    } else {
        slirp->mfr_id = 0;
        memset(slirp->oob_eth_addr, 0, ETH_ALEN);
    }

    ip6_post_init(slirp);
    return slirp;
}

Slirp *slirp_init(int restricted, bool in_enabled, struct in_addr vnetwork,
                  struct in_addr vnetmask, struct in_addr vhost,
                  bool in6_enabled, struct in6_addr vprefix_addr6,
                  uint8_t vprefix_len, struct in6_addr vhost6,
                  const char *vhostname, const char *tftp_server_name,
                  const char *tftp_path, const char *bootfile,
                  struct in_addr vdhcp_start, struct in_addr vnameserver,
                  struct in6_addr vnameserver6, const char **vdnssearch,
                  const char *vdomainname, const SlirpCb *callbacks,
                  void *opaque)
{
    SlirpConfig cfg;
    memset(&cfg, 0, sizeof(cfg));
    cfg.version = 1;
    cfg.restricted = restricted;
    cfg.in_enabled = in_enabled;
    cfg.vnetwork = vnetwork;
    cfg.vnetmask = vnetmask;
    cfg.vhost = vhost;
    cfg.in6_enabled = in6_enabled;
    cfg.vprefix_addr6 = vprefix_addr6;
    cfg.vprefix_len = vprefix_len;
    cfg.vhost6 = vhost6;
    cfg.vhostname = vhostname;
    cfg.tftp_server_name = tftp_server_name;
    cfg.tftp_path = tftp_path;
    cfg.bootfile = bootfile;
    cfg.vdhcp_start = vdhcp_start;
    cfg.vnameserver = vnameserver;
    cfg.vnameserver6 = vnameserver6;
    cfg.vdnssearch = vdnssearch;
    cfg.vdomainname = vdomainname;
    return slirp_new(&cfg, callbacks, opaque);
}

void slirp_cleanup(Slirp *slirp)
{
    struct gfwd_list *e, *next;

    for (e = slirp->guestfwd_list; e; e = next) {
        next = e->ex_next;
        g_free(e->ex_exec);
        g_free(e->ex_unix);
        g_free(e);
    }

    ip_cleanup(slirp);
    ip6_cleanup(slirp);
    m_cleanup(slirp);

    g_rand_free(slirp->grand);

    g_free(slirp->vdnssearch);
    g_free(slirp->tftp_prefix);
    g_free(slirp->bootp_filename);
    g_free(slirp->vdomainname);
    g_free(slirp);
}

#define CONN_CANFSEND(so) \
    (((so)->so_state & (SS_FCANTSENDMORE | SS_ISFCONNECTED)) == SS_ISFCONNECTED)
#define CONN_CANFRCV(so) \
    (((so)->so_state & (SS_FCANTRCVMORE | SS_ISFCONNECTED)) == SS_ISFCONNECTED)

static void slirp_update_timeout(Slirp *slirp, uint32_t *timeout)
{
    uint32_t t;

    if (*timeout <= TIMEOUT_FAST) {
        return;
    }

    t = MIN(1000, *timeout);

    /* If we have tcp timeout with slirp, then we will fill @timeout with
     * more precise value.
     */
    if (slirp->time_fasttimo) {
        *timeout = TIMEOUT_FAST;
        return;
    }
    if (slirp->do_slowtimo) {
        t = MIN(TIMEOUT_SLOW, t);
    }
    *timeout = t;
}

void slirp_pollfds_fill(Slirp *slirp, uint32_t *timeout,
                        SlirpAddPollCb add_poll, void *opaque)
{
    struct socket *so, *so_next;

    /*
     * First, TCP sockets
     */

    /*
     * *_slowtimo needs calling if there are IP fragments
     * in the fragment queue, or there are TCP connections active
     */
    slirp->do_slowtimo = ((slirp->tcb.so_next != &slirp->tcb) ||
                          (&slirp->ipq.ip_link != slirp->ipq.ip_link.next));

    for (so = slirp->tcb.so_next; so != &slirp->tcb; so = so_next) {
        int events = 0;

        so_next = so->so_next;

        so->pollfds_idx = -1;

        /*
         * See if we need a tcp_fasttimo
         */
        if (slirp->time_fasttimo == 0 && so->so_tcpcb->t_flags & TF_DELACK) {
            slirp->time_fasttimo = curtime; /* Flag when want a fasttimo */
        }

        /*
         * NOFDREF can include still connecting to local-host,
         * newly socreated() sockets etc. Don't want to select these.
         */
        if (so->so_state & SS_NOFDREF || so->s == -1) {
            continue;
        }

        /*
         * Set for reading sockets which are accepting
         */
        if (so->so_state & SS_FACCEPTCONN) {
            so->pollfds_idx = add_poll(
                so->s, SLIRP_POLL_IN | SLIRP_POLL_HUP | SLIRP_POLL_ERR, opaque);
            continue;
        }

        /*
         * Set for writing sockets which are connecting
         */
        if (so->so_state & SS_ISFCONNECTING) {
            so->pollfds_idx =
                add_poll(so->s, SLIRP_POLL_OUT | SLIRP_POLL_ERR, opaque);
            continue;
        }

        /*
         * Set for writing if we are connected, can send more, and
         * we have something to send
         */
        if (CONN_CANFSEND(so) && so->so_rcv.sb_cc) {
            events |= SLIRP_POLL_OUT | SLIRP_POLL_ERR;
        }

        /*
         * Set for reading (and urgent data) if we are connected, can
         * receive more, and we have room for it.
         *
         * If sb is already half full, we will wait for the guest to consume it,
         * and notify again in sbdrop() when the sb becomes less than half full.
         */
        if (CONN_CANFRCV(so) &&
            (so->so_snd.sb_cc < (so->so_snd.sb_datalen / 2))) {
            events |= SLIRP_POLL_IN | SLIRP_POLL_HUP | SLIRP_POLL_ERR |
                      SLIRP_POLL_PRI;
        }

        if (events) {
            so->pollfds_idx = add_poll(so->s, events, opaque);
        }
    }

    /*
     * UDP sockets
     */
    for (so = slirp->udb.so_next; so != &slirp->udb; so = so_next) {
        so_next = so->so_next;

        so->pollfds_idx = -1;

        /*
         * See if it's timed out
         */
        if (so->so_expire) {
            if (so->so_expire <= curtime) {
                udp_detach(so);
                continue;
            } else {
                slirp->do_slowtimo = true; /* Let socket expire */
            }
        }

        /*
         * When UDP packets are received from over the
         * link, they're sendto()'d straight away, so
         * no need for setting for writing
         * Limit the number of packets queued by this session
         * to 4.  Note that even though we try and limit this
         * to 4 packets, the session could have more queued
         * if the packets needed to be fragmented
         * (XXX <= 4 ?)
         */
        if ((so->so_state & SS_ISFCONNECTED) && so->so_queued <= 4) {
            so->pollfds_idx = add_poll(
                so->s, SLIRP_POLL_IN | SLIRP_POLL_HUP | SLIRP_POLL_ERR, opaque);
        }
    }

    /*
     * ICMP sockets
     */
    for (so = slirp->icmp.so_next; so != &slirp->icmp; so = so_next) {
        so_next = so->so_next;

        so->pollfds_idx = -1;

        /*
         * See if it's timed out
         */
        if (so->so_expire) {
            if (so->so_expire <= curtime) {
                icmp_detach(so);
                continue;
            } else {
                slirp->do_slowtimo = true; /* Let socket expire */
            }
        }

        if (so->so_state & SS_ISFCONNECTED) {
            so->pollfds_idx = add_poll(
                so->s, SLIRP_POLL_IN | SLIRP_POLL_HUP | SLIRP_POLL_ERR, opaque);
        }
    }

    slirp_update_timeout(slirp, timeout);
}

void slirp_pollfds_poll(Slirp *slirp, int select_error,
                        SlirpGetREventsCb get_revents, void *opaque)
{
    struct socket *so, *so_next;
    int ret;

    curtime = slirp->cb->clock_get_ns(slirp->opaque) / SCALE_MS;

    /*
     * See if anything has timed out
     */
    if (slirp->time_fasttimo &&
        ((curtime - slirp->time_fasttimo) >= TIMEOUT_FAST)) {
        tcp_fasttimo(slirp);
        slirp->time_fasttimo = 0;
    }
    if (slirp->do_slowtimo &&
        ((curtime - slirp->last_slowtimo) >= TIMEOUT_SLOW)) {
        ip_slowtimo(slirp);
        tcp_slowtimo(slirp);
        slirp->last_slowtimo = curtime;
    }

    /*
     * Check sockets
     */
    if (!select_error) {
        /*
         * Check TCP sockets
         */
        for (so = slirp->tcb.so_next; so != &slirp->tcb; so = so_next) {
            int revents;

            so_next = so->so_next;

            revents = 0;
            if (so->pollfds_idx != -1) {
                revents = get_revents(so->pollfds_idx, opaque);
            }

            if (so->so_state & SS_NOFDREF || so->s == -1) {
                continue;
            }

#ifndef __APPLE__
            /*
             * Check for URG data
             * This will soread as well, so no need to
             * test for SLIRP_POLL_IN below if this succeeds.
             *
             * This is however disabled on MacOS, which apparently always
             * reports data as PRI when it is the last data of the
             * connection. We would then report it out of band, which the guest
             * would most probably not be ready for.
             */
            if (revents & SLIRP_POLL_PRI) {
                ret = sorecvoob(so);
                if (ret < 0) {
                    /* Socket error might have resulted in the socket being
                     * removed, do not try to do anything more with it. */
                    continue;
                }
            }
            /*
             * Check sockets for reading
             */
            else
#endif
                if (revents &
                     (SLIRP_POLL_IN | SLIRP_POLL_HUP | SLIRP_POLL_ERR | SLIRP_POLL_PRI)) {
                /*
                 * Check for incoming connections
                 */
                if (so->so_state & SS_FACCEPTCONN) {
                    tcp_connect(so);
                    continue;
                } /* else */
                ret = soread(so);

                /* Output it if we read something */
                if (ret > 0) {
                    tcp_output(sototcpcb(so));
                }
                if (ret < 0) {
                    /* Socket error might have resulted in the socket being
                     * removed, do not try to do anything more with it. */
                    continue;
                }
            }

            /*
             * Check sockets for writing
             */
            if (!(so->so_state & SS_NOFDREF) &&
                (revents & (SLIRP_POLL_OUT | SLIRP_POLL_ERR))) {
                /*
                 * Check for non-blocking, still-connecting sockets
                 */
                if (so->so_state & SS_ISFCONNECTING) {
                    /* Connected */
                    so->so_state &= ~SS_ISFCONNECTING;

                    ret = send(so->s, (const void *)&ret, 0, 0);
                    if (ret < 0) {
                        /* XXXXX Must fix, zero bytes is a NOP */
                        if (errno == EAGAIN || errno == EWOULDBLOCK ||
                            errno == EINPROGRESS || errno == ENOTCONN) {
                            continue;
                        }

                        /* else failed */
                        so->so_state &= SS_PERSISTENT_MASK;
                        so->so_state |= SS_NOFDREF;
                    }
                    /* else so->so_state &= ~SS_ISFCONNECTING; */

                    /*
                     * Continue tcp_input
                     */
                    tcp_input((struct mbuf *)NULL, sizeof(struct ip), so,
                              so->so_ffamily);
                    /* continue; */
                } else {
                    ret = sowrite(so);
                    if (ret > 0) {
                        /* Call tcp_output in case we need to send a window
                         * update to the guest, otherwise it will be stuck
                         * until it sends a window probe. */
                        tcp_output(sototcpcb(so));
                    }
                }
            }
        }

        /*
         * Now UDP sockets.
         * Incoming packets are sent straight away, they're not buffered.
         * Incoming UDP data isn't buffered either.
         */
        for (so = slirp->udb.so_next; so != &slirp->udb; so = so_next) {
            int revents;

            so_next = so->so_next;

            revents = 0;
            if (so->pollfds_idx != -1) {
                revents = get_revents(so->pollfds_idx, opaque);
            }

            if (so->s != -1 &&
                (revents & (SLIRP_POLL_IN | SLIRP_POLL_HUP | SLIRP_POLL_ERR))) {
                sorecvfrom(so);
            }
        }

        /*
         * Check incoming ICMP relies.
         */
        for (so = slirp->icmp.so_next; so != &slirp->icmp; so = so_next) {
            int revents;

            so_next = so->so_next;

            revents = 0;
            if (so->pollfds_idx != -1) {
                revents = get_revents(so->pollfds_idx, opaque);
            }

            if (so->s != -1 &&
                (revents & (SLIRP_POLL_IN | SLIRP_POLL_HUP | SLIRP_POLL_ERR))) {
                icmp_receive(so);
            }
        }
    }

    if_start(slirp);
}

static void arp_input(Slirp *slirp, const uint8_t *pkt, int pkt_len)
{
    const struct slirp_arphdr *ah =
        (const struct slirp_arphdr *)(pkt + ETH_HLEN);
    uint8_t arp_reply[MAX(2 + ETH_HLEN + sizeof(struct slirp_arphdr), 2 + 64)];
    struct ethhdr *reh = (struct ethhdr *)(arp_reply + 2);
    struct slirp_arphdr *rah = (struct slirp_arphdr *)(arp_reply + 2 + ETH_HLEN);
    int ar_op;
    struct gfwd_list *ex_ptr;

    if (!slirp->in_enabled) {
        return;
    }

    if (pkt_len < ETH_HLEN + sizeof(struct slirp_arphdr)) {
        return; /* packet too short */
    }

    ar_op = ntohs(ah->ar_op);
    switch (ar_op) {
    case ARPOP_REQUEST:
        if (ah->ar_tip == ah->ar_sip) {
            /* Gratuitous ARP */
            arp_table_add(slirp, ah->ar_sip, ah->ar_sha);
            return;
        }

        if ((ah->ar_tip & slirp->vnetwork_mask.s_addr) ==
            slirp->vnetwork_addr.s_addr) {
            if (ah->ar_tip == slirp->vnameserver_addr.s_addr ||
                ah->ar_tip == slirp->vhost_addr.s_addr)
                goto arp_ok;
            /* TODO: IPv6 */
            for (ex_ptr = slirp->guestfwd_list; ex_ptr;
                 ex_ptr = ex_ptr->ex_next) {
                if (ex_ptr->ex_addr.s_addr == ah->ar_tip)
                    goto arp_ok;
            }
            return;
        arp_ok:
            memset(arp_reply, 0, sizeof(arp_reply));

            arp_table_add(slirp, ah->ar_sip, ah->ar_sha);

            /* ARP request for alias/dns mac address */
            memcpy(reh->h_dest, pkt + ETH_ALEN, ETH_ALEN);
            memcpy(reh->h_source, special_ethaddr, ETH_ALEN - 4);
            memcpy(&reh->h_source[2], &ah->ar_tip, 4);
            reh->h_proto = htons(ETH_P_ARP);

            rah->ar_hrd = htons(1);
            rah->ar_pro = htons(ETH_P_IP);
            rah->ar_hln = ETH_ALEN;
            rah->ar_pln = 4;
            rah->ar_op = htons(ARPOP_REPLY);
            memcpy(rah->ar_sha, reh->h_source, ETH_ALEN);
            rah->ar_sip = ah->ar_tip;
            memcpy(rah->ar_tha, ah->ar_sha, ETH_ALEN);
            rah->ar_tip = ah->ar_sip;
            slirp_send_packet_all(slirp, arp_reply + 2, sizeof(arp_reply) - 2);
        }
        break;
    case ARPOP_REPLY:
        arp_table_add(slirp, ah->ar_sip, ah->ar_sha);
        break;
    default:
        break;
    }
}

void slirp_input(Slirp *slirp, const uint8_t *pkt, int pkt_len)
{
    struct mbuf *m;
    int proto;

    if (pkt_len < ETH_HLEN)
        return;

    proto = (((uint16_t)pkt[12]) << 8) + pkt[13];
    switch (proto) {
    case ETH_P_ARP:
        arp_input(slirp, pkt, pkt_len);
        break;
    case ETH_P_IP:
    case ETH_P_IPV6:
        m = m_get(slirp);
        if (!m)
            return;
        /* Note: we add 2 to align the IP header on 8 bytes despite the ethernet
         * header, and add the margin for the tcpiphdr overhead  */
        if (M_FREEROOM(m) < pkt_len + TCPIPHDR_DELTA + 2) {
            m_inc(m, pkt_len + TCPIPHDR_DELTA + 2);
        }
        m->m_len = pkt_len + TCPIPHDR_DELTA + 2;
        memcpy(m->m_data + TCPIPHDR_DELTA + 2, pkt, pkt_len);

        m->m_data += TCPIPHDR_DELTA + 2 + ETH_HLEN;
        m->m_len -= TCPIPHDR_DELTA + 2 + ETH_HLEN;

        if (proto == ETH_P_IP) {
            ip_input(m);
        } else if (proto == ETH_P_IPV6) {
            ip6_input(m);
        }
        break;

    case ETH_P_NCSI:
        ncsi_input(slirp, pkt, pkt_len);
        break;

    default:
        break;
    }
}

/* Prepare the IPv4 packet to be sent to the ethernet device. Returns 1 if no
 * packet should be sent, 0 if the packet must be re-queued, 2 if the packet
 * is ready to go.
 */
static int if_encap4(Slirp *slirp, struct mbuf *ifm, struct ethhdr *eh,
                     uint8_t ethaddr[ETH_ALEN])
{
    const struct ip *iph = (const struct ip *)ifm->m_data;

    if (!arp_table_search(slirp, iph->ip_dst.s_addr, ethaddr)) {
        uint8_t arp_req[2 + ETH_HLEN + sizeof(struct slirp_arphdr)];
        struct ethhdr *reh = (struct ethhdr *)(arp_req + 2);
        struct slirp_arphdr *rah = (struct slirp_arphdr *)(arp_req + 2 + ETH_HLEN);

        if (!ifm->resolution_requested) {
            /* If the client addr is not known, send an ARP request */
            memset(reh->h_dest, 0xff, ETH_ALEN);
            memcpy(reh->h_source, special_ethaddr, ETH_ALEN - 4);
            memcpy(&reh->h_source[2], &slirp->vhost_addr, 4);
            reh->h_proto = htons(ETH_P_ARP);
            rah->ar_hrd = htons(1);
            rah->ar_pro = htons(ETH_P_IP);
            rah->ar_hln = ETH_ALEN;
            rah->ar_pln = 4;
            rah->ar_op = htons(ARPOP_REQUEST);

            /* source hw addr */
            memcpy(rah->ar_sha, special_ethaddr, ETH_ALEN - 4);
            memcpy(&rah->ar_sha[2], &slirp->vhost_addr, 4);

            /* source IP */
            rah->ar_sip = slirp->vhost_addr.s_addr;

            /* target hw addr (none) */
            memset(rah->ar_tha, 0, ETH_ALEN);

            /* target IP */
            rah->ar_tip = iph->ip_dst.s_addr;
            slirp->client_ipaddr = iph->ip_dst;
            slirp_send_packet_all(slirp, arp_req + 2, sizeof(arp_req) - 2);
            ifm->resolution_requested = true;

            /* Expire request and drop outgoing packet after 1 second */
            ifm->expiration_date =
                slirp->cb->clock_get_ns(slirp->opaque) + 1000000000ULL;
        }
        return 0;
    } else {
        memcpy(eh->h_source, special_ethaddr, ETH_ALEN - 4);
        /* XXX: not correct */
        memcpy(&eh->h_source[2], &slirp->vhost_addr, 4);
        eh->h_proto = htons(ETH_P_IP);

        /* Send this */
        return 2;
    }
}

/* Prepare the IPv6 packet to be sent to the ethernet device. Returns 1 if no
 * packet should be sent, 0 if the packet must be re-queued, 2 if the packet
 * is ready to go.
 */
static int if_encap6(Slirp *slirp, struct mbuf *ifm, struct ethhdr *eh,
                     uint8_t ethaddr[ETH_ALEN])
{
    const struct ip6 *ip6h = mtod(ifm, const struct ip6 *);
    if (!ndp_table_search(slirp, ip6h->ip_dst, ethaddr)) {
        if (!ifm->resolution_requested) {
            ndp_send_ns(slirp, ip6h->ip_dst);
            ifm->resolution_requested = true;
            ifm->expiration_date =
                slirp->cb->clock_get_ns(slirp->opaque) + 1000000000ULL;
        }
        return 0;
    } else {
        eh->h_proto = htons(ETH_P_IPV6);
        in6_compute_ethaddr(ip6h->ip_src, eh->h_source);

        /* Send this */
        return 2;
    }
}

/* Output the IP packet to the ethernet device. Returns 0 if the packet must be
 * re-queued.
 */
int if_encap(Slirp *slirp, struct mbuf *ifm)
{
    uint8_t buf[IF_MTU_MAX + 100];
    struct ethhdr *eh = (struct ethhdr *)(buf + 2);
    uint8_t ethaddr[ETH_ALEN];
    const struct ip *iph = (const struct ip *)ifm->m_data;
    int ret;
    char ethaddr_str[ETH_ADDRSTRLEN];

    if (ifm->m_len + ETH_HLEN > sizeof(buf) - 2) {
        return 1;
    }

    switch (iph->ip_v) {
    case IPVERSION:
        ret = if_encap4(slirp, ifm, eh, ethaddr);
        if (ret < 2) {
            return ret;
        }
        break;

    case IP6VERSION:
        ret = if_encap6(slirp, ifm, eh, ethaddr);
        if (ret < 2) {
            return ret;
        }
        break;

    default:
        g_assert_not_reached();
    }

    memcpy(eh->h_dest, ethaddr, ETH_ALEN);
    DEBUG_ARG("src = %s", slirp_ether_ntoa(eh->h_source, ethaddr_str,
                                           sizeof(ethaddr_str)));
    DEBUG_ARG("dst = %s", slirp_ether_ntoa(eh->h_dest, ethaddr_str,
                                           sizeof(ethaddr_str)));
    memcpy(buf + 2 + sizeof(struct ethhdr), ifm->m_data, ifm->m_len);
    slirp_send_packet_all(slirp, buf + 2, ifm->m_len + ETH_HLEN);
    return 1;
}

/* Drop host forwarding rule, return 0 if found. */
int slirp_remove_hostfwd(Slirp *slirp, int is_udp, struct in_addr host_addr,
                         int host_port)
{
    struct socket *so;
    struct socket *head = (is_udp ? &slirp->udb : &slirp->tcb);
    struct sockaddr_in addr;
    int port = htons(host_port);
    socklen_t addr_len;

    for (so = head->so_next; so != head; so = so->so_next) {
        addr_len = sizeof(addr);
        if ((so->so_state & SS_HOSTFWD) &&
            getsockname(so->s, (struct sockaddr *)&addr, &addr_len) == 0 &&
            addr_len == sizeof(addr) &&
            addr.sin_family == AF_INET &&
            addr.sin_addr.s_addr == host_addr.s_addr &&
            addr.sin_port == port) {
            so->slirp->cb->unregister_poll_fd(so->s, so->slirp->opaque);
            closesocket(so->s);
            sofree(so);
            return 0;
        }
    }

    return -1;
}

int slirp_add_hostfwd(Slirp *slirp, int is_udp, struct in_addr host_addr,
                      int host_port, struct in_addr guest_addr, int guest_port)
{
    if (!guest_addr.s_addr) {
        guest_addr = slirp->vdhcp_startaddr;
    }
    if (is_udp) {
        if (!udp_listen(slirp, host_addr.s_addr, htons(host_port),
                        guest_addr.s_addr, htons(guest_port), SS_HOSTFWD))
            return -1;
    } else {
        if (!tcp_listen(slirp, host_addr.s_addr, htons(host_port),
                        guest_addr.s_addr, htons(guest_port), SS_HOSTFWD))
            return -1;
    }
    return 0;
}

int slirp_remove_hostxfwd(Slirp *slirp,
                          const struct sockaddr *haddr, socklen_t haddrlen,
                          int flags)
{
    struct socket *so;
    struct socket *head = (flags & SLIRP_HOSTFWD_UDP ? &slirp->udb : &slirp->tcb);
    struct sockaddr_storage addr;
    socklen_t addr_len;

    for (so = head->so_next; so != head; so = so->so_next) {
        addr_len = sizeof(addr);
        if ((so->so_state & SS_HOSTFWD) &&
            getsockname(so->s, (struct sockaddr *)&addr, &addr_len) == 0 &&
            sockaddr_equal(&addr, (const struct sockaddr_storage *) haddr)) {
            so->slirp->cb->unregister_poll_fd(so->s, so->slirp->opaque);
            closesocket(so->s);
            sofree(so);
            return 0;
        }
    }

    return -1;
}

int slirp_add_hostxfwd(Slirp *slirp,
                       const struct sockaddr *haddr, socklen_t haddrlen,
                       const struct sockaddr *gaddr, socklen_t gaddrlen,
                       int flags)
{
    struct sockaddr_in gdhcp_addr;
    int fwd_flags = SS_HOSTFWD;

    if (flags & SLIRP_HOSTFWD_V6ONLY)
        fwd_flags |= SS_HOSTFWD_V6ONLY;

    if (gaddr->sa_family == AF_INET) {
        const struct sockaddr_in *gaddr_in = (const struct sockaddr_in *) gaddr;

        if (gaddrlen < sizeof(struct sockaddr_in)) {
            errno = EINVAL;
            return -1;
        }

        if (!gaddr_in->sin_addr.s_addr) {
            gdhcp_addr = *gaddr_in;
            gdhcp_addr.sin_addr = slirp->vdhcp_startaddr;
            gaddr = (struct sockaddr *) &gdhcp_addr;
            gaddrlen = sizeof(gdhcp_addr);
        }
    } else {
        if (gaddrlen < sizeof(struct sockaddr_in6)) {
            errno = EINVAL;
            return -1;
        }

        /*
         * Libslirp currently only provides a stateless DHCPv6 server, thus
         * we can't translate "addr-any" to the guest here. Instead, we defer
         * performing the translation to when it's needed. See
         * soassign_guest_addr_if_needed().
         */
    }

    if (flags & SLIRP_HOSTFWD_UDP) {
        if (!udpx_listen(slirp, haddr, haddrlen,
                                gaddr, gaddrlen,
                                fwd_flags))
            return -1;
    } else {
        if (!tcpx_listen(slirp, haddr, haddrlen,
                                gaddr, gaddrlen,
                                fwd_flags))
            return -1;
    }
    return 0;
}

/* TODO: IPv6 */
static bool check_guestfwd(Slirp *slirp, struct in_addr *guest_addr,
                           int guest_port)
{
    struct gfwd_list *tmp_ptr;

    if (!guest_addr->s_addr) {
        guest_addr->s_addr = slirp->vnetwork_addr.s_addr |
                             (htonl(0x0204) & ~slirp->vnetwork_mask.s_addr);
    }
    if ((guest_addr->s_addr & slirp->vnetwork_mask.s_addr) !=
            slirp->vnetwork_addr.s_addr ||
        guest_addr->s_addr == slirp->vhost_addr.s_addr ||
        guest_addr->s_addr == slirp->vnameserver_addr.s_addr) {
        return false;
    }

    /* check if the port is "bound" */
    for (tmp_ptr = slirp->guestfwd_list; tmp_ptr; tmp_ptr = tmp_ptr->ex_next) {
        if (guest_port == tmp_ptr->ex_fport &&
            guest_addr->s_addr == tmp_ptr->ex_addr.s_addr)
            return false;
    }

    return true;
}

int slirp_add_exec(Slirp *slirp, const char *cmdline,
                   struct in_addr *guest_addr, int guest_port)
{
    if (!check_guestfwd(slirp, guest_addr, guest_port)) {
        return -1;
    }

    add_exec(&slirp->guestfwd_list, cmdline, *guest_addr, htons(guest_port));
    return 0;
}

int slirp_add_unix(Slirp *slirp, const char *unixsock,
                   struct in_addr *guest_addr, int guest_port)
{
#ifdef G_OS_UNIX
    if (!check_guestfwd(slirp, guest_addr, guest_port)) {
        return -1;
    }

    add_unix(&slirp->guestfwd_list, unixsock, *guest_addr, htons(guest_port));
    return 0;
#else
    g_warn_if_reached();
    return -1;
#endif
}

int slirp_add_guestfwd(Slirp *slirp, SlirpWriteCb write_cb, void *opaque,
                       struct in_addr *guest_addr, int guest_port)
{
    if (!check_guestfwd(slirp, guest_addr, guest_port)) {
        return -1;
    }

    add_guestfwd(&slirp->guestfwd_list, write_cb, opaque, *guest_addr,
                 htons(guest_port));
    return 0;
}

int slirp_remove_guestfwd(Slirp *slirp, struct in_addr guest_addr,
                          int guest_port)
{
    return remove_guestfwd(&slirp->guestfwd_list, guest_addr,
                           htons(guest_port));
}

slirp_ssize_t slirp_send(struct socket *so, const void *buf, size_t len, int flags)
{
    if (so->s == -1 && so->guestfwd) {
        /* XXX this blocks entire thread. Rewrite to use
         * qemu_chr_fe_write and background I/O callbacks */
        so->guestfwd->write_cb(buf, len, so->guestfwd->opaque);
        return len;
    }

    if (so->s == -1) {
        /*
         * This should in theory not happen but it is hard to be
         * sure because some code paths will end up with so->s == -1
         * on a failure but don't dispose of the struct socket.
         * Check specifically, so we don't pass -1 to send().
         */
        errno = EBADF;
        return -1;
    }

    return send(so->s, buf, len, flags);
}

struct socket *slirp_find_ctl_socket(Slirp *slirp, struct in_addr guest_addr,
                                     int guest_port)
{
    struct socket *so;

    /* TODO: IPv6 */
    for (so = slirp->tcb.so_next; so != &slirp->tcb; so = so->so_next) {
        if (so->so_faddr.s_addr == guest_addr.s_addr &&
            htons(so->so_fport) == guest_port) {
            return so;
        }
    }
    return NULL;
}

size_t slirp_socket_can_recv(Slirp *slirp, struct in_addr guest_addr,
                             int guest_port)
{
    struct iovec iov[2];
    struct socket *so;

    so = slirp_find_ctl_socket(slirp, guest_addr, guest_port);

    if (!so || so->so_state & SS_NOFDREF) {
        return 0;
    }

    if (!CONN_CANFRCV(so) || so->so_snd.sb_cc >= (so->so_snd.sb_datalen / 2)) {
        /* If the sb is already half full, we will wait for the guest to consume it,
         * and notify again in sbdrop() when the sb becomes less than half full. */
        return 0;
    }

    return sopreprbuf(so, iov, NULL);
}

void slirp_socket_recv(Slirp *slirp, struct in_addr guest_addr, int guest_port,
                       const uint8_t *buf, int size)
{
    int ret;
    struct socket *so = slirp_find_ctl_socket(slirp, guest_addr, guest_port);

    if (!so)
        return;

    ret = soreadbuf(so, (const char *)buf, size);

    if (ret > 0)
        tcp_output(sototcpcb(so));
}

void slirp_send_packet_all(Slirp *slirp, const void *buf, size_t len)
{
    slirp_ssize_t ret = slirp->cb->send_packet(buf, len, slirp->opaque);

    if (ret < 0) {
        g_critical("Failed to send packet, ret: %ld", (long)ret);
    } else if (ret < len) {
        DEBUG_ERROR("send_packet() didn't send all data: %ld < %lu", (long)ret,
                    (unsigned long)len);
    }
}
