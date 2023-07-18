/* SPDX-License-Identifier: BSD-3-Clause */
/*
 * Copyright (c) 2021-2022 Samuel Thibault
 */

/*
 * This simple test configures slirp and tries to ping it
 *
 * Note: to make this example actually be able to use the outside world, you
 * need to either
 * - run as root
 * - set /proc/sys/net/ipv4/ping_group_range to allow sending ICMP echo requests
 * - run a UDP echo server on the target
 */

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <assert.h>

#include "libslirp.h"

//#define _WIN32
#ifdef _WIN32
//#include <sys/select.h>
#include <winsock2.h>
static int slirp_inet_aton(const char *cp, struct in_addr *ia)
{
    uint32_t addr = inet_addr(cp);
    if (addr == 0xffffffff) {
        return 0;
    }
    ia->s_addr = addr;
    return 1;
}
#define inet_aton slirp_inet_aton
#else
#include <sys/socket.h>
#include <arpa/inet.h>
#include <poll.h>
#endif

/* Dumb simulation tick: 100ms */
#define TICK 100

static Slirp *slirp;
static bool done;
static int64_t mytime;

/* Print a frame for debugging */
static void print_frame(const uint8_t *data, size_t len) {
    int i;

    printf("\ngot packet size %zd:\n", len);
    for (i = 0; i < len; i++) {
        if (i && i % 16 == 0)
            printf("\n");
        printf("%s%02x", i % 16 ? " " : "", data[i]);
    }
    if (len % 16 != 0)
        printf("\n");
    printf("\n");
}

/* Classical 16bit checksum */
static void checksum(uint8_t *data, size_t size, uint8_t *cksum) {
    uint32_t sum = 0;
    int i;

    cksum[0] = 0;
    cksum[1] = 0;

    for (i = 0; i+1 < size; i += 2)
        sum += (((uint16_t) data[i]) << 8) + data[i+1];
    if (i < size) /* Odd number of bytes */
        sum += ((uint16_t) data[i]) << 8;

    sum = (sum & 0xffff) + (sum >> 16);
    sum = (sum & 0xffff) + (sum >> 16);
    sum = ~sum;

    cksum[0] = sum >> 8;
    cksum[1] = sum;
}

/* This is called when receiving a packet from the virtual network, for the
 * guest */
static slirp_ssize_t send_packet(const void *buf, size_t len, void *opaque) {
    const uint8_t *data = buf;

    assert(len >= 14);

    if (data[12] == 0x86 &&
        data[13] == 0xdd) {
        /* Ignore IPv6 */
        return len;
    }

    print_frame(data, len);

    if (data[12] == 0x08 &&
        data[13] == 0x06) {
        /* ARP */
        /* We expect receiving an ARP request for our address */

        /* Ethernet address type */
        assert(data[14] == 0x00);
        assert(data[15] == 0x01);

        /* IPv4 address type */
        assert(data[16] == 0x08);
        assert(data[17] == 0x00);

        /* Ethernet addresses are 6 bytes long */
        assert(data[18] == 0x06);

        /* IPv4 addresses are 4 bytes long */
        assert(data[19] == 0x04);

        /* Opcode: ARP request */
        assert(data[20] == 0x00);
        assert(data[21] == 0x01);

        /* Ok, reply! */
        uint8_t myframe[] = {
            /*** Ethernet ***/
            /* dst */
            0x52, 0x55, 0x0a, 0x00, 0x02, 0x02,
            /* src */
            0x52, 0x55, 0x0a, 0x00, 0x02, 0x0e,
            /* Type: ARP */
            0x08, 0x06,

            /* ether,   IPv4,       */
            0x00, 0x01, 0x08, 0x00,
            /* elen, IPlen */
            0x06, 0x04,
            /* ARP reply */
            0x00, 0x02,

            /* Our ethernet address */
            0x52, 0x55, 0x0a, 0x00, 0x02, 0x0e,
            /* Our IP address */
            0x0a, 0x00, 0x02, 0x0e,

            /* Host ethernet address */
            0x52, 0x55, 0x0a, 0x00, 0x02, 0x02,
            /* Host IP address */
            0x0a, 0x00, 0x02, 0x02,
        };

        slirp_input(slirp, myframe, sizeof(myframe));
    }

    if (data[12] == 0x08 &&
        data[13] == 0x00) {
        /* IPv4 */
        assert(len >= 14 + 20);

        /* We expect receiving the ICMP echo reply for our echo request */

        /* IPv + hlen */
        assert(data[14] == 0x45);

        /* proto: ICMP */
        assert(data[23] == 0x01);

        /* ICMP */
        assert(len >= 14 + 20 + 8 + 4);

        /* ICMP type: reply */
        assert(data[34] == 0x00);

        /* Check the data */
        assert(data[42] == 0xde);
        assert(data[43] == 0xad);
        assert(data[44] == 0xbe);
        assert(data[45] == 0xef);

        /* Got the answer! */
        printf("got it!\n");
        done = 1;
    }

    return len;
}

static void guest_error(const char *msg, void *opaque) {
    printf("guest error %s\n",  msg);
}


/*
 * Dumb timer implementation
 */
static int64_t clock_get_ns(void *opaque) {
    return mytime;
}

struct timer {
    SlirpTimerId id;
    void *cb_opaque;
    int64_t expire;
    struct timer *next;
};

static struct timer *timer_queue;

static void *timer_new_opaque(SlirpTimerId id, void *cb_opaque, void *opaque) {
    struct timer *new_timer = malloc(sizeof(*new_timer));
    new_timer->id = id;
    new_timer->cb_opaque = cb_opaque;
    new_timer->next = NULL;
    return new_timer;
}

static void timer_free(void *_timer, void *opaque) {
    struct timer *timer = _timer;
    struct timer **t;

    for (t = &timer_queue; *t != NULL; *t = (*t)->next) {
        if (*t == timer) {
            /* Not expired yet, drop it */
            *t = timer->next;
            break;
        }
    }

    free(timer);
}

static void timer_mod(void *_timer, int64_t expire_time, void *opaque) {
    struct timer *timer = _timer;
    struct timer **t;

    timer->expire = expire_time * 1000 * 1000;

    for (t = &timer_queue; *t != NULL; *t = (*t)->next) {
        if (expire_time < (*t)->expire)
            break;
    }

    timer->next = *t;
    *t = timer;
}

static void timer_check(Slirp *slirp) {
    while (timer_queue && timer_queue->expire <= mytime)
    {
        struct timer *t = timer_queue;
        printf("handling %p at time %lu\n",
               t, (unsigned long) timer_queue->expire);
        timer_queue = t->next;
        slirp_handle_timer(slirp, t->id, t->cb_opaque);
    }
}

static uint32_t timer_timeout(void) {
    if (timer_queue)
    {
        uint32_t timeout = (timer_queue->expire - mytime) / (1000 * 1000);
        if (timeout < TICK)
            return timeout;
    }

    return TICK;
}


/*
 * Dumb polling implementation
 */
static int npoll;
static void register_poll_fd(int fd, void *opaque) {
    /* We might want to prepare for polling on fd */
    npoll++;
}

static void unregister_poll_fd(int fd, void *opaque) {
    /* We might want to clear polling on fd */
    npoll--;
}

static void notify(void *opaque) {
    /* No need for this in single-thread case */
}

#ifdef _WIN32
/* select() variant */
static fd_set readfds, writefds, exceptfds;
static int maxfd;
static int add_poll_cb(int fd, int events, void *opaque)
{
    if (events & SLIRP_POLL_IN)
        FD_SET(fd, &readfds);
    if (events & SLIRP_POLL_OUT)
        FD_SET(fd, &writefds);
    if (events & SLIRP_POLL_PRI)
        FD_SET(fd, &exceptfds);
    if (maxfd < fd)
        maxfd = fd;
    return fd;
}

static int get_revents_cb(int idx, void *opaque)
{
    int event = 0;
    if (FD_ISSET(idx, &readfds))
        event |= SLIRP_POLL_IN;
    if (FD_ISSET(idx, &writefds))
        event |= SLIRP_POLL_OUT;
    if (FD_ISSET(idx, &exceptfds))
        event |= SLIRP_POLL_PRI;
    return event;
}

static void dopoll(uint32_t timeout) {
    int err;
    FD_ZERO(&readfds);
    FD_ZERO(&writefds);
    FD_ZERO(&exceptfds);
    maxfd = 0;

    slirp_pollfds_fill(slirp, &timeout, add_poll_cb, NULL);
    printf("we will use timeout %u\n", (unsigned) timeout);

    struct timeval tv = {
        .tv_sec = timeout / 1000,
        .tv_usec = (timeout % 1000) * 1000,
    };
    err = select(maxfd+1, &readfds, &writefds, &exceptfds, &tv);

    slirp_pollfds_poll(slirp, err < 0, get_revents_cb, NULL);
}
#else
/* poll() variant */
static struct pollfd *fds;
static int cur_poll;
static int add_poll_cb(int fd, int events, void *opaque)
{
    short poll_events = 0;

    assert(cur_poll < npoll);
    fds[cur_poll].fd = fd;

    if (events & SLIRP_POLL_IN)
        poll_events |= POLLIN;
    if (events & SLIRP_POLL_OUT)
        poll_events |= POLLOUT;
    if (events & SLIRP_POLL_PRI)
        poll_events |= POLLPRI;
    fds[cur_poll].events = poll_events;

    return cur_poll++;
}

static int get_revents_cb(int idx, void *opaque)
{
    return fds[idx].revents;
}

static void dopoll(uint32_t timeout) {
    int err;
    fds = malloc(sizeof(*fds) * npoll);
    cur_poll = 0;

    slirp_pollfds_fill(slirp, &timeout, add_poll_cb, NULL);
    printf("we will use timeout %u\n", (unsigned) timeout);

    err = poll(fds, cur_poll, timeout);

    slirp_pollfds_poll(slirp, err < 0, get_revents_cb, NULL);

    free(fds);
}
#endif


static struct SlirpCb callbacks = {
    .send_packet = send_packet,
    .guest_error = guest_error,
    .clock_get_ns = clock_get_ns,
    .timer_new_opaque = timer_new_opaque,
    .timer_free = timer_free,
    .timer_mod = timer_mod,
    .register_poll_fd = register_poll_fd,
    .unregister_poll_fd = unregister_poll_fd,
    .notify = notify,
};


int main(int argc, char *argv[]) {
    SlirpConfig config = {
        .version = 4,
        .restricted = false,
        .in_enabled = true,
        .vnetwork.s_addr = htonl(0x0a000200),
        .vnetmask.s_addr = htonl(0xffffff00),
        .vhost.s_addr = htonl(0x0a000202),
        .vdhcp_start.s_addr = htonl(0x0a00020f),
        .vnameserver.s_addr = htonl(0x0a000203),
        .disable_host_loopback = false,
        .enable_emu = false,
        .disable_dns = false,
    };
    uint32_t timeout = 0;

    printf("Slirp version %s\n", slirp_version_string());

#if !defined(_WIN32)
    inet_pton(AF_INET6, "fec0::", &config.vprefix_addr6);
    config.vprefix_len = 64;
    config.vhost6 = config.vprefix_addr6;
    config.vhost6.s6_addr[15] = 2;
    config.vnameserver6 = config.vprefix_addr6;
    config.vnameserver6.s6_addr[15] = 2;
    config.in6_enabled = true,
#endif

    slirp = slirp_new(&config, &callbacks, NULL);

    /* Send echo request */
    uint8_t myframe[] = {
        /*** Ethernet ***/
        /* dst */
        0x52, 0x55, 0x0a, 0x00, 0x02, 0x02,
        /* src */
        0x52, 0x55, 0x0a, 0x00, 0x02, 0x0e,
        /* Type: IPv4 */
        0x08, 0x00,

        /*** IPv4 ***/
        /* vhl,tos, len         */
        0x45, 0x00, 0x00, 0x20,
        /* id,      off (DF)    */
        0x68, 0xd7, 0x40, 0x00,
        /* ttl,pro, cksum      */
        0x40, 0x01, 0x00, 0x00,
        /* src                  */
        0x0a, 0x00, 0x02, 0x0e,
        /* dst                  */
        0x00, 0x00, 0x00, 0x00,

        /*** ICMPv4 ***/
        /* type, code, cksum    */
        0x08, 0x00, 0x00, 0x00,
        /* id,     seq          */
        0x01, 0xec, 0x00, 0x01,
        /* data                 */
        0xde, 0xad, 0xbe, 0xef,
    };

    struct in_addr in_addr = { .s_addr = htonl(0x0a000202) };
    if (argc > 1) {
        if (inet_aton(argv[1], &in_addr) == 0) {
            printf("usage: %s [destination IPv4 address]\n", argv[0]);
            exit(EXIT_FAILURE);
        }
    }
    uint32_t addr = ntohl(in_addr.s_addr);
    myframe[30] = addr >> 24;
    myframe[31] = addr >> 16;
    myframe[32] = addr >> 8;
    myframe[33] = addr >> 0;

    /* IPv4 header checksum */
    checksum(&myframe[14], 20, &myframe[24]);
    /* ICMP header checksum */
    checksum(&myframe[34], 12, &myframe[36]);

    slirp_input(slirp, myframe, sizeof(myframe));

    /* Wait for echo reply */
    while (!done) {
        printf("time %lu\n", (unsigned long) mytime);

        timer_check(slirp);
        /* Here we make the virtual time wait like the real time, but we could
         * make it wait differently */
        timeout = timer_timeout();
        printf("we wish timeout %u\n", (unsigned) timeout);

        dopoll(timeout);

        /* Fake that the tick elapsed */
        mytime += TICK * 1000 * 1000;
    }

    slirp_cleanup(slirp);
}
