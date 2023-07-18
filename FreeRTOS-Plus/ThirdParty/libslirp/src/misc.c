/* SPDX-License-Identifier: BSD-3-Clause */
/*
 * Copyright (c) 1995 Danny Gasparovski.
 */

#include "slirp.h"
#ifdef G_OS_UNIX
#include <sys/un.h>
#endif

void slirp_insque(void *a, void *b)
{
    register struct slirp_quehead *element = (struct slirp_quehead *)a;
    register struct slirp_quehead *head = (struct slirp_quehead *)b;
    element->qh_link = head->qh_link;
    head->qh_link = (struct slirp_quehead *)element;
    element->qh_rlink = (struct slirp_quehead *)head;
    ((struct slirp_quehead *)(element->qh_link))->qh_rlink =
        (struct slirp_quehead *)element;
}

void slirp_remque(void *a)
{
    register struct slirp_quehead *element = (struct slirp_quehead *)a;
    ((struct slirp_quehead *)(element->qh_link))->qh_rlink = element->qh_rlink;
    ((struct slirp_quehead *)(element->qh_rlink))->qh_link = element->qh_link;
    element->qh_rlink = NULL;
}

/* TODO: IPv6 */
struct gfwd_list *add_guestfwd(struct gfwd_list **ex_ptr, SlirpWriteCb write_cb,
                               void *opaque, struct in_addr addr, int port)
{
    struct gfwd_list *f = g_new0(struct gfwd_list, 1);

    f->write_cb = write_cb;
    f->opaque = opaque;
    f->ex_fport = port;
    f->ex_addr = addr;
    f->ex_next = *ex_ptr;
    *ex_ptr = f;

    return f;
}

struct gfwd_list *add_exec(struct gfwd_list **ex_ptr, const char *cmdline,
                           struct in_addr addr, int port)
{
    struct gfwd_list *f = add_guestfwd(ex_ptr, NULL, NULL, addr, port);

    f->ex_exec = g_strdup(cmdline);

    return f;
}

struct gfwd_list *add_unix(struct gfwd_list **ex_ptr, const char *unixsock,
                           struct in_addr addr, int port)
{
    struct gfwd_list *f = add_guestfwd(ex_ptr, NULL, NULL, addr, port);

    f->ex_unix = g_strdup(unixsock);

    return f;
}

int remove_guestfwd(struct gfwd_list **ex_ptr, struct in_addr addr, int port)
{
    for (; *ex_ptr != NULL; ex_ptr = &((*ex_ptr)->ex_next)) {
        struct gfwd_list *f = *ex_ptr;
        if (f->ex_addr.s_addr == addr.s_addr && f->ex_fport == port) {
            *ex_ptr = f->ex_next;
            g_free(f->ex_exec);
            g_free(f);
            return 0;
        }
    }
    return -1;
}

static int slirp_socketpair_with_oob(int sv[2])
{
    struct sockaddr_in addr = {
        .sin_family = AF_INET,
        .sin_port = 0,
        .sin_addr.s_addr = htonl(INADDR_LOOPBACK),
    };
    socklen_t addrlen = sizeof(addr);
    int ret, s;

    sv[1] = -1;
    s = slirp_socket(AF_INET, SOCK_STREAM, 0);
    if (s < 0 || bind(s, (struct sockaddr *)&addr, addrlen) < 0 ||
        listen(s, 1) < 0 ||
        getsockname(s, (struct sockaddr *)&addr, &addrlen) < 0) {
        goto err;
    }

    sv[1] = slirp_socket(AF_INET, SOCK_STREAM, 0);
    if (sv[1] < 0) {
        goto err;
    }
    /*
     * This connect won't block because we've already listen()ed on
     * the server end (even though we won't accept() the connection
     * until later on).
     */
    do {
        ret = connect(sv[1], (struct sockaddr *)&addr, addrlen);
    } while (ret < 0 && errno == EINTR);
    if (ret < 0) {
        goto err;
    }

    do {
        sv[0] = accept(s, (struct sockaddr *)&addr, &addrlen);
    } while (sv[0] < 0 && errno == EINTR);
    if (sv[0] < 0) {
        goto err;
    }

    closesocket(s);
    return 0;

err:
    g_critical("slirp_socketpair(): %s", strerror(errno));
    if (s >= 0) {
        closesocket(s);
    }
    if (sv[1] >= 0) {
        closesocket(sv[1]);
    }
    return -1;
}

static void fork_exec_child_setup(gpointer data)
{
#ifndef _WIN32
    setsid();

    /* Unblock all signals and leave our exec()-ee to block what it wants */
    sigset_t ss;
    sigemptyset(&ss);
    sigprocmask(SIG_SETMASK, &ss, NULL);

    /* POSIX is obnoxious about SIGCHLD specifically across exec() */
    signal(SIGCHLD, SIG_DFL);
#endif
}

#ifdef __GNUC__
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wdeprecated-declarations"
#endif

#if !GLIB_CHECK_VERSION(2, 58, 0)
typedef struct SlirpGSpawnFds {
    GSpawnChildSetupFunc child_setup;
    gpointer user_data;
    gint stdin_fd;
    gint stdout_fd;
    gint stderr_fd;
} SlirpGSpawnFds;

static inline void slirp_gspawn_fds_setup(gpointer user_data)
{
    SlirpGSpawnFds *q = (SlirpGSpawnFds *)user_data;

    dup2(q->stdin_fd, 0);
    dup2(q->stdout_fd, 1);
    dup2(q->stderr_fd, 2);
    q->child_setup(q->user_data);
}
#endif

static inline gboolean
g_spawn_async_with_fds_slirp(const gchar *working_directory, gchar **argv,
                             gchar **envp, GSpawnFlags flags,
                             GSpawnChildSetupFunc child_setup,
                             gpointer user_data, GPid *child_pid, gint stdin_fd,
                             gint stdout_fd, gint stderr_fd, GError **error)
{
#if GLIB_CHECK_VERSION(2, 58, 0)
    return g_spawn_async_with_fds(working_directory, argv, envp, flags,
                                  child_setup, user_data, child_pid, stdin_fd,
                                  stdout_fd, stderr_fd, error);
#else
    SlirpGSpawnFds setup = {
        .child_setup = child_setup,
        .user_data = user_data,
        .stdin_fd = stdin_fd,
        .stdout_fd = stdout_fd,
        .stderr_fd = stderr_fd,
    };

    return g_spawn_async(working_directory, argv, envp, flags,
                         slirp_gspawn_fds_setup, &setup, child_pid, error);
#endif
}

#define g_spawn_async_with_fds(wd, argv, env, f, c, d, p, ifd, ofd, efd, err) \
    g_spawn_async_with_fds_slirp(wd, argv, env, f, c, d, p, ifd, ofd, efd, err)

#ifdef __GNUC__
#pragma GCC diagnostic pop
#endif

int fork_exec(struct socket *so, const char *ex)
{
    GError *err = NULL;
    gint argc = 0;
    gchar **argv = NULL;
    int opt, sp[2];

    DEBUG_CALL("fork_exec");
    DEBUG_ARG("so = %p", so);
    DEBUG_ARG("ex = %p", ex);

    if (slirp_socketpair_with_oob(sp) < 0) {
        return 0;
    }

    if (!g_shell_parse_argv(ex, &argc, &argv, &err)) {
        g_critical("fork_exec invalid command: %s\nerror: %s", ex, err->message);
        g_error_free(err);
        return 0;
    }

    g_spawn_async_with_fds(NULL /* cwd */, argv, NULL /* env */,
                           G_SPAWN_SEARCH_PATH, fork_exec_child_setup,
                           NULL /* data */, NULL /* child_pid */, sp[1], sp[1],
                           sp[1], &err);
    g_strfreev(argv);

    if (err) {
        g_critical("fork_exec: %s", err->message);
        g_error_free(err);
        closesocket(sp[0]);
        closesocket(sp[1]);
        return 0;
    }

    so->s = sp[0];
    closesocket(sp[1]);
    slirp_socket_set_fast_reuse(so->s);
    opt = 1;
    setsockopt(so->s, SOL_SOCKET, SO_OOBINLINE, &opt, sizeof(int));
    slirp_set_nonblock(so->s);
    so->slirp->cb->register_poll_fd(so->s, so->slirp->opaque);
    return 1;
}

int open_unix(struct socket *so, const char *unixpath)
{
#ifdef G_OS_UNIX
    struct sockaddr_un sa;
    int s;

    DEBUG_CALL("open_unix");
    DEBUG_ARG("so = %p", so);
    DEBUG_ARG("unixpath = %s", unixpath);

    memset(&sa, 0, sizeof(sa));
    sa.sun_family = AF_UNIX;
    if (g_strlcpy(sa.sun_path, unixpath, sizeof(sa.sun_path)) >= sizeof(sa.sun_path)) {
        g_critical("Bad unix path: %s", unixpath);
        return 0;
    }

    s = slirp_socket(PF_UNIX, SOCK_STREAM, 0);
    if (s < 0) {
        g_critical("open_unix(): %s", strerror(errno));
        return 0;
    }

    if (connect(s, (struct sockaddr *)&sa, sizeof(sa)) < 0) {
        g_critical("open_unix(): %s", strerror(errno));
        closesocket(s);
        return 0;
    }

    so->s = s;
    slirp_set_nonblock(so->s);
    so->slirp->cb->register_poll_fd(so->s, so->slirp->opaque);

    return 1;
#else
    g_assert_not_reached();
#endif
}

char *slirp_connection_info(Slirp *slirp)
{
    GString *str = g_string_new(NULL);
    const char *const tcpstates[] = {
        [TCPS_CLOSED] = "CLOSED",           [TCPS_LISTEN] = "LISTEN",
        [TCPS_SYN_SENT] = "SYN_SENT",       [TCPS_SYN_RECEIVED] = "SYN_RCVD",
        [TCPS_ESTABLISHED] = "ESTABLISHED", [TCPS_CLOSE_WAIT] = "CLOSE_WAIT",
        [TCPS_FIN_WAIT_1] = "FIN_WAIT_1",   [TCPS_CLOSING] = "CLOSING",
        [TCPS_LAST_ACK] = "LAST_ACK",       [TCPS_FIN_WAIT_2] = "FIN_WAIT_2",
        [TCPS_TIME_WAIT] = "TIME_WAIT",
    };
    struct in_addr dst_addr;
    struct sockaddr_in src;
    socklen_t src_len;
    uint16_t dst_port;
    struct socket *so;
    const char *state;
    char addr[INET_ADDRSTRLEN];
    char buf[20];

    g_string_append_printf(str,
                           "  Protocol[State]    FD  Source Address  Port   "
                           "Dest. Address  Port RecvQ SendQ\n");

    /* TODO: IPv6 */

    for (so = slirp->tcb.so_next; so != &slirp->tcb; so = so->so_next) {
        if (so->so_state & SS_HOSTFWD) {
            state = "HOST_FORWARD";
        } else if (so->so_tcpcb) {
            state = tcpstates[so->so_tcpcb->t_state];
        } else {
            state = "NONE";
        }
        if (so->so_state & (SS_HOSTFWD | SS_INCOMING)) {
            src_len = sizeof(src);
            getsockname(so->s, (struct sockaddr *)&src, &src_len);
            dst_addr = so->so_laddr;
            dst_port = so->so_lport;
        } else {
            src.sin_addr = so->so_laddr;
            src.sin_port = so->so_lport;
            dst_addr = so->so_faddr;
            dst_port = so->so_fport;
        }
        slirp_fmt0(buf, sizeof(buf), "  TCP[%s]", state);
        g_string_append_printf(str, "%-19s %3d %15s %5d ", buf, so->s,
                               src.sin_addr.s_addr ?
                               inet_ntop(AF_INET, &src.sin_addr, addr, sizeof(addr)) : "*",
                               ntohs(src.sin_port));
        g_string_append_printf(str, "%15s %5d %5d %5d\n",
                               inet_ntop(AF_INET, &dst_addr, addr, sizeof(addr)),
                               ntohs(dst_port), so->so_rcv.sb_cc,
                               so->so_snd.sb_cc);
    }

    for (so = slirp->udb.so_next; so != &slirp->udb; so = so->so_next) {
        if (so->so_state & SS_HOSTFWD) {
            slirp_fmt0(buf, sizeof(buf), "  UDP[HOST_FORWARD]");
            src_len = sizeof(src);
            getsockname(so->s, (struct sockaddr *)&src, &src_len);
            dst_addr = so->so_laddr;
            dst_port = so->so_lport;
        } else {
            slirp_fmt0(buf, sizeof(buf), "  UDP[%d sec]",
                       (so->so_expire - curtime) / 1000);
            src.sin_addr = so->so_laddr;
            src.sin_port = so->so_lport;
            dst_addr = so->so_faddr;
            dst_port = so->so_fport;
        }
        g_string_append_printf(str, "%-19s %3d %15s %5d ", buf, so->s,
                               src.sin_addr.s_addr ?
                               inet_ntop(AF_INET, &src.sin_addr, addr, sizeof(addr)) : "*",
                               ntohs(src.sin_port));
        g_string_append_printf(str, "%15s %5d %5d %5d\n",
                               inet_ntop(AF_INET, &dst_addr, addr, sizeof(addr)),
                               ntohs(dst_port), so->so_rcv.sb_cc,
                               so->so_snd.sb_cc);
    }

    for (so = slirp->icmp.so_next; so != &slirp->icmp; so = so->so_next) {
        slirp_fmt0(buf, sizeof(buf), "  ICMP[%d sec]",
                   (so->so_expire - curtime) / 1000);
        src.sin_addr = so->so_laddr;
        dst_addr = so->so_faddr;
        g_string_append_printf(str, "%-19s %3d %15s  -    ", buf, so->s,
                               src.sin_addr.s_addr ?
                               inet_ntop(AF_INET, &src.sin_addr, addr, sizeof(addr)) : "*");
        g_string_append_printf(str, "%15s  -    %5d %5d\n",
                               inet_ntop(AF_INET, &dst_addr, addr, sizeof(addr)),
                               so->so_rcv.sb_cc, so->so_snd.sb_cc);
    }

    return g_string_free(str, FALSE);
}

char *slirp_neighbor_info(Slirp *slirp)
{
    GString *str = g_string_new(NULL);
    ArpTable *arp_table = &slirp->arp_table;
    NdpTable *ndp_table = &slirp->ndp_table;
    char ip_addr[INET6_ADDRSTRLEN];
    char eth_addr[ETH_ADDRSTRLEN];
    const char *ip;

    g_string_append_printf(str, "  %5s  %-17s  %s\n",
                           "Table", "MacAddr", "IP Address");

    for (int i = 0; i < ARP_TABLE_SIZE; ++i) {
        struct in_addr addr;
        addr.s_addr = arp_table->table[i].ar_sip;
        if (!addr.s_addr) {
            continue;
        }
        ip = inet_ntop(AF_INET, &addr, ip_addr, sizeof(ip_addr));
        g_assert(ip != NULL);
        g_string_append_printf(str, "  %5s  %-17s  %s\n", "ARP",
                               slirp_ether_ntoa(arp_table->table[i].ar_sha,
                                                eth_addr, sizeof(eth_addr)),
                               ip);
    }

    for (int i = 0; i < NDP_TABLE_SIZE; ++i) {
        if (in6_zero(&ndp_table->table[i].ip_addr)) {
            continue;
        }
        ip = inet_ntop(AF_INET6, &ndp_table->table[i].ip_addr, ip_addr,
                       sizeof(ip_addr));
        g_assert(ip != NULL);
        g_string_append_printf(str, "  %5s  %-17s  %s\n", "NDP",
                               slirp_ether_ntoa(ndp_table->table[i].eth_addr,
                                                eth_addr, sizeof(eth_addr)),
                               ip);
    }

    return g_string_free(str, FALSE);
}

int slirp_bind_outbound(struct socket *so, unsigned short af)
{
    int ret = 0;
    struct sockaddr *addr = NULL;
    int addr_size = 0;

    if (af == AF_INET && so->slirp->outbound_addr != NULL) {
        addr = (struct sockaddr *)so->slirp->outbound_addr;
        addr_size = sizeof(struct sockaddr_in);
    } else if (af == AF_INET6 && so->slirp->outbound_addr6 != NULL) {
        addr = (struct sockaddr *)so->slirp->outbound_addr6;
        addr_size = sizeof(struct sockaddr_in6);
    }

    if (addr != NULL) {
        ret = bind(so->s, addr, addr_size);
    }
    return ret;
}
