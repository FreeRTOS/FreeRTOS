/*
 * Copyright (c) 2001-2004 Swedish Institute of Computer Science.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT
 * SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
 * OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
 * OF SUCH DAMAGE.
 *
 * This file is part of the lwIP TCP/IP stack.
 *
 * Author: Adam Dunkels <adam@sics.se>
 *
 * Improved by Marc Boucher <marc@mbsi.ca> and David Haas <dhaas@alum.rpi.edu>
 *
 */

#include <string.h>
#include <errno.h>

#include "lwip/opt.h"
#include "lwip/api.h"
#include "lwip/arch.h"
#include "lwip/sys.h"

#include "lwip/sockets.h"

#define NUM_SOCKETS MEMP_NUM_NETCONN

struct lwip_socket {
  struct netconn *conn;
  struct netbuf *lastdata;
  u16_t lastoffset;
  u16_t rcvevent;
  u16_t sendevent;
  u16_t  flags;
  int err;
};

struct lwip_select_cb
{
    struct lwip_select_cb *next;
    fd_set *readset;
    fd_set *writeset;
    fd_set *exceptset;
    int sem_signalled;
    sys_sem_t sem;
};

static struct lwip_socket sockets[NUM_SOCKETS];
static struct lwip_select_cb *select_cb_list = 0;

static sys_sem_t socksem = 0;
static sys_sem_t selectsem = 0;

static void
event_callback(struct netconn *conn, enum netconn_evt evt, u16_t len);

static int err_to_errno_table[11] = {
    0,      /* ERR_OK    0      No error, everything OK. */
    ENOMEM,    /* ERR_MEM  -1      Out of memory error.     */
    ENOBUFS,    /* ERR_BUF  -2      Buffer error.            */
    ECONNABORTED,  /* ERR_ABRT -3      Connection aborted.      */
    ECONNRESET,    /* ERR_RST  -4      Connection reset.        */
    ESHUTDOWN,    /* ERR_CLSD -5      Connection closed.       */
    ENOTCONN,    /* ERR_CONN -6      Not connected.           */
    EINVAL,    /* ERR_VAL  -7      Illegal value.           */
    EIO,    /* ERR_ARG  -8      Illegal argument.        */
    EHOSTUNREACH,  /* ERR_RTE  -9      Routing problem.         */
    EADDRINUSE    /* ERR_USE  -10     Address in use.          */
};

#define err_to_errno(err) \
  ((err) < (sizeof(err_to_errno_table)/sizeof(int))) ? \
    err_to_errno_table[-(err)] : EIO

#ifdef ERRNO
#define set_errno(err) errno = (err)
#else
#define set_errno(err)
#endif

#define sock_set_errno(sk, e) do { \
      sk->err = (e); \
      set_errno(sk->err); \
} while (0)


static struct lwip_socket *
get_socket(int s)
{
  struct lwip_socket *sock;

  if ((s < 0) || (s > NUM_SOCKETS)) {
    LWIP_DEBUGF(SOCKETS_DEBUG, ("get_socket(%d): invalid\n", s));
    set_errno(EBADF);
    return NULL;
  }

  sock = &sockets[s];

  if (!sock->conn) {
    LWIP_DEBUGF(SOCKETS_DEBUG, ("get_socket(%d): not active\n", s));
    set_errno(EBADF);
    return NULL;
  }

  return sock;
}

static int
alloc_socket(struct netconn *newconn)
{
  int i;

  if (!socksem)
      socksem = sys_sem_new(1);

  /* Protect socket array */
  sys_sem_wait(socksem);

  /* allocate a new socket identifier */
  for(i = 0; i < NUM_SOCKETS; ++i) {
    if (!sockets[i].conn) {
      sockets[i].conn = newconn;
      sockets[i].lastdata = NULL;
      sockets[i].lastoffset = 0;
      sockets[i].rcvevent = 0;
      sockets[i].sendevent = 1; /* TCP send buf is empty */
      sockets[i].flags = 0;
      sockets[i].err = 0;
      sys_sem_signal(socksem);
      return i;
    }
  }
  sys_sem_signal(socksem);
  return -1;
}

int
lwip_accept(int s, struct sockaddr *addr, socklen_t *addrlen)
{
  struct lwip_socket *sock;
  struct netconn *newconn;
  struct ip_addr naddr;
  u16_t port;
  int newsock;
  struct sockaddr_in sin;

  LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_accept(%d)...\n", s));
  sock = get_socket(s);
  if (!sock) {
    set_errno(EBADF);
    return -1;
  }

  newconn = netconn_accept(sock->conn);

  /* get the IP address and port of the remote host */
  netconn_peer(newconn, &naddr, &port);

  memset(&sin, 0, sizeof(sin));
  sin.sin_len = sizeof(sin);
  sin.sin_family = AF_INET;
  sin.sin_port = htons(port);
  sin.sin_addr.s_addr = naddr.addr;

  if (*addrlen > sizeof(sin))
      *addrlen = sizeof(sin);

  memcpy(addr, &sin, *addrlen);

  newsock = alloc_socket(newconn);
  if (newsock == -1) {
    netconn_delete(newconn);
  sock_set_errno(sock, ENOBUFS);
  return -1;
  }
  newconn->callback = event_callback;
  sock = get_socket(newsock);

  sys_sem_wait(socksem);
  sock->rcvevent += -1 - newconn->socket;
  newconn->socket = newsock;
  sys_sem_signal(socksem);

  LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_accept(%d) returning new sock=%d addr=", s, newsock));
  ip_addr_debug_print(SOCKETS_DEBUG, &naddr);
  LWIP_DEBUGF(SOCKETS_DEBUG, (" port=%u\n", port));

  sock_set_errno(sock, 0);
  return newsock;
}

int
lwip_bind(int s, struct sockaddr *name, socklen_t namelen)
{
  struct lwip_socket *sock;
  struct ip_addr local_addr;
  u16_t local_port;
  err_t err;

  sock = get_socket(s);
  if (!sock) {
    set_errno(EBADF);
    return -1;
  }

  local_addr.addr = ((struct sockaddr_in *)name)->sin_addr.s_addr;
  local_port = ((struct sockaddr_in *)name)->sin_port;

  LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_bind(%d, addr=", s));
  ip_addr_debug_print(SOCKETS_DEBUG, &local_addr);
  LWIP_DEBUGF(SOCKETS_DEBUG, (" port=%u)\n", ntohs(local_port)));

  err = netconn_bind(sock->conn, &local_addr, ntohs(local_port));

  if (err != ERR_OK) {
    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_bind(%d) failed, err=%d\n", s, err));
    sock_set_errno(sock, err_to_errno(err));
    return -1;
  }

  LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_bind(%d) succeeded\n", s));
  sock_set_errno(sock, 0);
  return 0;
}

int
lwip_close(int s)
{
  struct lwip_socket *sock;

  LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_close(%d)\n", s));
  if (!socksem)
      socksem = sys_sem_new(1);

  /* We cannot allow multiple closes of the same socket. */
  sys_sem_wait(socksem);

  sock = get_socket(s);
  if (!sock) {
      sys_sem_signal(socksem);
      set_errno(EBADF);
      return -1;
  }

  netconn_delete(sock->conn);
  if (sock->lastdata) {
    netbuf_delete(sock->lastdata);
  }
  sock->lastdata = NULL;
  sock->lastoffset = 0;
  sock->conn = NULL;
  sys_sem_signal(socksem);
  sock_set_errno(sock, 0);
  return 0;
}

int
lwip_connect(int s, struct sockaddr *name, socklen_t namelen)
{
  struct lwip_socket *sock;
  err_t err;

  sock = get_socket(s);
  if (!sock) {
    set_errno(EBADF);
    return -1;
  }

  if (((struct sockaddr_in *)name)->sin_family == AF_UNSPEC) {
    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_connect(%d, AF_UNSPEC)\n", s));
    err = netconn_disconnect(sock->conn);
  } else {
    struct ip_addr remote_addr;
    u16_t remote_port;

    remote_addr.addr = ((struct sockaddr_in *)name)->sin_addr.s_addr;
    remote_port = ((struct sockaddr_in *)name)->sin_port;

    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_connect(%d, addr=", s));
    ip_addr_debug_print(SOCKETS_DEBUG, &remote_addr);
    LWIP_DEBUGF(SOCKETS_DEBUG, (" port=%u)\n", ntohs(remote_port)));

    err = netconn_connect(sock->conn, &remote_addr, ntohs(remote_port));
   }

  if (err != ERR_OK) {
    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_connect(%d) failed, err=%d\n", s, err));
    sock_set_errno(sock, err_to_errno(err));
    return -1;
  }

  LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_connect(%d) succeeded\n", s));
  sock_set_errno(sock, 0);
  return 0;
}

int
lwip_listen(int s, int backlog)
{
  struct lwip_socket *sock;
  err_t err;

  LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_listen(%d, backlog=%d)\n", s, backlog));
  sock = get_socket(s);
  if (!sock) {
    set_errno(EBADF);
    return -1;
  }

  err = netconn_listen(sock->conn);

  if (err != ERR_OK) {
    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_listen(%d) failed, err=%d\n", s, err));
    sock_set_errno(sock, err_to_errno(err));
    return -1;
  }

  sock_set_errno(sock, 0);
  return 0;
}

int
lwip_recvfrom(int s, void *mem, int len, unsigned int flags,
        struct sockaddr *from, socklen_t *fromlen)
{
  struct lwip_socket *sock;
  struct netbuf *buf;
  u16_t buflen, copylen;
  struct ip_addr *addr;
  u16_t port;


  LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_recvfrom(%d, %p, %d, 0x%x, ..)\n", s, mem, len, flags));
  sock = get_socket(s);
  if (!sock) {
    set_errno(EBADF);
    return -1;
  }

  /* Check if there is data left from the last recv operation. */
  if (sock->lastdata) {
    buf = sock->lastdata;
  } else {
    /* If this is non-blocking call, then check first */
    if (((flags & MSG_DONTWAIT) || (sock->flags & O_NONBLOCK))
  && !sock->rcvevent)
    {
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_recvfrom(%d): returning EWOULDBLOCK\n", s));
      sock_set_errno(sock, EWOULDBLOCK);
      return -1;
    }

    /* No data was left from the previous operation, so we try to get
       some from the network. */
    buf = netconn_recv(sock->conn);

    if (!buf) {
      /* We should really do some error checking here. */
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_recvfrom(%d): buf == NULL!\n", s));
      sock_set_errno(sock, 0);
      return 0;
    }
  }

  buflen = netbuf_len(buf);

  buflen -= sock->lastoffset;

  if (len > buflen) {
    copylen = buflen;
  } else {
    copylen = len;
  }

  /* copy the contents of the received buffer into
     the supplied memory pointer mem */
  netbuf_copy_partial(buf, mem, copylen, sock->lastoffset);

  /* Check to see from where the data was. */
  if (from && fromlen) {
    struct sockaddr_in sin;

    addr = netbuf_fromaddr(buf);
    port = netbuf_fromport(buf);

    memset(&sin, 0, sizeof(sin));
    sin.sin_len = sizeof(sin);
    sin.sin_family = AF_INET;
    sin.sin_port = htons(port);
    sin.sin_addr.s_addr = addr->addr;

    if (*fromlen > sizeof(sin))
      *fromlen = sizeof(sin);

    memcpy(from, &sin, *fromlen);

    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_recvfrom(%d): addr=", s));
    ip_addr_debug_print(SOCKETS_DEBUG, addr);
    LWIP_DEBUGF(SOCKETS_DEBUG, (" port=%u len=%u\n", port, copylen));
  } else {
#if SOCKETS_DEBUG
    addr = netbuf_fromaddr(buf);
    port = netbuf_fromport(buf);

    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_recvfrom(%d): addr=", s));
    ip_addr_debug_print(SOCKETS_DEBUG, addr);
    LWIP_DEBUGF(SOCKETS_DEBUG, (" port=%u len=%u\n", port, copylen));
#endif

  }

  /* If this is a TCP socket, check if there is data left in the
     buffer. If so, it should be saved in the sock structure for next
     time around. */
  if (netconn_type(sock->conn) == NETCONN_TCP && buflen - copylen > 0) {
    sock->lastdata = buf;
    sock->lastoffset += copylen;
  } else {
    sock->lastdata = NULL;
    sock->lastoffset = 0;
    netbuf_delete(buf);
  }


  sock_set_errno(sock, 0);
  return copylen;
}

int
lwip_read(int s, void *mem, int len)
{
  return lwip_recvfrom(s, mem, len, 0, NULL, NULL);
}

int
lwip_recv(int s, void *mem, int len, unsigned int flags)
{
  return lwip_recvfrom(s, mem, len, flags, NULL, NULL);
}

int
lwip_send(int s, void *data, int size, unsigned int flags)
{
  struct lwip_socket *sock;
  struct netbuf *buf;
  err_t err;

  LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_send(%d, data=%p, size=%d, flags=0x%x)\n", s, data, size, flags));

  sock = get_socket(s);
  if (!sock) {
    set_errno(EBADF);
    return -1;
  }

  switch (netconn_type(sock->conn)) {
  case NETCONN_RAW:
  case NETCONN_UDP:
  case NETCONN_UDPLITE:
  case NETCONN_UDPNOCHKSUM:
    /* create a buffer */
    buf = netbuf_new();

    if (!buf) {
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_send(%d) ENOBUFS\n", s));
      sock_set_errno(sock, ENOBUFS);
      return -1;
    }

    /* make the buffer point to the data that should
       be sent */
    netbuf_ref(buf, data, size);

    /* send the data */
    err = netconn_send(sock->conn, buf);

    /* deallocated the buffer */
    netbuf_delete(buf);
    break;
  case NETCONN_TCP:
    err = netconn_write(sock->conn, data, size, NETCONN_COPY);
    break;
  default:
    err = ERR_ARG;
    break;
  }
  if (err != ERR_OK) {
    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_send(%d) err=%d\n", s, err));
    sock_set_errno(sock, err_to_errno(err));
    return -1;
  }

  LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_send(%d) ok size=%d\n", s, size));
  sock_set_errno(sock, 0);
  return size;
}

int
lwip_sendto(int s, void *data, int size, unsigned int flags,
       struct sockaddr *to, socklen_t tolen)
{
  struct lwip_socket *sock;
  struct ip_addr remote_addr, addr;
  u16_t remote_port, port;
  int ret,connected;

  sock = get_socket(s);
  if (!sock) {
    set_errno(EBADF);
    return -1;
  }

  /* get the peer if currently connected */
  connected = (netconn_peer(sock->conn, &addr, &port) == ERR_OK);

  remote_addr.addr = ((struct sockaddr_in *)to)->sin_addr.s_addr;
  remote_port = ((struct sockaddr_in *)to)->sin_port;

  LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_sendto(%d, data=%p, size=%d, flags=0x%x to=", s, data, size, flags));
  ip_addr_debug_print(SOCKETS_DEBUG, &remote_addr);
  LWIP_DEBUGF(SOCKETS_DEBUG, (" port=%u\n", ntohs(remote_port)));

  netconn_connect(sock->conn, &remote_addr, ntohs(remote_port));

  ret = lwip_send(s, data, size, flags);

  /* reset the remote address and port number
     of the connection */
  if (connected)
    netconn_connect(sock->conn, &addr, port);
  else
  netconn_disconnect(sock->conn);
  return ret;
}

int
lwip_socket(int domain, int type, int protocol)
{
  struct netconn *conn;
  int i;

  /* create a netconn */
  switch (type) {
  case SOCK_RAW:
    conn = netconn_new_with_proto_and_callback(NETCONN_RAW, protocol, event_callback);
    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_socket(%s, SOCK_RAW, %d) = ", domain == PF_INET ? "PF_INET" : "UNKNOWN", protocol));
    break;
  case SOCK_DGRAM:
    conn = netconn_new_with_callback(NETCONN_UDP, event_callback);
    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_socket(%s, SOCK_DGRAM, %d) = ", domain == PF_INET ? "PF_INET" : "UNKNOWN", protocol));
    break;
  case SOCK_STREAM:
    conn = netconn_new_with_callback(NETCONN_TCP, event_callback);
    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_socket(%s, SOCK_STREAM, %d) = ", domain == PF_INET ? "PF_INET" : "UNKNOWN", protocol));
    break;
  default:
    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_socket(%d, %d/UNKNOWN, %d) = -1\n", domain, type, protocol));
    set_errno(EINVAL);
    return -1;
  }

  if (!conn) {
    LWIP_DEBUGF(SOCKETS_DEBUG, ("-1 / ENOBUFS (could not create netconn)\n"));
    set_errno(ENOBUFS);
    return -1;
  }

  i = alloc_socket(conn);

  if (i == -1) {
    netconn_delete(conn);
  set_errno(ENOBUFS);
  return -1;
  }
  conn->socket = i;
  LWIP_DEBUGF(SOCKETS_DEBUG, ("%d\n", i));
  set_errno(0);
  return i;
}

int
lwip_write(int s, void *data, int size)
{
   return lwip_send(s, data, size, 0);
}


static int
lwip_selscan(int maxfdp1, fd_set *readset, fd_set *writeset, fd_set *exceptset)
{
    int i, nready = 0;
    fd_set lreadset, lwriteset, lexceptset;
    struct lwip_socket *p_sock;

    FD_ZERO(&lreadset);
    FD_ZERO(&lwriteset);
    FD_ZERO(&lexceptset);

    /* Go through each socket in each list to count number of sockets which
       currently match */
    for(i = 0; i < maxfdp1; i++)
    {
        if (FD_ISSET(i, readset))
        {
            /* See if netconn of this socket is ready for read */
            p_sock = get_socket(i);
            if (p_sock && (p_sock->lastdata || p_sock->rcvevent))
            {
                FD_SET(i, &lreadset);
		LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_selscan: fd=%d ready for reading\n", i));
                nready++;
            }
        }
        if (FD_ISSET(i, writeset))
        {
            /* See if netconn of this socket is ready for write */
            p_sock = get_socket(i);
            if (p_sock && p_sock->sendevent)
            {
                FD_SET(i, &lwriteset);
		LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_selscan: fd=%d ready for writing\n", i));
                nready++;
            }
        }
    }
    *readset = lreadset;
    *writeset = lwriteset;
    FD_ZERO(exceptset);

    return nready;
}



int
lwip_select(int maxfdp1, fd_set *readset, fd_set *writeset, fd_set *exceptset,
               struct timeval *timeout)
{
    int i;
    int nready;
    fd_set lreadset, lwriteset, lexceptset;
    u32_t msectimeout;
    struct lwip_select_cb select_cb;
    struct lwip_select_cb *p_selcb;

    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_select(%d, %p, %p, %p, tvsec=%ld tvusec=%ld)\n", maxfdp1, (void *)readset, (void *) writeset, (void *) exceptset, timeout ? timeout->tv_sec : -1L, timeout ? timeout->tv_usec : -1L));

    select_cb.next = 0;
    select_cb.readset = readset;
    select_cb.writeset = writeset;
    select_cb.exceptset = exceptset;
    select_cb.sem_signalled = 0;

    /* Protect ourselves searching through the list */
    if (!selectsem)
        selectsem = sys_sem_new(1);
    sys_sem_wait(selectsem);

    if (readset)
        lreadset = *readset;
    else
        FD_ZERO(&lreadset);
    if (writeset)
        lwriteset = *writeset;
    else
        FD_ZERO(&lwriteset);
    if (exceptset)
        lexceptset = *exceptset;
    else
        FD_ZERO(&lexceptset);

    /* Go through each socket in each list to count number of sockets which
       currently match */
    nready = lwip_selscan(maxfdp1, &lreadset, &lwriteset, &lexceptset);

    /* If we don't have any current events, then suspend if we are supposed to */
    if (!nready)
    {
        if (timeout && timeout->tv_sec == 0 && timeout->tv_usec == 0)
        {
            sys_sem_signal(selectsem);
            if (readset)
                FD_ZERO(readset);
            if (writeset)
                FD_ZERO(writeset);
            if (exceptset)
                FD_ZERO(exceptset);

	    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_select: no timeout, returning 0\n"));
	    set_errno(0);

            return 0;
        }

        /* add our semaphore to list */
        /* We don't actually need any dynamic memory. Our entry on the
         * list is only valid while we are in this function, so it's ok
         * to use local variables */

        select_cb.sem = sys_sem_new(0);
        /* Note that we are still protected */
        /* Put this select_cb on top of list */
        select_cb.next = select_cb_list;
        select_cb_list = &select_cb;

        /* Now we can safely unprotect */
        sys_sem_signal(selectsem);

        /* Now just wait to be woken */
        if (timeout == 0)
            /* Wait forever */
            msectimeout = 0;
        else
            msectimeout =  ((timeout->tv_sec * 1000) + ((timeout->tv_usec + 500)/1000));

        i = sys_sem_wait_timeout(select_cb.sem, msectimeout);

        /* Take us off the list */
        sys_sem_wait(selectsem);
        if (select_cb_list == &select_cb)
            select_cb_list = select_cb.next;
        else
            for (p_selcb = select_cb_list; p_selcb; p_selcb = p_selcb->next)
                if (p_selcb->next == &select_cb)
                {
                    p_selcb->next = select_cb.next;
                    break;
                }

        sys_sem_signal(selectsem);

        sys_sem_free(select_cb.sem);
        if (i == 0)             /* Timeout */
        {
            if (readset)
                FD_ZERO(readset);
            if (writeset)
                FD_ZERO(writeset);
            if (exceptset)
                FD_ZERO(exceptset);

	    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_select: timeout expired\n"));
	    set_errno(0);

            return 0;
        }

        if (readset)
            lreadset = *readset;
        else
            FD_ZERO(&lreadset);
        if (writeset)
            lwriteset = *writeset;
        else
            FD_ZERO(&lwriteset);
        if (exceptset)
            lexceptset = *exceptset;
        else
            FD_ZERO(&lexceptset);

        /* See what's set */
        nready = lwip_selscan(maxfdp1, &lreadset, &lwriteset, &lexceptset);
    }
    else
        sys_sem_signal(selectsem);

    if (readset)
        *readset = lreadset;
    if (writeset)
        *writeset = lwriteset;
    if (exceptset)
        *exceptset = lexceptset;

    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_select: nready=%d\n", nready));
    set_errno(0);

    return nready;
}


static void
event_callback(struct netconn *conn, enum netconn_evt evt, u16_t len)
{
    int s;
    struct lwip_socket *sock;
    struct lwip_select_cb *scb;

    /* Get socket */
    if (conn)
    {
        s = conn->socket;
        if (s < 0)
        {
            /* Data comes in right away after an accept, even though
             * the server task might not have created a new socket yet.
             * Just count down (or up) if that's the case and we
             * will use the data later. Note that only receive events
             * can happen before the new socket is set up. */
            if (evt == NETCONN_EVT_RCVPLUS)
                conn->socket--;
            return;
        }

        sock = get_socket(s);
        if (!sock)
            return;
    }
    else
        return;

    if (!selectsem)
        selectsem = sys_sem_new(1);

    sys_sem_wait(selectsem);
    /* Set event as required */
    switch (evt)
    {
      case NETCONN_EVT_RCVPLUS:
        sock->rcvevent++;
        break;
      case NETCONN_EVT_RCVMINUS:
        sock->rcvevent--;
        break;
      case NETCONN_EVT_SENDPLUS:
        sock->sendevent = 1;
        break;
      case NETCONN_EVT_SENDMINUS:
        sock->sendevent = 0;
        break;
    }
    sys_sem_signal(selectsem);

    /* Now decide if anyone is waiting for this socket */
    /* NOTE: This code is written this way to protect the select link list
       but to avoid a deadlock situation by releasing socksem before
       signalling for the select. This means we need to go through the list
       multiple times ONLY IF a select was actually waiting. We go through
       the list the number of waiting select calls + 1. This list is
       expected to be small. */
    while (1)
    {
        sys_sem_wait(selectsem);
        for (scb = select_cb_list; scb; scb = scb->next)
        {
            if (scb->sem_signalled == 0)
            {
                /* Test this select call for our socket */
                if (scb->readset && FD_ISSET(s, scb->readset))
                    if (sock->rcvevent)
                        break;
                if (scb->writeset && FD_ISSET(s, scb->writeset))
                    if (sock->sendevent)
                        break;
            }
        }
        if (scb)
        {
            scb->sem_signalled = 1;
            sys_sem_signal(selectsem);
            sys_sem_signal(scb->sem);
        } else {
            sys_sem_signal(selectsem);
            break;
        }
    }

}




int lwip_shutdown(int s, int how)
{
  LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_shutdown(%d, how=%d)\n", s, how));
  return lwip_close(s); /* XXX temporary hack until proper implementation */
}

int lwip_getpeername (int s, struct sockaddr *name, socklen_t *namelen)
{
  struct lwip_socket *sock;
  struct sockaddr_in sin;
  struct ip_addr naddr;

  sock = get_socket(s);
  if (!sock) {
    set_errno(EBADF);
    return -1;
  }

  memset(&sin, 0, sizeof(sin));
  sin.sin_len = sizeof(sin);
  sin.sin_family = AF_INET;

  /* get the IP address and port of the remote host */
  netconn_peer(sock->conn, &naddr, &sin.sin_port);

  LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_getpeername(%d, addr=", s));
  ip_addr_debug_print(SOCKETS_DEBUG, &naddr);
  LWIP_DEBUGF(SOCKETS_DEBUG, (" port=%d)\n", sin.sin_port));

  sin.sin_port = htons(sin.sin_port);
  sin.sin_addr.s_addr = naddr.addr;

  if (*namelen > sizeof(sin))
      *namelen = sizeof(sin);

  memcpy(name, &sin, *namelen);
  sock_set_errno(sock, 0);
  return 0;
}

int lwip_getsockname (int s, struct sockaddr *name, socklen_t *namelen)
{
  struct lwip_socket *sock;
  struct sockaddr_in sin;
  struct ip_addr *naddr;

  sock = get_socket(s);
  if (!sock) {
    set_errno(EBADF);
    return -1;
  }

  memset(&sin, 0, sizeof(sin));
  sin.sin_len = sizeof(sin);
  sin.sin_family = AF_INET;

  /* get the IP address and port of the remote host */
  netconn_addr(sock->conn, &naddr, &sin.sin_port);

  LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_getsockname(%d, addr=", s));
  ip_addr_debug_print(SOCKETS_DEBUG, naddr);
  LWIP_DEBUGF(SOCKETS_DEBUG, (" port=%d)\n", sin.sin_port));

  sin.sin_port = htons(sin.sin_port);
  sin.sin_addr.s_addr = naddr->addr;

  if (*namelen > sizeof(sin))
      *namelen = sizeof(sin);

  memcpy(name, &sin, *namelen);
  sock_set_errno(sock, 0);
  return 0;
}

int lwip_getsockopt (int s, int level, int optname, void *optval, socklen_t *optlen)
{
  int err = 0;
  struct lwip_socket *sock = get_socket(s);

  if(!sock) {
   	set_errno(EBADF);
    return -1;
  }

  if( NULL == optval || NULL == optlen ) {
    sock_set_errno( sock, EFAULT );
    return -1;
  }

  /* Do length and type checks for the various options first, to keep it readable. */
  switch( level ) {
   
/* Level: SOL_SOCKET */
  case SOL_SOCKET:
      switch(optname) {
         
      case SO_ACCEPTCONN:
      case SO_BROADCAST:
      /* UNIMPL case SO_DEBUG: */
      /* UNIMPL case SO_DONTROUTE: */
      case SO_ERROR:
      case SO_KEEPALIVE:
      /* UNIMPL case SO_OOBINLINE: */
      /* UNIMPL case SO_RCVBUF: */
      /* UNIMPL case SO_SNDBUF: */
      /* UNIMPL case SO_RCVLOWAT: */
      /* UNIMPL case SO_SNDLOWAT: */
#if SO_REUSE
      case SO_REUSEADDR:
      case SO_REUSEPORT:
#endif /* SO_REUSE */
      case SO_TYPE:
      /* UNIMPL case SO_USELOOPBACK: */
        if( *optlen < sizeof(int) ) {
          err = EINVAL;
        }
          break;

      default:
        LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_getsockopt(%d, SOL_SOCKET, UNIMPL: optname=0x%x, ..)\n", s, optname));
        err = ENOPROTOOPT;
      }  /* switch */
      break;
                     
/* Level: IPPROTO_IP */
  case IPPROTO_IP:
      switch(optname) {
      /* UNIMPL case IP_HDRINCL: */
      /* UNIMPL case IP_RCVDSTADDR: */
      /* UNIMPL case IP_RCVIF: */
      case IP_TTL:
      case IP_TOS:
        if( *optlen < sizeof(int) ) {
          err = EINVAL;
        }
        break;

      default:
        LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_getsockopt(%d, IPPROTO_IP, UNIMPL: optname=0x%x, ..)\n", s, optname));
        err = ENOPROTOOPT;
      }  /* switch */
      break;
         
/* Level: IPPROTO_TCP */
  case IPPROTO_TCP:
      if( *optlen < sizeof(int) ) {
        err = EINVAL;
        break;
    }
      
      /* If this is no TCP socket, ignore any options. */
      if ( sock->conn->type != NETCONN_TCP ) return 0;

      switch( optname ) {
      case TCP_NODELAY:
      case TCP_KEEPALIVE:
        break;
         
      default:
        LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_getsockopt(%d, IPPROTO_TCP, UNIMPL: optname=0x%x, ..)\n", s, optname));
        err = ENOPROTOOPT;
      }  /* switch */
      break;

/* UNDEFINED LEVEL */
  default:
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_getsockopt(%d, level=0x%x, UNIMPL: optname=0x%x, ..)\n", s, level, optname));
      err = ENOPROTOOPT;
  }  /* switch */

   
  if( 0 != err ) {
    sock_set_errno(sock, err);
    return -1;
  }
   


  /* Now do the actual option processing */

  switch(level) {
   
/* Level: SOL_SOCKET */
  case SOL_SOCKET:
    switch( optname ) {

    /* The option flags */
    case SO_ACCEPTCONN:
    case SO_BROADCAST:
    /* UNIMPL case SO_DEBUG: */
    /* UNIMPL case SO_DONTROUTE: */
    case SO_KEEPALIVE:
    /* UNIMPL case SO_OOBINCLUDE: */
#if SO_REUSE
    case SO_REUSEADDR:
    case SO_REUSEPORT:
#endif /* SO_REUSE */
    /*case SO_USELOOPBACK: UNIMPL */
      *(int*)optval = sock->conn->pcb.tcp->so_options & optname;
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_getsockopt(%d, SOL_SOCKET, optname=0x%x, ..) = %s\n", s, optname, (*(int*)optval?"on":"off")));
      break;

    case SO_TYPE:
      switch (sock->conn->type) {
      case NETCONN_RAW:
        *(int*)optval = SOCK_RAW;
        break;
      case NETCONN_TCP:
        *(int*)optval = SOCK_STREAM;
        break;
      case NETCONN_UDP:
      case NETCONN_UDPLITE:
      case NETCONN_UDPNOCHKSUM:
        *(int*)optval = SOCK_DGRAM;
        break;
      default: /* unrecognized socket type */
        *(int*)optval = sock->conn->type;
        LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_getsockopt(%d, SOL_SOCKET, SO_TYPE): unrecognized socket type %d\n", s, *(int *)optval));
      }  /* switch */
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_getsockopt(%d, SOL_SOCKET, SO_TYPE) = %d\n", s, *(int *)optval));
      break;

    case SO_ERROR:
      *(int *)optval = sock->err;
      sock->err = 0;
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_getsockopt(%d, SOL_SOCKET, SO_ERROR) = %d\n", s, *(int *)optval));
      break;
    }  /* switch */
    break;

/* Level: IPPROTO_IP */
  case IPPROTO_IP:
    switch( optname ) {
    case IP_TTL:
      *(int*)optval = sock->conn->pcb.tcp->ttl;
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_getsockopt(%d, IPPROTO_IP, IP_TTL) = %d\n", s, *(int *)optval));
      break;
    case IP_TOS:
      *(int*)optval = sock->conn->pcb.tcp->tos;
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_getsockopt(%d, IPPROTO_IP, IP_TOS) = %d\n", s, *(int *)optval));
      break;
    }  /* switch */
    break;

/* Level: IPPROTO_TCP */
  case IPPROTO_TCP:
    switch( optname ) {
    case TCP_NODELAY:
      *(int*)optval = (sock->conn->pcb.tcp->flags & TF_NODELAY);
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_getsockopt(%d, IPPROTO_TCP, TCP_NODELAY) = %s\n", s, (*(int*)optval)?"on":"off") );
      break;
    case TCP_KEEPALIVE:
      *(int*)optval = (int)sock->conn->pcb.tcp->keepalive;
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_getsockopt(%d, IPPROTO_IP, TCP_KEEPALIVE) = %d\n", s, *(int *)optval));
      break;
    }  /* switch */
    break;
  }


  sock_set_errno(sock, err);
  return err ? -1 : 0;
}

int lwip_setsockopt (int s, int level, int optname, const void *optval, socklen_t optlen)
{
  struct lwip_socket *sock = get_socket(s);
  int err = 0;

  if(!sock) {
   	set_errno(EBADF);
    return -1;
  }

  if( NULL == optval ) {
    sock_set_errno( sock, EFAULT );
    return -1;
  }


  /* Do length and type checks for the various options first, to keep it readable. */
  switch( level ) {

/* Level: SOL_SOCKET */
  case SOL_SOCKET:
    switch(optname) {

    case SO_BROADCAST:
    /* UNIMPL case SO_DEBUG: */
    /* UNIMPL case SO_DONTROUTE: */
    case SO_KEEPALIVE:
    /* UNIMPL case SO_OOBINLINE: */
    /* UNIMPL case SO_RCVBUF: */
    /* UNIMPL case SO_SNDBUF: */
    /* UNIMPL case SO_RCVLOWAT: */
    /* UNIMPL case SO_SNDLOWAT: */
#if SO_REUSE
    case SO_REUSEADDR:
    case SO_REUSEPORT:
#endif /* SO_REUSE */
    /* UNIMPL case SO_USELOOPBACK: */
      if( optlen < sizeof(int) ) {
        err = EINVAL;
      }
      break;
    default:
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_setsockopt(%d, SOL_SOCKET, UNIMPL: optname=0x%x, ..)\n", s, optname));
      err = ENOPROTOOPT;
    }  /* switch */
    break;

/* Level: IPPROTO_IP */
  case IPPROTO_IP:
    switch(optname) {
    /* UNIMPL case IP_HDRINCL: */
    /* UNIMPL case IP_RCVDSTADDR: */
    /* UNIMPL case IP_RCVIF: */
    case IP_TTL:
    case IP_TOS:
      if( optlen < sizeof(int) ) {
        err = EINVAL;
      }
        break;
      default:
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_setsockopt(%d, IPPROTO_IP, UNIMPL: optname=0x%x, ..)\n", s, optname));
      err = ENOPROTOOPT;
    }  /* switch */
    break;

/* Level: IPPROTO_TCP */
  case IPPROTO_TCP:
    if( optlen < sizeof(int) ) {
      err = EINVAL;
        break;
    }

    /* If this is no TCP socket, ignore any options. */
    if ( sock->conn->type != NETCONN_TCP ) return 0;

    switch( optname ) {
    case TCP_NODELAY:
    case TCP_KEEPALIVE:
      break;

    default:
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_setsockopt(%d, IPPROTO_TCP, UNIMPL: optname=0x%x, ..)\n", s, optname));
      err = ENOPROTOOPT;
    }  /* switch */
    break;

/* UNDEFINED LEVEL */      
  default:
    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_setsockopt(%d, level=0x%x, UNIMPL: optname=0x%x, ..)\n", s, level, optname));
    err = ENOPROTOOPT;
  }  /* switch */


  if( 0 != err ) {
    sock_set_errno(sock, err);
    return -1;
  }



  /* Now do the actual option processing */

  switch(level) {

/* Level: SOL_SOCKET */
  case SOL_SOCKET:
    switch(optname) {

    /* The option flags */
    case SO_BROADCAST:
    /* UNIMPL case SO_DEBUG: */
    /* UNIMPL case SO_DONTROUTE: */
    case SO_KEEPALIVE:
    /* UNIMPL case SO_OOBINCLUDE: */
#if SO_REUSE
    case SO_REUSEADDR:
    case SO_REUSEPORT:
#endif /* SO_REUSE */
    /* UNIMPL case SO_USELOOPBACK: */
      if ( *(int*)optval ) {
        sock->conn->pcb.tcp->so_options |= optname;
      } else {
        sock->conn->pcb.tcp->so_options &= ~optname;
      }
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_setsockopt(%d, SOL_SOCKET, optname=0x%x, ..) -> %s\n", s, optname, (*(int*)optval?"on":"off")));
      break;
    }  /* switch */
    break;

/* Level: IPPROTO_IP */
  case IPPROTO_IP:
    switch( optname ) {
    case IP_TTL:
      sock->conn->pcb.tcp->ttl = (u8_t)(*(int*)optval);
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_setsockopt(%d, IPPROTO_IP, IP_TTL, ..) -> %u\n", s, sock->conn->pcb.tcp->ttl));
      break;
    case IP_TOS:
      sock->conn->pcb.tcp->tos = (u8_t)(*(int*)optval);
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_setsockopt(%d, IPPROTO_IP, IP_TOS, ..)-> %u\n", s, sock->conn->pcb.tcp->tos));
      break;
    }  /* switch */
    break;

/* Level: IPPROTO_TCP */
  case IPPROTO_TCP:
    switch( optname ) {
    case TCP_NODELAY:
      if ( *(int*)optval ) {
        sock->conn->pcb.tcp->flags |= TF_NODELAY;
      } else {
        sock->conn->pcb.tcp->flags &= ~TF_NODELAY;
      }
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_setsockopt(%d, IPPROTO_TCP, TCP_NODELAY) -> %s\n", s, (*(int *)optval)?"on":"off") );
      break;
    case TCP_KEEPALIVE:
      sock->conn->pcb.tcp->keepalive = (u32_t)(*(int*)optval);
      LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_setsockopt(%d, IPPROTO_TCP, TCP_KEEPALIVE) -> %lu\n", s, sock->conn->pcb.tcp->keepalive));
      break;
    }  /* switch */
    break;
  }  /* switch */

  sock_set_errno(sock, err);
  return err ? -1 : 0;
}

int lwip_ioctl(int s, long cmd, void *argp)
{
  struct lwip_socket *sock = get_socket(s);

  if(!sock) {
   	set_errno(EBADF);
    return -1;
  }

  switch (cmd) {
  case FIONREAD:
    if (!argp) {
      sock_set_errno(sock, EINVAL);
      return -1;
    }

    *((u16_t*)argp) = sock->conn->recv_avail;

    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_ioctl(%d, FIONREAD, %p) = %u\n", s, argp, *((u16_t*)argp)));
    sock_set_errno(sock, 0);
    return 0;

  case FIONBIO:
    if (argp && *(u32_t*)argp)
      sock->flags |= O_NONBLOCK;
    else
      sock->flags &= ~O_NONBLOCK;
    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_ioctl(%d, FIONBIO, %d)\n", s, !!(sock->flags & O_NONBLOCK)));
    sock_set_errno(sock, 0);
    return 0;

  default:
    LWIP_DEBUGF(SOCKETS_DEBUG, ("lwip_ioctl(%d, UNIMPL: 0x%lx, %p)\n", s, cmd, argp));
    sock_set_errno(sock, ENOSYS); /* not yet implemented */
    return -1;
  }
}

