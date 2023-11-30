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
 */
#ifndef __LWIP_API_H__
#define __LWIP_API_H__

#include "lwip/opt.h"
#include "lwip/pbuf.h"
#include "lwip/sys.h"

#include "lwip/ip.h"

#include "lwip/raw.h"
#include "lwip/udp.h"
#include "lwip/tcp.h"

#include "lwip/err.h"

#define NETCONN_NOCOPY 0x00
#define NETCONN_COPY   0x01

enum netconn_type {
  NETCONN_TCP,
  NETCONN_UDP,
  NETCONN_UDPLITE,
  NETCONN_UDPNOCHKSUM,
  NETCONN_RAW
};

enum netconn_state {
  NETCONN_NONE,
  NETCONN_WRITE,
  NETCONN_ACCEPT,
  NETCONN_RECV,
  NETCONN_CONNECT,
  NETCONN_CLOSE
};

enum netconn_evt {
  NETCONN_EVT_RCVPLUS,
  NETCONN_EVT_RCVMINUS,
  NETCONN_EVT_SENDPLUS,
  NETCONN_EVT_SENDMINUS
};

struct netbuf {
  struct pbuf *p, *ptr;
  struct ip_addr *fromaddr;
  u16_t fromport;
  err_t err;
};

struct netconn {
  enum netconn_type type;
  enum netconn_state state;
  union {
    struct tcp_pcb *tcp;
    struct udp_pcb *udp;
    struct raw_pcb *raw;
  } pcb;
  err_t err;
  sys_mbox_t mbox;
  sys_mbox_t recvmbox;
  sys_mbox_t acceptmbox;
  sys_sem_t sem;
  int socket;
  u16_t recv_avail;
  void (* callback)(struct netconn *, enum netconn_evt, u16_t len);
};

/* Network buffer functions: */
struct netbuf *   netbuf_new      (void);
void              netbuf_delete   (struct netbuf *buf);
void *            netbuf_alloc    (struct netbuf *buf, u16_t size);
void              netbuf_free     (struct netbuf *buf);
void              netbuf_ref      (struct netbuf *buf,
           void *dataptr, u16_t size);
void              netbuf_chain    (struct netbuf *head,
           struct netbuf *tail);

u16_t             netbuf_len      (struct netbuf *buf);
err_t             netbuf_data     (struct netbuf *buf,
           void **dataptr, u16_t *len);
s8_t              netbuf_next     (struct netbuf *buf);
void              netbuf_first    (struct netbuf *buf);

void              netbuf_copy     (struct netbuf *buf,
           void *dataptr, u16_t len);
void              netbuf_copy_partial(struct netbuf *buf, void *dataptr, 
              u16_t len, u16_t offset);
struct ip_addr *  netbuf_fromaddr (struct netbuf *buf);
u16_t             netbuf_fromport (struct netbuf *buf);

/* Network connection functions: */
struct netconn *  netconn_new     (enum netconn_type type);
struct
netconn *netconn_new_with_callback(enum netconn_type t,
                                   void (*callback)(struct netconn *, enum netconn_evt, u16_t len));
struct
netconn *netconn_new_with_proto_and_callback(enum netconn_type t, u16_t proto,
                                   void (*callback)(struct netconn *, enum netconn_evt, u16_t len));
err_t             netconn_delete  (struct netconn *conn);
enum netconn_type netconn_type    (struct netconn *conn);
err_t             netconn_peer    (struct netconn *conn,
           struct ip_addr *addr,
           u16_t *port);
err_t             netconn_addr    (struct netconn *conn,
           struct ip_addr **addr,
           u16_t *port);
err_t             netconn_bind    (struct netconn *conn,
           struct ip_addr *addr,
           u16_t port);
err_t             netconn_connect (struct netconn *conn,
           struct ip_addr *addr,
           u16_t port);
err_t             netconn_disconnect (struct netconn *conn);
err_t             netconn_listen  (struct netconn *conn);
struct netconn *  netconn_accept  (struct netconn *conn);
struct netbuf *   netconn_recv    (struct netconn *conn);
err_t             netconn_send    (struct netconn *conn,
           struct netbuf *buf);
err_t             netconn_write   (struct netconn *conn,
           void *dataptr, u16_t size,
           u8_t copy);
err_t             netconn_close   (struct netconn *conn);

err_t             netconn_err     (struct netconn *conn);

#endif /* __LWIP_API_H__ */


