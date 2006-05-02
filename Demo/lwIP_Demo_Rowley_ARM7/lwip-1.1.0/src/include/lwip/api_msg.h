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
#ifndef __LWIP_API_MSG_H__
#define __LWIP_API_MSG_H__

#include "lwip/opt.h"
#include "lwip/pbuf.h"
#include "lwip/sys.h"

#include "lwip/ip.h"

#include "lwip/udp.h"
#include "lwip/tcp.h"

#include "lwip/api.h"

enum api_msg_type {
  API_MSG_NEWCONN,
  API_MSG_DELCONN,
  
  API_MSG_BIND,
  API_MSG_CONNECT,
  API_MSG_DISCONNECT,

  API_MSG_LISTEN,
  API_MSG_ACCEPT,

  API_MSG_SEND,
  API_MSG_RECV,
  API_MSG_WRITE,

  API_MSG_CLOSE,
  
  API_MSG_MAX
};

struct api_msg_msg {
  struct netconn *conn;
  enum netconn_type conntype;
  union {
    struct pbuf *p;   
    struct  {
      struct ip_addr *ipaddr;
      u16_t port;
    } bc;
    struct {
      void *dataptr;
      u16_t len;
      unsigned char copy;
    } w;    
    sys_mbox_t mbox;
    u16_t len;
  } msg;
};

struct api_msg {
  enum api_msg_type type;
  struct api_msg_msg msg;
};

void api_msg_input(struct api_msg *msg);
void api_msg_post(struct api_msg *msg);

#endif /* __LWIP_API_MSG_H__ */

