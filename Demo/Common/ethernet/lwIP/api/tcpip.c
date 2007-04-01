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

#include "lwip/opt.h"

#include "lwip/sys.h"

#include "lwip/memp.h"
#include "lwip/pbuf.h"

#include "lwip/ip.h"
#include "lwip/ip_frag.h"
#include "lwip/udp.h"
#include "lwip/tcp.h"

#include "lwip/tcpip.h"

static void (* tcpip_init_done)(void *arg) = NULL;
static void *tcpip_init_done_arg;
static sys_mbox_t mbox;

#if LWIP_TCP
static int tcpip_tcp_timer_active = 0;

static void
tcpip_tcp_timer(void *arg)
{
  (void)arg;

  /* call TCP timer handler */
  tcp_tmr();
  /* timer still needed? */
  if (tcp_active_pcbs || tcp_tw_pcbs) {
    /* restart timer */
    sys_timeout(TCP_TMR_INTERVAL, tcpip_tcp_timer, NULL);
  } else {
    /* disable timer */
    tcpip_tcp_timer_active = 0;
  }
}

#if !NO_SYS
void
tcp_timer_needed(void)
{
  /* timer is off but needed again? */
  if (!tcpip_tcp_timer_active && (tcp_active_pcbs || tcp_tw_pcbs)) {
    /* enable and start timer */
    tcpip_tcp_timer_active = 1;
    sys_timeout(TCP_TMR_INTERVAL, tcpip_tcp_timer, NULL);
  }
}
#endif /* !NO_SYS */
#endif /* LWIP_TCP */

#if IP_REASSEMBLY
static void
ip_timer(void *data)
{
  LWIP_DEBUGF(TCPIP_DEBUG, ("tcpip: ip_reass_tmr()\n"));
  ip_reass_tmr();
  sys_timeout(1000, ip_timer, NULL);
}
#endif

static void
tcpip_thread(void *arg)
{
  struct tcpip_msg *msg;

  (void)arg;

  ip_init();
#if LWIP_UDP  
  udp_init();
#endif
#if LWIP_TCP
  tcp_init();
#endif
#if IP_REASSEMBLY
  sys_timeout(1000, ip_timer, NULL);
#endif
  if (tcpip_init_done != NULL) {
    tcpip_init_done(tcpip_init_done_arg);
  }

  while (1) {                          /* MAIN Loop */
    sys_mbox_fetch(mbox, (void *)&msg);
    switch (msg->type) {
    case TCPIP_MSG_API:
      LWIP_DEBUGF(TCPIP_DEBUG, ("tcpip_thread: API message %p\n", (void *)msg));
      api_msg_input(msg->msg.apimsg);
      break;
    case TCPIP_MSG_INPUT:
      LWIP_DEBUGF(TCPIP_DEBUG, ("tcpip_thread: IP packet %p\n", (void *)msg));
      ip_input(msg->msg.inp.p, msg->msg.inp.netif);
      break;
    case TCPIP_MSG_CALLBACK:
      LWIP_DEBUGF(TCPIP_DEBUG, ("tcpip_thread: CALLBACK %p\n", (void *)msg));
      msg->msg.cb.f(msg->msg.cb.ctx);
      break;
    default:
      break;
    }
    memp_free(MEMP_TCPIP_MSG, msg);
  }
}

err_t
tcpip_input(struct pbuf *p, struct netif *inp)
{
  struct tcpip_msg *msg;
  
  msg = memp_malloc(MEMP_TCPIP_MSG);
  if (msg == NULL) {
    pbuf_free(p);    
    return ERR_MEM;  
  }
  
  msg->type = TCPIP_MSG_INPUT;
  msg->msg.inp.p = p;
  msg->msg.inp.netif = inp;
  sys_mbox_post(mbox, msg);
  return ERR_OK;
}

err_t
tcpip_callback(void (*f)(void *ctx), void *ctx)
{
  struct tcpip_msg *msg;
  
  msg = memp_malloc(MEMP_TCPIP_MSG);
  if (msg == NULL) {
    return ERR_MEM;  
  }
  
  msg->type = TCPIP_MSG_CALLBACK;
  msg->msg.cb.f = f;
  msg->msg.cb.ctx = ctx;
  sys_mbox_post(mbox, msg);
  return ERR_OK;
}

void
tcpip_apimsg(struct api_msg *apimsg)
{
  struct tcpip_msg *msg;
  msg = memp_malloc(MEMP_TCPIP_MSG);
  if (msg == NULL) {
    memp_free(MEMP_API_MSG, apimsg);
    return;
  }
  msg->type = TCPIP_MSG_API;
  msg->msg.apimsg = apimsg;
  sys_mbox_post(mbox, msg);
}

void
tcpip_init(void (* initfunc)(void *), void *arg)
{
  tcpip_init_done = initfunc;
  tcpip_init_done_arg = arg;
  mbox = sys_mbox_new();
  sys_thread_new(tcpip_thread, NULL, TCPIP_THREAD_PRIO);
}




