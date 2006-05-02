/**
 * \addtogroup httpd
 * @{
 */

/**
 * \file
 * HTTP server script language C functions file.
 * \author Adam Dunkels <adam@dunkels.com>
 *
 * This file contains functions that are called by the web server
 * scripts. The functions takes one argument, and the return value is
 * interpreted as follows. A zero means that the function did not
 * complete and should be invoked for the next packet as well. A
 * non-zero value indicates that the function has completed and that
 * the web server should move along to the next script line.
 *
 */

/*
 * Copyright (c) 2001, Adam Dunkels.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote
 *    products derived from this software without specific prior
 *    written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS
 * OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
 * GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * This file is part of the uIP TCP/IP stack.
 *
 * $Id: cgi.c,v 1.23.2.4 2003/10/07 13:22:27 adam Exp $
 *
 */

#include "uip.h"
#include "cgi.h"
#include "httpd.h"
#include "fs.h"

#include <stdio.h>
#include <string.h>

static u8_t print_stats(u8_t next);
static u8_t file_stats(u8_t next);
static u8_t tcp_stats(u8_t next);
static u8_t rtos_stats(u8_t next);

cgifunction cgitab[] = {
  print_stats,   /* CGI function "a" */
  file_stats,    /* CGI function "b" */
  tcp_stats,      /* CGI function "c" */
  rtos_stats	/* CGI function "d" */
};

static const char closed[] =   /*  "CLOSED",*/
{0x43, 0x4c, 0x4f, 0x53, 0x45, 0x44, 0};
static const char syn_rcvd[] = /*  "SYN-RCVD",*/
{0x53, 0x59, 0x4e, 0x2d, 0x52, 0x43, 0x56,
 0x44,  0};
static const char syn_sent[] = /*  "SYN-SENT",*/
{0x53, 0x59, 0x4e, 0x2d, 0x53, 0x45, 0x4e,
 0x54,  0};
static const char established[] = /*  "ESTABLISHED",*/
{0x45, 0x53, 0x54, 0x41, 0x42, 0x4c, 0x49, 0x53, 0x48,
 0x45, 0x44, 0};
static const char fin_wait_1[] = /*  "FIN-WAIT-1",*/
{0x46, 0x49, 0x4e, 0x2d, 0x57, 0x41, 0x49,
 0x54, 0x2d, 0x31, 0};
static const char fin_wait_2[] = /*  "FIN-WAIT-2",*/
{0x46, 0x49, 0x4e, 0x2d, 0x57, 0x41, 0x49,
 0x54, 0x2d, 0x32, 0};
static const char closing[] = /*  "CLOSING",*/
{0x43, 0x4c, 0x4f, 0x53, 0x49,
 0x4e, 0x47, 0};
static const char time_wait[] = /*  "TIME-WAIT,"*/
{0x54, 0x49, 0x4d, 0x45, 0x2d, 0x57, 0x41,
 0x49, 0x54, 0};
static const char last_ack[] = /*  "LAST-ACK"*/
{0x4c, 0x41, 0x53, 0x54, 0x2d, 0x41, 0x43,
 0x4b, 0};

static const char *states[] = {
  closed,
  syn_rcvd,
  syn_sent,
  established,
  fin_wait_1,
  fin_wait_2,
  closing,
  time_wait,
  last_ack};


/*-----------------------------------------------------------------------------------*/
/* print_stats:
 *
 * Prints out a part of the uIP statistics. The statistics data is
 * written into the uip_appdata buffer. It overwrites any incoming
 * packet.
 */
static u8_t
print_stats(u8_t next)
{
#if UIP_STATISTICS
  u16_t i, j;
  u8_t *buf;
  u16_t *databytes;

  if(next) {
    /* If our last data has been acknowledged, we move on the next
       chunk of statistics. */
    hs->count = hs->count + 4;
    if(hs->count >= sizeof(struct uip_stats)/sizeof(u16_t)) {
      /* We have printed out all statistics, so we return 1 to
	 indicate that we are done. */
      return 1;
    }
  }

  /* Write part of the statistics into the uip_appdata buffer. */
  databytes = (u16_t *)&uip_stat + hs->count;
  buf       = (u8_t *)uip_appdata;

  j = 4 + 1;
  i = hs->count;
  while (i < sizeof(struct uip_stats)/sizeof(u16_t) && --j > 0) {
    sprintf((char *)buf, "%5u\r\n", *databytes);
    ++databytes;
    buf += 6;
    ++i;
  }

  /* Send the data. */
  uip_send(uip_appdata, buf - uip_appdata);

  return 0;
#else
  return 1;
#endif /* UIP_STATISTICS */
}
/*-----------------------------------------------------------------------------------*/
static u8_t
file_stats(u8_t next)
{
  /* We use sprintf() to print the number of file accesses to a
     particular file (given as an argument to the function in the
     script). We then use uip_send() to actually send the data. */
  if(next) {
    return 1;
  }
  uip_send(uip_appdata, sprintf((char *)uip_appdata, "%5u", fs_count(&hs->script[4])));
  return 0;
}
/*-----------------------------------------------------------------------------------*/
static u8_t
tcp_stats(u8_t next)
{
  struct uip_conn *conn;

  if(next) {
    /* If the previously sent data has been acknowledged, we move
       forward one connection. */
    if(++hs->count == UIP_CONNS) {
      /* If all connections has been printed out, we are done and
	 return 1. */
      return 1;
    }
  }

  conn = &uip_conns[hs->count];
  if((conn->tcpstateflags & TS_MASK) == CLOSED) {
    uip_send(uip_appdata, sprintf((char *)uip_appdata,
				  "<tr align=\"center\"><td>-</td><td>-</td><td>%u</td><td>%u</td><td>%c %c</td></tr>\r\n",
				  conn->nrtx,
				  conn->timer,
				  (uip_outstanding(conn))? '*':' ',
    				  (uip_stopped(conn))? '!':' '));
  } else {
    uip_send(uip_appdata, sprintf((char *)uip_appdata,
				  "<tr align=\"center\"><td>%u.%u.%u.%u:%u</td><td>%s</td><td>%u</td><td>%u</td><td>%c %c</td></tr>\r\n",
				  htons(conn->ripaddr[0]) >> 8,
				  htons(conn->ripaddr[0]) & 0xff,
				  htons(conn->ripaddr[1]) >> 8,
				  htons(conn->ripaddr[1]) & 0xff,
				  htons(conn->rport),
				  states[conn->tcpstateflags & TS_MASK],
				  conn->nrtx,
				  conn->timer,
				  (uip_outstanding(conn))? '*':' ',
    				  (uip_stopped(conn))? '!':' '));
  }
  return 0;
}
/*-----------------------------------------------------------------------------------*/

static u8_t
rtos_stats(u8_t next)
{
static char cTraceBuffer[ 1024 ];
extern void ( vTaskList )( char * );

	vTaskList( cTraceBuffer );
	uip_send( ( void * ) cTraceBuffer, strlen( cTraceBuffer ) );

	return 1;
}
