/**
 * \addtogroup telnetd
 * @{
 */

/**
 * \file
 * Header file for the telnet server.
 * \author Adam Dunkels <adam@dunkels.com>
 */

/*
 * Copyright (c) 2002, Adam Dunkels.
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
 * $Id: telnetd.h,v 1.1.2.2 2003/10/07 13:22:27 adam Exp $
 *
 */
#ifndef __TELNETD_H__
#define __TELNETD_H__

#include "uip.h"

/**
 * The maximum length of a telnet line.
 *
 * \hideinitializer
 */
#define TELNETD_LINELEN 36

/**
 * The number of output lines being buffered for all telnet
 * connections.
 *
 * \hideinitializer
 */
#define TELNETD_NUMLINES 2

/**
 * A telnet connection structure.
 */
struct telnetd_state {
  char *lines[TELNETD_NUMLINES];
  char buf[TELNETD_LINELEN];
  char bufptr;
  u8_t state;
};


/**
 * Callback function that is called when a telnet connection has been
 * established.
 *
 * \param s The telnet connection. 
 */
void telnetd_connected(struct telnetd_state *s);

/**
 * Callback function that is called when a line of text has arrived on
 * a telnet connection.
 *
 * \param s The telnet connection.
 *
 * \param cmd The line of text.
 */
void telnetd_input(struct telnetd_state *s, char *cmd);


void telnetd_close(struct telnetd_state *s);
void telnetd_output(struct telnetd_state *s, char *s1, char *s2);
void telnetd_prompt(struct telnetd_state *s, char *str);

void telnetd_app(void);

#ifndef UIP_APPCALL
#define UIP_APPCALL     telnetd_app
#endif

#ifndef UIP_APPSTATE_SIZE
#define UIP_APPSTATE_SIZE (sizeof(struct telnetd_state))
#endif

void telnetd_init(void);


#endif /* __TELNET_H__ */

/** @} */
