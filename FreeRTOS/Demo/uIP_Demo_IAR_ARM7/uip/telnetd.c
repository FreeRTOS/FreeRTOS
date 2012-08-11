/**
 * \addtogroup exampleapps
 * @{
 */

/**
 * \defgroup telnetd Telnet server
 * @{
 *
 * The uIP telnet server provides a command based interface to uIP. It
 * allows using the "telnet" application to access uIP, and implements
 * the required telnet option negotiation.
 *
 * The code is structured in a way which makes it possible to add
 * commands without having to rewrite the main telnet code. The main
 * telnet code calls two callback functions, telnetd_connected() and
 * telnetd_input(), when a telnet connection has been established and
 * when a line of text arrives on a telnet connection. These two
 * functions can be implemented in a way which suits the particular
 * application or environment in which the uIP system is intended to
 * be run.
 *
 * The uIP distribution contains an example telnet shell
 * implementation that provides a basic set of commands.
 */

/**
 * \file
 * Implementation of the Telnet server.
 * \author Adam Dunkels <adam@dunkels.com>
 */

/*
 * Copyright (c) 2003, Adam Dunkels.
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
 * $Id: telnetd.c,v 1.1.2.2 2003/10/07 13:47:50 adam Exp $
 *
 */

#include "uip.h"
#include "memb.h"
#include "telnetd.h"
#include <string.h>

#define ISO_nl       0x0a
#define ISO_cr       0x0d

MEMB(linemem, TELNETD_LINELEN, TELNETD_NUMLINES);

static u8_t i;

#define STATE_NORMAL 0
#define STATE_IAC    1
#define STATE_WILL   2
#define STATE_WONT   3
#define STATE_DO     4  
#define STATE_DONT   5
#define STATE_CLOSE  6

#define TELNET_IAC   255
#define TELNET_WILL  251
#define TELNET_WONT  252
#define TELNET_DO    253
#define TELNET_DONT  254
/*-----------------------------------------------------------------------------------*/
static char *
alloc_line(void)
{  
  return memb_alloc(&linemem);
}
/*-----------------------------------------------------------------------------------*/
static void
dealloc_line(char *line)
{
  memb_free(&linemem, line);
}
/*-----------------------------------------------------------------------------------*/
static void
sendline(struct telnetd_state *s, char *line)
{
  static unsigned int i;
  for(i = 0; i < TELNETD_NUMLINES; ++i) {
    if(s->lines[i] == NULL) {
      s->lines[i] = line;
      break;
    }
  }
  if(i == TELNETD_NUMLINES) {
    dealloc_line(line);
  }
}
/*-----------------------------------------------------------------------------------*/
/**
 * Close a telnet session.
 *
 * This function can be called from a telnet command in order to close
 * the connection.
 *
 * \param s The connection which is to be closed.
 *
 */
/*-----------------------------------------------------------------------------------*/
void
telnetd_close(struct telnetd_state *s)
{
  s->state = STATE_CLOSE;
}
/*-----------------------------------------------------------------------------------*/
/**
 * Print a prompt on a telnet connection.
 *
 * This function can be called by the telnet command shell in order to
 * print out a command prompt.
 *
 * \param s A telnet connection.
 *
 * \param str The command prompt.
 *
 */
/*-----------------------------------------------------------------------------------*/
void
telnetd_prompt(struct telnetd_state *s, char *str)
{
  char *line;
  line = alloc_line();
  if(line != NULL) {
    strncpy(line, str, TELNETD_LINELEN);
    sendline(s, line);
  }         
}
/*-----------------------------------------------------------------------------------*/
/**
 * Print out a string on a telnet connection.
 *
 * This function can be called from a telnet command parser in order
 * to print out a string of text on the connection. The two strings
 * given as arguments to the function will be concatenated, a carrige
 * return and a new line character will be added, and the line is
 * sent.
 *
 * \param s The telnet connection.
 *
 * \param str1 The first string.
 *
 * \param str2 The second string.
 *
 */
/*-----------------------------------------------------------------------------------*/
void
telnetd_output(struct telnetd_state *s, char *str1, char *str2)
{
  static unsigned len;
  char *line;
  
  line = alloc_line();
  if(line != NULL) {
    len = strlen(str1);
    strncpy(line, str1, TELNETD_LINELEN);
    if(len < TELNETD_LINELEN) {
      strncpy(line + len, str2, TELNETD_LINELEN - len);
    }
    len = strlen(line);
    if(len < TELNETD_LINELEN - 2) {
      line[len] = ISO_cr;
      line[len+1] = ISO_nl;
      line[len+2] = 0;
    }
    sendline(s, line);
  }
}
/*-----------------------------------------------------------------------------------*/
/**
 * Initialize the telnet server.
 *
 * This function will perform the necessary initializations and start
 * listening on TCP port 23.
 */
/*-----------------------------------------------------------------------------------*/
void
telnetd_init(void)
{
  memb_init(&linemem);
  uip_listen(HTONS(23));
}
/*-----------------------------------------------------------------------------------*/
static void
acked(struct telnetd_state *s)     
{
  dealloc_line(s->lines[0]);
  for(i = 1; i < TELNETD_NUMLINES; ++i) {
    s->lines[i - 1] = s->lines[i];
  }
}
/*-----------------------------------------------------------------------------------*/
static void
senddata(struct telnetd_state *s)    
{
  if(s->lines[0] != NULL) {
    uip_send(s->lines[0], strlen(s->lines[0]));
  }
}
/*-----------------------------------------------------------------------------------*/
static void
getchar(struct telnetd_state *s, u8_t c)
{
  if(c == ISO_cr) {
    return;
  }
  
  s->buf[(int)s->bufptr] = c;  
  if(s->buf[(int)s->bufptr] == ISO_nl ||
     s->bufptr == sizeof(s->buf) - 1) {    
    if(s->bufptr > 0) {
      s->buf[(int)s->bufptr] = 0;
    }
    telnetd_input(s, s->buf);
    s->bufptr = 0;
  } else {
    ++s->bufptr;
  }
}
/*-----------------------------------------------------------------------------------*/
static void
sendopt(struct telnetd_state *s, u8_t option, u8_t value)
{
  char *line;
  line = alloc_line();
  if(line != NULL) {
    line[0] = TELNET_IAC;
    line[1] = option;
    line[2] = value;
    line[3] = 0;
    sendline(s, line);
  }       
}
/*-----------------------------------------------------------------------------------*/
static void
newdata(struct telnetd_state *s)
{
  u16_t len;
  u8_t c;
    
  
  len = uip_datalen();
  
  while(len > 0 && s->bufptr < sizeof(s->buf)) {
    c = *uip_appdata;
    ++uip_appdata;
    --len;
    switch(s->state) {
    case STATE_IAC:
      if(c == TELNET_IAC) {
	getchar(s, c);
	s->state = STATE_NORMAL;
      } else {
	switch(c) {
	case TELNET_WILL:
	  s->state = STATE_WILL;
	  break;
	case TELNET_WONT:
	  s->state = STATE_WONT;
	  break;
	case TELNET_DO:
	  s->state = STATE_DO;
	  break;
	case TELNET_DONT:
	  s->state = STATE_DONT;
	  break;
	default:
	  s->state = STATE_NORMAL;
	  break;
	}
      }
      break;
    case STATE_WILL:
      /* Reply with a DONT */
      sendopt(s, TELNET_DONT, c);
      s->state = STATE_NORMAL;
      break;
      
    case STATE_WONT:
      /* Reply with a DONT */
      sendopt(s, TELNET_DONT, c);
      s->state = STATE_NORMAL;
      break;
    case STATE_DO:
      /* Reply with a WONT */
      sendopt(s, TELNET_WONT, c);
      s->state = STATE_NORMAL;
      break;
    case STATE_DONT:
      /* Reply with a WONT */
      sendopt(s, TELNET_WONT, c);
      s->state = STATE_NORMAL;
      break;
    case STATE_NORMAL:
      if(c == TELNET_IAC) {
	s->state = STATE_IAC;
      } else {
	getchar(s, c);
      }      
      break;
    } 

    
  }  
  
}
/*-----------------------------------------------------------------------------------*/
void
telnetd_app(void)
{
  struct telnetd_state *s;

  s = (struct telnetd_state *)uip_conn->appstate;
  
  if(uip_connected()) {

    for(i = 0; i < TELNETD_NUMLINES; ++i) {
      s->lines[i] = NULL;
    }
    s->bufptr = 0;
    s->state = STATE_NORMAL;

    telnetd_connected(s);
    senddata(s);
    return;
  }

  if(s->state == STATE_CLOSE) {
    s->state = STATE_NORMAL;
    uip_close();
    return;
  }
  
  if(uip_closed()) {
    telnetd_output(s, "Connection closed", "");
  }

  
  if(uip_aborted()) {
    telnetd_output(s, "Connection reset", "");
  }
  
  if(uip_timedout()) {
    telnetd_output(s, "Connection timed out", "");
  }
  
  if(uip_acked()) {
    acked(s);
  }
  
  if(uip_newdata()) {
    newdata(s);
  }
  
  if(uip_rexmit() ||
     uip_newdata() ||
     uip_acked()) {
    senddata(s);
  } else if(uip_poll()) {    
    senddata(s);
  }
}
/*-----------------------------------------------------------------------------------*/
