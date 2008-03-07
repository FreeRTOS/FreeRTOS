/**
 * \addtogroup telnetd
 * @{
 */

/**
 * \file
 * An example telnet server shell
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
 * This file is part of the Contiki desktop OS.
 *
 * $Id: telnetd-shell.c,v 1.1.2.1 2003/10/06 22:56:22 adam Exp $
 *
 */

#include "uip.h"
#include "telnetd.h"
#include <string.h>

struct ptentry {
  char c;
  void (* pfunc)(struct telnetd_state *s, char *str);
};

/*-----------------------------------------------------------------------------------*/
static void
parse(struct telnetd_state *s, register char *str, struct ptentry *t)
{
  register struct ptentry *p;
  char *sstr;

  sstr = str;
  
  /* Loop over the parse table entries in t in order to find one that
     matches the first character in str. */
  for(p = t; p->c != 0; ++p) {
    if(*str == p->c) {
      /* Skip rest of the characters up to the first space. */
      while(*str != ' ') {
	++str;
      }

      /* Skip all spaces.*/
      while(*str == ' ') {
	++str;
      }

      /* Call parse table entry function and return. */
      p->pfunc(s, str);
      return;
    }
  }

  /* Did not find matching entry in parse table. We just call the
     default handler supplied by the caller and return. */
  p->pfunc(s, str);
}
/*-----------------------------------------------------------------------------------*/
static void
exitt(struct telnetd_state *s, char *str)
{
  telnetd_close(s);
}
/*-----------------------------------------------------------------------------------*/
static void
inttostr(register char *str, unsigned int i)
{
  str[0] = '0' + i / 100;
  if(str[0] == '0') {
    str[0] = ' ';
  }
  str[1] = '0' + (i / 10) % 10;
  if(str[1] == '0') {
    str[1] = ' ';
  }
  str[2] = '0' + i % 10;
  str[3] = ' ';
  str[4] = 0;
}
/*-----------------------------------------------------------------------------------*/
static void
stats(struct telnetd_state *s, char *strr)
{
  char str[10];

  inttostr(str, uip_stat.ip.recv);
  telnetd_output(s, "IP packets received ", str);
  inttostr(str, uip_stat.ip.sent);
  telnetd_output(s, "IP packets sent ", str);
  inttostr(str, uip_stat.ip.drop);
  telnetd_output(s, "IP packets dropped ", str);

  inttostr(str, uip_stat.icmp.recv);
  telnetd_output(s, "ICMP packets received ", str);
  inttostr(str, uip_stat.icmp.sent);
  telnetd_output(s, "ICMP packets sent ", str);
  inttostr(str, uip_stat.icmp.drop);
  telnetd_output(s, "ICMP packets dropped ", str);

  inttostr(str, uip_stat.tcp.recv);
  telnetd_output(s, "TCP packets received ", str);
  inttostr(str, uip_stat.tcp.sent);
  telnetd_output(s, "TCP packets sent ", str);
  inttostr(str, uip_stat.tcp.drop);
  telnetd_output(s, "TCP packets dropped ", str);
  inttostr(str, uip_stat.tcp.rexmit);
  telnetd_output(s, "TCP packets retransmitted ", str);
  inttostr(str, uip_stat.tcp.synrst);
  telnetd_output(s, "TCP connection attempts ", str);
}
/*-----------------------------------------------------------------------------------*/
static void
help(struct telnetd_state *s, char *str)
{
  telnetd_output(s, "Available commands:", "");
  telnetd_output(s, "stats - show uIP statistics", "");
  telnetd_output(s, "exit  - exit shell", "");  
  telnetd_output(s, "?     - show this help", "");        
}
/*-----------------------------------------------------------------------------------*/
static void
none(struct telnetd_state *s, char *str)
{
  if(strlen(str) > 0) {
    telnetd_output(s, "Unknown command", "");
  }
}
/*-----------------------------------------------------------------------------------*/
static struct ptentry configparsetab[] =
  {{'s', stats},
   {'e', exitt},
   {'?', help},

   /* Default action */
   {0, none}};
/*-----------------------------------------------------------------------------------*/
void
telnetd_connected(struct telnetd_state *s)
{
  telnetd_output(s, "uIP command shell", "");
  telnetd_output(s, "Type '?' for help", "");  
  telnetd_prompt(s, "uIP-0.9> "); 
}
/*-----------------------------------------------------------------------------------*/
void
telnetd_input(struct telnetd_state *s, char *cmd)
{
  parse(s, cmd, configparsetab);
  telnetd_prompt(s, "uIP-0.9> "); 
}
/*-----------------------------------------------------------------------------------*/
