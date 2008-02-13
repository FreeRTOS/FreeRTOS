/*
 * Copyright (c) 2001, Swedish Institute of Computer Science.
 * All rights reserved. 
 *
 * Redistribution and use in source and binary forms, with or without 
 * modification, are permitted provided that the following conditions 
 * are met: 
 *
 * 1. Redistributions of source code must retain the above copyright 
 *    notice, this list of conditions and the following disclaimer. 
 *
 * 2. Redistributions in binary form must reproduce the above copyright 
 *    notice, this list of conditions and the following disclaimer in the 
 *    documentation and/or other materials provided with the distribution. 
 *
 * 3. Neither the name of the Institute nor the names of its contributors 
 *    may be used to endorse or promote products derived from this software 
 *    without specific prior written permission. 
 *
 * THIS SOFTWARE IS PROVIDED BY THE INSTITUTE AND CONTRIBUTORS ``AS IS'' AND 
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE 
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE 
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE 
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL 
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS 
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) 
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT 
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY 
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF 
 * SUCH DAMAGE. 
 *
 * Author: Adam Dunkels <adam@sics.se>
 *
 * $Id: tapdev.c,v 1.7.2.1 2003/10/07 13:23:19 adam Exp $
 */


#include <fcntl.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/time.h>
#include <sys/uio.h>
#include <sys/socket.h>

#ifdef linux
#include <sys/ioctl.h>
#include <linux/if.h>
#include <linux/if_tun.h>
#define DEVTAP "/dev/net/tun"
#else  /* linux */
#define DEVTAP "/dev/tap0"
#endif /* linux */

#include "uip.h"

static int fd;

static unsigned long lasttime;
static struct timezone tz;

/*-----------------------------------------------------------------------------------*/
void
tapdev_init(void)
{
  char buf[1024];
  
  fd = open(DEVTAP, O_RDWR);
  if(fd == -1) {
    perror("tapdev: tapdev_init: open");
    exit(1);
  }

#ifdef linux
  {
    struct ifreq ifr;
    memset(&ifr, 0, sizeof(ifr));
    ifr.ifr_flags = IFF_TAP|IFF_NO_PI;
    if (ioctl(fd, TUNSETIFF, (void *) &ifr) < 0) {
      perror(buf);
      exit(1);
    }
  }
#endif /* Linux */

  snprintf(buf, sizeof(buf), "ifconfig tap0 inet %d.%d.%d.%d",
	   UIP_DRIPADDR0, UIP_DRIPADDR1, UIP_DRIPADDR2, UIP_DRIPADDR3);
  system(buf);

  lasttime = 0;
}
/*-----------------------------------------------------------------------------------*/
unsigned int
tapdev_read(void)
{
  fd_set fdset;
  struct timeval tv, now;
  int ret;
  
  if(lasttime >= 500000) {
    lasttime = 0;
    return 0;
  }
  
  tv.tv_sec = 0;
  tv.tv_usec = 500000 - lasttime;


  FD_ZERO(&fdset);
  FD_SET(fd, &fdset);

  gettimeofday(&now, &tz);  
  ret = select(fd + 1, &fdset, NULL, NULL, &tv);
  if(ret == 0) {
    lasttime = 0;    
    return 0;
  } 
  ret = read(fd, uip_buf, UIP_BUFSIZE);  
  if(ret == -1) {
    perror("tap_dev: tapdev_read: read");
  }
  gettimeofday(&tv, &tz);
  lasttime += (tv.tv_sec - now.tv_sec) * 1000000 + (tv.tv_usec - now.tv_usec);

  return ret;
}
/*-----------------------------------------------------------------------------------*/
void
tapdev_send(void)
{
  int ret;
  struct iovec iov[2];
  
#ifdef linux
  {
    char tmpbuf[UIP_BUFSIZE];
    int i;

    for(i = 0; i < 40 + UIP_LLH_LEN; i++) {
      tmpbuf[i] = uip_buf[i];
    }
    
    for(; i < uip_len; i++) {
      tmpbuf[i] = uip_appdata[i - 40 - UIP_LLH_LEN];
    }
    
    ret = write(fd, tmpbuf, uip_len);
  }  
#else 

  if(uip_len < 40 + UIP_LLH_LEN) {
    ret = write(fd, uip_buf, uip_len + UIP_LLH_LEN);
  } else {
    iov[0].iov_base = uip_buf;
    iov[0].iov_len = 40 + UIP_LLH_LEN;
    iov[1].iov_base = (char *)uip_appdata;
    iov[1].iov_len = uip_len - (40 + UIP_LLH_LEN);  
    
    ret = writev(fd, iov, 2);
  }
#endif
  if(ret == -1) {
    perror("tap_dev: tapdev_send: writev");
    exit(1);
  }
}  
/*-----------------------------------------------------------------------------------*/
