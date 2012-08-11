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


/* inet.c
 *
 * Functions common to all TCP/IP modules, such as the Internet checksum and the
 * byte order functions.
 *
 */


#include "lwip/opt.h"

#include "lwip/arch.h"

#include "lwip/def.h"
#include "lwip/inet.h"

#include "lwip/sys.h"

/* This is a reference implementation of the checksum algorithm

 - it may not work on all architectures, and all processors, particularly
   if they have issues with alignment and 16 bit access.

 - in this case you will need to port it to your architecture and 
   #define LWIP_CHKSUM <your_checksum_routine> 
   in your sys_arch.h
*/
#ifndef LWIP_CHKSUM
#define LWIP_CHKSUM lwip_standard_chksum
static u16_t
lwip_standard_chksum(void *dataptr, int len)
{
  u32_t acc;

  LWIP_DEBUGF(INET_DEBUG, ("lwip_chksum(%p, %d)\n", (void *)dataptr, len));
  for(acc = 0; len > 1; len -= 2) {
      /*    acc = acc + *((u16_t *)dataptr)++;*/
    acc += *(u16_t *)dataptr;
    dataptr = (void *)((u16_t *)dataptr + 1);
  }

  /* add up any odd byte */
  if (len == 1) {
    acc += htons((u16_t)((*(u8_t *)dataptr) & 0xff) << 8);
    LWIP_DEBUGF(INET_DEBUG, ("inet: chksum: odd byte %d\n", (unsigned int)(*(u8_t *)dataptr)));
  } else {
    LWIP_DEBUGF(INET_DEBUG, ("inet: chksum: no odd byte\n"));
  }
  acc = (acc >> 16) + (acc & 0xffffUL);

  if ((acc & 0xffff0000) != 0) {
    acc = (acc >> 16) + (acc & 0xffffUL);
  }

  return (u16_t)acc;
}
#endif

/* inet_chksum_pseudo:
 *
 * Calculates the pseudo Internet checksum used by TCP and UDP for a pbuf chain.
 */

u16_t
inet_chksum_pseudo(struct pbuf *p,
       struct ip_addr *src, struct ip_addr *dest,
       u8_t proto, u16_t proto_len)
{
  u32_t acc;
  struct pbuf *q;
  u8_t swapped;

  acc = 0;
  swapped = 0;
  /* iterate through all pbuf in chain */
  for(q = p; q != NULL; q = q->next) {
    LWIP_DEBUGF(INET_DEBUG, ("inet_chksum_pseudo(): checksumming pbuf %p (has next %p) \n",
      (void *)q, (void *)q->next));
    acc += LWIP_CHKSUM(q->payload, q->len);
    /*LWIP_DEBUGF(INET_DEBUG, ("inet_chksum_pseudo(): unwrapped lwip_chksum()=%lx \n", acc));*/
    while (acc >> 16) {
      acc = (acc & 0xffffUL) + (acc >> 16);
    }
    if (q->len % 2 != 0) {
      swapped = 1 - swapped;
      acc = ((acc & 0xff) << 8) | ((acc & 0xff00UL) >> 8);
    }
    /*LWIP_DEBUGF(INET_DEBUG, ("inet_chksum_pseudo(): wrapped lwip_chksum()=%lx \n", acc));*/
  }

  if (swapped) {
    acc = ((acc & 0xff) << 8) | ((acc & 0xff00UL) >> 8);
  }
  acc += (src->addr & 0xffffUL);
  acc += ((src->addr >> 16) & 0xffffUL);
  acc += (dest->addr & 0xffffUL);
  acc += ((dest->addr >> 16) & 0xffffUL);
  acc += (u32_t)htons((u16_t)proto);
  acc += (u32_t)htons(proto_len);

  while (acc >> 16) {
    acc = (acc & 0xffffUL) + (acc >> 16);
  }
  LWIP_DEBUGF(INET_DEBUG, ("inet_chksum_pseudo(): pbuf chain lwip_chksum()=%lx\n", acc));
  return (u16_t)~(acc & 0xffffUL);
}

/* inet_chksum:
 *
 * Calculates the Internet checksum over a portion of memory. Used primarely for IP
 * and ICMP.
 */

u16_t
inet_chksum(void *dataptr, u16_t len)
{
  u32_t acc;

  acc = LWIP_CHKSUM(dataptr, len);
  while (acc >> 16) {
    acc = (acc & 0xffff) + (acc >> 16);
  }
  return (u16_t)~(acc & 0xffff);
}

u16_t
inet_chksum_pbuf(struct pbuf *p)
{
  u32_t acc;
  struct pbuf *q;
  u8_t swapped;

  acc = 0;
  swapped = 0;
  for(q = p; q != NULL; q = q->next) {
    acc += LWIP_CHKSUM(q->payload, q->len);
    while (acc >> 16) {
      acc = (acc & 0xffffUL) + (acc >> 16);
    }
    if (q->len % 2 != 0) {
      swapped = 1 - swapped;
      acc = (acc & 0x00ffUL << 8) | (acc & 0xff00UL >> 8);
    }
  }

  if (swapped) {
    acc = ((acc & 0x00ffUL) << 8) | ((acc & 0xff00UL) >> 8);
  }
  return (u16_t)~(acc & 0xffffUL);
}

/* Here for now until needed in other places in lwIP */
#ifndef isascii
#define in_range(c, lo, up)  ((u8_t)c >= lo && (u8_t)c <= up)
#define isascii(c)           in_range(c, 0x20, 0x7f)
#define isdigit(c)           in_range(c, '0', '9')
#define isxdigit(c)          (isdigit(c) || in_range(c, 'a', 'f') || in_range(c, 'A', 'F'))
#define islower(c)           in_range(c, 'a', 'z')
#define isspace(c)           (c == ' ' || c == '\f' || c == '\n' || c == '\r' || c == '\t' || c == '\v')
#endif		
		

 /*
  * Ascii internet address interpretation routine.
  * The value returned is in network order.
  */

 /*  */
 /* inet_addr */
 u32_t inet_addr(const char *cp)
 {
     struct in_addr val;

     if (inet_aton(cp, &val)) {
         return (val.s_addr);
     }
     return (INADDR_NONE);
 }

 /*
  * Check whether "cp" is a valid ascii representation
  * of an Internet address and convert to a binary address.
  * Returns 1 if the address is valid, 0 if not.
  * This replaces inet_addr, the return value from which
  * cannot distinguish between failure and a local broadcast address.
  */
 /*  */
 /* inet_aton */
 int inet_aton(const char *cp, struct in_addr *addr)
 {
     u32_t val;
     int base, n;
     char c;
     u32_t parts[4];
     u32_t* pp = parts;

     c = *cp;
     for (;;) {
         /*
          * Collect number up to ``.''.
          * Values are specified as for C:
          * 0x=hex, 0=octal, isdigit=decimal.
          */
         if (!isdigit(c))
             return (0);
         val = 0; base = 10;
         if (c == '0') {
             c = *++cp;
             if (c == 'x' || c == 'X')
                 base = 16, c = *++cp;
             else
                 base = 8;
         }
         for (;;) {
             if (isdigit(c)) {
                 val = (val * base) + (int)(c - '0');
                 c = *++cp;
             } else if (base == 16 && isxdigit(c)) {
                 val = (val << 4) |
                     (int)(c + 10 - (islower(c) ? 'a' : 'A'));
                 c = *++cp;
             } else
             break;
         }
         if (c == '.') {
             /*
              * Internet format:
              *  a.b.c.d
              *  a.b.c   (with c treated as 16 bits)
              *  a.b (with b treated as 24 bits)
              */
             if (pp >= parts + 3)
                 return (0);
             *pp++ = val;
             c = *++cp;
         } else
             break;
     }
     /*
      * Check for trailing characters.
      */
     if (c != '\0' && (!isascii(c) || !isspace(c)))
         return (0);
     /*
      * Concoct the address according to
      * the number of parts specified.
      */
     n = pp - parts + 1;
     switch (n) {

     case 0:
         return (0);     /* initial nondigit */

     case 1:             /* a -- 32 bits */
         break;

     case 2:             /* a.b -- 8.24 bits */
         if (val > 0xffffff)
             return (0);
         val |= parts[0] << 24;
         break;

     case 3:             /* a.b.c -- 8.8.16 bits */
         if (val > 0xffff)
             return (0);
         val |= (parts[0] << 24) | (parts[1] << 16);
         break;

     case 4:             /* a.b.c.d -- 8.8.8.8 bits */
         if (val > 0xff)
             return (0);
         val |= (parts[0] << 24) | (parts[1] << 16) | (parts[2] << 8);
         break;
     }
     if (addr)
         addr->s_addr = htonl(val);
     return (1);
 }

/* Convert numeric IP address into decimal dotted ASCII representation.
 * returns ptr to static buffer; not reentrant!
 */
char *inet_ntoa(struct in_addr addr)
{
  static char str[16];
  u32_t s_addr = addr.s_addr;
  char inv[3];
  char *rp;
  u8_t *ap;
  u8_t rem;
  u8_t n;
  u8_t i;

  rp = str;
  ap = (u8_t *)&s_addr;
  for(n = 0; n < 4; n++) {
    i = 0;
    do {
      rem = *ap % (u8_t)10;
      *ap /= (u8_t)10;
      inv[i++] = '0' + rem;
    } while(*ap);
    while(i--)
      *rp++ = inv[i];
    *rp++ = '.';
    ap++;
  }
  *--rp = 0;
  return str;
}


#ifndef BYTE_ORDER
#error BYTE_ORDER is not defined
#endif
#if BYTE_ORDER == LITTLE_ENDIAN

u16_t
htons(u16_t n)
{
  return ((n & 0xff) << 8) | ((n & 0xff00) >> 8);
}

u16_t
ntohs(u16_t n)
{
  return htons(n);
}

u32_t
htonl(u32_t n)
{
  return ((n & 0xff) << 24) |
    ((n & 0xff00) << 8) |
    ((n & 0xff0000) >> 8) |
    ((n & 0xff000000) >> 24);
}

u32_t
ntohl(u32_t n)
{
  return htonl(n);
}

#endif /* BYTE_ORDER == LITTLE_ENDIAN */
