/* arc4.c
 *
 * Copyright (C) 2006-2015 wolfSSL Inc.
 *
 * This file is part of wolfSSL. (formerly known as CyaSSL)
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#ifndef NO_RC4

#include <wolfssl/wolfcrypt/arc4.h>

#ifdef HAVE_CAVIUM
    static void wc_Arc4CaviumSetKey(Arc4* arc4, const byte* key, word32 length);
    static void wc_Arc4CaviumProcess(Arc4* arc4, byte* out, const byte* in,
                                  word32 length);
#endif


void wc_Arc4SetKey(Arc4* arc4, const byte* key, word32 length)
{
    word32 i;
    word32 keyIndex = 0, stateIndex = 0;

#ifdef HAVE_CAVIUM
    if (arc4->magic == WOLFSSL_ARC4_CAVIUM_MAGIC)
        return wc_Arc4CaviumSetKey(arc4, key, length);
#endif

    arc4->x = 1;
    arc4->y = 0;

    for (i = 0; i < ARC4_STATE_SIZE; i++)
        arc4->state[i] = (byte)i;

    for (i = 0; i < ARC4_STATE_SIZE; i++) {
        word32 a = arc4->state[i];
        stateIndex += key[keyIndex] + a;
        stateIndex &= 0xFF;
        arc4->state[i] = arc4->state[stateIndex];
        arc4->state[stateIndex] = (byte)a;

        if (++keyIndex >= length)
            keyIndex = 0;
    }
}


static INLINE byte MakeByte(word32* x, word32* y, byte* s)
{
    word32 a = s[*x], b;
    *y = (*y+a) & 0xff;

    b = s[*y];
    s[*x] = (byte)b;
    s[*y] = (byte)a;
    *x = (*x+1) & 0xff;

    return s[(a+b) & 0xff];
}


void wc_Arc4Process(Arc4* arc4, byte* out, const byte* in, word32 length)
{
    word32 x;
    word32 y;

#ifdef HAVE_CAVIUM
    if (arc4->magic == WOLFSSL_ARC4_CAVIUM_MAGIC)
        return wc_Arc4CaviumProcess(arc4, out, in, length);
#endif

    x = arc4->x;
    y = arc4->y;

    while(length--)
        *out++ = *in++ ^ MakeByte(&x, &y, arc4->state);

    arc4->x = (byte)x;
    arc4->y = (byte)y;
}


#ifdef HAVE_CAVIUM

#include <wolfssl/wolfcrypt/logging.h>
#include "cavium_common.h"

/* Initiliaze Arc4 for use with Nitrox device */
int wc_Arc4InitCavium(Arc4* arc4, int devId)
{
    if (arc4 == NULL)
        return -1;

    if (CspAllocContext(CONTEXT_SSL, &arc4->contextHandle, devId) != 0)
        return -1;

    arc4->devId = devId;
    arc4->magic = WOLFSSL_ARC4_CAVIUM_MAGIC;

    return 0;
}


/* Free Arc4 from use with Nitrox device */
void wc_Arc4FreeCavium(Arc4* arc4)
{
    if (arc4 == NULL)
        return;

    if (arc4->magic != WOLFSSL_ARC4_CAVIUM_MAGIC)
        return;

    CspFreeContext(CONTEXT_SSL, arc4->contextHandle, arc4->devId);
    arc4->magic = 0;
}


static void wc_Arc4CaviumSetKey(Arc4* arc4, const byte* key, word32 length)
{
    word32 requestId;

    if (CspInitializeRc4(CAVIUM_BLOCKING, arc4->contextHandle, length,
                         (byte*)key, &requestId, arc4->devId) != 0) {
        WOLFSSL_MSG("Bad Cavium Arc4 Init");
    }
}


static void wc_Arc4CaviumProcess(Arc4* arc4, byte* out, const byte* in,
                              word32 length)
{
    wolfssl_word offset = 0;
    word32 requestId;

    while (length > WOLFSSL_MAX_16BIT) {
        word16 slen = (word16)WOLFSSL_MAX_16BIT;
        if (CspEncryptRc4(CAVIUM_BLOCKING, arc4->contextHandle,CAVIUM_UPDATE,
                          slen, (byte*)in + offset, out + offset, &requestId,
                          arc4->devId) != 0) {
            WOLFSSL_MSG("Bad Cavium Arc4 Encrypt");
        }
        length -= WOLFSSL_MAX_16BIT;
        offset += WOLFSSL_MAX_16BIT;
    }
    if (length) {
        word16 slen = (word16)length;
        if (CspEncryptRc4(CAVIUM_BLOCKING, arc4->contextHandle,CAVIUM_UPDATE,
                          slen, (byte*)in + offset, out + offset, &requestId,
                          arc4->devId) != 0) {
            WOLFSSL_MSG("Bad Cavium Arc4 Encrypt");
        }
    }
}

#endif /* HAVE_CAVIUM */

#endif /* NO_RC4 */

