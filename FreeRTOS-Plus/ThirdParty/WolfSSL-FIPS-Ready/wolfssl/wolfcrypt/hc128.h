/* hc128.h
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */

/*!
    \file wolfssl/wolfcrypt/hc128.h
*/


#ifndef WOLF_CRYPT_HC128_H
#define WOLF_CRYPT_HC128_H

#include <wolfssl/wolfcrypt/types.h>

#ifndef NO_HC128

#ifdef __cplusplus
    extern "C" {
#endif

enum {
	HC128_ENC_TYPE =  WC_CIPHER_HC128,     /* cipher unique type */
};

/* HC-128 stream cipher */
typedef struct HC128 {
    word32 T[1024];             /* P[i] = T[i];  Q[i] = T[1024 + i ]; */
    word32 X[16];
    word32 Y[16];
    word32 counter1024;         /* counter1024 = i mod 1024 at the ith step */
    word32 key[8];
    word32 iv[8];
#ifdef XSTREAM_ALIGN
    void*  heap;  /* heap hint, currently XMALLOC only used with aligning */
#endif
} HC128;


WOLFSSL_API int wc_Hc128_Process(HC128*, byte*, const byte*, word32);
WOLFSSL_API int wc_Hc128_SetKey(HC128*, const byte* key, const byte* iv);

WOLFSSL_LOCAL int wc_Hc128_SetHeap(HC128* ctx, void* heap);

#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* HAVE_HC128 */
#endif /* WOLF_CRYPT_HC128_H */

