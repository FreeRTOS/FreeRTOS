/* hc128.h
 *
 * Copyright (C) 2006-2012 Sawtooth Consulting Ltd.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */


#ifndef NO_HC128

#ifndef CTAO_CRYPT_HC128_H
#define CTAO_CRYPT_HC128_H

#include <cyassl/ctaocrypt/types.h>

#ifdef __cplusplus
    extern "C" {
#endif


enum {
	HC128_ENC_TYPE    =  6    /* cipher unique type */
};

/* HC-128 stream cipher */
typedef struct HC128 {
    word32 T[1024];             /* P[i] = T[i];  Q[i] = T[1024 + i ]; */
    word32 X[16];
    word32 Y[16];
    word32 counter1024;         /* counter1024 = i mod 1024 at the ith step */
    word32 key[8];
    word32 iv[8];
} HC128;


CYASSL_API void Hc128_Process(HC128*, byte*, const byte*, word32);
CYASSL_API void Hc128_SetKey(HC128*, const byte* key, const byte* iv);


#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* CTAO_CRYPT_HC128_H */

#endif /* HAVE_HC128 */
