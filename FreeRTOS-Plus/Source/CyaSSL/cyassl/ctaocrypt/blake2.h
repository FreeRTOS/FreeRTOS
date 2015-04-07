/* blake2.h
 *
 * Copyright (C) 2006-2014 wolfSSL Inc.
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */


#ifdef HAVE_BLAKE2

#ifndef CTAOCRYPT_BLAKE2_H
#define CTAOCRYPT_BLAKE2_H

#include <cyassl/ctaocrypt/blake2-int.h>

#ifdef __cplusplus
    extern "C" {
#endif

/* in bytes, variable digest size up to 512 bits (64 bytes) */
enum {
    BLAKE2B_ID  = 7,   /* hash type unique */
    BLAKE2B_256 = 32   /* 256 bit type, SSL default */
};


/* BLAKE2b digest */
typedef struct Blake2b {
    blake2b_state S[1];         /* our state */
    word32        digestSz;     /* digest size used on init */
} Blake2b;


CYASSL_API int InitBlake2b(Blake2b*, word32);
CYASSL_API int Blake2bUpdate(Blake2b*, const byte*, word32);
CYASSL_API int Blake2bFinal(Blake2b*, byte*, word32);



#ifdef __cplusplus
    } 
#endif

#endif  /* CTAOCRYPT_BLAKE2_H */
#endif  /* HAVE_BLAKE2 */

