/* fe448_448.h
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */


#ifndef WOLF_CRYPT_FE_448_H
#define WOLF_CRYPT_FE_448_H

#include <wolfssl/wolfcrypt/settings.h>

#if defined(HAVE_CURVE448) || defined(HAVE_ED448)

#include <stdint.h>

#include <wolfssl/wolfcrypt/types.h>

#if defined(HAVE___UINT128_T) && !defined(NO_CURVED448_128BIT)
    #define CURVED448_128BIT
#endif

#ifdef __cplusplus
    extern "C" {
#endif

/* default to be faster but take more memory */
#if !defined(CURVE448_SMALL) || !defined(ED448_SMALL)

#if defined(CURVED448_128BIT)
    typedef int64_t fe448;
    #ifdef __SIZEOF_INT128__
        typedef __uint128_t uint128_t;
        typedef __int128_t int128_t;
    #else
        typedef unsigned long uint128_t __attribute__ ((mode(TI)));
        typedef long int128_t __attribute__ ((mode(TI)));
    #endif
#else
    typedef int32_t fe448;
#endif

WOLFSSL_LOCAL void fe448_init(void);
WOLFSSL_LOCAL int  curve448(byte* r, const byte* n, const byte* a);

#if !defined(CURVED448_128BIT)
WOLFSSL_LOCAL void fe448_reduce(fe448*);
#else
#define fe448_reduce(a)
#endif
WOLFSSL_LOCAL void fe448_neg(fe448*,const fe448*);
WOLFSSL_LOCAL void fe448_add(fe448*, const fe448*, const fe448*);
WOLFSSL_LOCAL void fe448_sub(fe448*, const fe448*, const fe448*);
WOLFSSL_LOCAL void fe448_mul(fe448*,const fe448*,const fe448*);
WOLFSSL_LOCAL void fe448_sqr(fe448*, const fe448*);
WOLFSSL_LOCAL void fe448_mul39081(fe448*, const fe448*);
WOLFSSL_LOCAL void fe448_invert(fe448*, const fe448*);

WOLFSSL_LOCAL void fe448_0(fe448*);
WOLFSSL_LOCAL void fe448_1(fe448*);
WOLFSSL_LOCAL void fe448_copy(fe448*, const fe448*);
WOLFSSL_LOCAL int  fe448_isnonzero(const fe448*);
WOLFSSL_LOCAL int  fe448_isnegative(const fe448*);

WOLFSSL_LOCAL void fe448_from_bytes(fe448*,const unsigned char *);
WOLFSSL_LOCAL void fe448_to_bytes(unsigned char *, const fe448*);

WOLFSSL_LOCAL void fe448_cmov(fe448*,const fe448*, int);
WOLFSSL_LOCAL void fe448_pow_2_446_222_1(fe448*,const fe448*);

#else

WOLFSSL_LOCAL void fe448_init(void);
WOLFSSL_LOCAL int  curve448(byte* r, const byte* n, const byte* a);

#define fe448_reduce(a)
WOLFSSL_LOCAL void fe448_neg(uint8_t*,const uint8_t*);
WOLFSSL_LOCAL void fe448_add(uint8_t*, const uint8_t*, const uint8_t*);
WOLFSSL_LOCAL void fe448_sub(uint8_t*, const uint8_t*, const uint8_t*);
WOLFSSL_LOCAL void fe448_mul(uint8_t*,const uint8_t*,const uint8_t*);
WOLFSSL_LOCAL void fe448_sqr(uint8_t*, const uint8_t*);
WOLFSSL_LOCAL void fe448_mul39081(uint8_t*, const uint8_t*);
WOLFSSL_LOCAL void fe448_invert(uint8_t*, const uint8_t*);

WOLFSSL_LOCAL void fe448_copy(uint8_t*, const uint8_t*);
WOLFSSL_LOCAL int  fe448_isnonzero(const uint8_t*);

WOLFSSL_LOCAL void fe448_norm(byte *a);

WOLFSSL_LOCAL void fe448_cmov(uint8_t*,const uint8_t*, int);
WOLFSSL_LOCAL void fe448_pow_2_446_222_1(uint8_t*,const uint8_t*);

#endif /* !CURVE448_SMALL || !ED448_SMALL */

#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* HAVE_CURVE448 || HAVE_ED448 */

#endif /* WOLF_CRYPT_FE_448_H */
