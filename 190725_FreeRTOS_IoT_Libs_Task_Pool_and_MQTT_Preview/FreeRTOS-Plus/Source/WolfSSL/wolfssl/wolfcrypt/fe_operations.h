/* fe_operations.h
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

#ifndef WOLF_CRYPT_FE_OPERATIONS_H
#define WOLF_CRYPT_FE_OPERATIONS_H

#include <wolfssl/wolfcrypt/settings.h>

#if defined(HAVE_CURVE25519) || defined(HAVE_ED25519)

#ifndef CURVED25519_SMALL
    #include <stdint.h>
#endif
#include <wolfssl/wolfcrypt/types.h>

/*
fe means field element.
Here the field is \Z/(2^255-19).
An element t, entries t[0]...t[9], represents the integer
t[0]+2^26 t[1]+2^51 t[2]+2^77 t[3]+2^102 t[4]+...+2^230 t[9].
Bounds on each t[i] vary depending on context.
*/

#ifdef CURVED25519_SMALL
    #define F25519_SIZE	32
    typedef byte     fe[32];
#else
    typedef int32_t  fe[10];
#endif

WOLFSSL_LOCAL int  curve25519(byte * q, byte * n, byte * p);
WOLFSSL_LOCAL void fe_copy(fe, const fe);
WOLFSSL_LOCAL void fe_add(fe, const fe, const fe);
WOLFSSL_LOCAL void fe_neg(fe,const fe);
WOLFSSL_LOCAL void fe_sub(fe, const fe, const fe);
WOLFSSL_LOCAL void fe_invert(fe, const fe);
WOLFSSL_LOCAL void fe_mul(fe,const fe,const fe);

/* default to be faster but take more memory */
#ifndef CURVED25519_SMALL

/* Based On Daniel J Bernstein's curve25519 and ed25519 Public Domain ref10
   work. */

WOLFSSL_LOCAL void fe_0(fe);
WOLFSSL_LOCAL void fe_1(fe);
WOLFSSL_LOCAL int  fe_isnonzero(const fe);
WOLFSSL_LOCAL int  fe_isnegative(const fe);
WOLFSSL_LOCAL void fe_tobytes(unsigned char *, const fe);
WOLFSSL_LOCAL void fe_sq(fe, const fe);
WOLFSSL_LOCAL void fe_sq2(fe,const fe);
WOLFSSL_LOCAL void fe_frombytes(fe,const unsigned char *);
WOLFSSL_LOCAL void fe_cswap(fe,fe,unsigned int);
WOLFSSL_LOCAL void fe_mul121666(fe,fe);
WOLFSSL_LOCAL void fe_cmov(fe,const fe,unsigned int);
WOLFSSL_LOCAL void fe_pow22523(fe,const fe);

/* 64 type needed for SHA512 */
WOLFSSL_LOCAL uint64_t load_3(const unsigned char *in);
WOLFSSL_LOCAL uint64_t load_4(const unsigned char *in);
#endif /* not defined CURVED25519_SMALL */

/* Use less memory and only 32bit types or less, but is slower
   Based on Daniel Beer's public domain work. */
#ifdef CURVED25519_SMALL
static const byte c25519_base_x[F25519_SIZE] = {9};
static const byte f25519_zero[F25519_SIZE]   = {0};
static const byte f25519_one[F25519_SIZE]    = {1};
static const byte fprime_zero[F25519_SIZE]   = {0};
static const byte fprime_one[F25519_SIZE]    = {1};

WOLFSSL_LOCAL void fe_load(byte *x, word32 c);
WOLFSSL_LOCAL void fe_normalize(byte *x);
WOLFSSL_LOCAL void fe_inv__distinct(byte *r, const byte *x);

/* Conditional copy. If condition == 0, then zero is copied to dst. If
 * condition == 1, then one is copied to dst. Any other value results in
 * undefined behaviour.
 */
WOLFSSL_LOCAL void fe_select(byte *dst, const byte *zero, const byte *one,
		   byte condition);

/* Multiply a point by a small constant. The two pointers are not
 * required to be distinct.
 *
 * The constant must be less than 2^24.
 */
WOLFSSL_LOCAL void fe_mul_c(byte *r, const byte *a, word32 b);
WOLFSSL_LOCAL void fe_mul__distinct(byte *r, const byte *a, const byte *b);

/* Compute one of the square roots of the field element, if the element
 * is square. The other square is -r.
 *
 * If the input is not square, the returned value is a valid field
 * element, but not the correct answer. If you don't already know that
 * your element is square, you should square the return value and test.
 */
WOLFSSL_LOCAL void fe_sqrt(byte *r, const byte *x);

/* Conditional copy. If condition == 0, then zero is copied to dst. If
 * condition == 1, then one is copied to dst. Any other value results in
 * undefined behaviour.
 */
WOLFSSL_LOCAL void fprime_select(byte *dst, const byte *zero, const byte *one,
		                         byte condition);
WOLFSSL_LOCAL void fprime_add(byte *r, const byte *a, const byte *modulus);
WOLFSSL_LOCAL void fprime_sub(byte *r, const byte *a, const byte *modulus);
WOLFSSL_LOCAL void fprime_mul(byte *r, const byte *a, const byte *b,
		                      const byte *modulus);
WOLFSSL_LOCAL void fprime_copy(byte *x, const byte *a);
#endif /* CURVED25519_SMALL */
#endif /* HAVE_CURVE25519 or HAVE_ED25519 */
#endif /* WOLF_CRYPT_FE_OPERATIONS_H */

