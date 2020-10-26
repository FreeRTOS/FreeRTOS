/* ge_448.h
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


#ifndef WOLF_CRYPT_GE_448_H
#define WOLF_CRYPT_GE_448_H

#include <wolfssl/wolfcrypt/settings.h>

#ifdef HAVE_ED448

#include <wolfssl/wolfcrypt/fe_448.h>

/*
ge448 means group element.

Here the group is the set of pairs (x,y) of field elements (see fe.h)
satisfying -x^2 + y^2 = 1 + d x^2y^2
where d = -39081.

Representations:
  ge448_p2 (projective) : (X:Y:Z) satisfying x=X/Z, y=Y/Z
  ge448_precomp (affine): (x,y)
*/

#ifdef ED448_SMALL
    typedef byte     ge448;
    #define GE448_WORDS    56
#elif defined(CURVED448_128BIT)
    typedef int64_t  ge448;
    #define GE448_WORDS    8
#else
    typedef int32_t  ge448;
    #define GE448_WORDS    16
#endif

typedef struct {
  ge448 X[GE448_WORDS];
  ge448 Y[GE448_WORDS];
  ge448 Z[GE448_WORDS];
} ge448_p2;


WOLFSSL_LOCAL int  ge448_compress_key(byte*, const byte*, const byte*);
WOLFSSL_LOCAL int  ge448_from_bytes_negate_vartime(ge448_p2 *,
                                                   const unsigned char *);

WOLFSSL_LOCAL int  ge448_double_scalarmult_vartime(ge448_p2 *,
                                                   const unsigned char *,
                                                   const ge448_p2 *,
                                                   const unsigned char *);
WOLFSSL_LOCAL void ge448_scalarmult_base(ge448_p2 *, const unsigned char *);
WOLFSSL_LOCAL void sc448_reduce(byte*);
WOLFSSL_LOCAL void sc448_muladd(byte*, const byte*, const byte*, const byte*);
WOLFSSL_LOCAL void ge448_to_bytes(unsigned char *, const ge448_p2 *);


#ifndef ED448_SMALL
typedef struct {
  ge448 x[GE448_WORDS];
  ge448 y[GE448_WORDS];
} ge448_precomp;

#endif /* !ED448_SMALL */

#endif /* HAVE_ED448 */

#endif /* WOLF_CRYPT_GE_448_H */
