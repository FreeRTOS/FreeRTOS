/* ge_operations.h
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

 /* Based On Daniel J Bernstein's ed25519 Public Domain ref10 work. */

#ifndef WOLF_CRYPT_GE_OPERATIONS_H
#define WOLF_CRYPT_GE_OPERATIONS_H

#include <wolfssl/wolfcrypt/settings.h>

#ifdef HAVE_ED25519

#ifndef CURVED25519_SMALL
    #include <stdint.h>
#endif
#include <wolfssl/wolfcrypt/fe_operations.h>

/*
ge means group element.

Here the group is the set of pairs (x,y) of field elements (see fe.h)
satisfying -x^2 + y^2 = 1 + d x^2y^2
where d = -121665/121666.

Representations:
  ge_p2 (projective): (X:Y:Z) satisfying x=X/Z, y=Y/Z
  ge_p3 (extended): (X:Y:Z:T) satisfying x=X/Z, y=Y/Z, XY=ZT
  ge_p1p1 (completed): ((X:Z),(Y:T)) satisfying x=X/Z, y=Y/T
  ge_precomp (Duif): (y+x,y-x,2dxy)
*/


typedef struct {
  fe X;
  fe Y;
  fe Z;
} ge_p2;

typedef struct {
  fe X;
  fe Y;
  fe Z;
  fe T;
} ge_p3;

WOLFSSL_LOCAL int  ge_compress_key(byte* out, const byte* xIn, const byte* yIn,
                                                                word32 keySz);
WOLFSSL_LOCAL int  ge_frombytes_negate_vartime(ge_p3 *,const unsigned char *);

WOLFSSL_LOCAL int  ge_double_scalarmult_vartime(ge_p2 *,const unsigned char *,
                                         const ge_p3 *,const unsigned char *);
WOLFSSL_LOCAL void ge_scalarmult_base(ge_p3 *,const unsigned char *);
WOLFSSL_LOCAL void sc_reduce(byte* s);
WOLFSSL_LOCAL void sc_muladd(byte* s, const byte* a, const byte* b,
                             const byte* c);
WOLFSSL_LOCAL void ge_tobytes(unsigned char *,const ge_p2 *);
WOLFSSL_LOCAL void ge_p3_tobytes(unsigned char *,const ge_p3 *);

#ifndef CURVED25519_SMALL
typedef struct {
  fe X;
  fe Y;
  fe Z;
  fe T;
} ge_p1p1;

typedef struct {
  fe yplusx;
  fe yminusx;
  fe xy2d;
} ge_precomp;

typedef struct {
  fe YplusX;
  fe YminusX;
  fe Z;
  fe T2d;
} ge_cached;

WOLFSSL_LOCAL void ge_p2_0(ge_p2 *);
WOLFSSL_LOCAL void ge_p3_0(ge_p3 *);
WOLFSSL_LOCAL void ge_precomp_0(ge_precomp *);
WOLFSSL_LOCAL void ge_p3_to_p2(ge_p2 *,const ge_p3 *);
WOLFSSL_LOCAL void ge_p3_to_cached(ge_cached *,const ge_p3 *);
WOLFSSL_LOCAL void ge_p1p1_to_p2(ge_p2 *,const ge_p1p1 *);
WOLFSSL_LOCAL void ge_p1p1_to_p3(ge_p3 *,const ge_p1p1 *);
WOLFSSL_LOCAL void ge_p2_dbl(ge_p1p1 *,const ge_p2 *);
WOLFSSL_LOCAL void ge_p3_dbl(ge_p1p1 *,const ge_p3 *);

WOLFSSL_LOCAL void ge_madd(ge_p1p1 *,const ge_p3 *,const ge_precomp *);
WOLFSSL_LOCAL void ge_msub(ge_p1p1 *,const ge_p3 *,const ge_precomp *);
WOLFSSL_LOCAL void ge_add(ge_p1p1 *,const ge_p3 *,const ge_cached *);
WOLFSSL_LOCAL void ge_sub(ge_p1p1 *,const ge_p3 *,const ge_cached *);
#endif /* no CURVED25519_SMALL */
#endif /* HAVE_ED25519 */
#endif /* WOLF_CRYPT_GE_OPERATIONS_H */

