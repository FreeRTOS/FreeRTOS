/* misc.h
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
/*

DESCRIPTION
This module implements the arithmetic-shift right, left, byte swapping, XOR,
masking and clearing memory logic.

*/
#ifndef WOLF_CRYPT_MISC_H
#define WOLF_CRYPT_MISC_H


#include <wolfssl/wolfcrypt/types.h>


#ifdef __cplusplus
    extern "C" {
#endif


#ifdef NO_INLINE
WOLFSSL_LOCAL
word32 rotlFixed(word32, word32);
WOLFSSL_LOCAL
word32 rotrFixed(word32, word32);

WOLFSSL_LOCAL
word32 ByteReverseWord32(word32);
WOLFSSL_LOCAL
void   ByteReverseWords(word32*, const word32*, word32);

WOLFSSL_LOCAL
void XorWords(wolfssl_word*, const wolfssl_word*, word32);
WOLFSSL_LOCAL
void xorbuf(void*, const void*, word32);

WOLFSSL_LOCAL
void ForceZero(const void*, word32);

WOLFSSL_LOCAL
int ConstantCompare(const byte*, const byte*, int);

#ifdef WORD64_AVAILABLE
WOLFSSL_LOCAL
word64 rotlFixed64(word64, word64);
WOLFSSL_LOCAL
word64 rotrFixed64(word64, word64);

WOLFSSL_LOCAL
word64 ByteReverseWord64(word64);
WOLFSSL_LOCAL
void   ByteReverseWords64(word64*, const word64*, word32);
#endif /* WORD64_AVAILABLE */

#ifndef WOLFSSL_HAVE_MIN
    #if defined(HAVE_FIPS) && !defined(min) /* so ifdef check passes */
        #define min min
    #endif
    WOLFSSL_LOCAL word32 min(word32 a, word32 b);
#endif

#ifndef WOLFSSL_HAVE_MAX
    #if defined(HAVE_FIPS) && !defined(max) /* so ifdef check passes */
        #define max max
    #endif
    WOLFSSL_LOCAL word32 max(word32 a, word32 b);
#endif /* WOLFSSL_HAVE_MAX */


void c32to24(word32 in, word24 out);
void c16toa(word16 u16, byte* c);
void c32toa(word32 u32, byte* c);
void c24to32(const word24 u24, word32* u32);
void ato16(const byte* c, word16* u16);
void ato24(const byte* c, word32* u24);
void ato32(const byte* c, word32* u32);
word32 btoi(byte b);


WOLFSSL_LOCAL byte ctMaskGT(int a, int b);
WOLFSSL_LOCAL byte ctMaskGTE(int a, int b);
WOLFSSL_LOCAL int  ctMaskIntGTE(int a, int b);
WOLFSSL_LOCAL byte ctMaskLT(int a, int b);
WOLFSSL_LOCAL byte ctMaskLTE(int a, int b);
WOLFSSL_LOCAL byte ctMaskEq(int a, int b);
WOLFSSL_LOCAL word16 ctMask16GT(int a, int b);
WOLFSSL_LOCAL word16 ctMask16LT(int a, int b);
WOLFSSL_LOCAL word16 ctMask16Eq(int a, int b);
WOLFSSL_LOCAL byte ctMaskNotEq(int a, int b);
WOLFSSL_LOCAL byte ctMaskSel(byte m, byte a, byte b);
WOLFSSL_LOCAL int  ctMaskSelInt(byte m, int a, int b);
WOLFSSL_LOCAL byte ctSetLTE(int a, int b);

#endif /* NO_INLINE */


#ifdef __cplusplus
    }   /* extern "C" */
#endif


#endif /* WOLF_CRYPT_MISC_H */

