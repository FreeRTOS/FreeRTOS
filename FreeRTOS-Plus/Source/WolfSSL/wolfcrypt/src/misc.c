/* misc.c
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


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#ifndef WOLF_CRYPT_MISC_C
#define WOLF_CRYPT_MISC_C

#include <wolfssl/wolfcrypt/misc.h>

/* inlining these functions is a huge speed increase and a small size decrease,
   because the functions are smaller than function call setup/cleanup, e.g.,
   md5 benchmark is twice as fast with inline.  If you don't want it, then
   define NO_INLINE and compile this file into wolfssl, otherwise it's used as
   a source header
 */

#ifdef NO_INLINE
    #define WC_STATIC
#else
    #define WC_STATIC static
#endif

/* Check for if compiling misc.c when not needed. */
#if !defined(WOLFSSL_MISC_INCLUDED) && !defined(NO_INLINE)
    #ifndef WOLFSSL_IGNORE_FILE_WARN
   //     #warning misc.c does not need to be compiled when using inline (NO_INLINE not defined)
    #endif

#else


#if defined(__ICCARM__)
    #include <intrinsics.h>
#endif


#ifdef INTEL_INTRINSICS

    #include <stdlib.h>      /* get intrinsic definitions */

    /* for non visual studio probably need no long version, 32 bit only
     * i.e., _rotl and _rotr */
    #pragma intrinsic(_lrotl, _lrotr)

    WC_STATIC WC_INLINE word32 rotlFixed(word32 x, word32 y)
    {
        return y ? _lrotl(x, y) : x;
    }

    WC_STATIC WC_INLINE word32 rotrFixed(word32 x, word32 y)
    {
        return y ? _lrotr(x, y) : x;
    }

#else /* generic */

    WC_STATIC WC_INLINE word32 rotlFixed(word32 x, word32 y)
    {
        return (x << y) | (x >> (sizeof(y) * 8 - y));
    }


    WC_STATIC WC_INLINE word32 rotrFixed(word32 x, word32 y)
    {
        return (x >> y) | (x << (sizeof(y) * 8 - y));
    }

#endif


WC_STATIC WC_INLINE word32 ByteReverseWord32(word32 value)
{
#ifdef PPC_INTRINSICS
    /* PPC: load reverse indexed instruction */
    return (word32)__lwbrx(&value,0);
#elif defined(__ICCARM__)
    return (word32)__REV(value);
#elif defined(KEIL_INTRINSICS)
    return (word32)__rev(value);
#elif defined(WOLF_ALLOW_BUILTIN) && \
        defined(__GNUC_PREREQ) && __GNUC_PREREQ(4, 3)
    return (word32)__builtin_bswap32(value);
#elif defined(FAST_ROTATE)
    /* 5 instructions with rotate instruction, 9 without */
    return (rotrFixed(value, 8U) & 0xff00ff00) |
           (rotlFixed(value, 8U) & 0x00ff00ff);
#else
    /* 6 instructions with rotate instruction, 8 without */
    value = ((value & 0xFF00FF00) >> 8) | ((value & 0x00FF00FF) << 8);
    return rotlFixed(value, 16U);
#endif
}


WC_STATIC WC_INLINE void ByteReverseWords(word32* out, const word32* in,
                                    word32 byteCount)
{
    word32 count = byteCount/(word32)sizeof(word32), i;

    for (i = 0; i < count; i++)
        out[i] = ByteReverseWord32(in[i]);

}


#if defined(WORD64_AVAILABLE) && !defined(WOLFSSL_NO_WORD64_OPS)


WC_STATIC WC_INLINE word64 rotlFixed64(word64 x, word64 y)
{
    return (x << y) | (x >> (sizeof(y) * 8 - y));
}


WC_STATIC WC_INLINE word64 rotrFixed64(word64 x, word64 y)
{
    return (x >> y) | (x << (sizeof(y) * 8 - y));
}


WC_STATIC WC_INLINE word64 ByteReverseWord64(word64 value)
{
#if defined(WOLF_ALLOW_BUILTIN) && defined(__GNUC_PREREQ) && __GNUC_PREREQ(4, 3)
    return (word64)__builtin_bswap64(value);
#elif defined(WOLFCRYPT_SLOW_WORD64)
	return (word64)((word64)ByteReverseWord32((word32) value)) << 32 |
                    (word64)ByteReverseWord32((word32)(value   >> 32));
#else
	value = ((value & W64LIT(0xFF00FF00FF00FF00)) >> 8) |
            ((value & W64LIT(0x00FF00FF00FF00FF)) << 8);
	value = ((value & W64LIT(0xFFFF0000FFFF0000)) >> 16) |
            ((value & W64LIT(0x0000FFFF0000FFFF)) << 16);
	return rotlFixed64(value, 32U);
#endif
}


WC_STATIC WC_INLINE void ByteReverseWords64(word64* out, const word64* in,
                                      word32 byteCount)
{
    word32 count = byteCount/(word32)sizeof(word64), i;

    for (i = 0; i < count; i++)
        out[i] = ByteReverseWord64(in[i]);

}

#endif /* WORD64_AVAILABLE && !WOLFSSL_NO_WORD64_OPS */

#ifndef WOLFSSL_NO_XOR_OPS
WC_STATIC WC_INLINE void XorWords(wolfssl_word* r, const wolfssl_word* a, word32 n)
{
    word32 i;

    for (i = 0; i < n; i++) r[i] ^= a[i];
}


WC_STATIC WC_INLINE void xorbuf(void* buf, const void* mask, word32 count)
{
    if (((wolfssl_word)buf | (wolfssl_word)mask | count) % WOLFSSL_WORD_SIZE == 0)
        XorWords( (wolfssl_word*)buf,
                  (const wolfssl_word*)mask, count / WOLFSSL_WORD_SIZE);
    else {
        word32 i;
        byte*       b = (byte*)buf;
        const byte* m = (const byte*)mask;

        for (i = 0; i < count; i++) b[i] ^= m[i];
    }
}
#endif

#ifndef WOLFSSL_NO_FORCE_ZERO
/* Make sure compiler doesn't skip */
WC_STATIC WC_INLINE void ForceZero(const void* mem, word32 len)
{
    volatile byte* z = (volatile byte*)mem;

#if defined(WOLFSSL_X86_64_BUILD) && defined(WORD64_AVAILABLE)
    volatile word64* w;
    #ifndef WOLFSSL_UNALIGNED_64BIT_ACCESS
        word32 l = (sizeof(word64) - ((size_t)z & (sizeof(word64)-1))) &
                                                             (sizeof(word64)-1);

        if (len < l) l = len;
        len -= l;
        while (l--) *z++ = 0;
    #endif
    for (w = (volatile word64*)z; len >= sizeof(*w); len -= sizeof(*w))
        *w++ = 0;
    z = (volatile byte*)w;
#endif

    while (len--) *z++ = 0;
}
#endif


#ifndef WOLFSSL_NO_CONST_CMP
/* check all length bytes for equality, return 0 on success */
WC_STATIC WC_INLINE int ConstantCompare(const byte* a, const byte* b, int length)
{
    int i;
    int compareSum = 0;

    for (i = 0; i < length; i++) {
        compareSum |= a[i] ^ b[i];
    }

    return compareSum;
}
#endif


#ifndef WOLFSSL_HAVE_MIN
    #define WOLFSSL_HAVE_MIN
    #if defined(HAVE_FIPS) && !defined(min) /* so ifdef check passes */
        #define min min
    #endif
    WC_STATIC WC_INLINE word32 min(word32 a, word32 b)
    {
        return a > b ? b : a;
    }
#endif /* !WOLFSSL_HAVE_MIN */

#ifndef WOLFSSL_HAVE_MAX
    #define WOLFSSL_HAVE_MAX
    #if defined(HAVE_FIPS) && !defined(max) /* so ifdef check passes */
        #define max max
    #endif
    WC_STATIC WC_INLINE word32 max(word32 a, word32 b)
    {
        return a > b ? a : b;
    }
#endif /* !WOLFSSL_HAVE_MAX */

#ifndef WOLFSSL_NO_INT_ENCODE
/* converts a 32 bit integer to 24 bit */
WC_STATIC WC_INLINE void c32to24(word32 in, word24 out)
{
    out[0] = (in >> 16) & 0xff;
    out[1] = (in >>  8) & 0xff;
    out[2] =  in & 0xff;
}

/* convert 16 bit integer to opaque */
WC_STATIC WC_INLINE void c16toa(word16 wc_u16, byte* c)
{
    c[0] = (wc_u16 >> 8) & 0xff;
    c[1] =  wc_u16 & 0xff;
}

/* convert 32 bit integer to opaque */
WC_STATIC WC_INLINE void c32toa(word32 wc_u32, byte* c)
{
    c[0] = (wc_u32 >> 24) & 0xff;
    c[1] = (wc_u32 >> 16) & 0xff;
    c[2] = (wc_u32 >>  8) & 0xff;
    c[3] =  wc_u32 & 0xff;
}
#endif

#ifndef WOLFSSL_NO_INT_DECODE
/* convert a 24 bit integer into a 32 bit one */
WC_STATIC WC_INLINE void c24to32(const word24 wc_u24, word32* wc_u32)
{
    *wc_u32 = ((word32)wc_u24[0] << 16) | (wc_u24[1] << 8) | wc_u24[2];
}


/* convert opaque to 24 bit integer */
WC_STATIC WC_INLINE void ato24(const byte* c, word32* wc_u24)
{
    *wc_u24 = ((word32)c[0] << 16) | (c[1] << 8) | c[2];
}

/* convert opaque to 16 bit integer */
WC_STATIC WC_INLINE void ato16(const byte* c, word16* wc_u16)
{
    *wc_u16 = (word16) ((c[0] << 8) | (c[1]));
}

/* convert opaque to 32 bit integer */
WC_STATIC WC_INLINE void ato32(const byte* c, word32* wc_u32)
{
    *wc_u32 = ((word32)c[0] << 24) | ((word32)c[1] << 16) | (c[2] << 8) | c[3];
}


WC_STATIC WC_INLINE word32 btoi(byte b)
{
    return (word32)(b - 0x30);
}
#endif


#ifndef WOLFSSL_NO_CT_OPS
/* Constant time - mask set when a > b. */
WC_STATIC WC_INLINE byte ctMaskGT(int a, int b)
{
    return (((word32)a - b - 1) >> 31) - 1;
}

/* Constant time - mask set when a >= b. */
WC_STATIC WC_INLINE byte ctMaskGTE(int a, int b)
{
    return (((word32)a - b    ) >> 31) - 1;
}

/* Constant time - mask set when a >= b. */
WC_STATIC WC_INLINE int ctMaskIntGTE(int a, int b)
{
    return (((word32)a - b    ) >> 31) - 1;
}

/* Constant time - mask set when a < b. */
WC_STATIC WC_INLINE byte ctMaskLT(int a, int b)
{
    return (((word32)b - a - 1) >> 31) - 1;
}

/* Constant time - mask set when a <= b. */
WC_STATIC WC_INLINE byte ctMaskLTE(int a, int b)
{
    return (((word32)b - a    ) >> 31) - 1;
}

/* Constant time - mask set when a == b. */
WC_STATIC WC_INLINE byte ctMaskEq(int a, int b)
{
    return (~ctMaskGT(a, b)) & (~ctMaskLT(a, b));
}

WC_STATIC WC_INLINE word16 ctMask16GT(int a, int b)
{
    return (((word32)a - b - 1) >> 31) - 1;
}

WC_STATIC WC_INLINE word16 ctMask16LT(int a, int b)
{
    return (((word32)a - b - 1) >> 31) - 1;
}

WC_STATIC WC_INLINE word16 ctMask16Eq(int a, int b)
{
    return (~ctMask16GT(a, b)) & (~ctMask16LT(a, b));
}

/* Constant time - mask set when a != b. */
WC_STATIC WC_INLINE byte ctMaskNotEq(int a, int b)
{
    return ctMaskGT(a, b) | ctMaskLT(a, b);
}

/* Constant time - select a when mask is set and b otherwise. */
WC_STATIC WC_INLINE byte ctMaskSel(byte m, byte a, byte b)
{
    return (b & ((byte)~(word32)m)) | (a & m);
}

/* Constant time - select integer a when mask is set and integer b otherwise. */
WC_STATIC WC_INLINE int ctMaskSelInt(byte m, int a, int b)
{
    return (b & (~(signed int)(signed char)m)) |
           (a & ( (signed int)(signed char)m));
}

/* Constant time - bit set when a <= b. */
WC_STATIC WC_INLINE byte ctSetLTE(int a, int b)
{
    return ((word32)a - b - 1) >> 31;
}
#endif


#undef WC_STATIC

#endif /* !WOLFSSL_MISC_INCLUDED && !NO_INLINE */

#endif /* WOLF_CRYPT_MISC_C */
