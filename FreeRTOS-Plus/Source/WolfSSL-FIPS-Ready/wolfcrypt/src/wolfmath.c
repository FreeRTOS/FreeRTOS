/* wolfmath.c
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


/* common functions for either math library */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

/* in case user set USE_FAST_MATH there */
#include <wolfssl/wolfcrypt/settings.h>

#include <wolfssl/wolfcrypt/integer.h>

#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/logging.h>

#if defined(USE_FAST_MATH) || !defined(NO_BIG_INT)

#ifdef WOLFSSL_ASYNC_CRYPT
    #include <wolfssl/wolfcrypt/async.h>
#endif

#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif


#if !defined(WC_NO_CACHE_RESISTANT) && \
    ((defined(HAVE_ECC) && defined(ECC_TIMING_RESISTANT)) || \
     (defined(USE_FAST_MATH) && defined(TFM_TIMING_RESISTANT)))

    /* all off / all on pointer addresses for constant calculations */
    /* ecc.c uses same table */
    const wolfssl_word wc_off_on_addr[2] =
    {
    #if defined(WC_64BIT_CPU)
        W64LIT(0x0000000000000000),
        W64LIT(0xffffffffffffffff)
    #elif defined(WC_16BIT_CPU)
        0x0000U,
        0xffffU
    #else
        /* 32 bit */
        0x00000000U,
        0xffffffffU
    #endif
    };
#endif


#if !defined(WOLFSSL_SP_MATH)
int get_digit_count(mp_int* a)
{
    if (a == NULL)
        return 0;

    return a->used;
}
#endif

mp_digit get_digit(mp_int* a, int n)
{
    if (a == NULL)
        return 0;

    return (n >= a->used || n < 0) ? 0 : a->dp[n];
}

/* Conditionally copy a into b. Performed in constant time.
 *
 * a     MP integer to copy.
 * copy  On 1, copy a into b. on 0 leave b unchanged.
 * b     MP integer to copy into.
 * returns BAD_FUNC_ARG when a or b is NULL, MEMORY_E when growing b fails and
 *         MP_OKAY otherwise.
 */
int mp_cond_copy(mp_int* a, int copy, mp_int* b)
{
    int err = MP_OKAY;
    int i;
    mp_digit mask = (mp_digit)0 - copy;

    if (a == NULL || b == NULL)
        err = BAD_FUNC_ARG;

    /* Ensure b has enough space to copy a into */
    if (err == MP_OKAY)
        err = mp_grow(b, a->used + 1);
    if (err == MP_OKAY) {
        /* When mask 0, b is unchanged2
         * When mask all set, b ^ b ^ a = a
         */
        /* Conditionaly copy all digits and then number of used diigits.
         * get_digit() returns 0 when index greater than available digit.
         */
        for (i = 0; i < a->used; i++) {
            b->dp[i] ^= (get_digit(a, i) ^ get_digit(b, i)) & mask;
        }
        for (; i < b->used; i++) {
            b->dp[i] ^= (get_digit(a, i) ^ get_digit(b, i)) & mask;
        }
        b->used ^= (a->used ^ b->used) & (int)mask;
    }

    return err;
}

#ifndef WC_NO_RNG
int get_rand_digit(WC_RNG* rng, mp_digit* d)
{
    return wc_RNG_GenerateBlock(rng, (byte*)d, sizeof(mp_digit));
}

#ifdef WC_RSA_BLINDING
int mp_rand(mp_int* a, int digits, WC_RNG* rng)
{
    int ret = 0;
    int cnt = digits * sizeof(mp_digit);
#if !defined(USE_FAST_MATH) && !defined(WOLFSSL_SP_MATH)
    int i;
#endif

    if (rng == NULL) {
        ret = MISSING_RNG_E;
    }
    else if (a == NULL || digits == 0) {
        ret = BAD_FUNC_ARG;
    }

#if !defined(USE_FAST_MATH) && !defined(WOLFSSL_SP_MATH)
    /* allocate space for digits */
    if (ret == MP_OKAY) {
        ret = mp_set_bit(a, digits * DIGIT_BIT - 1);
    }
#else
#if defined(WOLFSSL_SP_MATH)
    if ((ret == MP_OKAY) && (digits > SP_INT_DIGITS))
#else
    if ((ret == MP_OKAY) && (digits > FP_SIZE))
#endif
    {
        ret = BAD_FUNC_ARG;
    }
    if (ret == MP_OKAY) {
        a->used = digits;
    }
#endif
    /* fill the data with random bytes */
    if (ret == MP_OKAY) {
        ret = wc_RNG_GenerateBlock(rng, (byte*)a->dp, cnt);
    }
    if (ret == MP_OKAY) {
#if !defined(USE_FAST_MATH) && !defined(WOLFSSL_SP_MATH)
        /* Mask down each digit to only bits used */
        for (i = 0; i < a->used; i++) {
            a->dp[i] &= MP_MASK;
        }
#endif
        /* ensure top digit is not zero */
        while ((ret == MP_OKAY) && (a->dp[a->used - 1] == 0)) {
            ret = get_rand_digit(rng, &a->dp[a->used - 1]);
#if !defined(USE_FAST_MATH) && !defined(WOLFSSL_SP_MATH)
            a->dp[a->used - 1] &= MP_MASK;
#endif
        }
    }

    return ret;
}
#endif /* WC_RSA_BLINDING */
#endif

/* export an mp_int as unsigned char or hex string
 * encType is WC_TYPE_UNSIGNED_BIN or WC_TYPE_HEX_STR
 * return MP_OKAY on success */
int wc_export_int(mp_int* mp, byte* buf, word32* len, word32 keySz,
    int encType)
{
    int err;

    if (mp == NULL)
        return BAD_FUNC_ARG;

    /* check buffer size */
    if (*len < keySz) {
        *len = keySz;
        return BUFFER_E;
    }

    *len = keySz;
    XMEMSET(buf, 0, *len);

    if (encType == WC_TYPE_HEX_STR) {
    #ifdef WC_MP_TO_RADIX
        err = mp_tohex(mp, (char*)buf);
    #else
        err = NOT_COMPILED_IN;
    #endif
    }
    else {
        err = mp_to_unsigned_bin(mp, buf + (keySz - mp_unsigned_bin_size(mp)));
    }

    return err;
}


#ifdef HAVE_WOLF_BIGINT
void wc_bigint_init(WC_BIGINT* a)
{
    if (a != NULL) {
        a->buf = NULL;
        a->len = 0;
        a->heap = NULL;
    }
}

int wc_bigint_alloc(WC_BIGINT* a, word32 sz)
{
    int err = MP_OKAY;

    if (a == NULL)
        return BAD_FUNC_ARG;

    if (sz > 0) {
        if (a->buf && sz > a->len) {
            wc_bigint_free(a);
        }
        if (a->buf == NULL) {
            a->buf = (byte*)XMALLOC(sz, a->heap, DYNAMIC_TYPE_WOLF_BIGINT);
            if (a->buf == NULL) {
                err = MP_MEM;
            }
        }
        else {
            XMEMSET(a->buf, 0, sz);
        }
    }
    a->len = sz;

    return err;
}

/* assumes input is big endian format */
int wc_bigint_from_unsigned_bin(WC_BIGINT* a, const byte* in, word32 inlen)
{
    int err;

    if (a == NULL || in == NULL || inlen == 0)
        return BAD_FUNC_ARG;

    err = wc_bigint_alloc(a, inlen);
    if (err == 0) {
        XMEMCPY(a->buf, in, inlen);
    }

    return err;
}

int wc_bigint_to_unsigned_bin(WC_BIGINT* a, byte* out, word32* outlen)
{
    word32 sz;

    if (a == NULL || out == NULL || outlen == NULL || *outlen == 0)
        return BAD_FUNC_ARG;

    /* trim to fit into output buffer */
    sz = a->len;
    if (a->len > *outlen) {
        WOLFSSL_MSG("wc_bigint_export: Truncating output");
        sz = *outlen;
    }

    if (a->buf) {
        XMEMCPY(out, a->buf, sz);
    }

    *outlen = sz;

    return MP_OKAY;
}

void wc_bigint_zero(WC_BIGINT* a)
{
    if (a && a->buf) {
        ForceZero(a->buf, a->len);
    }
}

void wc_bigint_free(WC_BIGINT* a)
{
    if (a) {
        if (a->buf) {
          XFREE(a->buf, a->heap, DYNAMIC_TYPE_WOLF_BIGINT);
        }
        a->buf = NULL;
        a->len = 0;
    }
}

/* sz: make sure the buffer is at least that size and zero padded.
 *     A `sz == 0` will use the size of `src`.
 *     The calulcates sz is stored into dst->len in `wc_bigint_alloc`.
 */
int wc_mp_to_bigint_sz(mp_int* src, WC_BIGINT* dst, word32 sz)
{
    int err;
    word32 x, y;

    if (src == NULL || dst == NULL)
        return BAD_FUNC_ARG;

    /* get size of source */
    x = mp_unsigned_bin_size(src);
    if (sz < x)
        sz = x;

    /* make sure destination is allocated and large enough */
    err = wc_bigint_alloc(dst, sz);
    if (err == MP_OKAY) {

        /* leading zero pad */
        y = sz - x;
        XMEMSET(dst->buf, 0, y);

        /* export src as unsigned bin to destination buf */
        err = mp_to_unsigned_bin(src, dst->buf + y);
    }

    return err;
}

int wc_mp_to_bigint(mp_int* src, WC_BIGINT* dst)
{
    if (src == NULL || dst == NULL)
        return BAD_FUNC_ARG;

    return wc_mp_to_bigint_sz(src, dst, 0);
}

int wc_bigint_to_mp(WC_BIGINT* src, mp_int* dst)
{
    int err;

    if (src == NULL || dst == NULL)
        return BAD_FUNC_ARG;

    if (src->buf == NULL)
        return BAD_FUNC_ARG;

    err = mp_read_unsigned_bin(dst, src->buf, src->len);
    wc_bigint_free(src);

    return err;
}
#endif /* HAVE_WOLF_BIGINT */

#endif /* USE_FAST_MATH || !NO_BIG_INT */
