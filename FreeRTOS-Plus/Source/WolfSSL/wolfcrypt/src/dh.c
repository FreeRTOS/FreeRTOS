/* dh.c
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

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#ifndef NO_DH

#include <wolfssl/wolfcrypt/dh.h>
#include <wolfssl/wolfcrypt/error-crypt.h>

#ifndef USER_MATH_LIB
    #include <math.h>
    #define XPOW(x,y) pow((x),(y))
    #define XLOG(x)   log((x))
#else
    /* user's own math lib */
#endif


#ifndef WOLFSSL_HAVE_MIN
#define WOLFSSL_HAVE_MIN

    static INLINE word32 min(word32 a, word32 b)
    {
        return a > b ? b : a;
    }

#endif /* WOLFSSL_HAVE_MIN */


void wc_InitDhKey(DhKey* key)
{
    (void)key;
/* TomsFastMath doesn't use memory allocation */
#ifndef USE_FAST_MATH
    key->p.dp = 0;
    key->g.dp = 0;
#endif
}


void wc_FreeDhKey(DhKey* key)
{
    (void)key;
/* TomsFastMath doesn't use memory allocation */
#ifndef USE_FAST_MATH
    mp_clear(&key->p);
    mp_clear(&key->g);
#endif
}


static word32 DiscreteLogWorkFactor(word32 n)
{
    /* assuming discrete log takes about the same time as factoring */
    if (n<5)
        return 0;
    else
        return (word32)(2.4 * XPOW((double)n, 1.0/3.0) *
                XPOW(XLOG((double)n), 2.0/3.0) - 5);
}


static int GeneratePrivate(DhKey* key, RNG* rng, byte* priv, word32* privSz)
{
    int ret;
    word32 sz = mp_unsigned_bin_size(&key->p);
    sz = min(sz, 2 * DiscreteLogWorkFactor(sz * WOLFSSL_BIT_SIZE) /
                                           WOLFSSL_BIT_SIZE + 1);

    ret = wc_RNG_GenerateBlock(rng, priv, sz);
    if (ret != 0)
        return ret;

    priv[0] |= 0x0C;

    *privSz = sz;

    return 0;
}


static int GeneratePublic(DhKey* key, const byte* priv, word32 privSz,
                          byte* pub, word32* pubSz)
{
    int ret = 0;

    mp_int x; 
    mp_int y;

    if (mp_init_multi(&x, &y, 0, 0, 0, 0) != MP_OKAY)
        return MP_INIT_E;

    if (mp_read_unsigned_bin(&x, priv, privSz) != MP_OKAY)
        ret = MP_READ_E;

    if (ret == 0 && mp_exptmod(&key->g, &x, &key->p, &y) != MP_OKAY)
        ret = MP_EXPTMOD_E;

    if (ret == 0 && mp_to_unsigned_bin(&y, pub) != MP_OKAY)
        ret = MP_TO_E;

    if (ret == 0)
        *pubSz = mp_unsigned_bin_size(&y);

    mp_clear(&y);
    mp_clear(&x);

    return ret;
}


int wc_DhGenerateKeyPair(DhKey* key, RNG* rng, byte* priv, word32* privSz,
                      byte* pub, word32* pubSz)
{
    int ret = GeneratePrivate(key, rng, priv, privSz);

    return (ret != 0) ? ret : GeneratePublic(key, priv, *privSz, pub, pubSz);
}

int wc_DhAgree(DhKey* key, byte* agree, word32* agreeSz, const byte* priv,
            word32 privSz, const byte* otherPub, word32 pubSz)
{
    int ret = 0;

    mp_int x; 
    mp_int y;
    mp_int z;

    if (mp_init_multi(&x, &y, &z, 0, 0, 0) != MP_OKAY)
        return MP_INIT_E;

    if (mp_read_unsigned_bin(&x, priv, privSz) != MP_OKAY)
        ret = MP_READ_E;

    if (ret == 0 && mp_read_unsigned_bin(&y, otherPub, pubSz) != MP_OKAY)
        ret = MP_READ_E;

    if (ret == 0 && mp_exptmod(&y, &x, &key->p, &z) != MP_OKAY)
        ret = MP_EXPTMOD_E;

    if (ret == 0 && mp_to_unsigned_bin(&z, agree) != MP_OKAY)
        ret = MP_TO_E;

    if (ret == 0)
        *agreeSz = mp_unsigned_bin_size(&z);

    mp_clear(&z);
    mp_clear(&y);
    mp_clear(&x);

    return ret;
}


/* not in asn anymore since no actual asn types used */
int wc_DhSetKey(DhKey* key, const byte* p, word32 pSz, const byte* g,
                word32 gSz)
{
    if (key == NULL || p == NULL || g == NULL || pSz == 0 || gSz == 0)
        return BAD_FUNC_ARG;

    /* may have leading 0 */
    if (p[0] == 0) {
        pSz--; p++;
    }

    if (g[0] == 0) {
        gSz--; g++;
    }

    if (mp_init(&key->p) != MP_OKAY)
        return MP_INIT_E;
    if (mp_read_unsigned_bin(&key->p, p, pSz) != 0) {
        mp_clear(&key->p);
        return ASN_DH_KEY_E;
    }

    if (mp_init(&key->g) != MP_OKAY) {
        mp_clear(&key->p);
        return MP_INIT_E;
    }
    if (mp_read_unsigned_bin(&key->g, g, gSz) != 0) {
        mp_clear(&key->g);
        mp_clear(&key->p);
        return ASN_DH_KEY_E;
    }

    return 0;
}


#endif /* NO_DH */

