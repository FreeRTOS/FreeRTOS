/* dsa.c
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

#ifndef NO_DSA

#include <wolfssl/wolfcrypt/random.h>
#include <wolfssl/wolfcrypt/integer.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/logging.h>
#include <wolfssl/wolfcrypt/sha.h>
#include <wolfssl/wolfcrypt/dsa.h>

#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

int wc_InitDsaKey(DsaKey* key)
{
    if (key == NULL)
        return BAD_FUNC_ARG;

    key->type = -1;  /* haven't decided yet */
    key->heap = NULL;

    return mp_init_multi(
        /* public  alloc parts */
        &key->p,
        &key->q,
        &key->g,
        &key->y,

        /* private alloc parts */
        &key->x,
        NULL
    );
}


int wc_InitDsaKey_h(DsaKey* key, void* h)
{
    int ret = wc_InitDsaKey(key);
    if (ret == 0)
        key->heap = h;

    return ret;
}


void wc_FreeDsaKey(DsaKey* key)
{
    if (key == NULL)
        return;

    if (key->type == DSA_PRIVATE)
        mp_forcezero(&key->x);

    mp_clear(&key->x);
    mp_clear(&key->y);
    mp_clear(&key->g);
    mp_clear(&key->q);
    mp_clear(&key->p);
}


/* validate that (L,N) match allowed sizes from FIPS 186-4, Section 4.2.
 * modLen - represents L, the size of p (prime modulus) in bits
 * divLen - represents N, the size of q (prime divisor) in bits
 * return 0 on success, -1 on error */
static int CheckDsaLN(int modLen, int divLen)
{
    int ret = -1;

    switch (modLen) {
        case 1024:
            if (divLen == 160)
                ret = 0;
            break;
        case 2048:
            if (divLen == 224 || divLen == 256)
                ret = 0;
            break;
        case 3072:
            if (divLen == 256)
                ret = 0;
            break;
        default:
            break;
    }

    return ret;
}


#ifdef WOLFSSL_KEY_GEN

/* Create DSA key pair (&dsa->x, &dsa->y)
 *
 * Based on NIST FIPS 186-4,
 * "B.1.1 Key Pair Generation Using Extra Random Bits"
 *
 * rng - pointer to initialized WC_RNG structure
 * dsa - pointer to initialized DsaKey structure, will hold generated key
 *
 * return 0 on success, negative on error */
int wc_MakeDsaKey(WC_RNG *rng, DsaKey *dsa)
{
    byte* cBuf;
    int qSz, pSz, cSz, err;
    mp_int tmpQ;

    if (rng == NULL || dsa == NULL)
        return BAD_FUNC_ARG;

    qSz = mp_unsigned_bin_size(&dsa->q);
    pSz = mp_unsigned_bin_size(&dsa->p);

    /* verify (L,N) pair bit lengths */
    if (CheckDsaLN(pSz * WOLFSSL_BIT_SIZE, qSz * WOLFSSL_BIT_SIZE) != 0)
        return BAD_FUNC_ARG;

    /* generate extra 64 bits so that bias from mod function is negligible */
    cSz = qSz + (64 / WOLFSSL_BIT_SIZE);
    cBuf = (byte*)XMALLOC(cSz, dsa->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (cBuf == NULL) {
        return MEMORY_E;
    }

    if ((err = mp_init_multi(&dsa->x, &dsa->y, &tmpQ, NULL, NULL, NULL))
                   != MP_OKAY) {
        XFREE(cBuf, dsa->heap, DYNAMIC_TYPE_TMP_BUFFER);
        return err;
    }

    do {
        /* generate N+64 bits (c) from RBG into &dsa->x, making sure positive.
         * Hash_DRBG uses SHA-256 which matches maximum
         * requested_security_strength of (L,N) */
        err = wc_RNG_GenerateBlock(rng, cBuf, cSz);
        if (err != MP_OKAY) {
            mp_clear(&dsa->x);
            mp_clear(&dsa->y);
            mp_clear(&tmpQ);
            XFREE(cBuf, dsa->heap, DYNAMIC_TYPE_TMP_BUFFER);
            return err;
        }

        err = mp_read_unsigned_bin(&dsa->x, cBuf, cSz);
        if (err != MP_OKAY) {
            mp_clear(&dsa->x);
            mp_clear(&dsa->y);
            mp_clear(&tmpQ);
            XFREE(cBuf, dsa->heap, DYNAMIC_TYPE_TMP_BUFFER);
            return err;
        }
    } while (mp_cmp_d(&dsa->x, 1) != MP_GT);

    XFREE(cBuf, dsa->heap, DYNAMIC_TYPE_TMP_BUFFER);

    /* tmpQ = q - 1 */
    if (err == MP_OKAY)
        err = mp_copy(&dsa->q, &tmpQ);

    if (err == MP_OKAY)
        err = mp_sub_d(&tmpQ, 1, &tmpQ);

    /* x = c mod (q-1), &dsa->x holds c */
    if (err == MP_OKAY)
        err = mp_mod(&dsa->x, &tmpQ, &dsa->x);

    /* x = c mod (q-1) + 1 */
    if (err == MP_OKAY)
        err = mp_add_d(&dsa->x, 1, &dsa->x);

    /* public key : y = g^x mod p */
    if (err == MP_OKAY)
        err = mp_exptmod_ex(&dsa->g, &dsa->x, dsa->q.used, &dsa->p, &dsa->y);

    if (err == MP_OKAY)
        dsa->type = DSA_PRIVATE;

    if (err != MP_OKAY) {
        mp_clear(&dsa->x);
        mp_clear(&dsa->y);
    }
    mp_clear(&tmpQ);

    return err;
}


/* modulus_size in bits */
int wc_MakeDsaParameters(WC_RNG *rng, int modulus_size, DsaKey *dsa)
{
    mp_int  tmp, tmp2;
    int     err, msize, qsize,
            loop_check_prime = 0,
            check_prime = MP_NO;
    unsigned char   *buf;

    if (rng == NULL || dsa == NULL)
        return BAD_FUNC_ARG;

    /* set group size in bytes from modulus size
     * FIPS 186-4 defines valid values (1024, 160) (2048, 256) (3072, 256)
     */
    switch (modulus_size) {
        case 1024:
            qsize = 20;
            break;
        case 2048:
        case 3072:
            qsize = 32;
            break;
        default:
            return BAD_FUNC_ARG;
    }

    /* modulus size in bytes */
    msize = modulus_size / WOLFSSL_BIT_SIZE;

    /* allocate ram */
    buf = (unsigned char *)XMALLOC(msize - qsize,
                                   dsa->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (buf == NULL) {
        return MEMORY_E;
    }

    /* make a random string that will be multiplied against q */
    err = wc_RNG_GenerateBlock(rng, buf, msize - qsize);
    if (err != MP_OKAY) {
        XFREE(buf, dsa->heap, DYNAMIC_TYPE_TMP_BUFFER);
        return err;
    }

    /* force magnitude */
    buf[0] |= 0xC0;

    /* force even */
    buf[msize - qsize - 1] &= ~1;

    if (mp_init_multi(&tmp2, &dsa->p, &dsa->q, 0, 0, 0) != MP_OKAY) {
        mp_clear(&dsa->q);
        XFREE(buf, dsa->heap, DYNAMIC_TYPE_TMP_BUFFER);
        return MP_INIT_E;
    }

    err = mp_read_unsigned_bin(&tmp2, buf, msize - qsize);
    if (err != MP_OKAY) {
        mp_clear(&dsa->q);
        mp_clear(&dsa->p);
        mp_clear(&tmp2);
        XFREE(buf, dsa->heap, DYNAMIC_TYPE_TMP_BUFFER);
        return err;
    }
    XFREE(buf, dsa->heap, DYNAMIC_TYPE_TMP_BUFFER);

    /* make our prime q */
    err = mp_rand_prime(&dsa->q, qsize, rng, NULL);
    if (err != MP_OKAY) {
        mp_clear(&dsa->q);
        mp_clear(&dsa->p);
        mp_clear(&tmp2);
        return err;
    }

    /* p = random * q */
    err = mp_mul(&dsa->q, &tmp2, &dsa->p);
    if (err != MP_OKAY) {
        mp_clear(&dsa->q);
        mp_clear(&dsa->p);
        mp_clear(&tmp2);
        return err;
    }

    /* p = random * q + 1, so q is a prime divisor of p-1 */
    err = mp_add_d(&dsa->p, 1, &dsa->p);
    if (err != MP_OKAY) {
        mp_clear(&dsa->q);
        mp_clear(&dsa->p);
        mp_clear(&tmp2);
        return err;
    }

    if (mp_init(&tmp) != MP_OKAY) {
        mp_clear(&dsa->q);
        mp_clear(&dsa->p);
        mp_clear(&tmp2);
        return MP_INIT_E;
    }

    /* tmp = 2q  */
    err = mp_add(&dsa->q, &dsa->q, &tmp);
    if (err != MP_OKAY) {
        mp_clear(&dsa->q);
        mp_clear(&dsa->p);
        mp_clear(&tmp);
        mp_clear(&tmp2);
        return err;
    }

    /* loop until p is prime */
    while (check_prime == MP_NO) {
        err = mp_prime_is_prime_ex(&dsa->p, 8, &check_prime, rng);
        if (err != MP_OKAY) {
            mp_clear(&dsa->q);
            mp_clear(&dsa->p);
            mp_clear(&tmp);
            mp_clear(&tmp2);
            return err;
        }

        if (check_prime != MP_YES) {
            /* p += 2q */
            err = mp_add(&tmp, &dsa->p, &dsa->p);
            if (err != MP_OKAY) {
                mp_clear(&dsa->q);
                mp_clear(&dsa->p);
                mp_clear(&tmp);
                mp_clear(&tmp2);
                return err;
            }

            loop_check_prime++;
        }
    }

    /* tmp2 += (2*loop_check_prime)
     * to have p = (q * tmp2) + 1 prime
     */
    if (loop_check_prime) {
        err = mp_add_d(&tmp2, 2*loop_check_prime, &tmp2);
        if (err != MP_OKAY) {
            mp_clear(&dsa->q);
            mp_clear(&dsa->p);
            mp_clear(&tmp);
            mp_clear(&tmp2);
            return err;
        }
    }

    if (mp_init(&dsa->g) != MP_OKAY) {
        mp_clear(&dsa->q);
        mp_clear(&dsa->p);
        mp_clear(&tmp);
        mp_clear(&tmp2);
        return MP_INIT_E;
    }

    /* find a value g for which g^tmp2 != 1 */
    if (mp_set(&dsa->g, 1) != MP_OKAY) {
        mp_clear(&dsa->q);
        mp_clear(&dsa->p);
        mp_clear(&tmp);
        mp_clear(&tmp2);
        return MP_INIT_E;
    }

    do {
        err = mp_add_d(&dsa->g, 1, &dsa->g);
        if (err != MP_OKAY) {
            mp_clear(&dsa->q);
            mp_clear(&dsa->p);
            mp_clear(&dsa->g);
            mp_clear(&tmp);
            mp_clear(&tmp2);
            return err;
        }

        err = mp_exptmod(&dsa->g, &tmp2, &dsa->p, &tmp);
        if (err != MP_OKAY) {
            mp_clear(&dsa->q);
            mp_clear(&dsa->p);
            mp_clear(&dsa->g);
            mp_clear(&tmp);
            mp_clear(&tmp2);
            return err;
        }

    } while (mp_cmp_d(&tmp, 1) == MP_EQ);

    /* at this point tmp generates a group of order q mod p */
    mp_exch(&tmp, &dsa->g);

    mp_clear(&tmp);
    mp_clear(&tmp2);

    return MP_OKAY;
}
#endif /* WOLFSSL_KEY_GEN */


static int _DsaImportParamsRaw(DsaKey* dsa, const char* p, const char* q,
                          const char* g, int trusted, WC_RNG* rng)
{
    int err;
    word32 pSz, qSz;

    if (dsa == NULL || p == NULL || q == NULL || g == NULL)
        return BAD_FUNC_ARG;

    /* read p */
    err = mp_read_radix(&dsa->p, p, MP_RADIX_HEX);
    if (err == MP_OKAY && !trusted) {
        int isPrime = 1;
        if (rng == NULL)
            err = mp_prime_is_prime(&dsa->p, 8, &isPrime);
        else
            err = mp_prime_is_prime_ex(&dsa->p, 8, &isPrime, rng);

        if (err == MP_OKAY) {
            if (!isPrime)
                err = DH_CHECK_PUB_E;
        }
    }

    /* read q */
    if (err == MP_OKAY)
        err = mp_read_radix(&dsa->q, q, MP_RADIX_HEX);

    /* read g */
    if (err == MP_OKAY)
        err = mp_read_radix(&dsa->g, g, MP_RADIX_HEX);

    /* verify (L,N) pair bit lengths */
    pSz = mp_unsigned_bin_size(&dsa->p);
    qSz = mp_unsigned_bin_size(&dsa->q);

    if (CheckDsaLN(pSz * WOLFSSL_BIT_SIZE, qSz * WOLFSSL_BIT_SIZE) != 0) {
        WOLFSSL_MSG("Invalid DSA p or q parameter size");
        err = BAD_FUNC_ARG;
    }

    if (err != MP_OKAY) {
        mp_clear(&dsa->p);
        mp_clear(&dsa->q);
        mp_clear(&dsa->g);
    }

    return err;
}


/* Import raw DSA parameters into DsaKey structure for use with wc_MakeDsaKey(),
 * input parameters (p,q,g) should be represented as ASCII hex values.
 *
 * dsa  - pointer to initialized DsaKey structure
 * p    - DSA (p) parameter, ASCII hex string
 * pSz  - length of p
 * q    - DSA (q) parameter, ASCII hex string
 * qSz  - length of q
 * g    - DSA (g) parameter, ASCII hex string
 * gSz  - length of g
 *
 * returns 0 on success, negative upon failure
 */
int wc_DsaImportParamsRaw(DsaKey* dsa, const char* p, const char* q,
                          const char* g)
{
    return _DsaImportParamsRaw(dsa, p, q, g, 1, NULL);
}


/* Import raw DSA parameters into DsaKey structure for use with wc_MakeDsaKey(),
 * input parameters (p,q,g) should be represented as ASCII hex values. Check
 * that the p value is probably prime.
 *
 * dsa  - pointer to initialized DsaKey structure
 * p    - DSA (p) parameter, ASCII hex string
 * pSz  - length of p
 * q    - DSA (q) parameter, ASCII hex string
 * qSz  - length of q
 * g    - DSA (g) parameter, ASCII hex string
 * gSz  - length of g
 * trusted - trust that p is OK
 * rng  - random number generator for the prime test
 *
 * returns 0 on success, negative upon failure
 */
int wc_DsaImportParamsRawCheck(DsaKey* dsa, const char* p, const char* q,
                          const char* g, int trusted, WC_RNG* rng)
{
    return _DsaImportParamsRaw(dsa, p, q, g, trusted, rng);
}


/* Export raw DSA parameters from DsaKey structure
 *
 * dsa  - pointer to initialized DsaKey structure
 * p    - output location for DSA (p) parameter
 * pSz  - [IN/OUT] size of output buffer for p, size of p
 * q    - output location for DSA (q) parameter
 * qSz  - [IN/OUT] size of output buffer for q, size of q
 * g    - output location for DSA (g) parameter
 * gSz  - [IN/OUT] size of output buffer for g, size of g
 *
 * If p, q, and g pointers are all passed in as NULL, the function
 * will set pSz, qSz, and gSz to the required output buffer sizes for p,
 * q, and g. In this case, the function will return LENGTH_ONLY_E.
 *
 * returns 0 on success, negative upon failure
 */
int wc_DsaExportParamsRaw(DsaKey* dsa, byte* p, word32* pSz,
                          byte* q, word32* qSz, byte* g, word32* gSz)
{
    int err;
    word32 pLen, qLen, gLen;

    if (dsa == NULL || pSz == NULL || qSz == NULL || gSz == NULL)
        return BAD_FUNC_ARG;

    /* get required output buffer sizes */
    pLen = mp_unsigned_bin_size(&dsa->p);
    qLen = mp_unsigned_bin_size(&dsa->q);
    gLen = mp_unsigned_bin_size(&dsa->g);

    /* return buffer sizes and LENGTH_ONLY_E if buffers are NULL */
    if (p == NULL && q == NULL && g == NULL) {
        *pSz = pLen;
        *qSz = qLen;
        *gSz = gLen;
        return LENGTH_ONLY_E;
    }

    if (p == NULL || q == NULL || g == NULL)
        return BAD_FUNC_ARG;

    /* export p */
    if (*pSz < pLen) {
        WOLFSSL_MSG("Output buffer for DSA p parameter too small, "
                    "required size placed into pSz");
        *pSz = pLen;
        return BUFFER_E;
    }
    *pSz = pLen;
    err = mp_to_unsigned_bin(&dsa->p, p);

    /* export q */
    if (err == MP_OKAY) {
        if (*qSz < qLen) {
            WOLFSSL_MSG("Output buffer for DSA q parameter too small, "
                        "required size placed into qSz");
            *qSz = qLen;
            return BUFFER_E;
        }
        *qSz = qLen;
        err = mp_to_unsigned_bin(&dsa->q, q);
    }

    /* export g */
    if (err == MP_OKAY) {
        if (*gSz < gLen) {
            WOLFSSL_MSG("Output buffer for DSA g parameter too small, "
                        "required size placed into gSz");
            *gSz = gLen;
            return BUFFER_E;
        }
        *gSz = gLen;
        err = mp_to_unsigned_bin(&dsa->g, g);
    }

    return err;
}


/* Export raw DSA key (x, y) from DsaKey structure
 *
 * dsa  - pointer to initialized DsaKey structure
 * x    - output location for private key
 * xSz  - [IN/OUT] size of output buffer for x, size of x
 * y    - output location for public key
 * ySz  - [IN/OUT] size of output buffer for y, size of y
 *
 * If x and y pointers are all passed in as NULL, the function
 * will set xSz and ySz to the required output buffer sizes for x
 * and y. In this case, the function will return LENGTH_ONLY_E.
 *
 * returns 0 on success, negative upon failure
 */
int wc_DsaExportKeyRaw(DsaKey* dsa, byte* x, word32* xSz, byte* y, word32* ySz)
{
    int err;
    word32 xLen, yLen;

    if (dsa == NULL || xSz == NULL || ySz == NULL)
        return BAD_FUNC_ARG;

    /* get required output buffer sizes */
    xLen = mp_unsigned_bin_size(&dsa->x);
    yLen = mp_unsigned_bin_size(&dsa->y);

    /* return buffer sizes and LENGTH_ONLY_E if buffers are NULL */
    if (x == NULL && y == NULL) {
        *xSz = xLen;
        *ySz = yLen;
        return LENGTH_ONLY_E;
    }

    if (x == NULL || y == NULL)
        return BAD_FUNC_ARG;

    /* export x */
    if (*xSz < xLen) {
        WOLFSSL_MSG("Output buffer for DSA private key (x) too small, "
                    "required size placed into xSz");
        *xSz = xLen;
        return BUFFER_E;
    }
    *xSz = xLen;
    err = mp_to_unsigned_bin(&dsa->x, x);

    /* export y */
    if (err == MP_OKAY) {
        if (*ySz < yLen) {
            WOLFSSL_MSG("Output buffer to DSA public key (y) too small, "
                        "required size placed into ySz");
            *ySz = yLen;
            return BUFFER_E;
        }
        *ySz = yLen;
        err = mp_to_unsigned_bin(&dsa->y, y);
    }

    return err;
}


int wc_DsaSign(const byte* digest, byte* out, DsaKey* key, WC_RNG* rng)
{
    mp_int  k, kInv, r, s, H;
#ifndef WOLFSSL_MP_INVMOD_CONSTANT_TIME
    mp_int  b;
#endif
    mp_int* qMinus1;
    int     ret = 0, sz;
    byte    buffer[DSA_HALF_SIZE];
    byte*   tmp;  /* initial output pointer */

    if (digest == NULL || out == NULL || key == NULL || rng == NULL) {
        return BAD_FUNC_ARG;
    }

    tmp = out;

    sz = min((int)sizeof(buffer), mp_unsigned_bin_size(&key->q));

#ifdef WOLFSSL_MP_INVMOD_CONSTANT_TIME
    if (mp_init_multi(&k, &kInv, &r, &s, &H, 0) != MP_OKAY)
#else
    if (mp_init_multi(&k, &kInv, &r, &s, &H, &b) != MP_OKAY)
#endif
    {
        return MP_INIT_E;
    }
    qMinus1 = &kInv;

    /* NIST FIPS 186-4: B.2.2
     * Per-Message Secret Number Generation by Testing Candidates
     * Generate k in range [1, q-1].
     *   Check that k is less than q-1: range [0, q-2].
     *   Add 1 to k: range [1, q-1].
     */
    if (mp_sub_d(&key->q, 1, qMinus1))
        ret = MP_SUB_E;

    if (ret == 0) {
        do {
            /* Step 4: generate k */
            ret = wc_RNG_GenerateBlock(rng, buffer, sz);

            /* Step 5 */
            if (ret == 0 && mp_read_unsigned_bin(&k, buffer, sz) != MP_OKAY)
                ret = MP_READ_E;

            /* k is a random numnber and it should be less than q-1
             * if k greater than repeat
             */
        /* Step 6 */
        } while (ret == 0 && mp_cmp(&k, qMinus1) != MP_LT);
    }
    /* Step 7 */
    if (ret == 0 && mp_add_d(&k, 1, &k) != MP_OKAY)
        ret = MP_MOD_E;

#ifdef WOLFSSL_MP_INVMOD_CONSTANT_TIME
    /* inverse k mod q */
    if (ret == 0 && mp_invmod(&k, &key->q, &kInv) != MP_OKAY)
        ret = MP_INVMOD_E;

    /* generate r, r = (g exp k mod p) mod q */
    if (ret == 0 && mp_exptmod_ex(&key->g, &k, key->q.used, &key->p,
                                                               &r) != MP_OKAY) {
        ret = MP_EXPTMOD_E;
    }

    if (ret == 0 && mp_mod(&r, &key->q, &r) != MP_OKAY)
        ret = MP_MOD_E;

    /* generate H from sha digest */
    if (ret == 0 && mp_read_unsigned_bin(&H, digest,WC_SHA_DIGEST_SIZE) != MP_OKAY)
        ret = MP_READ_E;

    /* generate s, s = (kInv * (H + x*r)) % q */
    if (ret == 0 && mp_mul(&key->x, &r, &s) != MP_OKAY)
        ret = MP_MUL_E;

    if (ret == 0 && mp_add(&s, &H, &s) != MP_OKAY)
        ret = MP_ADD_E;

    if (ret == 0 && mp_mulmod(&s, &kInv, &key->q, &s) != MP_OKAY)
        ret = MP_MULMOD_E;
#else
    /* Blinding value
     * Generate b in range [1, q-1].
     */
    if (ret == 0) {
        do {
            ret = wc_RNG_GenerateBlock(rng, buffer, sz);
            if (ret == 0 && mp_read_unsigned_bin(&b, buffer, sz) != MP_OKAY)
                ret = MP_READ_E;
        } while (ret == 0 && mp_cmp(&b, qMinus1) != MP_LT);
    }
    if (ret == 0 && mp_add_d(&b, 1, &b) != MP_OKAY)
        ret = MP_MOD_E;

    /* set H from sha digest */
    if (ret == 0 && mp_read_unsigned_bin(&H, digest,
                                               WC_SHA_DIGEST_SIZE) != MP_OKAY) {
        ret = MP_READ_E;
    }

    /* generate r, r = (g exp k mod p) mod q */
    if (ret == 0 && mp_exptmod_ex(&key->g, &k, key->q.used, &key->p,
                                                               &r) != MP_OKAY) {
        ret = MP_EXPTMOD_E;
    }

    /* calculate s = (H + xr)/k
                   = b.(H/k.b + x.r/k.b) */

    /* k = k.b */
    if (ret == 0 && mp_mulmod(&k, &b, &key->q, &k) != MP_OKAY)
        ret = MP_MULMOD_E;

    /* kInv = 1/k.b mod q */
    if (ret == 0 && mp_invmod(&k, &key->q, &kInv) != MP_OKAY)
        ret = MP_INVMOD_E;

    if (ret == 0 && mp_mod(&r, &key->q, &r) != MP_OKAY)
        ret = MP_MOD_E;

    /* s = x.r */
    if (ret == 0 && mp_mul(&key->x, &r, &s) != MP_OKAY)
        ret = MP_MUL_E;

    /* s = x.r/k.b */
    if (ret == 0 && mp_mulmod(&s, &kInv, &key->q, &s) != MP_OKAY)
        ret = MP_MULMOD_E;

    /* H = H/k.b */
    if (ret == 0 && mp_mulmod(&H, &kInv, &key->q, &H) != MP_OKAY)
        ret = MP_MULMOD_E;

    /* s = H/k.b + x.r/k.b
         = (H + x.r)/k.b */
    if (ret == 0 && mp_add(&s, &H, &s) != MP_OKAY)
        ret = MP_ADD_E;

    /* s = b.(e + x.r)/k.b
         = (e + x.r)/k */
    if (ret == 0 && mp_mulmod(&s, &b, &key->q, &s) != MP_OKAY)
        ret = MP_MULMOD_E;

    /* s = (e + x.r)/k */
    if (ret == 0 && mp_mod(&s, &key->q, &s) != MP_OKAY)
        ret = MP_MOD_E;
#endif

    /* detect zero r or s */
    if (ret == 0 && (mp_iszero(&r) == MP_YES || mp_iszero(&s) == MP_YES))
        ret = MP_ZERO_E;

    /* write out */
    if (ret == 0)  {
        int rSz = mp_unsigned_bin_size(&r);
        int sSz = mp_unsigned_bin_size(&s);

        while (rSz++ < DSA_HALF_SIZE) {
            *out++ = 0x00;  /* pad front with zeros */
        }

        if (mp_to_unsigned_bin(&r, out) != MP_OKAY)
            ret = MP_TO_E;
        else {
            out = tmp + DSA_HALF_SIZE;  /* advance to s in output */
            while (sSz++ < DSA_HALF_SIZE) {
                *out++ = 0x00;  /* pad front with zeros */
            }
            ret = mp_to_unsigned_bin(&s, out);
        }
    }

    ForceZero(buffer, sz);
    mp_forcezero(&kInv);
    mp_forcezero(&k);
#ifndef WOLFSSL_MP_INVMOD_CONSTANT_TIME
    mp_forcezero(&b);

    mp_clear(&b);
#endif
    mp_clear(&H);
    mp_clear(&s);
    mp_clear(&r);
    mp_clear(&kInv);
    mp_clear(&k);

    return ret;
}


int wc_DsaVerify(const byte* digest, const byte* sig, DsaKey* key, int* answer)
{
    mp_int w, u1, u2, v, r, s;
    int    ret = 0;

    if (digest == NULL || sig == NULL || key == NULL || answer == NULL) {
        return BAD_FUNC_ARG;
    }

    if (mp_init_multi(&w, &u1, &u2, &v, &r, &s) != MP_OKAY)
        return MP_INIT_E;

    /* set r and s from signature */
    if (mp_read_unsigned_bin(&r, sig, DSA_HALF_SIZE) != MP_OKAY ||
        mp_read_unsigned_bin(&s, sig + DSA_HALF_SIZE, DSA_HALF_SIZE) != MP_OKAY)
        ret = MP_READ_E;

    /* sanity checks */
    if (ret == 0) {
        if (mp_iszero(&r) == MP_YES || mp_iszero(&s) == MP_YES ||
                mp_cmp(&r, &key->q) != MP_LT || mp_cmp(&s, &key->q) != MP_LT) {
            ret = MP_ZERO_E;
        }
    }

    /* put H into u1 from sha digest */
    if (ret == 0 && mp_read_unsigned_bin(&u1,digest,WC_SHA_DIGEST_SIZE) != MP_OKAY)
        ret = MP_READ_E;

    /* w = s invmod q */
    if (ret == 0 && mp_invmod(&s, &key->q, &w) != MP_OKAY)
        ret = MP_INVMOD_E;

    /* u1 = (H * w) % q */
    if (ret == 0 && mp_mulmod(&u1, &w, &key->q, &u1) != MP_OKAY)
        ret = MP_MULMOD_E;

    /* u2 = (r * w) % q */
    if (ret == 0 && mp_mulmod(&r, &w, &key->q, &u2) != MP_OKAY)
        ret = MP_MULMOD_E;

    /* verify v = ((g^u1 * y^u2) mod p) mod q */
    if (ret == 0 && mp_exptmod(&key->g, &u1, &key->p, &u1) != MP_OKAY)
        ret = MP_EXPTMOD_E;

    if (ret == 0 && mp_exptmod(&key->y, &u2, &key->p, &u2) != MP_OKAY)
        ret = MP_EXPTMOD_E;

    if (ret == 0 && mp_mulmod(&u1, &u2, &key->p, &v) != MP_OKAY)
        ret = MP_MULMOD_E;

    if (ret == 0 && mp_mod(&v, &key->q, &v) != MP_OKAY)
        ret = MP_MULMOD_E;

    /* do they match */
    if (ret == 0 && mp_cmp(&r, &v) == MP_EQ)
        *answer = 1;
    else
        *answer = 0;

    mp_clear(&s);
    mp_clear(&r);
    mp_clear(&u1);
    mp_clear(&u2);
    mp_clear(&w);
    mp_clear(&v);

    return ret;
}


#endif /* NO_DSA */

