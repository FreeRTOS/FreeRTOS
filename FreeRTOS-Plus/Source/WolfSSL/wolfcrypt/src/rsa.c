/* rsa.c
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
#include <wolfssl/wolfcrypt/error-crypt.h>

#ifndef NO_RSA

#if defined(HAVE_FIPS) && \
    defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2)

    /* set NO_WRAPPERS before headers, use direct internal f()s not wrappers */
    #define FIPS_NO_WRAPPERS

       #ifdef USE_WINDOWS_API
               #pragma code_seg(".fipsA$e")
               #pragma const_seg(".fipsB$e")
       #endif
#endif

#include <wolfssl/wolfcrypt/rsa.h>

#ifdef WOLFSSL_AFALG_XILINX_RSA
#include <wolfssl/wolfcrypt/port/af_alg/wc_afalg.h>
#endif

#ifdef WOLFSSL_HAVE_SP_RSA
#include <wolfssl/wolfcrypt/sp.h>
#endif

/*
Possible RSA enable options:
 * NO_RSA:              Overall control of RSA                      default: on (not defined)
 * WC_RSA_BLINDING:     Uses Blinding w/ Private Ops                default: off
                        Note: slower by ~20%
 * WOLFSSL_KEY_GEN:     Allows Private Key Generation               default: off
 * RSA_LOW_MEM:         NON CRT Private Operations, less memory     default: off
 * WC_NO_RSA_OAEP:      Disables RSA OAEP padding                   default: on (not defined)
 * WC_RSA_NONBLOCK:     Enables support for RSA non-blocking        default: off
 * WC_RSA_NONBLOCK_TIME:Enables support for time based blocking     default: off
 *                      time calculation.
*/

/*
RSA Key Size Configuration:
 * FP_MAX_BITS:         With USE_FAST_MATH only                     default: 4096
    If USE_FAST_MATH then use this to override default.
    Value is key size * 2. Example: RSA 3072 = 6144
*/


/* If building for old FIPS. */
#if defined(HAVE_FIPS) && \
    (!defined(HAVE_FIPS_VERSION) || (HAVE_FIPS_VERSION < 2))

int  wc_InitRsaKey(RsaKey* key, void* ptr)
{
    if (key == NULL) {
        return BAD_FUNC_ARG;
    }

    return InitRsaKey_fips(key, ptr);
}


int  wc_InitRsaKey_ex(RsaKey* key, void* ptr, int devId)
{
    (void)devId;
    if (key == NULL) {
        return BAD_FUNC_ARG;
    }
    return InitRsaKey_fips(key, ptr);
}


int  wc_FreeRsaKey(RsaKey* key)
{
    return FreeRsaKey_fips(key);
}


#ifndef WOLFSSL_RSA_VERIFY_ONLY
int  wc_RsaPublicEncrypt(const byte* in, word32 inLen, byte* out,
                                 word32 outLen, RsaKey* key, WC_RNG* rng)
{
    if (in == NULL || out == NULL || key == NULL || rng == NULL) {
        return BAD_FUNC_ARG;
    }
    return RsaPublicEncrypt_fips(in, inLen, out, outLen, key, rng);
}
#endif


#ifndef WOLFSSL_RSA_PUBLIC_ONLY
int  wc_RsaPrivateDecryptInline(byte* in, word32 inLen, byte** out,
                                        RsaKey* key)
{
    if (in == NULL || out == NULL || key == NULL) {
        return BAD_FUNC_ARG;
    }
    return RsaPrivateDecryptInline_fips(in, inLen, out, key);
}


int  wc_RsaPrivateDecrypt(const byte* in, word32 inLen, byte* out,
                                  word32 outLen, RsaKey* key)
{
    if (in == NULL || out == NULL || key == NULL) {
        return BAD_FUNC_ARG;
    }
    return RsaPrivateDecrypt_fips(in, inLen, out, outLen, key);
}


int  wc_RsaSSL_Sign(const byte* in, word32 inLen, byte* out,
                            word32 outLen, RsaKey* key, WC_RNG* rng)
{
    if (in == NULL || out == NULL || key == NULL || inLen == 0) {
        return BAD_FUNC_ARG;
    }
    return RsaSSL_Sign_fips(in, inLen, out, outLen, key, rng);
}
#endif


int  wc_RsaSSL_VerifyInline(byte* in, word32 inLen, byte** out, RsaKey* key)
{
    if (in == NULL || out == NULL || key == NULL) {
        return BAD_FUNC_ARG;
    }
    return RsaSSL_VerifyInline_fips(in, inLen, out, key);
}


int  wc_RsaSSL_Verify(const byte* in, word32 inLen, byte* out,
                              word32 outLen, RsaKey* key)
{
    if (in == NULL || out == NULL || key == NULL || inLen == 0) {
        return BAD_FUNC_ARG;
    }
    return RsaSSL_Verify_fips(in, inLen, out, outLen, key);
}


int  wc_RsaEncryptSize(RsaKey* key)
{
    if (key == NULL) {
        return BAD_FUNC_ARG;
    }
    return RsaEncryptSize_fips(key);
}


#ifndef WOLFSSL_RSA_VERIFY_ONLY
int wc_RsaFlattenPublicKey(RsaKey* key, byte* a, word32* aSz, byte* b,
                           word32* bSz)
{

    /* not specified as fips so not needing _fips */
    return RsaFlattenPublicKey(key, a, aSz, b, bSz);
}
#endif


#ifdef WOLFSSL_KEY_GEN
    int wc_MakeRsaKey(RsaKey* key, int size, long e, WC_RNG* rng)
    {
        return MakeRsaKey(key, size, e, rng);
    }
#endif


/* these are functions in asn and are routed to wolfssl/wolfcrypt/asn.c
* wc_RsaPrivateKeyDecode
* wc_RsaPublicKeyDecode
*/

#else /* else build without fips, or for new fips */

#include <wolfssl/wolfcrypt/random.h>
#include <wolfssl/wolfcrypt/logging.h>
#ifdef WOLF_CRYPTO_CB
    #include <wolfssl/wolfcrypt/cryptocb.h>
#endif
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif


enum {
    RSA_STATE_NONE = 0,

    RSA_STATE_ENCRYPT_PAD,
    RSA_STATE_ENCRYPT_EXPTMOD,
    RSA_STATE_ENCRYPT_RES,

    RSA_STATE_DECRYPT_EXPTMOD,
    RSA_STATE_DECRYPT_UNPAD,
    RSA_STATE_DECRYPT_RES,
};


static void wc_RsaCleanup(RsaKey* key)
{
#ifndef WOLFSSL_RSA_VERIFY_INLINE
    if (key && key->data) {
        /* make sure any allocated memory is free'd */
        if (key->dataIsAlloc) {
        #ifndef WOLFSSL_RSA_PUBLIC_ONLY
            if (key->type == RSA_PRIVATE_DECRYPT ||
                key->type == RSA_PRIVATE_ENCRYPT) {
                ForceZero(key->data, key->dataLen);
            }
        #endif
            XFREE(key->data, key->heap, DYNAMIC_TYPE_WOLF_BIGINT);
            key->dataIsAlloc = 0;
        }
        key->data = NULL;
        key->dataLen = 0;
    }
#else
    (void)key;
#endif
}

int wc_InitRsaKey_ex(RsaKey* key, void* heap, int devId)
{
    int ret = 0;

    if (key == NULL) {
        return BAD_FUNC_ARG;
    }

    XMEMSET(key, 0, sizeof(RsaKey));

    key->type = RSA_TYPE_UNKNOWN;
    key->state = RSA_STATE_NONE;
    key->heap = heap;
#ifndef WOLFSSL_RSA_VERIFY_INLINE
    key->dataIsAlloc = 0;
    key->data = NULL;
#endif
    key->dataLen = 0;
#ifdef WC_RSA_BLINDING
    key->rng = NULL;
#endif

#ifdef WOLF_CRYPTO_CB
    key->devId = devId;
#else
    (void)devId;
#endif

#ifdef WOLFSSL_ASYNC_CRYPT
    #ifdef WOLFSSL_CERT_GEN
        XMEMSET(&key->certSignCtx, 0, sizeof(CertSignCtx));
    #endif

    #ifdef WC_ASYNC_ENABLE_RSA
        /* handle as async */
        ret = wolfAsync_DevCtxInit(&key->asyncDev, WOLFSSL_ASYNC_MARKER_RSA,
                                                            key->heap, devId);
        if (ret != 0)
            return ret;
    #endif /* WC_ASYNC_ENABLE_RSA */
#endif /* WOLFSSL_ASYNC_CRYPT */

#ifndef WOLFSSL_RSA_PUBLIC_ONLY
    ret = mp_init_multi(&key->n, &key->e, NULL, NULL, NULL, NULL);
    if (ret != MP_OKAY)
        return ret;

#if !defined(WOLFSSL_KEY_GEN) && !defined(OPENSSL_EXTRA) && defined(RSA_LOW_MEM)
    ret = mp_init_multi(&key->d, &key->p, &key->q, NULL, NULL, NULL);
#else
    ret = mp_init_multi(&key->d, &key->p, &key->q, &key->dP, &key->dQ, &key->u);
#endif
    if (ret != MP_OKAY) {
        mp_clear(&key->n);
        mp_clear(&key->e);
        return ret;
    }
#else
    ret = mp_init(&key->n);
    if (ret != MP_OKAY)
        return ret;
    ret = mp_init(&key->e);
    if (ret != MP_OKAY) {
        mp_clear(&key->n);
        return ret;
    }
#endif

#ifdef WOLFSSL_XILINX_CRYPT
    key->pubExp = 0;
    key->mod    = NULL;
#endif

#ifdef WOLFSSL_AFALG_XILINX_RSA
    key->alFd = WC_SOCK_NOTSET;
    key->rdFd = WC_SOCK_NOTSET;
#endif

    return ret;
}

int wc_InitRsaKey(RsaKey* key, void* heap)
{
    return wc_InitRsaKey_ex(key, heap, INVALID_DEVID);
}

#ifdef HAVE_PKCS11
int wc_InitRsaKey_Id(RsaKey* key, unsigned char* id, int len, void* heap,
                     int devId)
{
    int ret = 0;

    if (key == NULL)
        ret = BAD_FUNC_ARG;
    if (ret == 0 && (len < 0 || len > RSA_MAX_ID_LEN))
        ret = BUFFER_E;

    if (ret == 0)
        ret = wc_InitRsaKey_ex(key, heap, devId);

    if (ret == 0 && id != NULL && len != 0) {
        XMEMCPY(key->id, id, len);
        key->idLen = len;
    }

    return ret;
}
#endif


#ifdef WOLFSSL_XILINX_CRYPT
#define MAX_E_SIZE 4
/* Used to setup hardware state
 *
 * key  the RSA key to setup
 *
 * returns 0 on success
 */
int wc_InitRsaHw(RsaKey* key)
{
    unsigned char* m; /* RSA modulous */
    word32 e = 0;     /* RSA public exponent */
    int mSz;
    int eSz;

    if (key == NULL) {
        return BAD_FUNC_ARG;
    }

    mSz = mp_unsigned_bin_size(&(key->n));
    m = (unsigned char*)XMALLOC(mSz, key->heap, DYNAMIC_TYPE_KEY);
    if (m == 0) {
        return MEMORY_E;
    }

    if (mp_to_unsigned_bin(&(key->n), m) != MP_OKAY) {
        WOLFSSL_MSG("Unable to get RSA key modulus");
        XFREE(m, key->heap, DYNAMIC_TYPE_KEY);
        return MP_READ_E;
    }

    eSz = mp_unsigned_bin_size(&(key->e));
    if (eSz > MAX_E_SIZE) {
        WOLFSSL_MSG("Exponent of size 4 bytes expected");
        XFREE(m, key->heap, DYNAMIC_TYPE_KEY);
        return BAD_FUNC_ARG;
    }

    if (mp_to_unsigned_bin(&(key->e), (byte*)&e + (MAX_E_SIZE - eSz))
                != MP_OKAY) {
        XFREE(m, key->heap, DYNAMIC_TYPE_KEY);
        WOLFSSL_MSG("Unable to get RSA key exponent");
        return MP_READ_E;
    }

    /* check for existing mod buffer to avoid memory leak */
    if (key->mod != NULL) {
        XFREE(key->mod, key->heap, DYNAMIC_TYPE_KEY);
    }

    key->pubExp = e;
    key->mod    = m;

    if (XSecure_RsaInitialize(&(key->xRsa), key->mod, NULL,
                (byte*)&(key->pubExp)) != XST_SUCCESS) {
        WOLFSSL_MSG("Unable to initialize RSA on hardware");
        XFREE(m, key->heap, DYNAMIC_TYPE_KEY);
        return BAD_STATE_E;
    }

#ifdef WOLFSSL_XILINX_PATCH
   /* currently a patch of xsecure_rsa.c for 2048 bit keys */
   if (wc_RsaEncryptSize(key) == 256) {
       if (XSecure_RsaSetSize(&(key->xRsa), 2048) != XST_SUCCESS) {
           WOLFSSL_MSG("Unable to set RSA key size on hardware");
           XFREE(m, key->heap, DYNAMIC_TYPE_KEY);
           return BAD_STATE_E;
       }
   }
#endif
    return 0;
} /* WOLFSSL_XILINX_CRYPT*/

#elif defined(WOLFSSL_CRYPTOCELL)

int wc_InitRsaHw(RsaKey* key)
{
    CRYSError_t ret = 0;
    byte e[3];
    word32 eSz = sizeof(e);
    byte n[256];
    word32 nSz = sizeof(n);
    byte d[256];
    word32 dSz = sizeof(d);
    byte p[128];
    word32 pSz = sizeof(p);
    byte q[128];
    word32 qSz = sizeof(q);

    if (key == NULL) {
        return BAD_FUNC_ARG;
    }

    ret = wc_RsaExportKey(key, e, &eSz, n, &nSz, d, &dSz, p, &pSz, q, &qSz);
    if (ret != 0)
        return MP_READ_E;

    ret = CRYS_RSA_Build_PubKey(&key->ctx.pubKey, e, eSz, n, nSz);
    if (ret != SA_SILIB_RET_OK){
        WOLFSSL_MSG("CRYS_RSA_Build_PubKey failed");
        return ret;
    }

    ret =  CRYS_RSA_Build_PrivKey(&key->ctx.privKey, d, dSz, e, eSz, n, nSz);

    if (ret != SA_SILIB_RET_OK){
        WOLFSSL_MSG("CRYS_RSA_Build_PrivKey failed");
        return ret;
    }
    key->type = RSA_PRIVATE;
    return 0;
}
static int cc310_RSA_GenerateKeyPair(RsaKey* key, int size, long e)
{
    CRYSError_t             ret = 0;
    CRYS_RSAKGData_t        KeyGenData;
    CRYS_RSAKGFipsContext_t FipsCtx;
    byte ex[3];
    uint16_t eSz = sizeof(ex);
    byte n[256];
    uint16_t nSz = sizeof(n);

    ret = CRYS_RSA_KG_GenerateKeyPair(&wc_rndState,
                        wc_rndGenVectFunc,
                        (byte*)&e,
                        3*sizeof(uint8_t),
                        size,
                        &key->ctx.privKey,
                        &key->ctx.pubKey,
                        &KeyGenData,
                        &FipsCtx);

    if (ret != SA_SILIB_RET_OK){
        WOLFSSL_MSG("CRYS_RSA_KG_GenerateKeyPair failed");
        return ret;
    }

    ret = CRYS_RSA_Get_PubKey(&key->ctx.pubKey, ex, &eSz, n, &nSz);
    if (ret != SA_SILIB_RET_OK){
        WOLFSSL_MSG("CRYS_RSA_Get_PubKey failed");
        return ret;
    }
    ret = wc_RsaPublicKeyDecodeRaw(n, nSz, ex, eSz, key);

    key->type = RSA_PRIVATE;

    return ret;
}
#endif /* WOLFSSL_CRYPTOCELL */

int wc_FreeRsaKey(RsaKey* key)
{
    int ret = 0;

    if (key == NULL) {
        return BAD_FUNC_ARG;
    }

    wc_RsaCleanup(key);

#if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_RSA)
    wolfAsync_DevCtxFree(&key->asyncDev, WOLFSSL_ASYNC_MARKER_RSA);
#endif

#ifndef WOLFSSL_RSA_PUBLIC_ONLY
    if (key->type == RSA_PRIVATE) {
#if defined(WOLFSSL_KEY_GEN) || defined(OPENSSL_EXTRA) || !defined(RSA_LOW_MEM)
        mp_forcezero(&key->u);
        mp_forcezero(&key->dQ);
        mp_forcezero(&key->dP);
#endif
        mp_forcezero(&key->q);
        mp_forcezero(&key->p);
        mp_forcezero(&key->d);
    }
    /* private part */
#if defined(WOLFSSL_KEY_GEN) || defined(OPENSSL_EXTRA) || !defined(RSA_LOW_MEM)
    mp_clear(&key->u);
    mp_clear(&key->dQ);
    mp_clear(&key->dP);
#endif
    mp_clear(&key->q);
    mp_clear(&key->p);
    mp_clear(&key->d);
#endif /* WOLFSSL_RSA_PUBLIC_ONLY */

    /* public part */
    mp_clear(&key->e);
    mp_clear(&key->n);

#ifdef WOLFSSL_XILINX_CRYPT
    XFREE(key->mod, key->heap, DYNAMIC_TYPE_KEY);
    key->mod = NULL;
#endif

#ifdef WOLFSSL_AFALG_XILINX_RSA
    /* make sure that sockets are closed on cleanup */
    if (key->alFd > 0) {
        close(key->alFd);
        key->alFd = WC_SOCK_NOTSET;
    }
    if (key->rdFd > 0) {
        close(key->rdFd);
        key->rdFd = WC_SOCK_NOTSET;
    }
#endif

    return ret;
}

#ifndef WOLFSSL_RSA_PUBLIC_ONLY
#if defined(WOLFSSL_KEY_GEN) && !defined(WOLFSSL_NO_RSA_KEY_CHECK)
/* Check the pair-wise consistency of the RSA key.
 * From NIST SP 800-56B, section 6.4.1.1.
 * Verify that k = (k^e)^d, for some k: 1 < k < n-1. */
int wc_CheckRsaKey(RsaKey* key)
{
#if defined(WOLFSSL_CRYPTOCELL)
    return 0;
#endif
#ifdef WOLFSSL_SMALL_STACK
    mp_int *k = NULL, *tmp = NULL;
#else
    mp_int k[1], tmp[1];
#endif
    int ret = 0;

#ifdef WOLFSSL_SMALL_STACK
    k = (mp_int*)XMALLOC(sizeof(mp_int) * 2, NULL, DYNAMIC_TYPE_RSA);
    if (k == NULL)
        return MEMORY_E;
    tmp = k + 1;
#endif

    if (mp_init_multi(k, tmp, NULL, NULL, NULL, NULL) != MP_OKAY)
        ret = MP_INIT_E;

    if (ret == 0) {
        if (key == NULL)
            ret = BAD_FUNC_ARG;
    }

    if (ret == 0) {
        if (mp_set_int(k, 0x2342) != MP_OKAY)
            ret = MP_READ_E;
    }

#ifdef WOLFSSL_HAVE_SP_RSA
#ifndef WOLFSSL_SP_NO_2048
    if (mp_count_bits(&key->n) == 2048) {
        ret = sp_ModExp_2048(k, &key->e, &key->n, tmp);
        if (ret != 0)
            ret = MP_EXPTMOD_E;
        ret = sp_ModExp_2048(tmp, &key->d, &key->n, tmp);
        if (ret != 0)
            ret = MP_EXPTMOD_E;
    }
    else
#endif
#ifndef WOLFSSL_SP_NO_3072
    if (mp_count_bits(&key->n) == 3072) {
        ret = sp_ModExp_3072(k, &key->e, &key->n, tmp);
        if (ret != 0)
            ret = MP_EXPTMOD_E;
        ret = sp_ModExp_3072(tmp, &key->d, &key->n, tmp);
        if (ret != 0)
            ret = MP_EXPTMOD_E;
    }
    else
#endif
#ifdef WOLFSSL_SP_4096
    if (mp_count_bits(&key->n) == 4096) {
        ret = sp_ModExp_4096(k, &key->e, &key->n, tmp);
        if (ret != 0)
            ret = MP_EXPTMOD_E;
        ret = sp_ModExp_4096(tmp, &key->d, &key->n, tmp);
        if (ret != 0)
            ret = MP_EXPTMOD_E;
    }
    else
#endif
#endif
#ifdef WOLFSSL_SP_MATH
    {
        ret = WC_KEY_SIZE_E;
    }
#else
    {
        if (ret == 0) {
            if (mp_exptmod(k, &key->e, &key->n, tmp) != MP_OKAY)
                ret = MP_EXPTMOD_E;
        }

        if (ret == 0) {
            if (mp_exptmod(tmp, &key->d, &key->n, tmp) != MP_OKAY)
                ret = MP_EXPTMOD_E;
        }
    }
#endif

    if (ret == 0) {
        if (mp_cmp(k, tmp) != MP_EQ)
            ret = RSA_KEY_PAIR_E;
    }

    /* Check d is less than n. */
    if (ret == 0 ) {
        if (mp_cmp(&key->d, &key->n) != MP_LT) {
            ret = MP_EXPTMOD_E;
        }
    }
    /* Check p*q = n. */
    if (ret == 0 ) {
        if (mp_mul(&key->p, &key->q, tmp) != MP_OKAY) {
            ret = MP_EXPTMOD_E;
        }
    }
    if (ret == 0 ) {
        if (mp_cmp(&key->n, tmp) != MP_EQ) {
            ret = MP_EXPTMOD_E;
        }
    }

    /* Check dP, dQ and u if they exist */
    if (ret == 0 && !mp_iszero(&key->dP)) {
        if (mp_sub_d(&key->p, 1, tmp) != MP_OKAY) {
            ret = MP_EXPTMOD_E;
        }
        /* Check dP <= p-1. */
        if (ret == 0) {
            if (mp_cmp(&key->dP, tmp) != MP_LT) {
                ret = MP_EXPTMOD_E;
            }
        }
        /* Check e*dP mod p-1 = 1. (dP = 1/e mod p-1) */
        if (ret == 0) {
            if (mp_mulmod(&key->dP, &key->e, tmp, tmp) != MP_OKAY) {
                ret = MP_EXPTMOD_E;
            }
        }
        if (ret == 0 ) {
            if (!mp_isone(tmp)) {
                ret = MP_EXPTMOD_E;
            }
        }

        if (ret == 0) {
            if (mp_sub_d(&key->q, 1, tmp) != MP_OKAY) {
                ret = MP_EXPTMOD_E;
            }
        }
        /* Check dQ <= q-1. */
        if (ret == 0) {
            if (mp_cmp(&key->dQ, tmp) != MP_LT) {
                ret = MP_EXPTMOD_E;
            }
        }
        /* Check e*dP mod p-1 = 1. (dQ = 1/e mod q-1) */
        if (ret == 0) {
            if (mp_mulmod(&key->dQ, &key->e, tmp, tmp) != MP_OKAY) {
                ret = MP_EXPTMOD_E;
            }
        }
        if (ret == 0 ) {
            if (!mp_isone(tmp)) {
                ret = MP_EXPTMOD_E;
            }
        }

        /* Check u <= p. */
        if (ret == 0) {
            if (mp_cmp(&key->u, &key->p) != MP_LT) {
                ret = MP_EXPTMOD_E;
            }
        }
        /* Check u*q mod p = 1. (u = 1/q mod p) */
        if (ret == 0) {
            if (mp_mulmod(&key->u, &key->q, &key->p, tmp) != MP_OKAY) {
                ret = MP_EXPTMOD_E;
            }
        }
        if (ret == 0 ) {
            if (!mp_isone(tmp)) {
                ret = MP_EXPTMOD_E;
            }
        }
    }

    mp_forcezero(tmp);
    mp_clear(tmp);
    mp_clear(k);
#ifdef WOLFSSL_SMALL_STACK
    XFREE(k, NULL, DYNAMIC_TYPE_RSA);
#endif

    return ret;
}
#endif
#endif


#if !defined(WC_NO_RSA_OAEP) || defined(WC_RSA_PSS)
/* Uses MGF1 standard as a mask generation function
   hType: hash type used
   seed:  seed to use for generating mask
   seedSz: size of seed buffer
   out:   mask output after generation
   outSz: size of output buffer
 */
#if !defined(NO_SHA) || !defined(NO_SHA256) || defined(WOLFSSL_SHA384) || defined(WOLFSSL_SHA512)
static int RsaMGF1(enum wc_HashType hType, byte* seed, word32 seedSz,
                                        byte* out, word32 outSz, void* heap)
{
    byte* tmp;
    /* needs to be large enough for seed size plus counter(4) */
    byte  tmpA[WC_MAX_DIGEST_SIZE + 4];
    byte   tmpF;     /* 1 if dynamic memory needs freed */
    word32 tmpSz;
    int hLen;
    int ret;
    word32 counter;
    word32 idx;
    hLen    = wc_HashGetDigestSize(hType);
    counter = 0;
    idx     = 0;

    (void)heap;

    /* check error return of wc_HashGetDigestSize */
    if (hLen < 0) {
        return hLen;
    }

    /* if tmp is not large enough than use some dynamic memory */
    if ((seedSz + 4) > sizeof(tmpA) || (word32)hLen > sizeof(tmpA)) {
        /* find largest amount of memory needed which will be the max of
         * hLen and (seedSz + 4) since tmp is used to store the hash digest */
        tmpSz = ((seedSz + 4) > (word32)hLen)? seedSz + 4: (word32)hLen;
        tmp = (byte*)XMALLOC(tmpSz, heap, DYNAMIC_TYPE_RSA_BUFFER);
        if (tmp == NULL) {
            return MEMORY_E;
        }
        tmpF = 1; /* make sure to free memory when done */
    }
    else {
        /* use array on the stack */
        tmpSz = sizeof(tmpA);
        tmp  = tmpA;
        tmpF = 0; /* no need to free memory at end */
    }

    do {
        int i = 0;
        XMEMCPY(tmp, seed, seedSz);

        /* counter to byte array appended to tmp */
        tmp[seedSz]     = (counter >> 24) & 0xFF;
        tmp[seedSz + 1] = (counter >> 16) & 0xFF;
        tmp[seedSz + 2] = (counter >>  8) & 0xFF;
        tmp[seedSz + 3] = (counter)       & 0xFF;

        /* hash and append to existing output */
        if ((ret = wc_Hash(hType, tmp, (seedSz + 4), tmp, tmpSz)) != 0) {
            /* check for if dynamic memory was needed, then free */
            if (tmpF) {
                XFREE(tmp, heap, DYNAMIC_TYPE_RSA_BUFFER);
            }
            return ret;
        }

        for (i = 0; i < hLen && idx < outSz; i++) {
            out[idx++] = tmp[i];
        }
        counter++;
    } while (idx < outSz);

    /* check for if dynamic memory was needed, then free */
    if (tmpF) {
        XFREE(tmp, heap, DYNAMIC_TYPE_RSA_BUFFER);
    }

    return 0;
}
#endif /* SHA2 Hashes */

/* helper function to direct which mask generation function is used
   switched on type input
 */
static int RsaMGF(int type, byte* seed, word32 seedSz, byte* out,
                                                    word32 outSz, void* heap)
{
    int ret;

    switch(type) {
    #ifndef NO_SHA
        case WC_MGF1SHA1:
            ret = RsaMGF1(WC_HASH_TYPE_SHA, seed, seedSz, out, outSz, heap);
            break;
    #endif
    #ifndef NO_SHA256
    #ifdef WOLFSSL_SHA224
        case WC_MGF1SHA224:
            ret = RsaMGF1(WC_HASH_TYPE_SHA224, seed, seedSz, out, outSz, heap);
            break;
    #endif
        case WC_MGF1SHA256:
            ret = RsaMGF1(WC_HASH_TYPE_SHA256, seed, seedSz, out, outSz, heap);
            break;
    #endif
    #ifdef WOLFSSL_SHA384
        case WC_MGF1SHA384:
            ret = RsaMGF1(WC_HASH_TYPE_SHA384, seed, seedSz, out, outSz, heap);
            break;
    #endif
    #ifdef WOLFSSL_SHA512
        case WC_MGF1SHA512:
            ret = RsaMGF1(WC_HASH_TYPE_SHA512, seed, seedSz, out, outSz, heap);
            break;
    #endif
        default:
            WOLFSSL_MSG("Unknown MGF type: check build options");
            ret = BAD_FUNC_ARG;
    }

    /* in case of default avoid unused warning */
    (void)seed;
    (void)seedSz;
    (void)out;
    (void)outSz;
    (void)heap;

    return ret;
}
#endif /* !WC_NO_RSA_OAEP || WC_RSA_PSS */


/* Padding */
#ifndef WOLFSSL_RSA_VERIFY_ONLY
#ifndef WC_NO_RNG
#ifndef WC_NO_RSA_OAEP
static int RsaPad_OAEP(const byte* input, word32 inputLen, byte* pkcsBlock,
        word32 pkcsBlockLen, byte padValue, WC_RNG* rng,
        enum wc_HashType hType, int mgf, byte* optLabel, word32 labelLen,
        void* heap)
{
    int ret;
    int hLen;
    int psLen;
    int i;
    word32 idx;

    byte* dbMask;

    #ifdef WOLFSSL_SMALL_STACK
        byte* lHash = NULL;
        byte* seed  = NULL;
    #else
        /* must be large enough to contain largest hash */
        byte lHash[WC_MAX_DIGEST_SIZE];
        byte seed[ WC_MAX_DIGEST_SIZE];
    #endif

    /* no label is allowed, but catch if no label provided and length > 0 */
    if (optLabel == NULL && labelLen > 0) {
        return BUFFER_E;
    }

    /* limit of label is the same as limit of hash function which is massive */
    hLen = wc_HashGetDigestSize(hType);
    if (hLen < 0) {
        return hLen;
    }

    #ifdef WOLFSSL_SMALL_STACK
        lHash = (byte*)XMALLOC(hLen, heap, DYNAMIC_TYPE_RSA_BUFFER);
        if (lHash == NULL) {
            return MEMORY_E;
        }
        seed = (byte*)XMALLOC(hLen, heap, DYNAMIC_TYPE_RSA_BUFFER);
        if (seed == NULL) {
            XFREE(lHash, heap, DYNAMIC_TYPE_RSA_BUFFER);
            return MEMORY_E;
        }
    #else
        /* hLen should never be larger than lHash since size is max digest size,
           but check before blindly calling wc_Hash */
        if ((word32)hLen > sizeof(lHash)) {
            WOLFSSL_MSG("OAEP lHash to small for digest!!");
            return MEMORY_E;
        }
    #endif

    if ((ret = wc_Hash(hType, optLabel, labelLen, lHash, hLen)) != 0) {
        WOLFSSL_MSG("OAEP hash type possibly not supported or lHash to small");
        #ifdef WOLFSSL_SMALL_STACK
            XFREE(lHash, heap, DYNAMIC_TYPE_RSA_BUFFER);
            XFREE(seed,  heap, DYNAMIC_TYPE_RSA_BUFFER);
        #endif
        return ret;
    }

    /* handles check of location for idx as well as psLen, cast to int to check
       for pkcsBlockLen(k) - 2 * hLen - 2 being negative
       This check is similar to decryption where k > 2 * hLen + 2 as msg
       size approaches 0. In decryption if k is less than or equal -- then there
       is no possible room for msg.
       k = RSA key size
       hLen = hash digest size -- will always be >= 0 at this point
     */
    if ((word32)(2 * hLen + 2) > pkcsBlockLen) {
        WOLFSSL_MSG("OAEP pad error hash to big for RSA key size");
        #ifdef WOLFSSL_SMALL_STACK
            XFREE(lHash, heap, DYNAMIC_TYPE_RSA_BUFFER);
            XFREE(seed,  heap, DYNAMIC_TYPE_RSA_BUFFER);
        #endif
        return BAD_FUNC_ARG;
    }

    if (inputLen > (pkcsBlockLen - 2 * hLen - 2)) {
        WOLFSSL_MSG("OAEP pad error message too long");
        #ifdef WOLFSSL_SMALL_STACK
            XFREE(lHash, heap, DYNAMIC_TYPE_RSA_BUFFER);
            XFREE(seed,  heap, DYNAMIC_TYPE_RSA_BUFFER);
        #endif
        return BAD_FUNC_ARG;
    }

    /* concatenate lHash || PS || 0x01 || msg */
    idx = pkcsBlockLen - 1 - inputLen;
    psLen = pkcsBlockLen - inputLen - 2 * hLen - 2;
    if (pkcsBlockLen < inputLen) { /*make sure not writing over end of buffer */
        #ifdef WOLFSSL_SMALL_STACK
            XFREE(lHash, heap, DYNAMIC_TYPE_RSA_BUFFER);
            XFREE(seed,  heap, DYNAMIC_TYPE_RSA_BUFFER);
        #endif
        return BUFFER_E;
    }
    XMEMCPY(pkcsBlock + (pkcsBlockLen - inputLen), input, inputLen);
    pkcsBlock[idx--] = 0x01; /* PS and M separator */
    while (psLen > 0 && idx > 0) {
        pkcsBlock[idx--] = 0x00;
        psLen--;
    }

    idx = idx - hLen + 1;
    XMEMCPY(pkcsBlock + idx, lHash, hLen);

    /* generate random seed */
    if ((ret = wc_RNG_GenerateBlock(rng, seed, hLen)) != 0) {
        #ifdef WOLFSSL_SMALL_STACK
            XFREE(lHash, heap, DYNAMIC_TYPE_RSA_BUFFER);
            XFREE(seed,  heap, DYNAMIC_TYPE_RSA_BUFFER);
        #endif
        return ret;
    }

    /* create maskedDB from dbMask */
    dbMask = (byte*)XMALLOC(pkcsBlockLen - hLen - 1, heap, DYNAMIC_TYPE_RSA);
    if (dbMask == NULL) {
        #ifdef WOLFSSL_SMALL_STACK
            XFREE(lHash, heap, DYNAMIC_TYPE_RSA_BUFFER);
            XFREE(seed,  heap, DYNAMIC_TYPE_RSA_BUFFER);
        #endif
        return MEMORY_E;
    }
    XMEMSET(dbMask, 0, pkcsBlockLen - hLen - 1); /* help static analyzer */

    ret = RsaMGF(mgf, seed, hLen, dbMask, pkcsBlockLen - hLen - 1, heap);
    if (ret != 0) {
        XFREE(dbMask, heap, DYNAMIC_TYPE_RSA);
        #ifdef WOLFSSL_SMALL_STACK
            XFREE(lHash, heap, DYNAMIC_TYPE_RSA_BUFFER);
            XFREE(seed,  heap, DYNAMIC_TYPE_RSA_BUFFER);
        #endif
        return ret;
    }

    i = 0;
    idx = hLen + 1;
    while (idx < pkcsBlockLen && (word32)i < (pkcsBlockLen - hLen -1)) {
        pkcsBlock[idx] = dbMask[i++] ^ pkcsBlock[idx];
        idx++;
    }
    XFREE(dbMask, heap, DYNAMIC_TYPE_RSA);


    /* create maskedSeed from seedMask */
    idx = 0;
    pkcsBlock[idx++] = 0x00;
    /* create seedMask inline */
    if ((ret = RsaMGF(mgf, pkcsBlock + hLen + 1, pkcsBlockLen - hLen - 1,
                                           pkcsBlock + 1, hLen, heap)) != 0) {
        #ifdef WOLFSSL_SMALL_STACK
            XFREE(lHash, heap, DYNAMIC_TYPE_RSA_BUFFER);
            XFREE(seed,  heap, DYNAMIC_TYPE_RSA_BUFFER);
        #endif
        return ret;
    }

    /* xor created seedMask with seed to make maskedSeed */
    i = 0;
    while (idx < (word32)(hLen + 1) && i < hLen) {
        pkcsBlock[idx] = pkcsBlock[idx] ^ seed[i++];
        idx++;
    }

    #ifdef WOLFSSL_SMALL_STACK
        XFREE(lHash, heap, DYNAMIC_TYPE_RSA_BUFFER);
        XFREE(seed,  heap, DYNAMIC_TYPE_RSA_BUFFER);
    #endif
    (void)padValue;

    return 0;
}
#endif /* !WC_NO_RSA_OAEP */

#ifdef WC_RSA_PSS

/* 0x00 .. 0x00 0x01 | Salt | Gen Hash | 0xbc
 * XOR MGF over all bytes down to end of Salt
 * Gen Hash = HASH(8 * 0x00 | Message Hash | Salt)
 *
 * input         Digest of the message.
 * inputLen      Length of digest.
 * pkcsBlock     Buffer to write to.
 * pkcsBlockLen  Length of buffer to write to.
 * rng           Random number generator (for salt).
 * htype         Hash function to use.
 * mgf           Mask generation function.
 * saltLen       Length of salt to put in padding.
 * bits          Length of key in bits.
 * heap          Used for dynamic memory allocation.
 * returns 0 on success, PSS_SALTLEN_E when the salt length is invalid
 * and other negative values on error.
 */
static int RsaPad_PSS(const byte* input, word32 inputLen, byte* pkcsBlock,
        word32 pkcsBlockLen, WC_RNG* rng, enum wc_HashType hType, int mgf,
        int saltLen, int bits, void* heap)
{
    int   ret = 0;
    int   hLen, i, o, maskLen, hiBits;
    byte* m;
    byte* s;
#if defined(WOLFSSL_PSS_LONG_SALT) || defined(WOLFSSL_PSS_SALT_LEN_DISCOVER)
    #if defined(WOLFSSL_NO_MALLOC) && !defined(WOLFSSL_STATIC_MEMORY)
        byte salt[RSA_MAX_SIZE/8 + RSA_PSS_PAD_SZ];
    #else
        byte* salt = NULL;
    #endif
#else
    byte salt[WC_MAX_DIGEST_SIZE];
#endif

#if defined(WOLFSSL_PSS_LONG_SALT) || defined(WOLFSSL_PSS_SALT_LEN_DISCOVER)
    if (pkcsBlockLen > RSA_MAX_SIZE/8) {
        return MEMORY_E;
    }
#endif

    hLen = wc_HashGetDigestSize(hType);
    if (hLen < 0)
        return hLen;

    hiBits = (bits - 1) & 0x7;
    if (hiBits == 0) {
        *(pkcsBlock++) = 0;
        pkcsBlockLen--;
    }

    if (saltLen == RSA_PSS_SALT_LEN_DEFAULT) {
        saltLen = hLen;
        #ifdef WOLFSSL_SHA512
            /* See FIPS 186-4 section 5.5 item (e). */
            if (bits == 1024 && hLen == WC_SHA512_DIGEST_SIZE) {
                saltLen = RSA_PSS_SALT_MAX_SZ;
            }
        #endif
    }
#ifndef WOLFSSL_PSS_LONG_SALT
    else if (saltLen > hLen) {
        return PSS_SALTLEN_E;
    }
#endif
#ifndef WOLFSSL_PSS_SALT_LEN_DISCOVER
    else if (saltLen < RSA_PSS_SALT_LEN_DEFAULT) {
        return PSS_SALTLEN_E;
    }
#else
    else if (saltLen == RSA_PSS_SALT_LEN_DISCOVER) {
        saltLen = (int)pkcsBlockLen - hLen - 2;
        if (saltLen < 0) {
            return PSS_SALTLEN_E;
        }
    }
    else if (saltLen < RSA_PSS_SALT_LEN_DISCOVER) {
        return PSS_SALTLEN_E;
    }
#endif
    if ((int)pkcsBlockLen - hLen < saltLen + 2) {
        return PSS_SALTLEN_E;
    }

    maskLen = pkcsBlockLen - 1 - hLen;

#if defined(WOLFSSL_PSS_LONG_SALT) || defined(WOLFSSL_PSS_SALT_LEN_DISCOVER)
    #if !defined(WOLFSSL_NO_MALLOC) || defined(WOLFSSL_STATIC_MEMORY)
        salt = (byte*)XMALLOC(RSA_PSS_PAD_SZ + inputLen + saltLen, heap,
                                                       DYNAMIC_TYPE_RSA_BUFFER);
        if (salt == NULL) {
            return MEMORY_E;
        }
    #endif
    s = m = salt;
    XMEMSET(m, 0, RSA_PSS_PAD_SZ);
    m += RSA_PSS_PAD_SZ;
    XMEMCPY(m, input, inputLen);
    m += inputLen;
    o = (int)(m - s);
    if (saltLen > 0) {
        ret = wc_RNG_GenerateBlock(rng, m, saltLen);
        if (ret == 0) {
            m += saltLen;
        }
    }
#else
    s = m = pkcsBlock;
    XMEMSET(m, 0, RSA_PSS_PAD_SZ);
    m += RSA_PSS_PAD_SZ;
    XMEMCPY(m, input, inputLen);
    m += inputLen;
    o = 0;
    if (saltLen > 0) {
        ret = wc_RNG_GenerateBlock(rng, salt, saltLen);
        if (ret == 0) {
            XMEMCPY(m, salt, saltLen);
            m += saltLen;
        }
    }
#endif
    if (ret == 0) {
        /* Put Hash at end of pkcsBlock - 1 */
        ret = wc_Hash(hType, s, (word32)(m - s), pkcsBlock + maskLen, hLen);
    }
    if (ret == 0) {
        pkcsBlock[pkcsBlockLen - 1] = RSA_PSS_PAD_TERM;

        ret = RsaMGF(mgf, pkcsBlock + maskLen, hLen, pkcsBlock, maskLen, heap);
    }
    if (ret == 0) {
        pkcsBlock[0] &= (1 << hiBits) - 1;

        m = pkcsBlock + maskLen - saltLen - 1;
        *(m++) ^= 0x01;
        for (i = 0; i < saltLen; i++) {
            m[i] ^= salt[o + i];
        }
    }

#if defined(WOLFSSL_PSS_LONG_SALT) || defined(WOLFSSL_PSS_SALT_LEN_DISCOVER)
    #if !defined(WOLFSSL_NO_MALLOC) || defined(WOLFSSL_STATIC_MEMORY)
        if (salt != NULL) {
            XFREE(salt, heap, DYNAMIC_TYPE_RSA_BUFFER);
        }
    #endif
#endif
    return ret;
}
#endif /* WC_RSA_PSS */
#endif /* !WC_NO_RNG */

static int RsaPad(const byte* input, word32 inputLen, byte* pkcsBlock,
                           word32 pkcsBlockLen, byte padValue, WC_RNG* rng)
{
    if (input == NULL || inputLen == 0 || pkcsBlock == NULL ||
                                                        pkcsBlockLen == 0) {
        return BAD_FUNC_ARG;
    }

    pkcsBlock[0] = 0x0;       /* set first byte to zero and advance */
    pkcsBlock++; pkcsBlockLen--;
    pkcsBlock[0] = padValue;  /* insert padValue */

    if (padValue == RSA_BLOCK_TYPE_1) {
        if (pkcsBlockLen < inputLen + 2) {
            WOLFSSL_MSG("RsaPad error, invalid length");
            return RSA_PAD_E;
        }

        /* pad with 0xff bytes */
        XMEMSET(&pkcsBlock[1], 0xFF, pkcsBlockLen - inputLen - 2);
    }
    else {
#if !defined(WOLFSSL_RSA_VERIFY_ONLY) && !defined(WC_NO_RNG)
        /* pad with non-zero random bytes */
        word32 padLen, i;
        int    ret;

        if (pkcsBlockLen < inputLen + 1) {
            WOLFSSL_MSG("RsaPad error, invalid length");
            return RSA_PAD_E;
        }

        padLen = pkcsBlockLen - inputLen - 1;
        ret    = wc_RNG_GenerateBlock(rng, &pkcsBlock[1], padLen);
        if (ret != 0) {
            return ret;
        }

        /* remove zeros */
        for (i = 1; i < padLen; i++) {
            if (pkcsBlock[i] == 0) pkcsBlock[i] = 0x01;
        }
#else
        (void)rng;
        return RSA_WRONG_TYPE_E;
#endif
    }

    pkcsBlock[pkcsBlockLen-inputLen-1] = 0;     /* separator */
    XMEMCPY(pkcsBlock+pkcsBlockLen-inputLen, input, inputLen);

    return 0;
}

/* helper function to direct which padding is used */
int wc_RsaPad_ex(const byte* input, word32 inputLen, byte* pkcsBlock,
    word32 pkcsBlockLen, byte padValue, WC_RNG* rng, int padType,
    enum wc_HashType hType, int mgf, byte* optLabel, word32 labelLen,
    int saltLen, int bits, void* heap)
{
    int ret;

    switch (padType)
    {
        case WC_RSA_PKCSV15_PAD:
            /*WOLFSSL_MSG("wolfSSL Using RSA PKCSV15 padding");*/
            ret = RsaPad(input, inputLen, pkcsBlock, pkcsBlockLen,
                                                                 padValue, rng);
            break;

#ifndef WC_NO_RNG
    #ifndef WC_NO_RSA_OAEP
        case WC_RSA_OAEP_PAD:
            WOLFSSL_MSG("wolfSSL Using RSA OAEP padding");
            ret = RsaPad_OAEP(input, inputLen, pkcsBlock, pkcsBlockLen,
                           padValue, rng, hType, mgf, optLabel, labelLen, heap);
            break;
    #endif

    #ifdef WC_RSA_PSS
        case WC_RSA_PSS_PAD:
            WOLFSSL_MSG("wolfSSL Using RSA PSS padding");
            ret = RsaPad_PSS(input, inputLen, pkcsBlock, pkcsBlockLen, rng,
                                               hType, mgf, saltLen, bits, heap);
            break;
    #endif
#endif /* !WC_NO_RNG */

    #ifdef WC_RSA_NO_PADDING
        case WC_RSA_NO_PAD:
            WOLFSSL_MSG("wolfSSL Using NO padding");

            /* In the case of no padding being used check that input is exactly
             * the RSA key length */
            if (bits <= 0 || inputLen != ((word32)bits/WOLFSSL_BIT_SIZE)) {
                WOLFSSL_MSG("Bad input size");
                ret = RSA_PAD_E;
            }
            else {
                XMEMCPY(pkcsBlock, input, inputLen);
                ret = 0;
            }
            break;
    #endif

        default:
            WOLFSSL_MSG("Unknown RSA Pad Type");
            ret = RSA_PAD_E;
    }

    /* silence warning if not used with padding scheme */
    (void)input;
    (void)inputLen;
    (void)pkcsBlock;
    (void)pkcsBlockLen;
    (void)padValue;
    (void)rng;
    (void)padType;
    (void)hType;
    (void)mgf;
    (void)optLabel;
    (void)labelLen;
    (void)saltLen;
    (void)bits;
    (void)heap;

    return ret;
}
#endif /* WOLFSSL_RSA_VERIFY_ONLY */


/* UnPadding */
#ifndef WC_NO_RSA_OAEP
/* UnPad plaintext, set start to *output, return length of plaintext,
 * < 0 on error */
static int RsaUnPad_OAEP(byte *pkcsBlock, unsigned int pkcsBlockLen,
                            byte **output, enum wc_HashType hType, int mgf,
                            byte* optLabel, word32 labelLen, void* heap)
{
    int hLen;
    int ret;
    byte h[WC_MAX_DIGEST_SIZE]; /* max digest size */
    byte* tmp;
    word32 idx;

    /* no label is allowed, but catch if no label provided and length > 0 */
    if (optLabel == NULL && labelLen > 0) {
        return BUFFER_E;
    }

    hLen = wc_HashGetDigestSize(hType);
    if ((hLen < 0) || (pkcsBlockLen < (2 * (word32)hLen + 2))) {
        return BAD_FUNC_ARG;
    }

    tmp = (byte*)XMALLOC(pkcsBlockLen, heap, DYNAMIC_TYPE_RSA_BUFFER);
    if (tmp == NULL) {
        return MEMORY_E;
    }
    XMEMSET(tmp, 0, pkcsBlockLen);

    /* find seedMask value */
    if ((ret = RsaMGF(mgf, (byte*)(pkcsBlock + (hLen + 1)),
                            pkcsBlockLen - hLen - 1, tmp, hLen, heap)) != 0) {
        XFREE(tmp, heap, DYNAMIC_TYPE_RSA_BUFFER);
        return ret;
    }

    /* xor seedMask value with maskedSeed to get seed value */
    for (idx = 0; idx < (word32)hLen; idx++) {
        tmp[idx] = tmp[idx] ^ pkcsBlock[1 + idx];
    }

    /* get dbMask value */
    if ((ret = RsaMGF(mgf, tmp, hLen, tmp + hLen,
                                       pkcsBlockLen - hLen - 1, heap)) != 0) {
        XFREE(tmp, NULL, DYNAMIC_TYPE_RSA_BUFFER);
        return ret;
    }

    /* get DB value by doing maskedDB xor dbMask */
    for (idx = 0; idx < (pkcsBlockLen - hLen - 1); idx++) {
        pkcsBlock[hLen + 1 + idx] = pkcsBlock[hLen + 1 + idx] ^ tmp[idx + hLen];
    }

    /* done with use of tmp buffer */
    XFREE(tmp, heap, DYNAMIC_TYPE_RSA_BUFFER);

    /* advance idx to index of PS and msg separator, account for PS size of 0*/
    idx = hLen + 1 + hLen;
    while (idx < pkcsBlockLen && pkcsBlock[idx] == 0) {idx++;}

    /* create hash of label for comparison with hash sent */
    if ((ret = wc_Hash(hType, optLabel, labelLen, h, hLen)) != 0) {
        return ret;
    }

    /* say no to chosen ciphertext attack.
       Comparison of lHash, Y, and separator value needs to all happen in
       constant time.
       Attackers should not be able to get error condition from the timing of
       these checks.
     */
    ret = 0;
    ret |= ConstantCompare(pkcsBlock + hLen + 1, h, hLen);
    ret += pkcsBlock[idx++] ^ 0x01; /* separator value is 0x01 */
    ret += pkcsBlock[0]     ^ 0x00; /* Y, the first value, should be 0 */

    /* Return 0 data length on error. */
    idx = ctMaskSelInt(ctMaskEq(ret, 0), idx, pkcsBlockLen);

    /* adjust pointer to correct location in array and return size of M */
    *output = (byte*)(pkcsBlock + idx);
    return pkcsBlockLen - idx;
}
#endif /* WC_NO_RSA_OAEP */

#ifdef WC_RSA_PSS
/* 0x00 .. 0x00 0x01 | Salt | Gen Hash | 0xbc
 * MGF over all bytes down to end of Salt
 *
 * pkcsBlock     Buffer holding decrypted data.
 * pkcsBlockLen  Length of buffer.
 * htype         Hash function to use.
 * mgf           Mask generation function.
 * saltLen       Length of salt to put in padding.
 * bits          Length of key in bits.
 * heap          Used for dynamic memory allocation.
 * returns 0 on success, PSS_SALTLEN_E when the salt length is invalid,
 * BAD_PADDING_E when the padding is not valid, MEMORY_E when allocation fails
 * and other negative values on error.
 */
static int RsaUnPad_PSS(byte *pkcsBlock, unsigned int pkcsBlockLen,
                        byte **output, enum wc_HashType hType, int mgf,
                        int saltLen, int bits, void* heap)
{
    int   ret;
    byte* tmp;
    int   hLen, i, maskLen;
#ifdef WOLFSSL_SHA512
    int orig_bits = bits;
#endif
#if defined(WOLFSSL_NO_MALLOC) && !defined(WOLFSSL_STATIC_MEMORY)
    byte tmp_buf[RSA_MAX_SIZE/8];
    tmp = tmp_buf;

    if (pkcsBlockLen > RSA_MAX_SIZE/8) {
        return MEMORY_E;
    }
#endif

    hLen = wc_HashGetDigestSize(hType);
    if (hLen < 0)
        return hLen;
    bits = (bits - 1) & 0x7;
    if ((pkcsBlock[0] & (0xff << bits)) != 0) {
        return BAD_PADDING_E;
    }
    if (bits == 0) {
        pkcsBlock++;
        pkcsBlockLen--;
    }
    maskLen = (int)pkcsBlockLen - 1 - hLen;
    if (maskLen < 0) {
        WOLFSSL_MSG("RsaUnPad_PSS: Hash too large");
        return WC_KEY_SIZE_E;
    }

    if (saltLen == RSA_PSS_SALT_LEN_DEFAULT) {
        saltLen = hLen;
        #ifdef WOLFSSL_SHA512
            /* See FIPS 186-4 section 5.5 item (e). */
            if (orig_bits == 1024 && hLen == WC_SHA512_DIGEST_SIZE)
                saltLen = RSA_PSS_SALT_MAX_SZ;
        #endif
    }
#ifndef WOLFSSL_PSS_LONG_SALT
    else if (saltLen > hLen)
        return PSS_SALTLEN_E;
#endif
#ifndef WOLFSSL_PSS_SALT_LEN_DISCOVER
    else if (saltLen < RSA_PSS_SALT_LEN_DEFAULT)
        return PSS_SALTLEN_E;
    if (maskLen < saltLen + 1) {
        return PSS_SALTLEN_E;
    }
#else
    else if (saltLen < RSA_PSS_SALT_LEN_DISCOVER)
        return PSS_SALTLEN_E;
    if (saltLen != RSA_PSS_SALT_LEN_DISCOVER && maskLen < saltLen + 1) {
        return WC_KEY_SIZE_E;
    }
#endif

    if (pkcsBlock[pkcsBlockLen - 1] != RSA_PSS_PAD_TERM) {
        WOLFSSL_MSG("RsaUnPad_PSS: Padding Term Error");
        return BAD_PADDING_E;
    }

#if !defined(WOLFSSL_NO_MALLOC) || defined(WOLFSSL_STATIC_MEMORY)
    tmp = (byte*)XMALLOC(maskLen, heap, DYNAMIC_TYPE_RSA_BUFFER);
    if (tmp == NULL) {
        return MEMORY_E;
    }
#endif

    if ((ret = RsaMGF(mgf, pkcsBlock + maskLen, hLen, tmp, maskLen,
                                                                  heap)) != 0) {
        XFREE(tmp, heap, DYNAMIC_TYPE_RSA_BUFFER);
        return ret;
    }

    tmp[0] &= (1 << bits) - 1;
    pkcsBlock[0] &= (1 << bits) - 1;
#ifdef WOLFSSL_PSS_SALT_LEN_DISCOVER
    if (saltLen == RSA_PSS_SALT_LEN_DISCOVER) {
        for (i = 0; i < maskLen - 1; i++) {
            if (tmp[i] != pkcsBlock[i]) {
                break;
            }
        }
        if (tmp[i] != (pkcsBlock[i] ^ 0x01)) {
            XFREE(tmp, heap, DYNAMIC_TYPE_RSA_BUFFER);
            WOLFSSL_MSG("RsaUnPad_PSS: Padding Error Match");
            return PSS_SALTLEN_RECOVER_E;
        }
        saltLen = maskLen - (i + 1);
    }
    else
#endif
    {
        for (i = 0; i < maskLen - 1 - saltLen; i++) {
            if (tmp[i] != pkcsBlock[i]) {
                XFREE(tmp, heap, DYNAMIC_TYPE_RSA_BUFFER);
                WOLFSSL_MSG("RsaUnPad_PSS: Padding Error Match");
                return PSS_SALTLEN_E;
            }
        }
        if (tmp[i] != (pkcsBlock[i] ^ 0x01)) {
            XFREE(tmp, heap, DYNAMIC_TYPE_RSA_BUFFER);
            WOLFSSL_MSG("RsaUnPad_PSS: Padding Error End");
            return PSS_SALTLEN_E;
        }
    }
    for (i++; i < maskLen; i++)
        pkcsBlock[i] ^= tmp[i];

#if !defined(WOLFSSL_NO_MALLOC) || defined(WOLFSSL_STATIC_MEMORY)
    XFREE(tmp, heap, DYNAMIC_TYPE_RSA_BUFFER);
#endif

    *output = pkcsBlock + maskLen - saltLen;
    return saltLen + hLen;
}
#endif

/* UnPad plaintext, set start to *output, return length of plaintext,
 * < 0 on error */
static int RsaUnPad(const byte *pkcsBlock, unsigned int pkcsBlockLen,
                    byte **output, byte padValue)
{
    int    ret = BAD_FUNC_ARG;
    word16 i;
#ifndef WOLFSSL_RSA_VERIFY_ONLY
    byte   invalid = 0;
#endif

    if (output == NULL || pkcsBlockLen == 0 || pkcsBlockLen > 0xFFFF) {
        return BAD_FUNC_ARG;
    }

    if (padValue == RSA_BLOCK_TYPE_1) {
        /* First byte must be 0x00 and Second byte, block type, 0x01 */
        if (pkcsBlock[0] != 0 || pkcsBlock[1] != RSA_BLOCK_TYPE_1) {
            WOLFSSL_MSG("RsaUnPad error, invalid formatting");
            return RSA_PAD_E;
        }

        /* check the padding until we find the separator */
        for (i = 2; i < pkcsBlockLen && pkcsBlock[i++] == 0xFF; ) { }

        /* Minimum of 11 bytes of pre-message data and must have separator. */
        if (i < RSA_MIN_PAD_SZ || pkcsBlock[i-1] != 0) {
            WOLFSSL_MSG("RsaUnPad error, bad formatting");
            return RSA_PAD_E;
        }

        *output = (byte *)(pkcsBlock + i);
        ret = pkcsBlockLen - i;
    }
#ifndef WOLFSSL_RSA_VERIFY_ONLY
    else {
        word16 j;
        word16 pastSep = 0;

        /* Decrypted with private key - unpad must be constant time. */
        for (i = 0, j = 2; j < pkcsBlockLen; j++) {
           /* Update i if not passed the separator and at separator. */
            i |= (~pastSep) & ctMask16Eq(pkcsBlock[j], 0x00) & (j + 1);
            pastSep |= ctMask16Eq(pkcsBlock[j], 0x00);
        }

        /* Minimum of 11 bytes of pre-message data - including leading 0x00. */
        invalid |= ctMaskLT(i, RSA_MIN_PAD_SZ);
        /* Must have seen separator. */
        invalid |= ~pastSep;
        /* First byte must be 0x00. */
        invalid |= ctMaskNotEq(pkcsBlock[0], 0x00);
        /* Check against expected block type: padValue */
        invalid |= ctMaskNotEq(pkcsBlock[1], padValue);

        *output = (byte *)(pkcsBlock + i);
        ret = ((int)~invalid) & (pkcsBlockLen - i);
    }
#endif

    return ret;
}

/* helper function to direct unpadding
 *
 * bits is the key modulus size in bits
 */
int wc_RsaUnPad_ex(byte* pkcsBlock, word32 pkcsBlockLen, byte** out,
                   byte padValue, int padType, enum wc_HashType hType,
                   int mgf, byte* optLabel, word32 labelLen, int saltLen,
                   int bits, void* heap)
{
    int ret;

    switch (padType) {
        case WC_RSA_PKCSV15_PAD:
            /*WOLFSSL_MSG("wolfSSL Using RSA PKCSV15 un-padding");*/
            ret = RsaUnPad(pkcsBlock, pkcsBlockLen, out, padValue);
            break;

    #ifndef WC_NO_RSA_OAEP
        case WC_RSA_OAEP_PAD:
            WOLFSSL_MSG("wolfSSL Using RSA OAEP un-padding");
            ret = RsaUnPad_OAEP((byte*)pkcsBlock, pkcsBlockLen, out,
                                        hType, mgf, optLabel, labelLen, heap);
            break;
    #endif

    #ifdef WC_RSA_PSS
        case WC_RSA_PSS_PAD:
            WOLFSSL_MSG("wolfSSL Using RSA PSS un-padding");
            ret = RsaUnPad_PSS((byte*)pkcsBlock, pkcsBlockLen, out, hType, mgf,
                                                           saltLen, bits, heap);
            break;
    #endif

    #ifdef WC_RSA_NO_PADDING
        case WC_RSA_NO_PAD:
            WOLFSSL_MSG("wolfSSL Using NO un-padding");

            /* In the case of no padding being used check that input is exactly
             * the RSA key length */
            if (bits <= 0 || pkcsBlockLen !=
                         ((word32)(bits+WOLFSSL_BIT_SIZE-1)/WOLFSSL_BIT_SIZE)) {
                WOLFSSL_MSG("Bad input size");
                ret = RSA_PAD_E;
            }
            else {
                if (out != NULL) {
                    *out = pkcsBlock;
                }
                ret = pkcsBlockLen;
            }
            break;
    #endif /* WC_RSA_NO_PADDING */

        default:
            WOLFSSL_MSG("Unknown RSA UnPad Type");
            ret = RSA_PAD_E;
    }

    /* silence warning if not used with padding scheme */
    (void)hType;
    (void)mgf;
    (void)optLabel;
    (void)labelLen;
    (void)saltLen;
    (void)bits;
    (void)heap;

    return ret;
}

#if defined(WOLFSSL_XILINX_CRYPT)
/*
 * Xilinx hardened crypto acceleration.
 *
 * Returns 0 on success and negative values on error.
 */
static int wc_RsaFunctionXil(const byte* in, word32 inLen, byte* out,
                          word32* outLen, int type, RsaKey* key, WC_RNG* rng)
{
    int    ret = 0;
    word32 keyLen;
    (void)rng;

    keyLen = wc_RsaEncryptSize(key);
    if (keyLen > *outLen) {
        WOLFSSL_MSG("Output buffer is not big enough");
        return BAD_FUNC_ARG;
    }

    if (inLen != keyLen) {
        WOLFSSL_MSG("Expected that inLen equals RSA key length");
        return BAD_FUNC_ARG;
    }

    switch(type) {
    case RSA_PRIVATE_DECRYPT:
    case RSA_PRIVATE_ENCRYPT:
        /* Currently public exponent is loaded by default.
         * In SDK 2017.1 RSA exponent values are expected to be of 4 bytes
         * leading to private key operations with Xsecure_RsaDecrypt not being
         * supported */
        ret = RSA_WRONG_TYPE_E;
        break;
    case RSA_PUBLIC_ENCRYPT:
    case RSA_PUBLIC_DECRYPT:
        if (XSecure_RsaDecrypt(&(key->xRsa), in, out) != XST_SUCCESS) {
            ret = BAD_STATE_E;
        }
        break;
    default:
        ret = RSA_WRONG_TYPE_E;
    }

    *outLen = keyLen;

    return ret;
}
#endif /* WOLFSSL_XILINX_CRYPT */

#ifdef WC_RSA_NONBLOCK
static int wc_RsaFunctionNonBlock(const byte* in, word32 inLen, byte* out,
                          word32* outLen, int type, RsaKey* key)
{
    int    ret = 0;
    word32 keyLen, len;

    if (key == NULL || key->nb == NULL) {
        return BAD_FUNC_ARG;
    }

    if (key->nb->exptmod.state == TFM_EXPTMOD_NB_INIT) {
        if (mp_init(&key->nb->tmp) != MP_OKAY) {
            ret = MP_INIT_E;
        }

        if (ret == 0) {
            if (mp_read_unsigned_bin(&key->nb->tmp, (byte*)in, inLen) != MP_OKAY) {
                ret = MP_READ_E;
            }
        }
    }

    if (ret == 0) {
        switch(type) {
        case RSA_PRIVATE_DECRYPT:
        case RSA_PRIVATE_ENCRYPT:
            ret = fp_exptmod_nb(&key->nb->exptmod, &key->nb->tmp, &key->d,
                &key->n, &key->nb->tmp);
            if (ret == FP_WOULDBLOCK)
                return ret;
            if (ret != MP_OKAY)
                ret = MP_EXPTMOD_E;
            break;

        case RSA_PUBLIC_ENCRYPT:
        case RSA_PUBLIC_DECRYPT:
            ret = fp_exptmod_nb(&key->nb->exptmod, &key->nb->tmp, &key->e,
                &key->n, &key->nb->tmp);
            if (ret == FP_WOULDBLOCK)
                return ret;
            if (ret != MP_OKAY)
                ret = MP_EXPTMOD_E;
            break;
        default:
            ret = RSA_WRONG_TYPE_E;
            break;
        }
    }

    if (ret == 0) {
        keyLen = wc_RsaEncryptSize(key);
        if (keyLen > *outLen)
            ret = RSA_BUFFER_E;
    }
    if (ret == 0) {
        len = mp_unsigned_bin_size(&key->nb->tmp);

        /* pad front w/ zeros to match key length */
        while (len < keyLen) {
            *out++ = 0x00;
            len++;
        }

        *outLen = keyLen;

        /* convert */
        if (mp_to_unsigned_bin(&key->nb->tmp, out) != MP_OKAY) {
             ret = MP_TO_E;
        }
    }

    mp_clear(&key->nb->tmp);

    return ret;
}
#endif /* WC_RSA_NONBLOCK */

#ifdef WOLFSSL_AFALG_XILINX_RSA
#ifndef ERROR_OUT
#define ERROR_OUT(x) ret = (x); goto done
#endif

static const char WC_TYPE_ASYMKEY[] = "skcipher";
static const char WC_NAME_RSA[] = "xilinx-zynqmp-rsa";
#ifndef MAX_XILINX_RSA_KEY
    /* max key size of 4096 bits / 512 bytes */
    #define MAX_XILINX_RSA_KEY 512
#endif
static const byte XILINX_RSA_FLAG[] = {0x1};


/* AF_ALG implementation of RSA */
static int wc_RsaFunctionSync(const byte* in, word32 inLen, byte* out,
                          word32* outLen, int type, RsaKey* key, WC_RNG* rng)
{
    struct msghdr   msg;
    struct cmsghdr* cmsg;
    struct iovec      iov;
    byte*  keyBuf   = NULL;
    word32 keyBufSz = 0;
    char cbuf[CMSG_SPACE(4) + CMSG_SPACE(sizeof(struct af_alg_iv) + 1)] = {0};
    int    ret = 0;
    int    op  = 0;    /* decryption vs encryption flag */
    word32 keyLen;

    /* input and output buffer need to be aligned */
    ALIGN64 byte outBuf[MAX_XILINX_RSA_KEY];
    ALIGN64 byte inBuf[MAX_XILINX_RSA_KEY];

    XMEMSET(&msg, 0, sizeof(struct msghdr));
    (void)rng;

    keyLen = wc_RsaEncryptSize(key);
    if (keyLen > *outLen) {
        ERROR_OUT(RSA_BUFFER_E);
    }

    if (keyLen > MAX_XILINX_RSA_KEY) {
        WOLFSSL_MSG("RSA key size larger than supported");
        ERROR_OUT(BAD_FUNC_ARG);
    }

    if ((keyBuf = (byte*)XMALLOC(keyLen * 2, key->heap, DYNAMIC_TYPE_KEY))
            == NULL) {
        ERROR_OUT(MEMORY_E);
    }

    if ((ret = mp_to_unsigned_bin(&(key->n), keyBuf)) != MP_OKAY) {
        ERROR_OUT(MP_TO_E);
    }

    switch(type) {
        case RSA_PRIVATE_DECRYPT:
        case RSA_PRIVATE_ENCRYPT:
            op = 1; /* set as decrypt */
            {
                keyBufSz = mp_unsigned_bin_size(&(key->d));
                if ((mp_to_unsigned_bin(&(key->d), keyBuf + keyLen))
                        != MP_OKAY) {
                    ERROR_OUT(MP_TO_E);
                }
            }
            break;

        case RSA_PUBLIC_DECRYPT:
        case RSA_PUBLIC_ENCRYPT: {
            word32 exp = 0;
            word32 eSz = mp_unsigned_bin_size(&(key->e));
            if ((mp_to_unsigned_bin(&(key->e), (byte*)&exp +
                            (sizeof(word32) - eSz))) != MP_OKAY) {
                ERROR_OUT(MP_TO_E);
            }
            keyBufSz = sizeof(word32);
            XMEMCPY(keyBuf + keyLen, (byte*)&exp, keyBufSz);
            break;
        }

        default:
            ERROR_OUT(RSA_WRONG_TYPE_E);
    }
    keyBufSz += keyLen; /* add size of modulus */

    /* check for existing sockets before creating new ones */
    if (key->alFd > 0) {
        close(key->alFd);
        key->alFd = WC_SOCK_NOTSET;
    }
    if (key->rdFd > 0) {
        close(key->rdFd);
        key->rdFd = WC_SOCK_NOTSET;
    }

    /* create new sockets and set the key to use */
    if ((key->alFd = wc_Afalg_Socket()) < 0) {
        WOLFSSL_MSG("Unable to create socket");
        ERROR_OUT(key->alFd);
    }
    if ((key->rdFd = wc_Afalg_CreateRead(key->alFd, WC_TYPE_ASYMKEY,
                    WC_NAME_RSA)) < 0) {
        WOLFSSL_MSG("Unable to bind and create read/send socket");
        ERROR_OUT(key->rdFd);
    }
    if ((ret = setsockopt(key->alFd, SOL_ALG, ALG_SET_KEY, keyBuf,
                    keyBufSz)) < 0) {
        WOLFSSL_MSG("Error setting RSA key");
        ERROR_OUT(ret);
    }

    msg.msg_control    = cbuf;
    msg.msg_controllen = sizeof(cbuf);
    cmsg = CMSG_FIRSTHDR(&msg);
    if ((ret = wc_Afalg_SetOp(cmsg, op)) < 0) {
        ERROR_OUT(ret);
    }

    /* set flag in IV spot, needed for Xilinx hardware acceleration use */
    cmsg = CMSG_NXTHDR(&msg, cmsg);
    if ((ret = wc_Afalg_SetIv(cmsg, (byte*)XILINX_RSA_FLAG,
                    sizeof(XILINX_RSA_FLAG))) != 0) {
        ERROR_OUT(ret);
    }

    /* compose and send msg */
    XMEMCPY(inBuf, (byte*)in, inLen); /* for alignment */
    iov.iov_base = inBuf;
    iov.iov_len  = inLen;
    msg.msg_iov  = &iov;
    msg.msg_iovlen = 1;
    if ((ret = sendmsg(key->rdFd, &msg, 0)) <= 0) {
        ERROR_OUT(WC_AFALG_SOCK_E);
    }

    if ((ret = read(key->rdFd, outBuf, inLen)) <= 0) {
        ERROR_OUT(WC_AFALG_SOCK_E);
    }
    XMEMCPY(out, outBuf, ret);
    *outLen = keyLen;

done:
    /* clear key data and free buffer */
    if (keyBuf != NULL) {
        ForceZero(keyBuf, keyBufSz);
    }
    XFREE(keyBuf, key->heap, DYNAMIC_TYPE_KEY);

    if (key->alFd > 0) {
        close(key->alFd);
        key->alFd = WC_SOCK_NOTSET;
    }
    if (key->rdFd > 0) {
        close(key->rdFd);
        key->rdFd = WC_SOCK_NOTSET;
    }

    return ret;
}

#else
static int wc_RsaFunctionSync(const byte* in, word32 inLen, byte* out,
                          word32* outLen, int type, RsaKey* key, WC_RNG* rng)
{
#ifndef WOLFSSL_SP_MATH
#ifdef WOLFSSL_SMALL_STACK
    mp_int* tmp;
#ifdef WC_RSA_BLINDING
    mp_int* rnd;
    mp_int* rndi;
#endif
#else
    mp_int tmp[1];
#ifdef WC_RSA_BLINDING
    mp_int rnd[1], rndi[1];
#endif
#endif
    int    ret = 0;
    word32 keyLen = 0;
#endif

#ifdef WOLFSSL_HAVE_SP_RSA
#ifndef WOLFSSL_SP_NO_2048
    if (mp_count_bits(&key->n) == 2048) {
        switch(type) {
#ifndef WOLFSSL_RSA_PUBLIC_ONLY
        case RSA_PRIVATE_DECRYPT:
        case RSA_PRIVATE_ENCRYPT:
    #ifdef WC_RSA_BLINDING
            if (rng == NULL)
                return MISSING_RNG_E;
    #endif
    #ifndef RSA_LOW_MEM
            return sp_RsaPrivate_2048(in, inLen, &key->d, &key->p, &key->q,
                                      &key->dP, &key->dQ, &key->u, &key->n,
                                      out, outLen);
    #else
            return sp_RsaPrivate_2048(in, inLen, &key->d, &key->p, &key->q,
                                      NULL, NULL, NULL, &key->n, out, outLen);
    #endif
#endif
        case RSA_PUBLIC_ENCRYPT:
        case RSA_PUBLIC_DECRYPT:
            return sp_RsaPublic_2048(in, inLen, &key->e, &key->n, out, outLen);
        }
    }
#endif
#ifndef WOLFSSL_SP_NO_3072
    if (mp_count_bits(&key->n) == 3072) {
        switch(type) {
#ifndef WOLFSSL_RSA_PUBLIC_ONLY
        case RSA_PRIVATE_DECRYPT:
        case RSA_PRIVATE_ENCRYPT:
    #ifdef WC_RSA_BLINDING
            if (rng == NULL)
                return MISSING_RNG_E;
    #endif
    #ifndef RSA_LOW_MEM
            return sp_RsaPrivate_3072(in, inLen, &key->d, &key->p, &key->q,
                                      &key->dP, &key->dQ, &key->u, &key->n,
                                      out, outLen);
    #else
            return sp_RsaPrivate_3072(in, inLen, &key->d, &key->p, &key->q,
                                      NULL, NULL, NULL, &key->n, out, outLen);
    #endif
#endif
        case RSA_PUBLIC_ENCRYPT:
        case RSA_PUBLIC_DECRYPT:
            return sp_RsaPublic_3072(in, inLen, &key->e, &key->n, out, outLen);
        }
    }
#endif
#ifdef WOLFSSL_SP_4096
    if (mp_count_bits(&key->n) == 4096) {
        switch(type) {
#ifndef WOLFSSL_RSA_PUBLIC_ONLY
        case RSA_PRIVATE_DECRYPT:
        case RSA_PRIVATE_ENCRYPT:
    #ifdef WC_RSA_BLINDING
            if (rng == NULL)
                return MISSING_RNG_E;
    #endif
    #ifndef RSA_LOW_MEM
            return sp_RsaPrivate_4096(in, inLen, &key->d, &key->p, &key->q,
                                      &key->dP, &key->dQ, &key->u, &key->n,
                                      out, outLen);
    #else
            return sp_RsaPrivate_4096(in, inLen, &key->d, &key->p, &key->q,
                                      NULL, NULL, NULL, &key->n, out, outLen);
    #endif
#endif
        case RSA_PUBLIC_ENCRYPT:
        case RSA_PUBLIC_DECRYPT:
            return sp_RsaPublic_4096(in, inLen, &key->e, &key->n, out, outLen);
        }
    }
#endif
#endif /* WOLFSSL_HAVE_SP_RSA */

#ifdef WOLFSSL_SP_MATH
    (void)rng;
    WOLFSSL_MSG("SP Key Size Error");
    return WC_KEY_SIZE_E;
#else
    (void)rng;

#ifdef WOLFSSL_SMALL_STACK
    tmp = (mp_int*)XMALLOC(sizeof(mp_int), key->heap, DYNAMIC_TYPE_RSA);
    if (tmp == NULL)
        return MEMORY_E;
#ifdef WC_RSA_BLINDING
    rnd = (mp_int*)XMALLOC(sizeof(mp_int) * 2, key->heap, DYNAMIC_TYPE_RSA);
    if (rnd == NULL) {
        XFREE(tmp, key->heap, DYNAMIC_TYPE_RSA);
        return MEMORY_E;
    }
    rndi = rnd + 1;
#endif /* WC_RSA_BLINDING */
#endif /* WOLFSSL_SMALL_STACK */

    if (mp_init(tmp) != MP_OKAY)
        ret = MP_INIT_E;

#ifdef WC_RSA_BLINDING
    if (ret == 0) {
        if (type == RSA_PRIVATE_DECRYPT || type == RSA_PRIVATE_ENCRYPT) {
            if (mp_init_multi(rnd, rndi, NULL, NULL, NULL, NULL) != MP_OKAY) {
                mp_clear(tmp);
                ret = MP_INIT_E;
            }
        }
    }
#endif

#ifndef TEST_UNPAD_CONSTANT_TIME
    if (ret == 0 && mp_read_unsigned_bin(tmp, (byte*)in, inLen) != MP_OKAY)
        ret = MP_READ_E;

    if (ret == 0) {
        switch(type) {
    #ifndef WOLFSSL_RSA_PUBLIC_ONLY
        case RSA_PRIVATE_DECRYPT:
        case RSA_PRIVATE_ENCRYPT:
        {
        #if defined(WC_RSA_BLINDING) && !defined(WC_NO_RNG)
            /* blind */
            ret = mp_rand(rnd, get_digit_count(&key->n), rng);

            /* rndi = 1/rnd mod n */
            if (ret == 0 && mp_invmod(rnd, &key->n, rndi) != MP_OKAY)
                ret = MP_INVMOD_E;

            /* rnd = rnd^e */
            if (ret == 0 && mp_exptmod(rnd, &key->e, &key->n, rnd) != MP_OKAY)
                ret = MP_EXPTMOD_E;

            /* tmp = tmp*rnd mod n */
            if (ret == 0 && mp_mulmod(tmp, rnd, &key->n, tmp) != MP_OKAY)
                ret = MP_MULMOD_E;
        #endif /* WC_RSA_BLINDING && !WC_NO_RNG */

        #ifdef RSA_LOW_MEM      /* half as much memory but twice as slow */
            if (ret == 0 && mp_exptmod(tmp, &key->d, &key->n, tmp) != MP_OKAY)
                ret = MP_EXPTMOD_E;
        #else
            if (ret == 0) {
            #ifdef WOLFSSL_SMALL_STACK
                mp_int* tmpa;
                mp_int* tmpb = NULL;
            #else
                mp_int tmpa[1], tmpb[1];
            #endif
                int cleara = 0, clearb = 0;

            #ifdef WOLFSSL_SMALL_STACK
                tmpa = (mp_int*)XMALLOC(sizeof(mp_int) * 2,
                        key->heap, DYNAMIC_TYPE_RSA);
                if (tmpa != NULL)
                    tmpb = tmpa + 1;
                else
                    ret = MEMORY_E;
            #endif

                if (ret == 0) {
                    if (mp_init(tmpa) != MP_OKAY)
                        ret = MP_INIT_E;
                    else
                        cleara = 1;
                }

                if (ret == 0) {
                    if (mp_init(tmpb) != MP_OKAY)
                        ret = MP_INIT_E;
                    else
                        clearb = 1;
                }

                /* tmpa = tmp^dP mod p */
                if (ret == 0 && mp_exptmod(tmp, &key->dP, &key->p,
                                                               tmpa) != MP_OKAY)
                    ret = MP_EXPTMOD_E;

                /* tmpb = tmp^dQ mod q */
                if (ret == 0 && mp_exptmod(tmp, &key->dQ, &key->q,
                                                               tmpb) != MP_OKAY)
                    ret = MP_EXPTMOD_E;

                /* tmp = (tmpa - tmpb) * qInv (mod p) */
                if (ret == 0 && mp_sub(tmpa, tmpb, tmp) != MP_OKAY)
                    ret = MP_SUB_E;

                if (ret == 0 && mp_mulmod(tmp, &key->u, &key->p,
                                                                tmp) != MP_OKAY)
                    ret = MP_MULMOD_E;

                /* tmp = tmpb + q * tmp */
                if (ret == 0 && mp_mul(tmp, &key->q, tmp) != MP_OKAY)
                    ret = MP_MUL_E;

                if (ret == 0 && mp_add(tmp, tmpb, tmp) != MP_OKAY)
                    ret = MP_ADD_E;

            #ifdef WOLFSSL_SMALL_STACK
                if (tmpa != NULL)
            #endif
                {
                    if (cleara)
                        mp_clear(tmpa);
                    if (clearb)
                        mp_clear(tmpb);
            #ifdef WOLFSSL_SMALL_STACK
                    XFREE(tmpa, key->heap, DYNAMIC_TYPE_RSA);
            #endif
                }
            } /* tmpa/b scope */
        #endif   /* RSA_LOW_MEM */

        #ifdef WC_RSA_BLINDING
            /* unblind */
            if (ret == 0 && mp_mulmod(tmp, rndi, &key->n, tmp) != MP_OKAY)
                ret = MP_MULMOD_E;
        #endif   /* WC_RSA_BLINDING */

            break;
        }
    #endif
        case RSA_PUBLIC_ENCRYPT:
        case RSA_PUBLIC_DECRYPT:
        #ifdef WOLFSSL_XILINX_CRYPT
            ret = wc_RsaFunctionXil(in, inLen, out, outLen, type, key, rng);
        #else
            if (mp_exptmod_nct(tmp, &key->e, &key->n, tmp) != MP_OKAY)
                ret = MP_EXPTMOD_E;
        #endif
            break;
        default:
            ret = RSA_WRONG_TYPE_E;
            break;
        }
    }

    if (ret == 0) {
        keyLen = wc_RsaEncryptSize(key);
        if (keyLen > *outLen)
            ret = RSA_BUFFER_E;
    }
    if (ret == 0) {
        *outLen = keyLen;
        if (mp_to_unsigned_bin_len(tmp, out, keyLen) != MP_OKAY)
             ret = MP_TO_E;
    }
#else
    (void)type;
    (void)key;
    (void)keyLen;
    XMEMCPY(out, in, inLen);
    *outLen = inLen;
#endif

    mp_clear(tmp);
#ifdef WOLFSSL_SMALL_STACK
    XFREE(tmp, key->heap, DYNAMIC_TYPE_RSA);
#endif
#ifdef WC_RSA_BLINDING
    if (type == RSA_PRIVATE_DECRYPT || type == RSA_PRIVATE_ENCRYPT) {
        mp_clear(rndi);
        mp_clear(rnd);
    }
#ifdef WOLFSSL_SMALL_STACK
    XFREE(rnd, key->heap, DYNAMIC_TYPE_RSA);
#endif
#endif /* WC_RSA_BLINDING */
    return ret;
#endif /* WOLFSSL_SP_MATH */
}
#endif

#if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_RSA)
static int wc_RsaFunctionAsync(const byte* in, word32 inLen, byte* out,
                          word32* outLen, int type, RsaKey* key, WC_RNG* rng)
{
    int ret = 0;

    (void)rng;

#ifdef WOLFSSL_ASYNC_CRYPT_TEST
    if (wc_AsyncTestInit(&key->asyncDev, ASYNC_TEST_RSA_FUNC)) {
        WC_ASYNC_TEST* testDev = &key->asyncDev.test;
        testDev->rsaFunc.in = in;
        testDev->rsaFunc.inSz = inLen;
        testDev->rsaFunc.out = out;
        testDev->rsaFunc.outSz = outLen;
        testDev->rsaFunc.type = type;
        testDev->rsaFunc.key = key;
        testDev->rsaFunc.rng = rng;
        return WC_PENDING_E;
    }
#endif /* WOLFSSL_ASYNC_CRYPT_TEST */

    switch(type) {
#ifndef WOLFSSL_RSA_PUBLIC_ONLY
    case RSA_PRIVATE_DECRYPT:
    case RSA_PRIVATE_ENCRYPT:
    #ifdef HAVE_CAVIUM
        key->dataLen = key->n.raw.len;
        ret = NitroxRsaExptMod(in, inLen,
                               key->d.raw.buf, key->d.raw.len,
                               key->n.raw.buf, key->n.raw.len,
                               out, outLen, key);
    #elif defined(HAVE_INTEL_QA)
        #ifdef RSA_LOW_MEM
            ret = IntelQaRsaPrivate(&key->asyncDev, in, inLen,
                                    &key->d.raw, &key->n.raw,
                                    out, outLen);
        #else
            ret = IntelQaRsaCrtPrivate(&key->asyncDev, in, inLen,
                                &key->p.raw, &key->q.raw,
                                &key->dP.raw, &key->dQ.raw,
                                &key->u.raw,
                                out, outLen);
        #endif
    #else /* WOLFSSL_ASYNC_CRYPT_TEST */
        ret = wc_RsaFunctionSync(in, inLen, out, outLen, type, key, rng);
    #endif
        break;
#endif

    case RSA_PUBLIC_ENCRYPT:
    case RSA_PUBLIC_DECRYPT:
    #ifdef HAVE_CAVIUM
        key->dataLen = key->n.raw.len;
        ret = NitroxRsaExptMod(in, inLen,
                               key->e.raw.buf, key->e.raw.len,
                               key->n.raw.buf, key->n.raw.len,
                               out, outLen, key);
    #elif defined(HAVE_INTEL_QA)
        ret = IntelQaRsaPublic(&key->asyncDev, in, inLen,
                               &key->e.raw, &key->n.raw,
                               out, outLen);
    #else /* WOLFSSL_ASYNC_CRYPT_TEST */
        ret = wc_RsaFunctionSync(in, inLen, out, outLen, type, key, rng);
    #endif
        break;

    default:
        ret = RSA_WRONG_TYPE_E;
    }

    return ret;
}
#endif /* WOLFSSL_ASYNC_CRYPT && WC_ASYNC_ENABLE_RSA */

#if defined(WC_RSA_DIRECT) || defined(WC_RSA_NO_PADDING)
/* Function that does the RSA operation directly with no padding.
 *
 * in       buffer to do operation on
 * inLen    length of input buffer
 * out      buffer to hold results
 * outSz    gets set to size of result buffer. Should be passed in as length
 *          of out buffer. If the pointer "out" is null then outSz gets set to
 *          the expected buffer size needed and LENGTH_ONLY_E gets returned.
 * key      RSA key to use for encrypt/decrypt
 * type     if using private or public key {RSA_PUBLIC_ENCRYPT,
 *          RSA_PUBLIC_DECRYPT, RSA_PRIVATE_ENCRYPT, RSA_PRIVATE_DECRYPT}
 * rng      wolfSSL RNG to use if needed
 *
 * returns size of result on success
 */
int wc_RsaDirect(byte* in, word32 inLen, byte* out, word32* outSz,
        RsaKey* key, int type, WC_RNG* rng)
{
    int ret;

    if (in == NULL || outSz == NULL || key == NULL) {
        return BAD_FUNC_ARG;
    }

    /* sanity check on type of RSA operation */
    switch (type) {
        case RSA_PUBLIC_ENCRYPT:
        case RSA_PUBLIC_DECRYPT:
        case RSA_PRIVATE_ENCRYPT:
        case RSA_PRIVATE_DECRYPT:
            break;
        default:
            WOLFSSL_MSG("Bad RSA type");
            return BAD_FUNC_ARG;
    }

    if ((ret = wc_RsaEncryptSize(key)) < 0) {
        return BAD_FUNC_ARG;
    }

    if (inLen != (word32)ret) {
        WOLFSSL_MSG("Bad input length. Should be RSA key size");
        return BAD_FUNC_ARG;
    }

    if (out == NULL) {
        *outSz = inLen;
        return LENGTH_ONLY_E;
    }

    switch (key->state) {
        case RSA_STATE_NONE:
        case RSA_STATE_ENCRYPT_PAD:
        case RSA_STATE_ENCRYPT_EXPTMOD:
        case RSA_STATE_DECRYPT_EXPTMOD:
        case RSA_STATE_DECRYPT_UNPAD:
            key->state = (type == RSA_PRIVATE_ENCRYPT ||
                    type == RSA_PUBLIC_ENCRYPT) ? RSA_STATE_ENCRYPT_EXPTMOD:
                                                  RSA_STATE_DECRYPT_EXPTMOD;

            key->dataLen = *outSz;

            ret = wc_RsaFunction(in, inLen, out, &key->dataLen, type, key, rng);
            if (ret >= 0 || ret == WC_PENDING_E) {
                key->state = (type == RSA_PRIVATE_ENCRYPT ||
                    type == RSA_PUBLIC_ENCRYPT) ? RSA_STATE_ENCRYPT_RES:
                                                  RSA_STATE_DECRYPT_RES;
            }
            if (ret < 0) {
                break;
            }

            FALL_THROUGH;

        case RSA_STATE_ENCRYPT_RES:
        case RSA_STATE_DECRYPT_RES:
            ret = key->dataLen;
            break;

        default:
            ret = BAD_STATE_E;
    }

    /* if async pending then skip cleanup*/
    if (ret == WC_PENDING_E
    #ifdef WC_RSA_NONBLOCK
        || ret == FP_WOULDBLOCK
    #endif
    ) {
        return ret;
    }

    key->state = RSA_STATE_NONE;
    wc_RsaCleanup(key);

    return ret;
}
#endif /* WC_RSA_DIRECT || WC_RSA_NO_PADDING */

#if defined(WOLFSSL_CRYPTOCELL)
static int cc310_RsaPublicEncrypt(const byte* in, word32 inLen, byte* out,
                            word32 outLen, RsaKey* key)
{
    CRYSError_t ret = 0;
    CRYS_RSAPrimeData_t primeData;
    int modulusSize = wc_RsaEncryptSize(key);

    /* The out buffer must be at least modulus size bytes long. */
    if (outLen < modulusSize)
        return BAD_FUNC_ARG;

    ret = CRYS_RSA_PKCS1v15_Encrypt(&wc_rndState,
                                    wc_rndGenVectFunc,
                                    &key->ctx.pubKey,
                                    &primeData,
                                    (byte*)in,
                                    inLen,
                                    out);

    if (ret != SA_SILIB_RET_OK){
        WOLFSSL_MSG("CRYS_RSA_PKCS1v15_Encrypt failed");
        return -1;
    }

    return modulusSize;
}
static int cc310_RsaPublicDecrypt(const byte* in, word32 inLen, byte* out,
                            word32 outLen, RsaKey* key)
{
    CRYSError_t ret = 0;
    CRYS_RSAPrimeData_t primeData;
    uint16_t actualOutLen = outLen;

    ret = CRYS_RSA_PKCS1v15_Decrypt(&key->ctx.privKey,
                                    &primeData,
                                    (byte*)in,
                                    inLen,
                                    out,
                                    &actualOutLen);

    if (ret != SA_SILIB_RET_OK){
        WOLFSSL_MSG("CRYS_RSA_PKCS1v15_Decrypt failed");
        return -1;
    }
    return actualOutLen;
}

int cc310_RsaSSL_Sign(const byte* in, word32 inLen, byte* out,
                  word32 outLen, RsaKey* key, CRYS_RSA_HASH_OpMode_t mode)
{
    CRYSError_t ret = 0;
    uint16_t actualOutLen = outLen*sizeof(byte);
    CRYS_RSAPrivUserContext_t  contextPrivate;

    ret =  CRYS_RSA_PKCS1v15_Sign(&wc_rndState,
                wc_rndGenVectFunc,
                &contextPrivate,
                &key->ctx.privKey,
                mode,
                (byte*)in,
                inLen,
                out,
                &actualOutLen);

    if (ret != SA_SILIB_RET_OK){
        WOLFSSL_MSG("CRYS_RSA_PKCS1v15_Sign failed");
        return -1;
    }
    return actualOutLen;
}

int cc310_RsaSSL_Verify(const byte* in, word32 inLen, byte* sig,
                               RsaKey* key, CRYS_RSA_HASH_OpMode_t mode)
{
    CRYSError_t ret = 0;
    CRYS_RSAPubUserContext_t contextPub;

    /* verify the signature in the sig pointer */
    ret =  CRYS_RSA_PKCS1v15_Verify(&contextPub,
                &key->ctx.pubKey,
                mode,
                (byte*)in,
                inLen,
                sig);

    if (ret != SA_SILIB_RET_OK){
        WOLFSSL_MSG("CRYS_RSA_PKCS1v15_Verify failed");
        return -1;
    }

    return ret;
}
#endif /* WOLFSSL_CRYPTOCELL */

int wc_RsaFunction(const byte* in, word32 inLen, byte* out,
                          word32* outLen, int type, RsaKey* key, WC_RNG* rng)
{
    int ret = 0;

    if (key == NULL || in == NULL || inLen == 0 || out == NULL ||
            outLen == NULL || *outLen == 0 || type == RSA_TYPE_UNKNOWN) {
        return BAD_FUNC_ARG;
    }

#ifdef WOLF_CRYPTO_CB
    if (key->devId != INVALID_DEVID) {
        ret = wc_CryptoCb_Rsa(in, inLen, out, outLen, type, key, rng);
        if (ret != CRYPTOCB_UNAVAILABLE)
            return ret;
        /* fall-through when unavailable */
        ret = 0; /* reset error code and try using software */
    }
#endif

#ifndef TEST_UNPAD_CONSTANT_TIME
#ifndef NO_RSA_BOUNDS_CHECK
    if (type == RSA_PRIVATE_DECRYPT &&
        key->state == RSA_STATE_DECRYPT_EXPTMOD) {

        /* Check that 1 < in < n-1. (Requirement of 800-56B.) */
#ifdef WOLFSSL_SMALL_STACK
        mp_int* c;
#else
        mp_int c[1];
#endif

#ifdef WOLFSSL_SMALL_STACK
        c = (mp_int*)XMALLOC(sizeof(mp_int), key->heap, DYNAMIC_TYPE_RSA);
        if (c == NULL)
            ret = MEMORY_E;
#endif

        if (mp_init(c) != MP_OKAY)
            ret = MEMORY_E;
        if (ret == 0) {
            if (mp_read_unsigned_bin(c, in, inLen) != 0)
                ret = MP_READ_E;
        }
        if (ret == 0) {
            /* check c > 1 */
            if (mp_cmp_d(c, 1) != MP_GT)
                ret = RSA_OUT_OF_RANGE_E;
        }
        if (ret == 0) {
            /* add c+1 */
            if (mp_add_d(c, 1, c) != MP_OKAY)
                ret = MP_ADD_E;
        }
        if (ret == 0) {
            /* check c+1 < n */
            if (mp_cmp(c, &key->n) != MP_LT)
                ret = RSA_OUT_OF_RANGE_E;
        }
        mp_clear(c);

#ifdef WOLFSSL_SMALL_STACK
        XFREE(c, key->heap, DYNAMIC_TYPE_RSA);
#endif

        if (ret != 0)
            return ret;
    }
#endif /* NO_RSA_BOUNDS_CHECK */
#endif

#if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_RSA)
    if (key->asyncDev.marker == WOLFSSL_ASYNC_MARKER_RSA &&
                                                        key->n.raw.len > 0) {
        ret = wc_RsaFunctionAsync(in, inLen, out, outLen, type, key, rng);
    }
    else
#endif
#ifdef WC_RSA_NONBLOCK
    if (key->nb) {
        ret = wc_RsaFunctionNonBlock(in, inLen, out, outLen, type, key);
    }
    else
#endif
    {
        ret = wc_RsaFunctionSync(in, inLen, out, outLen, type, key, rng);
    }

    /* handle error */
    if (ret < 0 && ret != WC_PENDING_E
    #ifdef WC_RSA_NONBLOCK
        && ret != FP_WOULDBLOCK
    #endif
    ) {
        if (ret == MP_EXPTMOD_E) {
            /* This can happen due to incorrectly set FP_MAX_BITS or missing XREALLOC */
            WOLFSSL_MSG("RSA_FUNCTION MP_EXPTMOD_E: memory/config problem");
        }

        key->state = RSA_STATE_NONE;
        wc_RsaCleanup(key);
    }

    return ret;
}


#ifndef WOLFSSL_RSA_VERIFY_ONLY
/* Internal Wrappers */
/* Gives the option of choosing padding type
   in : input to be encrypted
   inLen: length of input buffer
   out: encrypted output
   outLen: length of encrypted output buffer
   key   : wolfSSL initialized RSA key struct
   rng   : wolfSSL initialized random number struct
   rsa_type  : type of RSA: RSA_PUBLIC_ENCRYPT, RSA_PUBLIC_DECRYPT,
        RSA_PRIVATE_ENCRYPT or RSA_PRIVATE_DECRYPT
   pad_value: RSA_BLOCK_TYPE_1 or RSA_BLOCK_TYPE_2
   pad_type  : type of padding: WC_RSA_PKCSV15_PAD, WC_RSA_OAEP_PAD,
        WC_RSA_NO_PAD or WC_RSA_PSS_PAD
   hash  : type of hash algorithm to use found in wolfssl/wolfcrypt/hash.h
   mgf   : type of mask generation function to use
   label : optional label
   labelSz : size of optional label buffer
   saltLen : Length of salt used in PSS
   rng : random number generator */
static int RsaPublicEncryptEx(const byte* in, word32 inLen, byte* out,
                            word32 outLen, RsaKey* key, int rsa_type,
                            byte pad_value, int pad_type,
                            enum wc_HashType hash, int mgf,
                            byte* label, word32 labelSz, int saltLen,
                            WC_RNG* rng)
{
    int ret, sz;

    if (in == NULL || inLen == 0 || out == NULL || key == NULL) {
        return BAD_FUNC_ARG;
    }

    sz = wc_RsaEncryptSize(key);
    if (sz > (int)outLen) {
        return RSA_BUFFER_E;
    }

    if (sz < RSA_MIN_PAD_SZ) {
        return WC_KEY_SIZE_E;
    }

    if (inLen > (word32)(sz - RSA_MIN_PAD_SZ)) {
#ifdef WC_RSA_NO_PADDING
        /* In the case that no padding is used the input length can and should
         * be the same size as the RSA key. */
        if (pad_type != WC_RSA_NO_PAD)
#endif
        return RSA_BUFFER_E;
    }

    switch (key->state) {
    case RSA_STATE_NONE:
    case RSA_STATE_ENCRYPT_PAD:
    #if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_RSA) && \
            defined(HAVE_CAVIUM)
        if (key->asyncDev.marker == WOLFSSL_ASYNC_MARKER_RSA &&
                                 pad_type != WC_RSA_PSS_PAD && key->n.raw.buf) {
            /* Async operations that include padding */
            if (rsa_type == RSA_PUBLIC_ENCRYPT &&
                                                pad_value == RSA_BLOCK_TYPE_2) {
                key->state = RSA_STATE_ENCRYPT_RES;
                key->dataLen = key->n.raw.len;
                return NitroxRsaPublicEncrypt(in, inLen, out, outLen, key);
            }
            else if (rsa_type == RSA_PRIVATE_ENCRYPT &&
                                                pad_value == RSA_BLOCK_TYPE_1) {
                key->state = RSA_STATE_ENCRYPT_RES;
                key->dataLen = key->n.raw.len;
                return NitroxRsaSSL_Sign(in, inLen, out, outLen, key);
            }
        }
    #elif defined(WOLFSSL_CRYPTOCELL)
        if (rsa_type == RSA_PUBLIC_ENCRYPT &&
                                            pad_value == RSA_BLOCK_TYPE_2) {

            return cc310_RsaPublicEncrypt(in, inLen, out, outLen, key);
        }
        else if (rsa_type == RSA_PRIVATE_ENCRYPT &&
                                         pad_value == RSA_BLOCK_TYPE_1) {
         return cc310_RsaSSL_Sign(in, inLen, out, outLen, key,
                                  cc310_hashModeRSA(hash, 0));
        }
    #endif /* WOLFSSL_CRYPTOCELL */

        key->state = RSA_STATE_ENCRYPT_PAD;
        ret = wc_RsaPad_ex(in, inLen, out, sz, pad_value, rng, pad_type, hash,
                           mgf, label, labelSz, saltLen, mp_count_bits(&key->n),
                           key->heap);
        if (ret < 0) {
            break;
        }

        key->state = RSA_STATE_ENCRYPT_EXPTMOD;
        FALL_THROUGH;

    case RSA_STATE_ENCRYPT_EXPTMOD:

        key->dataLen = outLen;
        ret = wc_RsaFunction(out, sz, out, &key->dataLen, rsa_type, key, rng);

        if (ret >= 0 || ret == WC_PENDING_E) {
            key->state = RSA_STATE_ENCRYPT_RES;
        }
        if (ret < 0) {
            break;
        }

        FALL_THROUGH;

    case RSA_STATE_ENCRYPT_RES:
        ret = key->dataLen;
        break;

    default:
        ret = BAD_STATE_E;
        break;
    }

    /* if async pending then return and skip done cleanup below */
    if (ret == WC_PENDING_E
    #ifdef WC_RSA_NONBLOCK
        || ret == FP_WOULDBLOCK
    #endif
    ) {
        return ret;
    }

    key->state = RSA_STATE_NONE;
    wc_RsaCleanup(key);

    return ret;
}

#endif

/* Gives the option of choosing padding type
   in : input to be decrypted
   inLen: length of input buffer
   out:  decrypted message
   outLen: length of decrypted message in bytes
   outPtr: optional inline output pointer (if provided doing inline)
   key   : wolfSSL initialized RSA key struct
   rsa_type  : type of RSA: RSA_PUBLIC_ENCRYPT, RSA_PUBLIC_DECRYPT,
        RSA_PRIVATE_ENCRYPT or RSA_PRIVATE_DECRYPT
   pad_value: RSA_BLOCK_TYPE_1 or RSA_BLOCK_TYPE_2
   pad_type  : type of padding: WC_RSA_PKCSV15_PAD, WC_RSA_OAEP_PAD,
        WC_RSA_NO_PAD, WC_RSA_PSS_PAD
   hash  : type of hash algorithm to use found in wolfssl/wolfcrypt/hash.h
   mgf   : type of mask generation function to use
   label : optional label
   labelSz : size of optional label buffer
   saltLen : Length of salt used in PSS
   rng : random number generator */
static int RsaPrivateDecryptEx(byte* in, word32 inLen, byte* out,
                            word32 outLen, byte** outPtr, RsaKey* key,
                            int rsa_type, byte pad_value, int pad_type,
                            enum wc_HashType hash, int mgf,
                            byte* label, word32 labelSz, int saltLen,
                            WC_RNG* rng)
{
    int ret = RSA_WRONG_TYPE_E;
    byte* pad = NULL;

    if (in == NULL || inLen == 0 || out == NULL || key == NULL) {
        return BAD_FUNC_ARG;
    }

    switch (key->state) {
    case RSA_STATE_NONE:
        key->dataLen = inLen;

    #if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_RSA) && \
            defined(HAVE_CAVIUM)
        /* Async operations that include padding */
        if (key->asyncDev.marker == WOLFSSL_ASYNC_MARKER_RSA &&
                                                   pad_type != WC_RSA_PSS_PAD) {
#ifndef WOLFSSL_RSA_PUBLIC_ONLY
            if (rsa_type == RSA_PRIVATE_DECRYPT &&
                                                pad_value == RSA_BLOCK_TYPE_2) {
                key->state = RSA_STATE_DECRYPT_RES;
                key->data = NULL;
                return NitroxRsaPrivateDecrypt(in, inLen, out, &key->dataLen,
                                               key);
#endif
            }
            else if (rsa_type == RSA_PUBLIC_DECRYPT &&
                                                pad_value == RSA_BLOCK_TYPE_1) {
                key->state = RSA_STATE_DECRYPT_RES;
                key->data = NULL;
                return NitroxRsaSSL_Verify(in, inLen, out, &key->dataLen, key);
            }
        }
    #elif defined(WOLFSSL_CRYPTOCELL)
        if (rsa_type == RSA_PRIVATE_DECRYPT &&
                                            pad_value == RSA_BLOCK_TYPE_2) {
            ret = cc310_RsaPublicDecrypt(in, inLen, out, outLen, key);
            if (outPtr != NULL)
                *outPtr = out; /* for inline */
            return ret;
        }
        else if (rsa_type == RSA_PUBLIC_DECRYPT &&
                                            pad_value == RSA_BLOCK_TYPE_1) {
            return cc310_RsaSSL_Verify(in, inLen, out, key,
                                       cc310_hashModeRSA(hash, 0));
        }
    #endif /* WOLFSSL_CRYPTOCELL */


#if !defined(WOLFSSL_RSA_VERIFY_ONLY) && !defined(WOLFSSL_RSA_VERIFY_INLINE)
        /* verify the tmp ptr is NULL, otherwise indicates bad state */
        if (key->data != NULL) {
            ret = BAD_STATE_E;
            break;
        }

        /* if not doing this inline then allocate a buffer for it */
        if (outPtr == NULL) {
            key->data = (byte*)XMALLOC(inLen, key->heap,
                                                      DYNAMIC_TYPE_WOLF_BIGINT);
            key->dataIsAlloc = 1;
            if (key->data == NULL) {
                ret = MEMORY_E;
                break;
            }
            XMEMCPY(key->data, in, inLen);
        }
        else {
            key->data = out;
        }
#endif

        key->state = RSA_STATE_DECRYPT_EXPTMOD;
        FALL_THROUGH;

    case RSA_STATE_DECRYPT_EXPTMOD:
#if !defined(WOLFSSL_RSA_VERIFY_ONLY) && !defined(WOLFSSL_RSA_VERIFY_INLINE)
        ret = wc_RsaFunction(key->data, inLen, key->data, &key->dataLen,
                                                            rsa_type, key, rng);
#else
        ret = wc_RsaFunction(in, inLen, out, &key->dataLen, rsa_type, key, rng);
#endif

        if (ret >= 0 || ret == WC_PENDING_E) {
            key->state = RSA_STATE_DECRYPT_UNPAD;
        }
        if (ret < 0) {
            break;
        }

        FALL_THROUGH;

    case RSA_STATE_DECRYPT_UNPAD:
#if !defined(WOLFSSL_RSA_VERIFY_ONLY) && !defined(WOLFSSL_RSA_VERIFY_INLINE)
        ret = wc_RsaUnPad_ex(key->data, key->dataLen, &pad, pad_value, pad_type,
                             hash, mgf, label, labelSz, saltLen,
                             mp_count_bits(&key->n), key->heap);
#else
        ret = wc_RsaUnPad_ex(out, key->dataLen, &pad, pad_value, pad_type, hash,
                             mgf, label, labelSz, saltLen,
                             mp_count_bits(&key->n), key->heap);
#endif
        if (rsa_type == RSA_PUBLIC_DECRYPT && ret > (int)outLen)
            ret = RSA_BUFFER_E;
        else if (ret >= 0 && pad != NULL) {
#if !defined(WOLFSSL_RSA_VERIFY_ONLY) && !defined(WOLFSSL_RSA_VERIFY_INLINE)
            signed char c;
#endif

            /* only copy output if not inline */
            if (outPtr == NULL) {
#if !defined(WOLFSSL_RSA_VERIFY_ONLY) && !defined(WOLFSSL_RSA_VERIFY_INLINE)
                if (rsa_type == RSA_PRIVATE_DECRYPT) {
                    word32 i, j;
                    int start = (int)((size_t)pad - (size_t)key->data);

                    for (i = 0, j = 0; j < key->dataLen; j++) {
                        out[i] = key->data[j];
                        c  = ctMaskGTE(j, start);
                        c &= ctMaskLT(i, outLen);
                        /* 0 - no add, -1 add */
                        i += (word32)((byte)(-c));
                    }
                }
                else
#endif
                {
                    XMEMCPY(out, pad, ret);
                }
            }
            else
                *outPtr = pad;

#if !defined(WOLFSSL_RSA_VERIFY_ONLY)
            ret = ctMaskSelInt(ctMaskLTE(ret, outLen), ret, RSA_BUFFER_E);
            ret = ctMaskSelInt(ctMaskNotEq(ret, 0), ret, RSA_BUFFER_E);
#else
            if (outLen < (word32)ret)
                ret = RSA_BUFFER_E;
#endif
        }

        key->state = RSA_STATE_DECRYPT_RES;
        FALL_THROUGH;

    case RSA_STATE_DECRYPT_RES:
    #if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_RSA) && \
            defined(HAVE_CAVIUM)
        if (key->asyncDev.marker == WOLFSSL_ASYNC_MARKER_RSA &&
                                                   pad_type != WC_RSA_PSS_PAD) {
            if (ret > 0) {
                /* convert result */
                byte* dataLen = (byte*)&key->dataLen;
                ret = (dataLen[0] << 8) | (dataLen[1]);

                if (outPtr)
                    *outPtr = in;
            }
        }
    #endif
        break;

    default:
        ret = BAD_STATE_E;
        break;
    }

    /* if async pending then return and skip done cleanup below */
    if (ret == WC_PENDING_E
    #ifdef WC_RSA_NONBLOCK
        || ret == FP_WOULDBLOCK
    #endif
    ) {
        return ret;
    }

    key->state = RSA_STATE_NONE;
    wc_RsaCleanup(key);

    return ret;
}


#ifndef WOLFSSL_RSA_VERIFY_ONLY
/* Public RSA Functions */
int wc_RsaPublicEncrypt(const byte* in, word32 inLen, byte* out, word32 outLen,
                                                     RsaKey* key, WC_RNG* rng)
{
    return RsaPublicEncryptEx(in, inLen, out, outLen, key,
        RSA_PUBLIC_ENCRYPT, RSA_BLOCK_TYPE_2, WC_RSA_PKCSV15_PAD,
        WC_HASH_TYPE_NONE, WC_MGF1NONE, NULL, 0, 0, rng);
}


#if !defined(WC_NO_RSA_OAEP) || defined(WC_RSA_NO_PADDING)
int wc_RsaPublicEncrypt_ex(const byte* in, word32 inLen, byte* out,
                    word32 outLen, RsaKey* key, WC_RNG* rng, int type,
                    enum wc_HashType hash, int mgf, byte* label,
                    word32 labelSz)
{
    return RsaPublicEncryptEx(in, inLen, out, outLen, key, RSA_PUBLIC_ENCRYPT,
        RSA_BLOCK_TYPE_2, type, hash, mgf, label, labelSz, 0, rng);
}
#endif /* WC_NO_RSA_OAEP */
#endif


#ifndef WOLFSSL_RSA_PUBLIC_ONLY
int wc_RsaPrivateDecryptInline(byte* in, word32 inLen, byte** out, RsaKey* key)
{
    WC_RNG* rng;
#ifdef WC_RSA_BLINDING
    rng = key->rng;
#else
    rng = NULL;
#endif
    return RsaPrivateDecryptEx(in, inLen, in, inLen, out, key,
        RSA_PRIVATE_DECRYPT, RSA_BLOCK_TYPE_2, WC_RSA_PKCSV15_PAD,
        WC_HASH_TYPE_NONE, WC_MGF1NONE, NULL, 0, 0, rng);
}


#ifndef WC_NO_RSA_OAEP
int wc_RsaPrivateDecryptInline_ex(byte* in, word32 inLen, byte** out,
                                  RsaKey* key, int type, enum wc_HashType hash,
                                  int mgf, byte* label, word32 labelSz)
{
    WC_RNG* rng;
#ifdef WC_RSA_BLINDING
    rng = key->rng;
#else
    rng = NULL;
#endif
    return RsaPrivateDecryptEx(in, inLen, in, inLen, out, key,
        RSA_PRIVATE_DECRYPT, RSA_BLOCK_TYPE_2, type, hash,
        mgf, label, labelSz, 0, rng);
}
#endif /* WC_NO_RSA_OAEP */


int wc_RsaPrivateDecrypt(const byte* in, word32 inLen, byte* out,
                                                 word32 outLen, RsaKey* key)
{
    WC_RNG* rng;
#ifdef WC_RSA_BLINDING
    rng = key->rng;
#else
    rng = NULL;
#endif
    return RsaPrivateDecryptEx((byte*)in, inLen, out, outLen, NULL, key,
        RSA_PRIVATE_DECRYPT, RSA_BLOCK_TYPE_2, WC_RSA_PKCSV15_PAD,
        WC_HASH_TYPE_NONE, WC_MGF1NONE, NULL, 0, 0, rng);
}

#if !defined(WC_NO_RSA_OAEP) || defined(WC_RSA_NO_PADDING)
int wc_RsaPrivateDecrypt_ex(const byte* in, word32 inLen, byte* out,
                            word32 outLen, RsaKey* key, int type,
                            enum wc_HashType hash, int mgf, byte* label,
                            word32 labelSz)
{
    WC_RNG* rng;
#ifdef WC_RSA_BLINDING
    rng = key->rng;
#else
    rng = NULL;
#endif
    return RsaPrivateDecryptEx((byte*)in, inLen, out, outLen, NULL, key,
        RSA_PRIVATE_DECRYPT, RSA_BLOCK_TYPE_2, type, hash, mgf, label,
        labelSz, 0, rng);
}
#endif /* WC_NO_RSA_OAEP || WC_RSA_NO_PADDING */
#endif /* WOLFSSL_RSA_PUBLIC_ONLY */

#if !defined(WOLFSSL_CRYPTOCELL)
int wc_RsaSSL_VerifyInline(byte* in, word32 inLen, byte** out, RsaKey* key)
{
    WC_RNG* rng;
#ifdef WC_RSA_BLINDING
    rng = key->rng;
#else
    rng = NULL;
#endif
    return RsaPrivateDecryptEx(in, inLen, in, inLen, out, key,
        RSA_PUBLIC_DECRYPT, RSA_BLOCK_TYPE_1, WC_RSA_PKCSV15_PAD,
        WC_HASH_TYPE_NONE, WC_MGF1NONE, NULL, 0, 0, rng);
}
#endif

#ifndef WOLFSSL_RSA_VERIFY_ONLY
int wc_RsaSSL_Verify(const byte* in, word32 inLen, byte* out, word32 outLen,
                                                                 RsaKey* key)
{
    return wc_RsaSSL_Verify_ex(in, inLen, out, outLen, key , WC_RSA_PKCSV15_PAD);
}

int  wc_RsaSSL_Verify_ex(const byte* in, word32 inLen, byte* out, word32 outLen,
                         RsaKey* key, int pad_type)
{
    WC_RNG* rng;

    if (key == NULL) {
        return BAD_FUNC_ARG;
    }

#ifdef WC_RSA_BLINDING
    rng = key->rng;
#else
    rng = NULL;
#endif

    return RsaPrivateDecryptEx((byte*)in, inLen, out, outLen, NULL, key,
        RSA_PUBLIC_DECRYPT, RSA_BLOCK_TYPE_1, pad_type,
        WC_HASH_TYPE_NONE, WC_MGF1NONE, NULL, 0, 0, rng);
}
#endif

#ifdef WC_RSA_PSS
/* Verify the message signed with RSA-PSS.
 * The input buffer is reused for the output buffer.
 * Salt length is equal to hash length.
 *
 * in     Buffer holding encrypted data.
 * inLen  Length of data in buffer.
 * out    Pointer to address containing the PSS data.
 * hash   Hash algorithm.
 * mgf    Mask generation function.
 * key    Public RSA key.
 * returns the length of the PSS data on success and negative indicates failure.
 */
int wc_RsaPSS_VerifyInline(byte* in, word32 inLen, byte** out,
                           enum wc_HashType hash, int mgf, RsaKey* key)
{
#ifndef WOLFSSL_PSS_SALT_LEN_DISCOVER
    return wc_RsaPSS_VerifyInline_ex(in, inLen, out, hash, mgf,
                                                 RSA_PSS_SALT_LEN_DEFAULT, key);
#else
    return wc_RsaPSS_VerifyInline_ex(in, inLen, out, hash, mgf,
                                                RSA_PSS_SALT_LEN_DISCOVER, key);
#endif
}

/* Verify the message signed with RSA-PSS.
 * The input buffer is reused for the output buffer.
 *
 * in       Buffer holding encrypted data.
 * inLen    Length of data in buffer.
 * out      Pointer to address containing the PSS data.
 * hash     Hash algorithm.
 * mgf      Mask generation function.
 * key      Public RSA key.
 * saltLen  Length of salt used. RSA_PSS_SALT_LEN_DEFAULT (-1) indicates salt
 *          length is the same as the hash length. RSA_PSS_SALT_LEN_DISCOVER
 *          indicates salt length is determined from the data.
 * returns the length of the PSS data on success and negative indicates failure.
 */
int wc_RsaPSS_VerifyInline_ex(byte* in, word32 inLen, byte** out,
                              enum wc_HashType hash, int mgf, int saltLen,
                              RsaKey* key)
{
    WC_RNG* rng;
#ifdef WC_RSA_BLINDING
    rng = key->rng;
#else
    rng = NULL;
#endif
    return RsaPrivateDecryptEx(in, inLen, in, inLen, out, key,
        RSA_PUBLIC_DECRYPT, RSA_BLOCK_TYPE_1, WC_RSA_PSS_PAD,
        hash, mgf, NULL, 0, saltLen, rng);
}

/* Verify the message signed with RSA-PSS.
 * Salt length is equal to hash length.
 *
 * in     Buffer holding encrypted data.
 * inLen  Length of data in buffer.
 * out    Pointer to address containing the PSS data.
 * hash   Hash algorithm.
 * mgf    Mask generation function.
 * key    Public RSA key.
 * returns the length of the PSS data on success and negative indicates failure.
 */
int wc_RsaPSS_Verify(byte* in, word32 inLen, byte* out, word32 outLen,
                     enum wc_HashType hash, int mgf, RsaKey* key)
{
#ifndef WOLFSSL_PSS_SALT_LEN_DISCOVER
    return wc_RsaPSS_Verify_ex(in, inLen, out, outLen, hash, mgf,
                                                 RSA_PSS_SALT_LEN_DEFAULT, key);
#else
    return wc_RsaPSS_Verify_ex(in, inLen, out, outLen, hash, mgf,
                                                RSA_PSS_SALT_LEN_DISCOVER, key);
#endif
}

/* Verify the message signed with RSA-PSS.
 *
 * in       Buffer holding encrypted data.
 * inLen    Length of data in buffer.
 * out      Pointer to address containing the PSS data.
 * hash     Hash algorithm.
 * mgf      Mask generation function.
 * key      Public RSA key.
 * saltLen  Length of salt used. RSA_PSS_SALT_LEN_DEFAULT (-1) indicates salt
 *          length is the same as the hash length. RSA_PSS_SALT_LEN_DISCOVER
 *          indicates salt length is determined from the data.
 * returns the length of the PSS data on success and negative indicates failure.
 */
int wc_RsaPSS_Verify_ex(byte* in, word32 inLen, byte* out, word32 outLen,
                        enum wc_HashType hash, int mgf, int saltLen,
                        RsaKey* key)
{
    WC_RNG* rng;
#ifdef WC_RSA_BLINDING
    rng = key->rng;
#else
    rng = NULL;
#endif
    return RsaPrivateDecryptEx(in, inLen, out, outLen, NULL, key,
        RSA_PUBLIC_DECRYPT, RSA_BLOCK_TYPE_1, WC_RSA_PSS_PAD,
        hash, mgf, NULL, 0, saltLen, rng);
}


/* Checks the PSS data to ensure that the signature matches.
 * Salt length is equal to hash length.
 *
 * in        Hash of the data that is being verified.
 * inSz      Length of hash.
 * sig       Buffer holding PSS data.
 * sigSz     Size of PSS data.
 * hashType  Hash algorithm.
 * returns BAD_PADDING_E when the PSS data is invalid, BAD_FUNC_ARG when
 * NULL is passed in to in or sig or inSz is not the same as the hash
 * algorithm length and 0 on success.
 */
int wc_RsaPSS_CheckPadding(const byte* in, word32 inSz, byte* sig,
                           word32 sigSz, enum wc_HashType hashType)
{
    return wc_RsaPSS_CheckPadding_ex(in, inSz, sig, sigSz, hashType, inSz, 0);
}

/* Checks the PSS data to ensure that the signature matches.
 *
 * in        Hash of the data that is being verified.
 * inSz      Length of hash.
 * sig       Buffer holding PSS data.
 * sigSz     Size of PSS data.
 * hashType  Hash algorithm.
 * saltLen   Length of salt used. RSA_PSS_SALT_LEN_DEFAULT (-1) indicates salt
 *           length is the same as the hash length. RSA_PSS_SALT_LEN_DISCOVER
 *           indicates salt length is determined from the data.
 * returns BAD_PADDING_E when the PSS data is invalid, BAD_FUNC_ARG when
 * NULL is passed in to in or sig or inSz is not the same as the hash
 * algorithm length and 0 on success.
 */
int wc_RsaPSS_CheckPadding_ex(const byte* in, word32 inSz, byte* sig,
                              word32 sigSz, enum wc_HashType hashType,
                              int saltLen, int bits)
{
    int ret = 0;
#ifndef WOLFSSL_PSS_LONG_SALT
    byte sigCheck[WC_MAX_DIGEST_SIZE*2 + RSA_PSS_PAD_SZ];
#else
    byte *sigCheck = NULL;
#endif

    (void)bits;

    if (in == NULL || sig == NULL ||
                               inSz != (word32)wc_HashGetDigestSize(hashType)) {
        ret = BAD_FUNC_ARG;
    }

    if (ret == 0) {
        if (saltLen == RSA_PSS_SALT_LEN_DEFAULT) {
            saltLen = inSz;
            #ifdef WOLFSSL_SHA512
                /* See FIPS 186-4 section 5.5 item (e). */
                if (bits == 1024 && inSz == WC_SHA512_DIGEST_SIZE) {
                    saltLen = RSA_PSS_SALT_MAX_SZ;
                }
            #endif
        }
#ifndef WOLFSSL_PSS_LONG_SALT
        else if ((word32)saltLen > inSz) {
            ret = PSS_SALTLEN_E;
        }
#endif
#ifndef WOLFSSL_PSS_SALT_LEN_DISCOVER
        else if (saltLen < RSA_PSS_SALT_LEN_DEFAULT) {
            ret = PSS_SALTLEN_E;
        }
#else
        else if (saltLen == RSA_PSS_SALT_LEN_DISCOVER) {
            saltLen = sigSz - inSz;
            if (saltLen < 0) {
                ret = PSS_SALTLEN_E;
            }
        }
        else if (saltLen < RSA_PSS_SALT_LEN_DISCOVER) {
            ret = PSS_SALTLEN_E;
        }
#endif
    }

    /* Sig = Salt | Exp Hash */
    if (ret == 0) {
        if (sigSz != inSz + saltLen) {
            ret = PSS_SALTLEN_E;
        }
    }

#ifdef WOLFSSL_PSS_LONG_SALT
    if (ret == 0) {
        sigCheck = (byte*)XMALLOC(RSA_PSS_PAD_SZ + inSz + saltLen, NULL,
                                                       DYNAMIC_TYPE_RSA_BUFFER);
        if (sigCheck == NULL) {
            ret = MEMORY_E;
        }
    }
#endif

    /* Exp Hash = HASH(8 * 0x00 | Message Hash | Salt) */
    if (ret == 0) {
        XMEMSET(sigCheck, 0, RSA_PSS_PAD_SZ);
        XMEMCPY(sigCheck + RSA_PSS_PAD_SZ, in, inSz);
        XMEMCPY(sigCheck + RSA_PSS_PAD_SZ + inSz, sig, saltLen);
        ret = wc_Hash(hashType, sigCheck, RSA_PSS_PAD_SZ + inSz + saltLen,
                      sigCheck, inSz);
    }
    if (ret == 0) {
        if (XMEMCMP(sigCheck, sig + saltLen, inSz) != 0) {
            WOLFSSL_MSG("RsaPSS_CheckPadding: Padding Error");
            ret = BAD_PADDING_E;
        }
    }

#ifdef WOLFSSL_PSS_LONG_SALT
    if (sigCheck != NULL) {
        XFREE(sigCheck, NULL, DYNAMIC_TYPE_RSA_BUFFER);
    }
#endif
    return ret;
}


/* Verify the message signed with RSA-PSS.
 * The input buffer is reused for the output buffer.
 * Salt length is equal to hash length.
 *
 * in     Buffer holding encrypted data.
 * inLen  Length of data in buffer.
 * out    Pointer to address containing the PSS data.
 * digest Hash of the data that is being verified.
 * digestLen Length of hash.
 * hash   Hash algorithm.
 * mgf    Mask generation function.
 * key    Public RSA key.
 * returns the length of the PSS data on success and negative indicates failure.
 */
int wc_RsaPSS_VerifyCheckInline(byte* in, word32 inLen, byte** out,
                           const byte* digest, word32 digestLen,
                           enum wc_HashType hash, int mgf, RsaKey* key)
{
    int ret = 0, verify, saltLen, hLen, bits = 0;

    hLen = wc_HashGetDigestSize(hash);
    if (hLen < 0)
        return hLen;
    if ((word32)hLen != digestLen)
        return BAD_FUNC_ARG;

    saltLen = hLen;
    #ifdef WOLFSSL_SHA512
        /* See FIPS 186-4 section 5.5 item (e). */
        bits = mp_count_bits(&key->n);
        if (bits == 1024 && hLen == WC_SHA512_DIGEST_SIZE)
            saltLen = RSA_PSS_SALT_MAX_SZ;
    #endif

    verify = wc_RsaPSS_VerifyInline_ex(in, inLen, out, hash, mgf, saltLen, key);
    if (verify > 0)
        ret = wc_RsaPSS_CheckPadding_ex(digest, digestLen, *out, verify,
                                        hash, saltLen, bits);
    if (ret == 0)
        ret = verify;

    return ret;
}


/* Verify the message signed with RSA-PSS.
 * Salt length is equal to hash length.
 *
 * in     Buffer holding encrypted data.
 * inLen  Length of data in buffer.
 * out    Pointer to address containing the PSS data.
 * outLen Length of the output.
 * digest Hash of the data that is being verified.
 * digestLen Length of hash.
 * hash   Hash algorithm.
 * mgf    Mask generation function.
 * key    Public RSA key.
 * returns the length of the PSS data on success and negative indicates failure.
 */
int wc_RsaPSS_VerifyCheck(byte* in, word32 inLen, byte* out, word32 outLen,
                          const byte* digest, word32 digestLen,
                          enum wc_HashType hash, int mgf,
                          RsaKey* key)
{
    int ret = 0, verify, saltLen, hLen, bits = 0;

    hLen = wc_HashGetDigestSize(hash);
    if (hLen < 0)
        return hLen;
    if ((word32)hLen != digestLen)
        return BAD_FUNC_ARG;

    saltLen = hLen;
    #ifdef WOLFSSL_SHA512
        /* See FIPS 186-4 section 5.5 item (e). */
        bits = mp_count_bits(&key->n);
        if (bits == 1024 && hLen == WC_SHA512_DIGEST_SIZE)
            saltLen = RSA_PSS_SALT_MAX_SZ;
    #endif

    verify = wc_RsaPSS_Verify_ex(in, inLen, out, outLen, hash,
                                 mgf, saltLen, key);
    if (verify > 0)
        ret = wc_RsaPSS_CheckPadding_ex(digest, digestLen, out, verify,
                                        hash, saltLen, bits);
    if (ret == 0)
        ret = verify;

    return ret;
}

#endif

#if !defined(WOLFSSL_RSA_PUBLIC_ONLY) && !defined(WOLFSSL_RSA_VERIFY_ONLY)
int wc_RsaSSL_Sign(const byte* in, word32 inLen, byte* out, word32 outLen,
                                                   RsaKey* key, WC_RNG* rng)
{
    return RsaPublicEncryptEx(in, inLen, out, outLen, key,
        RSA_PRIVATE_ENCRYPT, RSA_BLOCK_TYPE_1, WC_RSA_PKCSV15_PAD,
        WC_HASH_TYPE_NONE, WC_MGF1NONE, NULL, 0, 0, rng);
}

#ifdef WC_RSA_PSS
/* Sign the hash of a message using RSA-PSS.
 * Salt length is equal to hash length.
 *
 * in      Buffer holding hash of message.
 * inLen   Length of data in buffer (hash length).
 * out     Buffer to write encrypted signature into.
 * outLen  Size of buffer to write to.
 * hash    Hash algorithm.
 * mgf     Mask generation function.
 * key     Public RSA key.
 * rng     Random number generator.
 * returns the length of the encrypted signature on success, a negative value
 * indicates failure.
 */
int wc_RsaPSS_Sign(const byte* in, word32 inLen, byte* out, word32 outLen,
                       enum wc_HashType hash, int mgf, RsaKey* key, WC_RNG* rng)
{
    return wc_RsaPSS_Sign_ex(in, inLen, out, outLen, hash, mgf,
                                            RSA_PSS_SALT_LEN_DEFAULT, key, rng);
}

/* Sign the hash of a message using RSA-PSS.
 *
 * in       Buffer holding hash of message.
 * inLen    Length of data in buffer (hash length).
 * out      Buffer to write encrypted signature into.
 * outLen   Size of buffer to write to.
 * hash     Hash algorithm.
 * mgf      Mask generation function.
 * saltLen  Length of salt used. RSA_PSS_SALT_LEN_DEFAULT (-1) indicates salt
 *          length is the same as the hash length. RSA_PSS_SALT_LEN_DISCOVER
 *          indicates salt length is determined from the data.
 * key      Public RSA key.
 * rng      Random number generator.
 * returns the length of the encrypted signature on success, a negative value
 * indicates failure.
 */
int wc_RsaPSS_Sign_ex(const byte* in, word32 inLen, byte* out, word32 outLen,
                      enum wc_HashType hash, int mgf, int saltLen, RsaKey* key,
                      WC_RNG* rng)
{
    return RsaPublicEncryptEx(in, inLen, out, outLen, key,
        RSA_PRIVATE_ENCRYPT, RSA_BLOCK_TYPE_1, WC_RSA_PSS_PAD,
        hash, mgf, NULL, 0, saltLen, rng);
}
#endif
#endif

#if !defined(WOLFSSL_RSA_VERIFY_ONLY) || !defined(WOLFSSL_SP_MATH) || \
                                                             defined(WC_RSA_PSS)
int wc_RsaEncryptSize(RsaKey* key)
{
    int ret;

    if (key == NULL) {
        return BAD_FUNC_ARG;
    }

    ret = mp_unsigned_bin_size(&key->n);

#ifdef WOLF_CRYPTO_CB
    if (ret == 0 && key->devId != INVALID_DEVID) {
        ret = 2048/8; /* hardware handles, use 2048-bit as default */
    }
#endif

    return ret;
}
#endif

#ifndef WOLFSSL_RSA_VERIFY_ONLY
/* flatten RsaKey structure into individual elements (e, n) */
int wc_RsaFlattenPublicKey(RsaKey* key, byte* e, word32* eSz, byte* n,
                                                                   word32* nSz)
{
    int sz, ret;

    if (key == NULL || e == NULL || eSz == NULL || n == NULL || nSz == NULL) {
        return BAD_FUNC_ARG;
    }

    sz = mp_unsigned_bin_size(&key->e);
    if ((word32)sz > *eSz)
        return RSA_BUFFER_E;
    ret = mp_to_unsigned_bin(&key->e, e);
    if (ret != MP_OKAY)
        return ret;
    *eSz = (word32)sz;

    sz = wc_RsaEncryptSize(key);
    if ((word32)sz > *nSz)
        return RSA_BUFFER_E;
    ret = mp_to_unsigned_bin(&key->n, n);
    if (ret != MP_OKAY)
        return ret;
    *nSz = (word32)sz;

    return 0;
}
#endif

#endif /* HAVE_FIPS */


#ifndef WOLFSSL_RSA_VERIFY_ONLY
static int RsaGetValue(mp_int* in, byte* out, word32* outSz)
{
    word32 sz;
    int ret = 0;

    /* Parameters ensured by calling function. */

    sz = (word32)mp_unsigned_bin_size(in);
    if (sz > *outSz)
        ret = RSA_BUFFER_E;

    if (ret == 0)
        ret = mp_to_unsigned_bin(in, out);

    if (ret == MP_OKAY)
        *outSz = sz;

    return ret;
}


int wc_RsaExportKey(RsaKey* key,
                    byte* e, word32* eSz, byte* n, word32* nSz,
                    byte* d, word32* dSz, byte* p, word32* pSz,
                    byte* q, word32* qSz)
{
    int ret = BAD_FUNC_ARG;

    if (key && e && eSz && n && nSz && d && dSz && p && pSz && q && qSz)
        ret = 0;

    if (ret == 0)
        ret = RsaGetValue(&key->e, e, eSz);
    if (ret == 0)
        ret = RsaGetValue(&key->n, n, nSz);
#ifndef WOLFSSL_RSA_PUBLIC_ONLY
    if (ret == 0)
        ret = RsaGetValue(&key->d, d, dSz);
    if (ret == 0)
        ret = RsaGetValue(&key->p, p, pSz);
    if (ret == 0)
        ret = RsaGetValue(&key->q, q, qSz);
#else
    /* no private parts to key */
    if (d == NULL || p == NULL || q == NULL || dSz == NULL || pSz == NULL
            || qSz == NULL) {
        ret = BAD_FUNC_ARG;
    }
    else {
        *dSz = 0;
        *pSz = 0;
        *qSz = 0;
    }
#endif /* WOLFSSL_RSA_PUBLIC_ONLY */

    return ret;
}
#endif


#ifdef WOLFSSL_KEY_GEN

/* Check that |p-q| > 2^((size/2)-100) */
static int wc_CompareDiffPQ(mp_int* p, mp_int* q, int size)
{
    mp_int c, d;
    int ret;

    if (p == NULL || q == NULL)
        return BAD_FUNC_ARG;

    ret = mp_init_multi(&c, &d, NULL, NULL, NULL, NULL);

    /* c = 2^((size/2)-100) */
    if (ret == 0)
        ret = mp_2expt(&c, (size/2)-100);

    /* d = |p-q| */
    if (ret == 0)
        ret = mp_sub(p, q, &d);

    if (ret == 0)
        ret = mp_abs(&d, &d);

    /* compare */
    if (ret == 0)
        ret = mp_cmp(&d, &c);

    if (ret == MP_GT)
        ret = MP_OKAY;

    mp_clear(&d);
    mp_clear(&c);

    return ret;
}


/* The lower_bound value is floor(2^(0.5) * 2^((nlen/2)-1)) where nlen is 4096.
 * This number was calculated using a small test tool written with a common
 * large number math library. Other values of nlen may be checked with a subset
 * of lower_bound. */
static const byte lower_bound[] = {
    0xB5, 0x04, 0xF3, 0x33, 0xF9, 0xDE, 0x64, 0x84,
    0x59, 0x7D, 0x89, 0xB3, 0x75, 0x4A, 0xBE, 0x9F,
    0x1D, 0x6F, 0x60, 0xBA, 0x89, 0x3B, 0xA8, 0x4C,
    0xED, 0x17, 0xAC, 0x85, 0x83, 0x33, 0x99, 0x15,
/* 512 */
    0x4A, 0xFC, 0x83, 0x04, 0x3A, 0xB8, 0xA2, 0xC3,
    0xA8, 0xB1, 0xFE, 0x6F, 0xDC, 0x83, 0xDB, 0x39,
    0x0F, 0x74, 0xA8, 0x5E, 0x43, 0x9C, 0x7B, 0x4A,
    0x78, 0x04, 0x87, 0x36, 0x3D, 0xFA, 0x27, 0x68,
/* 1024 */
    0xD2, 0x20, 0x2E, 0x87, 0x42, 0xAF, 0x1F, 0x4E,
    0x53, 0x05, 0x9C, 0x60, 0x11, 0xBC, 0x33, 0x7B,
    0xCA, 0xB1, 0xBC, 0x91, 0x16, 0x88, 0x45, 0x8A,
    0x46, 0x0A, 0xBC, 0x72, 0x2F, 0x7C, 0x4E, 0x33,
    0xC6, 0xD5, 0xA8, 0xA3, 0x8B, 0xB7, 0xE9, 0xDC,
    0xCB, 0x2A, 0x63, 0x43, 0x31, 0xF3, 0xC8, 0x4D,
    0xF5, 0x2F, 0x12, 0x0F, 0x83, 0x6E, 0x58, 0x2E,
    0xEA, 0xA4, 0xA0, 0x89, 0x90, 0x40, 0xCA, 0x4A,
/* 2048 */
    0x81, 0x39, 0x4A, 0xB6, 0xD8, 0xFD, 0x0E, 0xFD,
    0xF4, 0xD3, 0xA0, 0x2C, 0xEB, 0xC9, 0x3E, 0x0C,
    0x42, 0x64, 0xDA, 0xBC, 0xD5, 0x28, 0xB6, 0x51,
    0xB8, 0xCF, 0x34, 0x1B, 0x6F, 0x82, 0x36, 0xC7,
    0x01, 0x04, 0xDC, 0x01, 0xFE, 0x32, 0x35, 0x2F,
    0x33, 0x2A, 0x5E, 0x9F, 0x7B, 0xDA, 0x1E, 0xBF,
    0xF6, 0xA1, 0xBE, 0x3F, 0xCA, 0x22, 0x13, 0x07,
    0xDE, 0xA0, 0x62, 0x41, 0xF7, 0xAA, 0x81, 0xC2,
/* 3072 */
    0xC1, 0xFC, 0xBD, 0xDE, 0xA2, 0xF7, 0xDC, 0x33,
    0x18, 0x83, 0x8A, 0x2E, 0xAF, 0xF5, 0xF3, 0xB2,
    0xD2, 0x4F, 0x4A, 0x76, 0x3F, 0xAC, 0xB8, 0x82,
    0xFD, 0xFE, 0x17, 0x0F, 0xD3, 0xB1, 0xF7, 0x80,
    0xF9, 0xAC, 0xCE, 0x41, 0x79, 0x7F, 0x28, 0x05,
    0xC2, 0x46, 0x78, 0x5E, 0x92, 0x95, 0x70, 0x23,
    0x5F, 0xCF, 0x8F, 0x7B, 0xCA, 0x3E, 0xA3, 0x3B,
    0x4D, 0x7C, 0x60, 0xA5, 0xE6, 0x33, 0xE3, 0xE1
/* 4096 */
};


/* returns 1 on key size ok and 0 if not ok */
static WC_INLINE int RsaSizeCheck(int size)
{
    if (size < RSA_MIN_SIZE || size > RSA_MAX_SIZE) {
        return 0;
    }

#ifdef HAVE_FIPS
    /* Key size requirements for CAVP */
    switch (size) {
        case 1024:
        case 2048:
        case 3072:
        case 4096:
            return 1;
    }

    return 0;
#else
    return 1; /* allow unusual key sizes in non FIPS mode */
#endif /* HAVE_FIPS */
}


static int _CheckProbablePrime(mp_int* p, mp_int* q, mp_int* e, int nlen,
                                    int* isPrime, WC_RNG* rng)
{
    int ret;
    mp_int tmp1, tmp2;
    mp_int* prime;

    if (p == NULL || e == NULL || isPrime == NULL)
        return BAD_FUNC_ARG;

    if (!RsaSizeCheck(nlen))
        return BAD_FUNC_ARG;

    *isPrime = MP_NO;

    if (q != NULL) {
        /* 5.4 - check that |p-q| <= (2^(1/2))(2^((nlen/2)-1)) */
        ret = wc_CompareDiffPQ(p, q, nlen);
        if (ret != MP_OKAY) goto notOkay;
        prime = q;
    }
    else
        prime = p;

    ret = mp_init_multi(&tmp1, &tmp2, NULL, NULL, NULL, NULL);
    if (ret != MP_OKAY) goto notOkay;

    /* 4.4,5.5 - Check that prime >= (2^(1/2))(2^((nlen/2)-1))
     *           This is a comparison against lowerBound */
    ret = mp_read_unsigned_bin(&tmp1, lower_bound, nlen/16);
    if (ret != MP_OKAY) goto notOkay;
    ret = mp_cmp(prime, &tmp1);
    if (ret == MP_LT) goto exit;

    /* 4.5,5.6 - Check that GCD(p-1, e) == 1 */
    ret = mp_sub_d(prime, 1, &tmp1);  /* tmp1 = prime-1 */
    if (ret != MP_OKAY) goto notOkay;
    ret = mp_gcd(&tmp1, e, &tmp2);  /* tmp2 = gcd(prime-1, e) */
    if (ret != MP_OKAY) goto notOkay;
    ret = mp_cmp_d(&tmp2, 1);
    if (ret != MP_EQ) goto exit; /* e divides p-1 */

    /* 4.5.1,5.6.1 - Check primality of p with 8 rounds of M-R.
     * mp_prime_is_prime_ex() performs test divisions against the first 256
     * prime numbers. After that it performs 8 rounds of M-R using random
     * bases between 2 and n-2.
     * mp_prime_is_prime() performs the same test divisions and then does
     * M-R with the first 8 primes. Both functions set isPrime as a
     * side-effect. */
    if (rng != NULL)
        ret = mp_prime_is_prime_ex(prime, 8, isPrime, rng);
    else
        ret = mp_prime_is_prime(prime, 8, isPrime);
    if (ret != MP_OKAY) goto notOkay;

exit:
    ret = MP_OKAY;
notOkay:
    mp_clear(&tmp1);
    mp_clear(&tmp2);
    return ret;
}


int wc_CheckProbablePrime_ex(const byte* pRaw, word32 pRawSz,
                          const byte* qRaw, word32 qRawSz,
                          const byte* eRaw, word32 eRawSz,
                          int nlen, int* isPrime, WC_RNG* rng)
{
    mp_int p, q, e;
    mp_int* Q = NULL;
    int ret;

    if (pRaw == NULL || pRawSz == 0 ||
        eRaw == NULL || eRawSz == 0 ||
        isPrime == NULL) {

        return BAD_FUNC_ARG;
    }

    if ((qRaw != NULL && qRawSz == 0) || (qRaw == NULL && qRawSz != 0))
        return BAD_FUNC_ARG;

    ret = mp_init_multi(&p, &q, &e, NULL, NULL, NULL);

    if (ret == MP_OKAY)
        ret = mp_read_unsigned_bin(&p, pRaw, pRawSz);

    if (ret == MP_OKAY) {
        if (qRaw != NULL) {
            ret = mp_read_unsigned_bin(&q, qRaw, qRawSz);
            if (ret == MP_OKAY)
                Q = &q;
        }
    }

    if (ret == MP_OKAY)
        ret = mp_read_unsigned_bin(&e, eRaw, eRawSz);

    if (ret == MP_OKAY)
        ret = _CheckProbablePrime(&p, Q, &e, nlen, isPrime, rng);

    ret = (ret == MP_OKAY) ? 0 : PRIME_GEN_E;

    mp_clear(&p);
    mp_clear(&q);
    mp_clear(&e);

    return ret;
}


int wc_CheckProbablePrime(const byte* pRaw, word32 pRawSz,
                          const byte* qRaw, word32 qRawSz,
                          const byte* eRaw, word32 eRawSz,
                          int nlen, int* isPrime)
{
    return wc_CheckProbablePrime_ex(pRaw, pRawSz, qRaw, qRawSz,
                          eRaw, eRawSz, nlen, isPrime, NULL);
}

#if !defined(HAVE_FIPS) || (defined(HAVE_FIPS) && \
        defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2))
/* Make an RSA key for size bits, with e specified, 65537 is a good e */
int wc_MakeRsaKey(RsaKey* key, int size, long e, WC_RNG* rng)
{
#ifndef WC_NO_RNG
    mp_int p, q, tmp1, tmp2, tmp3;
    int err, i, failCount, primeSz, isPrime = 0;
    byte* buf = NULL;

    if (key == NULL || rng == NULL)
        return BAD_FUNC_ARG;

    if (!RsaSizeCheck(size))
        return BAD_FUNC_ARG;

    if (e < 3 || (e & 1) == 0)
        return BAD_FUNC_ARG;

#if defined(WOLFSSL_CRYPTOCELL)

    return cc310_RSA_GenerateKeyPair(key, size, e);

#endif /*WOLFSSL_CRYPTOCELL*/

#ifdef WOLF_CRYPTO_CB
    if (key->devId != INVALID_DEVID) {
        int ret = wc_CryptoCb_MakeRsaKey(key, size, e, rng);
        if (ret != CRYPTOCB_UNAVAILABLE)
            return ret;
        /* fall-through when unavailable */
    }
#endif

#if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_RSA) && \
    defined(WC_ASYNC_ENABLE_RSA_KEYGEN)
    if (key->asyncDev.marker == WOLFSSL_ASYNC_MARKER_RSA) {
    #ifdef HAVE_CAVIUM
        /* TODO: Not implemented */
    #elif defined(HAVE_INTEL_QA)
        return IntelQaRsaKeyGen(&key->asyncDev, key, size, e, rng);
    #else
        if (wc_AsyncTestInit(&key->asyncDev, ASYNC_TEST_RSA_MAKE)) {
            WC_ASYNC_TEST* testDev = &key->asyncDev.test;
            testDev->rsaMake.rng = rng;
            testDev->rsaMake.key = key;
            testDev->rsaMake.size = size;
            testDev->rsaMake.e = e;
            return WC_PENDING_E;
        }
    #endif
    }
#endif

    err = mp_init_multi(&p, &q, &tmp1, &tmp2, &tmp3, NULL);

    if (err == MP_OKAY)
        err = mp_set_int(&tmp3, e);

    /* The failCount value comes from NIST FIPS 186-4, section B.3.3,
     * process steps 4.7 and 5.8. */
    failCount = 5 * (size / 2);
    primeSz = size / 16; /* size is the size of n in bits.
                            primeSz is in bytes. */

    /* allocate buffer to work with */
    if (err == MP_OKAY) {
        buf = (byte*)XMALLOC(primeSz, key->heap, DYNAMIC_TYPE_RSA);
        if (buf == NULL)
            err = MEMORY_E;
    }

    /* make p */
    if (err == MP_OKAY) {
        isPrime = 0;
        i = 0;
        do {
#ifdef SHOW_GEN
            printf(".");
            fflush(stdout);
#endif
            /* generate value */
            err = wc_RNG_GenerateBlock(rng, buf, primeSz);
            if (err == 0) {
                /* prime lower bound has the MSB set, set it in candidate */
                buf[0] |= 0x80;
                /* make candidate odd */
                buf[primeSz-1] |= 0x01;
                /* load value */
                err = mp_read_unsigned_bin(&p, buf, primeSz);
            }

            if (err == MP_OKAY)
                err = _CheckProbablePrime(&p, NULL, &tmp3, size, &isPrime, rng);

#ifdef HAVE_FIPS
            i++;
#else
            /* Keep the old retry behavior in non-FIPS build. */
            (void)i;
#endif
        } while (err == MP_OKAY && !isPrime && i < failCount);
    }

    if (err == MP_OKAY && !isPrime)
        err = PRIME_GEN_E;

    /* make q */
    if (err == MP_OKAY) {
        isPrime = 0;
        i = 0;
        do {
#ifdef SHOW_GEN
            printf(".");
            fflush(stdout);
#endif
            /* generate value */
            err = wc_RNG_GenerateBlock(rng, buf, primeSz);
            if (err == 0) {
                /* prime lower bound has the MSB set, set it in candidate */
                buf[0] |= 0x80;
                /* make candidate odd */
                buf[primeSz-1] |= 0x01;
                /* load value */
                err = mp_read_unsigned_bin(&q, buf, primeSz);
            }

            if (err == MP_OKAY)
                err = _CheckProbablePrime(&p, &q, &tmp3, size, &isPrime, rng);

#ifdef HAVE_FIPS
            i++;
#else
            /* Keep the old retry behavior in non-FIPS build. */
            (void)i;
#endif
        } while (err == MP_OKAY && !isPrime && i < failCount);
    }

    if (err == MP_OKAY && !isPrime)
        err = PRIME_GEN_E;

    if (buf) {
        ForceZero(buf, primeSz);
        XFREE(buf, key->heap, DYNAMIC_TYPE_RSA);
    }

    if (err == MP_OKAY && mp_cmp(&p, &q) < 0) {
        err = mp_copy(&p, &tmp1);
        if (err == MP_OKAY)
            err = mp_copy(&q, &p);
        if (err == MP_OKAY)
            mp_copy(&tmp1, &q);
    }

    /* Setup RsaKey buffers */
    if (err == MP_OKAY)
        err = mp_init_multi(&key->n, &key->e, &key->d, &key->p, &key->q, NULL);
    if (err == MP_OKAY)
        err = mp_init_multi(&key->dP, &key->dQ, &key->u, NULL, NULL, NULL);

    /* Software Key Calculation */
    if (err == MP_OKAY)                /* tmp1 = p-1 */
        err = mp_sub_d(&p, 1, &tmp1);
    if (err == MP_OKAY)                /* tmp2 = q-1 */
        err = mp_sub_d(&q, 1, &tmp2);
#ifdef WC_RSA_BLINDING
    if (err == MP_OKAY)                /* tmp3 = order of n */
        err = mp_mul(&tmp1, &tmp2, &tmp3);
#else
    if (err == MP_OKAY)                /* tmp3 = lcm(p-1, q-1), last loop */
        err = mp_lcm(&tmp1, &tmp2, &tmp3);
#endif
    /* make key */
    if (err == MP_OKAY)                /* key->e = e */
        err = mp_set_int(&key->e, (mp_digit)e);
#ifdef WC_RSA_BLINDING
    /* Blind the inverse operation with a value that is invertable */
    if (err == MP_OKAY) {
        do {
            err = mp_rand(&key->p, get_digit_count(&tmp3), rng);
            if (err == MP_OKAY)
                err = mp_set_bit(&key->p, 0);
            if (err == MP_OKAY)
                err = mp_set_bit(&key->p, size - 1);
            if (err == MP_OKAY)
                err = mp_gcd(&key->p, &tmp3, &key->q);
        }
        while ((err == MP_OKAY) && !mp_isone(&key->q));
    }
    if (err == MP_OKAY)
        err = mp_mul_d(&key->p, (mp_digit)e, &key->e);
#endif
    if (err == MP_OKAY)                /* key->d = 1/e mod lcm(p-1, q-1) */
        err = mp_invmod(&key->e, &tmp3, &key->d);
#ifdef WC_RSA_BLINDING
    /* Take off blinding from d and reset e */
    if (err == MP_OKAY)
        err = mp_mulmod(&key->d, &key->p, &tmp3, &key->d);
    if (err == MP_OKAY)
        err = mp_set_int(&key->e, (mp_digit)e);
#endif
    if (err == MP_OKAY)                /* key->n = pq */
        err = mp_mul(&p, &q, &key->n);
    if (err == MP_OKAY)                /* key->dP = d mod(p-1) */
        err = mp_mod(&key->d, &tmp1, &key->dP);
    if (err == MP_OKAY)                /* key->dQ = d mod(q-1) */
        err = mp_mod(&key->d, &tmp2, &key->dQ);
#ifdef WOLFSSL_MP_INVMOD_CONSTANT_TIME
    if (err == MP_OKAY)                /* key->u = 1/q mod p */
        err = mp_invmod(&q, &p, &key->u);
#else
    if (err == MP_OKAY)
        err = mp_sub_d(&p, 2, &tmp3);
    if (err == MP_OKAY)                /* key->u = 1/q mod p = q^p-2 mod p */
        err = mp_exptmod(&q, &tmp3 , &p, &key->u);
#endif
    if (err == MP_OKAY)
        err = mp_copy(&p, &key->p);
    if (err == MP_OKAY)
        err = mp_copy(&q, &key->q);

#ifdef HAVE_WOLF_BIGINT
    /* make sure raw unsigned bin version is available */
    if (err == MP_OKAY)
         err = wc_mp_to_bigint(&key->n, &key->n.raw);
    if (err == MP_OKAY)
         err = wc_mp_to_bigint(&key->e, &key->e.raw);
    if (err == MP_OKAY)
         err = wc_mp_to_bigint(&key->d, &key->d.raw);
    if (err == MP_OKAY)
         err = wc_mp_to_bigint(&key->p, &key->p.raw);
    if (err == MP_OKAY)
         err = wc_mp_to_bigint(&key->q, &key->q.raw);
    if (err == MP_OKAY)
         err = wc_mp_to_bigint(&key->dP, &key->dP.raw);
    if (err == MP_OKAY)
         err = wc_mp_to_bigint(&key->dQ, &key->dQ.raw);
    if (err == MP_OKAY)
         err = wc_mp_to_bigint(&key->u, &key->u.raw);
#endif

    if (err == MP_OKAY)
        key->type = RSA_PRIVATE;

    mp_clear(&tmp1);
    mp_clear(&tmp2);
    mp_clear(&tmp3);
    mp_clear(&p);
    mp_clear(&q);

#if defined(WOLFSSL_KEY_GEN) && !defined(WOLFSSL_NO_RSA_KEY_CHECK)
    /* Perform the pair-wise consistency test on the new key. */
    if (err == 0)
        err = wc_CheckRsaKey(key);
#endif

    if (err != 0) {
        wc_FreeRsaKey(key);
        return err;
    }

#if defined(WOLFSSL_XILINX_CRYPT) || defined(WOLFSSL_CRYPTOCELL)
    if (wc_InitRsaHw(key) != 0) {
        return BAD_STATE_E;
    }
#endif
    return 0;
#else
    return NOT_COMPILED_IN;
#endif
}
#endif /* !FIPS || FIPS_VER >= 2 */
#endif /* WOLFSSL_KEY_GEN */


#ifdef WC_RSA_BLINDING
int wc_RsaSetRNG(RsaKey* key, WC_RNG* rng)
{
    if (key == NULL)
        return BAD_FUNC_ARG;

    key->rng = rng;

    return 0;
}
#endif /* WC_RSA_BLINDING */

#ifdef WC_RSA_NONBLOCK
int wc_RsaSetNonBlock(RsaKey* key, RsaNb* nb)
{
    if (key == NULL)
        return BAD_FUNC_ARG;

    if (nb) {
        XMEMSET(nb, 0, sizeof(RsaNb));
    }

    /* Allow nb == NULL to clear non-block mode */
    key->nb = nb;

    return 0;
}
#ifdef WC_RSA_NONBLOCK_TIME
int wc_RsaSetNonBlockTime(RsaKey* key, word32 maxBlockUs, word32 cpuMHz)
{
    if (key == NULL || key->nb == NULL) {
        return BAD_FUNC_ARG;
    }

    /* calculate maximum number of instructions to block */
    key->nb->exptmod.maxBlockInst = cpuMHz * maxBlockUs;

    return 0;
}
#endif /* WC_RSA_NONBLOCK_TIME */
#endif /* WC_RSA_NONBLOCK */

#endif /* NO_RSA */
