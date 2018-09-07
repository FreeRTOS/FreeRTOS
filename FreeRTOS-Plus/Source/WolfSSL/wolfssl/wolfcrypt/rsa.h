/* rsa.h
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

#ifndef WOLF_CRYPT_RSA_H
#define WOLF_CRYPT_RSA_H

#include <wolfssl/wolfcrypt/types.h>

#ifndef NO_RSA

#ifdef HAVE_FIPS
/* for fips @wc_fips */
#include <cyassl/ctaocrypt/rsa.h>
#if defined(CYASSL_KEY_GEN) && !defined(WOLFSSL_KEY_GEN)
    #define WOLFSSL_KEY_GEN
#endif
#else
    #include <wolfssl/wolfcrypt/integer.h>
    #include <wolfssl/wolfcrypt/random.h>
#endif /* HAVE_FIPS */

#ifdef __cplusplus
    extern "C" {
#endif

#ifndef HAVE_FIPS /* avoid redefinition of structs */
#define WOLFSSL_RSA_CAVIUM_MAGIC 0xBEEF0006

enum {
    RSA_PUBLIC   = 0,
    RSA_PRIVATE  = 1
};

/* RSA */
typedef struct RsaKey {
    mp_int n, e, d, p, q, dP, dQ, u;
    int   type;                               /* public or private */
    void* heap;                               /* for user memory overrides */
#ifdef HAVE_CAVIUM
    int    devId;           /* nitrox device id */
    word32 magic;           /* using cavium magic */
    word64 contextHandle;   /* nitrox context memory handle */
    byte*  c_n;             /* cavium byte buffers for key parts */
    byte*  c_e;
    byte*  c_d;
    byte*  c_p;
    byte*  c_q;
    byte*  c_dP;
    byte*  c_dQ;
    byte*  c_u;             /* sizes in bytes */
    word16 c_nSz, c_eSz, c_dSz, c_pSz, c_qSz, c_dP_Sz, c_dQ_Sz, c_uSz;
#endif
} RsaKey;
#endif /*HAVE_FIPS */


WOLFSSL_API int  wc_InitRsaKey(RsaKey* key, void*);
WOLFSSL_API int  wc_FreeRsaKey(RsaKey* key);

WOLFSSL_API int  wc_RsaPublicEncrypt(const byte* in, word32 inLen, byte* out,
                                 word32 outLen, RsaKey* key, RNG* rng);
WOLFSSL_API int  wc_RsaPrivateDecryptInline(byte* in, word32 inLen, byte** out,
                                        RsaKey* key);
WOLFSSL_API int  wc_RsaPrivateDecrypt(const byte* in, word32 inLen, byte* out,
                                  word32 outLen, RsaKey* key);
WOLFSSL_API int  wc_RsaSSL_Sign(const byte* in, word32 inLen, byte* out,
                            word32 outLen, RsaKey* key, RNG* rng);
WOLFSSL_API int  wc_RsaSSL_VerifyInline(byte* in, word32 inLen, byte** out,
                                    RsaKey* key);
WOLFSSL_API int  wc_RsaSSL_Verify(const byte* in, word32 inLen, byte* out,
                              word32 outLen, RsaKey* key);
WOLFSSL_API int  wc_RsaEncryptSize(RsaKey* key);

#ifndef HAVE_FIPS /* to avoid asn duplicate symbols @wc_fips */
WOLFSSL_API int  wc_RsaPrivateKeyDecode(const byte* input, word32* inOutIdx,
                                                               RsaKey*, word32);
WOLFSSL_API int  wc_RsaPublicKeyDecode(const byte* input, word32* inOutIdx,
                                                               RsaKey*, word32);
WOLFSSL_API int  wc_RsaPublicKeyDecodeRaw(const byte* n, word32 nSz,
                                        const byte* e, word32 eSz, RsaKey* key);
#ifdef WOLFSSL_KEY_GEN
    WOLFSSL_API int wc_RsaKeyToDer(RsaKey*, byte* output, word32 inLen);
#endif
#endif /* HAVE_FIPS*/
WOLFSSL_API int  wc_RsaFlattenPublicKey(RsaKey*, byte*, word32*, byte*,
                                                                       word32*);

#ifdef WOLFSSL_KEY_GEN
    WOLFSSL_API int wc_MakeRsaKey(RsaKey* key, int size, long e, RNG* rng);
#endif

#ifdef HAVE_CAVIUM
    WOLFSSL_API int  wc_RsaInitCavium(RsaKey*, int);
    WOLFSSL_API void wc_RsaFreeCavium(RsaKey*);
#endif

#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* NO_RSA */
#endif /* WOLF_CRYPT_RSA_H */

