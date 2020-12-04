/* cryptocb.h
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

#ifndef _WOLF_CRYPTO_CB_H_
#define _WOLF_CRYPTO_CB_H_

#include <wolfssl/wolfcrypt/types.h>

#ifdef __cplusplus
    extern "C" {
#endif

/* Defines the Crypto Callback interface version, for compatibility */
/* Increment this when Crypto Callback interface changes are made */
#define CRYPTO_CB_VER   2


#ifdef WOLF_CRYPTO_CB

#ifndef NO_RSA
    #include <wolfssl/wolfcrypt/rsa.h>
#endif
#ifdef HAVE_ECC
    #include <wolfssl/wolfcrypt/ecc.h>
#endif
#ifndef NO_AES
    #include <wolfssl/wolfcrypt/aes.h>
#endif
#ifndef NO_SHA
    #include <wolfssl/wolfcrypt/sha.h>
#endif
#ifndef NO_SHA256
    #include <wolfssl/wolfcrypt/sha256.h>
#endif
#ifndef NO_HMAC
    #include <wolfssl/wolfcrypt/hmac.h>
#endif
#ifndef WC_NO_RNG
    #include <wolfssl/wolfcrypt/random.h>
#endif
#ifndef NO_DES3
    #include <wolfssl/wolfcrypt/des3.h>
#endif


/* Crypto Information Structure for callbacks */
typedef struct wc_CryptoInfo {
    int algo_type; /* enum wc_AlgoType */
#if !defined(NO_RSA) || defined(HAVE_ECC)
    struct {
        int type; /* enum wc_PkType */
        union {
        #ifndef NO_RSA
            struct {
                const byte* in;
                word32      inLen;
                byte*       out;
                word32*     outLen;
                int         type;
                RsaKey*     key;
                WC_RNG*     rng;
            } rsa;
        #ifdef WOLFSSL_KEY_GEN
            struct {
                RsaKey* key;
                int     size;
                long    e;
                WC_RNG* rng;
            } rsakg;
        #endif
        #endif
        #ifdef HAVE_ECC
            struct {
                WC_RNG*  rng;
                int      size;
                ecc_key* key;
                int      curveId;
            } eckg;
            struct {
                ecc_key* private_key;
                ecc_key* public_key;
                byte*    out;
                word32*  outlen;
            } ecdh;
            struct {
                const byte* in;
                word32      inlen;
                byte*       out;
                word32*     outlen;
                WC_RNG*     rng;
                ecc_key*    key;
            } eccsign;
            struct {
                const byte* sig;
                word32      siglen;
                const byte* hash;
                word32      hashlen;
                int*        res;
                ecc_key*    key;
            } eccverify;
        #endif
        };
    } pk;
#endif /* !NO_RSA || HAVE_ECC */
#if !defined(NO_AES) || !defined(NO_DES3)
    struct {
        int type; /* enum wc_CipherType */
        int enc;
        union {
        #ifdef HAVE_AESGCM
            struct {
                Aes*        aes;
                byte*       out;
                const byte* in;
                word32      sz;
                const byte* iv;
                word32      ivSz;
                byte*       authTag;
                word32      authTagSz;
                const byte* authIn;
                word32      authInSz;
            } aesgcm_enc;
            struct {
                Aes*        aes;
                byte*       out;
                const byte* in;
                word32      sz;
                const byte* iv;
                word32      ivSz;
                const byte* authTag;
                word32      authTagSz;
                const byte* authIn;
                word32      authInSz;
            } aesgcm_dec;
        #endif /* HAVE_AESGCM */
        #ifdef HAVE_AES_CBC
            struct {
                Aes*        aes;
                byte*       out;
                const byte* in;
                word32      sz;
            } aescbc;
        #endif /* HAVE_AES_CBC */
        #ifndef NO_DES3
            struct {
                Des3*       des;
                byte*       out;
                const byte* in;
                word32      sz;
            } des3;
        #endif
        };
    } cipher;
#endif /* !NO_AES || !NO_DES3 */
#if !defined(NO_SHA) || !defined(NO_SHA256)
    struct {
        int type; /* enum wc_HashType */
        const byte* in;
        word32 inSz;
        byte* digest;
        union {
        #ifndef NO_SHA
            wc_Sha* sha1;
        #endif
        #ifndef NO_SHA256
            wc_Sha256* sha256;
        #endif
        };
    } hash;
#endif /* !NO_SHA || !NO_SHA256 */
#ifndef NO_HMAC
    struct {
        int macType; /* enum wc_HashType */
        const byte* in;
        word32 inSz;
        byte* digest;
        Hmac* hmac;
    } hmac;
#endif
#ifndef WC_NO_RNG
    struct {
        WC_RNG* rng;
        byte* out;
        word32 sz;
    } rng;
    struct {
        OS_Seed* os;
        byte* seed;
        word32 sz;
    } seed;
#endif
} wc_CryptoInfo;


typedef int (*CryptoDevCallbackFunc)(int devId, wc_CryptoInfo* info, void* ctx);

WOLFSSL_LOCAL void wc_CryptoCb_Init(void);

WOLFSSL_API int  wc_CryptoCb_RegisterDevice(int devId, CryptoDevCallbackFunc cb, void* ctx);
WOLFSSL_API void wc_CryptoCb_UnRegisterDevice(int devId);

/* old function names */
#define wc_CryptoDev_RegisterDevice   wc_CryptoCb_RegisterDevice
#define wc_CryptoDev_UnRegisterDevice wc_CryptoCb_UnRegisterDevice


#ifndef NO_RSA
WOLFSSL_LOCAL int wc_CryptoCb_Rsa(const byte* in, word32 inLen, byte* out,
    word32* outLen, int type, RsaKey* key, WC_RNG* rng);

#ifdef WOLFSSL_KEY_GEN
WOLFSSL_LOCAL int wc_CryptoCb_MakeRsaKey(RsaKey* key, int size, long e,
    WC_RNG* rng);
#endif /* WOLFSSL_KEY_GEN */
#endif /* !NO_RSA */

#ifdef HAVE_ECC
WOLFSSL_LOCAL int wc_CryptoCb_MakeEccKey(WC_RNG* rng, int keySize,
    ecc_key* key, int curveId);

WOLFSSL_LOCAL int wc_CryptoCb_Ecdh(ecc_key* private_key, ecc_key* public_key,
    byte* out, word32* outlen);

WOLFSSL_LOCAL int wc_CryptoCb_EccSign(const byte* in, word32 inlen, byte* out,
    word32 *outlen, WC_RNG* rng, ecc_key* key);

WOLFSSL_LOCAL int wc_CryptoCb_EccVerify(const byte* sig, word32 siglen,
    const byte* hash, word32 hashlen, int* res, ecc_key* key);
#endif /* HAVE_ECC */

#ifndef NO_AES
#ifdef HAVE_AESGCM
WOLFSSL_LOCAL int wc_CryptoCb_AesGcmEncrypt(Aes* aes, byte* out,
     const byte* in, word32 sz, const byte* iv, word32 ivSz,
     byte* authTag, word32 authTagSz, const byte* authIn, word32 authInSz);

WOLFSSL_LOCAL int wc_CryptoCb_AesGcmDecrypt(Aes* aes, byte* out,
     const byte* in, word32 sz, const byte* iv, word32 ivSz,
     const byte* authTag, word32 authTagSz,
     const byte* authIn, word32 authInSz);
#endif /* HAVE_AESGCM */
#ifdef HAVE_AES_CBC
WOLFSSL_LOCAL int wc_CryptoCb_AesCbcEncrypt(Aes* aes, byte* out,
                               const byte* in, word32 sz);
WOLFSSL_LOCAL int wc_CryptoCb_AesCbcDecrypt(Aes* aes, byte* out,
                               const byte* in, word32 sz);
#endif /* HAVE_AES_CBC */
#endif /* !NO_AES */

#ifndef NO_DES3
WOLFSSL_LOCAL int wc_CryptoCb_Des3Encrypt(Des3* des3, byte* out,
                               const byte* in, word32 sz);
WOLFSSL_LOCAL int wc_CryptoCb_Des3Decrypt(Des3* des3, byte* out,
                               const byte* in, word32 sz);
#endif /* !NO_DES3 */

#ifndef NO_SHA
WOLFSSL_LOCAL int wc_CryptoCb_ShaHash(wc_Sha* sha, const byte* in,
    word32 inSz, byte* digest);
#endif /* !NO_SHA */

#ifndef NO_SHA256
WOLFSSL_LOCAL int wc_CryptoCb_Sha256Hash(wc_Sha256* sha256, const byte* in,
    word32 inSz, byte* digest);
#endif /* !NO_SHA256 */
#ifndef NO_HMAC
WOLFSSL_LOCAL int wc_CryptoCb_Hmac(Hmac* hmac, int macType, const byte* in,
    word32 inSz, byte* digest);
#endif /* !NO_HMAC */

#ifndef WC_NO_RNG
WOLFSSL_LOCAL int wc_CryptoCb_RandomBlock(WC_RNG* rng, byte* out, word32 sz);
WOLFSSL_LOCAL int wc_CryptoCb_RandomSeed(OS_Seed* os, byte* seed, word32 sz);
#endif

#endif /* WOLF_CRYPTO_CB */

#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* _WOLF_CRYPTO_CB_H_ */
