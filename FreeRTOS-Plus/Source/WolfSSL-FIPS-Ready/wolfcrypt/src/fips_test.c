/* fips_test.c
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


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

/* in case user set HAVE_FIPS there */
#include <wolfssl/wolfcrypt/settings.h>

#ifdef HAVE_FIPS

#include <wolfssl/wolfcrypt/fips_test.h>
#include <wolfssl/wolfcrypt/aes.h>
#include <wolfssl/wolfcrypt/des3.h>
#include <wolfssl/wolfcrypt/sha.h>
#include <wolfssl/wolfcrypt/sha512.h>
#include <wolfssl/wolfcrypt/random.h>
#include <wolfssl/wolfcrypt/sha256.h>
#include <wolfssl/wolfcrypt/sha3.h>
#include <wolfssl/wolfcrypt/rsa.h>
#include <wolfssl/wolfcrypt/hmac.h>
#include <wolfssl/wolfcrypt/ecc.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/coding.h>
#include <wolfssl/wolfcrypt/asn.h>

#define USE_CERT_BUFFERS_256
#define USE_CERT_BUFFERS_2048
#include <wolfssl/certs_test.h>   /* rsa 2048 bit key */


#ifdef USE_WINDOWS_API
    #pragma code_seg(".fipsA$p")
    #pragma const_seg(".fipsB$p")
#endif

enum {
    FIPS_AES_KEY_SZ     = 16,
    FIPS_AES_IV_SZ      = FIPS_AES_KEY_SZ,
    FIPS_AES_PLAIN_SZ   = 64,
    FIPS_AES_CBC_SZ     = FIPS_AES_PLAIN_SZ,
    FIPS_AES_CIPHER_SZ  = FIPS_AES_PLAIN_SZ,

    FIPS_GCM_KEY_SZ     = 16,
    FIPS_GCM_AUTH_SZ    = FIPS_GCM_KEY_SZ,
    FIPS_GCM_CHECK_SZ   = FIPS_GCM_KEY_SZ,
    FIPS_GCM_TAG_SZ     = FIPS_GCM_KEY_SZ,
    FIPS_GCM_PLAIN_SZ   = 32,
    FIPS_GCM_CIPHER_SZ  = FIPS_GCM_PLAIN_SZ,
    FIPS_GCM_OUT_SZ     = FIPS_GCM_PLAIN_SZ,
    FIPS_GCM_IV_SZ      = 12,

    FIPS_CCM_KEY_SZ     = 16,
    FIPS_CCM_AUTH_SZ    = 32,
    FIPS_CCM_CHECK_SZ   = FIPS_CCM_KEY_SZ,
    FIPS_CCM_TAG_SZ     = FIPS_CCM_KEY_SZ,
    FIPS_CCM_PLAIN_SZ   = 24,
    FIPS_CCM_CIPHER_SZ  = FIPS_CCM_PLAIN_SZ,
    FIPS_CCM_OUT_SZ     = FIPS_CCM_PLAIN_SZ,
    FIPS_CCM_IV_SZ      = 12,

    FIPS_DES3_KEY_SZ    = 24,
    FIPS_DES3_PLAIN_SZ  = FIPS_DES3_KEY_SZ,
    FIPS_DES3_CBC_SZ    = FIPS_DES3_KEY_SZ,
    FIPS_DES3_CIPHER_SZ = FIPS_DES3_KEY_SZ,
    FIPS_DES3_IV_SZ     = 8,

    FIPS_MAX_DIGEST_SZ  = 64,
    FIPS_HMAC_DIGEST_SZ = 64,
    FIPS_HMAC_KEY_SZ    = FIPS_HMAC_DIGEST_SZ,

    FIPS_DRBG_EA_SZ     = 48,
    FIPS_DRBG_EB_SZ     = 32,
    FIPS_DRBG_OUT_SZ    = 128,

    FIPS_RSA_SIG_SZ     = 256,
    FIPS_RSA_RESULT_SZ  = FIPS_RSA_SIG_SZ,
    FIPS_RSA_PRIME_SZ   = 1024,
    FIPS_RSA_MOD_SHORT  = 128,

    FIPS_ECC_256_SZ     = 32,
    FIPS_FFC_FIELD_SZ   = 256,
    FIPS_FFC_ORDER_SZ   = 32,

    FIPS_IN_CORE_KEY_SZ = 32,
    FIPS_IN_CORE_VERIFY_SZ = FIPS_IN_CORE_KEY_SZ
};

extern const unsigned int wolfCrypt_FIPS_ro_start[];
extern const unsigned int wolfCrypt_FIPS_ro_end[];


int wolfCrypt_FIPS_first(void);
int wolfCrypt_FIPS_last(void);

typedef int (*fips_address_function)(void);


/* sanity size checks */
#define MAX_FIPS_DATA_SZ  100000
#define MAX_FIPS_CODE_SZ 1000000

static int GenBase16_Hash(const byte* in, int length, char* out, int outSz);


/* convert hex string to binary, store size, 0 success (free mem on failure) */
static int ConvertHexToBin(const char* h1, byte* b1, word32* b1Sz,
                           const char* h2, byte* b2, word32* b2Sz,
                           const char* h3, byte* b3, word32* b3Sz,
                           const char* h4, byte* b4, word32* b4Sz)
{
    int ret;
    word32 h1Sz, h2Sz, h3Sz, h4Sz, tempSz;
    (void) h1Sz;
    (void) h2Sz;
    (void) h3Sz;
    (void) h4Sz;

    /* b1 */
    if (h1 && b1 && b1Sz) {
        h1Sz = (int) XSTRLEN(h1);
        tempSz = h1Sz / 2;
        if (tempSz > *b1Sz || tempSz <= 0) {
            return BUFFER_E;
        }
        *b1Sz = tempSz;

        ret = Base16_Decode((const byte*)h1, h1Sz, b1, b1Sz);

        if (ret != 0) {
            return ret;
        }
    }

    /* b2 */
    if (h2 && b2 && b2Sz) {
        h2Sz = (int)XSTRLEN(h2);
        tempSz = h2Sz / 2;
        if (tempSz > *b2Sz || tempSz <= 0) {
            return BUFFER_E;
        }
        *b2Sz = tempSz;

        ret = Base16_Decode((const byte*)h2, h2Sz, b2, b2Sz);
        if (ret != 0) {
            return ret;
        }
    }

    /* b3 */
    if (h3 && b3 && b3Sz) {
        h3Sz = (int)XSTRLEN(h3);
        tempSz = h3Sz / 2;
        if (tempSz > *b3Sz || tempSz <= 0) {
            return BUFFER_E;
        }
        *b3Sz =  tempSz;

        ret = Base16_Decode((const byte*)h3, h3Sz, b3, b3Sz);
        if (ret != 0) {
            return ret;
        }
    }

    /* b4 */
    if (h4 && b4 && b4Sz) {
        h4Sz = (int)XSTRLEN(h4);
        tempSz = h4Sz / 2;
        if (tempSz > *b4Sz || tempSz <= 0) {
            return BUFFER_E;
        }
        *b4Sz =  tempSz;

        ret = Base16_Decode((const byte*)h4, h4Sz, b4, b4Sz);
        if (ret != 0) {
            return ret;
        }
    }

    return 0;
}



/* 0 on success */
#if !defined(NO_AES) && !defined(NO_AES_CBC)
static int AesKnownAnswerTest(const char* key, const char* iv,
                              const char* plainText, const char* cbc)
{
    Aes   aes;

    word32 keySz   = FIPS_AES_KEY_SZ;
    word32 ivSz    = FIPS_AES_IV_SZ;
    word32 plainSz = FIPS_AES_PLAIN_SZ;
    word32 cbcSz   = FIPS_AES_CBC_SZ;

    byte binKey   [FIPS_AES_KEY_SZ];    /* AES_Key is 32 bytes */
    byte binIv    [FIPS_AES_IV_SZ];     /* AES_IV is 32 bytes */
    byte binPlain [FIPS_AES_PLAIN_SZ];  /* AES_Plain is 128 bytes */
    byte binCbc   [FIPS_AES_CBC_SZ];    /* AES_Cbc is 128 bytes */
    byte cipher   [FIPS_AES_CIPHER_SZ]; /* for cipher (same as plainSz */

    int ret = ConvertHexToBin(key, binKey, &keySz,
                              iv,  binIv,  &ivSz,
                              plainText, binPlain,  &plainSz,
                              cbc, binCbc,  &cbcSz);
    if (ret != 0)
        return ret;

    ret = AesSetKey_fips(&aes, binKey, keySz, binIv, AES_ENCRYPTION);
    if (ret != 0) {
        return ret;
    }

    ret = AesCbcEncrypt_fips(&aes, cipher, binPlain, plainSz);
    if (ret != 0) {
        return ret;
    }

    if (XMEMCMP(cipher, binCbc, plainSz) != 0) {
        return -1;
    }

    ret = AesSetKey_fips(&aes, binKey, keySz, binIv, AES_DECRYPTION);
    if (ret != 0) {
        return ret;
    }

    /* decrypt cipher in place back to plain for verify */
    ret = AesCbcDecrypt_fips(&aes, cipher, cipher, plainSz);
    if (ret != 0) {
        return ret;
    }

    if (XMEMCMP(cipher, binPlain, plainSz) != 0) {
        return -1;
    }

    return 0;
}
#endif /* NO_AES */


/* 0 on success */
#ifdef HAVE_AESGCM
static int AesGcm_KnownAnswerTest(int decrypt,
                                  const char* key, const char* iv,
                                  const char* plain, const char* auth,
                                  const char* cipher, const char* tag)
{
    Aes aes;

    byte binKey    [FIPS_GCM_KEY_SZ];    /* key */
    byte binIv     [FIPS_GCM_IV_SZ];     /* iv */
    byte binPlain  [FIPS_GCM_PLAIN_SZ];  /* plain */
    byte binAuth   [FIPS_GCM_AUTH_SZ];   /* auth */
    byte binCipher [FIPS_GCM_CIPHER_SZ]; /* cipher */
    byte binTag    [FIPS_GCM_TAG_SZ];    /* tag */
    byte out       [FIPS_GCM_OUT_SZ];    /* out */
    byte check     [FIPS_GCM_CHECK_SZ];  /* check */
    byte checkIv   [FIPS_GCM_IV_SZ];     /* check IV */

    word32 binKeySz   = FIPS_GCM_KEY_SZ,     binIvSz   = FIPS_GCM_IV_SZ,
           binPlainSz = FIPS_GCM_PLAIN_SZ,   binAuthSz = FIPS_GCM_AUTH_SZ,
           binCipherSz = FIPS_GCM_CIPHER_SZ, binTagSz  = FIPS_GCM_TAG_SZ;

    int ret = ConvertHexToBin(key, binKey, &binKeySz, iv, binIv, &binIvSz,
                              NULL, NULL, NULL, NULL, NULL, NULL);
    if (ret != 0)
        return ret;

    ret = ConvertHexToBin(plain, binPlain, &binPlainSz,
                          auth, binAuth, &binAuthSz,
                          cipher, binCipher, &binCipherSz,
                          tag, binTag, &binTagSz);
    if (ret != 0) {
        return ret;
    }

    ret = AesGcmSetKey_fips(&aes, binKey, binKeySz);
    if (ret != 0) {
        return ret;
    }

    if (decrypt) {
        ret = AesGcmDecrypt_fips(&aes, out, binCipher,
                                 binCipherSz, binIv, binIvSz,
                                 binTag, binTagSz,
                                 binAuth, binAuthSz);
        if (ret != 0) {
            return ret;
        }

        if (XMEMCMP(binPlain, out, binPlainSz) != 0) {
            return -1;
        }
    }
    else {

        ret = AesGcmSetExtIV_fips(&aes, binIv, binIvSz);
        if (ret != 0)
            return ret;

        ret = AesGcmEncrypt_fips(&aes, out, binPlain, binPlainSz,
                                 checkIv, sizeof(checkIv),
                                 check, binTagSz,
                                 binAuth, binAuthSz);
        if (ret != 0)
            return -1;

        if (XMEMCMP(binIv, checkIv, binIvSz) != 0 ||
            XMEMCMP(binCipher, out, binCipherSz) != 0 ||
            XMEMCMP(binTag, check, binTagSz) != 0) {

            return -1;
        }
    }

    return 0;
}
#endif /* HAVE_AESGCM */


/* 0 on success */
#ifndef NO_DES3
static int Des3_KnownAnswerTest(const char* key, const char* iv,
                                const char* plainText, const char* cbc)
{
    Des3  des3;

    word32 keySz   = FIPS_DES3_KEY_SZ;
    word32 ivSz    = FIPS_DES3_IV_SZ;
    word32 plainSz = FIPS_DES3_PLAIN_SZ;
    word32 cbcSz   = FIPS_DES3_CBC_SZ;

    byte binKey    [FIPS_DES3_KEY_SZ];    /* key */
    byte binIv     [FIPS_DES3_IV_SZ];     /* iv */
    byte binPlain  [FIPS_DES3_PLAIN_SZ];  /* plain */
    byte binCbc    [FIPS_DES3_CBC_SZ];    /* cbc */
    byte cipher    [FIPS_DES3_CIPHER_SZ]; /* cipher */

    int ret = ConvertHexToBin(key, binKey, &keySz,
                              iv,  binIv,  &ivSz,
                              plainText, binPlain,  &plainSz,
                              cbc, binCbc,  &cbcSz);
    if (ret != 0)
        return ret;

    ret = Des3_SetKey_fips(&des3, binKey, binIv, DES_ENCRYPTION);
    if (ret != 0) {
        return ret;
    }

    ret = Des3_CbcEncrypt_fips(&des3, cipher, binPlain, plainSz);
    if (ret != 0) {
        return ret;
    }

    if (XMEMCMP(cipher, binCbc, plainSz) != 0) {
        return -1;
    }

    ret = Des3_SetKey_fips(&des3, binKey, binIv, DES_DECRYPTION);
    if (ret != 0) {
        return ret;
    }

    /* decrypt cipher in place back to plain for verify */
    ret = Des3_CbcDecrypt_fips(&des3, cipher, cipher, plainSz);
    if (ret != 0) {
        return ret;
    }

    if (XMEMCMP(cipher, binPlain, plainSz) != 0) {
        return -1;
    }


    return 0;
}
#endif /* NO_DES3 */

#if !defined(NO_SHA) || defined(WOLFSSL_SHA512)|| defined(WOLFSSL_SHA3)
/* 0 on success */
static int HMAC_KnownAnswerTest(int type, const char* key, const char* msg,
                                const char* digest)
{
    Hmac        hmac;
    const byte* binMsg    = (const byte*)msg;
    byte        final[FIPS_MAX_DIGEST_SZ];

    word32 msgSz    = (word32)XSTRLEN(msg);
    word32 digestSz = FIPS_HMAC_DIGEST_SZ;
    word32 keySz    = FIPS_HMAC_KEY_SZ;

    byte binDigest [FIPS_HMAC_DIGEST_SZ]; /* Longest HMAC Digest 128 bytes */
    byte binKey    [FIPS_HMAC_KEY_SZ];    /* Longest HMAC Key is 128 bytes */

    int ret = ConvertHexToBin(digest, binDigest, &digestSz,
                              key, binKey, &keySz,
                              NULL, NULL, NULL,
                              NULL, NULL, NULL);
    if (ret != 0)
        return ret;

    ret = HmacSetKey_fips(&hmac, type, binKey, keySz);
    if (ret != 0) {
        return ret;
    }

    ret = HmacUpdate_fips(&hmac, binMsg, msgSz);
    if (ret != 0) {
        return ret;
    }

    ret = HmacFinal_fips(&hmac, final);
    if (ret != 0) {
        return ret;
    }

    if (XMEMCMP(final, binDigest, digestSz) != 0) {
        return -1;
    }


    return 0;
}
#endif

/* 0 on success */
#ifdef HAVE_HASHDRBG
static int DRBG_KnownAnswerTest(int reseed, const char* entropyA,
                                const char* entropyB, const char* output)
{
    word32 binEntropyASz = FIPS_DRBG_EA_SZ;
    word32 binEntropyBSz = FIPS_DRBG_EB_SZ;
    word32 binOutputSz   = FIPS_DRBG_OUT_SZ;

    byte check[WC_SHA256_DIGEST_SIZE * 4];

    byte binEntropyA [FIPS_DRBG_EA_SZ];  /* entropyA */
    byte binEntropyB [FIPS_DRBG_EB_SZ];  /* entropyB */
    byte binOutput   [FIPS_DRBG_OUT_SZ]; /* output */

    int ret = ConvertHexToBin(entropyA, binEntropyA, &binEntropyASz,
                              entropyB, binEntropyB, &binEntropyBSz,
                              output, binOutput, &binOutputSz,
                              NULL, NULL, NULL);

    if (ret != 0)
        return ret;

    /* Test Body */
    ret = RNG_HealthTest_fips(reseed, binEntropyA, binEntropyASz,
                                      binEntropyB, binEntropyBSz,
                                      check, sizeof(check));
    if (ret != 0) {
        return ret;
    }

    if (XMEMCMP(binOutput, check, sizeof(check)) != 0) {
        return -1;
    }

    return 0;
}
#endif /* HAVE_HASHDRBG */


#ifdef HAVE_ECC_CDH

static int ECC_CDH_KnownAnswerTest(const char* ax, const char* ay,
                                   const char* d, const char* ix,
                                   const char* iy, const char* z)
{
    ecc_key pub_key, priv_key;

    word32 aSz  = FIPS_ECC_256_SZ;
    word32 bSz  = FIPS_ECC_256_SZ;

    byte sharedA[FIPS_ECC_256_SZ] = {0};
    byte sharedB[FIPS_ECC_256_SZ] = {0};
#ifdef ECC_TIMING_RESISTANT
    WC_RNG rng;
#endif

    /* setup private and public keys */
    int ret = wc_ecc_init(&pub_key);
    if (ret != 0) {
        return ret;
    }
    ret = wc_ecc_init(&priv_key);
    if (ret != 0) {
        wc_ecc_free(&pub_key);
        return ret;
    }
#ifdef ECC_TIMING_RESISTANT
    if (ret == 0)
        ret = wc_InitRng(&rng);
    if (ret == 0)
        ret = wc_ecc_set_rng(&priv_key, &rng);
#endif
    ret = wc_ecc_set_flags(&priv_key, WC_ECC_FLAG_COFACTOR);
    if (ret == 0) {
        ret = wc_ecc_import_raw(&pub_key, ax, ay, NULL, "SECP256R1");
    }
    if (ret == 0) {
        ret = wc_ecc_import_raw(&priv_key, ix, iy, d, "SECP256R1");
    }

    /* compute ECC Cofactor shared secret */
    if (ret == 0) {
        ret = wc_ecc_shared_secret(&priv_key, &pub_key, sharedA, &aSz);
    }

    /* read in expected Z */
    if (ret == 0) {
        ret = Base16_Decode((const byte*)z, (word32)XSTRLEN(z), sharedB, &bSz);
    }

    /* compare results */
    if (ret == 0) {
        if (aSz != bSz || XMEMCMP(sharedA, sharedB, aSz) != 0) {
            ret = -1;
        }
    }

    wc_ecc_free(&priv_key);
    wc_ecc_free(&pub_key);
#ifdef ECC_TIMING_RESISTANT
    wc_FreeRng(&rng);
#endif

    return ret;
}

#endif /* HAVE_ECC_CDH */


#ifndef NO_RSA
static int RsaSignPKCS1v15_KnownAnswerTest(int type, const char* msg,
                                           const char* sig)
{
    RsaKey      rsa;
    const byte* binMsg = (const byte*)msg;
    byte        final[FIPS_MAX_DIGEST_SZ];
    byte        verify[FIPS_MAX_DIGEST_SZ];
    word32 msgSz    = (word32)XSTRLEN(msg);
    word32 sigSz    = FIPS_RSA_SIG_SZ;
    word32 digestSz = 0;
    word32 verifySz = (word32)sizeof(verify);
    word32 resultSz = 0;
    word32 idx      = 0;

    byte binSig    [FIPS_RSA_SIG_SZ];    /* signature */
    byte result    [FIPS_RSA_RESULT_SZ]; /* result */

    int ret = ConvertHexToBin(sig, binSig, &sigSz,
                              NULL, NULL, NULL,
                              NULL, NULL, NULL,
                              NULL, NULL, NULL);
    if (ret != 0)
        return ret;

    resultSz = sigSz;

    ret = InitRsaKey_fips(&rsa, NULL);
    if (ret != 0) {
        return ret;
    }

    switch (type) {
        case WC_SHA256 :
        {
            wc_Sha256 sha256;

            InitSha256_fips(&sha256);
            Sha256Update_fips(&sha256, binMsg, msgSz);
            Sha256Final_fips(&sha256, final);
            digestSz = WC_SHA256_DIGEST_SIZE;

            break;
        }

        default:
            FreeRsaKey_fips(&rsa);
            return -1;
    }

    ret = wc_RsaPrivateKeyDecode(client_key_der_2048, &idx, &rsa,
                                 sizeof_client_key_der_2048);
    if (ret != 0) {
        FreeRsaKey_fips(&rsa);
        return ret;
    }

    ret = RsaSSL_Sign_fips(final, digestSz, result, resultSz, &rsa, NULL);
    if (ret != (int)sigSz) {
        FreeRsaKey_fips(&rsa);
        return ret;
    }

    if (XMEMCMP(result, binSig, sigSz) != 0) {
        FreeRsaKey_fips(&rsa);
        return -1;
    }

    ret = RsaSSL_Verify_fips(result, sigSz, verify, verifySz, &rsa);
    if (ret != (int)digestSz) {
        FreeRsaKey_fips(&rsa);
        return ret;
    }

    if (XMEMCMP(verify, final, digestSz) != 0) {
        FreeRsaKey_fips(&rsa);
        return -1;
    }

    FreeRsaKey_fips(&rsa);

    return 0;
}
#endif /* NO_RSA */


#ifdef HAVE_ECC_DHE
static int EccPrimitiveZ_KnownAnswerTest(
            const char* qexServer, const char* qeyServer,
            const char* qexClient, const char* qeyClient,
            const char* deClient, const char* zVerify)
{
    ecc_key serverKey, clientKey;
    wc_Sha256 sha;
    byte z[FIPS_ECC_256_SZ];
    byte zVerifyFlat[WC_SHA256_DIGEST_SIZE];
    byte zHash[WC_SHA256_DIGEST_SIZE];
    word32 zVerifyFlatSz = sizeof(zVerifyFlat);
    word32 zSz = sizeof(z);
    int ret;
#ifdef ECC_TIMING_RESISTANT
    WC_RNG rng;
#endif

    ret = ConvertHexToBin(zVerify, zVerifyFlat, &zVerifyFlatSz,
            NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL);
#ifdef ECC_TIMING_RESISTANT
    if (ret == 0)
        ret = wc_InitRng(&rng);
#endif
    if (ret == 0)
        ret = wc_ecc_init(&serverKey);
    if (ret == 0)
        ret = wc_ecc_init(&clientKey);
#ifdef ECC_TIMING_RESISTANT
    if (ret == 0)
        ret = wc_ecc_set_rng(&clientKey, &rng);
#endif
    if (ret == 0)
        ret = wc_ecc_import_raw_ex(&serverKey, qexServer, qeyServer,
                                   NULL, ECC_SECP256R1);
    if (ret == 0)
        ret = wc_ecc_check_key(&serverKey);
    if (ret == 0)
        ret = wc_ecc_import_raw_ex(&clientKey, qexClient, qeyClient,
                                   deClient, ECC_SECP256R1);
    if (ret == 0)
        ret = wc_ecc_check_key(&clientKey);
    if (ret == 0)
        ret = wc_ecc_shared_secret(&clientKey, &serverKey, z, &zSz);
    if (ret == 0)
        ret = wc_InitSha256(&sha);
    if (ret == 0)
        ret = wc_Sha256Update(&sha, z, zSz);
    if (ret == 0)
        ret = wc_Sha256Final(&sha, zHash);
    if (ret == 0) {
        if ((zVerifyFlatSz != zSz) || XMEMCMP(zHash, zVerifyFlat, zSz))
            ret = -1;
    }
    wc_ecc_free(&serverKey);
    wc_ecc_free(&clientKey);
#ifdef ECC_TIMING_RESISTANT
    wc_FreeRng(&rng);
#endif
    return ret;
}
#endif /* HAVE_ECC_DHE */


#ifndef NO_DH

static int DhPrimitiveZ_KnownAnswerTest(const char* p, const char* q, const char* g,
                                        const char* xClient, const char* yServer,
                                        const char* zVerify)
{
    DhKey dh;
    wc_Sha256 sha;
    byte pFlat[FIPS_FFC_FIELD_SZ];
    byte qFlat[FIPS_FFC_ORDER_SZ];
    byte gFlat[FIPS_FFC_FIELD_SZ];
    byte yServerFlat[FIPS_FFC_FIELD_SZ];
    byte xClientFlat[FIPS_FFC_ORDER_SZ];
    byte zVerifyFlat[WC_SHA256_DIGEST_SIZE];
    byte z[FIPS_FFC_FIELD_SZ];
    byte zHash[WC_SHA256_DIGEST_SIZE];
    word32 pFlatSz = sizeof(pFlat);
    word32 qFlatSz = sizeof(qFlat);
    word32 gFlatSz = sizeof(gFlat);
    word32 yServerFlatSz = sizeof(yServerFlat);
    word32 xClientFlatSz = sizeof(xClientFlat);
    word32 zVerifyFlatSz = sizeof(zVerifyFlat);
    word32 zSz = sizeof(z);
    int ret;

    ret = ConvertHexToBin(yServer, yServerFlat, &yServerFlatSz,
                          xClient, xClientFlat, &xClientFlatSz,
                          zVerify, zVerifyFlat, &zVerifyFlatSz,
                          NULL, NULL, NULL);
    if (ret != 0)
        return ret;

    ret = ConvertHexToBin(p, pFlat, &pFlatSz, g, gFlat, &gFlatSz,
                          q, qFlat, &qFlatSz, NULL, NULL, NULL);
    if (ret != 0)
        return ret;

    ret = wc_InitDhKey(&dh);
    if (ret != 0) {
        return ret;
    }

    ret = wc_DhSetKey_ex(&dh, pFlat, pFlatSz, gFlat, gFlatSz, qFlat, qFlatSz);
    if (ret != 0) {
        wc_FreeDhKey(&dh);
        return ret;
    }

    ret = wc_DhAgree(&dh, z, &zSz, xClientFlat, xClientFlatSz,
                     yServerFlat, yServerFlatSz);
    if (ret != 0) {
        wc_FreeDhKey(&dh);
        return ret;
    }

    wc_InitSha256(&sha);
    wc_Sha256Update(&sha, z, zSz);
    wc_Sha256Final(&sha, zHash);

    if (XMEMCMP(zHash, zVerifyFlat, zVerifyFlatSz) != 0)
        return -1;

    wc_FreeDhKey(&dh);
    return 0;
}

#endif /* NO_DH */


#if defined(HAVE_ECC) && defined(HAVE_ECC_SIGN) && defined(HAVE_ECC_VERIFY)

static int ECDSA_PairwiseAgreeTest(int type, const char* msg)
{
    ecc_key     ecc;
    WC_RNG      rng;
    byte        msgDigest[FIPS_MAX_DIGEST_SZ];
    byte        msgSigned[(FIPS_ECC_256_SZ+1)*2 + 6];
    word32      msgSz = (word32)XSTRLEN(msg);
    word32      msgDigestSz = 0;
    word32      msgSignedSz = sizeof(msgSigned);
    word32      idx = 0;
    int         verify = 0;
    int         ret;

    ret = wc_ecc_init(&ecc);
    if (ret != 0) {
        return ret;
    }

    ret = wc_EccPrivateKeyDecode(ecc_clikey_der_256, &idx, &ecc,
                                 (word32)sizeof_ecc_clikey_der_256);
    if (ret != 0) {
        wc_ecc_free(&ecc);
        return ret;
    }

    ret = wc_InitRng(&rng);
    if (ret != 0) {
        wc_ecc_free(&ecc);
        return ret;
    }

    switch (type) {
        case WC_SHA256 :
        {
            wc_Sha256 sha256;

            wc_InitSha256(&sha256);
            wc_Sha256Update(&sha256, (const byte*)msg, msgSz);
            wc_Sha256Final(&sha256, msgDigest);
            msgDigestSz = WC_SHA256_DIGEST_SIZE;
            break;
        }

        default:
            wc_ecc_free(&ecc);
            wc_FreeRng(&rng);
            return -1;
    }

    ret = wc_ecc_sign_hash(msgDigest, msgDigestSz, msgSigned, &msgSignedSz,
                           &rng, &ecc);
    if (ret != 0) {
        wc_ecc_free(&ecc);
        wc_FreeRng(&rng);
        return ret;
    }

    ret = wc_ecc_verify_hash(msgSigned, msgSignedSz, msgDigest, msgDigestSz,
                             &verify, &ecc);
    if (ret != 0) {
        wc_ecc_free(&ecc);
        wc_FreeRng(&rng);
        return ret;
    }

    if (verify == 0) {
        wc_ecc_free(&ecc);
        wc_FreeRng(&rng);
        return -1;
    }

    wc_ecc_free(&ecc);
    wc_FreeRng(&rng);

    return 0;
}

#endif /* HAVE_ECC && HAVE_ECC_SIGN && HAVE_ECC_VERIFY */


/* dead simple base16 encoder, 0 on success */
static int GenBase16_Hash(const byte* in, int length, char* out, int outSz)
{
    int i;
    int index = 0;

    if ( (length * 2 + 1) > outSz)
        return -1;

    for (i = 0; i < length; i++) {
        byte a = in[i] >> 4;
        byte b = in[i] & 0x0f;

        if (a > 9)
            a+=7;
        if (b > 9)
            b+=7;

        out[index++] = a + 0x30;
        out[index++] = b + 0x30;
    }
    out[index++] = '\0';

    return 0;
}


/* hmac-sha256 in memory core verify hash, output to pos callback,
 * copy here when changes */
static const char verifyCore[] =
"542F30458624B1C57D6FDDE94A7E28C7A688097F6FB8A7FF647BF418C2D6867A";


#ifdef USE_WINDOWS_API
    #pragma warning(push)
    #pragma warning(disable:4054 4305 4311)
    /* For Windows builds, disable compiler warnings for:
     * - 4305: typecasting pointers into unsigned longs
     * - 4054: typecasting function pointer into char pointer
     * - 4311: typecasting pointer truncation
     */
#endif

/* Do in core memory integrity check, 0 on success */
static int DoInCoreCheck(char* base16_hash, int base16_hashSz)
{
    Hmac     hmac;
    byte     hash[WC_SHA256_DIGEST_SIZE];
    word32   verifySz  = FIPS_IN_CORE_VERIFY_SZ;
    word32   binCoreSz  = FIPS_IN_CORE_KEY_SZ;
    int      ret;

    byte binCoreKey [FIPS_IN_CORE_KEY_SZ];       /* CoreKey bin will be 32 */
    byte binVerify  [FIPS_IN_CORE_VERIFY_SZ];    /* Verify bin will be 32 */

    static const char coreKey[] =
             "EAD92D38850B03D7160EA4F5C90EDD49C0B6933FAA4833213ED6F0F1596E356B";

    fips_address_function first = wolfCrypt_FIPS_first;
    fips_address_function last  = wolfCrypt_FIPS_last;

    char* start = (char*)wolfCrypt_FIPS_ro_start;
    char* end   = (char*)wolfCrypt_FIPS_ro_end;

    unsigned long code_sz = (unsigned long)last - (unsigned long)first;
    unsigned long data_sz = (unsigned long)end - (unsigned long)start;

    if (data_sz == 0 || data_sz > MAX_FIPS_DATA_SZ)
        return -1;  /* bad fips data size */

    if (code_sz == 0 || code_sz > MAX_FIPS_CODE_SZ)
        return -1;  /* bad fips code size */

    ret = ConvertHexToBin(coreKey, binCoreKey, &binCoreSz,
                          NULL, NULL, NULL,
                          NULL, NULL, NULL,
                          NULL, NULL, NULL);
    if (ret != 0) return ret;

    HmacSetKey_fips(&hmac, WC_SHA256, binCoreKey, binCoreSz);

    HmacUpdate_fips(&hmac, (byte*)first, (word32)code_sz);

    /* don't hash verifyCore or changing verifyCore will change hash */
    if (verifyCore >= start && verifyCore < end) {
        data_sz = (unsigned long)verifyCore - (unsigned long)start;
        HmacUpdate_fips(&hmac, (byte*)start, (word32)data_sz);
        start   = (char*)verifyCore + sizeof(verifyCore);
        data_sz = (unsigned long)end - (unsigned long)start;
    }
    HmacUpdate_fips(&hmac, (byte*)start, (word32)data_sz);

    HmacFinal_fips(&hmac, hash);

    ret = GenBase16_Hash(hash, sizeof(hash), base16_hash, base16_hashSz);
    if (ret != 0)
        return ret;

    ret = ConvertHexToBin(verifyCore, binVerify, &verifySz,
                          NULL, NULL, NULL,
                          NULL, NULL, NULL,
                          NULL, NULL, NULL);
    if (ret != 0)
        return ret;

    if (XMEMCMP(hash, binVerify, sizeof(hash)) != 0) {
        ret = -1;
    }

    return ret;
}

#ifdef USE_WINDOWS_API
    #pragma warning(pop)
#endif


/* do all tests, 0 on success */
int DoKnownAnswerTests(char* base16_hash, int base16_hashSz)
{
    if (DoInCoreCheck(base16_hash, base16_hashSz) != 0) {
        printf("In core integrity check error: hash = %s\n", base16_hash);
        return IN_CORE_FIPS_E;
    }

#if !defined(NO_AES) && !defined(NO_AES_CBC)
    if (AesKnownAnswerTest(
             "2b7e151628aed2a6abf7158809cf4f3c",  /* key */
             "000102030405060708090a0b0c0d0e0f",  /* iv */
             "6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac" /* plainText */
             "9c9eb76fac45af8e5130c81c46a35ce411e5fbc1191a0a"
             "52eff69f2445df4f9b17ad2b417be66c3710",
             "7649abac8119b246cee98e9b12e9197d5086cb9b507219" /* cbc */
             "ee95db113a917678b273bed6b8e3c1743b7116e69e2222"
             "95163ff1caa1681fac09120eca307586e1a7"
             ) != 0) {
        return AES_KAT_FIPS_E;
    }
#endif

#ifdef HAVE_AESGCM
    if (AesGcm_KnownAnswerTest(0,
             "298efa1ccf29cf62ae6824bfc19557fc",                /* key */
             "6f58a93fe1d207fae4ed2f6d",                        /* iv */
             "cc38bccd6bc536ad919b1395f5d63801f99f8068d65ca5ac" /* plain */
             "63872daf16b93901",
             "021fafd238463973ffe80256e5b1c6b1",                /* auth */
             "dfce4e9cd291103d7fe4e63351d9e79d3dfd391e32671046" /* cipher */
             "58212da96521b7db",
             "542465ef599316f73a7a560509a2d9f2"                 /* tag */
             ) != 0) {
        return AESGCM_KAT_FIPS_E;
    }

    if (AesGcm_KnownAnswerTest(1,
             "afa272c03d0343f882008f6e163d6047",                /* key */
             "271ba21f8fdcac34dc93be54",                        /* iv */
             "f3ee01423f192c36033542221c5545dd939de52ada18b9e8" /* plain */
             "b72ba17d02c5dddd",
             "cdf5496a50214683304aec0a80337f9a",                /* auth */
             "36a4029c9e7d0307d31c29cea885bb6c8022452016a29754" /* cipher */
             "ba8a344c5bbfc3e1",
             "ed8d916c171f0688d7e7cca547ab3ab2"                 /* tag */
             ) != 0) {
        return AESGCM_KAT_FIPS_E;
    }
#endif

#ifndef NO_DES3
    if (Des3_KnownAnswerTest(
            "385D7189A5C3D485E1370AA5D408082B5CCCCB5E19F2D90E",  /* key */
            "C141B5FCCD28DC8A",                                  /* iv  */
            "6E1BD7C6120947A464A6AAB293A0F89A563D8D40D3461B68",  /* plain */
            "6235A461AFD312973E3B4F7AA7D23E34E03371F8E8C376C9"   /* cbc */
             ) != 0) {
        return DES3_KAT_FIPS_E;
    }
#endif

#ifndef NO_SHA
    if (HMAC_KnownAnswerTest(WC_SHA,                          /* type */
            "303132333435363738393a3b3c3d3e3f40414243",       /* key */
            "Sample #2",                                      /* msg */
            "0922D3405FAA3D194F82A45830737D5CC6C75D24"        /* digest */
            ) != 0) {
        return HMAC_KAT_FIPS_E;
    }
#endif

#ifdef WOLFSSL_SHA512
    if (HMAC_KnownAnswerTest(WC_SHA512,                       /* type */
            "303132333435363738393a3b3c3d3e3f40414243",       /* key */
            "Sample #2",                                      /* msg */
            "809d44057c5b954105bd041316db0fac44d5a4d5d0892bd04e866412c0907768"
            "f187b77c4fae2c2f21a5b5659a4f4ba74702a3de9b51f145bd4f252742989905"
            /* digest */
            ) != 0) {
        return HMAC_KAT_FIPS_E;
    }
#endif

#ifdef WOLFSSL_SHA3
    if (HMAC_KnownAnswerTest(WC_SHA3_256,                     /* type */
            "302132333435363738393a3b3c3d3e3f"
            "302132333435363738393a3b3c3d3e3f",               /* key */
            "Sample #2",                                      /* msg */
            "1c91ce1a0cbf7501f432a8e23a17cd98"
            "3c96c9b5a16742016c179ff73eb8aa83"                /* digest */
            ) != 0) {
        return HMAC_KAT_FIPS_E;
    }
#endif

#ifndef NO_RSA
    if (RsaSignPKCS1v15_KnownAnswerTest(WC_SHA256,            /* type */
            "Everyone gets Friday off.",                      /* msg */
            "8CFA57979578B9D781C7F7EEDD21E962FC45D8B7CCDA68837"
            "D84E8345973856089C025A06F89F77D7C3694C483A6EF6B42"
            "EE69B8C2E01CC113F137F498890752EF6C6094D3819979122"
            "7928ED82D5BB50FB96A754F977D66FE75ABCF70F5D9448352"
            "26D30BF6F62D7B9CAFFA18179C5DABCE58BA497424A5AC8D6"
            "11814B726CF3294D0C238000DC2B775791925CA528F6B4947"
            "D3E4BA1F8CDF4C3E88E1AA2FCDAE461F6DF245DD3C39F980F"
            "D0FEC213FCB7B7D1679F4689D08538E16A8E0F357BADFD1F0"
            "D56C635B9E6E7CBD6E2F32F347AB9E07685166016EEF8F857"
            "37542185635688469BC08AF743B02B5C6FB5CED8924B20C14"
            "7B9F349FAA1943DBF677CA"
            /* signature */
            ) != 0) {
        return RSA_KAT_FIPS_E;
    }
#endif

#ifdef HAVE_HASHDRBG
    if (DRBG_KnownAnswerTest(0,
            "a65ad0f345db4e0effe875c3a2e71f42"
            "c7129d620ff5c119a9ef55f05185e0fb"
            "8581f9317517276e06e9607ddbcbcc2e", /* entropy + nonce input */
            NULL,                               /* no reseed */
            "d3e160c35b99f340b2628264d1751060"
            "e0045da383ff57a57d73a673d2b8d80d"
            "aaf6a6c35a91bb4579d73fd0c8fed111"
            "b0391306828adfed528f018121b3febd"
            "c343e797b87dbb63db1333ded9d1ece1"
            "77cfa6b71fe8ab1da46624ed6415e51c"
            "cde2c7ca86e283990eeaeb9112041552"
            "8b2295910281b02dd431f4c9f70427df"  /* pseudorandom output */
            ) != 0) {
        return DRBG_KAT_FIPS_E;
    }

    if (DRBG_KnownAnswerTest(1,
            "63363377e41e86468deb0ab4a8ed683f"
            "6a134e47e014c700454e81e95358a569"
            "808aa38f2a72a62359915a9f8a04ca68", /* entropy + nonce input */
            "e62b8a8ee8f141b6980566e3bfe3c049"
            "03dad4ac2cdf9f2280010a6739bc83d3", /* reseed entropy input */
            "04eec63bb231df2c630a1afbe724949d"
            "005a587851e1aa795e477347c8b05662"
            "1c18bddcdd8d99fc5fc2b92053d8cfac"
            "fb0bb8831205fad1ddd6c071318a6018"
            "f03b73f5ede4d4d071f9de03fd7aea10"
            "5d9299b8af99aa075bdb4db9aa28c18d"
            "174b56ee2a014d098896ff2282c955a8"
            "1969e069fa8ce007a180183a07dfae17"  /* pseudorandom output */
            ) != 0) {
        return DRBG_KAT_FIPS_E;
    }
#endif

#ifdef HAVE_ECC_CDH
    if (ECC_CDH_KnownAnswerTest(
                /* ax */
        "700c48f77f56584c5cc632ca65640db91b6bacce3a4df6b42ce7cc838833d287",
                /* ay */
        "db71e509e3fd9b060ddb20ba5c51dcc5948d46fbf640dfe0441782cab85fa4ac",
                /* d */
        "7d7dc5f71eb29ddaf80d6214632eeae03d9058af1fb6d22ed80badb62bc1a534",
                /* ix */
        "ead218590119e8876b29146ff89ca61770c4edbbf97d38ce385ed281d8a6b230",
                /* iy */
        "28af61281fd35e2fa7002523acc85a429cb06ee6648325389f59edfce1405141",
                /* z */
        "46fc62106420ff012e54a434fbdd2d25ccc5852060561e68040dd7778997bd7b"
            ) != 0) {
        return ECC_CDH_KAT_FIPS_E;
    }
#endif

#ifdef HAVE_ECC_DHE
    if (EccPrimitiveZ_KnownAnswerTest(
            /* qexServer */
            "a2f5af030e280c76512f4591c200a3aac5b3f464fe7b598b2677af1df90f7c16",
            /* qeyServer */
            "0052d0fcf017d89126e51c837705826c6b954cf3ce4513706ab3cd1cf69287f7",
            /* qexClient */
            "6483453e74522854c940d9817e464f846975aeddbde3742e46ff10110178b5d4",
            /* qeyClient */
            "e3a66b3758279713ff594f485e9f7e0c34215090575ac4b4595ebaa301bda0b3",
            /* deClient */
            "02697f40772eb4bc12dd43436b0f8c9f5852e8df1e994f5857e18ef26e78d8e0",
            /* zVerify */
            "322f2e5a51d78300e5ec692e7c592a25e65c960f76de8729ee0b678dc9d0e99e"
            ) != 0) {
        return ECDHE_KAT_FIPS_E;
    }
#endif

#ifndef NO_DH
    if (DhPrimitiveZ_KnownAnswerTest(
            /* p */
            "c7a528b2747cd4080d5da193285ef3eddf7bea8be391df9503c9f6a73372f6ee"
            "4e8b2cc0577bf7f8366a29b59286be32e1a13e60bea187e654b6c71268e39c97"
            "3ff220e4a8545cef5a85980d1c9687193faac4355370dee4a37acfc3a29c3e1c"
            "82faad94a2afc004ea1861fde4a9c25950a85264eb87175d047af23ad048d840"
            "50f8f0ea071672a6d210b545656c0556e94d2b4ab0b739eaf4d6c2d8d09c464f"
            "8d6afc1a8283ef3a6227d87ab6fef5e6208645a468bbba478d4b84dedb398689"
            "15e28317a7111ee75c028fe2ecfcf92453b89ff7d8c860e875b266d4455c2ac2"
            "626b6a748af0597ca9907405981d4e9af12451dad23a46f4219da89cc5be7453",
            /* q */
            "bc611c3b67b20c469972651de49b3b879d624d72ea41951615a04cc5b7f04a1f",
            /* g */
            "2fa3f79bb9cfb3fbaa4b19b8c0b5fb1e791da1c3426fb33c979ad2fcde6f984c"
            "c1578fb79125b646694ef937e2a4b1c45ff1ecb7847d4e2cc5761fa483116a9c"
            "cf628aa9c71c15cb37547ec1bd64930fb9a7569e90219b2d6ed82ad2cfee8b04"
            "4aefb475dfd0f89acb690b5021d7cacba9cbdcb517416bdbade00003dd9ea18d"
            "310e9c5734f8508ca57eb523b84b199600c130ce7bd0ab2f3dc151c10301fefc"
            "11bcd7f4fc628a84e58e4b34eb9e17406cfece2db09d7966b76582a13b31ebd7"
            "fd51bf57495144598300c9c1dc2f69237aba4e0d6d6aee1bdff125f5fee62735"
            "6759ba8c2f64dbef44565dde7875362b8e681cdf63aa2add4fa83b0a7509c3cc",
            /* xClient */
            "5b359fb62eea923b26727316a2a54126bd89a5b5015be6ac1b294ffaf180d1cb",
            /* yServer */
            "b503c9e08cf1461540eed4d794a8dc103fa47c3e1689cc3145b8f9bdeb1df99b"
            "d029f4431ce36b5854c7e16b8d076cf58023f7696fad93789a730a8b42d11345"
            "0903cea3555a39b3c1a9756dcd22915e5bb2ac62e4607f0c455da951b43135db"
            "37e171ddb4da8ae671a90f1bd288d634d4f18481d25c139d44672bbef0245928"
            "a9a78d1f5d28665eed690acdf0e06a82a3e4fdb9776a2705248f10ac638f6525"
            "03fd69d73ed46b4d0e47beb738d90913a48840d4a05f059aee4050572d6432c0"
            "a4a50e455d2b92195eadb7193c96f31e89d469b16ef9b5ddef006102652a90cd"
            "1d6d29f366f88321eb6ce0bdf6c567b302670df28ad42424dc8475a6b0153826",
            /* zVerify */
            "288cc3c9b62c6af7ae8ceaa61c1ebe3de7fe8040928b7154428fa3a08e148b27"
            ) != 0) {
        return DH_KAT_FIPS_E;
    }
#endif

#ifdef HAVE_ECC
    if (ECDSA_PairwiseAgreeTest(WC_SHA256, "Everyone gets Friday off.") != 0) {
        return ECDSA_PAT_FIPS_E;
    }
#endif

    return 0;  /* success */
}


#endif /* HAVE_FIPS */
