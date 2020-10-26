/* fips.h
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



#ifndef WOLF_CRYPT_FIPS_H
#define WOLF_CRYPT_FIPS_H


#include <wolfssl/wolfcrypt/types.h>


#ifdef __cplusplus
    extern "C" {
#endif


/* Forward declaractions. */
enum wc_HashType;


WOLFSSL_API const char* wolfCrypt_GetVersion_fips(void);


/* Hash_DRBG API */
#ifdef HAVE_HASHDRBG

#ifdef FIPS_NO_WRAPPERS
    #ifndef WC_RNG_TYPE_DEFINED
        typedef struct WC_RNG WC_RNG;
        #define WC_RNG_TYPE_DEFINED
    #endif

    WOLFSSL_API int InitRng_fips(WC_RNG*);
    WOLFSSL_API int InitRngNonce_fips(WC_RNG*, byte*, word32);
    WOLFSSL_API int FreeRng_fips(WC_RNG*);
    WOLFSSL_API int RNG_GenerateBlock_fips(WC_RNG*, byte*, word32);
    WOLFSSL_API int RNG_HealthTest_fips(int, const byte*, word32,
                                        const byte*, word32, byte*, word32);

#else /* FIPS_NO_WRAPPERS */
    /* if not impl or fips.c impl wrapper force fips calls if fips build */
    #define wc_InitRng                  InitRng_fips
    #define wc_InitRngNonce             InitRngNonce_fips
    #define wc_FreeRng                  FreeRng_fips
    #define wc_RNG_GenerateBlock        RNG_GenerateBlock_fips
    #define wc_RNG_HealthTest           RNG_HealthTest_fips
#endif /* FIPS_NO_WRAPPERS */

#endif /* HAVE_HASHDRBG */


/* AES API */
#ifndef NO_AES

#ifdef FIPS_NO_WRAPPERS
    #ifndef WC_AES_TYPE_DEFINED
        typedef struct Aes Aes;
        #define WC_AES_TYPE_DEFINED
    #endif

    WOLFSSL_API int AesSetKey_fips(Aes*, const byte*, word32, const byte*, int);
    WOLFSSL_API int AesSetIV_fips(Aes*, const byte*);
    WOLFSSL_API int AesEcbEncrypt_fips(Aes*, byte*, const byte*, word32);
    WOLFSSL_API int AesEcbDecrypt_fips(Aes*, byte*, const byte*, word32);
    WOLFSSL_API int AesCbcEncrypt_fips(Aes*, byte*, const byte*, word32);
    WOLFSSL_API int AesCbcDecrypt_fips(Aes*, byte*, const byte*, word32);
    WOLFSSL_API int AesCtrEncrypt_fips(Aes*, byte*, const byte*, word32);
    WOLFSSL_API int AesGcmSetKey_fips(Aes*, const byte*, word32);
    WOLFSSL_API int AesGcmSetExtIV_fips(Aes*, const byte*, word32);
    WOLFSSL_API int AesGcmSetIV_fips(Aes*, word32, const byte*, word32,
                            WC_RNG*);
    WOLFSSL_API int AesGcmEncrypt_fips(Aes*, byte*, const byte*, word32,
                            byte*, word32, byte*, word32, const byte*, word32);
    WOLFSSL_API int AesGcmDecrypt_fips(Aes*, byte*, const byte*, word32,
                            const byte*, word32, const byte*, word32,
                            const byte*, word32);
    WOLFSSL_API int Gmac_fips(const byte*, word32, byte*, word32,
                            const byte*, word32, byte*, word32, WC_RNG*);
    WOLFSSL_API int GmacVerify_fips(const byte*, word32, const byte*, word32,
                            const byte*, word32, const byte*, word32);
    WOLFSSL_API int AesCcmSetKey_fips(Aes*, const byte*, word32);
    WOLFSSL_API int AesCcmSetNonce_fips(Aes*, const byte*, word32);
    WOLFSSL_API int AesCcmEncrypt_fips(Aes*, byte*, const byte*, word32,
                            byte*, word32, byte*, word32, const byte*, word32);
    WOLFSSL_API int AesCcmDecrypt_fips(Aes*, byte*, const byte*, word32,
                            const byte*, word32, const byte*, word32,
                            const byte*, word32);

#else /* NO_FIPS_WRAPPERS */
    /* if not impl or fips.c impl wrapper force fips calls if fips build */
    #define wc_AesSetKey               AesSetKey_fips
    #define wc_AesSetIV                AesSetIV_fips
    #define wc_AesEcbEncrypt           AesEcbEncrypt_fips
    #define wc_AesEcbDecrypt           AesEcbDecrypt_fips
    #define wc_AesCbcEncrypt           AesCbcEncrypt_fips
    #define wc_AesCbcDecrypt           AesCbcDecrypt_fips
    #define wc_AesCtrEncrypt           AesCtrEncrypt_fips
    #define wc_AesGcmSetKey            AesGcmSetKey_fips
    #define wc_AesGcmSetExtIV          AesGcmSetExtIV_fips
    #define wc_AesGcmSetIV             AesGcmSetIV_fips
    #define wc_AesGcmEncrypt_ex        AesGcmEncrypt_fips
    #define wc_AesGcmDecrypt           AesGcmDecrypt_fips
    #define wc_AesCcmSetKey            AesCcmSetKey_fips
    #define wc_AesCcmSetNonce          AesCcmSetNonce_fips
    #define wc_AesCcmEncrypt_ex        AesCcmEncrypt_fips
    #define wc_AesCcmDecrypt           AesCcmDecrypt_fips
#endif /* NO_FIPS_WRAPPERS */

#endif /* NO_AES */


/* DES3 API */
#ifndef NO_DES3

#ifdef FIPS_NO_WRAPPERS
    #ifndef WC_DES3_TYPE_DEFINED
        typedef struct Des3 Des3;
        #define WC_DES3_TYPE_DEFINED
    #endif

    WOLFSSL_API int Des3_SetKey_fips(Des3*, const byte*, const byte*, int);
    WOLFSSL_API int Des3_SetIV_fips(Des3*, const byte*);
    WOLFSSL_API int Des3_CbcEncrypt_fips(Des3*, byte*, const byte*, word32);
    WOLFSSL_API int Des3_CbcDecrypt_fips(Des3*, byte*, const byte*, word32);

#else /* NO_FIPS_WRAPPERS */
    /* if not impl or fips.c impl wrapper force fips calls if fips build */
    #define wc_Des3_SetKey             Des3_SetKey_fips
    #define wc_Des3_SetIV              Des3_SetIV_fips
    #define wc_Des3_CbcEncrypt         Des3_CbcEncrypt_fips
    #define wc_Des3_CbcDecrypt         Des3_CbcDecrypt_fips
#endif /* NO_FIPS_WRAPPERS */

#endif /* NO_DES3 */


/* RSA API */
#ifndef NO_RSA

#ifdef FIPS_NO_WRAPPERS
    #ifndef WC_RSAKEY_TYPE_DEFINED
        typedef struct RsaKey RsaKey;
        #define WC_RSAKEY_TYPE_DEFINED
    #endif

    WOLFSSL_API int InitRsaKey_fips(RsaKey*, void*);
    WOLFSSL_API int InitRsaKeyEx_fips(RsaKey*, void*, int);
    WOLFSSL_API int FreeRsaKey_fips(RsaKey*);
    WOLFSSL_API int CheckRsaKey_fips(RsaKey*);
    WOLFSSL_API int RsaPublicEncrypt_fips(const byte*, word32, byte*, word32,
                            RsaKey*, WC_RNG*);
    WOLFSSL_API int RsaPublicEncryptEx_fips(const byte*, word32, byte*, word32,
                            RsaKey*, WC_RNG*, int, enum wc_HashType, int,
                            byte*, word32);
    WOLFSSL_API int RsaPrivateDecryptInline_fips(byte*, word32, byte**,
                            RsaKey*);
    WOLFSSL_API int RsaPrivateDecryptInlineEx_fips(byte*, word32, byte**,
                            RsaKey*, int, enum wc_HashType, int, byte*, word32);
    WOLFSSL_API int RsaPrivateDecrypt_fips(const byte*, word32, byte*, word32,
                            RsaKey*);
    WOLFSSL_API int RsaPrivateDecryptEx_fips(const byte*, word32, byte*, word32,
                            RsaKey*, int, enum wc_HashType, int, byte*, word32);
    WOLFSSL_API int RsaSSL_Sign_fips(const byte*, word32, byte*, word32,
                            RsaKey*, WC_RNG*);
    WOLFSSL_API int RsaSSL_VerifyInline_fips(byte*, word32, byte**, RsaKey*);
    WOLFSSL_API int RsaSSL_Verify_fips(const byte*, word32, byte*, word32,
                            RsaKey*);
    WOLFSSL_API int RsaPSS_Sign_fips(const byte*, word32, byte*, word32,
                            enum wc_HashType, int, RsaKey*, WC_RNG*);
    WOLFSSL_API int RsaPSS_SignEx_fips(const byte*, word32, byte*, word32,
                            enum wc_HashType, int, int, RsaKey*, WC_RNG*);
    WOLFSSL_API int RsaPSS_VerifyInline_fips(byte*, word32, byte**,
                            enum wc_HashType, int, RsaKey*);
    WOLFSSL_API int RsaPSS_VerifyInlineEx_fips(byte*, word32, byte**,
                            enum wc_HashType, int, int, RsaKey*);
    WOLFSSL_API int RsaPSS_Verify_fips(byte*, word32, byte*, word32,
                            enum wc_HashType, int, RsaKey*);
    WOLFSSL_API int RsaPSS_VerifyEx_fips(byte*, word32, byte*, word32,
                            enum wc_HashType, int, int, RsaKey*);
    WOLFSSL_API int RsaPSS_CheckPadding_fips(const byte*, word32, byte*, word32,
                            enum wc_HashType);
    WOLFSSL_API int RsaPSS_CheckPaddingEx_fips(const byte*, word32, byte*,
                            word32, enum wc_HashType, int, int);
    WOLFSSL_API int RsaEncryptSize_fips(RsaKey*);
    WOLFSSL_API int RsaExportKey_fips(RsaKey*, byte*, word32*, byte*, word32*,
                            byte*, word32*, byte*, word32*, byte*, word32*);
    WOLFSSL_API int CheckProbablePrime_fips(const byte*, word32, const byte*,
                            word32, const byte*, word32, int, int*);
    WOLFSSL_API int MakeRsaKey_fips(RsaKey*, int, long, WC_RNG*);

#else /* FIPS_NO_WRAPPERS */
    /* if not impl or fips.c impl wrapper force fips calls if fips build */
    #define wc_InitRsaKey              InitRsaKey_fips
    #define wc_InitRsaKey_ex           InitRsaKeyEx_fips
    #define wc_FreeRsaKey              FreeRsaKey_fips
    #define wc_CheckRsaKey             CheckRsaKey_fips
    #define wc_RsaPublicEncrypt        RsaPublicEncrypt_fips
    #define wc_RsaPublicEncrypt_ex     RsaPublicEncryptEx_fips
    #define wc_RsaPrivateDecryptInline RsaPrivateDecryptInline_fips
    #define wc_RsaPrivateDecryptInline_ex RsaPrivateDecryptInlineEx_fips
    #define wc_RsaPrivateDecrypt       RsaPrivateDecrypt_fips
    #define wc_RsaPrivateDecrypt_ex    RsaPrivateDecryptEx_fips
    #define wc_RsaSSL_Sign             RsaSSL_Sign_fips
    #define wc_RsaSSL_VerifyInline     RsaSSL_VerifyInline_fips
    #define wc_RsaSSL_Verify           RsaSSL_Verify_fips
    #define wc_RsaPSS_Sign             RsaPSS_Sign_fips
    #define wc_RsaPSS_Sign_ex          RsaPSS_SignEx_fips
    #define wc_RsaPSS_VerifyInline     RsaPSS_VerifyInline_fips
    #define wc_RsaPSS_VerifyInline_ex  RsaPSS_VerifyInlineEx_fips
    #define wc_RsaPSS_Verify           RsaPSS_Verify_fips
    #define wc_RsaPSS_Verify_ex        RsaPSS_VerifyEx_fips
    #define wc_RsaPSS_CheckPadding     RsaPSS_CheckPadding_fips
    #define wc_RsaPSS_CheckPadding_ex  RsaPSS_CheckPaddingEx_fips
    #define wc_RsaEncryptSize          RsaEncryptSize_fips
    #define wc_RsaExportKey            RsaExportKey_fips
    #define wc_CheckProbablePrime      CheckProbablePrime_fips
    #define wc_MakeRsaKey              MakeRsaKey_fips
#endif /* FIPS_NO_WRAPPERS */

#endif /* NO_RSA */


/* ECC API */
#ifdef HAVE_ECC

#ifdef FIPS_NO_WRAPPERS
    #ifndef WC_ECCKEY_TYPE_DEFINED
        typedef struct ecc_key ecc_key;
        #define WC_ECCKEY_TYPE_DEFINED
    #endif

    WOLFSSL_API int ecc_init_fips(ecc_key*);
    WOLFSSL_API int ecc_free_fips(ecc_key*);
    WOLFSSL_API int ecc_check_key_fips(ecc_key*);
    WOLFSSL_API int ecc_make_key_fips(WC_RNG*, int, ecc_key*);
    WOLFSSL_API int ecc_make_key_ex_fips(WC_RNG*, int, ecc_key*, int);
    WOLFSSL_API int ecc_export_x963_fips(ecc_key*, byte*, word32*);
    WOLFSSL_API int ecc_import_x963_fips(const byte*, word32, ecc_key*);
    WOLFSSL_API int ecc_shared_secret_fips(ecc_key*, ecc_key*, byte*, word32*);
    WOLFSSL_API int ecc_sign_hash_fips(const byte*, word32, byte*, word32*,
                            WC_RNG* rng, ecc_key* key);
    WOLFSSL_API int ecc_verify_hash_fips(const byte*, word32, const byte*,
                            word32, int*, ecc_key*);

#else /* FIPS_NO_WRAPPERS */
    /* if not impl or fips.c impl wrapper force fips calls if fips build */
    #define wc_ecc_init                 ecc_init_fips
    #define wc_ecc_free                 ecc_free_fips
    #define wc_ecc_check_key            ecc_check_key_fips
    #define wc_ecc_make_key             ecc_make_key_fips
    #define wc_ecc_make_key_ex          ecc_make_key_ex_fips
    #define wc_ecc_export_x963          ecc_export_x963_fips
    #define wc_ecc_import_x963          ecc_import_x963_fips
    #define wc_ecc_shared_secret        ecc_shared_secret_fips
    #define wc_ecc_sign_hash            ecc_sign_hash_fips
    #define wc_ecc_verify_hash          ecc_verify_hash_fips
#endif /* FIPS_NO_WRAPPERS */

#endif /* HAVE_ECC */


/* DH API */
#ifndef NO_DH

#ifdef FIPS_NO_WRAPPERS
    #ifndef WC_DH_TYPE_DEFINED
        typedef struct DhKey DhKey;
        #define WC_DH_TYPE_DEFINED
    #endif

    WOLFSSL_API int InitDhKey_fips(DhKey*);
    WOLFSSL_API int FreeDhKey_fips(DhKey*);
    WOLFSSL_API int DhSetKeyEx_fips(DhKey*, const byte*, word32,
                            const byte*, word32, const byte*, word32);
    WOLFSSL_API int DhGenerateKeyPair_fips(DhKey*, WC_RNG*, byte*, word32*,
                            byte*, word32*);
    WOLFSSL_API int DhCheckPubKeyEx_fips(DhKey*, const byte*, word32,
                            const byte*, word32);
    WOLFSSL_API int DhCheckPrivKeyEx_fips(DhKey*, const byte*, word32,
                            const byte*, word32);
    WOLFSSL_API int DhCheckKeyPair_fips(DhKey*, const byte*, word32,
                            const byte*, word32);
    WOLFSSL_API int DhAgree_fips(DhKey*, byte*, word32*, const byte*, word32,
                            const byte*, word32);

#else /* FIPS_NO_WRAPPERS */
    /* if not impl or fips.c impl wrapper force fips calls if fips build */
    #define wc_InitDhKey                InitDhKey_fips
    #define wc_FreeDhKey                FreeDhKey_fips
    #define wc_DhSetKey_ex              DhSetKeyEx_fips
    #define wc_DhGenerateKeyPair        DhGenerateKeyPair_fips
    #define wc_DhCheckPubKey_ex         DhCheckPubKeyEx_fips
    #define wc_DhCheckPrivKey_ex        DhCheckPrivKeyEx_fips
    #define wc_DhCheckKeyPair           DhCheckKeyPair_fips
    #define wc_DhAgree                  DhAgree_fips
#endif /* FIPS_NO_WRAPPERS */

#endif /* NO_DH */


/* SHA-1 API */
#ifndef NO_SHA

#ifdef FIPS_NO_WRAPPERS
    #ifndef WC_SHA_TYPE_DEFINED
        typedef struct wc_Sha wc_Sha;
        #define WC_SHA_TYPE_DEFINED
    #endif

    WOLFSSL_API int InitSha_fips(wc_Sha*);
    WOLFSSL_API int ShaUpdate_fips(wc_Sha*, const byte*, word32);
    WOLFSSL_API int ShaFinal_fips(wc_Sha*, byte*);

#else /* FIPS_NO_WRAPPERS */
    /* if not impl or fips.c impl wrapper force fips calls if fips build */
    #define wc_InitSha                  InitSha_fips
    #define wc_ShaUpdate                ShaUpdate_fips
    #define wc_ShaFinal                 ShaFinal_fips
#endif /* FIPS_NO_WRAPPERS */

#endif /* NO_SHA */


/* SHA-224 and SHA-256 API */
#ifndef NO_SHA256

#ifdef FIPS_NO_WRAPPERS
    #ifndef WC_SHA256_TYPE_DEFINED
        typedef struct wc_Sha256 wc_Sha256;
        #define WC_SHA256_TYPE_DEFINED
    #endif

    WOLFSSL_API int InitSha256_fips(wc_Sha256*);
    WOLFSSL_API int Sha256Update_fips(wc_Sha256*, const byte*, word32);
    WOLFSSL_API int Sha256Final_fips(wc_Sha256*, byte*);

    #ifdef WOLFSSL_SHA224
		#ifndef WC_SHA224_TYPE_DEFINED
			typedef struct wc_Sha256 wc_Sha224;
			#define WC_SHA224_TYPE_DEFINED
		#endif

        WOLFSSL_API int InitSha224_fips(wc_Sha224*);
        WOLFSSL_API int Sha224Update_fips(wc_Sha224*, const byte*, word32);
        WOLFSSL_API int Sha224Final_fips(wc_Sha224*, byte*);
    #endif /* WOLFSSL_SHA224 */

#else /* FIPS_NO_WRAPPERS */
    /* if not impl or fips.c impl wrapper force fips calls if fips build */
    #define wc_InitSha256               InitSha256_fips
    #define wc_Sha256Update             Sha256Update_fips
    #define wc_Sha256Final              Sha256Final_fips
    #ifdef WOLFSSL_SHA224
        #define wc_InitSha224           InitSha224_fips
        #define wc_Sha224Update         Sha224Update_fips
        #define wc_Sha224Final          Sha224Final_fips
    #endif /* WOLFSSL_SHA224 */
#endif /* FIPS_NO_WRAPPERS */

#endif /* NO_SHA256 */


/* SHA-384 and SHA-512 API */
#ifndef NO_SHA512

#ifdef FIPS_NO_WRAPPERS
    #ifndef WC_SHA512_TYPE_DEFINED
        typedef struct wc_Sha512 wc_Sha512;
        #define WC_SHA512_TYPE_DEFINED
    #endif

    WOLFSSL_API int InitSha512_fips(wc_Sha512*);
    WOLFSSL_API int Sha512Update_fips(wc_Sha512*, const byte*, word32);
    WOLFSSL_API int Sha512Final_fips(wc_Sha512*, byte*);

    #ifdef WOLFSSL_SHA384
		#ifndef WC_SHA384_TYPE_DEFINED
			typedef struct wc_Sha512 wc_Sha384;
			#define WC_SHA384_TYPE_DEFINED
		#endif
        WOLFSSL_API int InitSha384_fips(wc_Sha384*);
        WOLFSSL_API int Sha384Update_fips(wc_Sha384*, const byte*, word32);
        WOLFSSL_API int Sha384Final_fips(wc_Sha384*, byte*);
    #endif /* WOLFSSL_SHA384 */

#else /* FIPS_NO_WRAPPERS */
    /* if not impl or fips.c impl wrapper force fips calls if fips build */
    #define wc_InitSha512               InitSha512_fips
    #define wc_Sha512Update             Sha512Update_fips
    #define wc_Sha512Final              Sha512Final_fips
    #ifdef WOLFSSL_SHA384
        #define wc_InitSha384           InitSha384_fips
        #define wc_Sha384Update         Sha384Update_fips
        #define wc_Sha384Final          Sha384Final_fips
    #endif /* WOLFSSL_SHA384 */
#endif /* FIPS_NO_WRAPPERS */

#endif /* NO_SHA512 */


/* SHA-3 API */
#ifdef WOLFSSL_SHA3

#ifdef FIPS_NO_WRAPPERS
    #ifndef WC_SHA3_TYPE_DEFINED
        typedef struct wc_Sha3 wc_Sha3;
        #define WC_SHA3_TYPE_DEFINED
    #endif

    WOLFSSL_API int InitSha3_224_fips(wc_Sha3*, void*, int);
    WOLFSSL_API int Sha3_224_Update_fips(wc_Sha3*, const byte*, word32);
    WOLFSSL_API int Sha3_224_Final_fips(wc_Sha3*, byte*);

    WOLFSSL_API int InitSha3_256_fips(wc_Sha3*, void*, int);
    WOLFSSL_API int Sha3_256_Update_fips(wc_Sha3*, const byte*, word32);
    WOLFSSL_API int Sha3_256_Final_fips(wc_Sha3*, byte*);

    WOLFSSL_API int InitSha3_384_fips(wc_Sha3*, void*, int);
    WOLFSSL_API int Sha3_384_Update_fips(wc_Sha3*, const byte*, word32);
    WOLFSSL_API int Sha3_384_Final_fips(wc_Sha3*, byte*);

    WOLFSSL_API int InitSha3_512_fips(wc_Sha3*, void*, int);
    WOLFSSL_API int Sha3_512_Update_fips(wc_Sha3*, const byte*, word32);
    WOLFSSL_API int Sha3_512_Final_fips(wc_Sha3*, byte*);

#else /* FIPS_NO_WRAPPERS */
    /* if not impl or fips.c impl wrapper force fips calls if fips build */
    #define wc_InitSha3_224             InitSha3_224_fips
    #define wc_Sha3_224_Update          Sha3_224_Update_fips
    #define wc_Sha3_224_Final           Sha3_224_Final_fips
    #define wc_InitSha3_256             InitSha3_256_fips
    #define wc_Sha3_256_Update          Sha3_256_Update_fips
    #define wc_Sha3_256_Final           Sha3_256_Final_fips
    #define wc_InitSha3_384             InitSha3_384_fips
    #define wc_Sha3_384_Update          Sha3_384_Update_fips
    #define wc_Sha3_384_Final           Sha3_384_Final_fips
    #define wc_InitSha3_512             InitSha3_512_fips
    #define wc_Sha3_512_Update          Sha3_512_Update_fips
    #define wc_Sha3_512_Final           Sha3_512_Final_fips
#endif /* FIPS_NO_WRAPPERS */

#endif /* WOLFSSL_SHA3 */


/* HMAC API */
#ifndef NO_HMAC

#ifdef FIPS_NO_WRAPPERS
    #ifndef WC_HMAC_TYPE_DEFINED
        typedef struct Hmac Hmac;
        #define WC_HMAC_TYPE_DEFINED
    #endif

    WOLFSSL_API int HmacSetKey_fips(Hmac*, int, const byte*, word32);
    WOLFSSL_API int HmacUpdate_fips(Hmac*, const byte*, word32);
    WOLFSSL_API int HmacFinal_fips(Hmac*, byte*);
    #ifdef HAVE_HKDF
        WOLFSSL_API int HKDF_fips(int type, const byte* inKey, word32 inKeySz,
                                  const byte* salt, word32 saltSz,
                                  const byte* info, word32 infoSz,
                                  byte* out, word32 outSz);
    #endif /* HAVE_HKDF */

#else /* FIPS_NO_WRAPPERS */
    /* if not impl or fips.c impl wrapper force fips calls if fips build */
    #define wc_HmacSetKey               HmacSetKey_fips
    #define wc_HmacUpdate               HmacUpdate_fips
    #define wc_HmacFinal                HmacFinal_fips
    #ifdef HAVE_HKDF
        #define wc_HKDF                 HKDF_fips
    #endif /* HAVE_HKDF */
#endif /* FIPS_NO_WRAPPERS */

#endif /* NO_HMAC */


/* CMAC API */
#ifdef WOLFSSL_CMAC

#ifdef FIPS_NO_WRAPPERS
    #ifndef WC_CMAC_TYPE_DEFINED
        typedef struct Cmac Cmac;
        #define WC_CMAC_TYPE_DEFINED
    #endif

    WOLFSSL_API int InitCmac_fips(Cmac*, const byte*, word32, int, void*);
    WOLFSSL_API int CmacUpdate_fips(Cmac*, const byte*, word32);
    WOLFSSL_API int CmacFinal_fips(Cmac*, byte*, word32*);

#else /* FIPS_NO_WRAPPERS */
    /* if not impl or fips.c impl wrapper force fips calls if fips build */
    #define wc_InitCmac                 InitCmac_fips
    #define wc_CmacUpdate               CmacUpdate_fips
    #define wc_CmacFinal                CmacFinal_fips
#endif /* FIPS_NO_WRAPPERS */

#endif /* WOLFSSL_CMAC */


#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* WOLF_CRYPT_FIPS_H */

