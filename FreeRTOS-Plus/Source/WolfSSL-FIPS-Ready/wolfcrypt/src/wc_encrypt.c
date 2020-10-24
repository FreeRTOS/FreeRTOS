/* wc_encrypt.c
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

#include <wolfssl/wolfcrypt/settings.h>
#include <wolfssl/wolfcrypt/aes.h>
#include <wolfssl/wolfcrypt/des3.h>
#include <wolfssl/wolfcrypt/hash.h>
#include <wolfssl/wolfcrypt/arc4.h>
#include <wolfssl/wolfcrypt/wc_encrypt.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/asn.h>
#include <wolfssl/wolfcrypt/coding.h>
#include <wolfssl/wolfcrypt/pwdbased.h>
#include <wolfssl/wolfcrypt/logging.h>

#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

#if !defined(NO_AES) && defined(HAVE_AES_CBC)
#ifdef HAVE_AES_DECRYPT
int wc_AesCbcDecryptWithKey(byte* out, const byte* in, word32 inSz,
                                  const byte* key, word32 keySz, const byte* iv)
{
    int  ret = 0;
#ifdef WOLFSSL_SMALL_STACK
    Aes* aes = NULL;
#else
    Aes  aes[1];
#endif

    if (out == NULL || in == NULL || key == NULL || iv == NULL) {
        return BAD_FUNC_ARG;
    }

#ifdef WOLFSSL_SMALL_STACK
    aes = (Aes*)XMALLOC(sizeof(Aes), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (aes == NULL)
        return MEMORY_E;
#endif

    ret = wc_AesInit(aes, NULL, INVALID_DEVID);
    if (ret == 0) {
        ret = wc_AesSetKey(aes, key, keySz, iv, AES_DECRYPTION);
        if (ret == 0)
            ret = wc_AesCbcDecrypt(aes, out, in, inSz);

        wc_AesFree(aes);
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(aes, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}
#endif /* HAVE_AES_DECRYPT */

int wc_AesCbcEncryptWithKey(byte* out, const byte* in, word32 inSz,
                            const byte* key, word32 keySz, const byte* iv)
{
    int  ret = 0;
#ifdef WOLFSSL_SMALL_STACK
    Aes* aes;
#else
    Aes  aes[1];
#endif

#ifdef WOLFSSL_SMALL_STACK
    aes = (Aes*)XMALLOC(sizeof(Aes), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (aes == NULL)
        return MEMORY_E;
#endif

    ret = wc_AesInit(aes, NULL, INVALID_DEVID);
    if (ret == 0) {
        ret = wc_AesSetKey(aes, key, keySz, iv, AES_ENCRYPTION);
        if (ret == 0)
            ret = wc_AesCbcEncrypt(aes, out, in, inSz);

        wc_AesFree(aes);
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(aes, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}
#endif /* !NO_AES && HAVE_AES_CBC */


#if !defined(NO_DES3) && !defined(WOLFSSL_TI_CRYPT)
int wc_Des_CbcEncryptWithKey(byte* out, const byte* in, word32 sz,
                             const byte* key, const byte* iv)
{
    int ret  = 0;
#ifdef WOLFSSL_SMALL_STACK
    Des* des;
#else
    Des  des[1];
#endif

#ifdef WOLFSSL_SMALL_STACK
    des = (Des*)XMALLOC(sizeof(Des), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (des == NULL)
        return MEMORY_E;
#endif

    ret = wc_Des_SetKey(des, key, iv, DES_ENCRYPTION);
    if (ret == 0)
        ret = wc_Des_CbcEncrypt(des, out, in, sz);

#ifdef WOLFSSL_SMALL_STACK
    XFREE(des, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

int wc_Des_CbcDecryptWithKey(byte* out, const byte* in, word32 sz,
                             const byte* key, const byte* iv)
{
    int ret  = 0;
#ifdef WOLFSSL_SMALL_STACK
    Des* des;
#else
    Des  des[1];
#endif

#ifdef WOLFSSL_SMALL_STACK
    des = (Des*)XMALLOC(sizeof(Des), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (des == NULL)
        return MEMORY_E;
#endif

    ret = wc_Des_SetKey(des, key, iv, DES_DECRYPTION);
    if (ret == 0)
        ret = wc_Des_CbcDecrypt(des, out, in, sz);

#ifdef WOLFSSL_SMALL_STACK
    XFREE(des, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}


int wc_Des3_CbcEncryptWithKey(byte* out, const byte* in, word32 sz,
                              const byte* key, const byte* iv)
{
    int ret    = 0;
#ifdef WOLFSSL_SMALL_STACK
    Des3* des3;
#else
    Des3  des3[1];
#endif

#ifdef WOLFSSL_SMALL_STACK
    des3 = (Des3*)XMALLOC(sizeof(Des3), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (des3 == NULL)
        return MEMORY_E;
#endif

    ret = wc_Des3Init(des3, NULL, INVALID_DEVID);
    if (ret == 0) {
        ret = wc_Des3_SetKey(des3, key, iv, DES_ENCRYPTION);
        if (ret == 0)
            ret = wc_Des3_CbcEncrypt(des3, out, in, sz);
        wc_Des3Free(des3);
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(des3, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}


int wc_Des3_CbcDecryptWithKey(byte* out, const byte* in, word32 sz,
                              const byte* key, const byte* iv)
{
    int ret    = 0;
#ifdef WOLFSSL_SMALL_STACK
    Des3* des3;
#else
    Des3  des3[1];
#endif

#ifdef WOLFSSL_SMALL_STACK
    des3 = (Des3*)XMALLOC(sizeof(Des3), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (des3 == NULL)
        return MEMORY_E;
#endif

    ret = wc_Des3Init(des3, NULL, INVALID_DEVID);
    if (ret == 0) {
        ret = wc_Des3_SetKey(des3, key, iv, DES_DECRYPTION);
        if (ret == 0)
            ret = wc_Des3_CbcDecrypt(des3, out, in, sz);
        wc_Des3Free(des3);
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(des3, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

#endif /* !NO_DES3 */


#ifdef WOLFSSL_ENCRYPTED_KEYS

int wc_BufferKeyDecrypt(EncryptedInfo* info, byte* der, word32 derSz,
    const byte* password, int passwordSz, int hashType)
{
    int ret = NOT_COMPILED_IN;
#ifdef WOLFSSL_SMALL_STACK
    byte* key      = NULL;
#else
    byte  key[WC_MAX_SYM_KEY_SIZE];
#endif

    (void)derSz;
    (void)passwordSz;
    (void)hashType;

    if (der == NULL || password == NULL || info == NULL || info->keySz == 0) {
        return BAD_FUNC_ARG;
    }

    /* use file's salt for key derivation, hex decode first */
    if (Base16_Decode(info->iv, info->ivSz, info->iv, &info->ivSz) != 0) {
        return BUFFER_E;
    }
    if (info->ivSz < PKCS5_SALT_SZ)
        return BUFFER_E;

#ifdef WOLFSSL_SMALL_STACK
    key = (byte*)XMALLOC(WC_MAX_SYM_KEY_SIZE, NULL, DYNAMIC_TYPE_SYMMETRIC_KEY);
    if (key == NULL) {
        return MEMORY_E;
    }
#endif

    (void)XMEMSET(key, 0, WC_MAX_SYM_KEY_SIZE);

#ifndef NO_PWDBASED
    if ((ret = wc_PBKDF1(key, password, passwordSz, info->iv, PKCS5_SALT_SZ, 1,
                                        info->keySz, hashType)) != 0) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(key, NULL, DYNAMIC_TYPE_SYMMETRIC_KEY);
#endif
        return ret;
    }
#endif

#ifndef NO_DES3
    if (info->cipherType == WC_CIPHER_DES)
        ret = wc_Des_CbcDecryptWithKey(der, der, derSz, key, info->iv);
    if (info->cipherType == WC_CIPHER_DES3)
        ret = wc_Des3_CbcDecryptWithKey(der, der, derSz, key, info->iv);
#endif /* NO_DES3 */
#if !defined(NO_AES) && defined(HAVE_AES_CBC) && defined(HAVE_AES_DECRYPT)
    if (info->cipherType == WC_CIPHER_AES_CBC)
        ret = wc_AesCbcDecryptWithKey(der, der, derSz, key, info->keySz,
            info->iv);
#endif /* !NO_AES && HAVE_AES_CBC && HAVE_AES_DECRYPT */

#ifdef WOLFSSL_SMALL_STACK
    XFREE(key, NULL, DYNAMIC_TYPE_SYMMETRIC_KEY);
#endif

    return ret;
}

int wc_BufferKeyEncrypt(EncryptedInfo* info, byte* der, word32 derSz,
    const byte* password, int passwordSz, int hashType)
{
    int ret = NOT_COMPILED_IN;
#ifdef WOLFSSL_SMALL_STACK
    byte* key      = NULL;
#else
    byte  key[WC_MAX_SYM_KEY_SIZE];
#endif

    (void)derSz;
    (void)passwordSz;
    (void)hashType;

    if (der == NULL || password == NULL || info == NULL || info->keySz == 0 ||
            info->ivSz < PKCS5_SALT_SZ) {
        return BAD_FUNC_ARG;
    }

#ifdef WOLFSSL_SMALL_STACK
    key = (byte*)XMALLOC(WC_MAX_SYM_KEY_SIZE, NULL, DYNAMIC_TYPE_SYMMETRIC_KEY);
    if (key == NULL) {
        return MEMORY_E;
    }
#endif /* WOLFSSL_SMALL_STACK */

    (void)XMEMSET(key, 0, WC_MAX_SYM_KEY_SIZE);

#ifndef NO_PWDBASED
    if ((ret = wc_PBKDF1(key, password, passwordSz, info->iv, PKCS5_SALT_SZ, 1,
                                        info->keySz, hashType)) != 0) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(key, NULL, DYNAMIC_TYPE_SYMMETRIC_KEY);
#endif
        return ret;
    }
#endif

#ifndef NO_DES3
    if (info->cipherType == WC_CIPHER_DES)
        ret = wc_Des_CbcEncryptWithKey(der, der, derSz, key, info->iv);
    if (info->cipherType == WC_CIPHER_DES3)
        ret = wc_Des3_CbcEncryptWithKey(der, der, derSz, key, info->iv);
#endif /* NO_DES3 */
#if !defined(NO_AES) && defined(HAVE_AES_CBC)
    if (info->cipherType == WC_CIPHER_AES_CBC)
        ret = wc_AesCbcEncryptWithKey(der, der, derSz, key, info->keySz,
            info->iv);
#endif /* !NO_AES && HAVE_AES_CBC */

#ifdef WOLFSSL_SMALL_STACK
    XFREE(key, NULL, DYNAMIC_TYPE_SYMMETRIC_KEY);
#endif

    return ret;
}

#endif /* WOLFSSL_ENCRYPTED_KEYS */


#if !defined(NO_PWDBASED) && !defined(NO_ASN)

#if defined(HAVE_PKCS8) || defined(HAVE_PKCS12)
/* Decrypt/Encrypt input in place from parameters based on id
 *
 * returns a negative value on fail case
 */
int wc_CryptKey(const char* password, int passwordSz, byte* salt,
                      int saltSz, int iterations, int id, byte* input,
                      int length, int version, byte* cbcIv, int enc, int shaOid)
{
    int typeH;
    int derivedLen = 0;
    int ret = 0;
#ifdef WOLFSSL_SMALL_STACK
    byte* key;
#else
    byte key[MAX_KEY_SIZE];
#endif

    (void)input;
    (void)length;
    (void)enc;

    WOLFSSL_ENTER("wc_CryptKey");

    switch (id) {
    #ifndef NO_DES3
        #ifndef NO_MD5
        case PBE_MD5_DES:
            typeH = WC_MD5;
            derivedLen = 16;           /* may need iv for v1.5 */
            break;
        #endif
        #ifndef NO_SHA
        case PBE_SHA1_DES:
            typeH = WC_SHA;
            derivedLen = 16;           /* may need iv for v1.5 */
            break;

        case PBE_SHA1_DES3:
            switch(shaOid) {
                case HMAC_SHA256_OID:
                    typeH = WC_SHA256;
                    derivedLen = 32;
                    break;
                default:
                    typeH = WC_SHA;
                    derivedLen = 32;           /* may need iv for v1.5 */
                    break;
            }
        break;
        #endif /* !NO_SHA */
    #endif /* !NO_DES3 */
    #if !defined(NO_SHA) && !defined(NO_RC4)
        case PBE_SHA1_RC4_128:
            typeH = WC_SHA;
            derivedLen = 16;
            break;
    #endif
    #if defined(WOLFSSL_AES_256)
        case PBE_AES256_CBC:
            switch(shaOid) {
                case HMAC_SHA256_OID:
                    typeH = WC_SHA256;
                    derivedLen = 32;
                    break;
            #ifndef NO_SHA
                default:
                    typeH = WC_SHA;
                    derivedLen = 32;
                    break;
            #endif
            }
            break;
    #endif /* WOLFSSL_AES_256 && !NO_SHA */
    #if defined(WOLFSSL_AES_128)
        case PBE_AES128_CBC:
            switch(shaOid) {
                case HMAC_SHA256_OID:
                    typeH = WC_SHA256;
                    derivedLen = 16;
                    break;
            #ifndef NO_SHA
                default:
                    typeH = WC_SHA;
                    derivedLen = 16;
                    break;
            #endif
            }
            break;
    #endif /* WOLFSSL_AES_128 && !NO_SHA */
        default:
            WOLFSSL_MSG("Unknown/Unsupported encrypt/decrypt id");
            (void)shaOid;
            return ALGO_ID_E;
    }

#ifdef WOLFSSL_SMALL_STACK
    key = (byte*)XMALLOC(MAX_KEY_SIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (key == NULL)
        return MEMORY_E;
#endif

    if (version == PKCS5v2)
        ret = wc_PBKDF2(key, (byte*)password, passwordSz,
                        salt, saltSz, iterations, derivedLen, typeH);
#ifndef NO_SHA
    else if (version == PKCS5)
        ret = wc_PBKDF1(key, (byte*)password, passwordSz,
                        salt, saltSz, iterations, derivedLen, typeH);
#endif
#ifdef HAVE_PKCS12
    else if (version == PKCS12v1) {
        int  i, idx = 0;
        byte unicodePasswd[MAX_UNICODE_SZ];

        if ( (passwordSz * 2 + 2) > (int)sizeof(unicodePasswd)) {
#ifdef WOLFSSL_SMALL_STACK
            XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return UNICODE_SIZE_E;
        }

        for (i = 0; i < passwordSz; i++) {
            unicodePasswd[idx++] = 0x00;
            unicodePasswd[idx++] = (byte)password[i];
        }
        /* add trailing NULL */
        unicodePasswd[idx++] = 0x00;
        unicodePasswd[idx++] = 0x00;

        ret =  wc_PKCS12_PBKDF(key, unicodePasswd, idx, salt, saltSz,
                            iterations, derivedLen, typeH, 1);
        if (id != PBE_SHA1_RC4_128)
            ret += wc_PKCS12_PBKDF(cbcIv, unicodePasswd, idx, salt, saltSz,
                                iterations, 8, typeH, 2);
    }
#endif /* HAVE_PKCS12 */
    else {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        WOLFSSL_MSG("Unknown/Unsupported PKCS version");
        return ALGO_ID_E;
    }

    if (ret != 0) {
#ifdef WOLFSSL_SMALL_STACK
        XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
        return ret;
    }

    switch (id) {
#ifndef NO_DES3
    #if !defined(NO_SHA) || !defined(NO_MD5)
        case PBE_MD5_DES:
        case PBE_SHA1_DES:
        {
            Des    des;
            byte*  desIv = key + 8;

            if (version == PKCS5v2 || version == PKCS12v1)
                desIv = cbcIv;

            if (enc) {
                ret = wc_Des_SetKey(&des, key, desIv, DES_ENCRYPTION);
            }
            else {
                ret = wc_Des_SetKey(&des, key, desIv, DES_DECRYPTION);
            }
            if (ret != 0) {
#ifdef WOLFSSL_SMALL_STACK
                XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return ret;
            }

            if (enc) {
                wc_Des_CbcEncrypt(&des, input, input, length);
            }
            else {
                wc_Des_CbcDecrypt(&des, input, input, length);
            }
            break;
        }
    #endif /* !NO_SHA || !NO_MD5 */

    #ifndef NO_SHA
        case PBE_SHA1_DES3:
        {
            Des3   des;
            byte*  desIv = key + 24;

            if (version == PKCS5v2 || version == PKCS12v1)
                desIv = cbcIv;

            ret = wc_Des3Init(&des, NULL, INVALID_DEVID);
            if (ret != 0) {
#ifdef WOLFSSL_SMALL_STACK
                XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return ret;
            }
            if (enc) {
                ret = wc_Des3_SetKey(&des, key, desIv, DES_ENCRYPTION);
            }
            else {
                ret = wc_Des3_SetKey(&des, key, desIv, DES_DECRYPTION);
            }
            if (ret != 0) {
#ifdef WOLFSSL_SMALL_STACK
                XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return ret;
            }
            if (enc) {
                ret = wc_Des3_CbcEncrypt(&des, input, input, length);
            }
            else {
                ret = wc_Des3_CbcDecrypt(&des, input, input, length);
            }
            if (ret != 0) {
#ifdef WOLFSSL_SMALL_STACK
                XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return ret;
            }
            break;
        }
    #endif /* !NO_SHA */
#endif
#if !defined(NO_RC4) && !defined(NO_SHA)
        case PBE_SHA1_RC4_128:
        {
            Arc4    dec;

            wc_Arc4SetKey(&dec, key, derivedLen);
            wc_Arc4Process(&dec, input, input, length);
            break;
        }
#endif
#if !defined(NO_AES) && defined(HAVE_AES_CBC)
    #ifdef WOLFSSL_AES_256
        case PBE_AES256_CBC:
        case PBE_AES128_CBC:
        {
            Aes aes;
            ret = wc_AesInit(&aes, NULL, INVALID_DEVID);
            if (ret == 0) {
                if (enc) {
                    ret = wc_AesSetKey(&aes, key, derivedLen, cbcIv,
                                                                AES_ENCRYPTION);
                }
                else {
                    ret = wc_AesSetKey(&aes, key, derivedLen, cbcIv,
                                                                AES_DECRYPTION);
                }
            }
            if (ret == 0) {
                if (enc)
                    ret = wc_AesCbcEncrypt(&aes, input, input, length);
                else
                    ret = wc_AesCbcDecrypt(&aes, input, input, length);
            }
            if (ret != 0) {
#ifdef WOLFSSL_SMALL_STACK
                XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
                return ret;
            }
            ForceZero(&aes, sizeof(Aes));
            break;
        }
    #endif /* WOLFSSL_AES_256 */
#endif /* !NO_AES && HAVE_AES_CBC */

        default:
#ifdef WOLFSSL_SMALL_STACK
            XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            WOLFSSL_MSG("Unknown/Unsupported encrypt/decryption algorithm");
            return ALGO_ID_E;
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(key, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

#endif /* HAVE_PKCS8 || HAVE_PKCS12 */
#endif /* !NO_PWDBASED */
