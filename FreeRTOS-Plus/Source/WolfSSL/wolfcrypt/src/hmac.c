/* hmac.c
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

#ifndef NO_HMAC

#if defined(HAVE_FIPS) && \
    defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2)

    /* set NO_WRAPPERS before headers, use direct internal f()s not wrappers */
    #define FIPS_NO_WRAPPERS

    #ifdef USE_WINDOWS_API
        #pragma code_seg(".fipsA$b")
        #pragma const_seg(".fipsB$b")
    #endif
#endif

#include <wolfssl/wolfcrypt/hmac.h>

#ifdef WOLF_CRYPTO_CB
    #include <wolfssl/wolfcrypt/cryptocb.h>
#endif

#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif


/* fips wrapper calls, user can call direct */
/* If building for old FIPS. */
#if defined(HAVE_FIPS) && \
    (!defined(HAVE_FIPS_VERSION) || (HAVE_FIPS_VERSION < 2))

    /* does init */
    int wc_HmacSetKey(Hmac* hmac, int type, const byte* key, word32 keySz)
    {
        if (hmac == NULL || (key == NULL && keySz != 0) ||
           !(type == WC_MD5 || type == WC_SHA || type == WC_SHA256 ||
                type == WC_SHA384 || type == WC_SHA512)) {
            return BAD_FUNC_ARG;
        }

        return HmacSetKey_fips(hmac, type, key, keySz);
    }
    int wc_HmacUpdate(Hmac* hmac, const byte* in, word32 sz)
    {
        if (hmac == NULL || (in == NULL && sz > 0)) {
            return BAD_FUNC_ARG;
        }

        return HmacUpdate_fips(hmac, in, sz);
    }
    int wc_HmacFinal(Hmac* hmac, byte* out)
    {
        if (hmac == NULL) {
            return BAD_FUNC_ARG;
        }

        return HmacFinal_fips(hmac, out);
    }
    int wolfSSL_GetHmacMaxSize(void)
    {
        return CyaSSL_GetHmacMaxSize();
    }

    int wc_HmacInit(Hmac* hmac, void* heap, int devId)
    {
        (void)hmac;
        (void)heap;
        (void)devId;
        /* FIPS doesn't support:
            return HmacInit(hmac, heap, devId); */
        return 0;
    }
    void wc_HmacFree(Hmac* hmac)
    {
        (void)hmac;
        /* FIPS doesn't support:
            HmacFree(hmac); */
    }

    #ifdef HAVE_HKDF
        int wc_HKDF(int type, const byte* inKey, word32 inKeySz,
                    const byte* salt, word32 saltSz,
                    const byte* info, word32 infoSz,
                    byte* out, word32 outSz)
        {
            return HKDF(type, inKey, inKeySz, salt, saltSz,
                info, infoSz, out, outSz);
        }
    #endif /* HAVE_HKDF */

#else /* else build without fips, or for new fips */


int wc_HmacSizeByType(int type)
{
    int ret;

    if (!(type == WC_MD5 || type == WC_SHA ||
            type == WC_SHA224 || type == WC_SHA256 ||
            type == WC_SHA384 || type == WC_SHA512 ||
            type == WC_SHA3_224 || type == WC_SHA3_256 ||
            type == WC_SHA3_384 || type == WC_SHA3_512)) {
        return BAD_FUNC_ARG;
    }

    switch (type) {
    #ifndef NO_MD5
        case WC_MD5:
            ret = WC_MD5_DIGEST_SIZE;
            break;
    #endif /* !NO_MD5 */

    #ifndef NO_SHA
        case WC_SHA:
            ret = WC_SHA_DIGEST_SIZE;
            break;
    #endif /* !NO_SHA */

    #ifdef WOLFSSL_SHA224
        case WC_SHA224:
            ret = WC_SHA224_DIGEST_SIZE;
            break;
    #endif /* WOLFSSL_SHA224 */

    #ifndef NO_SHA256
        case WC_SHA256:
            ret = WC_SHA256_DIGEST_SIZE;
            break;
    #endif /* !NO_SHA256 */

    #ifdef WOLFSSL_SHA384
        case WC_SHA384:
            ret = WC_SHA384_DIGEST_SIZE;
            break;
    #endif /* WOLFSSL_SHA384 */
    #ifdef WOLFSSL_SHA512
        case WC_SHA512:
            ret = WC_SHA512_DIGEST_SIZE;
            break;
    #endif /* WOLFSSL_SHA512 */

    #ifdef WOLFSSL_SHA3
        case WC_SHA3_224:
            ret = WC_SHA3_224_DIGEST_SIZE;
            break;

        case WC_SHA3_256:
            ret = WC_SHA3_256_DIGEST_SIZE;
            break;

        case WC_SHA3_384:
            ret = WC_SHA3_384_DIGEST_SIZE;
            break;

        case WC_SHA3_512:
            ret = WC_SHA3_512_DIGEST_SIZE;
            break;

    #endif

        default:
            ret = BAD_FUNC_ARG;
            break;
    }

    return ret;
}

int _InitHmac(Hmac* hmac, int type, void* heap)
{
    int ret = 0;

    switch (type) {
    #ifndef NO_MD5
        case WC_MD5:
            ret = wc_InitMd5(&hmac->hash.md5);
            break;
    #endif /* !NO_MD5 */

    #ifndef NO_SHA
        case WC_SHA:
            ret = wc_InitSha(&hmac->hash.sha);
            break;
    #endif /* !NO_SHA */

    #ifdef WOLFSSL_SHA224
        case WC_SHA224:
            ret = wc_InitSha224(&hmac->hash.sha224);
            break;
    #endif /* WOLFSSL_SHA224 */

    #ifndef NO_SHA256
        case WC_SHA256:
            ret = wc_InitSha256(&hmac->hash.sha256);
            break;
    #endif /* !NO_SHA256 */

    #ifdef WOLFSSL_SHA384
        case WC_SHA384:
            ret = wc_InitSha384(&hmac->hash.sha384);
            break;
    #endif /* WOLFSSL_SHA384 */
    #ifdef WOLFSSL_SHA512
        case WC_SHA512:
            ret = wc_InitSha512(&hmac->hash.sha512);
            break;
    #endif /* WOLFSSL_SHA512 */

    #ifdef WOLFSSL_SHA3
    #ifndef WOLFSSL_NOSHA3_224
        case WC_SHA3_224:
            ret = wc_InitSha3_224(&hmac->hash.sha3, heap, INVALID_DEVID);
            break;
    #endif
    #ifndef WOLFSSL_NOSHA3_256
        case WC_SHA3_256:
            ret = wc_InitSha3_256(&hmac->hash.sha3, heap, INVALID_DEVID);
            break;
    #endif
    #ifndef WOLFSSL_NOSHA3_384
        case WC_SHA3_384:
            ret = wc_InitSha3_384(&hmac->hash.sha3, heap, INVALID_DEVID);
            break;
    #endif
    #ifndef WOLFSSL_NOSHA3_512
        case WC_SHA3_512:
            ret = wc_InitSha3_512(&hmac->hash.sha3, heap, INVALID_DEVID);
            break;
    #endif
    #endif

        default:
            ret = BAD_FUNC_ARG;
            break;
    }

    /* default to NULL heap hint or test value */
#ifdef WOLFSSL_HEAP_TEST
    hmac->heap = (void)WOLFSSL_HEAP_TEST;
#else
    hmac->heap = heap;
#endif /* WOLFSSL_HEAP_TEST */

    return ret;
}


int wc_HmacSetKey(Hmac* hmac, int type, const byte* key, word32 length)
{
    byte*  ip;
    byte*  op;
    word32 i, hmac_block_size = 0;
    int    ret = 0;
    void*  heap = NULL;

    if (hmac == NULL || (key == NULL && length != 0) ||
       !(type == WC_MD5 || type == WC_SHA ||
            type == WC_SHA224 || type == WC_SHA256 ||
            type == WC_SHA384 || type == WC_SHA512 ||
            type == WC_SHA3_224 || type == WC_SHA3_256 ||
            type == WC_SHA3_384 || type == WC_SHA3_512)) {
        return BAD_FUNC_ARG;
    }

#ifndef HAVE_FIPS
    /* if set key has already been run then make sure and free existing */
    /* This is for async and PIC32MZ situations, and just normally OK,
       provided the user calls wc_HmacInit() first. That function is not
       available in FIPS builds. In current FIPS builds, the hashes are
       not allocating resources. */
    if (hmac->macType != WC_HASH_TYPE_NONE) {
        wc_HmacFree(hmac);
    }
#endif

    hmac->innerHashKeyed = 0;
    hmac->macType = (byte)type;

    ret = _InitHmac(hmac, type, heap);
    if (ret != 0)
        return ret;

#ifdef HAVE_FIPS
    if (length < HMAC_FIPS_MIN_KEY)
        return HMAC_MIN_KEYLEN_E;
#endif

#ifdef WOLF_CRYPTO_CB
    hmac->keyRaw = key; /* use buffer directly */
    hmac->keyLen = length;
#endif

    ip = (byte*)hmac->ipad;
    op = (byte*)hmac->opad;

    switch (hmac->macType) {
    #ifndef NO_MD5
        case WC_MD5:
            hmac_block_size = WC_MD5_BLOCK_SIZE;
            if (length <= WC_MD5_BLOCK_SIZE) {
                if (key != NULL) {
                    XMEMCPY(ip, key, length);
                }
            }
            else {
                ret = wc_Md5Update(&hmac->hash.md5, key, length);
                if (ret != 0)
                    break;
                ret = wc_Md5Final(&hmac->hash.md5, ip);
                if (ret != 0)
                    break;
                length = WC_MD5_DIGEST_SIZE;
            }
            break;
    #endif /* !NO_MD5 */

    #ifndef NO_SHA
        case WC_SHA:
            hmac_block_size = WC_SHA_BLOCK_SIZE;
            if (length <= WC_SHA_BLOCK_SIZE) {
                if (key != NULL) {
                    XMEMCPY(ip, key, length);
                }
            }
            else {
                ret = wc_ShaUpdate(&hmac->hash.sha, key, length);
                if (ret != 0)
                    break;
                ret = wc_ShaFinal(&hmac->hash.sha, ip);
                if (ret != 0)
                    break;

                length = WC_SHA_DIGEST_SIZE;
            }
            break;
    #endif /* !NO_SHA */

    #ifdef WOLFSSL_SHA224
        case WC_SHA224:
            hmac_block_size = WC_SHA224_BLOCK_SIZE;
            if (length <= WC_SHA224_BLOCK_SIZE) {
                if (key != NULL) {
                    XMEMCPY(ip, key, length);
                }
            }
            else {
                ret = wc_Sha224Update(&hmac->hash.sha224, key, length);
                if (ret != 0)
                    break;
                ret = wc_Sha224Final(&hmac->hash.sha224, ip);
                if (ret != 0)
                    break;

                length = WC_SHA224_DIGEST_SIZE;
            }
            break;
    #endif /* WOLFSSL_SHA224 */
    #ifndef NO_SHA256
        case WC_SHA256:
            hmac_block_size = WC_SHA256_BLOCK_SIZE;
            if (length <= WC_SHA256_BLOCK_SIZE) {
                if (key != NULL) {
                    XMEMCPY(ip, key, length);
                }
            }
            else {
                ret = wc_Sha256Update(&hmac->hash.sha256, key, length);
                if (ret != 0)
                    break;
                ret = wc_Sha256Final(&hmac->hash.sha256, ip);
                if (ret != 0)
                    break;

                length = WC_SHA256_DIGEST_SIZE;
            }
            break;
    #endif /* !NO_SHA256 */

    #ifdef WOLFSSL_SHA384
        case WC_SHA384:
            hmac_block_size = WC_SHA384_BLOCK_SIZE;
            if (length <= WC_SHA384_BLOCK_SIZE) {
                if (key != NULL) {
                    XMEMCPY(ip, key, length);
                }
            }
            else {
                ret = wc_Sha384Update(&hmac->hash.sha384, key, length);
                if (ret != 0)
                    break;
                ret = wc_Sha384Final(&hmac->hash.sha384, ip);
                if (ret != 0)
                    break;

                length = WC_SHA384_DIGEST_SIZE;
            }
            break;
    #endif /* WOLFSSL_SHA384 */
    #ifdef WOLFSSL_SHA512
        case WC_SHA512:
            hmac_block_size = WC_SHA512_BLOCK_SIZE;
            if (length <= WC_SHA512_BLOCK_SIZE) {
                if (key != NULL) {
                    XMEMCPY(ip, key, length);
                }
            }
            else {
                ret = wc_Sha512Update(&hmac->hash.sha512, key, length);
                if (ret != 0)
                    break;
                ret = wc_Sha512Final(&hmac->hash.sha512, ip);
                if (ret != 0)
                    break;

                length = WC_SHA512_DIGEST_SIZE;
            }
            break;
    #endif /* WOLFSSL_SHA512 */

    #ifdef WOLFSSL_SHA3
    #ifndef WOLFSSL_NOSHA3_224
        case WC_SHA3_224:
            hmac_block_size = WC_SHA3_224_BLOCK_SIZE;
            if (length <= WC_SHA3_224_BLOCK_SIZE) {
                if (key != NULL) {
                    XMEMCPY(ip, key, length);
                }
            }
            else {
                ret = wc_Sha3_224_Update(&hmac->hash.sha3, key, length);
                if (ret != 0)
                    break;
                ret = wc_Sha3_224_Final(&hmac->hash.sha3, ip);
                if (ret != 0)
                    break;

                length = WC_SHA3_224_DIGEST_SIZE;
            }
            break;
    #endif
    #ifndef WOLFSSL_NOSHA3_256
        case WC_SHA3_256:
            hmac_block_size = WC_SHA3_256_BLOCK_SIZE;
            if (length <= WC_SHA3_256_BLOCK_SIZE) {
                if (key != NULL) {
                    XMEMCPY(ip, key, length);
                }
            }
            else {
                ret = wc_Sha3_256_Update(&hmac->hash.sha3, key, length);
                if (ret != 0)
                    break;
                ret = wc_Sha3_256_Final(&hmac->hash.sha3, ip);
                if (ret != 0)
                    break;

                length = WC_SHA3_256_DIGEST_SIZE;
            }
            break;
    #endif
    #ifndef WOLFSSL_NOSHA3_384
        case WC_SHA3_384:
            hmac_block_size = WC_SHA3_384_BLOCK_SIZE;
            if (length <= WC_SHA3_384_BLOCK_SIZE) {
                if (key != NULL) {
                    XMEMCPY(ip, key, length);
                }
            }
            else {
                ret = wc_Sha3_384_Update(&hmac->hash.sha3, key, length);
                if (ret != 0)
                    break;
                ret = wc_Sha3_384_Final(&hmac->hash.sha3, ip);
                if (ret != 0)
                    break;

                length = WC_SHA3_384_DIGEST_SIZE;
            }
            break;
    #endif
    #ifndef WOLFSSL_NOSHA3_512
        case WC_SHA3_512:
            hmac_block_size = WC_SHA3_512_BLOCK_SIZE;
            if (length <= WC_SHA3_512_BLOCK_SIZE) {
                if (key != NULL) {
                    XMEMCPY(ip, key, length);
                }
            }
            else {
                ret = wc_Sha3_512_Update(&hmac->hash.sha3, key, length);
                if (ret != 0)
                    break;
                ret = wc_Sha3_512_Final(&hmac->hash.sha3, ip);
                if (ret != 0)
                    break;

                length = WC_SHA3_512_DIGEST_SIZE;
            }
            break;
    #endif
    #endif /* WOLFSSL_SHA3 */

        default:
            return BAD_FUNC_ARG;
    }

#if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_HMAC)
    if (hmac->asyncDev.marker == WOLFSSL_ASYNC_MARKER_HMAC) {
    #if defined(HAVE_INTEL_QA) || defined(HAVE_CAVIUM)
        #ifdef HAVE_INTEL_QA
        if (IntelQaHmacGetType(hmac->macType, NULL) == 0)
        #endif
        {
            if (length > hmac_block_size)
                length = hmac_block_size;
            /* update key length */
            hmac->keyLen = (word16)length;

            return ret;
        }
        /* no need to pad below */
    #endif
    }
#endif

    if (ret == 0) {
        if (length < hmac_block_size)
            XMEMSET(ip + length, 0, hmac_block_size - length);

        for(i = 0; i < hmac_block_size; i++) {
            op[i] = ip[i] ^ OPAD;
            ip[i] ^= IPAD;
        }
    }

    return ret;
}


static int HmacKeyInnerHash(Hmac* hmac)
{
    int ret = 0;

    switch (hmac->macType) {
    #ifndef NO_MD5
        case WC_MD5:
            ret = wc_Md5Update(&hmac->hash.md5, (byte*)hmac->ipad,
                                                             WC_MD5_BLOCK_SIZE);
            break;
    #endif /* !NO_MD5 */

    #ifndef NO_SHA
        case WC_SHA:
            ret = wc_ShaUpdate(&hmac->hash.sha, (byte*)hmac->ipad,
                                                             WC_SHA_BLOCK_SIZE);
            break;
    #endif /* !NO_SHA */

    #ifdef WOLFSSL_SHA224
        case WC_SHA224:
            ret = wc_Sha224Update(&hmac->hash.sha224, (byte*)hmac->ipad,
                                                          WC_SHA224_BLOCK_SIZE);
            break;
    #endif /* WOLFSSL_SHA224 */
    #ifndef NO_SHA256
        case WC_SHA256:
            ret = wc_Sha256Update(&hmac->hash.sha256, (byte*)hmac->ipad,
                                                          WC_SHA256_BLOCK_SIZE);
            break;
    #endif /* !NO_SHA256 */

    #ifdef WOLFSSL_SHA384
        case WC_SHA384:
            ret = wc_Sha384Update(&hmac->hash.sha384, (byte*)hmac->ipad,
                                                          WC_SHA384_BLOCK_SIZE);
            break;
    #endif /* WOLFSSL_SHA384 */
    #ifdef WOLFSSL_SHA512
        case WC_SHA512:
            ret = wc_Sha512Update(&hmac->hash.sha512, (byte*)hmac->ipad,
                                                          WC_SHA512_BLOCK_SIZE);
            break;
    #endif /* WOLFSSL_SHA512 */

    #ifdef WOLFSSL_SHA3
    #ifndef WOLFSSL_NOSHA3_224
        case WC_SHA3_224:
            ret = wc_Sha3_224_Update(&hmac->hash.sha3, (byte*)hmac->ipad,
                                                        WC_SHA3_224_BLOCK_SIZE);
            break;
    #endif
    #ifndef WOLFSSL_NOSHA3_256
        case WC_SHA3_256:
            ret = wc_Sha3_256_Update(&hmac->hash.sha3, (byte*)hmac->ipad,
                                                        WC_SHA3_256_BLOCK_SIZE);
            break;
    #endif
    #ifndef WOLFSSL_NOSHA3_384
        case WC_SHA3_384:
            ret = wc_Sha3_384_Update(&hmac->hash.sha3, (byte*)hmac->ipad,
                                                        WC_SHA3_384_BLOCK_SIZE);
            break;
    #endif
    #ifndef WOLFSSL_NOSHA3_512
        case WC_SHA3_512:
            ret = wc_Sha3_512_Update(&hmac->hash.sha3, (byte*)hmac->ipad,
                                                        WC_SHA3_512_BLOCK_SIZE);
            break;
    #endif
    #endif /* WOLFSSL_SHA3 */

        default:
            break;
    }

    if (ret == 0)
        hmac->innerHashKeyed = WC_HMAC_INNER_HASH_KEYED_SW;

    return ret;
}


int wc_HmacUpdate(Hmac* hmac, const byte* msg, word32 length)
{
    int ret = 0;

    if (hmac == NULL || (msg == NULL && length > 0)) {
        return BAD_FUNC_ARG;
    }

#ifdef WOLF_CRYPTO_CB
    if (hmac->devId != INVALID_DEVID) {
        ret = wc_CryptoCb_Hmac(hmac, hmac->macType, msg, length, NULL);
        if (ret != CRYPTOCB_UNAVAILABLE)
            return ret;
        /* fall-through when unavailable */
        ret = 0; /* reset error code */
    }
#endif
#if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_HMAC)
    if (hmac->asyncDev.marker == WOLFSSL_ASYNC_MARKER_HMAC) {
    #if defined(HAVE_CAVIUM)
        return NitroxHmacUpdate(hmac, msg, length);
    #elif defined(HAVE_INTEL_QA)
        if (IntelQaHmacGetType(hmac->macType, NULL) == 0) {
            return IntelQaHmac(&hmac->asyncDev, hmac->macType,
                (byte*)hmac->ipad, hmac->keyLen, NULL, msg, length);
        }
    #endif
    }
#endif /* WOLFSSL_ASYNC_CRYPT */

    if (!hmac->innerHashKeyed) {
        ret = HmacKeyInnerHash(hmac);
        if (ret != 0)
            return ret;
    }

    switch (hmac->macType) {
    #ifndef NO_MD5
        case WC_MD5:
            ret = wc_Md5Update(&hmac->hash.md5, msg, length);
            break;
    #endif /* !NO_MD5 */

    #ifndef NO_SHA
        case WC_SHA:
            ret = wc_ShaUpdate(&hmac->hash.sha, msg, length);
            break;
    #endif /* !NO_SHA */

    #ifdef WOLFSSL_SHA224
        case WC_SHA224:
            ret = wc_Sha224Update(&hmac->hash.sha224, msg, length);
            break;
    #endif /* WOLFSSL_SHA224 */

    #ifndef NO_SHA256
        case WC_SHA256:
            ret = wc_Sha256Update(&hmac->hash.sha256, msg, length);
            break;
    #endif /* !NO_SHA256 */

    #ifdef WOLFSSL_SHA384
        case WC_SHA384:
            ret = wc_Sha384Update(&hmac->hash.sha384, msg, length);
            break;
    #endif /* WOLFSSL_SHA384 */
    #ifdef WOLFSSL_SHA512
        case WC_SHA512:
            ret = wc_Sha512Update(&hmac->hash.sha512, msg, length);
            break;
    #endif /* WOLFSSL_SHA512 */

    #ifdef WOLFSSL_SHA3
    #ifndef WOLFSSL_NOSHA3_224
        case WC_SHA3_224:
            ret = wc_Sha3_224_Update(&hmac->hash.sha3, msg, length);
            break;
    #endif
    #ifndef WOLFSSL_NOSHA3_256
        case WC_SHA3_256:
            ret = wc_Sha3_256_Update(&hmac->hash.sha3, msg, length);
            break;
    #endif
    #ifndef WOLFSSL_NOSHA3_384
        case WC_SHA3_384:
            ret = wc_Sha3_384_Update(&hmac->hash.sha3, msg, length);
            break;
    #endif
    #ifndef WOLFSSL_NOSHA3_512
        case WC_SHA3_512:
            ret = wc_Sha3_512_Update(&hmac->hash.sha3, msg, length);
            break;
    #endif
    #endif /* WOLFSSL_SHA3 */

        default:
            break;
    }

    return ret;
}


int wc_HmacFinal(Hmac* hmac, byte* hash)
{
    int ret;

    if (hmac == NULL || hash == NULL) {
        return BAD_FUNC_ARG;
    }

#ifdef WOLF_CRYPTO_CB
    if (hmac->devId != INVALID_DEVID) {
        ret = wc_CryptoCb_Hmac(hmac, hmac->macType, NULL, 0, hash);
        if (ret != CRYPTOCB_UNAVAILABLE)
            return ret;
        /* fall-through when unavailable */
    }
#endif
#if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_HMAC)
    if (hmac->asyncDev.marker == WOLFSSL_ASYNC_MARKER_HMAC) {
        int hashLen = wc_HmacSizeByType(hmac->macType);
        if (hashLen <= 0)
            return hashLen;

    #if defined(HAVE_CAVIUM)
        return NitroxHmacFinal(hmac, hash, hashLen);
    #elif defined(HAVE_INTEL_QA)
        if (IntelQaHmacGetType(hmac->macType, NULL) == 0) {
            return IntelQaHmac(&hmac->asyncDev, hmac->macType,
                (byte*)hmac->ipad, hmac->keyLen, hash, NULL, hashLen);
        }
    #endif
    }
#endif /* WOLFSSL_ASYNC_CRYPT */

    if (!hmac->innerHashKeyed) {
        ret = HmacKeyInnerHash(hmac);
        if (ret != 0)
            return ret;
    }

    switch (hmac->macType) {
    #ifndef NO_MD5
        case WC_MD5:
            ret = wc_Md5Final(&hmac->hash.md5, (byte*)hmac->innerHash);
            if (ret != 0)
                break;
            ret = wc_Md5Update(&hmac->hash.md5, (byte*)hmac->opad,
                                                             WC_MD5_BLOCK_SIZE);
            if (ret != 0)
                break;
            ret = wc_Md5Update(&hmac->hash.md5, (byte*)hmac->innerHash,
                                                            WC_MD5_DIGEST_SIZE);
            if (ret != 0)
                break;
            ret = wc_Md5Final(&hmac->hash.md5, hash);
            break;
    #endif /* !NO_MD5 */

    #ifndef NO_SHA
        case WC_SHA:
            ret = wc_ShaFinal(&hmac->hash.sha, (byte*)hmac->innerHash);
            if (ret != 0)
                break;
            ret = wc_ShaUpdate(&hmac->hash.sha, (byte*)hmac->opad,
                                                             WC_SHA_BLOCK_SIZE);
            if (ret != 0)
                break;
            ret = wc_ShaUpdate(&hmac->hash.sha, (byte*)hmac->innerHash,
                                                            WC_SHA_DIGEST_SIZE);
            if (ret != 0)
                break;
            ret = wc_ShaFinal(&hmac->hash.sha, hash);
            break;
    #endif /* !NO_SHA */

    #ifdef WOLFSSL_SHA224
        case WC_SHA224:
            ret = wc_Sha224Final(&hmac->hash.sha224, (byte*)hmac->innerHash);
            if (ret != 0)
                break;
            ret = wc_Sha224Update(&hmac->hash.sha224, (byte*)hmac->opad,
                                                          WC_SHA224_BLOCK_SIZE);
            if (ret != 0)
                break;
            ret = wc_Sha224Update(&hmac->hash.sha224, (byte*)hmac->innerHash,
                                                         WC_SHA224_DIGEST_SIZE);
            if (ret != 0)
                break;
            ret = wc_Sha224Final(&hmac->hash.sha224, hash);
            if (ret != 0)
                break;
            break;
    #endif /* WOLFSSL_SHA224 */
    #ifndef NO_SHA256
        case WC_SHA256:
            ret = wc_Sha256Final(&hmac->hash.sha256, (byte*)hmac->innerHash);
            if (ret != 0)
                break;
            ret = wc_Sha256Update(&hmac->hash.sha256, (byte*)hmac->opad,
                                                          WC_SHA256_BLOCK_SIZE);
            if (ret != 0)
                break;
            ret = wc_Sha256Update(&hmac->hash.sha256, (byte*)hmac->innerHash,
                                                         WC_SHA256_DIGEST_SIZE);
            if (ret != 0)
                break;
            ret = wc_Sha256Final(&hmac->hash.sha256, hash);
            break;
    #endif /* !NO_SHA256 */

    #ifdef WOLFSSL_SHA384
        case WC_SHA384:
            ret = wc_Sha384Final(&hmac->hash.sha384, (byte*)hmac->innerHash);
            if (ret != 0)
                break;
            ret = wc_Sha384Update(&hmac->hash.sha384, (byte*)hmac->opad,
                                                          WC_SHA384_BLOCK_SIZE);
            if (ret != 0)
                break;
            ret = wc_Sha384Update(&hmac->hash.sha384, (byte*)hmac->innerHash,
                                                         WC_SHA384_DIGEST_SIZE);
            if (ret != 0)
                break;
            ret = wc_Sha384Final(&hmac->hash.sha384, hash);
            break;
    #endif /* WOLFSSL_SHA384 */
    #ifdef WOLFSSL_SHA512
        case WC_SHA512:
            ret = wc_Sha512Final(&hmac->hash.sha512, (byte*)hmac->innerHash);
            if (ret != 0)
                break;
            ret = wc_Sha512Update(&hmac->hash.sha512, (byte*)hmac->opad,
                                                          WC_SHA512_BLOCK_SIZE);
            if (ret != 0)
                break;
            ret = wc_Sha512Update(&hmac->hash.sha512, (byte*)hmac->innerHash,
                                                         WC_SHA512_DIGEST_SIZE);
            if (ret != 0)
                break;
            ret = wc_Sha512Final(&hmac->hash.sha512, hash);
            break;
    #endif /* WOLFSSL_SHA512 */

    #ifdef WOLFSSL_SHA3
    #ifndef WOLFSSL_NOSHA3_224
        case WC_SHA3_224:
            ret = wc_Sha3_224_Final(&hmac->hash.sha3, (byte*)hmac->innerHash);
            if (ret != 0)
                break;
            ret = wc_Sha3_224_Update(&hmac->hash.sha3, (byte*)hmac->opad,
                                                        WC_SHA3_224_BLOCK_SIZE);
            if (ret != 0)
                break;
            ret = wc_Sha3_224_Update(&hmac->hash.sha3, (byte*)hmac->innerHash,
                                                       WC_SHA3_224_DIGEST_SIZE);
            if (ret != 0)
                break;
            ret = wc_Sha3_224_Final(&hmac->hash.sha3, hash);
            break;
    #endif
    #ifndef WOLFSSL_NOSHA3_256
        case WC_SHA3_256:
            ret = wc_Sha3_256_Final(&hmac->hash.sha3, (byte*)hmac->innerHash);
            if (ret != 0)
                break;
            ret = wc_Sha3_256_Update(&hmac->hash.sha3, (byte*)hmac->opad,
                                                        WC_SHA3_256_BLOCK_SIZE);
            if (ret != 0)
                break;
            ret = wc_Sha3_256_Update(&hmac->hash.sha3, (byte*)hmac->innerHash,
                                                       WC_SHA3_256_DIGEST_SIZE);
            if (ret != 0)
                break;
            ret = wc_Sha3_256_Final(&hmac->hash.sha3, hash);
            break;
    #endif
    #ifndef WOLFSSL_NOSHA3_384
        case WC_SHA3_384:
            ret = wc_Sha3_384_Final(&hmac->hash.sha3, (byte*)hmac->innerHash);
            if (ret != 0)
                break;
            ret = wc_Sha3_384_Update(&hmac->hash.sha3, (byte*)hmac->opad,
                                                        WC_SHA3_384_BLOCK_SIZE);
            if (ret != 0)
                break;
            ret = wc_Sha3_384_Update(&hmac->hash.sha3, (byte*)hmac->innerHash,
                                                       WC_SHA3_384_DIGEST_SIZE);
            if (ret != 0)
                break;
            ret = wc_Sha3_384_Final(&hmac->hash.sha3, hash);
            break;
    #endif
    #ifndef WOLFSSL_NOSHA3_512
        case WC_SHA3_512:
            ret = wc_Sha3_512_Final(&hmac->hash.sha3, (byte*)hmac->innerHash);
            if (ret != 0)
                break;
            ret = wc_Sha3_512_Update(&hmac->hash.sha3, (byte*)hmac->opad,
                                                        WC_SHA3_512_BLOCK_SIZE);
            if (ret != 0)
                break;
            ret = wc_Sha3_512_Update(&hmac->hash.sha3, (byte*)hmac->innerHash,
                                                       WC_SHA3_512_DIGEST_SIZE);
            if (ret != 0)
                break;
            ret = wc_Sha3_512_Final(&hmac->hash.sha3, hash);
            break;
    #endif
    #endif /* WOLFSSL_SHA3 */

        default:
            ret = BAD_FUNC_ARG;
            break;
    }

    if (ret == 0) {
        hmac->innerHashKeyed = 0;
    }

    return ret;
}


/* Initialize Hmac for use with async device */
int wc_HmacInit(Hmac* hmac, void* heap, int devId)
{
    int ret = 0;

    if (hmac == NULL)
        return BAD_FUNC_ARG;

    XMEMSET(hmac, 0, sizeof(Hmac));
    hmac->macType = WC_HASH_TYPE_NONE;
    hmac->heap = heap;
#ifdef WOLF_CRYPTO_CB
    hmac->devId = devId;
    hmac->devCtx = NULL;
#endif

#if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_HMAC)
    ret = wolfAsync_DevCtxInit(&hmac->asyncDev, WOLFSSL_ASYNC_MARKER_HMAC,
                                                         hmac->heap, devId);
#else
    (void)devId;
#endif /* WOLFSSL_ASYNC_CRYPT */

    return ret;
}

#ifdef HAVE_PKCS11
int  wc_HmacInit_Id(Hmac* hmac, unsigned char* id, int len, void* heap,
                    int devId)
{
    int ret = 0;

    if (hmac == NULL)
        ret = BAD_FUNC_ARG;
    if (ret == 0 && (len < 0 || len > HMAC_MAX_ID_LEN))
        ret = BUFFER_E;

    if (ret == 0)
        ret  = wc_HmacInit(hmac, heap, devId);
    if (ret == 0) {
        XMEMCPY(hmac->id, id, len);
        hmac->idLen = len;
    }

    return ret;
}
#endif

/* Free Hmac from use with async device */
void wc_HmacFree(Hmac* hmac)
{
    if (hmac == NULL)
        return;

#ifdef WOLF_CRYPTO_CB
    /* handle cleanup case where final is not called */
    if (hmac->devId != INVALID_DEVID && hmac->devCtx != NULL) {
        int  ret;
        byte finalHash[WC_HMAC_BLOCK_SIZE];
        ret = wc_CryptoCb_Hmac(hmac, hmac->macType, NULL, 0, finalHash);
        (void)ret; /* must ignore return code here */
        (void)finalHash;
    }
#endif

    switch (hmac->macType) {
    #ifndef NO_MD5
        case WC_MD5:
            wc_Md5Free(&hmac->hash.md5);
            break;
    #endif /* !NO_MD5 */

    #ifndef NO_SHA
        case WC_SHA:
            wc_ShaFree(&hmac->hash.sha);
            break;
    #endif /* !NO_SHA */

    #ifdef WOLFSSL_SHA224
        case WC_SHA224:
            wc_Sha224Free(&hmac->hash.sha224);
            break;
    #endif /* WOLFSSL_SHA224 */
    #ifndef NO_SHA256
        case WC_SHA256:
            wc_Sha256Free(&hmac->hash.sha256);
            break;
    #endif /* !NO_SHA256 */

    #ifdef WOLFSSL_SHA384
        case WC_SHA384:
            wc_Sha384Free(&hmac->hash.sha384);
            break;
    #endif /* WOLFSSL_SHA384 */
    #ifdef WOLFSSL_SHA512
        case WC_SHA512:
            wc_Sha512Free(&hmac->hash.sha512);
            break;
    #endif /* WOLFSSL_SHA512 */

    #ifdef WOLFSSL_SHA3
    #ifndef WOLFSSL_NOSHA3_224
        case WC_SHA3_224:
            wc_Sha3_224_Free(&hmac->hash.sha3);
            break;
    #endif
    #ifndef WOLFSSL_NOSHA3_256
        case WC_SHA3_256:
            wc_Sha3_256_Free(&hmac->hash.sha3);
            break;
    #endif
    #ifndef WOLFSSL_NOSHA3_384
        case WC_SHA3_384:
            wc_Sha3_384_Free(&hmac->hash.sha3);
            break;
    #endif
    #ifndef WOLFSSL_NOSHA3_512
        case WC_SHA3_512:
            wc_Sha3_512_Free(&hmac->hash.sha3);
            break;
    #endif
    #endif /* WOLFSSL_SHA3 */

        default:
            break;
    }

#if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_HMAC)
    wolfAsync_DevCtxFree(&hmac->asyncDev, WOLFSSL_ASYNC_MARKER_HMAC);
#endif /* WOLFSSL_ASYNC_CRYPT */

    switch (hmac->macType) {
    #ifndef NO_MD5
        case WC_MD5:
            wc_Md5Free(&hmac->hash.md5);
            break;
    #endif /* !NO_MD5 */

    #ifndef NO_SHA
        case WC_SHA:
            wc_ShaFree(&hmac->hash.sha);
            break;
    #endif /* !NO_SHA */

    #ifdef WOLFSSL_SHA224
        case WC_SHA224:
            wc_Sha224Free(&hmac->hash.sha224);
            break;
    #endif /* WOLFSSL_SHA224 */
    #ifndef NO_SHA256
        case WC_SHA256:
            wc_Sha256Free(&hmac->hash.sha256);
            break;
    #endif /* !NO_SHA256 */

    #ifdef WOLFSSL_SHA512
    #ifdef WOLFSSL_SHA384
        case WC_SHA384:
            wc_Sha384Free(&hmac->hash.sha384);
            break;
    #endif /* WOLFSSL_SHA384 */
        case WC_SHA512:
            wc_Sha512Free(&hmac->hash.sha512);
            break;
    #endif /* WOLFSSL_SHA512 */
    }
}

int wolfSSL_GetHmacMaxSize(void)
{
    return WC_MAX_DIGEST_SIZE;
}

#ifdef HAVE_HKDF
    /* HMAC-KDF-Extract.
     * RFC 5869 - HMAC-based Extract-and-Expand Key Derivation Function (HKDF).
     *
     * type     The hash algorithm type.
     * salt     The optional salt value.
     * saltSz   The size of the salt.
     * inKey    The input keying material.
     * inKeySz  The size of the input keying material.
     * out      The pseudorandom key with the length that of the hash.
     * returns 0 on success, otherwise failure.
     */
    int wc_HKDF_Extract(int type, const byte* salt, word32 saltSz,
                        const byte* inKey, word32 inKeySz, byte* out)
    {
        byte   tmp[WC_MAX_DIGEST_SIZE]; /* localSalt helper */
        Hmac   myHmac;
        int    ret;
        const  byte* localSalt;  /* either points to user input or tmp */
        int    hashSz;

        ret = wc_HmacSizeByType(type);
        if (ret < 0)
            return ret;

        hashSz = ret;
        localSalt = salt;
        if (localSalt == NULL) {
            XMEMSET(tmp, 0, hashSz);
            localSalt = tmp;
            saltSz    = hashSz;
        }

        ret = wc_HmacInit(&myHmac, NULL, INVALID_DEVID);
        if (ret == 0) {
            ret = wc_HmacSetKey(&myHmac, type, localSalt, saltSz);
            if (ret == 0)
                ret = wc_HmacUpdate(&myHmac, inKey, inKeySz);
            if (ret == 0)
                ret = wc_HmacFinal(&myHmac,  out);
            wc_HmacFree(&myHmac);
        }

        return ret;
    }

    /* HMAC-KDF-Expand.
     * RFC 5869 - HMAC-based Extract-and-Expand Key Derivation Function (HKDF).
     *
     * type     The hash algorithm type.
     * inKey    The input key.
     * inKeySz  The size of the input key.
     * info     The application specific information.
     * infoSz   The size of the application specific information.
     * out      The output keying material.
     * returns 0 on success, otherwise failure.
     */
    int wc_HKDF_Expand(int type, const byte* inKey, word32 inKeySz,
                       const byte* info, word32 infoSz, byte* out, word32 outSz)
    {
        byte   tmp[WC_MAX_DIGEST_SIZE];
        Hmac   myHmac;
        int    ret = 0;
        word32 outIdx = 0;
        word32 hashSz = wc_HmacSizeByType(type);
        byte   n = 0x1;

        ret = wc_HmacInit(&myHmac, NULL, INVALID_DEVID);
        if (ret != 0)
            return ret;

        while (outIdx < outSz) {
            int    tmpSz = (n == 1) ? 0 : hashSz;
            word32 left = outSz - outIdx;

            ret = wc_HmacSetKey(&myHmac, type, inKey, inKeySz);
            if (ret != 0)
                break;
            ret = wc_HmacUpdate(&myHmac, tmp, tmpSz);
            if (ret != 0)
                break;
            ret = wc_HmacUpdate(&myHmac, info, infoSz);
            if (ret != 0)
                break;
            ret = wc_HmacUpdate(&myHmac, &n, 1);
            if (ret != 0)
                break;
            ret = wc_HmacFinal(&myHmac, tmp);
            if (ret != 0)
                break;

            left = min(left, hashSz);
            XMEMCPY(out+outIdx, tmp, left);

            outIdx += hashSz;
            n++;
        }

        wc_HmacFree(&myHmac);

        return ret;
    }

    /* HMAC-KDF.
     * RFC 5869 - HMAC-based Extract-and-Expand Key Derivation Function (HKDF).
     *
     * type     The hash algorithm type.
     * inKey    The input keying material.
     * inKeySz  The size of the input keying material.
     * salt     The optional salt value.
     * saltSz   The size of the salt.
     * info     The application specific information.
     * infoSz   The size of the application specific information.
     * out      The output keying material.
     * returns 0 on success, otherwise failure.
     */
    int wc_HKDF(int type, const byte* inKey, word32 inKeySz,
                       const byte* salt,  word32 saltSz,
                       const byte* info,  word32 infoSz,
                       byte* out,         word32 outSz)
    {
        byte   prk[WC_MAX_DIGEST_SIZE];
        int    hashSz = wc_HmacSizeByType(type);
        int    ret;

        if (hashSz < 0)
            return BAD_FUNC_ARG;

        ret = wc_HKDF_Extract(type, salt, saltSz, inKey, inKeySz, prk);
        if (ret != 0)
            return ret;

        return wc_HKDF_Expand(type, prk, hashSz, info, infoSz, out, outSz);
    }

#endif /* HAVE_HKDF */

#endif /* HAVE_FIPS */
#endif /* NO_HMAC */
