/* pwdbased.c
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

#ifndef NO_PWDBASED

#ifdef WOLFSSL_PIC32MZ_HASH
    #ifndef NO_MD5
        #define wc_InitMd5   wc_InitMd5_sw
        #define wc_Md5Update wc_Md5Update_sw
        #define wc_Md5Final  wc_Md5Final_sw
    #endif /* NO_MD5 */

    #define wc_InitSha   wc_InitSha_sw
    #define wc_ShaUpdate wc_ShaUpdate_sw
    #define wc_ShaFinal  wc_ShaFinal_sw

    #define wc_InitSha256   wc_InitSha256_sw
    #define wc_Sha256Update wc_Sha256Update_sw
    #define wc_Sha256Final  wc_Sha256Final_sw
#endif

#include <wolfssl/wolfcrypt/pwdbased.h>
#include <wolfssl/wolfcrypt/hmac.h>
#include <wolfssl/wolfcrypt/integer.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#if defined(WOLFSSL_SHA512) || defined(WOLFSSL_SHA384)
    #include <wolfssl/wolfcrypt/sha512.h>
#endif

#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #include <wolfcrypt/src/misc.c>
#endif

#ifndef WOLFSSL_HAVE_MIN
#define WOLFSSL_HAVE_MIN

    static INLINE word32 min(word32 a, word32 b)
    {
        return a > b ? b : a;
    }

#endif /* WOLFSSL_HAVE_MIN */


#ifndef NO_SHA
/* PBKDF1 needs at least SHA available */
int wc_PBKDF1(byte* output, const byte* passwd, int pLen, const byte* salt,
           int sLen, int iterations, int kLen, int hashType)
{
    Sha  sha;
#ifndef NO_MD5
    Md5  md5;
#endif
    int  hLen = (int)SHA_DIGEST_SIZE;
    int  i, ret = 0;
    byte buffer[SHA_DIGEST_SIZE];  /* max size */

    if (hashType != MD5 && hashType != SHA)
        return BAD_FUNC_ARG;

#ifndef NO_MD5
    if (hashType == MD5)
        hLen = (int)MD5_DIGEST_SIZE;
#endif

    if (kLen > hLen)
        return BAD_FUNC_ARG;

    if (iterations < 1)
        return BAD_FUNC_ARG;

    switch (hashType) {
#ifndef NO_MD5
        case MD5:
            wc_InitMd5(&md5);
            wc_Md5Update(&md5, passwd, pLen);
            wc_Md5Update(&md5, salt,   sLen);
            wc_Md5Final(&md5,  buffer);
            break;
#endif /* NO_MD5 */
        case SHA:
        default:
            ret = wc_InitSha(&sha);
            if (ret != 0)
                return ret;
            wc_ShaUpdate(&sha, passwd, pLen);
            wc_ShaUpdate(&sha, salt,   sLen);
            wc_ShaFinal(&sha,  buffer);
            break;
    }

    for (i = 1; i < iterations; i++) {
        if (hashType == SHA) {
            wc_ShaUpdate(&sha, buffer, hLen);
            wc_ShaFinal(&sha,  buffer);
        }
#ifndef NO_MD5
        else {
            wc_Md5Update(&md5, buffer, hLen);
            wc_Md5Final(&md5,  buffer);
        }
#endif
    }
    XMEMCPY(output, buffer, kLen);

    return 0;
}
#endif /* NO_SHA */


int GetDigestSize(int hashType)
{
    int hLen;

    switch (hashType) {
#ifndef NO_MD5
        case MD5:
            hLen = MD5_DIGEST_SIZE;
            break;
#endif
#ifndef NO_SHA
        case SHA:
            hLen = SHA_DIGEST_SIZE;
            break;
#endif
#ifndef NO_SHA256
        case SHA256:
            hLen = SHA256_DIGEST_SIZE;
            break;
#endif
#ifdef WOLFSSL_SHA512
        case SHA512:
            hLen = SHA512_DIGEST_SIZE;
            break;
#endif
        default:
            return BAD_FUNC_ARG;
    }

    return hLen;
}


int wc_PBKDF2(byte* output, const byte* passwd, int pLen, const byte* salt,
           int sLen, int iterations, int kLen, int hashType)
{
    word32 i = 1;
    int    hLen;
    int    j, ret;
    Hmac   hmac;
#ifdef WOLFSSL_SMALL_STACK
    byte*  buffer;
#else
    byte   buffer[MAX_DIGEST_SIZE];
#endif

    hLen = GetDigestSize(hashType);
    if (hLen < 0)
        return BAD_FUNC_ARG;

#ifdef WOLFSSL_SMALL_STACK
    buffer = (byte*)XMALLOC(MAX_DIGEST_SIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (buffer == NULL)
        return MEMORY_E;
#endif

    ret = wc_HmacSetKey(&hmac, hashType, passwd, pLen);

    if (ret == 0) {
        while (kLen) {
            int currentLen;

            ret = wc_HmacUpdate(&hmac, salt, sLen);
            if (ret != 0)
                break;

            /* encode i */
            for (j = 0; j < 4; j++) {
                byte b = (byte)(i >> ((3-j) * 8));

                ret = wc_HmacUpdate(&hmac, &b, 1);
                if (ret != 0)
                    break;
            }

            /* check ret from inside for loop */
            if (ret != 0)
                break;

            ret = wc_HmacFinal(&hmac, buffer);
            if (ret != 0)
                break;

            currentLen = min(kLen, hLen);
            XMEMCPY(output, buffer, currentLen);

            for (j = 1; j < iterations; j++) {
                ret = wc_HmacUpdate(&hmac, buffer, hLen);
                if (ret != 0)
                    break;
                ret = wc_HmacFinal(&hmac, buffer);
                if (ret != 0)
                    break;
                xorbuf(output, buffer, currentLen);
            }

            /* check ret from inside for loop */
            if (ret != 0)
                break;

            output += currentLen;
            kLen   -= currentLen;
            i++;
        }
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(buffer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

#ifdef WOLFSSL_SHA512
    #define PBKDF_DIGEST_SIZE SHA512_BLOCK_SIZE
#elif !defined(NO_SHA256)
    #define PBKDF_DIGEST_SIZE SHA256_BLOCK_SIZE
#else
    #define PBKDF_DIGEST_SIZE SHA_DIGEST_SIZE
#endif

/* helper for wc_PKCS12_PBKDF(), sets block and digest sizes */
int GetPKCS12HashSizes(int hashType, word32* v, word32* u)
{
    if (!v || !u)
        return BAD_FUNC_ARG;

    switch (hashType) {
#ifndef NO_MD5
        case MD5:
            *v = MD5_BLOCK_SIZE;
            *u = MD5_DIGEST_SIZE;
            break;
#endif
#ifndef NO_SHA
        case SHA:
            *v = SHA_BLOCK_SIZE;
            *u = SHA_DIGEST_SIZE;
            break;
#endif
#ifndef NO_SHA256
        case SHA256:
            *v = SHA256_BLOCK_SIZE;
            *u = SHA256_DIGEST_SIZE;
            break;
#endif
#ifdef WOLFSSL_SHA512
        case SHA512:
            *v = SHA512_BLOCK_SIZE;
            *u = SHA512_DIGEST_SIZE;
            break;
#endif
        default:
            return BAD_FUNC_ARG;
    }

    return 0;
}

/* helper for PKCS12_PBKDF(), does hash operation */
int DoPKCS12Hash(int hashType, byte* buffer, word32 totalLen,
                 byte* Ai, word32 u, int iterations)
{
    int i;
    int ret = 0;

    if (buffer == NULL || Ai == NULL)
        return BAD_FUNC_ARG;

    switch (hashType) {
#ifndef NO_MD5
        case MD5:
            {
                Md5 md5;
                wc_InitMd5(&md5);
                wc_Md5Update(&md5, buffer, totalLen);
                wc_Md5Final(&md5, Ai);

                for (i = 1; i < iterations; i++) {
                    wc_Md5Update(&md5, Ai, u);
                    wc_Md5Final(&md5, Ai);
                }
            }
            break;
#endif /* NO_MD5 */
#ifndef NO_SHA
        case SHA:
            {
                Sha sha;
                ret = wc_InitSha(&sha);
                if (ret != 0)
                    break;
                wc_ShaUpdate(&sha, buffer, totalLen);
                wc_ShaFinal(&sha, Ai);

                for (i = 1; i < iterations; i++) {
                    wc_ShaUpdate(&sha, Ai, u);
                    wc_ShaFinal(&sha, Ai);
                }
            }
            break;
#endif /* NO_SHA */
#ifndef NO_SHA256
        case SHA256:
            {
                Sha256 sha256;
                ret = wc_InitSha256(&sha256);
                if (ret != 0)
                    break;

                ret = wc_Sha256Update(&sha256, buffer, totalLen);
                if (ret != 0)
                    break;

                ret = wc_Sha256Final(&sha256, Ai);
                if (ret != 0)
                    break;

                for (i = 1; i < iterations; i++) {
                    ret = wc_Sha256Update(&sha256, Ai, u);
                    if (ret != 0)
                        break;

                    ret = wc_Sha256Final(&sha256, Ai);
                    if (ret != 0)
                        break;
                }
            }
            break;
#endif /* NO_SHA256 */
#ifdef WOLFSSL_SHA512
        case SHA512:
            {
                Sha512 sha512;
                ret = wc_InitSha512(&sha512);
                if (ret != 0)
                    break;

                ret = wc_Sha512Update(&sha512, buffer, totalLen);
                if (ret != 0)
                    break;

                ret = wc_Sha512Final(&sha512, Ai);
                if (ret != 0)
                    break;

                for (i = 1; i < iterations; i++) {
                    ret = wc_Sha512Update(&sha512, Ai, u);
                    if (ret != 0)
                        break;

                    ret = wc_Sha512Final(&sha512, Ai);
                    if (ret != 0)
                        break;
                }
            }
            break;
#endif /* WOLFSSL_SHA512 */

        default:
            ret = BAD_FUNC_ARG;
            break;
    }

    return ret;
}

int wc_PKCS12_PBKDF(byte* output, const byte* passwd, int passLen,const byte* salt,
                 int saltLen, int iterations, int kLen, int hashType, int id)
{
    /* all in bytes instead of bits */
    word32 u, v, dLen, pLen, iLen, sLen, totalLen;
    int    dynamic = 0;
    int    ret = 0;
    int    i;
    byte   *D, *S, *P, *I;
#ifdef WOLFSSL_SMALL_STACK
    byte   staticBuffer[1]; /* force dynamic usage */
#else
    byte   staticBuffer[1024];
#endif
    byte*  buffer = staticBuffer;

#ifdef WOLFSSL_SMALL_STACK
    byte*  Ai;
    byte*  B;
#else
    byte   Ai[PBKDF_DIGEST_SIZE];
    byte   B[PBKDF_DIGEST_SIZE];
#endif

    if (!iterations)
        iterations = 1;

    ret = GetPKCS12HashSizes(hashType, &v, &u);
    if (ret < 0)
        return BAD_FUNC_ARG;

#ifdef WOLFSSL_SMALL_STACK
    Ai = (byte*)XMALLOC(PBKDF_DIGEST_SIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (Ai == NULL)
        return MEMORY_E;

    B = (byte*)XMALLOC(PBKDF_DIGEST_SIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (B == NULL) {
        XFREE(Ai, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
#endif

    XMEMSET(Ai, 0, PBKDF_DIGEST_SIZE);
    XMEMSET(B,  0, PBKDF_DIGEST_SIZE);

    dLen = v;
    sLen =  v * ((saltLen + v - 1) / v);
    if (passLen)
        pLen = v * ((passLen + v - 1) / v);
    else
        pLen = 0;
    iLen = sLen + pLen;

    totalLen = dLen + sLen + pLen;

    if (totalLen > sizeof(staticBuffer)) {
        buffer = (byte*)XMALLOC(totalLen, 0, DYNAMIC_TYPE_KEY);
        if (buffer == NULL) {
#ifdef WOLFSSL_SMALL_STACK
            XFREE(Ai, NULL, DYNAMIC_TYPE_TMP_BUFFER);
            XFREE(B,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
            return MEMORY_E;
        }
        dynamic = 1;
    }

    D = buffer;
    S = D + dLen;
    P = S + sLen;
    I = S;

    XMEMSET(D, id, dLen);

    for (i = 0; i < (int)sLen; i++)
        S[i] = salt[i % saltLen];
    for (i = 0; i < (int)pLen; i++)
        P[i] = passwd[i % passLen];

    while (kLen > 0) {
        word32 currentLen;
        mp_int B1;

        ret = DoPKCS12Hash(hashType, buffer, totalLen, Ai, u, iterations);
        if (ret < 0)
            break;

        for (i = 0; i < (int)v; i++)
            B[i] = Ai[i % u];

        if (mp_init(&B1) != MP_OKAY)
            ret = MP_INIT_E;
        else if (mp_read_unsigned_bin(&B1, B, v) != MP_OKAY)
            ret = MP_READ_E;
        else if (mp_add_d(&B1, (mp_digit)1, &B1) != MP_OKAY)
            ret = MP_ADD_E;

        if (ret != 0) {
            mp_clear(&B1);
            break;
        }

        for (i = 0; i < (int)iLen; i += v) {
            int    outSz;
            mp_int i1;
            mp_int res;

            if (mp_init_multi(&i1, &res, NULL, NULL, NULL, NULL) != MP_OKAY) {
                ret = MP_INIT_E;
                break;
            }
            if (mp_read_unsigned_bin(&i1, I + i, v) != MP_OKAY)
                ret = MP_READ_E;
            else if (mp_add(&i1, &B1, &res) != MP_OKAY)
                ret = MP_ADD_E;
            else if ( (outSz = mp_unsigned_bin_size(&res)) < 0)
                ret = MP_TO_E;
            else {
                if (outSz > (int)v) {
                    /* take off MSB */
                    byte  tmp[129];
                    ret = mp_to_unsigned_bin(&res, tmp);
                    XMEMCPY(I + i, tmp + 1, v);
                }
                else if (outSz < (int)v) {
                    XMEMSET(I + i, 0, v - outSz);
                    ret = mp_to_unsigned_bin(&res, I + i + v - outSz);
                }
                else
                    ret = mp_to_unsigned_bin(&res, I + i);
            }

            mp_clear(&i1);
            mp_clear(&res);
            if (ret < 0) break;
        }

        currentLen = min(kLen, (int)u);
        XMEMCPY(output, Ai, currentLen);
        output += currentLen;
        kLen   -= currentLen;
        mp_clear(&B1);
    }

    if (dynamic) XFREE(buffer, 0, DYNAMIC_TYPE_KEY);

#ifdef WOLFSSL_SMALL_STACK
    XFREE(Ai, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(B,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

#undef PBKDF_DIGEST_SIZE

#endif /* NO_PWDBASED */

