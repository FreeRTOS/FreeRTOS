/* pwdbased.c
 *
 * Copyright (C) 2006-2014 wolfSSL Inc.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
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

#include <cyassl/ctaocrypt/settings.h>

#ifndef NO_PWDBASED

#ifdef CYASSL_PIC32MZ_HASH

#define InitMd5   InitMd5_sw
#define Md5Update Md5Update_sw
#define Md5Final  Md5Final_sw

#define InitSha   InitSha_sw
#define ShaUpdate ShaUpdate_sw
#define ShaFinal  ShaFinal_sw

#define InitSha256   InitSha256_sw
#define Sha256Update Sha256Update_sw
#define Sha256Final  Sha256Final_sw

#endif

#include <cyassl/ctaocrypt/pwdbased.h>
#include <cyassl/ctaocrypt/hmac.h>
#include <cyassl/ctaocrypt/integer.h>
#include <cyassl/ctaocrypt/error-crypt.h>
#if defined(CYASSL_SHA512) || defined(CYASSL_SHA384)
    #include <cyassl/ctaocrypt/sha512.h>
#endif

#ifdef NO_INLINE
    #include <cyassl/ctaocrypt/misc.h>
#else
    #include <ctaocrypt/src/misc.c>
#endif


#ifndef min

    static INLINE word32 min(word32 a, word32 b)
    {
        return a > b ? b : a;
    }

#endif /* min */


int PBKDF1(byte* output, const byte* passwd, int pLen, const byte* salt,
           int sLen, int iterations, int kLen, int hashType)
{
    Md5  md5;
    Sha  sha;
    int  hLen = (hashType == MD5) ? (int)MD5_DIGEST_SIZE : (int)SHA_DIGEST_SIZE;
    int  i, ret = 0;
    byte buffer[SHA_DIGEST_SIZE];  /* max size */

    if (hashType != MD5 && hashType != SHA)
        return BAD_FUNC_ARG;

    if (kLen > hLen)
        return BAD_FUNC_ARG;

    if (iterations < 1)
        return BAD_FUNC_ARG;

    if (hashType == MD5) {
        InitMd5(&md5);
        Md5Update(&md5, passwd, pLen);
        Md5Update(&md5, salt,   sLen);
        Md5Final(&md5,  buffer);
    }
    else {
        ret = InitSha(&sha);
        if (ret != 0)
            return ret;
        ShaUpdate(&sha, passwd, pLen);
        ShaUpdate(&sha, salt,   sLen);
        ShaFinal(&sha,  buffer);
    }

    for (i = 1; i < iterations; i++) {
        if (hashType == MD5) {
            Md5Update(&md5, buffer, hLen);
            Md5Final(&md5,  buffer);
        }
        else {
            ShaUpdate(&sha, buffer, hLen);
            ShaFinal(&sha,  buffer);
        }
    }
    XMEMCPY(output, buffer, kLen);

    return 0;
}


int PBKDF2(byte* output, const byte* passwd, int pLen, const byte* salt,
           int sLen, int iterations, int kLen, int hashType)
{
    word32 i = 1;
    int    hLen;
    int    j, ret;
    Hmac   hmac;
#ifdef CYASSL_SMALL_STACK
    byte*  buffer;
#else
    byte   buffer[MAX_DIGEST_SIZE];
#endif

    if (hashType == MD5) {
        hLen = MD5_DIGEST_SIZE;
    }
    else if (hashType == SHA) {
        hLen = SHA_DIGEST_SIZE;
    }
#ifndef NO_SHA256
    else if (hashType == SHA256) {
        hLen = SHA256_DIGEST_SIZE;
    }
#endif
#ifdef CYASSL_SHA512
    else if (hashType == SHA512) {
        hLen = SHA512_DIGEST_SIZE;
    }
#endif
    else
        return BAD_FUNC_ARG;

#ifdef CYASSL_SMALL_STACK
    buffer = (byte*)XMALLOC(MAX_DIGEST_SIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (buffer == NULL)
        return MEMORY_E;
#endif

    ret = HmacSetKey(&hmac, hashType, passwd, pLen);

    if (ret == 0) {
        while (kLen) {
            int currentLen;

            ret = HmacUpdate(&hmac, salt, sLen);
            if (ret != 0)
                break;

            /* encode i */
            for (j = 0; j < 4; j++) {
                byte b = (byte)(i >> ((3-j) * 8));

                ret = HmacUpdate(&hmac, &b, 1);
                if (ret != 0)
                    break;
            }

            /* check ret from inside for loop */
            if (ret != 0)
                break;

            ret = HmacFinal(&hmac, buffer);
            if (ret != 0)
                break;

            currentLen = min(kLen, hLen);
            XMEMCPY(output, buffer, currentLen);

            for (j = 1; j < iterations; j++) {
                ret = HmacUpdate(&hmac, buffer, hLen);
                if (ret != 0)
                    break;
                ret = HmacFinal(&hmac, buffer);
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

#ifdef CYASSL_SMALL_STACK
    XFREE(buffer, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

#ifdef CYASSL_SHA512
#define PBKDF_DIGEST_SIZE SHA512_BLOCK_SIZE
#elif !defined(NO_SHA256)
#define PBKDF_DIGEST_SIZE SHA256_BLOCK_SIZE
#else
#define PBKDF_DIGEST_SIZE SHA_DIGEST_SIZE
#endif

int PKCS12_PBKDF(byte* output, const byte* passwd, int passLen,const byte* salt,
                 int saltLen, int iterations, int kLen, int hashType, int id)
{
    /* all in bytes instead of bits */
    word32 u, v, dLen, pLen, iLen, sLen, totalLen;
    int    dynamic = 0;
    int    ret = 0;
    int    i;
    byte   *D, *S, *P, *I;
#ifdef CYASSL_SMALL_STACK
    byte   staticBuffer[1]; /* force dynamic usage */
#else
    byte   staticBuffer[1024];
#endif
    byte*  buffer = staticBuffer;

#ifdef CYASSL_SMALL_STACK
    byte*  Ai;
    byte*  B;
#else
    byte   Ai[PBKDF_DIGEST_SIZE];
    byte   B[PBKDF_DIGEST_SIZE];
#endif

    if (!iterations)
        iterations = 1;

    if (hashType == MD5) {
        v = MD5_BLOCK_SIZE;
        u = MD5_DIGEST_SIZE;
    }
    else if (hashType == SHA) {
        v = SHA_BLOCK_SIZE;
        u = SHA_DIGEST_SIZE;
    }
#ifndef NO_SHA256
    else if (hashType == SHA256) {
        v = SHA256_BLOCK_SIZE;
        u = SHA256_DIGEST_SIZE;
    }
#endif
#ifdef CYASSL_SHA512
    else if (hashType == SHA512) {
        v = SHA512_BLOCK_SIZE;
        u = SHA512_DIGEST_SIZE;
    }
#endif
    else
        return BAD_FUNC_ARG;

#ifdef CYASSL_SMALL_STACK
    Ai = (byte*)XMALLOC(PBKDF_DIGEST_SIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (Ai == NULL)
        return MEMORY_E;

    B = (byte*)XMALLOC(PBKDF_DIGEST_SIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (B == NULL) {
        XFREE(Ai, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
#endif

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
#ifdef CYASSL_SMALL_STACK
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

        if (hashType == MD5) {
            Md5 md5;

            InitMd5(&md5);
            Md5Update(&md5, buffer, totalLen);
            Md5Final(&md5, Ai);

            for (i = 1; i < iterations; i++) {
                Md5Update(&md5, Ai, u);
                Md5Final(&md5, Ai);
            }
        }
        else if (hashType == SHA) {
            Sha sha;

            ret = InitSha(&sha);
            if (ret != 0)
                break;
            ShaUpdate(&sha, buffer, totalLen);
            ShaFinal(&sha, Ai);

            for (i = 1; i < iterations; i++) {
                ShaUpdate(&sha, Ai, u);
                ShaFinal(&sha, Ai);
            }
        }
#ifndef NO_SHA256
        else if (hashType == SHA256) {
            Sha256 sha256;

            ret = InitSha256(&sha256);
            if (ret != 0)
                break;

            ret = Sha256Update(&sha256, buffer, totalLen);
            if (ret != 0)
                break;

            ret = Sha256Final(&sha256, Ai);
            if (ret != 0)
                break;

            for (i = 1; i < iterations; i++) {
                ret = Sha256Update(&sha256, Ai, u);
                if (ret != 0)
                    break;

                ret = Sha256Final(&sha256, Ai);
                if (ret != 0)
                    break;
            }
        }
#endif
#ifdef CYASSL_SHA512
        else if (hashType == SHA512) {
            Sha512 sha512;

            ret = InitSha512(&sha512);
            if (ret != 0)
                break;

            ret = Sha512Update(&sha512, buffer, totalLen);
            if (ret != 0)
                break;

            ret = Sha512Final(&sha512, Ai);
            if (ret != 0)
                break;

            for (i = 1; i < iterations; i++) {
                ret = Sha512Update(&sha512, Ai, u);
                if (ret != 0)
                    break;

                ret = Sha512Final(&sha512, Ai);
                if (ret != 0)
                    break;
            }
        }
#endif

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

#ifdef CYASSL_SMALL_STACK
    XFREE(Ai, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(B,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

#undef PBKDF_DIGEST_SIZE

#endif /* NO_PWDBASED */

