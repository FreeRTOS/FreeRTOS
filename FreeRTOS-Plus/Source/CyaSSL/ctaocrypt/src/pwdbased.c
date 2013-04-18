/* pwdbased.c
 *
 * Copyright (C) 2006-2012 Sawtooth Consulting Ltd.
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
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#ifndef NO_PWDBASED

#include <cyassl/ctaocrypt/pwdbased.h>
#include <cyassl/ctaocrypt/hmac.h>
#include <cyassl/ctaocrypt/integer.h>
#include <cyassl/ctaocrypt/error.h>
#ifdef CYASSL_SHA512
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
    int  hLen = (hashType == MD5) ? MD5_DIGEST_SIZE : SHA_DIGEST_SIZE;
    int  i;
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
        InitSha(&sha);
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
    int    j;
    Hmac   hmac;
    byte   buffer[INNER_HASH_SIZE];  /* max size */

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

    HmacSetKey(&hmac, hashType, passwd, pLen);

    while (kLen) {
        int currentLen;
        HmacUpdate(&hmac, salt, sLen);

        /* encode i */
        for (j = 0; j < 4; j++) {
            byte b = (byte)(i >> ((3-j) * 8));
            HmacUpdate(&hmac, &b, 1);
        }
        HmacFinal(&hmac, buffer);

        currentLen = min(kLen, hLen);
        XMEMCPY(output, buffer, currentLen);

        for (j = 1; j < iterations; j++) {
            HmacUpdate(&hmac, buffer, hLen);
            HmacFinal(&hmac, buffer);
            xorbuf(output, buffer, currentLen);
        }

        output += currentLen;
        kLen   -= currentLen;
        i++;
    }

    return 0;
}


int PKCS12_PBKDF(byte* output, const byte* passwd, int passLen,const byte* salt,
                 int saltLen, int iterations, int kLen, int hashType, int id)
{
    /* all in bytes instead of bits */
    word32 u, v, dLen, pLen, iLen, sLen, totalLen;
    int    dynamic = 0;
    int    ret = 0;
    int    i;
    byte   *D, *S, *P, *I;
    byte   staticBuffer[1024];
    byte*  buffer = staticBuffer;
#ifdef CYASSL_SHA512
    byte   Ai[SHA512_DIGEST_SIZE];
    byte   B[SHA512_BLOCK_SIZE];
#elif !defined(NO_SHA256)
    byte   Ai[SHA256_DIGEST_SIZE];
    byte   B[SHA256_BLOCK_SIZE];
#else
    byte   Ai[SHA_DIGEST_SIZE];
    byte   B[SHA_BLOCK_SIZE];
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
        if (buffer == NULL) return MEMORY_E;
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
        }
        else if (hashType == SHA) {
            Sha sha;

            InitSha(&sha);
            ShaUpdate(&sha, buffer, totalLen);
            ShaFinal(&sha, Ai);

            for (i = 1; i < iterations; i++) {
                ShaUpdate(&sha, Ai, u);
                ShaFinal(&sha, Ai);
            }
        }
#ifndef NO_SHA256
        else if (hashType == SHA256) {
        }
#endif
#ifdef CYASSL_SHA512
        else if (hashType == SHA512) {
        }
#endif

        for (i = 0; i < (int)v; i++)
            B[i] = Ai[i % u];

        mp_init(&B1);
        if (mp_read_unsigned_bin(&B1, B, v) != MP_OKAY)
            ret = MP_READ_E;
        else if (mp_add_d(&B1, (mp_digit)1, &B1) != MP_OKAY) {
            ret = MP_ADD_E;
            mp_clear(&B1);
            break;
        }

        for (i = 0; i < (int)iLen; i += v) {
            int    outSz;
            mp_int i1;
            mp_int res;

            mp_init(&i1);
            mp_init(&res);

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
                    mp_to_unsigned_bin(&res, tmp);
                    XMEMCPY(I + i, tmp + 1, v);
                }
                else if (outSz < (int)v) {
                    XMEMSET(I + i, 0, v - outSz);
                    mp_to_unsigned_bin(&res, I + i + v - outSz);
                }
                else
                    mp_to_unsigned_bin(&res, I + i);
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
    return ret;
}

#endif /* NO_PWDBASED */

