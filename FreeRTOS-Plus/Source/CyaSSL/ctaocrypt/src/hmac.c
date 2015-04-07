/* hmac.c
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

#ifndef NO_HMAC

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

#ifdef HAVE_FIPS
    /* set NO_WRAPPERS before headers, use direct internal f()s not wrappers */
    #define FIPS_NO_WRAPPERS
#endif

#include <cyassl/ctaocrypt/hmac.h>
#include <cyassl/ctaocrypt/error-crypt.h>


#ifdef HAVE_CAVIUM
    static void HmacCaviumFinal(Hmac* hmac, byte* hash);
    static void HmacCaviumUpdate(Hmac* hmac, const byte* msg, word32 length);
    static void HmacCaviumSetKey(Hmac* hmac, int type, const byte* key,
                                 word32 length);
#endif

static int InitHmac(Hmac* hmac, int type)
{
    int ret = 0;

    hmac->innerHashKeyed = 0;
    hmac->macType = (byte)type;

    if (!(type == MD5 || type == SHA    || type == SHA256 || type == SHA384
                      || type == SHA512 || type == BLAKE2B_ID))
        return BAD_FUNC_ARG;

    switch (type) {
        #ifndef NO_MD5
        case MD5:
            InitMd5(&hmac->hash.md5);
        break;
        #endif

        #ifndef NO_SHA
        case SHA:
            ret = InitSha(&hmac->hash.sha);
        break;
        #endif
        
        #ifndef NO_SHA256
        case SHA256:
            ret = InitSha256(&hmac->hash.sha256);
        break;
        #endif
        
        #ifdef CYASSL_SHA384
        case SHA384:
            ret = InitSha384(&hmac->hash.sha384);
        break;
        #endif
        
        #ifdef CYASSL_SHA512
        case SHA512:
            ret = InitSha512(&hmac->hash.sha512);
        break;
        #endif
        
        #ifdef HAVE_BLAKE2 
        case BLAKE2B_ID:
            ret = InitBlake2b(&hmac->hash.blake2b, BLAKE2B_256);
        break;
        #endif
        
        default:
            return BAD_FUNC_ARG;
    }

    return ret;
}


int HmacSetKey(Hmac* hmac, int type, const byte* key, word32 length)
{
    byte*  ip = (byte*) hmac->ipad;
    byte*  op = (byte*) hmac->opad;
    word32 i, hmac_block_size = 0;
    int    ret;

#ifdef HAVE_CAVIUM
    if (hmac->magic == CYASSL_HMAC_CAVIUM_MAGIC)
        return HmacCaviumSetKey(hmac, type, key, length);
#endif

    ret = InitHmac(hmac, type);
    if (ret != 0)
        return ret;

#ifdef HAVE_FIPS
    if (length < HMAC_FIPS_MIN_KEY)
        return HMAC_MIN_KEYLEN_E;
#endif

    switch (hmac->macType) {
        #ifndef NO_MD5
        case MD5:
        {
            hmac_block_size = MD5_BLOCK_SIZE;
            if (length <= MD5_BLOCK_SIZE) {
                XMEMCPY(ip, key, length);
            }
            else {
                Md5Update(&hmac->hash.md5, key, length);
                Md5Final(&hmac->hash.md5, ip);
                length = MD5_DIGEST_SIZE;
            }
        }
        break;
        #endif

        #ifndef NO_SHA
        case SHA:
        {
            hmac_block_size = SHA_BLOCK_SIZE;
            if (length <= SHA_BLOCK_SIZE) {
                XMEMCPY(ip, key, length);
            }
            else {
                ShaUpdate(&hmac->hash.sha, key, length);
                ShaFinal(&hmac->hash.sha, ip);
                length = SHA_DIGEST_SIZE;
            }
        }
        break;
        #endif

        #ifndef NO_SHA256
        case SHA256:
        {
    		hmac_block_size = SHA256_BLOCK_SIZE;
            if (length <= SHA256_BLOCK_SIZE) {
                XMEMCPY(ip, key, length);
            }
            else {
                ret = Sha256Update(&hmac->hash.sha256, key, length);
                if (ret != 0)
                    return ret;

                ret = Sha256Final(&hmac->hash.sha256, ip);
                if (ret != 0)
                    return ret;

                length = SHA256_DIGEST_SIZE;
            }
        }
        break;
        #endif

        #ifdef CYASSL_SHA384
        case SHA384:
        {
            hmac_block_size = SHA384_BLOCK_SIZE;
            if (length <= SHA384_BLOCK_SIZE) {
                XMEMCPY(ip, key, length);
            }
            else {
                ret = Sha384Update(&hmac->hash.sha384, key, length);
                if (ret != 0)
                    return ret;

                ret = Sha384Final(&hmac->hash.sha384, ip);
                if (ret != 0)
                    return ret;

                length = SHA384_DIGEST_SIZE;
            }
        }
        break;
        #endif

        #ifdef CYASSL_SHA512
        case SHA512:
        {
            hmac_block_size = SHA512_BLOCK_SIZE;
            if (length <= SHA512_BLOCK_SIZE) {
                XMEMCPY(ip, key, length);
            }
            else {
                ret = Sha512Update(&hmac->hash.sha512, key, length);
                if (ret != 0)
                    return ret;

                ret = Sha512Final(&hmac->hash.sha512, ip);
                if (ret != 0)
                    return ret;

                length = SHA512_DIGEST_SIZE;
            }
        }
        break;
        #endif

        #ifdef HAVE_BLAKE2 
        case BLAKE2B_ID:
        {
            hmac_block_size = BLAKE2B_BLOCKBYTES;
            if (length <= BLAKE2B_BLOCKBYTES) {
                XMEMCPY(ip, key, length);
            }
            else {
                ret = Blake2bUpdate(&hmac->hash.blake2b, key, length);
                if (ret != 0)
                    return ret;

                ret = Blake2bFinal(&hmac->hash.blake2b, ip, BLAKE2B_256);
                if (ret != 0)
                    return ret;

                length = BLAKE2B_256;
            }
        }
        break;
        #endif

        default:
            return BAD_FUNC_ARG;
    }
    if (length < hmac_block_size)
        XMEMSET(ip + length, 0, hmac_block_size - length);

    for(i = 0; i < hmac_block_size; i++) {
        op[i] = ip[i] ^ OPAD;
        ip[i] ^= IPAD;
    }
    return 0;
}


static int HmacKeyInnerHash(Hmac* hmac)
{
    int ret = 0;

    switch (hmac->macType) {
        #ifndef NO_MD5
        case MD5:
            Md5Update(&hmac->hash.md5, (byte*) hmac->ipad, MD5_BLOCK_SIZE);
        break;
        #endif

        #ifndef NO_SHA
        case SHA:
            ShaUpdate(&hmac->hash.sha, (byte*) hmac->ipad, SHA_BLOCK_SIZE);
        break;
        #endif

        #ifndef NO_SHA256
        case SHA256:
            ret = Sha256Update(&hmac->hash.sha256,
                                         (byte*) hmac->ipad, SHA256_BLOCK_SIZE);
            if (ret != 0)
                return ret;
        break;
        #endif

        #ifdef CYASSL_SHA384
        case SHA384:
            ret = Sha384Update(&hmac->hash.sha384,
                                         (byte*) hmac->ipad, SHA384_BLOCK_SIZE);
            if (ret != 0)
                return ret;
        break;
        #endif

        #ifdef CYASSL_SHA512
        case SHA512:
            ret = Sha512Update(&hmac->hash.sha512,
                                         (byte*) hmac->ipad, SHA512_BLOCK_SIZE);
            if (ret != 0)
                return ret;
        break;
        #endif

        #ifdef HAVE_BLAKE2 
        case BLAKE2B_ID:
            ret = Blake2bUpdate(&hmac->hash.blake2b,
                                         (byte*) hmac->ipad,BLAKE2B_BLOCKBYTES);
            if (ret != 0)
                return ret;
        break;
        #endif

        default:
        break;
    }

    hmac->innerHashKeyed = 1;

    return ret;
}


int HmacUpdate(Hmac* hmac, const byte* msg, word32 length)
{
    int ret;

#ifdef HAVE_CAVIUM
    if (hmac->magic == CYASSL_HMAC_CAVIUM_MAGIC)
        return HmacCaviumUpdate(hmac, msg, length);
#endif

    if (!hmac->innerHashKeyed) {
        ret = HmacKeyInnerHash(hmac);
        if (ret != 0)
            return ret;
    }

    switch (hmac->macType) {
        #ifndef NO_MD5
        case MD5:
            Md5Update(&hmac->hash.md5, msg, length);
        break;
        #endif

        #ifndef NO_SHA
        case SHA:
            ShaUpdate(&hmac->hash.sha, msg, length);
        break;
        #endif

        #ifndef NO_SHA256
        case SHA256:
            ret = Sha256Update(&hmac->hash.sha256, msg, length);
            if (ret != 0)
                return ret;
        break;
        #endif

        #ifdef CYASSL_SHA384
        case SHA384:
            ret = Sha384Update(&hmac->hash.sha384, msg, length);
            if (ret != 0)
                return ret;
        break;
        #endif

        #ifdef CYASSL_SHA512
        case SHA512:
            ret = Sha512Update(&hmac->hash.sha512, msg, length);
            if (ret != 0)
                return ret;
        break;
        #endif

        #ifdef HAVE_BLAKE2 
        case BLAKE2B_ID:
            ret = Blake2bUpdate(&hmac->hash.blake2b, msg, length);
            if (ret != 0)
                return ret;
        break;
        #endif

        default:
        break;
    }

    return 0;
}


int HmacFinal(Hmac* hmac, byte* hash)
{
    int ret;

#ifdef HAVE_CAVIUM
    if (hmac->magic == CYASSL_HMAC_CAVIUM_MAGIC)
        return HmacCaviumFinal(hmac, hash);
#endif

    if (!hmac->innerHashKeyed) {
        ret = HmacKeyInnerHash(hmac);
        if (ret != 0)
            return ret;
    }

    switch (hmac->macType) {
        #ifndef NO_MD5
        case MD5:
        {
            Md5Final(&hmac->hash.md5, (byte*) hmac->innerHash);

            Md5Update(&hmac->hash.md5, (byte*) hmac->opad, MD5_BLOCK_SIZE);
            Md5Update(&hmac->hash.md5,
                                     (byte*) hmac->innerHash, MD5_DIGEST_SIZE);

            Md5Final(&hmac->hash.md5, hash);
        }
        break;
        #endif

        #ifndef NO_SHA
        case SHA:
        {
            ShaFinal(&hmac->hash.sha, (byte*) hmac->innerHash);

            ShaUpdate(&hmac->hash.sha, (byte*) hmac->opad, SHA_BLOCK_SIZE);
            ShaUpdate(&hmac->hash.sha,
                                     (byte*) hmac->innerHash, SHA_DIGEST_SIZE);

            ShaFinal(&hmac->hash.sha, hash);
        }
        break;
        #endif

        #ifndef NO_SHA256
        case SHA256:
        {
            ret = Sha256Final(&hmac->hash.sha256, (byte*) hmac->innerHash);
            if (ret != 0)
                return ret;

            ret = Sha256Update(&hmac->hash.sha256,
                                (byte*) hmac->opad, SHA256_BLOCK_SIZE);
            if (ret != 0)
                return ret;

            ret = Sha256Update(&hmac->hash.sha256,
                                (byte*) hmac->innerHash, SHA256_DIGEST_SIZE);
            if (ret != 0)
                return ret;

            ret = Sha256Final(&hmac->hash.sha256, hash);
            if (ret != 0)
                return ret;
        }
        break;
        #endif

        #ifdef CYASSL_SHA384
        case SHA384:
        {
            ret = Sha384Final(&hmac->hash.sha384, (byte*) hmac->innerHash);
            if (ret != 0)
                return ret;

            ret = Sha384Update(&hmac->hash.sha384,
                                 (byte*) hmac->opad, SHA384_BLOCK_SIZE);
            if (ret != 0)
                return ret;

            ret = Sha384Update(&hmac->hash.sha384,
                                 (byte*) hmac->innerHash, SHA384_DIGEST_SIZE);
            if (ret != 0)
                return ret;

            ret = Sha384Final(&hmac->hash.sha384, hash);
            if (ret != 0)
                return ret;
        }
        break;
        #endif

        #ifdef CYASSL_SHA512
        case SHA512:
        {
            ret = Sha512Final(&hmac->hash.sha512, (byte*) hmac->innerHash);
            if (ret != 0)
                return ret;

            ret = Sha512Update(&hmac->hash.sha512,
                                 (byte*) hmac->opad, SHA512_BLOCK_SIZE);
            if (ret != 0)
                return ret;

            ret = Sha512Update(&hmac->hash.sha512,
                                 (byte*) hmac->innerHash, SHA512_DIGEST_SIZE);
            if (ret != 0)
                return ret;

            ret = Sha512Final(&hmac->hash.sha512, hash);
            if (ret != 0)
                return ret;
        }
        break;
        #endif

        #ifdef HAVE_BLAKE2 
        case BLAKE2B_ID:
        {
            ret = Blake2bFinal(&hmac->hash.blake2b, (byte*) hmac->innerHash,
                         BLAKE2B_256);
            if (ret != 0)
                return ret;

            ret = Blake2bUpdate(&hmac->hash.blake2b,
                                 (byte*) hmac->opad, BLAKE2B_BLOCKBYTES);
            if (ret != 0)
                return ret;

            ret = Blake2bUpdate(&hmac->hash.blake2b,
                                 (byte*) hmac->innerHash, BLAKE2B_256);
            if (ret != 0)
                return ret;

            ret = Blake2bFinal(&hmac->hash.blake2b, hash, BLAKE2B_256);
            if (ret != 0)
                return ret;
        }
        break;
        #endif

        default:
        break;
    }

    hmac->innerHashKeyed = 0;

    return 0;
}


#ifdef HAVE_CAVIUM

/* Initiliaze Hmac for use with Nitrox device */
int HmacInitCavium(Hmac* hmac, int devId)
{
    if (hmac == NULL)
        return -1;

    if (CspAllocContext(CONTEXT_SSL, &hmac->contextHandle, devId) != 0)
        return -1;

    hmac->keyLen  = 0;
    hmac->dataLen = 0;
    hmac->type    = 0;
    hmac->devId   = devId;
    hmac->magic   = CYASSL_HMAC_CAVIUM_MAGIC;
    hmac->data    = NULL;        /* buffered input data */
   
    hmac->innerHashKeyed = 0;

    return 0;
}


/* Free Hmac from use with Nitrox device */
void HmacFreeCavium(Hmac* hmac)
{
    if (hmac == NULL)
        return;

    CspFreeContext(CONTEXT_SSL, hmac->contextHandle, hmac->devId);
    hmac->magic = 0;
    XFREE(hmac->data, NULL, DYNAMIC_TYPE_CAVIUM_TMP);
    hmac->data = NULL;
}


static void HmacCaviumFinal(Hmac* hmac, byte* hash)
{
    word32 requestId;

    if (CspHmac(CAVIUM_BLOCKING, hmac->type, NULL, hmac->keyLen,
                (byte*)hmac->ipad, hmac->dataLen, hmac->data, hash, &requestId,
                hmac->devId) != 0) {
        CYASSL_MSG("Cavium Hmac failed");
    } 
    hmac->innerHashKeyed = 0;  /* tell update to start over if used again */
}


static void HmacCaviumUpdate(Hmac* hmac, const byte* msg, word32 length)
{
    word16 add = (word16)length;
    word32 total;
    byte*  tmp;

    if (length > CYASSL_MAX_16BIT) {
        CYASSL_MSG("Too big msg for cavium hmac");
        return;
    }

    if (hmac->innerHashKeyed == 0) {  /* starting new */
        hmac->dataLen        = 0;
        hmac->innerHashKeyed = 1;
    }

    total = add + hmac->dataLen;
    if (total > CYASSL_MAX_16BIT) {
        CYASSL_MSG("Too big msg for cavium hmac");
        return;
    }

    tmp = XMALLOC(hmac->dataLen + add, NULL,DYNAMIC_TYPE_CAVIUM_TMP);
    if (tmp == NULL) {
        CYASSL_MSG("Out of memory for cavium update");
        return;
    }
    if (hmac->dataLen)
        XMEMCPY(tmp, hmac->data,  hmac->dataLen);
    XMEMCPY(tmp + hmac->dataLen, msg, add);
        
    hmac->dataLen += add;
    XFREE(hmac->data, NULL, DYNAMIC_TYPE_CAVIUM_TMP);
    hmac->data = tmp;
}


static void HmacCaviumSetKey(Hmac* hmac, int type, const byte* key,
                             word32 length)
{
    hmac->macType = (byte)type;
    if (type == MD5)
        hmac->type = MD5_TYPE;
    else if (type == SHA)
        hmac->type = SHA1_TYPE;
    else if (type == SHA256)
        hmac->type = SHA256_TYPE;
    else  {
        CYASSL_MSG("unsupported cavium hmac type");
    }

    hmac->innerHashKeyed = 0;  /* should we key Startup flag */

    hmac->keyLen = (word16)length;
    /* store key in ipad */
    XMEMCPY(hmac->ipad, key, length);
}

#endif /* HAVE_CAVIUM */

int CyaSSL_GetHmacMaxSize(void)
{
    return MAX_DIGEST_SIZE;
}

#ifdef HAVE_HKDF

#ifndef min

    static INLINE word32 min(word32 a, word32 b)
    {
        return a > b ? b : a;
    }

#endif /* min */


static INLINE int GetHashSizeByType(int type)
{
    if (!(type == MD5 || type == SHA    || type == SHA256 || type == SHA384
                      || type == SHA512 || type == BLAKE2B_ID))
        return BAD_FUNC_ARG;

    switch (type) {
        #ifndef NO_MD5
        case MD5:
            return MD5_DIGEST_SIZE;
        break;
        #endif

        #ifndef NO_SHA
        case SHA:
            return SHA_DIGEST_SIZE;
        break;
        #endif
        
        #ifndef NO_SHA256
        case SHA256:
            return SHA256_DIGEST_SIZE;
        break;
        #endif
        
        #ifdef CYASSL_SHA384
        case SHA384:
            return SHA384_DIGEST_SIZE;
        break;
        #endif
        
        #ifdef CYASSL_SHA512
        case SHA512:
            return SHA512_DIGEST_SIZE;
        break;
        #endif
        
        #ifdef HAVE_BLAKE2 
        case BLAKE2B_ID:
            return BLAKE2B_OUTBYTES;
        break;
        #endif
        
        default:
            return BAD_FUNC_ARG;
        break;
    }
}


/* HMAC-KDF with hash type, optional salt and info, return 0 on success */
int HKDF(int type, const byte* inKey, word32 inKeySz,
                   const byte* salt,  word32 saltSz,
                   const byte* info,  word32 infoSz,
                   byte* out,         word32 outSz)
{
    Hmac   myHmac;
#ifdef CYASSL_SMALL_STACK
    byte* tmp;
    byte* prk;
#else
    byte   tmp[MAX_DIGEST_SIZE]; /* localSalt helper and T */
    byte   prk[MAX_DIGEST_SIZE];
#endif
    const  byte* localSalt;  /* either points to user input or tmp */
    int    hashSz = GetHashSizeByType(type);
    word32 outIdx = 0;
    byte   n = 0x1;
    int    ret;

    if (hashSz < 0)
        return BAD_FUNC_ARG;

#ifdef CYASSL_SMALL_STACK
    tmp = (byte*)XMALLOC(MAX_DIGEST_SIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (tmp == NULL)
        return MEMORY_E;

    prk = (byte*)XMALLOC(MAX_DIGEST_SIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (prk == NULL) {
        XFREE(tmp, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
#endif

    localSalt = salt;
    if (localSalt == NULL) {
        XMEMSET(tmp, 0, hashSz);
        localSalt = tmp;
        saltSz    = hashSz;
    }
    
    do {
    ret = HmacSetKey(&myHmac, type, localSalt, saltSz);
    if (ret != 0)
        break;
    ret = HmacUpdate(&myHmac, inKey, inKeySz);
    if (ret != 0)
        break;
    ret = HmacFinal(&myHmac,  prk);
    } while (0);

    if (ret == 0) {
        while (outIdx < outSz) {
            int    tmpSz = (n == 1) ? 0 : hashSz;
            word32 left = outSz - outIdx;

            ret = HmacSetKey(&myHmac, type, prk, hashSz);
            if (ret != 0)
                break;
            ret = HmacUpdate(&myHmac, tmp, tmpSz);
            if (ret != 0)
                break;
            ret = HmacUpdate(&myHmac, info, infoSz);
            if (ret != 0)
                break;
            ret = HmacUpdate(&myHmac, &n, 1);
            if (ret != 0)
                break;
            ret = HmacFinal(&myHmac, tmp);
            if (ret != 0)
                break;

            left = min(left, (word32)hashSz);
            XMEMCPY(out+outIdx, tmp, left);

            outIdx += hashSz;
            n++;
        }
    }

#ifdef CYASSL_SMALL_STACK
    XFREE(tmp, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(prk, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

#endif /* HAVE_HKDF */

#endif /* NO_HMAC */

