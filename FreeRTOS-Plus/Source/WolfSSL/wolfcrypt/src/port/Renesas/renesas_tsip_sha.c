/* renesas_tsip_sha.c
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
#include <string.h>
#include <stdio.h>

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif
#include <wolfssl/wolfcrypt/settings.h>

#if !defined(NO_SHA) || !defined(NO_SHA256)

#include <wolfssl/wolfcrypt/logging.h>

#if defined(WOLFSSL_RENESAS_TSIP_CRYPT)

#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/port/Renesas/renesas-tsip-crypt.h>

#if !defined(NO_SHA)
#include <wolfssl/wolfcrypt/sha.h>

static void TSIPHashFree(wolfssl_TSIP_Hash* hash)
{
    if (hash == NULL)
        return;
        
    if (hash->msg != NULL) {
        XFREE(hash->msg, hash->heap, DYNAMIC_TYPE_TMP_BUFFER);
        hash->msg = NULL;
    }
}

static int TSIPHashInit(wolfssl_TSIP_Hash* hash, void* heap, int devId,
    word32 sha_type)
{
    if (hash == NULL) {
        return BAD_FUNC_ARG;
    }
    
    (void)devId;
    XMEMSET(hash, 0, sizeof(wolfssl_TSIP_Hash));
    
    hash->heap = heap;
    hash->len  = 0;
    hash->used = 0;
    hash->msg  = NULL;
    hash->sha_type = sha_type;
    
    return 0;
}

static int TSIPHashUpdate(wolfssl_TSIP_Hash* hash, const byte* data, word32 sz)
{
    if (hash == NULL || (sz > 0 && data == NULL)) {
        return BAD_FUNC_ARG;
    }
    
    if (hash->len < hash->used + sz) {
        if (hash->msg == NULL) {
            hash->msg = (byte*)XMALLOC(hash->used + sz, hash->heap,
                    DYNAMIC_TYPE_TMP_BUFFER);
        } else {
#ifdef FREERTOS
            byte* pt = (byte*)XMALLOC(hash->used + sz, hash->heap,
                    DYNAMIC_TYPE_TMP_BUFFER);
            if (pt == NULL) {
                return MEMORY_E;
            }
            XMEMCPY(pt, hash->msg, hash->used);
            XFREE(hash->msg, hash->heap, DYNAMIC_TYPE_TMP_BUFFER);
            hash->msg = NULL;
            hash->msg = pt;
#else
            byte* pt = (byte*)XREALLOC(hash->msg, hash->used + sz, hash->heap,
                    DYNAMIC_TYPE_TMP_BUFFER);
            if (pt == NULL) {
                return MEMORY_E;
            }
            hash->msg = pt;
#endif
        }
        if (hash->msg == NULL) {
            return MEMORY_E;
        }
        hash->len = hash->used + sz;
    }
    XMEMCPY(hash->msg + hash->used, data , sz);
    hash->used += sz;
    
    return 0;
}

static int TSIPHashFinal(wolfssl_TSIP_Hash* hash, byte* out, word32 outSz)
{
    int ret;
    void* heap;
    tsip_sha_md5_handle_t handle;
    uint32_t sz;
    
    e_tsip_err_t (*Init)(tsip_sha_md5_handle_t*);
    e_tsip_err_t (*Update)(tsip_sha_md5_handle_t*, uint8_t*, uint32_t);
    e_tsip_err_t (*Final )(tsip_sha_md5_handle_t*, uint8_t*, uint32_t*);
    
    if (hash == NULL || out == NULL) {
        return BAD_FUNC_ARG;
    }
    
    if (hash->sha_type == TSIP_SHA1) {
        Init = R_TSIP_Sha1Init;
        Update = R_TSIP_Sha1Update;
        Final = R_TSIP_Sha1Final;
    } else if (hash->sha_type == TSIP_SHA256) {
        Init = R_TSIP_Sha256Init;
        Update = R_TSIP_Sha256Update;
        Final = R_TSIP_Sha256Final;
    } else 
        return BAD_FUNC_ARG;
    
    heap = hash->heap;
    
    tsip_hw_lock();
    
    if (Init(&handle) == TSIP_SUCCESS) {
        ret = Update(&handle, (uint8_t*)hash->msg, hash->used);
        if (ret == TSIP_SUCCESS) {
            ret = Final(&handle, out, (uint32_t*)&sz);
            if (ret != TSIP_SUCCESS || sz != outSz) {
                return ret;
            }
        }
    }
    tsip_hw_unlock();
    
    TSIPHashFree(hash);
    return TSIPHashInit(hash, heap, 0, hash->sha_type);
}

static int TSIPHashGet(wolfssl_TSIP_Hash* hash, byte* out, word32 outSz)
{
    int ret;
    tsip_sha_md5_handle_t handle;
    uint32_t sz;
    
    e_tsip_err_t (*Init)(tsip_sha_md5_handle_t*);
    e_tsip_err_t (*Update)(tsip_sha_md5_handle_t*, uint8_t*, uint32_t);
    e_tsip_err_t (*Final )(tsip_sha_md5_handle_t*, uint8_t*, uint32_t*);
    
    if (hash == NULL || out == NULL) {
        return BAD_FUNC_ARG;
    }
    
    if (hash->sha_type == TSIP_SHA1) {
        Init = R_TSIP_Sha1Init;
        Update = R_TSIP_Sha1Update;
        Final = R_TSIP_Sha1Final;
    } else if (hash->sha_type == TSIP_SHA256) {
        Init = R_TSIP_Sha256Init;
        Update = R_TSIP_Sha256Update;
        Final = R_TSIP_Sha256Final;
    } else 
        return BAD_FUNC_ARG;
    
    tsip_hw_lock();
    
    if (Init(&handle) == TSIP_SUCCESS) {
        ret = Update(&handle, (uint8_t*)hash->msg, hash->used);
        if (ret == TSIP_SUCCESS) {
            ret = Final(&handle, out, &sz);
            if (ret != TSIP_SUCCESS || sz != outSz) {
                return ret;
            }
        }
    }
    
    tsip_hw_unlock();
    
    return 0;
}

static int TSIPHashCopy(wolfssl_TSIP_Hash* src, wolfssl_TSIP_Hash* dst)
{
    if (src == NULL || dst == NULL) {
        return BAD_FUNC_ARG;
    }
    
    XMEMCPY(dst, src, sizeof(wolfssl_TSIP_Hash));
    
    if (src->len > 0 && src->msg != NULL) {
        dst->msg = (byte*)XMALLOC(src->len, dst->heap, DYNAMIC_TYPE_TMP_BUFFER);
        if (dst->msg == NULL) {
            return MEMORY_E;
        }
        XMEMCPY(dst->msg, src->msg, src->len);
    }
    
    return 0;
}
 /*  */
int wc_InitSha_ex(wc_Sha* sha, void* heap, int devId)
{
    return TSIPHashInit(sha, heap, devId, TSIP_SHA1);
}

int wc_ShaUpdate(wc_Sha* sha, const byte* in, word32 sz)
{
    return TSIPHashUpdate(sha, in, sz);
}

int wc_ShaFinal(wc_Sha* sha, byte* hash)
{
    return TSIPHashFinal(sha, hash, WC_SHA_DIGEST_SIZE);
}

int wc_ShaGetHash(wc_Sha* sha, byte* hash)
{
    return TSIPHashGet(sha, hash, WC_SHA_DIGEST_SIZE);
}

int wc_ShaCopy(wc_Sha256* src, wc_Sha256* dst)
{
    return TSIPHashCopy(src, dst);
}
#endif /* !NO_SHA */

#if !defined(NO_SHA256)
#include <wolfssl/wolfcrypt/sha256.h>

/*  */
int wc_InitSha256_ex(wc_Sha256* sha, void* heap, int devId)
{
    return TSIPHashInit(sha, heap, devId, TSIP_SHA256);
}

int wc_Sha256Update(wc_Sha256* sha, const byte* in, word32 sz)
{
    return TSIPHashUpdate(sha, in, sz);
}

int wc_Sha256Final(wc_Sha256* sha, byte* hash)
{
    return TSIPHashFinal(sha, hash, WC_SHA256_DIGEST_SIZE);
}

int wc_Sha256GetHash(wc_Sha256* sha, byte* hash)
{
    return TSIPHashGet(sha, hash, WC_SHA256_DIGEST_SIZE);
}

int wc_Sha256Copy(wc_Sha256* src, wc_Sha256* dst)
{
    return TSIPHashCopy(src, dst);
}
#endif /* !NO_SHA256 */
#endif /* WOLFSSL_RENESAS_TSIP_CRYPT */
#endif /* #if !defined(NO_SHA) || !defined(NO_SHA256) */
