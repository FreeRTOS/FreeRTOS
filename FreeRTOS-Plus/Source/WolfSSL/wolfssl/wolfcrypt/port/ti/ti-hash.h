/* port/ti/ti-hash.h
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
 
#ifndef WOLF_CRYPT_TI_HASH_H
#define WOLF_CRYPT_TI_HASH_H

#include <wolfssl/wolfcrypt/types.h>

#ifndef WOLFSSL_TI_INITBUFF
#define WOLFSSL_TI_INITBUFF 64
#endif

#define WOLFSSL_MAX_HASH_SIZE  64

typedef struct {
    byte   *msg ;
    word32 used ;
    word32 len ;
    byte hash[WOLFSSL_MAX_HASH_SIZE] ;
} wolfssl_TI_Hash ;


#ifndef TI_HASH_TEST
#if !defined(NO_MD5)
typedef wolfssl_TI_Hash Md5 ;

#endif
#if !defined(NO_SHA)
typedef wolfssl_TI_Hash Sha ;
#endif
#if !defined(NO_SHA256)
typedef wolfssl_TI_Hash Sha256 ;
#endif

#if defined(HAVE_SHA224)
typedef wolfssl_TI_Hash Sha224 ;
#define SHA224_DIGEST_SIZE  28

WOLFSSL_API int wc_InitSha224(Sha224* sha224) ;
WOLFSSL_API int wc_Sha224Update(Sha224* sha224, const byte* data, word32 len) ;
WOLFSSL_API int wc_Sha224Final(Sha224* sha224, byte* hash) ;
WOLFSSL_API int wc_Sha224Hash(const byte* data, word32 len, byte*hash) ;

#endif
#endif
#endif /* WOLF_CRYPT_TI_HASH_H  */
