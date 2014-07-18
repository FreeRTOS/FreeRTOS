/* sha256.h
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


/* code submitted by raphael.huck@efixo.com */


#ifndef NO_SHA256

#ifndef CTAO_CRYPT_SHA256_H
#define CTAO_CRYPT_SHA256_H

#include <cyassl/ctaocrypt/types.h>

#ifdef __cplusplus
    extern "C" {
#endif

#ifdef CYASSL_PIC32MZ_HASH
#include "port/pic32/pic32mz-crypt.h"
#endif


/* in bytes */
enum {
    SHA256              =  2,   /* hash type unique */
    SHA256_BLOCK_SIZE   = 64,
    SHA256_DIGEST_SIZE  = 32,
    SHA256_PAD_SIZE     = 56
};


/* Sha256 digest */
typedef struct Sha256 {
    word32  buffLen;   /* in bytes          */
    word32  loLen;     /* length in bytes   */
    word32  hiLen;     /* length in bytes   */
    word32  digest[SHA256_DIGEST_SIZE / sizeof(word32)];
    word32  buffer[SHA256_BLOCK_SIZE  / sizeof(word32)];
    #ifdef CYASSL_PIC32MZ_HASH
        pic32mz_desc desc ; /* Crypt Engine descripter */
    #endif
} Sha256;


CYASSL_API int InitSha256(Sha256*);
CYASSL_API int Sha256Update(Sha256*, const byte*, word32);
CYASSL_API int Sha256Final(Sha256*, byte*);
CYASSL_API int Sha256Hash(const byte*, word32, byte*);


#ifdef HAVE_FIPS
    /* fips wrapper calls, user can call direct */
    CYASSL_API int InitSha256_fips(Sha256*);
    CYASSL_API int Sha256Update_fips(Sha256*, const byte*, word32);
    CYASSL_API int Sha256Final_fips(Sha256*, byte*);
    #ifndef FIPS_NO_WRAPPERS
        /* if not impl or fips.c impl wrapper force fips calls if fips build */
        #define InitSha256   InitSha256_fips
        #define Sha256Update Sha256Update_fips
        #define Sha256Final  Sha256Final_fips
    #endif /* FIPS_NO_WRAPPERS */

#endif /* HAVE_FIPS */

 
#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* CTAO_CRYPT_SHA256_H */
#endif /* NO_SHA256 */

