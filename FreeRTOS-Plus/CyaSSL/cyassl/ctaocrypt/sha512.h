/* sha512.h
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


#ifdef CYASSL_SHA512

#ifndef CTAO_CRYPT_SHA512_H
#define CTAO_CRYPT_SHA512_H

#include <cyassl/ctaocrypt/types.h>

#ifdef __cplusplus
    extern "C" {
#endif


/* in bytes */
enum {
    SHA512              =   4,   /* hash type unique */
    SHA512_BLOCK_SIZE   = 128,
    SHA512_DIGEST_SIZE  =  64,
    SHA512_PAD_SIZE     = 112 
};


/* Sha512 digest */
typedef struct Sha512 {
    word32  buffLen;   /* in bytes          */
    word32  loLen;     /* length in bytes   */
    word32  hiLen;     /* length in bytes   */
    word64  digest[SHA512_DIGEST_SIZE / sizeof(word64)];
    word64  buffer[SHA512_BLOCK_SIZE  / sizeof(word64)];
} Sha512;


CYASSL_API void InitSha512(Sha512*);
CYASSL_API void Sha512Update(Sha512*, const byte*, word32);
CYASSL_API void Sha512Final(Sha512*, byte*);


#ifdef CYASSL_SHA384

/* in bytes */
enum {
    SHA384              =   5,   /* hash type unique */
    SHA384_BLOCK_SIZE   = 128,
    SHA384_DIGEST_SIZE  =  48,
    SHA384_PAD_SIZE     = 112 
};


/* Sha384 digest */
typedef struct Sha384 {
    word32  buffLen;   /* in bytes          */
    word32  loLen;     /* length in bytes   */
    word32  hiLen;     /* length in bytes   */
    word64  digest[SHA512_DIGEST_SIZE / sizeof(word64)]; /* for transform 512 */
    word64  buffer[SHA384_BLOCK_SIZE  / sizeof(word64)];
} Sha384;


CYASSL_API void InitSha384(Sha384*);
CYASSL_API void Sha384Update(Sha384*, const byte*, word32);
CYASSL_API void Sha384Final(Sha384*, byte*);

#endif /* CYASSL_SHA384 */

#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* CTAO_CRYPT_SHA512_H */
#endif /* CYASSL_SHA512 */
