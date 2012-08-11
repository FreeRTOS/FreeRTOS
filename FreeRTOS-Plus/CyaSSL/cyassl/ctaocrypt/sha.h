/* sha.h
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


#ifndef CTAO_CRYPT_SHA_H
#define CTAO_CRYPT_SHA_H

#include <cyassl/ctaocrypt/types.h>

#ifdef __cplusplus
    extern "C" {
#endif


/* in bytes */
enum {
    SHA              =  1,    /* hash type unique */
    SHA_BLOCK_SIZE   = 64,
    SHA_DIGEST_SIZE  = 20,
    SHA_PAD_SIZE     = 56
};


/* Sha digest */
typedef struct Sha {
    word32  buffLen;   /* in bytes          */
    word32  loLen;     /* length in bytes   */
    word32  hiLen;     /* length in bytes   */
    word32  digest[SHA_DIGEST_SIZE / sizeof(word32)];
    word32  buffer[SHA_BLOCK_SIZE  / sizeof(word32)];
} Sha;


CYASSL_API void InitSha(Sha*);
CYASSL_API void ShaUpdate(Sha*, const byte*, word32);
CYASSL_API void ShaFinal(Sha*, byte*);


#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* CTAO_CRYPT_SHA_H */

