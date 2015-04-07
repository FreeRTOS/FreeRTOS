/* md4.h
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


#ifndef NO_MD4

#ifndef CTAO_CRYPT_MD4_H
#define CTAO_CRYPT_MD4_H

#include <cyassl/ctaocrypt/types.h>

#ifdef __cplusplus
    extern "C" {
#endif


/* in bytes */
enum {
    MD4_BLOCK_SIZE  = 64,
    MD4_DIGEST_SIZE = 16,
    MD4_PAD_SIZE    = 56
};


/* MD4 digest */
typedef struct Md4 {
    word32  buffLen;   /* in bytes          */
    word32  loLen;     /* length in bytes   */
    word32  hiLen;     /* length in bytes   */
    word32  digest[MD4_DIGEST_SIZE / sizeof(word32)];
    word32  buffer[MD4_BLOCK_SIZE  / sizeof(word32)];
} Md4;


CYASSL_API void InitMd4(Md4*);
CYASSL_API void Md4Update(Md4*, const byte*, word32);
CYASSL_API void Md4Final(Md4*, byte*);


#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* CTAO_CRYPT_MD4_H */

#endif /* NO_MD4 */

