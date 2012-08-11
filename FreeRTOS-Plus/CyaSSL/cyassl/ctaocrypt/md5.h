/* md5.h
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


#ifndef CTAO_CRYPT_MD5_H
#define CTAO_CRYPT_MD5_H

#include <cyassl/ctaocrypt/types.h>

#ifdef __cplusplus
    extern "C" {
#endif


/* in bytes */
enum {
    MD5             =  0,      /* hash type unique */
    MD5_BLOCK_SIZE  = 64,
    MD5_DIGEST_SIZE = 16,
    MD5_PAD_SIZE    = 56
};


/* MD5 digest */
typedef struct Md5 {
    word32  buffLen;   /* in bytes          */
    word32  loLen;     /* length in bytes   */
    word32  hiLen;     /* length in bytes   */
    word32  digest[MD5_DIGEST_SIZE / sizeof(word32)];
    word32  buffer[MD5_BLOCK_SIZE  / sizeof(word32)];
} Md5;


CYASSL_API void InitMd5(Md5*);
CYASSL_API void Md5Update(Md5*, const byte*, word32);
CYASSL_API void Md5Final(Md5*, byte*);


#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* CTAO_CRYPT_MD5_H */

