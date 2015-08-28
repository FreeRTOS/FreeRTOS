/* des.h
 *
 * Copyright (C) 2013 wolfSSL Inc.
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


/*  des.h defines mini des openssl compatibility layer 
 *
 */


#ifndef CYASSL_DES_H_
#define CYASSL_DES_H_

#include <cyassl/ctaocrypt/settings.h>

#ifdef YASSL_PREFIX
#include "prefix_des.h"
#endif


#ifdef __cplusplus
    extern "C" {
#endif

typedef unsigned char CYASSL_DES_cblock[8];
typedef /* const */ CYASSL_DES_cblock CYASSL_const_DES_cblock;
typedef CYASSL_DES_cblock CYASSL_DES_key_schedule;


enum {
    DES_ENCRYPT = 1,
    DES_DECRYPT = 0
};


CYASSL_API void CyaSSL_DES_set_key_unchecked(CYASSL_const_DES_cblock*,
                                             CYASSL_DES_key_schedule*);
CYASSL_API int  CyaSSL_DES_key_sched(CYASSL_const_DES_cblock* key,
                                     CYASSL_DES_key_schedule* schedule);
CYASSL_API void CyaSSL_DES_cbc_encrypt(const unsigned char* input,
                     unsigned char* output, long length,
                     CYASSL_DES_key_schedule* schedule, CYASSL_DES_cblock* ivec,
                     int enc);
CYASSL_API void CyaSSL_DES_ncbc_encrypt(const unsigned char* input,
                      unsigned char* output, long length,
                      CYASSL_DES_key_schedule* schedule,
                      CYASSL_DES_cblock* ivec, int enc);

CYASSL_API void CyaSSL_DES_set_odd_parity(CYASSL_DES_cblock*);
CYASSL_API void CyaSSL_DES_ecb_encrypt(CYASSL_DES_cblock*, CYASSL_DES_cblock*,
                                       CYASSL_DES_key_schedule*, int);


typedef CYASSL_DES_cblock DES_cblock;
typedef CYASSL_const_DES_cblock const_DES_cblock;
typedef CYASSL_DES_key_schedule DES_key_schedule;

#define DES_set_key_unchecked CyaSSL_DES_set_key_unchecked
#define DES_key_sched CyaSSL_DES_key_sched
#define DES_cbc_encrypt CyaSSL_DES_cbc_encrypt
#define DES_ncbc_encrypt CyaSSL_DES_ncbc_encrypt
#define DES_set_odd_parity CyaSSL_DES_set_odd_parity
#define DES_ecb_encrypt CyaSSL_DES_ecb_encrypt

#ifdef __cplusplus
    } /* extern "C" */
#endif


#endif /* CYASSL_DES_H_ */
