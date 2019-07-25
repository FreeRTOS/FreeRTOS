/* des.h
 *
 * Copyright (C) 2015 wolfSSL Inc.
 *
 * This file is part of wolfSSL. (formerly known as wolfSSL)
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


/*  des.h defines mini des openssl compatibility layer 
 *
 */


#ifndef WOLFSSL_DES_H_
#define WOLFSSL_DES_H_

#include <wolfssl/wolfcrypt/settings.h>

#ifndef NO_DES3

#ifdef WOLFSSL_PREFIX
#include "prefix_des.h"
#endif


#ifdef __cplusplus
    extern "C" {
#endif

typedef unsigned char WOLFSSL_DES_cblock[8];
typedef /* const */ WOLFSSL_DES_cblock WOLFSSL_const_DES_cblock;
typedef WOLFSSL_DES_cblock WOLFSSL_DES_key_schedule;


enum {
    DES_ENCRYPT = 1,
    DES_DECRYPT = 0
};


WOLFSSL_API void wolfSSL_DES_set_key_unchecked(WOLFSSL_const_DES_cblock*,
                                             WOLFSSL_DES_key_schedule*);
WOLFSSL_API int  wolfSSL_DES_key_sched(WOLFSSL_const_DES_cblock* key,
                                     WOLFSSL_DES_key_schedule* schedule);
WOLFSSL_API void wolfSSL_DES_cbc_encrypt(const unsigned char* input,
                     unsigned char* output, long length,
                     WOLFSSL_DES_key_schedule* schedule, WOLFSSL_DES_cblock* ivec,
                     int enc);
WOLFSSL_API void wolfSSL_DES_ncbc_encrypt(const unsigned char* input,
                      unsigned char* output, long length,
                      WOLFSSL_DES_key_schedule* schedule,
                      WOLFSSL_DES_cblock* ivec, int enc);

WOLFSSL_API void wolfSSL_DES_set_odd_parity(WOLFSSL_DES_cblock*);
WOLFSSL_API void wolfSSL_DES_ecb_encrypt(WOLFSSL_DES_cblock*, WOLFSSL_DES_cblock*,
                                       WOLFSSL_DES_key_schedule*, int);


typedef WOLFSSL_DES_cblock DES_cblock;
typedef WOLFSSL_const_DES_cblock const_DES_cblock;
typedef WOLFSSL_DES_key_schedule DES_key_schedule;

#define DES_set_key_unchecked wolfSSL_DES_set_key_unchecked
#define DES_key_sched wolfSSL_DES_key_sched
#define DES_cbc_encrypt wolfSSL_DES_cbc_encrypt
#define DES_ncbc_encrypt wolfSSL_DES_ncbc_encrypt
#define DES_set_odd_parity wolfSSL_DES_set_odd_parity
#define DES_ecb_encrypt wolfSSL_DES_ecb_encrypt
#define DES_ede3_cbc_encrypt(input, output, sz, ks1, ks2, ks3, ivec, enc) \
do {                                                         \
    Des3 des;                                                \
    byte key[24];/* EDE uses 24 size key */                  \
    memcpy(key, (ks1), DES_BLOCK_SIZE);                      \
    memcpy(&key[DES_BLOCK_SIZE], (ks2), DES_BLOCK_SIZE);     \
    memcpy(&key[DES_BLOCK_SIZE * 2], (ks3), DES_BLOCK_SIZE); \
    if (enc) {                                               \
        wc_Des3_SetKey(&des, key, (const byte*)(ivec), DES_ENCRYPTION);    \
        wc_Des3_CbcEncrypt(&des, (output), (input), (sz));    \
    }                                                         \
    else {                                                    \
        wc_Des3_SetKey(&des, key, (const byte*)(ivec), DES_ENCRYPTION);    \
        wc_Des3_CbcDecrypt(&des, (output), (input), (sz));    \
    }                                                         \
} while(0)

#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* NO_DES3 */

#endif /* WOLFSSL_DES_H_ */
