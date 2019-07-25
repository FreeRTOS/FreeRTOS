/* curve25519.h
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

#ifndef WOLF_CRYPT_CURVE25519_H
#define WOLF_CRYPT_CURVE25519_H

#include <wolfssl/wolfcrypt/types.h>

#ifdef HAVE_CURVE25519

#include <wolfssl/wolfcrypt/fe_operations.h>
#include <wolfssl/wolfcrypt/random.h>

#ifdef __cplusplus
    extern "C" {
#endif

#define CURVE25519_KEYSIZE 32

/* curve25519 set type */
typedef struct {
    int size;       /* The size of the curve in octets */
    const char* name;     /* name of this curve */
} curve25519_set_type;


/* ECC point */
typedef struct {
    byte point[CURVE25519_KEYSIZE];
}ECPoint;

/* A CURVE25519 Key */
typedef struct {
    int idx;            /* Index into the ecc_sets[] for the parameters of
                           this curve if -1, this key is using user supplied
                           curve in dp */
    const curve25519_set_type* dp;   /* domain parameters, either points to
                                   curves (idx >= 0) or user supplied */
    ECPoint   p;        /* public key  */
    ECPoint   k;        /* private key */
} curve25519_key;

WOLFSSL_API
int wc_curve25519_make_key(RNG* rng, int keysize, curve25519_key* key);

WOLFSSL_API
int wc_curve25519_shared_secret(curve25519_key* private_key,
                                curve25519_key* public_key,
                                byte* out, word32* outlen);

WOLFSSL_API
int wc_curve25519_init(curve25519_key* key);

WOLFSSL_API
void wc_curve25519_free(curve25519_key* key);


/* raw key helpers */
WOLFSSL_API
int wc_curve25519_import_private_raw(const byte* priv, word32 privSz,
                            const byte* pub, word32 pubSz, curve25519_key* key);
WOLFSSL_API
int wc_curve25519_export_private_raw(curve25519_key* key, byte* out,
                                     word32* outLen);

WOLFSSL_API
int wc_curve25519_import_public(const byte* in, word32 inLen,
                                curve25519_key* key);

WOLFSSL_API
int wc_curve25519_export_public(curve25519_key* key, byte* out, word32* outLen);


/* size helper */
WOLFSSL_API
int wc_curve25519_size(curve25519_key* key);

#ifdef __cplusplus
    }    /* extern "C" */
#endif

#endif /* HAVE_CURVE25519 */
#endif /* WOLF_CRYPT_CURVE25519_H */

