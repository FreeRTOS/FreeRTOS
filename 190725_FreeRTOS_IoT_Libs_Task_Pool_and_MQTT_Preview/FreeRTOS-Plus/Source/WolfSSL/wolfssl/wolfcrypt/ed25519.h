/* ed25519.h
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

#ifndef WOLF_CRYPT_ED25519_H
#define WOLF_CRYPT_ED25519_H

#include <wolfssl/wolfcrypt/types.h>

#ifdef HAVE_ED25519

#include <wolfssl/wolfcrypt/fe_operations.h>
#include <wolfssl/wolfcrypt/ge_operations.h>
#include <wolfssl/wolfcrypt/random.h>
#include <wolfssl/wolfcrypt/sha512.h>

#ifdef __cplusplus
    extern "C" {
#endif


/* info about EdDSA curve specifically ed25519, defined as an elliptic curve
   over GF(p) */
/*
    32,                key size
    "ED25519",         curve name
    "2^255-19",        prime number
    "SHA512",          hash function
    "-121665/121666",  value of d
*/

#define ED25519_KEY_SIZE 32
#define ED25519_SIG_SIZE 64


/* An ED25519 Key */
typedef struct {
    byte    p[32];        /* compressed public key */
    byte    k[64];        /* private key : 32 secret -- 32 public */
} ed25519_key;


WOLFSSL_API
int wc_ed25519_make_key(RNG* rng, int keysize, ed25519_key* key);
WOLFSSL_API
int wc_ed25519_sign_msg(const byte* in, word32 inlen, byte* out,
                        word32 *outlen, ed25519_key* key);
WOLFSSL_API
int wc_ed25519_verify_msg(byte* sig, word32 siglen, const byte* msg,
                          word32 msglen, int* stat, ed25519_key* key);
WOLFSSL_API
int wc_ed25519_init(ed25519_key* key);
WOLFSSL_API
void wc_ed25519_free(ed25519_key* key);
WOLFSSL_API
int wc_ed25519_import_public(const byte* in, word32 inLen, ed25519_key* key);
WOLFSSL_API
int wc_ed25519_import_private_key(const byte* priv, word32 privSz,
                               const byte* pub, word32 pubSz, ed25519_key* key);
WOLFSSL_API
int wc_ed25519_export_public(ed25519_key*, byte* out, word32* outLen);
WOLFSSL_API
int wc_ed25519_export_private_only(ed25519_key* key, byte* out, word32* outLen);

/* size helper */
WOLFSSL_API
int wc_ed25519_size(ed25519_key* key);
WOLFSSL_API
int wc_ed25519_sig_size(ed25519_key* key);

#ifdef __cplusplus
    }    /* extern "C" */
#endif

#endif /* HAVE_ED25519 */
#endif /* WOLF_CRYPT_ED25519_H */

