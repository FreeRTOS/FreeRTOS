/* ecc.h
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

#ifndef WOLF_CRYPT_ECC_H
#define WOLF_CRYPT_ECC_H

#include <wolfssl/wolfcrypt/types.h>

#ifdef HAVE_ECC

#include <wolfssl/wolfcrypt/integer.h>
#include <wolfssl/wolfcrypt/random.h>

#ifdef __cplusplus
    extern "C" {
#endif

enum {
    ECC_PUBLICKEY  = 1,
    ECC_PRIVATEKEY = 2,
    ECC_MAXNAME    = 16,     /* MAX CURVE NAME LENGTH */
    SIG_HEADER_SZ  =  6,     /* ECC signature header size */
    ECC_BUFSIZE    = 256,    /* for exported keys temp buffer */
    ECC_MINSIZE    = 20,     /* MIN Private Key size */
    ECC_MAXSIZE    = 66      /* MAX Private Key size */
};


/* ECC set type defined a NIST GF(p) curve */
typedef struct {
    int size;       /* The size of the curve in octets */
    const char* name;     /* name of this curve */
    const char* prime;    /* prime that defines the field, curve is in (hex) */
    const char* Af;       /* fields A param (hex) */
    const char* Bf;       /* fields B param (hex) */
    const char* order;    /* order of the curve (hex) */
    const char* Gx;       /* x coordinate of the base point on curve (hex) */
    const char* Gy;       /* y coordinate of the base point on curve (hex) */
} ecc_set_type;


#ifdef ALT_ECC_SIZE

/* Note on ALT_ECC_SIZE:
 * The fast math code uses an array of a fixed size to store the big integers.
 * By default, the array is big enough for RSA keys. There is a size,
 * FP_MAX_BITS which can be used to make the array smaller when one wants ECC
 * but not RSA. Some people want fast math sized for both RSA and ECC, where
 * ECC won't use as much as RSA. The flag ALT_ECC_SIZE switches in an alternate
 * ecc_point structure that uses an alternate fp_int that has a shorter array
 * of fp_digits.
 *
 * Now, without ALT_ECC_SIZE, the ecc_point has three single item arrays of
 * mp_ints for the components of the point. With ALT_ECC_SIZE, the components
 * of the point are pointers that are set to each of a three item array of
 * alt_fp_ints. While an mp_int will have 4096 bits of digit inside the
 * structure, the alt_fp_int will only have 512 bits. A size value was added
 * in the ALT case, as well, and is set by mp_init() and alt_fp_init(). The
 * functions fp_zero() and fp_copy() use the size parameter. An int needs to
 * be initialized before using it instead of just fp_zeroing it, the init will
 * call zero. FP_MAX_BITS_ECC defaults to 512, but can be set to change the
 * number of bits used in the alternate FP_INT.
 *
 * Do not enable ALT_ECC_SIZE and disable fast math in the configuration.
 */

#ifndef FP_MAX_BITS_ECC
    #define FP_MAX_BITS_ECC           512
#endif
#define FP_MAX_SIZE_ECC           (FP_MAX_BITS_ECC+(8*DIGIT_BIT))
#if FP_MAX_BITS_ECC % CHAR_BIT
   #error FP_MAX_BITS_ECC must be a multiple of CHAR_BIT
#endif
#define FP_SIZE_ECC    (FP_MAX_SIZE_ECC/DIGIT_BIT)

/* This needs to match the size of the fp_int struct, except the
 * fp_digit array will be shorter. */
typedef struct alt_fp_int {
    int used, sign, size;
    fp_digit dp[FP_SIZE_ECC];
} alt_fp_int;
#endif

/* A point on an ECC curve, stored in Jacbobian format such that (x,y,z) =>
   (x/z^2, y/z^3, 1) when interpreted as affine */
typedef struct {
#ifndef ALT_ECC_SIZE
    mp_int x[1];        /* The x coordinate */
    mp_int y[1];        /* The y coordinate */
    mp_int z[1];        /* The z coordinate */
#else
    mp_int* x;        /* The x coordinate */
    mp_int* y;        /* The y coordinate */
    mp_int* z;        /* The z coordinate */
    alt_fp_int xyz[3];
#endif
} ecc_point;


/* An ECC Key */
typedef struct {
    int type;           /* Public or Private */
    int idx;            /* Index into the ecc_sets[] for the parameters of
                           this curve if -1, this key is using user supplied
                           curve in dp */
    const ecc_set_type* dp;     /* domain parameters, either points to NIST
                                   curves (idx >= 0) or user supplied */
    ecc_point pubkey;   /* public key */
    mp_int    k;        /* private key */
} ecc_key;


/* ECC predefined curve sets  */
extern const ecc_set_type ecc_sets[];


WOLFSSL_API
int wc_ecc_make_key(RNG* rng, int keysize, ecc_key* key);
WOLFSSL_API
int wc_ecc_check_key(ecc_key* key);
WOLFSSL_API
int wc_ecc_shared_secret(ecc_key* private_key, ecc_key* public_key, byte* out,
                      word32* outlen);
WOLFSSL_API
int wc_ecc_sign_hash(const byte* in, word32 inlen, byte* out, word32 *outlen, 
                  RNG* rng, ecc_key* key);
WOLFSSL_API
int wc_ecc_verify_hash(const byte* sig, word32 siglen, const byte* hash,
                    word32 hashlen, int* stat, ecc_key* key);
WOLFSSL_API
int wc_ecc_init(ecc_key* key);
WOLFSSL_API
void wc_ecc_free(ecc_key* key);
WOLFSSL_API
void wc_ecc_fp_free(void);


/* ASN key helpers */
WOLFSSL_API
int wc_ecc_export_x963(ecc_key*, byte* out, word32* outLen);
WOLFSSL_API
int wc_ecc_export_x963_ex(ecc_key*, byte* out, word32* outLen, int compressed);
    /* extended functionality with compressed option */
WOLFSSL_API
int wc_ecc_import_x963(const byte* in, word32 inLen, ecc_key* key);
WOLFSSL_API
int wc_ecc_import_private_key(const byte* priv, word32 privSz, const byte* pub,
                           word32 pubSz, ecc_key* key);
WOLFSSL_API
int wc_ecc_rs_to_sig(const char* r, const char* s, byte* out, word32* outlen);
WOLFSSL_API
int wc_ecc_import_raw(ecc_key* key, const char* qx, const char* qy,
                   const char* d, const char* curveName);

WOLFSSL_API
int wc_ecc_export_private_only(ecc_key* key, byte* out, word32* outLen);

/* size helper */
WOLFSSL_API
int wc_ecc_size(ecc_key* key);
WOLFSSL_API
int wc_ecc_sig_size(ecc_key* key);


#ifdef HAVE_ECC_ENCRYPT
/* ecc encrypt */

enum ecEncAlgo {
    ecAES_128_CBC = 1,  /* default */
    ecAES_256_CBC = 2
};

enum ecKdfAlgo {
    ecHKDF_SHA256 = 1,  /* default */
    ecHKDF_SHA1   = 2
};

enum ecMacAlgo {
    ecHMAC_SHA256 = 1,  /* default */
    ecHMAC_SHA1   = 2
};

enum {
    KEY_SIZE_128     = 16,
    KEY_SIZE_256     = 32,
    IV_SIZE_64       =  8,
    EXCHANGE_SALT_SZ = 16,
    EXCHANGE_INFO_SZ = 23
};

enum ecFlags {
    REQ_RESP_CLIENT = 1,
    REQ_RESP_SERVER = 2
};


typedef struct ecEncCtx ecEncCtx;

WOLFSSL_API
ecEncCtx* wc_ecc_ctx_new(int flags, RNG* rng);
WOLFSSL_API
void wc_ecc_ctx_free(ecEncCtx*);
WOLFSSL_API
int wc_ecc_ctx_reset(ecEncCtx*, RNG*);   /* reset for use again w/o alloc/free */

WOLFSSL_API
const byte* wc_ecc_ctx_get_own_salt(ecEncCtx*);
WOLFSSL_API
int wc_ecc_ctx_set_peer_salt(ecEncCtx*, const byte* salt);
WOLFSSL_API
int wc_ecc_ctx_set_info(ecEncCtx*, const byte* info, int sz);

WOLFSSL_API
int wc_ecc_encrypt(ecc_key* privKey, ecc_key* pubKey, const byte* msg,
                word32 msgSz, byte* out, word32* outSz, ecEncCtx* ctx);
WOLFSSL_API
int wc_ecc_decrypt(ecc_key* privKey, ecc_key* pubKey, const byte* msg,
                word32 msgSz, byte* out, word32* outSz, ecEncCtx* ctx);

#endif /* HAVE_ECC_ENCRYPT */

#ifdef __cplusplus
    }    /* extern "C" */
#endif

#endif /* HAVE_ECC */
#endif /* WOLF_CRYPT_ECC_H */
