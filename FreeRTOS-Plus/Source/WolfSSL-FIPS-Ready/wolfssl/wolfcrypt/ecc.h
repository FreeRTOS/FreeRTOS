/* ecc.h
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */

/*!
    \file wolfssl/wolfcrypt/ecc.h
*/


#ifndef WOLF_CRYPT_ECC_H
#define WOLF_CRYPT_ECC_H

#include <wolfssl/wolfcrypt/types.h>

#ifdef HAVE_ECC

#if defined(HAVE_FIPS) && \
    defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2)
    #include <wolfssl/wolfcrypt/fips.h>
#endif /* HAVE_FIPS_VERSION >= 2 */

#include <wolfssl/wolfcrypt/integer.h>
#include <wolfssl/wolfcrypt/random.h>

#ifdef HAVE_X963_KDF
    #include <wolfssl/wolfcrypt/hash.h>
#endif

#ifdef WOLFSSL_ASYNC_CRYPT
    #include <wolfssl/wolfcrypt/async.h>
    #ifdef WOLFSSL_CERT_GEN
        #include <wolfssl/wolfcrypt/asn.h>
    #endif
#endif

#if defined(WOLFSSL_ATECC508A) || defined(WOLFSSL_ATECC608A)
    #include <wolfssl/wolfcrypt/port/atmel/atmel.h>
#endif /* WOLFSSL_ATECC508A */

#if defined(WOLFSSL_CRYPTOCELL)
    #include <wolfssl/wolfcrypt/port/arm/cryptoCell.h>
#endif

#ifdef WOLFSSL_HAVE_SP_ECC
    #include <wolfssl/wolfcrypt/sp_int.h>
#endif


#ifdef __cplusplus
    extern "C" {
#endif


/* Enable curve B parameter if needed */
#if defined(HAVE_COMP_KEY) || defined(ECC_CACHE_CURVE)
    #ifndef USE_ECC_B_PARAM /* Allow someone to force enable */
        #define USE_ECC_B_PARAM
    #endif
#endif


/* Use this as the key->idx if a custom ecc_set is used for key->dp */
#define ECC_CUSTOM_IDX    (-1)


/* Determine max ECC bits based on enabled curves */
#if defined(HAVE_ECC521) || defined(HAVE_ALL_CURVES)
    #define MAX_ECC_BITS    521
#elif defined(HAVE_ECC512)
    #define MAX_ECC_BITS    512
#elif defined(HAVE_ECC384)
    #define MAX_ECC_BITS    384
#elif defined(HAVE_ECC320)
    #define MAX_ECC_BITS    320
#elif !defined(NO_ECC256)
    #define MAX_ECC_BITS    256
#elif defined(HAVE_ECC239)
    #define MAX_ECC_BITS    239
#elif defined(HAVE_ECC224)
    #define MAX_ECC_BITS    224
#elif defined(HAVE_ECC192)
    #define MAX_ECC_BITS    192
#elif defined(HAVE_ECC160)
    #define MAX_ECC_BITS    160
#elif defined(HAVE_ECC128)
    #define MAX_ECC_BITS    128
#elif defined(HAVE_ECC112)
    #define MAX_ECC_BITS    112
#endif

/* calculate max ECC bytes */
#if ((MAX_ECC_BITS * 2) % 8) == 0
    #define MAX_ECC_BYTES     (MAX_ECC_BITS / 8)
#else
    /* add byte if not aligned */
    #define MAX_ECC_BYTES     ((MAX_ECC_BITS / 8) + 1)
#endif

#ifndef ECC_MAX_PAD_SZ
    /* ECC maximum padding size (when MSB is set extra byte required for R and S) */
    #define ECC_MAX_PAD_SZ 2
#endif

enum {
    ECC_PUBLICKEY       = 1,
    ECC_PRIVATEKEY      = 2,
    ECC_PRIVATEKEY_ONLY = 3,
    ECC_MAXNAME     = 16,   /* MAX CURVE NAME LENGTH */
    SIG_HEADER_SZ   =  7,   /* ECC signature header size (30 81 87 02 42 [R] 02 42 [S]) */
    ECC_BUFSIZE     = 256,  /* for exported keys temp buffer */
    ECC_MINSIZE     = 20,   /* MIN Private Key size */
    ECC_MAXSIZE     = 66,   /* MAX Private Key size */
    ECC_MAXSIZE_GEN = 74,   /* MAX Buffer size required when generating ECC keys*/
    ECC_MAX_OID_LEN = 16,
    ECC_MAX_SIG_SIZE= ((MAX_ECC_BYTES * 2) + ECC_MAX_PAD_SZ + SIG_HEADER_SZ),

    /* max crypto hardware size */
#if defined(WOLFSSL_ATECC508A) || defined(WOLFSSL_ATECC608A)
    ECC_MAX_CRYPTO_HW_SIZE = ATECC_KEY_SIZE, /* from port/atmel/atmel.h */
    ECC_MAX_CRYPTO_HW_PUBKEY_SIZE = (ATECC_KEY_SIZE*2),
#elif defined(PLUTON_CRYPTO_ECC)
    ECC_MAX_CRYPTO_HW_SIZE = 32,
#elif defined(WOLFSSL_CRYPTOCELL)
    #ifndef CRYPTOCELL_KEY_SIZE
        CRYPTOCELL_KEY_SIZE = ECC_MAXSIZE,
    #endif
    ECC_MAX_CRYPTO_HW_SIZE = CRYPTOCELL_KEY_SIZE,
#endif

    /* point compression type */
    ECC_POINT_COMP_EVEN = 0x02,
    ECC_POINT_COMP_ODD = 0x03,
    ECC_POINT_UNCOMP = 0x04,

    /* Shamir's dual add constants */
    SHAMIR_PRECOMP_SZ = 16,

#ifdef HAVE_PKCS11
    ECC_MAX_ID_LEN    = 32,
#endif
};

/* Curve Types */
typedef enum ecc_curve_id {
    ECC_CURVE_INVALID = -1,
    ECC_CURVE_DEF = 0, /* NIST or SECP */

    /* NIST Prime Curves */
    ECC_SECP192R1,
    ECC_PRIME192V2,
    ECC_PRIME192V3,
    ECC_PRIME239V1,
    ECC_PRIME239V2,
    ECC_PRIME239V3,
    ECC_SECP256R1,

    /* SECP Curves */
    ECC_SECP112R1,
    ECC_SECP112R2,
    ECC_SECP128R1,
    ECC_SECP128R2,
    ECC_SECP160R1,
    ECC_SECP160R2,
    ECC_SECP224R1,
    ECC_SECP384R1,
    ECC_SECP521R1,

    /* Koblitz */
    ECC_SECP160K1,
    ECC_SECP192K1,
    ECC_SECP224K1,
    ECC_SECP256K1,

    /* Brainpool Curves */
    ECC_BRAINPOOLP160R1,
    ECC_BRAINPOOLP192R1,
    ECC_BRAINPOOLP224R1,
    ECC_BRAINPOOLP256R1,
    ECC_BRAINPOOLP320R1,
    ECC_BRAINPOOLP384R1,
    ECC_BRAINPOOLP512R1,

    /* Twisted Edwards Curves */
#ifdef HAVE_CURVE25519
    ECC_X25519,
#endif
#ifdef HAVE_CURVE448
    ECC_X448,
#endif

#ifdef WOLFSSL_CUSTOM_CURVES
    ECC_CURVE_CUSTOM,
#endif
} ecc_curve_id;

#ifdef HAVE_OID_ENCODING
typedef word16 ecc_oid_t;
#else
typedef byte   ecc_oid_t;
    /* OID encoded with ASN scheme:
        first element = (oid[0] * 40) + oid[1]
        if any element > 127 then MSB 0x80 indicates additional byte */
#endif


#if !defined(WOLFSSL_ECC_CURVE_STATIC) && defined(USE_WINDOWS_API)
    /* MSC does something different with the pointers to the arrays than GCC,
     * and it causes the FIPS checksum to fail. In the case of windows builds,
     * store everything as arrays instead of pointers to strings. */

    #define WOLFSSL_ECC_CURVE_STATIC
#endif

/* ECC set type defined a GF(p) curve */
#ifndef WOLFSSL_ECC_CURVE_STATIC
typedef struct ecc_set_type {
    int size;             /* The size of the curve in octets */
    int id;               /* id of this curve */
    const char* name;     /* name of this curve */
    const char* prime;    /* prime that defines the field, curve is in (hex) */
    const char* Af;       /* fields A param (hex) */
    const char* Bf;       /* fields B param (hex) */
    const char* order;    /* order of the curve (hex) */
    const char* Gx;       /* x coordinate of the base point on curve (hex) */
    const char* Gy;       /* y coordinate of the base point on curve (hex) */
    const ecc_oid_t* oid;
    word32      oidSz;
    word32      oidSum;    /* sum of encoded OID bytes */
    int         cofactor;
} ecc_set_type;
#else
#define MAX_ECC_NAME 16
#define MAX_ECC_STRING ((MAX_ECC_BYTES * 2) + 1)
    /* The values are stored as text strings. */

typedef struct ecc_set_type {
    int size;             /* The size of the curve in octets */
    int id;               /* id of this curve */
    const char name[MAX_ECC_NAME];     /* name of this curve */
    const char prime[MAX_ECC_STRING];    /* prime that defines the field, curve is in (hex) */
    const char Af[MAX_ECC_STRING];       /* fields A param (hex) */
    const char Bf[MAX_ECC_STRING];       /* fields B param (hex) */
    const char order[MAX_ECC_STRING];    /* order of the curve (hex) */
    const char Gx[MAX_ECC_STRING];       /* x coordinate of the base point on curve (hex) */
    const char Gy[MAX_ECC_STRING];       /* y coordinate of the base point on curve (hex) */
    const ecc_oid_t oid[10];
    word32      oidSz;
    word32      oidSum;    /* sum of encoded OID bytes */
    int         cofactor;
} ecc_set_type;
#endif


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
 * structure, the alt_fp_int will only have 512 bits for ECC 256-bit and 
 * 1056-bits for ECC 521-bit. A size value was added in the ALT case, as well, 
 * and is set by mp_init() and alt_fp_init(). The functions fp_zero() and 
 * fp_copy() use the size parameter. An int needs to be initialized before 
 * using it instead of just fp_zeroing it, the init will call zero. The 
 * FP_MAX_BITS_ECC defaults to calculating based on MAX_ECC_BITS, but 
 * can be set to change the number of bits used in the alternate FP_INT.
 *
 * The ALT_ECC_SIZE option only applies to stack based fast math USE_FAST_MATH.
 */

#ifndef USE_FAST_MATH
    #error USE_FAST_MATH must be defined to use ALT_ECC_SIZE
#endif

/* determine max bits required for ECC math */
#ifndef FP_MAX_BITS_ECC
    /* max bits rounded up by 8 then doubled */
    /* (ROUND8(MAX_ECC_BITS) * 2) */
    #define FP_MAX_BITS_ECC (2 * \
        ((MAX_ECC_BITS + DIGIT_BIT - 1) / DIGIT_BIT) * DIGIT_BIT)

    /* Note: For ECC verify only FP_MAX_BITS_ECC can be reduced to:
             ROUND8(MAX_ECC_BITS) + ROUND8(DIGIT_BIT) */
#endif

/* verify alignment */
#if FP_MAX_BITS_ECC % CHAR_BIT
    #error FP_MAX_BITS_ECC must be a multiple of CHAR_BIT
#endif

/* determine buffer size */
#define FP_SIZE_ECC    (FP_MAX_BITS_ECC/DIGIT_BIT)


/* This needs to match the size of the fp_int struct, except the
 * fp_digit array will be shorter. */
typedef struct alt_fp_int {
    int used, sign, size;
    mp_digit dp[FP_SIZE_ECC];
} alt_fp_int;
#endif /* ALT_ECC_SIZE */

#ifndef WC_ECCKEY_TYPE_DEFINED
    typedef struct ecc_key ecc_key;
    #define WC_ECCKEY_TYPE_DEFINED
#endif


/* A point on an ECC curve, stored in Jacobian format such that (x,y,z) =>
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
#ifdef WOLFSSL_SMALL_STACK_CACHE
    ecc_key* key;
#endif
} ecc_point;

/* ECC Flags */
enum {
    WC_ECC_FLAG_NONE = 0x00,
#ifdef HAVE_ECC_CDH
    WC_ECC_FLAG_COFACTOR = 0x01,
#endif
};

/* ECC non-blocking */
#ifdef WC_ECC_NONBLOCK
    typedef struct ecc_nb_ctx {
    #if defined(WOLFSSL_HAVE_SP_ECC) && defined(WOLFSSL_SP_NONBLOCK)
        sp_ecc_ctx_t sp_ctx;
    #else
        /* build configuration not supported */
        #error ECC non-blocking only supports SP (--enable-sp=nonblock)
    #endif
    } ecc_nb_ctx_t;
#endif /* WC_ECC_NONBLOCK */


/* An ECC Key */
struct ecc_key {
    int type;           /* Public or Private */
    int idx;            /* Index into the ecc_sets[] for the parameters of
                           this curve if -1, this key is using user supplied
                           curve in dp */
    int    state;
    word32 flags;
    const ecc_set_type* dp;     /* domain parameters, either points to NIST
                                   curves (idx >= 0) or user supplied */
#ifdef WOLFSSL_CUSTOM_CURVES
    int deallocSet;
#endif
    void* heap;         /* heap hint */
    ecc_point pubkey;   /* public key */
    mp_int    k;        /* private key */
#if defined(WOLFSSL_ATECC508A) || defined(WOLFSSL_ATECC608A)
    int  slot;        /* Key Slot Number (-1 unknown) */
    byte pubkey_raw[ECC_MAX_CRYPTO_HW_PUBKEY_SIZE];
#endif
#if defined(PLUTON_CRYPTO_ECC) || defined(WOLF_CRYPTO_CB)
    int devId;
#endif
#ifdef WOLFSSL_ASYNC_CRYPT
    mp_int* r;          /* sign/verify temps */
    mp_int* s;
    WC_ASYNC_DEV asyncDev;
    #ifdef HAVE_CAVIUM_V
        mp_int* e;      /* Sign, Verify and Shared Secret */
        mp_int* signK;
    #endif
    #ifdef WOLFSSL_CERT_GEN
        CertSignCtx certSignCtx; /* context info for cert sign (MakeSignature) */
    #endif
#endif /* WOLFSSL_ASYNC_CRYPT */
#ifdef HAVE_PKCS11
    byte id[ECC_MAX_ID_LEN];
    int  idLen;
#endif
#if defined(WOLFSSL_CRYPTOCELL)
    ecc_context_t ctx;
#endif

#ifdef WOLFSSL_ECDSA_SET_K
    mp_int *sign_k;
#endif

#ifdef WOLFSSL_SMALL_STACK_CACHE
    mp_int* t1;
    mp_int* t2;
#ifdef ALT_ECC_SIZE
    mp_int* x;
    mp_int* y;
    mp_int* z;
#endif
#endif

#ifdef WOLFSSL_DSP
    remote_handle64 handle;
#endif
#ifdef ECC_TIMING_RESISTANT
    WC_RNG* rng;
#endif
#ifdef WC_ECC_NONBLOCK
    ecc_nb_ctx_t* nb_ctx;
#endif
};


WOLFSSL_ABI WOLFSSL_API ecc_key* wc_ecc_key_new(void*);
WOLFSSL_ABI WOLFSSL_API void wc_ecc_key_free(ecc_key*);


/* ECC predefined curve sets  */
extern const ecc_set_type ecc_sets[];
extern const size_t ecc_sets_count;

WOLFSSL_API
const char* wc_ecc_get_name(int curve_id);

#if !defined(WOLFSSL_ATECC508A) && !defined(WOLFSSL_ATECC608A)

#ifdef WOLFSSL_PUBLIC_ECC_ADD_DBL
    #define ECC_API    WOLFSSL_API
#else
    #define ECC_API    WOLFSSL_LOCAL
#endif

ECC_API int ecc_mul2add(ecc_point* A, mp_int* kA,
                ecc_point* B, mp_int* kB,
                ecc_point* C, mp_int* a, mp_int* modulus, void* heap);

ECC_API int ecc_map(ecc_point*, mp_int*, mp_digit);
ECC_API int ecc_map_ex(ecc_point*, mp_int*, mp_digit, int ct);
ECC_API int ecc_projective_add_point(ecc_point* P, ecc_point* Q, ecc_point* R,
                                     mp_int* a, mp_int* modulus, mp_digit mp);
ECC_API int ecc_projective_dbl_point(ecc_point* P, ecc_point* R, mp_int* a,
                                     mp_int* modulus, mp_digit mp);

#endif

WOLFSSL_API
int wc_ecc_make_key(WC_RNG* rng, int keysize, ecc_key* key);
WOLFSSL_ABI WOLFSSL_API
int wc_ecc_make_key_ex(WC_RNG* rng, int keysize, ecc_key* key, int curve_id);
WOLFSSL_API
int wc_ecc_make_pub(ecc_key* key, ecc_point* pubOut);
WOLFSSL_API
int wc_ecc_make_pub_ex(ecc_key* key, ecc_point* pubOut, WC_RNG* rng);
WOLFSSL_API
int wc_ecc_check_key(ecc_key* key);
WOLFSSL_API
int wc_ecc_is_point(ecc_point* ecp, mp_int* a, mp_int* b, mp_int* prime);
WOLFSSL_API
int wc_ecc_get_generator(ecc_point* ecp, int curve_idx);

#ifdef HAVE_ECC_DHE
WOLFSSL_API
int wc_ecc_shared_secret(ecc_key* private_key, ecc_key* public_key, byte* out,
                      word32* outlen);
WOLFSSL_LOCAL
int wc_ecc_shared_secret_gen(ecc_key* private_key, ecc_point* point,
                             byte* out, word32 *outlen);
WOLFSSL_API
int wc_ecc_shared_secret_ex(ecc_key* private_key, ecc_point* point,
                             byte* out, word32 *outlen);

#if defined(WOLFSSL_ATECC508A) || defined(WOLFSSL_ATECC608A) || \
    defined(PLUTON_CRYPTO_ECC) || defined(WOLFSSL_CRYPTOCELL)
#define wc_ecc_shared_secret_ssh wc_ecc_shared_secret
#else
#define wc_ecc_shared_secret_ssh wc_ecc_shared_secret_ex /* For backwards compat */
#endif

#endif /* HAVE_ECC_DHE */

#ifdef HAVE_ECC_SIGN
WOLFSSL_ABI WOLFSSL_API
int wc_ecc_sign_hash(const byte* in, word32 inlen, byte* out, word32 *outlen,
                     WC_RNG* rng, ecc_key* key);
WOLFSSL_API
int wc_ecc_sign_hash_ex(const byte* in, word32 inlen, WC_RNG* rng,
                        ecc_key* key, mp_int *r, mp_int *s);
#ifdef WOLFSSL_ECDSA_SET_K
WOLFSSL_API
int wc_ecc_sign_set_k(const byte* k, word32 klen, ecc_key* key);
#endif
#endif /* HAVE_ECC_SIGN */

#ifdef HAVE_ECC_VERIFY
WOLFSSL_API
int wc_ecc_verify_hash(const byte* sig, word32 siglen, const byte* hash,
                    word32 hashlen, int* stat, ecc_key* key);
WOLFSSL_API
int wc_ecc_verify_hash_ex(mp_int *r, mp_int *s, const byte* hash,
                          word32 hashlen, int* stat, ecc_key* key);
#endif /* HAVE_ECC_VERIFY */

WOLFSSL_API
int wc_ecc_init(ecc_key* key);
WOLFSSL_ABI WOLFSSL_API
int wc_ecc_init_ex(ecc_key* key, void* heap, int devId);
#ifdef HAVE_PKCS11
WOLFSSL_API
int wc_ecc_init_id(ecc_key* key, unsigned char* id, int len, void* heap,
                   int devId);
#endif
#ifdef WOLFSSL_CUSTOM_CURVES
WOLFSSL_LOCAL
void wc_ecc_free_curve(const ecc_set_type* curve, void* heap);
#endif
WOLFSSL_ABI WOLFSSL_API
int wc_ecc_free(ecc_key* key);
WOLFSSL_API
int wc_ecc_set_flags(ecc_key* key, word32 flags);
WOLFSSL_API
void wc_ecc_fp_free(void);
WOLFSSL_LOCAL
void wc_ecc_fp_init(void);
#ifdef ECC_TIMING_RESISTANT
WOLFSSL_API
int wc_ecc_set_rng(ecc_key* key, WC_RNG* rng);
#endif

WOLFSSL_API
int wc_ecc_set_curve(ecc_key* key, int keysize, int curve_id);

WOLFSSL_API
int wc_ecc_is_valid_idx(int n);
WOLFSSL_API
int wc_ecc_get_curve_idx(int curve_id);
WOLFSSL_API
int wc_ecc_get_curve_id(int curve_idx);
#define wc_ecc_get_curve_name_from_id wc_ecc_get_name
WOLFSSL_API
int wc_ecc_get_curve_size_from_id(int curve_id);

WOLFSSL_API
int wc_ecc_get_curve_idx_from_name(const char* curveName);
WOLFSSL_API
int wc_ecc_get_curve_size_from_name(const char* curveName);
WOLFSSL_API
int wc_ecc_get_curve_id_from_name(const char* curveName);
WOLFSSL_API
int wc_ecc_get_curve_id_from_params(int fieldSize,
        const byte* prime, word32 primeSz, const byte* Af, word32 AfSz,
        const byte* Bf, word32 BfSz, const byte* order, word32 orderSz,
        const byte* Gx, word32 GxSz, const byte* Gy, word32 GySz, int cofactor);
WOLFSSL_API
int wc_ecc_get_curve_id_from_dp_params(const ecc_set_type* dp);

WOLFSSL_API
int wc_ecc_get_curve_id_from_oid(const byte* oid, word32 len);

WOLFSSL_API const ecc_set_type* wc_ecc_get_curve_params(int curve_idx);

WOLFSSL_API
ecc_point* wc_ecc_new_point(void);
WOLFSSL_API
ecc_point* wc_ecc_new_point_h(void* h);
WOLFSSL_API
void wc_ecc_del_point(ecc_point* p);
WOLFSSL_API
void wc_ecc_del_point_h(ecc_point* p, void* h);
WOLFSSL_API
int wc_ecc_copy_point(ecc_point* p, ecc_point *r);
WOLFSSL_API
int wc_ecc_cmp_point(ecc_point* a, ecc_point *b);
WOLFSSL_API
int wc_ecc_point_is_at_infinity(ecc_point *p);
WOLFSSL_API
int wc_ecc_point_is_on_curve(ecc_point *p, int curve_idx);

#if !defined(WOLFSSL_ATECC508A) && !defined(WOLFSSL_ATECC608A)
WOLFSSL_API
int wc_ecc_mulmod(mp_int* k, ecc_point *G, ecc_point *R,
                  mp_int* a, mp_int* modulus, int map);
WOLFSSL_LOCAL
int wc_ecc_mulmod_ex(mp_int* k, ecc_point *G, ecc_point *R,
                  mp_int* a, mp_int* modulus, int map, void* heap);
WOLFSSL_LOCAL
int wc_ecc_mulmod_ex2(mp_int* k, ecc_point *G, ecc_point *R, mp_int* a,
                      mp_int* modulus, mp_int* order, WC_RNG* rng, int map,
                      void* heap);
#endif /* !WOLFSSL_ATECC508A */


#ifdef HAVE_ECC_KEY_EXPORT
/* ASN key helpers */
WOLFSSL_API
int wc_ecc_export_x963(ecc_key*, byte* out, word32* outLen);
WOLFSSL_API
int wc_ecc_export_x963_ex(ecc_key*, byte* out, word32* outLen, int compressed);
    /* extended functionality with compressed option */
#endif /* HAVE_ECC_KEY_EXPORT */

#ifdef HAVE_ECC_KEY_IMPORT
WOLFSSL_ABI WOLFSSL_API
int wc_ecc_import_x963(const byte* in, word32 inLen, ecc_key* key);
WOLFSSL_API
int wc_ecc_import_x963_ex(const byte* in, word32 inLen, ecc_key* key,
                          int curve_id);
WOLFSSL_API
int wc_ecc_import_private_key(const byte* priv, word32 privSz, const byte* pub,
                           word32 pubSz, ecc_key* key);
WOLFSSL_API
int wc_ecc_import_private_key_ex(const byte* priv, word32 privSz,
                const byte* pub, word32 pubSz, ecc_key* key, int curve_id);
WOLFSSL_API
int wc_ecc_rs_to_sig(const char* r, const char* s, byte* out, word32* outlen);
WOLFSSL_API
int wc_ecc_rs_raw_to_sig(const byte* r, word32 rSz, const byte* s, word32 sSz,
    byte* out, word32* outlen);
WOLFSSL_API
int wc_ecc_sig_to_rs(const byte* sig, word32 sigLen, byte* r, word32* rLen,
                   byte* s, word32* sLen);
WOLFSSL_API
int wc_ecc_import_raw(ecc_key* key, const char* qx, const char* qy,
                   const char* d, const char* curveName);
WOLFSSL_API
int wc_ecc_import_raw_ex(ecc_key* key, const char* qx, const char* qy,
                   const char* d, int curve_id);
WOLFSSL_API
int wc_ecc_import_unsigned(ecc_key* key, byte* qx, byte* qy,
                   byte* d, int curve_id);
#endif /* HAVE_ECC_KEY_IMPORT */

#ifdef HAVE_ECC_KEY_EXPORT
WOLFSSL_API
int wc_ecc_export_ex(ecc_key* key, byte* qx, word32* qxLen,
                     byte* qy, word32* qyLen, byte* d, word32* dLen,
                     int encType);
WOLFSSL_API
int wc_ecc_export_private_only(ecc_key* key, byte* out, word32* outLen);
WOLFSSL_API
int wc_ecc_export_public_raw(ecc_key* key, byte* qx, word32* qxLen,
                             byte* qy, word32* qyLen);
WOLFSSL_API
int wc_ecc_export_private_raw(ecc_key* key, byte* qx, word32* qxLen,
                              byte* qy, word32* qyLen, byte* d, word32* dLen);
#endif /* HAVE_ECC_KEY_EXPORT */

#ifdef HAVE_ECC_KEY_EXPORT
WOLFSSL_API
int wc_ecc_export_point_der_ex(const int curve_idx, ecc_point* point, byte* out,
                               word32* outLen, int compressed);
WOLFSSL_API
int wc_ecc_export_point_der(const int curve_idx, ecc_point* point,
                            byte* out, word32* outLen);
WOLFSSL_LOCAL
int wc_ecc_export_point_der_compressed(const int curve_idx, ecc_point* point,
                                       byte* out, word32* outLen);
#endif /* HAVE_ECC_KEY_EXPORT */


#ifdef HAVE_ECC_KEY_IMPORT
WOLFSSL_API
int wc_ecc_import_point_der_ex(byte* in, word32 inLen, const int curve_idx,
                               ecc_point* point, int shortKeySize);
WOLFSSL_API
int wc_ecc_import_point_der(byte* in, word32 inLen, const int curve_idx,
                            ecc_point* point);
#endif /* HAVE_ECC_KEY_IMPORT */

/* size helper */
WOLFSSL_API
int wc_ecc_size(ecc_key* key);
WOLFSSL_API
int wc_ecc_sig_size_calc(int sz);
WOLFSSL_API
int wc_ecc_sig_size(ecc_key* key);

WOLFSSL_API
int wc_ecc_get_oid(word32 oidSum, const byte** oid, word32* oidSz);

#ifdef WOLFSSL_CUSTOM_CURVES
    WOLFSSL_API
    int wc_ecc_set_custom_curve(ecc_key* key, const ecc_set_type* dp);
#endif

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
    IV_SIZE_128      = 16,
    EXCHANGE_SALT_SZ = 16,
    EXCHANGE_INFO_SZ = 23
};

enum ecFlags {
    REQ_RESP_CLIENT = 1,
    REQ_RESP_SERVER = 2
};


typedef struct ecEncCtx ecEncCtx;

WOLFSSL_API
ecEncCtx* wc_ecc_ctx_new(int flags, WC_RNG* rng);
WOLFSSL_API
ecEncCtx* wc_ecc_ctx_new_ex(int flags, WC_RNG* rng, void* heap);
WOLFSSL_API
void wc_ecc_ctx_free(ecEncCtx*);
WOLFSSL_API
int wc_ecc_ctx_reset(ecEncCtx*, WC_RNG*);  /* reset for use again w/o alloc/free */

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

#ifdef HAVE_X963_KDF
WOLFSSL_API int wc_X963_KDF(enum wc_HashType type, const byte* secret,
                word32 secretSz, const byte* sinfo, word32 sinfoSz,
                byte* out, word32 outSz);
#endif

#ifdef ECC_CACHE_CURVE
WOLFSSL_API int wc_ecc_curve_cache_init(void);
WOLFSSL_API void wc_ecc_curve_cache_free(void);
#endif

WOLFSSL_API
int wc_ecc_gen_k(WC_RNG* rng, int size, mp_int* k, mp_int* order);

#ifdef WOLFSSL_DSP
WOLFSSL_API
int wc_ecc_set_handle(ecc_key* key, remote_handle64 handle);
WOLFSSL_LOCAL
int sp_dsp_ecc_verify_256(remote_handle64 handle, const byte* hash, word32 hashLen, mp_int* pX,
    mp_int* pY, mp_int* pZ, mp_int* r, mp_int* sm, int* res, void* heap);
#endif

#ifdef WC_ECC_NONBLOCK
    WOLFSSL_API int wc_ecc_set_nonblock(ecc_key *key, ecc_nb_ctx_t* ctx);
#endif

#ifdef __cplusplus
    }    /* extern "C" */
#endif

#endif /* HAVE_ECC */
#endif /* WOLF_CRYPT_ECC_H */
