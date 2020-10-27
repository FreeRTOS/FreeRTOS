/* ed448.c
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */

/* Implemented to: RFC 8032 */

/* Based On Daniel J Bernstein's ed25519 Public Domain ref10 work.
 * Reworked for curve448 by Sean Parkinson.
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

/* in case user set HAVE_ED448 there */
#include <wolfssl/wolfcrypt/settings.h>

#ifdef HAVE_ED448

#include <wolfssl/wolfcrypt/ed448.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/hash.h>
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

#if defined(HAVE_ED448_SIGN) || defined(HAVE_ED448_VERIFY)
/* Size of context bytes to use with hash when signing and verifying. */
#define ED448CTX_SIZE    8
/* Context to pass to hash when signing and verifying. */
static const byte ed448Ctx[ED448CTX_SIZE+1] = "SigEd448";
#endif

/* Derive the public key for the private key.
 *
 * key       [in]  Ed448 key object.
 * pubKey    [in]  Byte array to hold te public key.
 * pubKeySz  [in]  Size of the array in bytes.
 * returns BAD_FUNC_ARG when key is NULL or pubKeySz is not equal to
 *         ED448_PUB_KEY_SIZE,
 *         other -ve value on hash failure,
 *         0 otherwise.
 */
int wc_ed448_make_public(ed448_key* key, unsigned char* pubKey, word32 pubKeySz)
{
    int   ret = 0;
    byte  az[ED448_PRV_KEY_SIZE];
    ge448_p2 A;

    if ((key == NULL) || (pubKey == NULL) || (pubKeySz != ED448_PUB_KEY_SIZE)) {
        ret = BAD_FUNC_ARG;
    }

    if (ret == 0) {
        ret = wc_Shake256Hash(key->k, ED448_KEY_SIZE, az, sizeof(az));
    }
    if (ret == 0) {
        /* apply clamp */
        az[0]  &= 0xfc;
        az[55] |= 0x80;
        az[56]  = 0x00;

        ge448_scalarmult_base(&A, az);
        ge448_to_bytes(pubKey, &A);
    }

    return ret;
}

/* Make a new ed448 private/public key.
 *
 * rng      [in]  Random number generator.
 * keysize  [in]  Size of the key to generate.
 * key      [in]  Ed448 key object.
 * returns BAD_FUNC_ARG when rng or key is NULL or keySz is not equal to
 *         ED448_KEY_SIZE,
 *         other -ve value on random number or hash failure,
 *         0 otherwise.
 */
int wc_ed448_make_key(WC_RNG* rng, int keySz, ed448_key* key)
{
    int ret = 0;

    if ((rng == NULL) || (key == NULL)) {
        ret = BAD_FUNC_ARG;
    }

    /* ed448 has 57 byte key sizes */
    if ((ret == 0) && (keySz != ED448_KEY_SIZE)) {
        ret = BAD_FUNC_ARG;
    }

    if (ret == 0) {
        ret = wc_RNG_GenerateBlock(rng, key->k, ED448_KEY_SIZE);
    }
    if (ret == 0) {
        ret = wc_ed448_make_public(key, key->p, ED448_PUB_KEY_SIZE);
        if (ret != 0) {
            ForceZero(key->k, ED448_KEY_SIZE);
        }
    }
    if (ret == 0) {
        /* put public key after private key, on the same buffer */
        XMEMMOVE(key->k + ED448_KEY_SIZE, key->p, ED448_PUB_KEY_SIZE);

        key->pubKeySet = 1;
    }

    return ret;
}


#ifdef HAVE_ED448_SIGN
/* Sign the message using the ed448 private key.
 *
 *  in          [in]      Message to sign.
 *  inLen       [in]      Length of the message in bytes.
 *  out         [in]      Buffer to write signature into.
 *  outLen      [in/out]  On in, size of buffer.
 *                        On out, the length of the signature in bytes.
 *  key         [in]      Ed448 key to use when signing
 *  type        [in]      Type of signature to perform: Ed448 or Ed448ph
 *  context     [in]      Context of signing.
 *  contextLen  [in]      Length of context in bytes.
 *  returns BAD_FUNC_ARG when a parameter is NULL or contextLen is zero when and
 *          context is not NULL or public key not set,
 *          BUFFER_E when outLen is less than ED448_SIG_SIZE,
 *          other -ve values when hash fails,
 *          0 otherwise.
 */
static int ed448_sign_msg(const byte* in, word32 inLen, byte* out,
                          word32 *outLen, ed448_key* key, byte type,
                          const byte* context, byte contextLen)
{
    ge448_p2 R;
    byte     nonce[ED448_SIG_SIZE];
    byte     hram[ED448_SIG_SIZE];
    byte     az[ED448_PRV_KEY_SIZE];
    wc_Shake sha;
    int      ret = 0;

    /* sanity check on arguments */
    if ((in == NULL) || (out == NULL) || (outLen == NULL) || (key == NULL) ||
                                     ((context == NULL) && (contextLen != 0))) {
        ret = BAD_FUNC_ARG;
    }
    if ((ret == 0) && (!key->pubKeySet)) {
        ret = BAD_FUNC_ARG;
    }

    /* check and set up out length */
    if ((ret == 0) && (*outLen < ED448_SIG_SIZE)) {
        *outLen = ED448_SIG_SIZE;
        ret = BUFFER_E;
    }

    if (ret == 0) {
        *outLen = ED448_SIG_SIZE;

        /* step 1: create nonce to use where nonce is r in
           r = H(h_b, ... ,h_2b-1,M) */
        ret = wc_Shake256Hash(key->k, ED448_KEY_SIZE, az, sizeof(az));
    }
    if (ret == 0) {
        /* apply clamp */
        az[0]  &= 0xfc;
        az[55] |= 0x80;
        az[56]  = 0x00;

        ret = wc_InitShake256(&sha, NULL, INVALID_DEVID);
        if (ret == 0) {
            ret = wc_Shake256_Update(&sha, ed448Ctx, ED448CTX_SIZE);
        }
        if (ret == 0) {
            ret = wc_Shake256_Update(&sha, &type, sizeof(type));
        }
        if (ret == 0) {
            ret = wc_Shake256_Update(&sha, &contextLen, sizeof(contextLen));
        }
        if ((ret == 0) && (context != NULL)) {
            ret = wc_Shake256_Update(&sha, context, contextLen);
        }
        if (ret == 0) {
            ret = wc_Shake256_Update(&sha, az + ED448_KEY_SIZE, ED448_KEY_SIZE);
        }
        if (ret == 0) {
            ret = wc_Shake256_Update(&sha, in, inLen);
        }
        if (ret == 0) {
            ret = wc_Shake256_Final(&sha, nonce, sizeof(nonce));
        }
        wc_Shake256_Free(&sha);
    }
    if (ret == 0) {
        sc448_reduce(nonce);

        /* step 2: computing R = rB where rB is the scalar multiplication of
           r and B */
        ge448_scalarmult_base(&R,nonce);
        ge448_to_bytes(out,&R);

        /* step 3: hash R + public key + message getting H(R,A,M) then
           creating S = (r + H(R,A,M)a) mod l */
        ret = wc_InitShake256(&sha, NULL, INVALID_DEVID);
        if (ret == 0) {
            ret = wc_Shake256_Update(&sha, ed448Ctx, ED448CTX_SIZE);
            if (ret == 0) {
                ret = wc_Shake256_Update(&sha, &type, sizeof(type));
            }
            if (ret == 0) {
                ret = wc_Shake256_Update(&sha, &contextLen, sizeof(contextLen));
            }
            if ((ret == 0) && (context != NULL)) {
                ret = wc_Shake256_Update(&sha, context, contextLen);
            }
            if (ret == 0) {
                ret = wc_Shake256_Update(&sha, out, ED448_SIG_SIZE/2);
            }
            if (ret == 0) {
                ret = wc_Shake256_Update(&sha, key->p, ED448_PUB_KEY_SIZE);
            }
            if (ret == 0) {
                ret = wc_Shake256_Update(&sha, in, inLen);
            }
            if (ret == 0) {
                ret = wc_Shake256_Final(&sha, hram, sizeof(hram));
            }
            wc_Shake256_Free(&sha);
        }
    }

    if (ret == 0) {
        sc448_reduce(hram);
        sc448_muladd(out + (ED448_SIG_SIZE/2), hram, az, nonce);
    }

    return ret;
}

/* Sign the message using the ed448 private key.
 * Signature type is Ed448.
 *
 *  in          [in]      Message to sign.
 *  inLen       [in]      Length of the message in bytes.
 *  out         [in]      Buffer to write signature into.
 *  outLen      [in/out]  On in, size of buffer.
 *                        On out, the length of the signature in bytes.
 *  key         [in]      Ed448 key to use when signing
 *  context     [in]      Context of signing.
 *  contextLen  [in]      Length of context in bytes.
 *  returns BAD_FUNC_ARG when a parameter is NULL or contextLen is zero when and
 *          context is not NULL or public key not set,
 *          BUFFER_E when outLen is less than ED448_SIG_SIZE,
 *          other -ve values when hash fails,
 *          0 otherwise.
 */
int wc_ed448_sign_msg(const byte* in, word32 inLen, byte* out, word32 *outLen,
                      ed448_key* key, const byte* context, byte contextLen)
{
    return ed448_sign_msg(in, inLen, out, outLen, key, Ed448, context,
                                                                    contextLen);
}

/* Sign the hash using the ed448 private key.
 * Signature type is Ed448ph.
 *
 *  hash        [in]      Hash of message to sign.
 *  hashLen     [in]      Length of hash of message in bytes.
 *  out         [in]      Buffer to write signature into.
 *  outLen      [in/out]  On in, size of buffer.
 *                        On out, the length of the signature in bytes.
 *  key         [in]      Ed448 key to use when signing
 *  context     [in]      Context of signing.
 *  contextLen  [in]      Length of context in bytes.
 *  returns BAD_FUNC_ARG when a parameter is NULL or contextLen is zero when and
 *          context is not NULL or public key not set,
 *          BUFFER_E when outLen is less than ED448_SIG_SIZE,
 *          other -ve values when hash fails,
 *          0 otherwise.
 */
int wc_ed448ph_sign_hash(const byte* hash, word32 hashLen, byte* out,
                         word32 *outLen, ed448_key* key,
                         const byte* context, byte contextLen)
{
    return ed448_sign_msg(hash, hashLen, out, outLen, key, Ed448ph, context,
                                                                    contextLen);
}

/* Sign the message using the ed448 private key.
 * Signature type is Ed448ph.
 *
 *  in          [in]      Message to sign.
 *  inLen       [in]      Length of the message to sign in bytes.
 *  out         [in]      Buffer to write signature into.
 *  outLen      [in/out]  On in, size of buffer.
 *                        On out, the length of the signature in bytes.
 *  key         [in]      Ed448 key to use when signing
 *  context     [in]      Context of signing.
 *  contextLen  [in]      Length of context in bytes.
 *  returns BAD_FUNC_ARG when a parameter is NULL or contextLen is zero when and
 *          context is not NULL or public key not set,
 *          BUFFER_E when outLen is less than ED448_SIG_SIZE,
 *          other -ve values when hash fails,
 *          0 otherwise.
 */
int wc_ed448ph_sign_msg(const byte* in, word32 inLen, byte* out, word32 *outLen,
                        ed448_key* key, const byte* context, byte contextLen)
{
    int  ret = 0;
    byte hash[64];

    ret = wc_Shake256Hash(in, inLen, hash, sizeof(hash));
    if (ret == 0) {
        ret = wc_ed448ph_sign_hash(hash, sizeof(hash), out, outLen, key,
                                                           context, contextLen);
    }

    return ret;
}
#endif /* HAVE_ED448_SIGN */

#ifdef HAVE_ED448_VERIFY

/* Verify the message using the ed448 public key.
 *
 *  sig         [in]  Signature to verify.
 *  sigLen      [in]  Size of signature in bytes.
 *  msg         [in]  Message to verify.
 *  msgLen      [in]  Length of the message in bytes.
 *  key         [in]  Ed448 key to use to verify.
 *  type        [in]  Type of signature to verify: Ed448 or Ed448ph
 *  context     [in]  Context of verification.
 *  contextLen  [in]  Length of context in bytes.
 *  returns BAD_FUNC_ARG when a parameter is NULL or contextLen is zero when and
 *          context is not NULL or public key not set,
 *          BUFFER_E when sigLen is less than ED448_SIG_SIZE,
 *          other -ve values when hash fails,
 *          0 otherwise.
 */
static int ed448_verify_msg(const byte* sig, word32 sigLen, const byte* msg,
                            word32 msgLen, int* res, ed448_key* key,
                            byte type, const byte* context, byte contextLen)
{
    byte     rcheck[ED448_KEY_SIZE];
    byte     h[ED448_SIG_SIZE];
    ge448_p2 A;
    ge448_p2 R;
    int      ret = 0;
    wc_Shake sha;

    /* sanity check on arguments */
    if ((sig == NULL) || (msg == NULL) || (res == NULL) || (key == NULL) ||
                                     ((context == NULL) && (contextLen != 0))) {
        ret = BAD_FUNC_ARG;
    }

    if (ret == 0) {
        /* set verification failed by default */
        *res = 0;

        /* check on basics needed to verify signature */
        if (sigLen != ED448_SIG_SIZE) {
            ret = BAD_FUNC_ARG;
        }
    }

    /* uncompress A (public key), test if valid, and negate it */
    if ((ret == 0) && (ge448_from_bytes_negate_vartime(&A, key->p) != 0)) {
        ret = BAD_FUNC_ARG;
    }

    if (ret == 0) {
        /* find H(R,A,M) and store it as h */
        ret  = wc_InitShake256(&sha, NULL, INVALID_DEVID);
        if (ret == 0) {
            ret = wc_Shake256_Update(&sha, ed448Ctx, ED448CTX_SIZE);
            if (ret == 0) {
                ret = wc_Shake256_Update(&sha, &type, sizeof(type));
            }
            if (ret == 0) {
                ret = wc_Shake256_Update(&sha, &contextLen, sizeof(contextLen));
            }
            if ((ret == 0) && (context != NULL)) {
                ret = wc_Shake256_Update(&sha, context, contextLen);
            }
            if (ret == 0) {
                ret = wc_Shake256_Update(&sha, sig, ED448_SIG_SIZE/2);
            }
            if (ret == 0) {
                ret = wc_Shake256_Update(&sha, key->p, ED448_PUB_KEY_SIZE);
            }
            if (ret == 0) {
                ret = wc_Shake256_Update(&sha, msg, msgLen);
            }
            if (ret == 0) {
                ret = wc_Shake256_Final(&sha,  h, sizeof(h));
            }
            wc_Shake256_Free(&sha);
        }
    }
    if (ret == 0) {
        sc448_reduce(h);

        /* Uses a fast single-signature verification SB = R + H(R,A,M)A becomes
         * SB - H(R,A,M)A saving decompression of R
         */
        ret = ge448_double_scalarmult_vartime(&R, h, &A,
                                                      sig + (ED448_SIG_SIZE/2));
    }

    if (ret == 0) {
        ge448_to_bytes(rcheck, &R);

        /* comparison of R created to R in sig */
        if (ConstantCompare(rcheck, sig, ED448_SIG_SIZE/2) != 0) {
            ret = SIG_VERIFY_E;
        }
        else {
            /* set the verification status */
            *res = 1;
        }
    }

    return ret;
}

/* Verify the message using the ed448 public key.
 * Signature type is Ed448.
 *
 *  sig         [in]  Signature to verify.
 *  sigLen      [in]  Size of signature in bytes.
 *  msg         [in]  Message to verify.
 *  msgLen      [in]  Length of the message in bytes.
 *  key         [in]  Ed448 key to use to verify.
 *  context     [in]  Context of verification.
 *  contextLen  [in]  Length of context in bytes.
 *  returns BAD_FUNC_ARG when a parameter is NULL or contextLen is zero when and
 *          context is not NULL or public key not set,
 *          BUFFER_E when sigLen is less than ED448_SIG_SIZE,
 *          other -ve values when hash fails,
 *          0 otherwise.
 */
int wc_ed448_verify_msg(const byte* sig, word32 sigLen, const byte* msg,
                        word32 msgLen, int* res, ed448_key* key,
                        const byte* context, byte contextLen)
{
    return ed448_verify_msg(sig, sigLen, msg, msgLen, res, key, Ed448,
                                                           context, contextLen);
}

/* Verify the hash using the ed448 public key.
 * Signature type is Ed448ph.
 *
 *  sig         [in]  Signature to verify.
 *  sigLen      [in]  Size of signature in bytes.
 *  hash        [in]  Hash of message to verify.
 *  hashLen     [in]  Length of the hash in bytes.
 *  key         [in]  Ed448 key to use to verify.
 *  context     [in]  Context of verification.
 *  contextLen  [in]  Length of context in bytes.
 *  returns BAD_FUNC_ARG when a parameter is NULL or contextLen is zero when and
 *          context is not NULL or public key not set,
 *          BUFFER_E when sigLen is less than ED448_SIG_SIZE,
 *          other -ve values when hash fails,
 *          0 otherwise.
 */
int wc_ed448ph_verify_hash(const byte* sig, word32 sigLen, const byte* hash,
                           word32 hashLen, int* res, ed448_key* key,
                           const byte* context, byte contextLen)
{
    return ed448_verify_msg(sig, sigLen, hash, hashLen, res, key, Ed448ph,
                                                           context, contextLen);
}

/* Verify the message using the ed448 public key.
 * Signature type is Ed448ph.
 *
 *  sig         [in]  Signature to verify.
 *  sigLen      [in]  Size of signature in bytes.
 *  msg         [in]  Message to verify.
 *  msgLen      [in]  Length of the message in bytes.
 *  key         [in]  Ed448 key to use to verify.
 *  context     [in]  Context of verification.
 *  contextLen  [in]  Length of context in bytes.
 *  returns BAD_FUNC_ARG when a parameter is NULL or contextLen is zero when and
 *          context is not NULL or public key not set,
 *          BUFFER_E when sigLen is less than ED448_SIG_SIZE,
 *          other -ve values when hash fails,
 *          0 otherwise.
 */
int wc_ed448ph_verify_msg(const byte* sig, word32 sigLen, const byte* msg,
                          word32 msgLen, int* res, ed448_key* key,
                          const byte* context, byte contextLen)
{
    int  ret = 0;
    byte hash[64];

    ret = wc_Shake256Hash(msg, msgLen, hash, sizeof(hash));
    if (ret == 0) {
        ret = wc_ed448ph_verify_hash(sig, sigLen, hash, sizeof(hash), res, key,
                                                           context, contextLen);
    }

    return ret;
}
#endif /* HAVE_ED448_VERIFY */

/* Initialize the ed448 private/public key.
 *
 * key  [in]  Ed448 key.
 * returns BAD_FUNC_ARG when key is NULL
 */
int wc_ed448_init(ed448_key* key)
{
    int ret = 0;

    if (key == NULL) {
        ret = BAD_FUNC_ARG;
    }
    else {
        XMEMSET(key, 0, sizeof(ed448_key));

        fe448_init();
    }

    return ret;
}


/* Clears the ed448 key data
 *
 * key  [in]  Ed448 key.
 */
void wc_ed448_free(ed448_key* key)
{
    if (key != NULL) {
        ForceZero(key, sizeof(ed448_key));
    }
}


#ifdef HAVE_ED448_KEY_EXPORT

/* Export the ed448 public key.
 *
 * key     [in]      Ed448 public key.
 * out     [in]      Array to hold public key.
 * outLen  [in/out]  On in, the number of bytes in array.
 *                   On out, the number bytes put into array.
 * returns BAD_FUNC_ARG when a parameter is NULL,
 *         ECC_BAD_ARG_E when outLen is less than ED448_PUB_KEY_SIZE,
 *         0 otherwise.
 */
int wc_ed448_export_public(ed448_key* key, byte* out, word32* outLen)
{
    int ret = 0;

    /* sanity check on arguments */
    if ((key == NULL) || (out == NULL) || (outLen == NULL)) {
        ret = BAD_FUNC_ARG;
    }

    if ((ret == 0) && (*outLen < ED448_PUB_KEY_SIZE)) {
        *outLen = ED448_PUB_KEY_SIZE;
        ret = BUFFER_E;
    }

    if (ret == 0) {
        *outLen = ED448_PUB_KEY_SIZE;
        XMEMCPY(out, key->p, ED448_PUB_KEY_SIZE);
    }

    return ret;
}

#endif /* HAVE_ED448_KEY_EXPORT */


#ifdef HAVE_ED448_KEY_IMPORT
/* Import a compressed or uncompressed ed448 public key from a byte array.
 * Public key encoded in big-endian.
 *
 * in      [in]  Array holding public key.
 * inLen   [in]  Number of bytes of data in array.
 * key     [in]  Ed448 public key.
 * returns BAD_FUNC_ARG when a parameter is NULL or key format is not supported,
 *         0 otherwise.
 */
int wc_ed448_import_public(const byte* in, word32 inLen, ed448_key* key)
{
    int ret = 0;

    /* sanity check on arguments */
    if ((in == NULL) || (key == NULL)) {
        ret = BAD_FUNC_ARG;
    }

    if  (inLen < ED448_PUB_KEY_SIZE) {
        ret = BAD_FUNC_ARG;
    }

    if (ret == 0) {
        /* compressed prefix according to draft
         * https://tools.ietf.org/html/draft-ietf-openpgp-rfc4880bis-06 */
        if (in[0] == 0x40 && inLen > ED448_PUB_KEY_SIZE) {
            /* key is stored in compressed format so just copy in */
            XMEMCPY(key->p, (in + 1), ED448_PUB_KEY_SIZE);
            key->pubKeySet = 1;
        }
        /* importing uncompressed public key */
        else if (in[0] == 0x04 && inLen > 2*ED448_PUB_KEY_SIZE) {
            /* pass in (x,y) and store compressed key */
            ret = ge448_compress_key(key->p, in+1, in+1+ED448_PUB_KEY_SIZE);
            if (ret == 0)
                key->pubKeySet = 1;
        }
        else if (inLen == ED448_PUB_KEY_SIZE) {
            /* if not specified compressed or uncompressed check key size
             * if key size is equal to compressed key size copy in key */
            XMEMCPY(key->p, in, ED448_PUB_KEY_SIZE);
            key->pubKeySet = 1;
        }
        else {
            /* bad public key format */
            ret = BAD_FUNC_ARG;
        }
    }

    return ret;
}


/* Import an ed448 private key from a byte array.
 *
 * priv    [in]  Array holding private key.
 * privSz  [in]  Number of bytes of data in array.
 * key     [in]  Ed448 private key.
 * returns BAD_FUNC_ARG when a parameter is NULL or privSz is less than
 *         ED448_KEY_SIZE,
 *         0 otherwise.
 */
int wc_ed448_import_private_only(const byte* priv, word32 privSz,
                                 ed448_key* key)
{
    int ret = 0;

    /* sanity check on arguments */
    if ((priv == NULL) || (key == NULL)) {
        ret = BAD_FUNC_ARG;
    }

    /* key size check */
    if ((ret == 0) && (privSz < ED448_KEY_SIZE)) {
        ret = BAD_FUNC_ARG;
    }

    if (ret == 0) {
        XMEMCPY(key->k, priv, ED448_KEY_SIZE);
    }

    return ret;
}

/* Import an ed448 private and public keys from a byte arrays.
 *
 * priv    [in]  Array holding private key.
 * privSz  [in]  Number of bytes of data in private key array.
 * pub     [in]  Array holding private key.
 * pubSz   [in]  Number of bytes of data in public key array.
 * key     [in]  Ed448 private/public key.
 * returns BAD_FUNC_ARG when a parameter is NULL or privSz is less than
 *         ED448_KEY_SIZE or pubSz is less than ED448_PUB_KEY_SIZE,
 *         0 otherwise.
 */
int wc_ed448_import_private_key(const byte* priv, word32 privSz,
                                const byte* pub, word32 pubSz, ed448_key* key)
{
    int ret = 0;

    /* sanity check on arguments */
    if ((priv == NULL) || (pub == NULL) || (key == NULL)) {
        ret = BAD_FUNC_ARG;
    }

    /* key size check */
    if ((ret == 0) && ((privSz < ED448_KEY_SIZE) ||
                                                (pubSz < ED448_PUB_KEY_SIZE))) {
        ret = BAD_FUNC_ARG;
    }

    if (ret == 0) {
        /* import public key */
        ret = wc_ed448_import_public(pub, pubSz, key);
    }
    if (ret == 0) {
        /* make the private key (priv + pub) */
        XMEMCPY(key->k, priv, ED448_KEY_SIZE);
        XMEMCPY(key->k + ED448_KEY_SIZE, key->p, ED448_PUB_KEY_SIZE);
    }

    return ret;
}

#endif /* HAVE_ED448_KEY_IMPORT */


#ifdef HAVE_ED448_KEY_EXPORT

/* Export the ed448 private key.
 *
 * key     [in]      Ed448 private key.
 * out     [in]      Array to hold private key.
 * outLen  [in/out]  On in, the number of bytes in array.
 *                   On out, the number bytes put into array.
 * returns BAD_FUNC_ARG when a parameter is NULL,
 *         ECC_BAD_ARG_E when outLen is less than ED448_KEY_SIZE,
 *         0 otherwise.
 */
int wc_ed448_export_private_only(ed448_key* key, byte* out, word32* outLen)
{
    int ret = 0;

    /* sanity checks on arguments */
    if ((key == NULL) || (out == NULL) || (outLen == NULL)) {
        ret = BAD_FUNC_ARG;
    }

    if ((ret == 0) && (*outLen < ED448_KEY_SIZE)) {
        *outLen = ED448_KEY_SIZE;
        ret = BUFFER_E;
    }

    if (ret == 0) {
        *outLen = ED448_KEY_SIZE;
        XMEMCPY(out, key->k, ED448_KEY_SIZE);
    }

    return ret;
}

/* Export the ed448 private and public key.
 *
 * key     [in]      Ed448 private/public key.
 * out     [in]      Array to hold private and public key.
 * outLen  [in/out]  On in, the number of bytes in array.
 *                   On out, the number bytes put into array.
 * returns BAD_FUNC_ARG when a parameter is NULL,
 *         BUFFER_E when outLen is less than ED448_PRV_KEY_SIZE,
 *         0 otherwise.
 */
int wc_ed448_export_private(ed448_key* key, byte* out, word32* outLen)
{
    int ret = 0;

    /* sanity checks on arguments */
    if ((key == NULL) || (out == NULL) || (outLen == NULL)) {
        ret = BAD_FUNC_ARG;
    }

    if ((ret == 0) && (*outLen < ED448_PRV_KEY_SIZE)) {
        *outLen = ED448_PRV_KEY_SIZE;
        ret = BUFFER_E;
    }

    if (ret == 0) {
        *outLen = ED448_PRV_KEY_SIZE;
        XMEMCPY(out, key->k, ED448_PRV_KEY_SIZE);
     }

    return ret;
}

/* Export the ed448 private and public key.
 *
 * key     [in]      Ed448 private/public key.
 * priv    [in]      Array to hold private key.
 * privSz  [in/out]  On in, the number of bytes in private key array.
 * pub     [in]      Array to hold  public key.
 * pubSz   [in/out]  On in, the number of bytes in public key array.
 *                   On out, the number bytes put into array.
 * returns BAD_FUNC_ARG when a parameter is NULL,
 *         BUFFER_E when privSz is less than ED448_PRV_KEY_SIZE or pubSz is less
 *         than ED448_PUB_KEY_SIZE,
 *         0 otherwise.
 */
int wc_ed448_export_key(ed448_key* key, byte* priv, word32 *privSz,
                        byte* pub, word32 *pubSz)
{
    int ret = 0;

    /* export 'full' private part */
    ret = wc_ed448_export_private(key, priv, privSz);
    if (ret == 0) {
        /* export public part */
        ret = wc_ed448_export_public(key, pub, pubSz);
    }

    return ret;
}

#endif /* HAVE_ED448_KEY_EXPORT */

/* Check the public key of the ed448 key matches the private key.
 *
 * key     [in]      Ed448 private/public key.
 * returns BAD_FUNC_ARG when key is NULL,
 *         PUBLIC_KEY_E when the public key is not set or doesn't match,
 *         other -ve value on hash failure,
 *         0 otherwise.
 */
int wc_ed448_check_key(ed448_key* key)
{
    int ret = 0;
    unsigned char pubKey[ED448_PUB_KEY_SIZE];

    if (key == NULL) {
        ret = BAD_FUNC_ARG;
    }

    if (!key->pubKeySet) {
        ret = PUBLIC_KEY_E;
    }
    if (ret == 0) {
        ret = wc_ed448_make_public(key, pubKey, sizeof(pubKey));
    }
    if ((ret == 0) && (XMEMCMP(pubKey, key->p, ED448_PUB_KEY_SIZE) != 0)) {
        ret = PUBLIC_KEY_E;
    }

    return ret;
}

/* Returns the size of an ed448 private key.
 *
 * key     [in]      Ed448 private/public key.
 * returns BAD_FUNC_ARG when key is NULL,
 *         ED448_KEY_SIZE otherwise.
 */
int wc_ed448_size(ed448_key* key)
{
    int ret = ED448_KEY_SIZE;

    if (key == NULL) {
        ret = BAD_FUNC_ARG;
    }

    return ret;
}

/* Returns the size of an ed448 private plus public key.
 *
 * key     [in]      Ed448 private/public key.
 * returns BAD_FUNC_ARG when key is NULL,
 *         ED448_PRV_KEY_SIZE otherwise.
 */
int wc_ed448_priv_size(ed448_key* key)
{
    int ret = ED448_PRV_KEY_SIZE;

    if (key == NULL) {
        ret = BAD_FUNC_ARG;
    }

    return ret;
}

/* Returns the size of an ed448 public key.
 *
 * key     [in]      Ed448 private/public key.
 * returns BAD_FUNC_ARG when key is NULL,
 *         ED448_PUB_KEY_SIZE otherwise.
 */
int wc_ed448_pub_size(ed448_key* key)
{
    int ret = ED448_PUB_KEY_SIZE;

    if (key == NULL) {
        ret = BAD_FUNC_ARG;
    }

    return ret;
}

/* Returns the size of an ed448 signature.
 *
 * key     [in]      Ed448 private/public key.
 * returns BAD_FUNC_ARG when key is NULL,
 *         ED448_SIG_SIZE otherwise.
 */
int wc_ed448_sig_size(ed448_key* key)
{
    int ret = ED448_SIG_SIZE;

    if (key == NULL) {
        ret = BAD_FUNC_ARG;
    }

    return ret;
}

#endif /* HAVE_ED448 */

