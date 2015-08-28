/* ed25519.c
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

 /* Based On Daniel J Bernstein's ed25519 Public Domain ref10 work. */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

/* in case user set HAVE_ED25519 there */
#include <wolfssl/wolfcrypt/settings.h>

#ifdef HAVE_ED25519

#include <wolfssl/wolfcrypt/ed25519.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #include <wolfcrypt/src/misc.c>
#endif


/*
    generate an ed25519 key pair.
    returns 0 on success
 */
int wc_ed25519_make_key(RNG* rng, int keySz, ed25519_key* key)
{
    byte  az[64];
    int   ret;
    ge_p3 A;

    if (rng == NULL || key == NULL)
        return BAD_FUNC_ARG;

    /* ed25519 has 32 byte key sizes */
    if (keySz != ED25519_KEY_SIZE)
        return BAD_FUNC_ARG;

    ret = 0;
    ret |= wc_RNG_GenerateBlock(rng, key->k, 32);
    ret |= wc_Sha512Hash(key->k, 32, az);
    az[0] &= 248;
    az[31] &= 63;
    az[31] |= 64;

    ge_scalarmult_base(&A, az);
    ge_p3_tobytes(key->p, &A);
    XMEMMOVE(key->k + 32, key->p, 32);

    return ret;
}


/*
    in     contains the message to sign
    inlen  is the length of the message to sign
    out    is the buffer to write the signature
    outlen [in/out] input size of out buf
                    output gets set as the final length of out
    key    is the ed25519 key to use when signing
    return 0 on success
 */
int wc_ed25519_sign_msg(const byte* in, word32 inlen, byte* out,
                        word32 *outlen, ed25519_key* key)
{
    ge_p3  R;
    byte   nonce[SHA512_DIGEST_SIZE];
    byte   hram[SHA512_DIGEST_SIZE];
    byte   az[64];
    word32 sigSz;
    Sha512 sha;
    int    ret = 0;

    /* sanity check on arguments */
    if (in == NULL || out == NULL || outlen == NULL || key == NULL)
        return BAD_FUNC_ARG;

    /* check and set up out length */
    ret   = 0;
    sigSz = wc_ed25519_sig_size(key);
    if (*outlen < sigSz)
        return BAD_FUNC_ARG;
    *outlen = sigSz;

    /* step 1: create nonce to use where nonce is r in
       r = H(h_b, ... ,h_2b-1,M) */
    ret |= wc_Sha512Hash(key->k,32,az);
    az[0]  &= 248;
    az[31] &= 63;
    az[31] |= 64;
    ret |= wc_InitSha512(&sha);
    ret |= wc_Sha512Update(&sha, az + 32, 32);
    ret |= wc_Sha512Update(&sha, in, inlen);
    ret |= wc_Sha512Final(&sha, nonce);
    sc_reduce(nonce);

    /* step 2: computing R = rB where rB is the scalar multiplication of
       r and B */
    ge_scalarmult_base(&R,nonce);
    ge_p3_tobytes(out,&R);

    /* step 3: hash R + public key + message getting H(R,A,M) then
       creating S = (r + H(R,A,M)a) mod l */
    ret |= wc_InitSha512(&sha);
    ret |= wc_Sha512Update(&sha, out, 32);
    ret |= wc_Sha512Update(&sha, key->p, 32);
    ret |= wc_Sha512Update(&sha, in, inlen);
    ret |= wc_Sha512Final(&sha, hram);
    sc_reduce(hram);
    sc_muladd(out + 32, hram, az, nonce);

    return ret;
}


/*
   sig     is array of bytes containing the signature
   siglen  is the length of sig byte array
   msg     the array of bytes containing the message
   msglen  length of msg array
   stat    will be 1 on successful verify and 0 on unsuccessful
*/
int wc_ed25519_verify_msg(byte* sig, word32 siglen, const byte* msg,
                          word32 msglen, int* stat, ed25519_key* key)
{
    byte   rcheck[32];
    byte   h[SHA512_DIGEST_SIZE];
    ge_p3  A;
    ge_p2  R;
    word32 sigSz;
    int    ret;
    Sha512 sha;

    /* sanity check on arguments */
    if (sig == NULL || msg == NULL || stat == NULL || key == NULL)
        return BAD_FUNC_ARG;

    ret   = 0;
    *stat = 0;
    sigSz = wc_ed25519_size(key);

    /* check on basics needed to verify signature */
    if (siglen < sigSz)
        return BAD_FUNC_ARG;
    if (sig[63] & 224)
        return BAD_FUNC_ARG;

    /* uncompress A (public key), test if valid, and negate it */
    if (ge_frombytes_negate_vartime(&A, key->p) != 0)
        return BAD_FUNC_ARG;

    /* find H(R,A,M) and store it as h */
    ret |= wc_InitSha512(&sha);
    ret |= wc_Sha512Update(&sha, sig,    32);
    ret |= wc_Sha512Update(&sha, key->p, 32);
    ret |= wc_Sha512Update(&sha, msg,    msglen);
    ret |= wc_Sha512Final(&sha,  h);
    sc_reduce(h);

    /*
       Uses a fast single-signature verification SB = R + H(R,A,M)A becomes
       SB - H(R,A,M)A saving decompression of R
    */
    ret |= ge_double_scalarmult_vartime(&R, h, &A, sig + 32);
    ge_tobytes(rcheck, &R);

    /* comparison of R created to R in sig */
    ret  |= ConstantCompare(rcheck, sig, 32);

    *stat = (ret == 0)? 1: 0;

    return ret;
}


/* initialize information and memory for key */
int wc_ed25519_init(ed25519_key* key)
{
    if (key == NULL)
        return BAD_FUNC_ARG;

    XMEMSET(key, 0, sizeof(ed25519_key));

    return 0;
}


/* clear memory of key */
void wc_ed25519_free(ed25519_key* key)
{
    if (key == NULL)
        return;

    ForceZero(key, sizeof(ed25519_key));
}


/*
    outLen should contain the size of out buffer when input. outLen is than set
    to the final output length.
    returns 0 on success
 */
int wc_ed25519_export_public(ed25519_key* key, byte* out, word32* outLen)
{
    word32 keySz;

    /* sanity check on arguments */
    if (key == NULL || out == NULL || outLen == NULL)
        return BAD_FUNC_ARG;

    keySz = wc_ed25519_size(key);
    if (*outLen < keySz) {
        *outLen = keySz;
        return BUFFER_E;
    }
    *outLen = keySz;
    XMEMCPY(out, key->p, keySz);

    return 0;
}


/*
    Imports a compressed/uncompressed public key.
    in    the byte array containing the public key
    inLen the length of the byte array being passed in
    key   ed25519 key struct to put the public key in
 */
int wc_ed25519_import_public(const byte* in, word32 inLen, ed25519_key* key)
{
    word32 keySz;
    int    ret;

    /* sanity check on arguments */
    if (in == NULL || key == NULL)
        return BAD_FUNC_ARG;

    keySz = wc_ed25519_size(key);

    if (inLen < keySz)
        return BAD_FUNC_ARG;

    /* compressed prefix according to draft
       http://www.ietf.org/id/draft-koch-eddsa-for-openpgp-02.txt */
    if (in[0] == 0x40) {
        /* key is stored in compressed format so just copy in */
        XMEMCPY(key->p, (in + 1), keySz);
        return 0;
    }

    /* importing uncompressed public key */
    if (in[0] == 0x04) {
        /* pass in (x,y) and store compressed key */
        ret = ge_compress_key(key->p, (in+1), (in+1+keySz), keySz);
        return ret;
    }

    /* if not specified compressed or uncompressed check key size
       if key size is equal to compressed key size copy in key */
    if (inLen == keySz) {
        XMEMCPY(key->p, in, keySz);
        return 0;
    }

    /* bad public key format */
    return BAD_FUNC_ARG;
}


/*
    For importing a private key and its associated public key.
 */
int wc_ed25519_import_private_key(const byte* priv, word32 privSz,
                                const byte* pub, word32 pubSz, ed25519_key* key)
{
    word32 keySz;
    int    ret;

    /* sanity check on arguments */
    if (priv == NULL || pub == NULL || key == NULL)
        return BAD_FUNC_ARG;

    keySz = wc_ed25519_size(key);

    /* key size check */
    if (privSz < keySz || pubSz < keySz)
        return BAD_FUNC_ARG;

    XMEMCPY(key->k, priv, keySz);
    ret = wc_ed25519_import_public(pub, pubSz, key);
    XMEMCPY((key->k + keySz), key->p, keySz);

    return ret;
}


/*
    outLen should contain the size of out buffer when input. outLen is than set
    to the final output length.
    returns 0 on success
 */
int wc_ed25519_export_private_only(ed25519_key* key, byte* out, word32* outLen)
{
    word32 keySz;

    /* sanity checks on arguments */
    if (key == NULL || out == NULL || outLen == NULL)
        return BAD_FUNC_ARG;

    keySz = wc_ed25519_size(key);
    if (*outLen < keySz) {
        *outLen = keySz;
        return BUFFER_E;
    }
    *outLen = keySz;
    XMEMCPY(out, key->k, keySz);

    return 0;
}


/* is the compressed key size in bytes */
int wc_ed25519_size(ed25519_key* key)
{
    word32 keySz;

    if (key == NULL)
        return BAD_FUNC_ARG;

    keySz = ED25519_KEY_SIZE;

    return keySz;
}


/* returns the size of signature in bytes */
int wc_ed25519_sig_size(ed25519_key* key)
{
    word32 sigSz;

    if (key == NULL)
        return BAD_FUNC_ARG;

    sigSz = ED25519_SIG_SIZE;

    return sigSz;
}

#endif /* HAVE_ED25519 */

