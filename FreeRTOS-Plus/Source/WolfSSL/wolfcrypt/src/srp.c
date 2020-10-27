/* srp.c
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


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#ifdef WOLFCRYPT_HAVE_SRP

#include <wolfssl/wolfcrypt/srp.h>
#include <wolfssl/wolfcrypt/random.h>
#include <wolfssl/wolfcrypt/error-crypt.h>

#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

/** Computes the session key using the Mask Generation Function 1. */
static int wc_SrpSetKey(Srp* srp, byte* secret, word32 size);

static int SrpHashInit(SrpHash* hash, SrpType type)
{
    hash->type = type;

    switch (type) {
        case SRP_TYPE_SHA:
            #ifndef NO_SHA
                return wc_InitSha(&hash->data.sha);
            #else
                return BAD_FUNC_ARG;
            #endif

        case SRP_TYPE_SHA256:
            #ifndef NO_SHA256
                return wc_InitSha256(&hash->data.sha256);
            #else
                return BAD_FUNC_ARG;
            #endif

        case SRP_TYPE_SHA384:
            #ifdef WOLFSSL_SHA384
                return wc_InitSha384(&hash->data.sha384);
            #else
                return BAD_FUNC_ARG;
            #endif

        case SRP_TYPE_SHA512:
            #ifdef WOLFSSL_SHA512
                return wc_InitSha512(&hash->data.sha512);
            #else
                return BAD_FUNC_ARG;
            #endif

        default:
            return BAD_FUNC_ARG;
    }
}

static int SrpHashUpdate(SrpHash* hash, const byte* data, word32 size)
{
    switch (hash->type) {
        case SRP_TYPE_SHA:
            #ifndef NO_SHA
                return wc_ShaUpdate(&hash->data.sha, data, size);
            #else
                return BAD_FUNC_ARG;
            #endif

        case SRP_TYPE_SHA256:
            #ifndef NO_SHA256
                return wc_Sha256Update(&hash->data.sha256, data, size);
            #else
                return BAD_FUNC_ARG;
            #endif

        case SRP_TYPE_SHA384:
            #ifdef WOLFSSL_SHA384
                return wc_Sha384Update(&hash->data.sha384, data, size);
            #else
                return BAD_FUNC_ARG;
            #endif

        case SRP_TYPE_SHA512:
            #ifdef WOLFSSL_SHA512
                return wc_Sha512Update(&hash->data.sha512, data, size);
            #else
                return BAD_FUNC_ARG;
            #endif

        default:
            return BAD_FUNC_ARG;
    }
}

static int SrpHashFinal(SrpHash* hash, byte* digest)
{
    switch (hash->type) {
        case SRP_TYPE_SHA:
            #ifndef NO_SHA
                return wc_ShaFinal(&hash->data.sha, digest);
            #else
                return BAD_FUNC_ARG;
            #endif

        case SRP_TYPE_SHA256:
            #ifndef NO_SHA256
                return wc_Sha256Final(&hash->data.sha256, digest);
            #else
                return BAD_FUNC_ARG;
            #endif

        case SRP_TYPE_SHA384:
            #ifdef WOLFSSL_SHA384
                return wc_Sha384Final(&hash->data.sha384, digest);
            #else
                return BAD_FUNC_ARG;
            #endif

        case SRP_TYPE_SHA512:
            #ifdef WOLFSSL_SHA512
                return wc_Sha512Final(&hash->data.sha512, digest);
            #else
                return BAD_FUNC_ARG;
            #endif

        default:
            return BAD_FUNC_ARG;
    }
}

static word32 SrpHashSize(SrpType type)
{
    switch (type) {
        case SRP_TYPE_SHA:
            #ifndef NO_SHA
                return WC_SHA_DIGEST_SIZE;
            #else
                return 0;
            #endif

        case SRP_TYPE_SHA256:
            #ifndef NO_SHA256
                return WC_SHA256_DIGEST_SIZE;
            #else
                return 0;
            #endif

        case SRP_TYPE_SHA384:
            #ifdef WOLFSSL_SHA384
                return WC_SHA384_DIGEST_SIZE;
            #else
                return 0;
            #endif

        case SRP_TYPE_SHA512:
            #ifdef WOLFSSL_SHA512
                return WC_SHA512_DIGEST_SIZE;
            #else
                return 0;
            #endif

        default:
            return 0;
    }
}

int wc_SrpInit(Srp* srp, SrpType type, SrpSide side)
{
    int r;

    /* validating params */

    if (!srp)
        return BAD_FUNC_ARG;

    if (side != SRP_CLIENT_SIDE && side != SRP_SERVER_SIDE)
        return BAD_FUNC_ARG;

    switch (type) {
        case SRP_TYPE_SHA:
            #ifdef NO_SHA
                return NOT_COMPILED_IN;
            #else
                break; /* OK */
            #endif

        case SRP_TYPE_SHA256:
            #ifdef NO_SHA256
                return NOT_COMPILED_IN;
            #else
                break; /* OK */
            #endif

        case SRP_TYPE_SHA384:
            #ifndef WOLFSSL_SHA384
                return NOT_COMPILED_IN;
            #else
                break; /* OK */
            #endif

        case SRP_TYPE_SHA512:
            #ifndef WOLFSSL_SHA512
                return NOT_COMPILED_IN;
            #else
                break; /* OK */
            #endif

        default:
            return BAD_FUNC_ARG;
    }

    /* initializing variables */

    XMEMSET(srp, 0, sizeof(Srp));

    if ((r = SrpHashInit(&srp->client_proof, type)) != 0)
        return r;

    if ((r = SrpHashInit(&srp->server_proof, type)) != 0)
        return r;

    if ((r = mp_init_multi(&srp->N,    &srp->g, &srp->auth,
                           &srp->priv, 0, 0)) != 0)
        return r;

    srp->side = side;    srp->type   = type;
    srp->salt = NULL;    srp->saltSz = 0;
    srp->user = NULL;    srp->userSz = 0;
    srp->key  = NULL;    srp->keySz  = 0;

    srp->keyGenFunc_cb = wc_SrpSetKey;

    /* default heap hint to NULL or test value */
#ifdef WOLFSSL_HEAP_TEST
    srp->heap = (void*)WOLFSSL_HEAP_TEST;
#else
    srp->heap = NULL;
#endif

    return 0;
}

void wc_SrpTerm(Srp* srp)
{
    if (srp) {
        mp_clear(&srp->N);    mp_clear(&srp->g);
        mp_clear(&srp->auth); mp_clear(&srp->priv);
        if (srp->salt) {
            ForceZero(srp->salt, srp->saltSz);
            XFREE(srp->salt, srp->heap, DYNAMIC_TYPE_SRP);
        }
        if (srp->user) {
            ForceZero(srp->user, srp->userSz);
            XFREE(srp->user, srp->heap, DYNAMIC_TYPE_SRP);
        }
        if (srp->key) {
            ForceZero(srp->key, srp->keySz);
            XFREE(srp->key, srp->heap, DYNAMIC_TYPE_SRP);
        }

        ForceZero(srp, sizeof(Srp));
    }
}

int wc_SrpSetUsername(Srp* srp, const byte* username, word32 size)
{
    if (!srp || !username)
        return BAD_FUNC_ARG;

    srp->user = (byte*)XMALLOC(size, srp->heap, DYNAMIC_TYPE_SRP);
    if (srp->user == NULL)
        return MEMORY_E;

    srp->userSz = size;
    XMEMCPY(srp->user, username, srp->userSz);

    return 0;
}

int wc_SrpSetParams(Srp* srp, const byte* N,    word32 nSz,
                              const byte* g,    word32 gSz,
                              const byte* salt, word32 saltSz)
{
    SrpHash hash;
    byte digest1[SRP_MAX_DIGEST_SIZE];
    byte digest2[SRP_MAX_DIGEST_SIZE];
    byte pad = 0;
    int i, r;
    int j = 0;

    if (!srp || !N || !g || !salt || nSz < gSz)
        return BAD_FUNC_ARG;

    if (!srp->user)
        return SRP_CALL_ORDER_E;

    /* Set N */
    if (mp_read_unsigned_bin(&srp->N, N, nSz) != MP_OKAY)
        return MP_READ_E;

    if (mp_count_bits(&srp->N) < SRP_MODULUS_MIN_BITS)
        return BAD_FUNC_ARG;

    /* Set g */
    if (mp_read_unsigned_bin(&srp->g, g, gSz) != MP_OKAY)
        return MP_READ_E;

    if (mp_cmp(&srp->N, &srp->g) != MP_GT)
        return BAD_FUNC_ARG;

    /* Set salt */
    if (srp->salt) {
        ForceZero(srp->salt, srp->saltSz);
        XFREE(srp->salt, srp->heap, DYNAMIC_TYPE_SRP);
    }

    srp->salt = (byte*)XMALLOC(saltSz, srp->heap, DYNAMIC_TYPE_SRP);
    if (srp->salt == NULL)
        return MEMORY_E;

    XMEMCPY(srp->salt, salt, saltSz);
    srp->saltSz = saltSz;

    /* Set k = H(N, g) */
            r = SrpHashInit(&hash, srp->type);
    if (!r) r = SrpHashUpdate(&hash, (byte*) N, nSz);
    for (i = 0; (word32)i < nSz - gSz; i++) {
        if (!r) r = SrpHashUpdate(&hash, &pad, 1);
    }
    if (!r) r = SrpHashUpdate(&hash, (byte*) g, gSz);
    if (!r) r = SrpHashFinal(&hash, srp->k);

    /* update client proof */

    /* digest1 = H(N) */
    if (!r) r = SrpHashInit(&hash, srp->type);
    if (!r) r = SrpHashUpdate(&hash, (byte*) N, nSz);
    if (!r) r = SrpHashFinal(&hash, digest1);

    /* digest2 = H(g) */
    if (!r) r = SrpHashInit(&hash, srp->type);
    if (!r) r = SrpHashUpdate(&hash, (byte*) g, gSz);
    if (!r) r = SrpHashFinal(&hash, digest2);

    /* digest1 = H(N) ^ H(g) */
    if (r == 0) {
        for (i = 0, j = SrpHashSize(srp->type); i < j; i++)
            digest1[i] ^= digest2[i];
    }

    /* digest2 = H(user) */
    if (!r) r = SrpHashInit(&hash, srp->type);
    if (!r) r = SrpHashUpdate(&hash, srp->user, srp->userSz);
    if (!r) r = SrpHashFinal(&hash, digest2);

    /* client proof = H( H(N) ^ H(g) | H(user) | salt) */
    if (!r) r = SrpHashUpdate(&srp->client_proof, digest1, j);
    if (!r) r = SrpHashUpdate(&srp->client_proof, digest2, j);
    if (!r) r = SrpHashUpdate(&srp->client_proof, salt, saltSz);

    return r;
}

int wc_SrpSetPassword(Srp* srp, const byte* password, word32 size)
{
    SrpHash hash;
    byte digest[SRP_MAX_DIGEST_SIZE];
    word32 digestSz;
    int r;

    if (!srp || !password || srp->side != SRP_CLIENT_SIDE)
        return BAD_FUNC_ARG;

    if (!srp->salt)
        return SRP_CALL_ORDER_E;

    digestSz = SrpHashSize(srp->type);

    /* digest = H(username | ':' | password) */
            r = SrpHashInit(&hash, srp->type);
    if (!r) r = SrpHashUpdate(&hash, srp->user, srp->userSz);
    if (!r) r = SrpHashUpdate(&hash, (const byte*) ":", 1);
    if (!r) r = SrpHashUpdate(&hash, password, size);
    if (!r) r = SrpHashFinal(&hash, digest);

    /* digest = H(salt | H(username | ':' | password)) */
    if (!r) r = SrpHashInit(&hash, srp->type);
    if (!r) r = SrpHashUpdate(&hash, srp->salt, srp->saltSz);
    if (!r) r = SrpHashUpdate(&hash, digest, digestSz);
    if (!r) r = SrpHashFinal(&hash, digest);

    /* Set x (private key) */
    if (!r) r = mp_read_unsigned_bin(&srp->auth, digest, digestSz);

    ForceZero(digest, SRP_MAX_DIGEST_SIZE);

    return r;
}

int wc_SrpGetVerifier(Srp* srp, byte* verifier, word32* size)
{
    mp_int v;
    int r;

    if (!srp || !verifier || !size || srp->side != SRP_CLIENT_SIDE)
        return BAD_FUNC_ARG;

    if (mp_iszero(&srp->auth) == MP_YES)
        return SRP_CALL_ORDER_E;

    r = mp_init(&v);
    if (r != MP_OKAY)
        return MP_INIT_E;

    /* v = g ^ x % N */
    if (!r) r = mp_exptmod(&srp->g, &srp->auth, &srp->N, &v);
    if (!r) r = *size < (word32)mp_unsigned_bin_size(&v) ? BUFFER_E : MP_OKAY;
    if (!r) r = mp_to_unsigned_bin(&v, verifier);
    if (!r) *size = mp_unsigned_bin_size(&v);

    mp_clear(&v);

    return r;
}

int wc_SrpSetVerifier(Srp* srp, const byte* verifier, word32 size)
{
    if (!srp || !verifier || srp->side != SRP_SERVER_SIDE)
        return BAD_FUNC_ARG;

    return mp_read_unsigned_bin(&srp->auth, verifier, size);
}

int wc_SrpSetPrivate(Srp* srp, const byte* priv, word32 size)
{
    mp_int p;
    int r;

    if (!srp || !priv || !size)
        return BAD_FUNC_ARG;

    if (mp_iszero(&srp->auth) == MP_YES)
        return SRP_CALL_ORDER_E;

    r = mp_init(&p);
    if (r != MP_OKAY)
        return MP_INIT_E;
    if (!r) r = mp_read_unsigned_bin(&p, priv, size);
    if (!r) r = mp_mod(&p, &srp->N, &srp->priv);
    if (!r) r = mp_iszero(&srp->priv) == MP_YES ? SRP_BAD_KEY_E : 0;

    mp_clear(&p);

    return r;
}

/** Generates random data using wolfcrypt RNG. */
static int wc_SrpGenPrivate(Srp* srp, byte* priv, word32 size)
{
    WC_RNG rng;
    int r = wc_InitRng(&rng);

    if (!r) r = wc_RNG_GenerateBlock(&rng, priv, size);
    if (!r) r = wc_SrpSetPrivate(srp, priv, size);
    if (!r) wc_FreeRng(&rng);

    return r;
}

int wc_SrpGetPublic(Srp* srp, byte* pub, word32* size)
{
    mp_int pubkey;
    word32 modulusSz;
    int r;

    if (!srp || !pub || !size)
        return BAD_FUNC_ARG;

    if (mp_iszero(&srp->auth) == MP_YES)
        return SRP_CALL_ORDER_E;

    modulusSz = mp_unsigned_bin_size(&srp->N);
    if (*size < modulusSz)
        return BUFFER_E;

    r = mp_init(&pubkey);
    if (r != MP_OKAY)
        return MP_INIT_E;

    /* priv = random() */
    if (mp_iszero(&srp->priv) == MP_YES)
        r = wc_SrpGenPrivate(srp, pub, SRP_PRIVATE_KEY_MIN_BITS / 8);

    /* client side: A = g ^ a % N */
    if (srp->side == SRP_CLIENT_SIDE) {
        if (!r) r = mp_exptmod(&srp->g, &srp->priv, &srp->N, &pubkey);

    /* server side: B = (k * v + (g ^ b % N)) % N */
    } else {
        mp_int i, j;

        if (mp_init_multi(&i, &j, 0, 0, 0, 0) == MP_OKAY) {
            if (!r) r = mp_read_unsigned_bin(&i, srp->k,SrpHashSize(srp->type));
            if (!r) r = mp_iszero(&i) == MP_YES ? SRP_BAD_KEY_E : 0;
            if (!r) r = mp_exptmod(&srp->g, &srp->priv, &srp->N, &pubkey);
            if (!r) r = mp_mulmod(&i, &srp->auth, &srp->N, &j);
            if (!r) r = mp_add(&j, &pubkey, &i);
            if (!r) r = mp_mod(&i, &srp->N, &pubkey);

            mp_clear(&i); mp_clear(&j);
        }
    }

    /* extract public key to buffer */
    XMEMSET(pub, 0, modulusSz);
    if (!r) r = mp_to_unsigned_bin(&pubkey, pub);
    if (!r) *size = mp_unsigned_bin_size(&pubkey);
    mp_clear(&pubkey);

    return r;
}

static int wc_SrpSetKey(Srp* srp, byte* secret, word32 size)
{
    SrpHash hash;
    byte digest[SRP_MAX_DIGEST_SIZE];
    word32 i, j, digestSz = SrpHashSize(srp->type);
    byte counter[4];
    int r = BAD_FUNC_ARG;

    XMEMSET(digest, 0, SRP_MAX_DIGEST_SIZE);

    srp->key = (byte*)XMALLOC(2 * digestSz, srp->heap, DYNAMIC_TYPE_SRP);
    if (srp->key == NULL)
        return MEMORY_E;

    srp->keySz = 2 * digestSz;

    for (i = j = 0; j < srp->keySz; i++) {
        counter[0] = (i >> 24) & 0xFF;
        counter[1] = (i >> 16) & 0xFF;
        counter[2] = (i >>  8) & 0xFF;
        counter[3] =  i        & 0xFF;

        r = SrpHashInit(&hash, srp->type);
        if (!r) r = SrpHashUpdate(&hash, secret, size);
        if (!r) r = SrpHashUpdate(&hash, counter, 4);

        if (j + digestSz > srp->keySz) {
            if (!r) r = SrpHashFinal(&hash, digest);
            XMEMCPY(srp->key + j, digest, srp->keySz - j);
            j = srp->keySz;
        }
        else {
            if (!r) r = SrpHashFinal(&hash, srp->key + j);
            j += digestSz;
        }
    }

    ForceZero(digest, sizeof(digest));
    ForceZero(&hash, sizeof(SrpHash));

    return r;
}

int wc_SrpComputeKey(Srp* srp, byte* clientPubKey, word32 clientPubKeySz,
                               byte* serverPubKey, word32 serverPubKeySz)
{
    SrpHash hash;
    byte *secret;
    byte digest[SRP_MAX_DIGEST_SIZE];
    word32 i, secretSz, digestSz;
    mp_int u, s, temp1, temp2;
    byte pad = 0;
    int r;

    /* validating params */

    if (!srp || !clientPubKey || clientPubKeySz == 0
             || !serverPubKey || serverPubKeySz == 0)
        return BAD_FUNC_ARG;

    if (mp_iszero(&srp->priv) == MP_YES)
        return SRP_CALL_ORDER_E;

    /* initializing variables */

    if ((r = SrpHashInit(&hash, srp->type)) != 0)
        return r;

    digestSz = SrpHashSize(srp->type);
    secretSz = mp_unsigned_bin_size(&srp->N);

    if ((secretSz < clientPubKeySz) || (secretSz < serverPubKeySz))
        return BAD_FUNC_ARG;

    if ((secret = (byte*)XMALLOC(secretSz, srp->heap, DYNAMIC_TYPE_SRP)) ==NULL)
        return MEMORY_E;

    if ((r = mp_init_multi(&u, &s, &temp1, &temp2, 0, 0)) != MP_OKAY) {
        XFREE(secret, srp->heap, DYNAMIC_TYPE_SRP);
        return r;
    }

    /* building u (random scrambling parameter) */

    /* H(A) */
    for (i = 0; !r && i < secretSz - clientPubKeySz; i++)
        r = SrpHashUpdate(&hash, &pad, 1);
    if (!r) r = SrpHashUpdate(&hash, clientPubKey, clientPubKeySz);

    /* H(A | B) */
    for (i = 0; !r && i < secretSz - serverPubKeySz; i++)
        r = SrpHashUpdate(&hash, &pad, 1);
    if (!r) r = SrpHashUpdate(&hash, serverPubKey, serverPubKeySz);

    /* set u */
    if (!r) r = SrpHashFinal(&hash, digest);
    if (!r) r = mp_read_unsigned_bin(&u, digest, SrpHashSize(srp->type));

    /* building s (secret) */

    if (!r && srp->side == SRP_CLIENT_SIDE) {

        /* temp1 = B - k * v; rejects k == 0, B == 0 and B >= N. */
        r = mp_read_unsigned_bin(&temp1, srp->k, digestSz);
        if (!r) r = mp_iszero(&temp1) == MP_YES ? SRP_BAD_KEY_E : 0;
        if (!r) r = mp_exptmod(&srp->g, &srp->auth, &srp->N, &temp2);
        if (!r) r = mp_mulmod(&temp1, &temp2, &srp->N, &s);
        if (!r) r = mp_read_unsigned_bin(&temp2, serverPubKey, serverPubKeySz);
        if (!r) r = mp_iszero(&temp2) == MP_YES ? SRP_BAD_KEY_E : 0;
        if (!r) r = mp_cmp(&temp2, &srp->N) != MP_LT ? SRP_BAD_KEY_E : 0;
        if (!r) r = mp_sub(&temp2, &s, &temp1);

        /* temp2 = a + u * x */
        if (!r) r = mp_mulmod(&u, &srp->auth, &srp->N, &s);
        if (!r) r = mp_add(&srp->priv, &s, &temp2);

        /* secret = temp1 ^ temp2 % N */
        if (!r) r = mp_exptmod(&temp1, &temp2, &srp->N, &s);

    } else if (!r && srp->side == SRP_SERVER_SIDE) {
        /* temp1 = v ^ u % N */
        r = mp_exptmod(&srp->auth, &u, &srp->N, &temp1);

        /* temp2 = A * temp1 % N; rejects A == 0, A >= N */
        if (!r) r = mp_read_unsigned_bin(&s, clientPubKey, clientPubKeySz);
        if (!r) r = mp_iszero(&s) == MP_YES ? SRP_BAD_KEY_E : 0;
        if (!r) r = mp_cmp(&s, &srp->N) != MP_LT ? SRP_BAD_KEY_E : 0;
        if (!r) r = mp_mulmod(&s, &temp1, &srp->N, &temp2);

        /* rejects A * v ^ u % N >= 1, A * v ^ u % N == -1 % N */
        if (!r) r = mp_read_unsigned_bin(&temp1, (const byte*)"\001", 1);
        if (!r) r = mp_cmp(&temp2, &temp1) != MP_GT ? SRP_BAD_KEY_E : 0;
        if (!r) r = mp_sub(&srp->N, &temp1, &s);
        if (!r) r = mp_cmp(&temp2, &s) == MP_EQ ? SRP_BAD_KEY_E : 0;

        /* secret = temp2 * b % N */
        if (!r) r = mp_exptmod(&temp2, &srp->priv, &srp->N, &s);
    }

    /* building session key from secret */

    if (!r) r = mp_to_unsigned_bin(&s, secret);
    if (!r) r = srp->keyGenFunc_cb(srp, secret, mp_unsigned_bin_size(&s));

    /* updating client proof = H( H(N) ^ H(g) | H(user) | salt | A | B | K) */

    if (!r) r = SrpHashUpdate(&srp->client_proof, clientPubKey, clientPubKeySz);
    if (!r) r = SrpHashUpdate(&srp->client_proof, serverPubKey, serverPubKeySz);
    if (!r) r = SrpHashUpdate(&srp->client_proof, srp->key,     srp->keySz);

    /* updating server proof = H(A) */

    if (!r) r = SrpHashUpdate(&srp->server_proof, clientPubKey, clientPubKeySz);

    XFREE(secret, srp->heap, DYNAMIC_TYPE_SRP);
    mp_clear(&u); mp_clear(&s); mp_clear(&temp1); mp_clear(&temp2);

    return r;
}

int wc_SrpGetProof(Srp* srp, byte* proof, word32* size)
{
    int r;

    if (!srp || !proof || !size)
        return BAD_FUNC_ARG;

    if (*size < SrpHashSize(srp->type))
        return BUFFER_E;

    if ((r = SrpHashFinal(srp->side == SRP_CLIENT_SIDE
                          ? &srp->client_proof
                          : &srp->server_proof, proof)) != 0)
        return r;

    *size = SrpHashSize(srp->type);

    if (srp->side == SRP_CLIENT_SIDE) {
        /* server proof = H( A | client proof | K) */
        if (!r) r = SrpHashUpdate(&srp->server_proof, proof, *size);
        if (!r) r = SrpHashUpdate(&srp->server_proof, srp->key, srp->keySz);
    }

    return r;
}

int wc_SrpVerifyPeersProof(Srp* srp, byte* proof, word32 size)
{
    byte digest[SRP_MAX_DIGEST_SIZE];
    int r;

    if (!srp || !proof)
        return BAD_FUNC_ARG;

    if (size != SrpHashSize(srp->type))
        return BUFFER_E;

    r = SrpHashFinal(srp->side == SRP_CLIENT_SIDE ? &srp->server_proof
                                                  : &srp->client_proof, digest);

    if (srp->side == SRP_SERVER_SIDE) {
        /* server proof = H( A | client proof | K) */
        if (!r) r = SrpHashUpdate(&srp->server_proof, proof, size);
        if (!r) r = SrpHashUpdate(&srp->server_proof, srp->key, srp->keySz);
    }

    if (!r && XMEMCMP(proof, digest, size) != 0)
        r = SRP_VERIFY_E;

    return r;
}

#endif /* WOLFCRYPT_HAVE_SRP */
