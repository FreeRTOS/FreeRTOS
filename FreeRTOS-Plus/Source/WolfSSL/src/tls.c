/* tls.c
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


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#include <wolfssl/ssl.h>
#include <wolfssl/internal.h>
#include <wolfssl/error-ssl.h>
#include <wolfssl/wolfcrypt/hmac.h>
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #include <wolfcrypt/src/misc.c>
#endif



#ifndef NO_TLS


#ifndef WOLFSSL_HAVE_MIN
#define WOLFSSL_HAVE_MIN

    static INLINE word32 min(word32 a, word32 b)
    {
        return a > b ? b : a;
    }

#endif /* WOLFSSL_HAVE_MIN */


#ifdef WOLFSSL_SHA384
    #define P_HASH_MAX_SIZE SHA384_DIGEST_SIZE
#else
    #define P_HASH_MAX_SIZE SHA256_DIGEST_SIZE
#endif

/* compute p_hash for MD5, SHA-1, SHA-256, or SHA-384 for TLSv1 PRF */
static int p_hash(byte* result, word32 resLen, const byte* secret,
                   word32 secLen, const byte* seed, word32 seedLen, int hash)
{
    word32 len = P_HASH_MAX_SIZE;
    word32 times;
    word32 lastLen;
    word32 lastTime;
    word32 i;
    word32 idx = 0;
    int    ret = 0;
#ifdef WOLFSSL_SMALL_STACK
    byte*  previous;
    byte*  current;
    Hmac*  hmac;
#else
    byte   previous[P_HASH_MAX_SIZE];  /* max size */
    byte   current[P_HASH_MAX_SIZE];   /* max size */
    Hmac   hmac[1];
#endif

#ifdef WOLFSSL_SMALL_STACK
    previous = (byte*)XMALLOC(P_HASH_MAX_SIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    current  = (byte*)XMALLOC(P_HASH_MAX_SIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    hmac     = (Hmac*)XMALLOC(sizeof(Hmac),    NULL, DYNAMIC_TYPE_TMP_BUFFER);

    if (previous == NULL || current == NULL || hmac == NULL) {
        if (previous) XFREE(previous, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (current)  XFREE(current,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (hmac)     XFREE(hmac,     NULL, DYNAMIC_TYPE_TMP_BUFFER);

        return MEMORY_E;
    }
#endif

    switch (hash) {
        #ifndef NO_MD5
            case md5_mac:
                hash = MD5;
                len  = MD5_DIGEST_SIZE;
            break;
        #endif

        #ifndef NO_SHA256
            case sha256_mac:
                hash = SHA256;
                len  = SHA256_DIGEST_SIZE;
            break;
        #endif

        #ifdef WOLFSSL_SHA384
            case sha384_mac:
                hash = SHA384;
                len  = SHA384_DIGEST_SIZE;
            break;
        #endif

        #ifndef NO_SHA
            case sha_mac:
            default:
                hash = SHA;
                len  = SHA_DIGEST_SIZE;
            break;
        #endif
    }

    times   = resLen / len;
    lastLen = resLen % len;

    if (lastLen)
        times += 1;

    lastTime = times - 1;

    if ((ret = wc_HmacSetKey(hmac, hash, secret, secLen)) == 0) {
        if ((ret = wc_HmacUpdate(hmac, seed, seedLen)) == 0) { /* A0 = seed */
            if ((ret = wc_HmacFinal(hmac, previous)) == 0) {   /* A1 */
                for (i = 0; i < times; i++) {
                    ret = wc_HmacUpdate(hmac, previous, len);
                    if (ret != 0)
                        break;
                    ret = wc_HmacUpdate(hmac, seed, seedLen);
                    if (ret != 0)
                        break;
                    ret = wc_HmacFinal(hmac, current);
                    if (ret != 0)
                        break;

                    if ((i == lastTime) && lastLen)
                        XMEMCPY(&result[idx], current,
                                                 min(lastLen, P_HASH_MAX_SIZE));
                    else {
                        XMEMCPY(&result[idx], current, len);
                        idx += len;
                        ret = wc_HmacUpdate(hmac, previous, len);
                        if (ret != 0)
                            break;
                        ret = wc_HmacFinal(hmac, previous);
                        if (ret != 0)
                            break;
                    }
                }
            }
        }
    }

    ForceZero(previous,  P_HASH_MAX_SIZE);
    ForceZero(current,   P_HASH_MAX_SIZE);
    ForceZero(hmac,      sizeof(Hmac));

#ifdef WOLFSSL_SMALL_STACK
    XFREE(previous, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(current,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(hmac,     NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

#undef P_HASH_MAX_SIZE


#ifndef NO_OLD_TLS

/* calculate XOR for TLSv1 PRF */
static INLINE void get_xor(byte *digest, word32 digLen, byte* md5, byte* sha)
{
    word32 i;

    for (i = 0; i < digLen; i++)
        digest[i] = md5[i] ^ sha[i];
}


/* compute TLSv1 PRF (pseudo random function using HMAC) */
static int doPRF(byte* digest, word32 digLen, const byte* secret,word32 secLen,
                 const byte* label, word32 labLen, const byte* seed,
                 word32 seedLen)
{
    int    ret  = 0;
    word32 half = (secLen + 1) / 2;

#ifdef WOLFSSL_SMALL_STACK
    byte* md5_half;
    byte* sha_half;
    byte* labelSeed;
    byte* md5_result;
    byte* sha_result;
#else
    byte  md5_half[MAX_PRF_HALF];     /* half is real size */
    byte  sha_half[MAX_PRF_HALF];     /* half is real size */
    byte  labelSeed[MAX_PRF_LABSEED]; /* labLen + seedLen is real size */
    byte  md5_result[MAX_PRF_DIG];    /* digLen is real size */
    byte  sha_result[MAX_PRF_DIG];    /* digLen is real size */
#endif

    if (half > MAX_PRF_HALF)
        return BUFFER_E;
    if (labLen + seedLen > MAX_PRF_LABSEED)
        return BUFFER_E;
    if (digLen > MAX_PRF_DIG)
        return BUFFER_E;

#ifdef WOLFSSL_SMALL_STACK
    md5_half   = (byte*)XMALLOC(MAX_PRF_HALF,    NULL, DYNAMIC_TYPE_TMP_BUFFER);
    sha_half   = (byte*)XMALLOC(MAX_PRF_HALF,    NULL, DYNAMIC_TYPE_TMP_BUFFER);
    labelSeed  = (byte*)XMALLOC(MAX_PRF_LABSEED, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    md5_result = (byte*)XMALLOC(MAX_PRF_DIG,     NULL, DYNAMIC_TYPE_TMP_BUFFER);
    sha_result = (byte*)XMALLOC(MAX_PRF_DIG,     NULL, DYNAMIC_TYPE_TMP_BUFFER);

    if (md5_half == NULL || sha_half == NULL || labelSeed == NULL ||
                                     md5_result == NULL || sha_result == NULL) {
        if (md5_half)   XFREE(md5_half,   NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (sha_half)   XFREE(sha_half,   NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (labelSeed)  XFREE(labelSeed,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (md5_result) XFREE(md5_result, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (sha_result) XFREE(sha_result, NULL, DYNAMIC_TYPE_TMP_BUFFER);

        return MEMORY_E;
    }
#endif

    XMEMSET(md5_result, 0, digLen);
    XMEMSET(sha_result, 0, digLen);

    XMEMCPY(md5_half, secret, half);
    XMEMCPY(sha_half, secret + half - secLen % 2, half);

    XMEMCPY(labelSeed, label, labLen);
    XMEMCPY(labelSeed + labLen, seed, seedLen);

    if ((ret = p_hash(md5_result, digLen, md5_half, half, labelSeed,
                                             labLen + seedLen, md5_mac)) == 0) {
        if ((ret = p_hash(sha_result, digLen, sha_half, half, labelSeed,
                                             labLen + seedLen, sha_mac)) == 0) {
            get_xor(digest, digLen, md5_result, sha_result);
        }
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(md5_half,   NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(sha_half,   NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(labelSeed,  NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(md5_result, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(sha_result, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

#endif


/* Wrapper to call straight thru to p_hash in TSL 1.2 cases to remove stack
   use */
static int PRF(byte* digest, word32 digLen, const byte* secret, word32 secLen,
            const byte* label, word32 labLen, const byte* seed, word32 seedLen,
            int useAtLeastSha256, int hash_type)
{
    int ret = 0;

    if (useAtLeastSha256) {
#ifdef WOLFSSL_SMALL_STACK
        byte* labelSeed;
#else
        byte labelSeed[MAX_PRF_LABSEED]; /* labLen + seedLen is real size */
#endif

        if (labLen + seedLen > MAX_PRF_LABSEED)
            return BUFFER_E;

#ifdef WOLFSSL_SMALL_STACK
        labelSeed = (byte*)XMALLOC(MAX_PRF_LABSEED, NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
        if (labelSeed == NULL)
           return MEMORY_E;
#endif

        XMEMCPY(labelSeed, label, labLen);
        XMEMCPY(labelSeed + labLen, seed, seedLen);

        /* If a cipher suite wants an algorithm better than sha256, it
         * should use better. */
        if (hash_type < sha256_mac)
            hash_type = sha256_mac;
        ret = p_hash(digest, digLen, secret, secLen, labelSeed,
                     labLen + seedLen, hash_type);

#ifdef WOLFSSL_SMALL_STACK
        XFREE(labelSeed, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
    }
#ifndef NO_OLD_TLS
    else {
        ret = doPRF(digest, digLen, secret, secLen, label, labLen, seed,
                    seedLen);
    }
#endif

    return ret;
}


#ifdef WOLFSSL_SHA384
    #define HSHASH_SZ SHA384_DIGEST_SIZE
#else
    #define HSHASH_SZ FINISHED_SZ
#endif


int BuildTlsFinished(WOLFSSL* ssl, Hashes* hashes, const byte* sender)
{
    const byte* side;
    byte        handshake_hash[HSHASH_SZ];
    word32      hashSz = FINISHED_SZ;

#ifndef NO_OLD_TLS
    wc_Md5GetHash(&ssl->hsHashes->hashMd5, handshake_hash);
    wc_ShaGetHash(&ssl->hsHashes->hashSha, &handshake_hash[MD5_DIGEST_SIZE]);
#endif

    if (IsAtLeastTLSv1_2(ssl)) {
#ifndef NO_SHA256
        if (ssl->specs.mac_algorithm <= sha256_mac) {
            int ret = wc_Sha256GetHash(&ssl->hsHashes->hashSha256,handshake_hash);

            if (ret != 0)
                return ret;

            hashSz = SHA256_DIGEST_SIZE;
        }
#endif
#ifdef WOLFSSL_SHA384
        if (ssl->specs.mac_algorithm == sha384_mac) {
            int ret = wc_Sha384Final(&ssl->hsHashes->hashSha384,handshake_hash);

            if (ret != 0)
                return ret;

            hashSz = SHA384_DIGEST_SIZE;
        }
#endif
    }

    if ( XSTRNCMP((const char*)sender, (const char*)client, SIZEOF_SENDER) == 0)
        side = tls_client;
    else
        side = tls_server;

    return PRF((byte*)hashes, TLS_FINISHED_SZ, ssl->arrays->masterSecret,
               SECRET_LEN, side, FINISHED_LABEL_SZ, handshake_hash, hashSz,
               IsAtLeastTLSv1_2(ssl), ssl->specs.mac_algorithm);
}


#ifndef NO_OLD_TLS

ProtocolVersion MakeTLSv1(void)
{
    ProtocolVersion pv;
    pv.major = SSLv3_MAJOR;
    pv.minor = TLSv1_MINOR;

    return pv;
}


ProtocolVersion MakeTLSv1_1(void)
{
    ProtocolVersion pv;
    pv.major = SSLv3_MAJOR;
    pv.minor = TLSv1_1_MINOR;

    return pv;
}

#endif


ProtocolVersion MakeTLSv1_2(void)
{
    ProtocolVersion pv;
    pv.major = SSLv3_MAJOR;
    pv.minor = TLSv1_2_MINOR;

    return pv;
}


static const byte master_label[MASTER_LABEL_SZ + 1] = "master secret";
static const byte key_label   [KEY_LABEL_SZ + 1]    = "key expansion";


/* External facing wrapper so user can call as well, 0 on success */
int wolfSSL_DeriveTlsKeys(byte* key_data, word32 keyLen,
                         const byte* ms, word32 msLen,
                         const byte* sr, const byte* cr,
                         int tls1_2, int hash_type)
{
    byte  seed[SEED_LEN];

    XMEMCPY(seed,           sr, RAN_LEN);
    XMEMCPY(seed + RAN_LEN, cr, RAN_LEN);

    return PRF(key_data, keyLen, ms, msLen, key_label, KEY_LABEL_SZ,
               seed, SEED_LEN, tls1_2, hash_type);
}


int DeriveTlsKeys(WOLFSSL* ssl)
{
    int   ret;
    int   length = 2 * ssl->specs.hash_size +
                   2 * ssl->specs.key_size  +
                   2 * ssl->specs.iv_size;
#ifdef WOLFSSL_SMALL_STACK
    byte* key_data;
#else
    byte  key_data[MAX_PRF_DIG];
#endif

#ifdef WOLFSSL_SMALL_STACK
    key_data = (byte*)XMALLOC(MAX_PRF_DIG, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (key_data == NULL) {
        return MEMORY_E;
    }
#endif

    ret = wolfSSL_DeriveTlsKeys(key_data, length,
                           ssl->arrays->masterSecret, SECRET_LEN,
                           ssl->arrays->serverRandom, ssl->arrays->clientRandom,
                           IsAtLeastTLSv1_2(ssl), ssl->specs.mac_algorithm);
    if (ret == 0)
        ret = StoreKeys(ssl, key_data);

#ifdef WOLFSSL_SMALL_STACK
    XFREE(key_data, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}


/* External facing wrapper so user can call as well, 0 on success */
int wolfSSL_MakeTlsMasterSecret(byte* ms, word32 msLen,
                               const byte* pms, word32 pmsLen,
                               const byte* cr, const byte* sr,
                               int tls1_2, int hash_type)
{
    byte  seed[SEED_LEN];

    XMEMCPY(seed,           cr, RAN_LEN);
    XMEMCPY(seed + RAN_LEN, sr, RAN_LEN);

    return PRF(ms, msLen, pms, pmsLen, master_label, MASTER_LABEL_SZ,
               seed, SEED_LEN, tls1_2, hash_type);
}


int MakeTlsMasterSecret(WOLFSSL* ssl)
{
    int   ret;

    ret = wolfSSL_MakeTlsMasterSecret(ssl->arrays->masterSecret, SECRET_LEN,
              ssl->arrays->preMasterSecret, ssl->arrays->preMasterSz,
              ssl->arrays->clientRandom, ssl->arrays->serverRandom,
              IsAtLeastTLSv1_2(ssl), ssl->specs.mac_algorithm);

    if (ret == 0) {
    #ifdef SHOW_SECRETS
        int i;

        printf("master secret: ");
        for (i = 0; i < SECRET_LEN; i++)
            printf("%02x", ssl->arrays->masterSecret[i]);
        printf("\n");
    #endif

        ret = DeriveTlsKeys(ssl);
    }

    return ret;
}


/* Used by EAP-TLS and EAP-TTLS to derive keying material from
 * the master_secret. */
int wolfSSL_make_eap_keys(WOLFSSL* ssl, void* msk, unsigned int len,
                                                              const char* label)
{
    int   ret;
#ifdef WOLFSSL_SMALL_STACK
    byte* seed;
#else
    byte  seed[SEED_LEN];
#endif

#ifdef WOLFSSL_SMALL_STACK
    seed = (byte*)XMALLOC(SEED_LEN, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (seed == NULL)
        return MEMORY_E;
#endif

    /*
     * As per RFC-5281, the order of the client and server randoms is reversed
     * from that used by the TLS protocol to derive keys.
     */
    XMEMCPY(seed,           ssl->arrays->clientRandom, RAN_LEN);
    XMEMCPY(seed + RAN_LEN, ssl->arrays->serverRandom, RAN_LEN);

    ret = PRF((byte*)msk, len, ssl->arrays->masterSecret, SECRET_LEN,
              (const byte *)label, (word32)strlen(label), seed, SEED_LEN,
              IsAtLeastTLSv1_2(ssl), ssl->specs.mac_algorithm);

#ifdef WOLFSSL_SMALL_STACK
    XFREE(seed, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}


/*** next for static INLINE s copied internal.c ***/

/* convert 16 bit integer to opaque */
static INLINE void c16toa(word16 u16, byte* c)
{
    c[0] = (u16 >> 8) & 0xff;
    c[1] =  u16 & 0xff;
}

#ifdef HAVE_TLS_EXTENSIONS
/* convert opaque to 16 bit integer */
static INLINE void ato16(const byte* c, word16* u16)
{
    *u16 = (c[0] << 8) | (c[1]);
}

#ifdef HAVE_SNI
/* convert a 24 bit integer into a 32 bit one */
static INLINE void c24to32(const word24 u24, word32* u32)
{
    *u32 = (u24[0] << 16) | (u24[1] << 8) | u24[2];
}
#endif
#endif

/* convert 32 bit integer to opaque */
static INLINE void c32toa(word32 u32, byte* c)
{
    c[0] = (u32 >> 24) & 0xff;
    c[1] = (u32 >> 16) & 0xff;
    c[2] = (u32 >>  8) & 0xff;
    c[3] =  u32 & 0xff;
}


static INLINE word32 GetSEQIncrement(WOLFSSL* ssl, int verify)
{
#ifdef WOLFSSL_DTLS
    if (ssl->options.dtls) {
        if (verify)
            return ssl->keys.dtls_state.curSeq; /* explicit from peer */
        else
            return ssl->keys.dtls_sequence_number - 1; /* already incremented */
    }
#endif
    if (verify)
        return ssl->keys.peer_sequence_number++;
    else
        return ssl->keys.sequence_number++;
}


#ifdef WOLFSSL_DTLS

static INLINE word32 GetEpoch(WOLFSSL* ssl, int verify)
{
    if (verify)
        return ssl->keys.dtls_state.curEpoch;
    else
        return ssl->keys.dtls_epoch;
}

#endif /* WOLFSSL_DTLS */


/*** end copy ***/


/* return HMAC digest type in wolfSSL format */
int wolfSSL_GetHmacType(WOLFSSL* ssl)
{
    if (ssl == NULL)
        return BAD_FUNC_ARG;

    switch (ssl->specs.mac_algorithm) {
        #ifndef NO_MD5
        case md5_mac:
        {
            return MD5;
        }
        #endif
        #ifndef NO_SHA256
        case sha256_mac:
        {
            return SHA256;
        }
        #endif
        #ifdef WOLFSSL_SHA384
        case sha384_mac:
        {
            return SHA384;
        }

        #endif
        #ifndef NO_SHA
        case sha_mac:
        {
            return SHA;
        }
        #endif
        #ifdef HAVE_BLAKE2
        case blake2b_mac:
        {
            return BLAKE2B_ID;
        }
        #endif
        default:
        {
            return SSL_FATAL_ERROR;
        }
    }
}


int wolfSSL_SetTlsHmacInner(WOLFSSL* ssl, byte* inner, word32 sz, int content,
                           int verify)
{
    if (ssl == NULL || inner == NULL)
        return BAD_FUNC_ARG;

    XMEMSET(inner, 0, WOLFSSL_TLS_HMAC_INNER_SZ);

#ifdef WOLFSSL_DTLS
    if (ssl->options.dtls)
        c16toa((word16)GetEpoch(ssl, verify), inner);
#endif
    c32toa(GetSEQIncrement(ssl, verify), &inner[sizeof(word32)]);
    inner[SEQ_SZ] = (byte)content;
    inner[SEQ_SZ + ENUM_LEN]            = ssl->version.major;
    inner[SEQ_SZ + ENUM_LEN + ENUM_LEN] = ssl->version.minor;
    c16toa((word16)sz, inner + SEQ_SZ + ENUM_LEN + VERSION_SZ);

    return 0;
}


/* TLS type HMAC */
int TLS_hmac(WOLFSSL* ssl, byte* digest, const byte* in, word32 sz,
              int content, int verify)
{
    Hmac hmac;
    int  ret;
    byte myInner[WOLFSSL_TLS_HMAC_INNER_SZ];

    if (ssl == NULL)
        return BAD_FUNC_ARG;

#ifdef HAVE_FUZZER
    if (ssl->fuzzerCb)
        ssl->fuzzerCb(ssl, in, sz, FUZZ_HMAC, ssl->fuzzerCtx);
#endif

    wolfSSL_SetTlsHmacInner(ssl, myInner, sz, content, verify);

    ret = wc_HmacSetKey(&hmac, wolfSSL_GetHmacType(ssl),
                     wolfSSL_GetMacSecret(ssl, verify), ssl->specs.hash_size);
    if (ret != 0)
        return ret;
    ret = wc_HmacUpdate(&hmac, myInner, sizeof(myInner));
    if (ret != 0)
        return ret;
    ret = wc_HmacUpdate(&hmac, in, sz);                                /* content */
    if (ret != 0)
        return ret;
    ret = wc_HmacFinal(&hmac, digest);
    if (ret != 0)
        return ret;

    return 0;
}

#ifdef HAVE_TLS_EXTENSIONS


/** Supports up to 64 flags. Update as needed. */
#define SEMAPHORE_SIZE 8


static INLINE word16 TLSX_ToSemaphore(word16 type)
{
    switch (type) {
        case SECURE_RENEGOTIATION:
            return 63;

        default:
            if (type > 62) {
                /* This message SHOULD only happens during the adding of
                   new TLS extensions in which its IANA number overflows
                   the current semaphore's range, or if its number already
                   is assigned to be used by another extension.
                   Use this check value for the new extension and decrement
                   the check value by one. */
                WOLFSSL_MSG("### TLSX semaphore colision or overflow detected!");
            }
    }

    return type;
}


#define IS_OFF(semaphore, light) \
    ((semaphore)[(light) / 8] ^  (byte) (0x01 << ((light) % 8)))


#define TURN_ON(semaphore, light) \
    ((semaphore)[(light) / 8] |= (byte) (0x01 << ((light) % 8)))


static int TLSX_Push(TLSX** list, TLSX_Type type, void* data)
{
    TLSX* extension;

    extension = (TLSX*)XMALLOC(sizeof(TLSX), 0, DYNAMIC_TYPE_TLSX);
    if (extension == NULL)
        return MEMORY_E;

    extension->type = type;
    extension->data = data;
    extension->resp = 0;
    extension->next = *list;
    *list = extension;

    /* remove duplicated extensions, there should be only one of each type. */
    do {
        if (extension->next && extension->next->type == type) {
            TLSX *next = extension->next;

            extension->next = next->next;
            next->next = NULL;

            TLSX_FreeAll(next);

            /* there is no way to occur more than */
            /* two extensions of the same type.   */
            break;
        }
    } while ((extension = extension->next));

    return 0;
}


#ifndef NO_WOLFSSL_SERVER

void TLSX_SetResponse(WOLFSSL* ssl, TLSX_Type type);

void TLSX_SetResponse(WOLFSSL* ssl, TLSX_Type type)
{
    TLSX *ext = TLSX_Find(ssl->extensions, type);

    if (ext)
        ext->resp = 1;
}

#endif

/* SNI - Server Name Indication */

#ifdef HAVE_SNI

static void TLSX_SNI_Free(SNI* sni)
{
    if (sni) {
        switch (sni->type) {
            case WOLFSSL_SNI_HOST_NAME:
                XFREE(sni->data.host_name, 0, DYNAMIC_TYPE_TLSX);
            break;
        }

        XFREE(sni, 0, DYNAMIC_TYPE_TLSX);
    }
}

static void TLSX_SNI_FreeAll(SNI* list)
{
    SNI* sni;

    while ((sni = list)) {
        list = sni->next;
        TLSX_SNI_Free(sni);
    }
}

static int TLSX_SNI_Append(SNI** list, byte type, const void* data, word16 size)
{
    SNI* sni;

    if (list == NULL)
        return BAD_FUNC_ARG;

    if ((sni = XMALLOC(sizeof(SNI), 0, DYNAMIC_TYPE_TLSX)) == NULL)
        return MEMORY_E;

    switch (type) {
        case WOLFSSL_SNI_HOST_NAME: {
            sni->data.host_name = XMALLOC(size + 1, 0, DYNAMIC_TYPE_TLSX);

            if (sni->data.host_name) {
                XSTRNCPY(sni->data.host_name, (const char*)data, size);
                sni->data.host_name[size] = 0;
            } else {
                XFREE(sni, 0, DYNAMIC_TYPE_TLSX);
                return MEMORY_E;
            }
        }
        break;

        default: /* invalid type */
            XFREE(sni, 0, DYNAMIC_TYPE_TLSX);
            return BAD_FUNC_ARG;
    }

    sni->type = type;
    sni->next = *list;

#ifndef NO_WOLFSSL_SERVER
    sni->options = 0;
    sni->status  = WOLFSSL_SNI_NO_MATCH;
#endif

    *list = sni;

    return 0;
}

static word16 TLSX_SNI_GetSize(SNI* list)
{
    SNI* sni;
    word16 length = OPAQUE16_LEN; /* list length */

    while ((sni = list)) {
        list = sni->next;

        length += ENUM_LEN + OPAQUE16_LEN; /* sni type + sni length */

        switch (sni->type) {
            case WOLFSSL_SNI_HOST_NAME:
                length += XSTRLEN((char*)sni->data.host_name);
            break;
        }
    }

    return length;
}

static word16 TLSX_SNI_Write(SNI* list, byte* output)
{
    SNI* sni;
    word16 length = 0;
    word16 offset = OPAQUE16_LEN; /* list length offset */

    while ((sni = list)) {
        list = sni->next;

        output[offset++] = sni->type; /* sni type */

        switch (sni->type) {
            case WOLFSSL_SNI_HOST_NAME:
                length = XSTRLEN((char*)sni->data.host_name);

                c16toa(length, output + offset); /* sni length */
                offset += OPAQUE16_LEN;

                XMEMCPY(output + offset, sni->data.host_name, length);

                offset += length;
            break;
        }
    }

    c16toa(offset - OPAQUE16_LEN, output); /* writing list length */

    return offset;
}

static SNI* TLSX_SNI_Find(SNI *list, byte type)
{
    SNI *sni = list;

    while (sni && sni->type != type)
        sni = sni->next;

    return sni;
}

#ifndef NO_WOLFSSL_SERVER
static void TLSX_SNI_SetStatus(TLSX* extensions, byte type, byte status)
{
    TLSX* extension = TLSX_Find(extensions, SERVER_NAME_INDICATION);
    SNI* sni = TLSX_SNI_Find(extension ? extension->data : NULL, type);

    if (sni) {
        sni->status = status;
        WOLFSSL_MSG("SNI did match!");
    }
}

byte TLSX_SNI_Status(TLSX* extensions, byte type)
{
    TLSX* extension = TLSX_Find(extensions, SERVER_NAME_INDICATION);
    SNI* sni = TLSX_SNI_Find(extension ? extension->data : NULL, type);

    if (sni)
        return sni->status;

    return 0;
}
#endif

static int TLSX_SNI_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                                                 byte isRequest)
{
#ifndef NO_WOLFSSL_SERVER
    word16 size = 0;
    word16 offset = 0;
#endif

    TLSX *extension = TLSX_Find(ssl->extensions, SERVER_NAME_INDICATION);

    if (!extension)
        extension = TLSX_Find(ssl->ctx->extensions, SERVER_NAME_INDICATION);

    if (!extension || !extension->data)
        return isRequest ? 0 : BUFFER_ERROR; /* not using SNI OR unexpected
                                                SNI response from server. */

    if (!isRequest)
        return length ? BUFFER_ERROR : 0; /* SNI response must be empty!
                                             Nothing else to do. */

#ifndef NO_WOLFSSL_SERVER

    if (OPAQUE16_LEN > length)
        return BUFFER_ERROR;

    ato16(input, &size);
    offset += OPAQUE16_LEN;

    /* validating sni list length */
    if (length != OPAQUE16_LEN + size)
        return BUFFER_ERROR;

    for (size = 0; offset < length; offset += size) {
        SNI *sni;
        byte type = input[offset++];

        if (offset + OPAQUE16_LEN > length)
            return BUFFER_ERROR;

        ato16(input + offset, &size);
        offset += OPAQUE16_LEN;

        if (offset + size > length)
            return BUFFER_ERROR;

        if (!(sni = TLSX_SNI_Find((SNI*)extension->data, type))) {
            continue; /* not using this SNI type */
        }

        switch(type) {
            case WOLFSSL_SNI_HOST_NAME: {
                byte matched = (XSTRLEN(sni->data.host_name) == size)
                            && (XSTRNCMP(sni->data.host_name,
                                       (const char*)input + offset, size) == 0);

                if (matched || sni->options & WOLFSSL_SNI_ANSWER_ON_MISMATCH) {
                    int r = TLSX_UseSNI(&ssl->extensions,
                                                    type, input + offset, size);

                    if (r != SSL_SUCCESS) return r; /* throw error */

                    TLSX_SNI_SetStatus(ssl->extensions, type,
                      matched ? WOLFSSL_SNI_REAL_MATCH : WOLFSSL_SNI_FAKE_MATCH);

                } else if (!(sni->options & WOLFSSL_SNI_CONTINUE_ON_MISMATCH)) {
                    SendAlert(ssl, alert_fatal, unrecognized_name);

                    return UNKNOWN_SNI_HOST_NAME_E;
                }
                break;
            }
        }

        TLSX_SetResponse(ssl, SERVER_NAME_INDICATION);
    }

#endif

    return 0;
}

int TLSX_UseSNI(TLSX** extensions, byte type, const void* data, word16 size)
{
    TLSX* extension = TLSX_Find(*extensions, SERVER_NAME_INDICATION);
    SNI*  sni       = NULL;
    int   ret       = 0;

    if (extensions == NULL || data == NULL)
        return BAD_FUNC_ARG;

    if ((ret = TLSX_SNI_Append(&sni, type, data, size)) != 0)
        return ret;

    if (!extension) {
        if ((ret = TLSX_Push(extensions, SERVER_NAME_INDICATION, (void*)sni))
                                                                         != 0) {
            TLSX_SNI_Free(sni);
            return ret;
        }
    }
    else {
        /* push new SNI object to extension data. */
        sni->next = (SNI*)extension->data;
        extension->data = (void*)sni;

        /* look for another server name of the same type to remove */
        do {
            if (sni->next && sni->next->type == type) {
                SNI *next = sni->next;

                sni->next = next->next;
                TLSX_SNI_Free(next);

                break;
            }
        } while ((sni = sni->next));
    }

    return SSL_SUCCESS;
}

#ifndef NO_WOLFSSL_SERVER
word16 TLSX_SNI_GetRequest(TLSX* extensions, byte type, void** data)
{
    TLSX* extension = TLSX_Find(extensions, SERVER_NAME_INDICATION);
    SNI* sni = TLSX_SNI_Find(extension ? extension->data : NULL, type);

    if (sni && sni->status != WOLFSSL_SNI_NO_MATCH) {
        switch (sni->type) {
            case WOLFSSL_SNI_HOST_NAME:
                *data = sni->data.host_name;
                return XSTRLEN(*data);
        }
    }

    return 0;
}

void TLSX_SNI_SetOptions(TLSX* extensions, byte type, byte options)
{
    TLSX* extension = TLSX_Find(extensions, SERVER_NAME_INDICATION);
    SNI* sni = TLSX_SNI_Find(extension ? extension->data : NULL, type);

    if (sni)
        sni->options = options;
}

int TLSX_SNI_GetFromBuffer(const byte* clientHello, word32 helloSz,
                           byte type, byte* sni, word32* inOutSz)
{
    word32 offset = 0;
    word32 len32  = 0;
    word16 len16  = 0;

    if (helloSz < RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ + CLIENT_HELLO_FIRST)
        return INCOMPLETE_DATA;

    /* TLS record header */
    if ((enum ContentType) clientHello[offset++] != handshake)
        return BUFFER_ERROR;

    if (clientHello[offset++] != SSLv3_MAJOR)
        return BUFFER_ERROR;

    if (clientHello[offset++] < TLSv1_MINOR)
        return SNI_UNSUPPORTED;

    ato16(clientHello + offset, &len16);
    offset += OPAQUE16_LEN;

    if (offset + len16 > helloSz)
        return INCOMPLETE_DATA;

    /* Handshake header */
    if ((enum HandShakeType) clientHello[offset] != client_hello)
        return BUFFER_ERROR;

    c24to32(clientHello + offset + 1, &len32);
    offset += HANDSHAKE_HEADER_SZ;

    if (offset + len32 > helloSz)
        return BUFFER_ERROR;

    /* client hello */
    offset += VERSION_SZ + RAN_LEN; /* version, random */

    if (helloSz < offset + clientHello[offset])
        return BUFFER_ERROR;

    offset += ENUM_LEN + clientHello[offset]; /* skip session id */

    /* cypher suites */
    if (helloSz < offset + OPAQUE16_LEN)
        return BUFFER_ERROR;

    ato16(clientHello + offset, &len16);
    offset += OPAQUE16_LEN;

    if (helloSz < offset + len16)
        return BUFFER_ERROR;

    offset += len16; /* skip cypher suites */

    /* compression methods */
    if (helloSz < offset + 1)
        return BUFFER_ERROR;

    if (helloSz < offset + clientHello[offset])
        return BUFFER_ERROR;

    offset += ENUM_LEN + clientHello[offset]; /* skip compression methods */

    /* extensions */
    if (helloSz < offset + OPAQUE16_LEN)
        return 0; /* no extensions in client hello. */

    ato16(clientHello + offset, &len16);
    offset += OPAQUE16_LEN;

    if (helloSz < offset + len16)
        return BUFFER_ERROR;

    while (len16 >= OPAQUE16_LEN + OPAQUE16_LEN) {
        word16 extType;
        word16 extLen;

        ato16(clientHello + offset, &extType);
        offset += OPAQUE16_LEN;

        ato16(clientHello + offset, &extLen);
        offset += OPAQUE16_LEN;

        if (helloSz < offset + extLen)
            return BUFFER_ERROR;

        if (extType != SERVER_NAME_INDICATION) {
            offset += extLen; /* skip extension */
        } else {
            word16 listLen;

            ato16(clientHello + offset, &listLen);
            offset += OPAQUE16_LEN;

            if (helloSz < offset + listLen)
                return BUFFER_ERROR;

            while (listLen > ENUM_LEN + OPAQUE16_LEN) {
                byte   sniType = clientHello[offset++];
                word16 sniLen;

                ato16(clientHello + offset, &sniLen);
                offset += OPAQUE16_LEN;

                if (helloSz < offset + sniLen)
                    return BUFFER_ERROR;

                if (sniType != type) {
                    offset  += sniLen;
                    listLen -= min(ENUM_LEN + OPAQUE16_LEN + sniLen, listLen);
                    continue;
                }

                *inOutSz = min(sniLen, *inOutSz);
                XMEMCPY(sni, clientHello + offset, *inOutSz);

                return SSL_SUCCESS;
            }
        }

        len16 -= min(2 * OPAQUE16_LEN + extLen, len16);
    }

    return len16 ? BUFFER_ERROR : 0;
}

#endif

#define SNI_FREE_ALL TLSX_SNI_FreeAll
#define SNI_GET_SIZE TLSX_SNI_GetSize
#define SNI_WRITE    TLSX_SNI_Write
#define SNI_PARSE    TLSX_SNI_Parse

#else

#define SNI_FREE_ALL(list)
#define SNI_GET_SIZE(list)    0
#define SNI_WRITE(a, b)       0
#define SNI_PARSE(a, b, c, d) 0

#endif /* HAVE_SNI */

#ifdef HAVE_MAX_FRAGMENT

static word16 TLSX_MFL_Write(byte* data, byte* output)
{
    output[0] = data[0];

    return ENUM_LEN;
}

static int TLSX_MFL_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                                                 byte isRequest)
{
    if (length != ENUM_LEN)
        return BUFFER_ERROR;

    switch (*input) {
        case WOLFSSL_MFL_2_9 : ssl->max_fragment =  512; break;
        case WOLFSSL_MFL_2_10: ssl->max_fragment = 1024; break;
        case WOLFSSL_MFL_2_11: ssl->max_fragment = 2048; break;
        case WOLFSSL_MFL_2_12: ssl->max_fragment = 4096; break;
        case WOLFSSL_MFL_2_13: ssl->max_fragment = 8192; break;

        default:
            SendAlert(ssl, alert_fatal, illegal_parameter);

            return UNKNOWN_MAX_FRAG_LEN_E;
    }

#ifndef NO_WOLFSSL_SERVER
    if (isRequest) {
        int r = TLSX_UseMaxFragment(&ssl->extensions, *input);

        if (r != SSL_SUCCESS) return r; /* throw error */

        TLSX_SetResponse(ssl, MAX_FRAGMENT_LENGTH);
    }
#endif

    return 0;
}

int TLSX_UseMaxFragment(TLSX** extensions, byte mfl)
{
    byte* data = NULL;
    int   ret  = 0;

    if (extensions == NULL)
        return BAD_FUNC_ARG;

    if (mfl < WOLFSSL_MFL_2_9 || WOLFSSL_MFL_2_13 < mfl)
        return BAD_FUNC_ARG;

    if ((data = XMALLOC(ENUM_LEN, 0, DYNAMIC_TYPE_TLSX)) == NULL)
        return MEMORY_E;

    data[0] = mfl;

    /* push new MFL extension. */
    if ((ret = TLSX_Push(extensions, MAX_FRAGMENT_LENGTH, data)) != 0) {
        XFREE(data, 0, DYNAMIC_TYPE_TLSX);
        return ret;
    }

    return SSL_SUCCESS;
}


#define MFL_FREE_ALL(data) XFREE(data, 0, DYNAMIC_TYPE_TLSX)
#define MFL_GET_SIZE(data) ENUM_LEN
#define MFL_WRITE          TLSX_MFL_Write
#define MFL_PARSE          TLSX_MFL_Parse

#else

#define MFL_FREE_ALL(a)
#define MFL_GET_SIZE(a)       0
#define MFL_WRITE(a, b)       0
#define MFL_PARSE(a, b, c, d) 0

#endif /* HAVE_MAX_FRAGMENT */

#ifdef HAVE_TRUNCATED_HMAC

static int TLSX_THM_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                                                 byte isRequest)
{
    if (length != 0 || input == NULL)
        return BUFFER_ERROR;

#ifndef NO_WOLFSSL_SERVER
    if (isRequest) {
        int r = TLSX_UseTruncatedHMAC(&ssl->extensions);

        if (r != SSL_SUCCESS) return r; /* throw error */

        TLSX_SetResponse(ssl, TRUNCATED_HMAC);
    }
#endif

    ssl->truncated_hmac = 1;

    return 0;
}

int TLSX_UseTruncatedHMAC(TLSX** extensions)
{
    int ret = 0;

    if (extensions == NULL)
        return BAD_FUNC_ARG;

    if ((ret = TLSX_Push(extensions, TRUNCATED_HMAC, NULL)) != 0)
        return ret;

    return SSL_SUCCESS;
}

#define THM_PARSE TLSX_THM_Parse

#else

#define THM_PARSE(a, b, c, d) 0

#endif /* HAVE_TRUNCATED_HMAC */

#ifdef HAVE_SUPPORTED_CURVES

#ifndef HAVE_ECC
#error Elliptic Curves Extension requires Elliptic Curve Cryptography. \
       Use --enable-ecc in the configure script or define HAVE_ECC.
#endif

static void TLSX_EllipticCurve_FreeAll(EllipticCurve* list)
{
    EllipticCurve* curve;

    while ((curve = list)) {
        list = curve->next;
        XFREE(curve, 0, DYNAMIC_TYPE_TLSX);
    }
}

static int TLSX_EllipticCurve_Append(EllipticCurve** list, word16 name)
{
    EllipticCurve* curve;

    if (list == NULL)
        return BAD_FUNC_ARG;

    if ((curve = XMALLOC(sizeof(EllipticCurve), 0, DYNAMIC_TYPE_TLSX)) == NULL)
        return MEMORY_E;

    curve->name = name;
    curve->next = *list;

    *list = curve;

    return 0;
}

#ifndef NO_WOLFSSL_CLIENT

static void TLSX_EllipticCurve_ValidateRequest(WOLFSSL* ssl, byte* semaphore)
{
    int i;

    for (i = 0; i < ssl->suites->suiteSz; i+= 2)
        if (ssl->suites->suites[i] == ECC_BYTE)
            return;

    /* No elliptic curve suite found */
    TURN_ON(semaphore, TLSX_ToSemaphore(ELLIPTIC_CURVES));
}

static word16 TLSX_EllipticCurve_GetSize(EllipticCurve* list)
{
    EllipticCurve* curve;
    word16 length = OPAQUE16_LEN; /* list length */

    while ((curve = list)) {
        list = curve->next;
        length += OPAQUE16_LEN; /* curve length */
    }

    return length;
}

static word16 TLSX_EllipticCurve_WriteR(EllipticCurve* curve, byte* output);
static word16 TLSX_EllipticCurve_WriteR(EllipticCurve* curve, byte* output)
{
    word16 offset = 0;

    if (!curve)
        return offset;

    offset = TLSX_EllipticCurve_WriteR(curve->next, output);
    c16toa(curve->name, output + offset);

    return OPAQUE16_LEN + offset;
}

static word16 TLSX_EllipticCurve_Write(EllipticCurve* list, byte* output)
{
    word16 length = TLSX_EllipticCurve_WriteR(list, output + OPAQUE16_LEN);

    c16toa(length, output); /* writing list length */

    return OPAQUE16_LEN + length;
}

#endif /* NO_WOLFSSL_CLIENT */
#ifndef NO_WOLFSSL_SERVER

static int TLSX_EllipticCurve_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                                                 byte isRequest)
{
    word16 offset;
    word16 name;
    int r;

    (void) isRequest; /* shut up compiler! */

    if (OPAQUE16_LEN > length || length % OPAQUE16_LEN)
        return BUFFER_ERROR;

    ato16(input, &offset);

    /* validating curve list length */
    if (length != OPAQUE16_LEN + offset)
        return BUFFER_ERROR;

    while (offset) {
        ato16(input + offset, &name);
        offset -= OPAQUE16_LEN;

        r = TLSX_UseSupportedCurve(&ssl->extensions, name);

        if (r != SSL_SUCCESS) return r; /* throw error */
    }

    return 0;
}

int TLSX_ValidateEllipticCurves(WOLFSSL* ssl, byte first, byte second) {
    TLSX*          extension = (first == ECC_BYTE)
                             ? TLSX_Find(ssl->extensions, ELLIPTIC_CURVES)
                             : NULL;
    EllipticCurve* curve     = NULL;
    word32         oid       = 0;
    word16         octets    = 0; /* acording to 'ecc_set_type ecc_sets[];' */
    int            sig       = 0; /* valitade signature */
    int            key       = 0; /* validate key       */

    (void)oid;
    (void)octets;

    if (!extension)
        return 1; /* no suite restriction */

    for (curve = extension->data; curve && !(sig && key); curve = curve->next) {

        switch (curve->name) {
#if defined(HAVE_ALL_CURVES) || defined(HAVE_ECC160)
            case WOLFSSL_ECC_SECP160R1: oid = ECC_160R1; octets = 20; break;
#endif
#if defined(HAVE_ALL_CURVES) || defined(HAVE_ECC192)
            case WOLFSSL_ECC_SECP192R1: oid = ECC_192R1; octets = 24; break;
#endif
#if defined(HAVE_ALL_CURVES) || defined(HAVE_ECC224)
            case WOLFSSL_ECC_SECP224R1: oid = ECC_224R1; octets = 28; break;
#endif
#if defined(HAVE_ALL_CURVES) || !defined(NO_ECC256)
            case WOLFSSL_ECC_SECP256R1: oid = ECC_256R1; octets = 32; break;
#endif
#if defined(HAVE_ALL_CURVES) || defined(HAVE_ECC384)
            case WOLFSSL_ECC_SECP384R1: oid = ECC_384R1; octets = 48; break;
#endif
#if defined(HAVE_ALL_CURVES) || defined(HAVE_ECC521)
            case WOLFSSL_ECC_SECP521R1: oid = ECC_521R1; octets = 66; break;
#endif
            default: continue; /* unsupported curve */
        }

        switch (second) {
#ifndef NO_DSA
            /* ECDHE_ECDSA */
            case TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA:
            case TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA:
            case TLS_ECDHE_ECDSA_WITH_RC4_128_SHA:
            case TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA:
            case TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256:
            case TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA384:
            case TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256:
            case TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384:
            case TLS_ECDHE_ECDSA_WITH_AES_128_CCM_8:
            case TLS_ECDHE_ECDSA_WITH_AES_256_CCM_8:
                sig |= ssl->pkCurveOID == oid;
                key |= ssl->eccTempKeySz == octets;
            break;

            /* ECDH_ECDSA */
            case TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA:
            case TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA:
            case TLS_ECDH_ECDSA_WITH_RC4_128_SHA:
            case TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA:
            case TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA256:
            case TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA384:
            case TLS_ECDH_ECDSA_WITH_AES_128_GCM_SHA256:
            case TLS_ECDH_ECDSA_WITH_AES_256_GCM_SHA384:
                sig |= ssl->pkCurveOID == oid;
                key |= ssl->pkCurveOID == oid;
            break;
#endif
#ifndef NO_RSA
            /* ECDHE_RSA */
            case TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA:
            case TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA:
            case TLS_ECDHE_RSA_WITH_RC4_128_SHA:
            case TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA:
            case TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256:
            case TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384:
            case TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256:
            case TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384:
                sig = 1;
                key |= ssl->eccTempKeySz == octets;
            break;

            /* ECDH_RSA */
            case TLS_ECDH_RSA_WITH_AES_256_CBC_SHA:
            case TLS_ECDH_RSA_WITH_AES_128_CBC_SHA:
            case TLS_ECDH_RSA_WITH_RC4_128_SHA:
            case TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA:
            case TLS_ECDH_RSA_WITH_AES_128_CBC_SHA256:
            case TLS_ECDH_RSA_WITH_AES_256_CBC_SHA384:
            case TLS_ECDH_RSA_WITH_AES_128_GCM_SHA256:
            case TLS_ECDH_RSA_WITH_AES_256_GCM_SHA384:
                sig = 1;
                key |= ssl->pkCurveOID == oid;
            break;
#endif
            default:
                sig = 1;
                key = 1;
            break;
        }
    }

    return sig && key;
}

#endif /* NO_WOLFSSL_SERVER */

int TLSX_UseSupportedCurve(TLSX** extensions, word16 name)
{
    TLSX*          extension = TLSX_Find(*extensions, ELLIPTIC_CURVES);
    EllipticCurve* curve     = NULL;
    int            ret       = 0;

    if (extensions == NULL)
        return BAD_FUNC_ARG;

    if ((ret = TLSX_EllipticCurve_Append(&curve, name)) != 0)
        return ret;

    if (!extension) {
        if ((ret = TLSX_Push(extensions, ELLIPTIC_CURVES, curve)) != 0) {
            XFREE(curve, 0, DYNAMIC_TYPE_TLSX);
            return ret;
        }
    }
    else {
        /* push new EllipticCurve object to extension data. */
        curve->next = (EllipticCurve*)extension->data;
        extension->data = (void*)curve;

        /* look for another curve of the same name to remove (replacement) */
        do {
            if (curve->next && curve->next->name == name) {
                EllipticCurve *next = curve->next;

                curve->next = next->next;
                XFREE(next, 0, DYNAMIC_TYPE_TLSX);

                break;
            }
        } while ((curve = curve->next));
    }

    return SSL_SUCCESS;
}

#define EC_FREE_ALL         TLSX_EllipticCurve_FreeAll
#define EC_VALIDATE_REQUEST TLSX_EllipticCurve_ValidateRequest

#ifndef NO_WOLFSSL_CLIENT
#define EC_GET_SIZE TLSX_EllipticCurve_GetSize
#define EC_WRITE    TLSX_EllipticCurve_Write
#else
#define EC_GET_SIZE(list)         0
#define EC_WRITE(a, b)            0
#endif

#ifndef NO_WOLFSSL_SERVER
#define EC_PARSE TLSX_EllipticCurve_Parse
#else
#define EC_PARSE(a, b, c, d)      0
#endif

#else

#define EC_FREE_ALL(list)
#define EC_GET_SIZE(list)         0
#define EC_WRITE(a, b)            0
#define EC_PARSE(a, b, c, d)      0
#define EC_VALIDATE_REQUEST(a, b)

#endif /* HAVE_SUPPORTED_CURVES */

#ifdef HAVE_SECURE_RENEGOTIATION

static byte TLSX_SecureRenegotiation_GetSize(SecureRenegotiation* data,
                                                                  int isRequest)
{
    byte length = OPAQUE8_LEN; /* empty info length */

    if (data->enabled) {
        /* client sends client_verify_data only */
        length += TLS_FINISHED_SZ;

        /* server also sends server_verify_data */
        if (!isRequest)
            length += TLS_FINISHED_SZ;
    }

    return length;
}

static word16 TLSX_SecureRenegotiation_Write(SecureRenegotiation* data,
                                                    byte* output, int isRequest)
{
    word16 offset = OPAQUE8_LEN; /* RenegotiationInfo length */

    if (data->enabled) {
        /* client sends client_verify_data only */
        XMEMCPY(output + offset, data->client_verify_data, TLS_FINISHED_SZ);
        offset += TLS_FINISHED_SZ;

        /* server also sends server_verify_data */
        if (!isRequest) {
            XMEMCPY(output + offset, data->server_verify_data, TLS_FINISHED_SZ);
            offset += TLS_FINISHED_SZ;
        }
    }

    output[0] = offset - 1;  /* info length - self */

    return offset;
}

static int TLSX_SecureRenegotiation_Parse(WOLFSSL* ssl, byte* input,
                                                  word16 length, byte isRequest)
{
    int ret = SECURE_RENEGOTIATION_E;

    if (length >= OPAQUE8_LEN) {
        if (ssl->secure_renegotiation == NULL) {
        #ifndef NO_WOLFSSL_SERVER
            if (isRequest && *input == 0) {
                ret = 0;  /* don't reply, user didn't enable */
            }
        #endif
        }
        else if (isRequest) {
        #ifndef NO_WOLFSSL_SERVER
            if (*input == TLS_FINISHED_SZ) {
                /* TODO compare client_verify_data */
                ret = 0;
            }
        #endif
        }
        else {
        #ifndef NO_WOLFSSL_CLIENT
            if (!ssl->secure_renegotiation->enabled) {
                if (*input == 0) {
                    ssl->secure_renegotiation->enabled = 1;
                    ret = 0;
                }
            }
            else if (*input == 2 * TLS_FINISHED_SZ) {
                /* TODO compare client_verify_data and server_verify_data */
                ret = 0;
            }
        #endif
        }
    }

    if (ret != 0) {
        /* TODO: turn on fatal error at ssl level too */
        SendAlert(ssl, alert_fatal, handshake_failure);
    }

    return ret;
}

int TLSX_UseSecureRenegotiation(TLSX** extensions)
{
    int ret = 0;
    SecureRenegotiation* data = NULL;

    data = (SecureRenegotiation*)XMALLOC(sizeof(SecureRenegotiation), NULL,
                                                             DYNAMIC_TYPE_TLSX);
    if (data == NULL)
        return MEMORY_E;

    XMEMSET(data, 0, sizeof(SecureRenegotiation));

    ret = TLSX_Push(extensions, SECURE_RENEGOTIATION, data);
    if (ret != 0) {
        XFREE(data, 0, DYNAMIC_TYPE_TLSX);
        return ret;
    }

    return SSL_SUCCESS;
}


#define SCR_FREE_ALL(data) XFREE(data, NULL, DYNAMIC_TYPE_TLSX)
#define SCR_GET_SIZE       TLSX_SecureRenegotiation_GetSize
#define SCR_WRITE          TLSX_SecureRenegotiation_Write
#define SCR_PARSE          TLSX_SecureRenegotiation_Parse

#else

#define SCR_FREE_ALL(a)
#define SCR_GET_SIZE(a, b)    0
#define SCR_WRITE(a, b, c)    0
#define SCR_PARSE(a, b, c, d) 0

#endif /* HAVE_SECURE_RENEGOTIATION */

#ifdef HAVE_SESSION_TICKET

static void TLSX_SessionTicket_ValidateRequest(WOLFSSL* ssl)
{
    TLSX*          extension = TLSX_Find(ssl->extensions, SESSION_TICKET);
    SessionTicket* ticket    = extension ? extension->data : NULL;

    if (ticket) {
        /* TODO validate ticket timeout here! */
        if (ticket->lifetime == 0xfffffff) {
            /* send empty ticket on timeout */
            TLSX_UseSessionTicket(&ssl->extensions, NULL);
        }
    }
}


static word16 TLSX_SessionTicket_GetSize(SessionTicket* ticket, int isRequest)
{
    (void)isRequest;
    return ticket ? ticket->size : 0;
}

static word16 TLSX_SessionTicket_Write(SessionTicket* ticket, byte* output,
                                                                  int isRequest)
{
    word16 offset = 0; /* empty ticket */

    if (isRequest && ticket) {
        XMEMCPY(output + offset, ticket->data, ticket->size);
        offset += ticket->size;
    }

    return offset;
}


static int TLSX_SessionTicket_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                                                 byte isRequest)
{
    int ret = 0;

    if (!isRequest) {
        /* client side */
        if (length != 0)
            return BUFFER_ERROR;

        ssl->expect_session_ticket = 1;
    }
#ifndef NO_WOLFSSL_SERVER
    else {
        /* server side */
        if (ssl->ctx->ticketEncCb == NULL) {
            WOLFSSL_MSG("Client sent session ticket, server has no callback");
            return 0;
        }

        if (length == 0) {
            /* blank ticket */
            ret = TLSX_UseSessionTicket(&ssl->extensions, NULL);
            if (ret == SSL_SUCCESS) {
                ret = 0;
                TLSX_SetResponse(ssl, SESSION_TICKET);  /* send blank ticket */
                ssl->options.createTicket = 1;  /* will send ticket msg */
                ssl->options.useTicket    = 1;
            }
        } else {
            /* got actual ticket from client */
            ret = DoClientTicket(ssl, input, length);
            if (ret == WOLFSSL_TICKET_RET_OK) {    /* use ticket to resume */
                WOLFSSL_MSG("Using exisitng client ticket");
                ssl->options.useTicket = 1;
                ssl->options.resuming  = 1;
            } else if (ret == WOLFSSL_TICKET_RET_CREATE) {
                WOLFSSL_MSG("Using existing client ticket, creating new one");
                ret = TLSX_UseSessionTicket(&ssl->extensions, NULL);
                if (ret == SSL_SUCCESS) {
                    ret = 0;
                    TLSX_SetResponse(ssl, SESSION_TICKET);
                                                    /* send blank ticket */
                    ssl->options.createTicket = 1;  /* will send ticket msg */
                    ssl->options.useTicket    = 1;
                    ssl->options.resuming     = 1;
                }
            } else if (ret == WOLFSSL_TICKET_RET_REJECT) {
                WOLFSSL_MSG("Process client ticket rejected, not using");
                ret = 0;  /* not fatal */
            } else if (ret == WOLFSSL_TICKET_RET_FATAL || ret < 0) {
                WOLFSSL_MSG("Process client ticket fatal error, not using");
            }
        }
    }
#endif /* NO_WOLFSSL_SERVER */

    return ret;
}

WOLFSSL_LOCAL SessionTicket* TLSX_SessionTicket_Create(word32 lifetime,
                                                       byte* data, word16 size)
{
    SessionTicket* ticket = (SessionTicket*)XMALLOC(sizeof(SessionTicket),
                                                       NULL, DYNAMIC_TYPE_TLSX);
    if (ticket) {
        ticket->data = (byte*)XMALLOC(size, NULL, DYNAMIC_TYPE_TLSX);
        if (ticket->data == NULL) {
            XFREE(ticket, NULL, DYNAMIC_TYPE_TLSX);
            return NULL;
        }

        XMEMCPY(ticket->data, data, size);
        ticket->size     = size;
        ticket->lifetime = lifetime;
    }

    return ticket;
}
WOLFSSL_LOCAL void TLSX_SessionTicket_Free(SessionTicket* ticket)
{
    if (ticket) {
        XFREE(ticket->data, NULL, DYNAMIC_TYPE_TLSX);
        XFREE(ticket,       NULL, DYNAMIC_TYPE_TLSX);
    }
}

int TLSX_UseSessionTicket(TLSX** extensions, SessionTicket* ticket)
{
    int ret = 0;

    if (extensions == NULL)
        return BAD_FUNC_ARG;

    /* If the ticket is NULL, the client will request a new ticket from the
       server. Otherwise, the client will use it in the next client hello. */
    if ((ret = TLSX_Push(extensions, SESSION_TICKET, (void*)ticket)) != 0)
        return ret;

    return SSL_SUCCESS;
}

#define STK_VALIDATE_REQUEST TLSX_SessionTicket_ValidateRequest
#define STK_GET_SIZE         TLSX_SessionTicket_GetSize
#define STK_WRITE            TLSX_SessionTicket_Write
#define STK_PARSE            TLSX_SessionTicket_Parse

#else

#define STK_VALIDATE_REQUEST(a)
#define STK_GET_SIZE(a, b)      0
#define STK_WRITE(a, b, c)      0
#define STK_PARSE(a, b, c, d)   0

#endif /* HAVE_SESSION_TICKET */


TLSX* TLSX_Find(TLSX* list, TLSX_Type type)
{
    TLSX* extension = list;

    while (extension && extension->type != type)
        extension = extension->next;

    return extension;
}

void TLSX_FreeAll(TLSX* list)
{
    TLSX* extension;

    while ((extension = list)) {
        list = extension->next;

        switch (extension->type) {
            case SERVER_NAME_INDICATION:
                SNI_FREE_ALL((SNI*)extension->data);
                break;

            case MAX_FRAGMENT_LENGTH:
                MFL_FREE_ALL(extension->data);
                break;

            case TRUNCATED_HMAC:
                /* Nothing to do. */
                break;

            case ELLIPTIC_CURVES:
                EC_FREE_ALL(extension->data);
                break;

            case SECURE_RENEGOTIATION:
                SCR_FREE_ALL(extension->data);
                break;

            case SESSION_TICKET:
                /* Nothing to do. */
                break;
        }

        XFREE(extension, 0, DYNAMIC_TYPE_TLSX);
    }
}

int TLSX_SupportExtensions(WOLFSSL* ssl) {
    return ssl && (IsTLS(ssl) || ssl->version.major == DTLS_MAJOR);
}

static word16 TLSX_GetSize(TLSX* list, byte* semaphore, byte isRequest)
{
    TLSX* extension;
    word16 length = 0;

    while ((extension = list)) {
        list = extension->next;

        if (!isRequest && !extension->resp)
            continue; /* skip! */

        if (!IS_OFF(semaphore, TLSX_ToSemaphore(extension->type)))
            continue; /* skip! */

        /* type + data length */
        length += HELLO_EXT_TYPE_SZ + OPAQUE16_LEN;

        switch (extension->type) {
            case SERVER_NAME_INDICATION:
                if (isRequest)
                    length += SNI_GET_SIZE(extension->data);
                break;
            case MAX_FRAGMENT_LENGTH:
                length += MFL_GET_SIZE(extension->data);
                break;

            case TRUNCATED_HMAC:
                /* empty extension. */
                break;

            case ELLIPTIC_CURVES:
                length += EC_GET_SIZE(extension->data);
                break;

            case SECURE_RENEGOTIATION:
                length += SCR_GET_SIZE(extension->data, isRequest);
                break;

            case SESSION_TICKET:
                length += STK_GET_SIZE(extension->data, isRequest);
                break;
        }

        TURN_ON(semaphore, TLSX_ToSemaphore(extension->type));
    }

    return length;
}

static word16 TLSX_Write(TLSX* list, byte* output, byte* semaphore,
                                                                 byte isRequest)
{
    TLSX* extension;
    word16 offset = 0;
    word16 length_offset = 0;

    while ((extension = list)) {
        list = extension->next;

        if (!isRequest && !extension->resp)
            continue; /* skip! */

        if (!IS_OFF(semaphore, TLSX_ToSemaphore(extension->type)))
            continue; /* skip! */

        /* extension type */
        c16toa(extension->type, output + offset);
        offset += HELLO_EXT_TYPE_SZ + OPAQUE16_LEN;
        length_offset = offset;

        /* extension data should be written internally */
        switch (extension->type) {
            case SERVER_NAME_INDICATION:
                if (isRequest)
                    offset += SNI_WRITE(extension->data, output + offset);
                break;

            case MAX_FRAGMENT_LENGTH:
                offset += MFL_WRITE(extension->data, output + offset);
                break;

            case TRUNCATED_HMAC:
                /* empty extension. */
                break;

            case ELLIPTIC_CURVES:
                offset += EC_WRITE(extension->data, output + offset);
                break;

            case SECURE_RENEGOTIATION:
                offset += SCR_WRITE(extension->data, output + offset,
                                                                     isRequest);
                break;

            case SESSION_TICKET:
                offset += STK_WRITE(extension->data, output + offset,
                                                                     isRequest);
                break;
        }

        /* writing extension data length */
        c16toa(offset - length_offset, output + length_offset - OPAQUE16_LEN);

        TURN_ON(semaphore, TLSX_ToSemaphore(extension->type));
    }

    return offset;
}

#ifndef NO_WOLFSSL_CLIENT

word16 TLSX_GetRequestSize(WOLFSSL* ssl)
{
    word16 length = 0;

    if (TLSX_SupportExtensions(ssl)) {
        byte semaphore[SEMAPHORE_SIZE] = {0};

        EC_VALIDATE_REQUEST(ssl, semaphore);
        STK_VALIDATE_REQUEST(ssl);

        if (ssl->extensions)
            length += TLSX_GetSize(ssl->extensions, semaphore, 1);

        if (ssl->ctx && ssl->ctx->extensions)
            length += TLSX_GetSize(ssl->ctx->extensions, semaphore, 1);

        if (IsAtLeastTLSv1_2(ssl) && ssl->suites->hashSigAlgoSz)
            length += ssl->suites->hashSigAlgoSz + HELLO_EXT_LEN;
    }

    if (length)
        length += OPAQUE16_LEN; /* for total length storage */

    return length;
}

word16 TLSX_WriteRequest(WOLFSSL* ssl, byte* output)
{
    word16 offset = 0;

    if (TLSX_SupportExtensions(ssl) && output) {
        byte semaphore[SEMAPHORE_SIZE] = {0};

        offset += OPAQUE16_LEN; /* extensions length */

        EC_VALIDATE_REQUEST(ssl, semaphore);

        if (ssl->extensions)
            offset += TLSX_Write(ssl->extensions, output + offset,
                                                                  semaphore, 1);

        if (ssl->ctx && ssl->ctx->extensions)
            offset += TLSX_Write(ssl->ctx->extensions, output + offset,
                                                                  semaphore, 1);

        if (IsAtLeastTLSv1_2(ssl) && ssl->suites->hashSigAlgoSz)
        {
            int i;
            /* extension type */
            c16toa(HELLO_EXT_SIG_ALGO, output + offset);
            offset += HELLO_EXT_TYPE_SZ;

            /* extension data length */
            c16toa(OPAQUE16_LEN + ssl->suites->hashSigAlgoSz, output + offset);
            offset += OPAQUE16_LEN;

            /* sig algos length */
            c16toa(ssl->suites->hashSigAlgoSz, output + offset);
            offset += OPAQUE16_LEN;

            /* sig algos */
            for (i = 0; i < ssl->suites->hashSigAlgoSz; i++, offset++)
                output[offset] = ssl->suites->hashSigAlgo[i];
        }

        if (offset > OPAQUE16_LEN)
            c16toa(offset - OPAQUE16_LEN, output); /* extensions length */
    }

    return offset;
}

#endif /* NO_WOLFSSL_CLIENT */

#ifndef NO_WOLFSSL_SERVER

word16 TLSX_GetResponseSize(WOLFSSL* ssl)
{
    word16 length = 0;
    byte semaphore[SEMAPHORE_SIZE] = {0};

    if (TLSX_SupportExtensions(ssl))
        length += TLSX_GetSize(ssl->extensions, semaphore, 0);

    /* All the response data is set at the ssl object only, so no ctx here. */

    if (length)
        length += OPAQUE16_LEN; /* for total length storage */

    return length;
}

word16 TLSX_WriteResponse(WOLFSSL *ssl, byte* output)
{
    word16 offset = 0;

    if (TLSX_SupportExtensions(ssl) && output) {
        byte semaphore[SEMAPHORE_SIZE] = {0};

        offset += OPAQUE16_LEN; /* extensions length */

        offset += TLSX_Write(ssl->extensions, output + offset, semaphore, 0);

        if (offset > OPAQUE16_LEN)
            c16toa(offset - OPAQUE16_LEN, output); /* extensions length */
    }

    return offset;
}

#endif /* NO_WOLFSSL_SERVER */

int TLSX_Parse(WOLFSSL* ssl, byte* input, word16 length, byte isRequest,
                                                                 Suites *suites)
{
    int ret = 0;
    word16 offset = 0;

    if (!ssl || !input || (isRequest && !suites))
        return BAD_FUNC_ARG;

    while (ret == 0 && offset < length) {
        word16 type;
        word16 size;

        if (length - offset < HELLO_EXT_TYPE_SZ + OPAQUE16_LEN)
            return BUFFER_ERROR;

        ato16(input + offset, &type);
        offset += HELLO_EXT_TYPE_SZ;

        ato16(input + offset, &size);
        offset += OPAQUE16_LEN;

        if (offset + size > length)
            return BUFFER_ERROR;

        switch (type) {
            case SERVER_NAME_INDICATION:
                WOLFSSL_MSG("SNI extension received");

                ret = SNI_PARSE(ssl, input + offset, size, isRequest);
                break;

            case MAX_FRAGMENT_LENGTH:
                WOLFSSL_MSG("Max Fragment Length extension received");

                ret = MFL_PARSE(ssl, input + offset, size, isRequest);
                break;

            case TRUNCATED_HMAC:
                WOLFSSL_MSG("Truncated HMAC extension received");

                ret = THM_PARSE(ssl, input + offset, size, isRequest);
                break;

            case ELLIPTIC_CURVES:
                WOLFSSL_MSG("Elliptic Curves extension received");

                ret = EC_PARSE(ssl, input + offset, size, isRequest);
                break;

            case SECURE_RENEGOTIATION:
                WOLFSSL_MSG("Secure Renegotiation extension received");

                ret = SCR_PARSE(ssl, input + offset, size, isRequest);
                break;

            case SESSION_TICKET:
                WOLFSSL_MSG("Session Ticket extension received");

                ret = STK_PARSE(ssl, input + offset, size, isRequest);
                break;

            case HELLO_EXT_SIG_ALGO:
                if (isRequest) {
                    /* do not mess with offset inside the switch! */
                    if (IsAtLeastTLSv1_2(ssl)) {
                        ato16(input + offset, &suites->hashSigAlgoSz);

                        if (suites->hashSigAlgoSz > size - OPAQUE16_LEN)
                            return BUFFER_ERROR;

                        XMEMCPY(suites->hashSigAlgo,
                                input + offset + OPAQUE16_LEN,
                                min(suites->hashSigAlgoSz,
                                                        HELLO_EXT_SIGALGO_MAX));
                    }
                } else {
                    WOLFSSL_MSG("Servers MUST NOT send SIG ALGO extension.");
                }

                break;
        }

        /* offset should be updated here! */
        offset += size;
    }

    return ret;
}

/* undefining semaphore macros */
#undef IS_OFF
#undef TURN_ON
#undef SEMAPHORE_SIZE

#endif


#ifndef NO_WOLFSSL_CLIENT

#ifndef NO_OLD_TLS

    WOLFSSL_METHOD* wolfTLSv1_client_method(void)
    {
        WOLFSSL_METHOD* method =
                             (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD), 0,
                                                      DYNAMIC_TYPE_METHOD);
        if (method)
            InitSSL_Method(method, MakeTLSv1());
        return method;
    }


    WOLFSSL_METHOD* wolfTLSv1_1_client_method(void)
    {
        WOLFSSL_METHOD* method =
                              (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
        if (method)
            InitSSL_Method(method, MakeTLSv1_1());
        return method;
    }

#endif /* !NO_OLD_TLS */

#ifndef NO_SHA256   /* can't use without SHA256 */

    WOLFSSL_METHOD* wolfTLSv1_2_client_method(void)
    {
        WOLFSSL_METHOD* method =
                              (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
        if (method)
            InitSSL_Method(method, MakeTLSv1_2());
        return method;
    }

#endif


    WOLFSSL_METHOD* wolfSSLv23_client_method(void)
    {
        WOLFSSL_METHOD* method =
                              (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
        if (method) {
#ifndef NO_SHA256         /* 1.2 requires SHA256 */
            InitSSL_Method(method, MakeTLSv1_2());
#else
            InitSSL_Method(method, MakeTLSv1_1());
#endif
#ifndef NO_OLD_TLS
            method->downgrade = 1;
#endif
        }
        return method;
    }


#endif /* NO_WOLFSSL_CLIENT */



#ifndef NO_WOLFSSL_SERVER

#ifndef NO_OLD_TLS

    WOLFSSL_METHOD* wolfTLSv1_server_method(void)
    {
        WOLFSSL_METHOD* method =
                              (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
        if (method) {
            InitSSL_Method(method, MakeTLSv1());
            method->side = WOLFSSL_SERVER_END;
        }
        return method;
    }


    WOLFSSL_METHOD* wolfTLSv1_1_server_method(void)
    {
        WOLFSSL_METHOD* method =
                              (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
        if (method) {
            InitSSL_Method(method, MakeTLSv1_1());
            method->side = WOLFSSL_SERVER_END;
        }
        return method;
    }

#endif /* !NO_OLD_TLS */

#ifndef NO_SHA256   /* can't use without SHA256 */

    WOLFSSL_METHOD* wolfTLSv1_2_server_method(void)
    {
        WOLFSSL_METHOD* method =
                              (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
        if (method) {
            InitSSL_Method(method, MakeTLSv1_2());
            method->side = WOLFSSL_SERVER_END;
        }
        return method;
    }

#endif


    WOLFSSL_METHOD* wolfSSLv23_server_method(void)
    {
        WOLFSSL_METHOD* method =
                              (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
        if (method) {
#ifndef NO_SHA256         /* 1.2 requires SHA256 */
            InitSSL_Method(method, MakeTLSv1_2());
#else
            InitSSL_Method(method, MakeTLSv1_1());
#endif
            method->side      = WOLFSSL_SERVER_END;
#ifndef NO_OLD_TLS
            method->downgrade = 1;
#endif /* !NO_OLD_TLS */
        }
        return method;
    }



#endif /* NO_WOLFSSL_SERVER */
#endif /* NO_TLS */

