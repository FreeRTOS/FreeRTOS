/* tls.c
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

#ifndef WOLFCRYPT_ONLY

#include <wolfssl/ssl.h>
#include <wolfssl/internal.h>
#include <wolfssl/error-ssl.h>
#include <wolfssl/wolfcrypt/hmac.h>
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

#ifdef HAVE_CURVE25519
    #include <wolfssl/wolfcrypt/curve25519.h>
#endif
#ifdef HAVE_CURVE448
    #include <wolfssl/wolfcrypt/curve448.h>
#endif
#ifdef HAVE_NTRU
    #include "libntruencrypt/ntru_crypto.h"
    #include <wolfssl/wolfcrypt/random.h>
#endif

#ifdef HAVE_QSH
    static int TLSX_AddQSHKey(QSHKey** list, QSHKey* key);
    static byte* TLSX_QSHKeyFind_Pub(QSHKey* qsh, word16* pubLen, word16 name);
#if defined(HAVE_NTRU)
    static int TLSX_CreateNtruKey(WOLFSSL* ssl, int type);
#endif
#endif /* HAVE_QSH */

#if (!defined(NO_WOLFSSL_SERVER) && defined(WOLFSSL_TLS13) && \
        !defined(WOLFSSL_NO_SERVER_GROUPS_EXT)) || \
    (defined(WOLFSSL_TLS13) && defined(HAVE_SUPPORTED_CURVES))
static int TLSX_KeyShare_IsSupported(int namedGroup);
#endif

#if ((!defined(NO_WOLFSSL_SERVER) && defined(WOLFSSL_TLS13) && \
        !defined(WOLFSSL_NO_SERVER_GROUPS_EXT)) || \
    (defined(WOLFSSL_TLS13) && !defined(HAVE_ECC) && !defined(HAVE_CURVE25519) \
        && !defined(HAVE_CURVE448) && defined(HAVE_SUPPORTED_CURVES)) || \
    ((defined(HAVE_ECC) || defined(HAVE_CURVE25519) || \
        defined(HAVE_CURVE448)) && defined(HAVE_SUPPORTED_CURVES))) && \
     defined(HAVE_TLS_EXTENSIONS)
static int TLSX_PopulateSupportedGroups(WOLFSSL* ssl, TLSX** extensions);
#endif


#ifndef NO_TLS

/* Digest enable checks */
#ifdef NO_OLD_TLS /* TLS 1.2 only */
    #if defined(NO_SHA256) && !defined(WOLFSSL_SHA384) && \
            !defined(WOLFSSL_SHA512)
        #error Must have SHA256, SHA384 or SHA512 enabled for TLS 1.2
    #endif
#else  /* TLS 1.1 or older */
    #if defined(NO_MD5) && defined(NO_SHA)
        #error Must have SHA1 and MD5 enabled for old TLS
    #endif
#endif

#ifdef WOLFSSL_TLS13
    #if !defined(NO_DH) && \
        !defined(HAVE_FFDHE_2048) && !defined(HAVE_FFDHE_3072) && \
        !defined(HAVE_FFDHE_4096) && !defined(HAVE_FFDHE_6144) && \
        !defined(HAVE_FFDHE_8192)
        #error Please configure your TLS 1.3 DH key size using either: HAVE_FFDHE_2048, HAVE_FFDHE_3072, HAVE_FFDHE_4096, HAVE_FFDHE_6144 or HAVE_FFDHE_8192
    #endif
    #if !defined(NO_RSA) && !defined(WC_RSA_PSS)
        #error The build option WC_RSA_PSS is required for TLS 1.3 with RSA
    #endif
    #ifndef HAVE_TLS_EXTENSIONS
        #ifndef _MSC_VER
            #error "The build option HAVE_TLS_EXTENSIONS is required for TLS 1.3"
        #else
            #pragma message("Error: The build option HAVE_TLS_EXTENSIONS is required for TLS 1.3")
        #endif
    #endif
#endif

/* Warn if secrets logging is enabled */
#if defined(SHOW_SECRETS) || defined(WOLFSSL_SSLKEYLOGFILE)
    #ifndef _MSC_VER
        #warning The SHOW_SECRETS and WOLFSSL_SSLKEYLOGFILE options should only be used for debugging and never in a production environment
    #else
        #pragma message("Warning: The SHOW_SECRETS and WOLFSSL_SSLKEYLOGFILE options should only be used for debugging and never in a production environment")
    #endif
#endif

/* Optional Pre-Master-Secret logging for Wireshark */
#if !defined(NO_FILESYSTEM) && defined(WOLFSSL_SSLKEYLOGFILE)
#ifndef WOLFSSL_SSLKEYLOGFILE_OUTPUT
    #define WOLFSSL_SSLKEYLOGFILE_OUTPUT "sslkeylog.log"
#endif
#endif

#ifndef WOLFSSL_NO_TLS12

#ifdef WOLFSSL_SHA384
    #define HSHASH_SZ WC_SHA384_DIGEST_SIZE
#else
    #define HSHASH_SZ FINISHED_SZ
#endif

#ifdef WOLFSSL_RENESAS_TSIP_TLS
    
    #if (WOLFSSL_RENESAS_TSIP_VER >=109)

    int tsip_generateMasterSecretEx(
            byte        cipherSuiteFirst,
            byte        cipherSuite,
            const byte* pr,                 /* pre-master    */
            const byte* cr,                 /* client random */
            const byte* sr,                 /* server random */
            byte*       ms);

    #elif (WOLFSSL_RENESAS_TSIP_VER >=106)
    
    int tsip_generateMasterSecret(
            const byte* pre,
            const byte* cr,
            const byte* sr,
            byte*       ms);
    
    #endif     

    int tsip_useable(const WOLFSSL *ssl);
    int tsip_generateSeesionKey(WOLFSSL *ssl);
    int tsip_generateVerifyData(
            const byte* ms,
            const byte* side,
            const byte* handshake_hash,
            byte*       hashes);

#endif /*WOLFSSL_RENESAS_TSIP_TLS*/

int BuildTlsHandshakeHash(WOLFSSL* ssl, byte* hash, word32* hashLen)
{
    int ret = 0;
    word32 hashSz = FINISHED_SZ;

    if (ssl == NULL || hash == NULL || hashLen == NULL || *hashLen < HSHASH_SZ)
        return BAD_FUNC_ARG;

    /* for constant timing perform these even if error */
#ifndef NO_OLD_TLS
    ret |= wc_Md5GetHash(&ssl->hsHashes->hashMd5, hash);
    ret |= wc_ShaGetHash(&ssl->hsHashes->hashSha, &hash[WC_MD5_DIGEST_SIZE]);
#endif

    if (IsAtLeastTLSv1_2(ssl)) {
#ifndef NO_SHA256
        if (ssl->specs.mac_algorithm <= sha256_mac ||
            ssl->specs.mac_algorithm == blake2b_mac) {
            ret |= wc_Sha256GetHash(&ssl->hsHashes->hashSha256, hash);
            hashSz = WC_SHA256_DIGEST_SIZE;
        }
#endif
#ifdef WOLFSSL_SHA384
        if (ssl->specs.mac_algorithm == sha384_mac) {
            ret |= wc_Sha384GetHash(&ssl->hsHashes->hashSha384, hash);
            hashSz = WC_SHA384_DIGEST_SIZE;
        }
#endif
    }

    *hashLen = hashSz;

    if (ret != 0)
        ret = BUILD_MSG_ERROR;

    return ret;
}


int BuildTlsFinished(WOLFSSL* ssl, Hashes* hashes, const byte* sender)
{
    int ret;
    const byte* side;
    word32 hashSz = HSHASH_SZ;
#if defined(WOLFSSL_ASYNC_CRYPT) && !defined(WC_ASYNC_NO_HASH)
    DECLARE_VAR(handshake_hash, byte, HSHASH_SZ, ssl->heap);
    if (handshake_hash == NULL)
        return MEMORY_E;
#else
    byte handshake_hash[HSHASH_SZ];
#endif

    ret = BuildTlsHandshakeHash(ssl, handshake_hash, &hashSz);
    if (ret == 0) {
        if (XSTRNCMP((const char*)sender, (const char*)client, SIZEOF_SENDER) == 0)
            side = tls_client;
        else
            side = tls_server;

#ifdef WOLFSSL_HAVE_PRF
#if defined(WOLFSSL_RENESAS_TSIP_TLS) && \
    !defined(NO_WOLFSSL_RENESAS_TSIP_TLS_SESSION)
        if (tsip_useable(ssl)) {
            ret = tsip_generateVerifyData(ssl->arrays->tsip_masterSecret,
                            side, handshake_hash, (byte*)hashes /* out */);
        } else
#endif
        ret = wc_PRF_TLS((byte*)hashes, TLS_FINISHED_SZ, ssl->arrays->masterSecret,
                   SECRET_LEN, side, FINISHED_LABEL_SZ, handshake_hash, hashSz,
                   IsAtLeastTLSv1_2(ssl), ssl->specs.mac_algorithm,
                   ssl->heap, ssl->devId);
#else
        /* Pseudo random function must be enabled in the configuration. */
        ret = PRF_MISSING;
        WOLFSSL_MSG("Pseudo-random function is not enabled");

        (void)side;
        (void)hashes;
#endif
    }

#if defined(WOLFSSL_ASYNC_CRYPT) && !defined(WC_ASYNC_NO_HASH)
    FREE_VAR(handshake_hash, ssl->heap);
#endif

    return ret;
}

#endif /* !WOLFSSL_NO_TLS12 */

#ifndef NO_OLD_TLS

#ifdef WOLFSSL_ALLOW_TLSV10
ProtocolVersion MakeTLSv1(void)
{
    ProtocolVersion pv;
    pv.major = SSLv3_MAJOR;
    pv.minor = TLSv1_MINOR;

    return pv;
}
#endif /* WOLFSSL_ALLOW_TLSV10 */


ProtocolVersion MakeTLSv1_1(void)
{
    ProtocolVersion pv;
    pv.major = SSLv3_MAJOR;
    pv.minor = TLSv1_1_MINOR;

    return pv;
}

#endif /* !NO_OLD_TLS */


#ifndef WOLFSSL_NO_TLS12

ProtocolVersion MakeTLSv1_2(void)
{
    ProtocolVersion pv;
    pv.major = SSLv3_MAJOR;
    pv.minor = TLSv1_2_MINOR;

    return pv;
}

#endif /* !WOLFSSL_NO_TLS12 */

#ifdef WOLFSSL_TLS13
/* The TLS v1.3 protocol version.
 *
 * returns the protocol version data for TLS v1.3.
 */
ProtocolVersion MakeTLSv1_3(void)
{
    ProtocolVersion pv;
    pv.major = SSLv3_MAJOR;
    pv.minor = TLSv1_3_MINOR;

    return pv;
}
#endif

#ifndef WOLFSSL_NO_TLS12

#ifdef HAVE_EXTENDED_MASTER
static const byte ext_master_label[EXT_MASTER_LABEL_SZ + 1] =
                                                      "extended master secret";
#endif
static const byte master_label[MASTER_LABEL_SZ + 1] = "master secret";
static const byte key_label   [KEY_LABEL_SZ + 1]    = "key expansion";

static int _DeriveTlsKeys(byte* key_dig, word32 key_dig_len,
                         const byte* ms, word32 msLen,
                         const byte* sr, const byte* cr,
                         int tls1_2, int hash_type,
                         void* heap, int devId)
{
    int ret;
#if defined(WOLFSSL_ASYNC_CRYPT) && !defined(WC_ASYNC_NO_HASH)
    DECLARE_VAR(seed, byte, SEED_LEN, heap);
    if (seed == NULL)
        return MEMORY_E;
#else
    byte seed[SEED_LEN];
#endif

    XMEMCPY(seed,           sr, RAN_LEN);
    XMEMCPY(seed + RAN_LEN, cr, RAN_LEN);

#ifdef WOLFSSL_HAVE_PRF
    ret = wc_PRF_TLS(key_dig, key_dig_len, ms, msLen, key_label, KEY_LABEL_SZ,
               seed, SEED_LEN, tls1_2, hash_type, heap, devId);
#else
    /* Pseudo random function must be enabled in the configuration. */
    ret = PRF_MISSING;
    WOLFSSL_MSG("Pseudo-random function is not enabled");

    (void)key_dig;
    (void)key_dig_len;
    (void)ms;
    (void)msLen;
    (void)tls1_2;
    (void)hash_type;
    (void)heap;
    (void)devId;
    (void)key_label;
    (void)master_label;
#ifdef HAVE_EXTENDED_MASTER
    (void)ext_master_label;
#endif
#endif

#if defined(WOLFSSL_ASYNC_CRYPT) && !defined(WC_ASYNC_NO_HASH)
    FREE_VAR(seed, heap);
#endif

    return ret;
}

/* External facing wrapper so user can call as well, 0 on success */
int wolfSSL_DeriveTlsKeys(byte* key_dig, word32 key_dig_len,
                         const byte* ms, word32 msLen,
                         const byte* sr, const byte* cr,
                         int tls1_2, int hash_type)
{
    return _DeriveTlsKeys(key_dig, key_dig_len, ms, msLen, sr, cr, tls1_2,
        hash_type, NULL, INVALID_DEVID);
}


int DeriveTlsKeys(WOLFSSL* ssl)
{
    int   ret;
    int   key_dig_len = 2 * ssl->specs.hash_size +
                        2 * ssl->specs.key_size  +
                        2 * ssl->specs.iv_size;
#ifdef WOLFSSL_SMALL_STACK
    byte* key_dig;
#else
    byte  key_dig[MAX_PRF_DIG];
#endif

#ifdef WOLFSSL_SMALL_STACK
    key_dig = (byte*)XMALLOC(MAX_PRF_DIG, ssl->heap, DYNAMIC_TYPE_DIGEST);
    if (key_dig == NULL) {
        return MEMORY_E;
    }
#endif
#if defined(WOLFSSL_RENESAS_TSIP_TLS) && \
    !defined(NO_WOLFSSL_RENESAS_TSIP_TLS_SESSION)
    if (tsip_useable(ssl))
        ret = tsip_generateSeesionKey(ssl);
    else {
#endif
    ret = _DeriveTlsKeys(key_dig, key_dig_len,
                         ssl->arrays->masterSecret, SECRET_LEN,
                         ssl->arrays->serverRandom, ssl->arrays->clientRandom,
                         IsAtLeastTLSv1_2(ssl), ssl->specs.mac_algorithm,
                         ssl->heap, ssl->devId);
    if (ret == 0)
        ret = StoreKeys(ssl, key_dig, PROVISION_CLIENT_SERVER);
#if defined(WOLFSSL_RENESAS_TSIP_TLS) && \
    !defined(NO_WOLFSSL_RENESAS_TSIP_TLS_SESSION)
    }
#endif

#ifdef WOLFSSL_SMALL_STACK
    XFREE(key_dig, ssl->heap, DYNAMIC_TYPE_DIGEST);
#endif

    return ret;
}

static int _MakeTlsMasterSecret(byte* ms, word32 msLen,
                               const byte* pms, word32 pmsLen,
                               const byte* cr, const byte* sr,
                               int tls1_2, int hash_type,
                               void* heap, int devId)
{
    int ret;
#if defined(WOLFSSL_ASYNC_CRYPT) && !defined(WC_ASYNC_NO_HASH)
    DECLARE_VAR(seed, byte, SEED_LEN, heap);
    if (seed == NULL)
        return MEMORY_E;
#else
    byte seed[SEED_LEN];
#endif

    XMEMCPY(seed,           cr, RAN_LEN);
    XMEMCPY(seed + RAN_LEN, sr, RAN_LEN);

#ifdef WOLFSSL_HAVE_PRF
    ret = wc_PRF_TLS(ms, msLen, pms, pmsLen, master_label, MASTER_LABEL_SZ,
               seed, SEED_LEN, tls1_2, hash_type, heap, devId);
#else
    /* Pseudo random function must be enabled in the configuration. */
    ret = PRF_MISSING;
    WOLFSSL_MSG("Pseudo-random function is not enabled");

    (void)ms;
    (void)msLen;
    (void)pms;
    (void)pmsLen;
    (void)tls1_2;
    (void)hash_type;
    (void)heap;
    (void)devId;
#endif

#if defined(WOLFSSL_ASYNC_CRYPT) && !defined(WC_ASYNC_NO_HASH)
    FREE_VAR(seed, heap);
#endif

    return ret;
}

/* External facing wrapper so user can call as well, 0 on success */
int wolfSSL_MakeTlsMasterSecret(byte* ms, word32 msLen,
                               const byte* pms, word32 pmsLen,
                               const byte* cr, const byte* sr,
                               int tls1_2, int hash_type)
{
    return _MakeTlsMasterSecret(ms, msLen, pms, pmsLen, cr, sr, tls1_2,
        hash_type, NULL, INVALID_DEVID);
}


#ifdef HAVE_EXTENDED_MASTER

static int _MakeTlsExtendedMasterSecret(byte* ms, word32 msLen,
                                        const byte* pms, word32 pmsLen,
                                        const byte* sHash, word32 sHashLen,
                                        int tls1_2, int hash_type,
                                        void* heap, int devId)
{
    int ret;

#ifdef WOLFSSL_HAVE_PRF
    ret = wc_PRF_TLS(ms, msLen, pms, pmsLen, ext_master_label, EXT_MASTER_LABEL_SZ,
               sHash, sHashLen, tls1_2, hash_type, heap, devId);
#else
    /* Pseudo random function must be enabled in the configuration. */
    ret = PRF_MISSING;
    WOLFSSL_MSG("Pseudo-random function is not enabled");

    (void)ms;
    (void)msLen;
    (void)pms;
    (void)pmsLen;
    (void)sHash;
    (void)sHashLen;
    (void)tls1_2;
    (void)hash_type;
    (void)heap;
    (void)devId;
#endif
    return ret;
}

/* External facing wrapper so user can call as well, 0 on success */
int wolfSSL_MakeTlsExtendedMasterSecret(byte* ms, word32 msLen,
                                        const byte* pms, word32 pmsLen,
                                        const byte* sHash, word32 sHashLen,
                                        int tls1_2, int hash_type)
{
    return _MakeTlsExtendedMasterSecret(ms, msLen, pms, pmsLen, sHash, sHashLen,
        tls1_2, hash_type, NULL, INVALID_DEVID);
}

#endif /* HAVE_EXTENDED_MASTER */


int MakeTlsMasterSecret(WOLFSSL* ssl)
{
    int ret;

#ifdef HAVE_EXTENDED_MASTER
    if (ssl->options.haveEMS) {
        word32 hashSz = HSHASH_SZ;
    #ifdef WOLFSSL_SMALL_STACK
        byte* handshake_hash = (byte*)XMALLOC(HSHASH_SZ, ssl->heap,
                                              DYNAMIC_TYPE_DIGEST);
        if (handshake_hash == NULL)
            return MEMORY_E;
    #else
        byte handshake_hash[HSHASH_SZ];
    #endif

        ret = BuildTlsHandshakeHash(ssl, handshake_hash, &hashSz);
        if (ret == 0) {
            ret = _MakeTlsExtendedMasterSecret(
                ssl->arrays->masterSecret, SECRET_LEN,
                ssl->arrays->preMasterSecret, ssl->arrays->preMasterSz,
                handshake_hash, hashSz,
                IsAtLeastTLSv1_2(ssl), ssl->specs.mac_algorithm,
                ssl->heap, ssl->devId);
        }

    #ifdef WOLFSSL_SMALL_STACK
        XFREE(handshake_hash, ssl->heap, DYNAMIC_TYPE_DIGEST);
    #endif
    }
    else
#endif /* HAVE_EXTENDED_MASTER */
    {
#if defined(WOLFSSL_RENESAS_TSIP_TLS) && \
    !defined(NO_WOLFSSL_RENESAS_TSIP_TLS_SESSION)
        if (tsip_useable(ssl)) {
            
            #if (WOLFSSL_RENESAS_TSIP_VER>=109)

            ret = tsip_generateMasterSecretEx(
                            ssl->options.cipherSuite0,
                            ssl->options.cipherSuite,                
                            &ssl->arrays->preMasterSecret[VERSION_SZ],
                            ssl->arrays->clientRandom,
                            ssl->arrays->serverRandom,
                            ssl->arrays->tsip_masterSecret);
            
            #elif (WOLFSSL_RENESAS_TSIP_VER>=106)

            ret = tsip_generateMasterSecret(
                            &ssl->arrays->preMasterSecret[VERSION_SZ],
                            ssl->arrays->clientRandom,
                            ssl->arrays->serverRandom,
                            ssl->arrays->tsip_masterSecret);
            
            #endif
        } else
#endif
        ret = _MakeTlsMasterSecret(ssl->arrays->masterSecret, SECRET_LEN,
              ssl->arrays->preMasterSecret, ssl->arrays->preMasterSz,
              ssl->arrays->clientRandom, ssl->arrays->serverRandom,
              IsAtLeastTLSv1_2(ssl), ssl->specs.mac_algorithm,
              ssl->heap, ssl->devId);
    }
    if (ret == 0) {
    #ifdef SHOW_SECRETS
        /* Wireshark Pre-Master-Secret Format:
         *  CLIENT_RANDOM <clientrandom> <mastersecret>
         */
        const char* CLIENT_RANDOM_LABEL = "CLIENT_RANDOM";
        int i, pmsPos = 0;
        char pmsBuf[13 + 1 + 64 + 1 + 96 + 1 + 1];

        XSNPRINTF(&pmsBuf[pmsPos], sizeof(pmsBuf) - pmsPos, "%s ",
            CLIENT_RANDOM_LABEL);
        pmsPos += XSTRLEN(CLIENT_RANDOM_LABEL) + 1;
        for (i = 0; i < RAN_LEN; i++) {
            XSNPRINTF(&pmsBuf[pmsPos], sizeof(pmsBuf) - pmsPos, "%02x",
                ssl->arrays->clientRandom[i]);
            pmsPos += 2;
        }
        XSNPRINTF(&pmsBuf[pmsPos], sizeof(pmsBuf) - pmsPos, " ");
        pmsPos += 1;
        for (i = 0; i < SECRET_LEN; i++) {
            XSNPRINTF(&pmsBuf[pmsPos], sizeof(pmsBuf) - pmsPos, "%02x",
                ssl->arrays->masterSecret[i]);
            pmsPos += 2;
        }
        XSNPRINTF(&pmsBuf[pmsPos], sizeof(pmsBuf) - pmsPos, "\n");
        pmsPos += 1;

        /* print master secret */
        puts(pmsBuf);

        #if !defined(NO_FILESYSTEM) && defined(WOLFSSL_SSLKEYLOGFILE)
        {
            FILE* f = XFOPEN(WOLFSSL_SSLKEYLOGFILE_OUTPUT, "a");
            if (f != XBADFILE) {
                XFWRITE(pmsBuf, 1, pmsPos, f);
                XFCLOSE(f);
            }
        }
        #endif
    #endif /* SHOW_SECRETS */

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
    seed = (byte*)XMALLOC(SEED_LEN, ssl->heap, DYNAMIC_TYPE_SEED);
    if (seed == NULL)
        return MEMORY_E;
#endif

    /*
     * As per RFC-5281, the order of the client and server randoms is reversed
     * from that used by the TLS protocol to derive keys.
     */
    XMEMCPY(seed,           ssl->arrays->clientRandom, RAN_LEN);
    XMEMCPY(seed + RAN_LEN, ssl->arrays->serverRandom, RAN_LEN);

#ifdef WOLFSSL_HAVE_PRF
    ret = wc_PRF_TLS((byte*)msk, len, ssl->arrays->masterSecret, SECRET_LEN,
              (const byte *)label, (word32)XSTRLEN(label), seed, SEED_LEN,
              IsAtLeastTLSv1_2(ssl), ssl->specs.mac_algorithm,
              ssl->heap, ssl->devId);
#else
    /* Pseudo random function must be enabled in the configuration. */
    ret = PRF_MISSING;
    WOLFSSL_MSG("Pseudo-random function is not enabled");

    (void)msk;
    (void)len;
    (void)label;
#endif

#ifdef WOLFSSL_SMALL_STACK
    XFREE(seed, ssl->heap, DYNAMIC_TYPE_SEED);
#endif

    return ret;
}


/* return HMAC digest type in wolfSSL format */
int wolfSSL_GetHmacType(WOLFSSL* ssl)
{
    if (ssl == NULL)
        return BAD_FUNC_ARG;

    switch (ssl->specs.mac_algorithm) {
        #ifndef NO_MD5
        case md5_mac:
        {
            return WC_MD5;
        }
        #endif
        #ifndef NO_SHA256
        case sha256_mac:
        {
            return WC_SHA256;
        }
        #endif
        #ifdef WOLFSSL_SHA384
        case sha384_mac:
        {
            return WC_SHA384;
        }

        #endif
        #ifndef NO_SHA
        case sha_mac:
        {
            return WC_SHA;
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
            return WOLFSSL_FATAL_ERROR;
        }
    }
}


int wolfSSL_SetTlsHmacInner(WOLFSSL* ssl, byte* inner, word32 sz, int content,
                           int verify)
{
    if (ssl == NULL || inner == NULL)
        return BAD_FUNC_ARG;

    XMEMSET(inner, 0, WOLFSSL_TLS_HMAC_INNER_SZ);

    WriteSEQ(ssl, verify, inner);
    inner[SEQ_SZ] = (byte)content;
    inner[SEQ_SZ + ENUM_LEN]            = ssl->version.major;
    inner[SEQ_SZ + ENUM_LEN + ENUM_LEN] = ssl->version.minor;
    c16toa((word16)sz, inner + SEQ_SZ + ENUM_LEN + VERSION_SZ);

    return 0;
}


#ifndef WOLFSSL_AEAD_ONLY
#if !defined(WOLFSSL_NO_HASH_RAW) && !defined(HAVE_FIPS) && \
    !defined(HAVE_SELFTEST)

/* Update the hash in the HMAC.
 *
 * hmac  HMAC object.
 * data  Data to be hashed.
 * sz    Size of data to hash.
 * returns 0 on success, otherwise failure.
 */
static int Hmac_HashUpdate(Hmac* hmac, const byte* data, word32 sz)
{
    int ret = BAD_FUNC_ARG;

    switch (hmac->macType) {
    #ifndef NO_SHA
        case WC_SHA:
            ret = wc_ShaUpdate(&hmac->hash.sha, data, sz);
            break;
    #endif /* !NO_SHA */

    #ifndef NO_SHA256
        case WC_SHA256:
            ret = wc_Sha256Update(&hmac->hash.sha256, data, sz);
            break;
    #endif /* !NO_SHA256 */

    #ifdef WOLFSSL_SHA384
        case WC_SHA384:
            ret = wc_Sha384Update(&hmac->hash.sha384, data, sz);
            break;
    #endif /* WOLFSSL_SHA384 */

    #ifdef WOLFSSL_SHA512
        case WC_SHA512:
            ret = wc_Sha512Update(&hmac->hash.sha512, data, sz);
            break;
    #endif /* WOLFSSL_SHA512 */
    }

    return ret;
}

/* Finalize the hash but don't put the EOC, padding or length in.
 *
 * hmac  HMAC object.
 * hash  Hash result.
 * returns 0 on success, otherwise failure.
 */
static int Hmac_HashFinalRaw(Hmac* hmac, unsigned char* hash)
{
    int ret = BAD_FUNC_ARG;

    switch (hmac->macType) {
    #ifndef NO_SHA
        case WC_SHA:
            ret = wc_ShaFinalRaw(&hmac->hash.sha, hash);
            break;
    #endif /* !NO_SHA */

    #ifndef NO_SHA256
        case WC_SHA256:
            ret = wc_Sha256FinalRaw(&hmac->hash.sha256, hash);
            break;
    #endif /* !NO_SHA256 */

    #ifdef WOLFSSL_SHA384
        case WC_SHA384:
            ret = wc_Sha384FinalRaw(&hmac->hash.sha384, hash);
            break;
    #endif /* WOLFSSL_SHA384 */

    #ifdef WOLFSSL_SHA512
        case WC_SHA512:
            ret = wc_Sha512FinalRaw(&hmac->hash.sha512, hash);
            break;
    #endif /* WOLFSSL_SHA512 */
    }

    return ret;
}

/* Finalize the HMAC by performing outer hash.
 *
 * hmac  HMAC object.
 * mac   MAC result.
 * returns 0 on success, otherwise failure.
 */
static int Hmac_OuterHash(Hmac* hmac, unsigned char* mac)
{
    int ret = BAD_FUNC_ARG;
    wc_HashAlg hash;
    enum wc_HashType hashType = (enum wc_HashType)hmac->macType;
    int digestSz = wc_HashGetDigestSize(hashType);
    int blockSz = wc_HashGetBlockSize(hashType);

    if ((digestSz >= 0) && (blockSz >= 0)) {
        ret = wc_HashInit(&hash, hashType);
    }
    if (ret == 0) {
        ret = wc_HashUpdate(&hash, hashType, (byte*)hmac->opad,
            blockSz);
        if (ret == 0)
            ret = wc_HashUpdate(&hash, hashType, (byte*)hmac->innerHash,
                digestSz);
        if (ret == 0)
            ret = wc_HashFinal(&hash, hashType, mac);
        wc_HashFree(&hash, hashType);
    }

    return ret;
}

/* Calculate the HMAC of the header + message data.
 * Constant time implementation using wc_Sha*FinalRaw().
 *
 * hmac    HMAC object.
 * digest  MAC result.
 * in      Message data.
 * sz      Size of the message data.
 * header  Constructed record header with length of handshake data.
 * returns 0 on success, otherwise failure.
 */
static int Hmac_UpdateFinal_CT(Hmac* hmac, byte* digest, const byte* in,
                               word32 sz, byte* header)
{
    byte lenBytes[8];
    int  i, j, k;
    int  blockBits, blockMask;
    int  lastBlockLen, macLen, extraLen, eocIndex;
    int  blocks, safeBlocks, lenBlock, eocBlock;
    int  maxLen;
    int  blockSz, padSz;
    int  ret;
    word32 realLen;
    byte extraBlock;

    switch (hmac->macType) {
    #ifndef NO_SHA
        case WC_SHA:
            blockSz = WC_SHA_BLOCK_SIZE;
            blockBits = 6;
            macLen = WC_SHA_DIGEST_SIZE;
            padSz = WC_SHA_BLOCK_SIZE - WC_SHA_PAD_SIZE + 1;
            break;
    #endif /* !NO_SHA */

    #ifndef NO_SHA256
        case WC_SHA256:
            blockSz = WC_SHA256_BLOCK_SIZE;
            blockBits = 6;
            macLen = WC_SHA256_DIGEST_SIZE;
            padSz = WC_SHA256_BLOCK_SIZE - WC_SHA256_PAD_SIZE + 1;
            break;
    #endif /* !NO_SHA256 */

    #ifdef WOLFSSL_SHA384
        case WC_SHA384:
            blockSz = WC_SHA384_BLOCK_SIZE;
            blockBits = 7;
            macLen = WC_SHA384_DIGEST_SIZE;
            padSz = WC_SHA384_BLOCK_SIZE - WC_SHA384_PAD_SIZE + 1;
            break;
    #endif /* WOLFSSL_SHA384 */

    #ifdef WOLFSSL_SHA512
        case WC_SHA512:
            blockSz = WC_SHA512_BLOCK_SIZE;
            blockBits = 7;
            macLen = WC_SHA512_DIGEST_SIZE;
            padSz = WC_SHA512_BLOCK_SIZE - WC_SHA512_PAD_SIZE + 1;
            break;
    #endif /* WOLFSSL_SHA512 */

        default:
            return BAD_FUNC_ARG;
    }
    blockMask = blockSz - 1;

    /* Size of data to HMAC if padding length byte is zero. */
    maxLen = WOLFSSL_TLS_HMAC_INNER_SZ + sz - 1 - macLen;
    /* Complete data (including padding) has block for EOC and/or length. */
    extraBlock = ctSetLTE((maxLen + padSz) & blockMask, padSz);
    /* Total number of blocks for data including padding. */
    blocks = ((maxLen + blockSz - 1) >> blockBits) + extraBlock;
    /* Up to last 6 blocks can be hashed safely. */
    safeBlocks = blocks - 6;

    /* Length of message data. */
    realLen = maxLen - in[sz - 1];
    /* Number of message bytes in last block. */
    lastBlockLen = realLen & blockMask;
    /* Number of padding bytes in last block. */
    extraLen = ((blockSz * 2 - padSz - lastBlockLen) & blockMask) + 1;
    /* Number of blocks to create for hash. */
    lenBlock = (realLen + extraLen) >> blockBits;
    /* Block containing EOC byte. */
    eocBlock = realLen >> blockBits;
    /* Index of EOC byte in block. */
    eocIndex = realLen & blockMask;

    /* Add length of hmac's ipad to total length. */
    realLen += blockSz;
    /* Length as bits - 8 bytes bigendian. */
    c32toa(realLen >> ((sizeof(word32) * 8) - 3), lenBytes);
    c32toa(realLen << 3, lenBytes + sizeof(word32));

    ret = Hmac_HashUpdate(hmac, (unsigned char*)hmac->ipad, blockSz);
    if (ret != 0)
        return ret;

    XMEMSET(hmac->innerHash, 0, macLen);

    if (safeBlocks > 0) {
        ret = Hmac_HashUpdate(hmac, header, WOLFSSL_TLS_HMAC_INNER_SZ);
        if (ret != 0)
            return ret;
        ret = Hmac_HashUpdate(hmac, in, safeBlocks * blockSz -
                                                     WOLFSSL_TLS_HMAC_INNER_SZ);
        if (ret != 0)
            return ret;
    }
    else
        safeBlocks = 0;

    XMEMSET(digest, 0, macLen);
    k = safeBlocks * blockSz;
    for (i = safeBlocks; i < blocks; i++) {
        unsigned char hashBlock[WC_MAX_BLOCK_SIZE];
        unsigned char isEocBlock = ctMaskEq(i, eocBlock);
        unsigned char isOutBlock = ctMaskEq(i, lenBlock);

        for (j = 0; j < blockSz; j++, k++) {
            unsigned char atEoc = ctMaskEq(j, eocIndex) & isEocBlock;
            unsigned char pastEoc = ctMaskGT(j, eocIndex) & isEocBlock;
            unsigned char b = 0;

            if (k < WOLFSSL_TLS_HMAC_INNER_SZ)
                b = header[k];
            else if (k < maxLen)
                b = in[k - WOLFSSL_TLS_HMAC_INNER_SZ];

            b = ctMaskSel(atEoc, 0x80, b);
            b &= (unsigned char)~(word32)pastEoc;
            b &= ((unsigned char)~(word32)isOutBlock) | isEocBlock;

            if (j >= blockSz - 8) {
                b = ctMaskSel(isOutBlock, lenBytes[j - (blockSz - 8)], b);
            }

            hashBlock[j] = b;
        }

        ret = Hmac_HashUpdate(hmac, hashBlock, blockSz);
        if (ret != 0)
            return ret;
        ret = Hmac_HashFinalRaw(hmac, hashBlock);
        if (ret != 0)
            return ret;
        for (j = 0; j < macLen; j++)
            ((unsigned char*)hmac->innerHash)[j] |= hashBlock[j] & isOutBlock;
    }

    ret = Hmac_OuterHash(hmac, digest);

    return ret;
}

#endif

#if defined(WOLFSSL_NO_HASH_RAW) || defined(HAVE_FIPS) || \
    defined(HAVE_SELFTEST) || defined(HAVE_BLAKE2)

/* Calculate the HMAC of the header + message data.
 * Constant time implementation using normal hashing operations.
 * Update-Final need to be constant time.
 *
 * hmac    HMAC object.
 * digest  MAC result.
 * in      Message data.
 * sz      Size of the message data.
 * header  Constructed record header with length of handshake data.
 * returns 0 on success, otherwise failure.
 */
static int Hmac_UpdateFinal(Hmac* hmac, byte* digest, const byte* in,
                            word32 sz, byte* header)
{
    byte       dummy[WC_MAX_BLOCK_SIZE] = {0};
    int        ret;
    word32     msgSz, blockSz, macSz, padSz, maxSz, realSz;
    word32     currSz, offset = 0;
    int        msgBlocks, blocks, blockBits;
    int        i;

    switch (hmac->macType) {
    #ifndef NO_SHA
        case WC_SHA:
            blockSz = WC_SHA_BLOCK_SIZE;
            blockBits = 6;
            macSz = WC_SHA_DIGEST_SIZE;
            padSz = WC_SHA_BLOCK_SIZE - WC_SHA_PAD_SIZE + 1;
            break;
    #endif /* !NO_SHA */

    #ifndef NO_SHA256
        case WC_SHA256:
            blockSz = WC_SHA256_BLOCK_SIZE;
            blockBits = 6;
            macSz = WC_SHA256_DIGEST_SIZE;
            padSz = WC_SHA256_BLOCK_SIZE - WC_SHA256_PAD_SIZE + 1;
            break;
    #endif /* !NO_SHA256 */

    #ifdef WOLFSSL_SHA384
        case WC_SHA384:
            blockSz = WC_SHA384_BLOCK_SIZE;
            blockBits = 7;
            macSz = WC_SHA384_DIGEST_SIZE;
            padSz = WC_SHA384_BLOCK_SIZE - WC_SHA384_PAD_SIZE + 1;
            break;
    #endif /* WOLFSSL_SHA384 */

    #ifdef WOLFSSL_SHA512
        case WC_SHA512:
            blockSz = WC_SHA512_BLOCK_SIZE;
            blockBits = 7;
            macSz = WC_SHA512_DIGEST_SIZE;
            padSz = WC_SHA512_BLOCK_SIZE - WC_SHA512_PAD_SIZE + 1;
            break;
    #endif /* WOLFSSL_SHA512 */

    #ifdef HAVE_BLAKE2
        case WC_HASH_TYPE_BLAKE2B:
            blockSz = BLAKE2B_BLOCKBYTES;
            blockBits = 7;
            macSz = BLAKE2B_256;
            padSz = 0;
            break;
    #endif /* HAVE_BLAK2 */

        default:
            return BAD_FUNC_ARG;
    }

    msgSz = sz - (1 + in[sz - 1] + macSz);
    /* Make negative result 0 */
    msgSz &= ~(0 - (msgSz >> 31));
    realSz = WOLFSSL_TLS_HMAC_INNER_SZ + msgSz;
    maxSz = WOLFSSL_TLS_HMAC_INNER_SZ + (sz - 1) - macSz;

    /* Calculate #blocks processed in HMAC for max and real data. */
    blocks      = maxSz >> blockBits;
    blocks     += ((maxSz + padSz) % blockSz) < padSz;
    msgBlocks   = realSz >> blockBits;
    /* #Extra blocks to process. */
    blocks -= msgBlocks + (((realSz + padSz) % blockSz) < padSz);
    /* Calculate whole blocks. */
    msgBlocks--;

    ret = wc_HmacUpdate(hmac, header, WOLFSSL_TLS_HMAC_INNER_SZ);
    if (ret == 0) {
        /* Fill the rest of the block with any available data. */
        currSz = ctMaskLT(msgSz, blockSz) & msgSz;
        currSz |= ctMaskGTE(msgSz, blockSz) & blockSz;
        currSz -= WOLFSSL_TLS_HMAC_INNER_SZ;
        currSz &= ~(0 - (currSz >> 31));
        ret = wc_HmacUpdate(hmac, in, currSz);
        offset = currSz;
    }
    if (ret == 0) {
        /* Do the hash operations on a block basis. */
        for (i = 0; i < msgBlocks; i++, offset += blockSz) {
            ret = wc_HmacUpdate(hmac, in + offset, blockSz);
            if (ret != 0)
                break;
        }
    }
    if (ret == 0)
        ret = wc_HmacUpdate(hmac, in + offset, msgSz - offset);
    if (ret == 0)
        ret = wc_HmacFinal(hmac, digest);
    if (ret == 0) {
        /* Do the dummy hash operations. Do at least one. */
        for (i = 0; i < blocks + 1; i++) {
            ret = wc_HmacUpdate(hmac, dummy, blockSz);
            if (ret != 0)
                break;
        }
    }

    return ret;
}

#endif

int TLS_hmac(WOLFSSL* ssl, byte* digest, const byte* in, word32 sz, int padSz,
             int content, int verify, int epochOrder)
{
    Hmac   hmac;
    byte   myInner[WOLFSSL_TLS_HMAC_INNER_SZ];
    int    ret = 0;
    const byte* macSecret = NULL;
    word32 hashSz = 0;

    if (ssl == NULL)
        return BAD_FUNC_ARG;

#ifdef HAVE_TRUNCATED_HMAC
    hashSz = ssl->truncated_hmac ? (byte)TRUNCATED_HMAC_SZ
                                        : ssl->specs.hash_size;
#else
    hashSz = ssl->specs.hash_size;
#endif

#ifdef HAVE_FUZZER
    /* Fuzz "in" buffer with sz to be used in HMAC algorithm */
    if (ssl->fuzzerCb) {
        if (verify && padSz >= 0) {
            ssl->fuzzerCb(ssl, in, sz + hashSz + padSz + 1, FUZZ_HMAC,
                          ssl->fuzzerCtx);
        }
        else {
            ssl->fuzzerCb(ssl, in, sz, FUZZ_HMAC, ssl->fuzzerCtx);
        }
    }
#endif

    if (!ssl->options.dtls)
        wolfSSL_SetTlsHmacInner(ssl, myInner, sz, content, verify);
    else
        wolfSSL_SetTlsHmacInner(ssl, myInner, sz, content, epochOrder);
#if defined(WOLFSSL_RENESAS_TSIP_TLS) && \
    !defined(NO_WOLFSSL_RENESAS_TSIP_TLS_SESSION)
    if (tsip_useable(ssl)) {
        if (ssl->specs.hash_size == WC_SHA_DIGEST_SIZE)
            ret = tsip_Sha1Hmac(ssl, myInner, WOLFSSL_TLS_HMAC_INNER_SZ,
                                                        in, sz, digest, verify);
        else if (ssl->specs.hash_size == WC_SHA256_DIGEST_SIZE)
            ret = tsip_Sha256Hmac(ssl, myInner, WOLFSSL_TLS_HMAC_INNER_SZ,
                                                        in, sz, digest, verify);
        else
            ret = TSIP_MAC_DIGSZ_E;

        return ret;
    }
#endif
    ret = wc_HmacInit(&hmac, ssl->heap, ssl->devId);
    if (ret != 0)
        return ret;


#ifdef WOLFSSL_DTLS
    if (ssl->options.dtls)
        macSecret = wolfSSL_GetDtlsMacSecret(ssl, verify, epochOrder);
    else
        macSecret = wolfSSL_GetMacSecret(ssl, verify);
#else
    macSecret = wolfSSL_GetMacSecret(ssl, verify);
#endif
    ret = wc_HmacSetKey(&hmac, wolfSSL_GetHmacType(ssl),
                                              macSecret,
                                              ssl->specs.hash_size);

    if (ret == 0) {
        /* Constant time verification required. */
        if (verify && padSz >= 0) {
#if !defined(WOLFSSL_NO_HASH_RAW) && !defined(HAVE_FIPS) && \
    !defined(HAVE_SELFTEST)
    #ifdef HAVE_BLAKE2
            if (wolfSSL_GetHmacType(ssl) == WC_HASH_TYPE_BLAKE2B) {
                ret = Hmac_UpdateFinal(&hmac, digest, in,
                                              sz + hashSz + padSz + 1, myInner);
            }
            else
    #endif
            {
                ret = Hmac_UpdateFinal_CT(&hmac, digest, in,
                                              sz + hashSz + padSz + 1, myInner);
            }
#else
            ret = Hmac_UpdateFinal(&hmac, digest, in, sz + hashSz + padSz + 1,
                                                                       myInner);
#endif
        }
        else {
            ret = wc_HmacUpdate(&hmac, myInner, sizeof(myInner));
            if (ret == 0)
                ret = wc_HmacUpdate(&hmac, in, sz);                /* content */
            if (ret == 0)
                ret = wc_HmacFinal(&hmac, digest);
        }
    }

    wc_HmacFree(&hmac);

    return ret;
}
#endif /* WOLFSSL_AEAD_ONLY */

#endif /* !WOLFSSL_NO_TLS12 */

#ifdef HAVE_TLS_EXTENSIONS

/**
 * The TLSX semaphore is used to calculate the size of the extensions to be sent
 * from one peer to another.
 */

/** Supports up to 64 flags. Increase as needed. */
#define SEMAPHORE_SIZE 8

/**
 * Converts the extension type (id) to an index in the semaphore.
 *
 * Official reference for TLS extension types:
 *   http://www.iana.org/assignments/tls-extensiontype-values/tls-extensiontype-values.xml
 *
 * Motivation:
 *   Previously, we used the extension type itself as the index of that
 *   extension in the semaphore as the extension types were declared
 *   sequentially, but maintain a semaphore as big as the number of available
 *   extensions is no longer an option since the release of renegotiation_info.
 *
 * How to update:
 *   Assign extension types that extrapolate the number of available semaphores
 *   to the first available index going backwards in the semaphore array.
 *   When adding a new extension type that don't extrapolate the number of
 *   available semaphores, check for a possible collision with with a
 *   'remapped' extension type.
 */
static WC_INLINE word16 TLSX_ToSemaphore(word16 type)
{
    switch (type) {

        case TLSX_RENEGOTIATION_INFO: /* 0xFF01 */
            return 63;

        default:
            if (type > 62) {
                /* This message SHOULD only happens during the adding of
                   new TLS extensions in which its IANA number overflows
                   the current semaphore's range, or if its number already
                   is assigned to be used by another extension.
                   Use this check value for the new extension and decrement
                   the check value by one. */
                WOLFSSL_MSG("### TLSX semaphore collision or overflow detected!");
            }
    }

    return type;
}

/** Checks if a specific light (tls extension) is not set in the semaphore. */
#define IS_OFF(semaphore, light) \
    (!(((semaphore)[(light) / 8] &  (byte) (0x01 << ((light) % 8)))))

/** Turn on a specific light (tls extension) in the semaphore. */
/* the semaphore marks the extensions already written to the message */
#define TURN_ON(semaphore, light) \
    ((semaphore)[(light) / 8] |= (byte) (0x01 << ((light) % 8)))

/** Turn off a specific light (tls extension) in the semaphore. */
#define TURN_OFF(semaphore, light) \
    ((semaphore)[(light) / 8] &= (byte) ~(0x01 << ((light) % 8)))

/** Creates a new extension. */
static TLSX* TLSX_New(TLSX_Type type, void* data, void* heap)
{
    TLSX* extension = (TLSX*)XMALLOC(sizeof(TLSX), heap, DYNAMIC_TYPE_TLSX);

    (void)heap;

    if (extension) {
        extension->type = type;
        extension->data = data;
        extension->resp = 0;
        extension->next = NULL;
    }

    return extension;
}

/**
 * Creates a new extension and pushes it to the provided list.
 * Checks for duplicate extensions, keeps the newest.
 */
static int TLSX_Push(TLSX** list, TLSX_Type type, void* data, void* heap)
{
    TLSX* extension = TLSX_New(type, data, heap);

    if (extension == NULL)
        return MEMORY_E;

    /* pushes the new extension on the list. */
    extension->next = *list;
    *list = extension;

    /* remove duplicate extensions, there should be only one of each type. */
    do {
        if (extension->next && extension->next->type == type) {
            TLSX *next = extension->next;

            extension->next = next->next;
            next->next = NULL;

            TLSX_FreeAll(next, heap);

            /* there is no way to occur more than
             * two extensions of the same type.
             */
            break;
        }
    } while ((extension = extension->next));

    return 0;
}

#ifdef WOLFSSL_TLS13

/**
 * Creates a new extension and prepend it to the provided list.
 * Checks for duplicate extensions, keeps the newest.
 */
static int TLSX_Prepend(TLSX** list, TLSX_Type type, void* data, void* heap)
{
    TLSX* extension = TLSX_New(type, data, heap);
    TLSX* curr = *list;

    if (extension == NULL)
        return MEMORY_E;

    /* remove duplicate extensions, there should be only one of each type. */
    while (curr && curr->next) {
        if (curr->next->type == type) {
            TLSX *next = curr->next;

            curr->next = next->next;
            next->next = NULL;

            TLSX_FreeAll(next, heap);
        }
        curr = curr->next;
    }

    if (curr)
        curr->next = extension;
    else
        *list = extension;

    return 0;
}

#endif /* WOLFSSL_TLS13 */

#ifndef NO_WOLFSSL_CLIENT

int TLSX_CheckUnsupportedExtension(WOLFSSL* ssl, TLSX_Type type);

int TLSX_CheckUnsupportedExtension(WOLFSSL* ssl, TLSX_Type type)
{
    TLSX *extension = TLSX_Find(ssl->extensions, type);

    if (!extension)
        extension = TLSX_Find(ssl->ctx->extensions, type);

    return extension == NULL;
}

int TLSX_HandleUnsupportedExtension(WOLFSSL* ssl);

int TLSX_HandleUnsupportedExtension(WOLFSSL* ssl)
{
    SendAlert(ssl, alert_fatal, unsupported_extension);
    return UNSUPPORTED_EXTENSION;
}

#else

#define TLSX_CheckUnsupportedExtension(ssl, type) 0
#define TLSX_HandleUnsupportedExtension(ssl) 0

#endif

/** Mark an extension to be sent back to the client. */
void TLSX_SetResponse(WOLFSSL* ssl, TLSX_Type type);

void TLSX_SetResponse(WOLFSSL* ssl, TLSX_Type type)
{
    TLSX *extension = TLSX_Find(ssl->extensions, type);

    if (extension)
        extension->resp = 1;
}

/******************************************************************************/
/* Application-Layer Protocol Negotiation                                     */
/******************************************************************************/

#ifdef HAVE_ALPN
/** Creates a new ALPN object, providing protocol name to use. */
static ALPN* TLSX_ALPN_New(char *protocol_name, word16 protocol_nameSz,
                                                                     void* heap)
{
    ALPN *alpn;

    WOLFSSL_ENTER("TLSX_ALPN_New");

    if (protocol_name == NULL ||
        protocol_nameSz > WOLFSSL_MAX_ALPN_PROTO_NAME_LEN) {
        WOLFSSL_MSG("Invalid arguments");
        return NULL;
    }

    alpn = (ALPN*)XMALLOC(sizeof(ALPN), heap, DYNAMIC_TYPE_TLSX);
    if (alpn == NULL) {
        WOLFSSL_MSG("Memory failure");
        return NULL;
    }

    alpn->next = NULL;
    alpn->negotiated = 0;
    alpn->options = 0;

    alpn->protocol_name = (char*)XMALLOC(protocol_nameSz + 1,
                                         heap, DYNAMIC_TYPE_TLSX);
    if (alpn->protocol_name == NULL) {
        WOLFSSL_MSG("Memory failure");
        XFREE(alpn, heap, DYNAMIC_TYPE_TLSX);
        return NULL;
    }

    XMEMCPY(alpn->protocol_name, protocol_name, protocol_nameSz);
    alpn->protocol_name[protocol_nameSz] = 0;

    (void)heap;

    return alpn;
}

/** Releases an ALPN object. */
static void TLSX_ALPN_Free(ALPN *alpn, void* heap)
{
    (void)heap;

    if (alpn == NULL)
        return;

    XFREE(alpn->protocol_name, heap, DYNAMIC_TYPE_TLSX);
    XFREE(alpn, heap, DYNAMIC_TYPE_TLSX);
}

/** Releases all ALPN objects in the provided list. */
static void TLSX_ALPN_FreeAll(ALPN *list, void* heap)
{
    ALPN* alpn;

    while ((alpn = list)) {
        list = alpn->next;
        TLSX_ALPN_Free(alpn, heap);
    }
}

/** Tells the buffered size of the ALPN objects in a list. */
static word16 TLSX_ALPN_GetSize(ALPN *list)
{
    ALPN* alpn;
    word16 length = OPAQUE16_LEN; /* list length */

    while ((alpn = list)) {
        list = alpn->next;

        length++; /* protocol name length is on one byte */
        length += (word16)XSTRLEN(alpn->protocol_name);
    }

    return length;
}

/** Writes the ALPN objects of a list in a buffer. */
static word16 TLSX_ALPN_Write(ALPN *list, byte *output)
{
    ALPN* alpn;
    word16 length = 0;
    word16 offset = OPAQUE16_LEN; /* list length offset */

    while ((alpn = list)) {
        list = alpn->next;

        length = (word16)XSTRLEN(alpn->protocol_name);

        /* protocol name length */
        output[offset++] = (byte)length;

        /* protocol name value */
        XMEMCPY(output + offset, alpn->protocol_name, length);

        offset += length;
    }

    /* writing list length */
    c16toa(offset - OPAQUE16_LEN, output);

    return offset;
}

/** Finds a protocol name in the provided ALPN list */
static ALPN* TLSX_ALPN_Find(ALPN *list, char *protocol_name, word16 size)
{
    ALPN *alpn;

    if (list == NULL || protocol_name == NULL)
        return NULL;

    alpn = list;
    while (alpn != NULL && (
           (word16)XSTRLEN(alpn->protocol_name) != size ||
           XSTRNCMP(alpn->protocol_name, protocol_name, size)))
        alpn = alpn->next;

    return alpn;
}

/** Set the ALPN matching client and server requirements */
static int TLSX_SetALPN(TLSX** extensions, const void* data, word16 size,
                                                                     void* heap)
{
    ALPN *alpn;
    int  ret;

    if (extensions == NULL || data == NULL)
        return BAD_FUNC_ARG;

    alpn = TLSX_ALPN_New((char *)data, size, heap);
    if (alpn == NULL) {
        WOLFSSL_MSG("Memory failure");
        return MEMORY_E;
    }

    alpn->negotiated = 1;

    ret = TLSX_Push(extensions, TLSX_APPLICATION_LAYER_PROTOCOL, (void*)alpn,
                                                                          heap);
    if (ret != 0) {
        TLSX_ALPN_Free(alpn, heap);
        return ret;
    }

    return WOLFSSL_SUCCESS;
}

/** Parses a buffer of ALPN extensions and set the first one matching
 * client and server requirements */
static int TLSX_ALPN_ParseAndSet(WOLFSSL *ssl, byte *input, word16 length,
                                 byte isRequest)
{
    word16  size = 0, offset = 0, idx = 0;
    int     r = BUFFER_ERROR;
    byte    match = 0;
    TLSX    *extension;
    ALPN    *alpn = NULL, *list;

    if (OPAQUE16_LEN > length)
        return BUFFER_ERROR;

    ato16(input, &size);
    offset += OPAQUE16_LEN;

    if (size == 0)
        return BUFFER_ERROR;

    extension = TLSX_Find(ssl->extensions, TLSX_APPLICATION_LAYER_PROTOCOL);
    if (extension == NULL)
        extension = TLSX_Find(ssl->ctx->extensions,
                                               TLSX_APPLICATION_LAYER_PROTOCOL);

#if defined(OPENSSL_ALL) || defined(WOLFSSL_NGINX) || defined(WOLFSSL_HAPROXY)
    if (ssl->alpnSelect != NULL) {
        const byte* out;
        unsigned char outLen;

        if (ssl->alpnSelect(ssl, &out, &outLen, input + offset, size,
                            ssl->alpnSelectArg) == 0) {
            WOLFSSL_MSG("ALPN protocol match");
            if (TLSX_UseALPN(&ssl->extensions, (char*)out, outLen, 0, ssl->heap)
                                                           == WOLFSSL_SUCCESS) {
                if (extension == NULL) {
                    extension = TLSX_Find(ssl->extensions,
                                          TLSX_APPLICATION_LAYER_PROTOCOL);
                }
            }
        }
    }
#endif

    if (extension == NULL || extension->data == NULL) {
        return isRequest ? 0
                         : TLSX_HandleUnsupportedExtension(ssl);
    }

    /* validating alpn list length */
    if (length != OPAQUE16_LEN + size)
        return BUFFER_ERROR;

    list = (ALPN*)extension->data;

    /* keep the list sent by client */
    if (isRequest) {
        if (ssl->alpn_client_list != NULL)
            XFREE(ssl->alpn_client_list, ssl->heap, DYNAMIC_TYPE_ALPN);

        ssl->alpn_client_list = (char *)XMALLOC(size, ssl->heap,
                                                DYNAMIC_TYPE_ALPN);
        if (ssl->alpn_client_list == NULL)
            return MEMORY_ERROR;
    }

    for (size = 0; offset < length; offset += size) {

        size = input[offset++];
        if (offset + size > length || size == 0)
            return BUFFER_ERROR;

        if (isRequest) {
            XMEMCPY(ssl->alpn_client_list+idx, (char*)input + offset, size);
            idx += size;
            ssl->alpn_client_list[idx++] = ',';
        }

        if (!match) {
            alpn = TLSX_ALPN_Find(list, (char*)input + offset, size);
            if (alpn != NULL) {
                WOLFSSL_MSG("ALPN protocol match");
                match = 1;

                /* skip reading other values if not required */
                if (!isRequest)
                    break;
            }
        }
    }

    if (isRequest)
        ssl->alpn_client_list[idx-1] = 0;

    if (!match) {
        WOLFSSL_MSG("No ALPN protocol match");

        /* do nothing if no protocol match between client and server and option
         is set to continue (like OpenSSL) */
        if (list->options & WOLFSSL_ALPN_CONTINUE_ON_MISMATCH) {
            WOLFSSL_MSG("Continue on mismatch");
            return 0;
        }

        SendAlert(ssl, alert_fatal, no_application_protocol);
        return UNKNOWN_ALPN_PROTOCOL_NAME_E;
    }

    /* set the matching negotiated protocol */
    r = TLSX_SetALPN(&ssl->extensions,
                     alpn->protocol_name,
                     (word16)XSTRLEN(alpn->protocol_name),
                     ssl->heap);
    if (r != WOLFSSL_SUCCESS) {
        WOLFSSL_MSG("TLSX_UseALPN failed");
        return BUFFER_ERROR;
    }

    /* reply to ALPN extension sent from client */
    if (isRequest) {
#ifndef NO_WOLFSSL_SERVER
        TLSX_SetResponse(ssl, TLSX_APPLICATION_LAYER_PROTOCOL);
#endif
    }

    return 0;
}

/** Add a protocol name to the list of accepted usable ones */
int TLSX_UseALPN(TLSX** extensions, const void* data, word16 size, byte options,
                                                                     void* heap)
{
    ALPN *alpn;
    TLSX *extension;
    int  ret;

    if (extensions == NULL || data == NULL)
        return BAD_FUNC_ARG;

    alpn = TLSX_ALPN_New((char *)data, size, heap);
    if (alpn == NULL) {
        WOLFSSL_MSG("Memory failure");
        return MEMORY_E;
    }

    /* Set Options of ALPN */
    alpn->options = options;

    extension = TLSX_Find(*extensions, TLSX_APPLICATION_LAYER_PROTOCOL);
    if (extension == NULL) {
        ret = TLSX_Push(extensions, TLSX_APPLICATION_LAYER_PROTOCOL,
                                                             (void*)alpn, heap);
        if (ret != 0) {
            TLSX_ALPN_Free(alpn, heap);
            return ret;
        }
    }
    else {
        /* push new ALPN object to extension data. */
        alpn->next = (ALPN*)extension->data;
        extension->data = (void*)alpn;
    }

    return WOLFSSL_SUCCESS;
}

/** Get the protocol name set by the server */
int TLSX_ALPN_GetRequest(TLSX* extensions, void** data, word16 *dataSz)
{
    TLSX *extension;
    ALPN *alpn;

    if (extensions == NULL || data == NULL || dataSz == NULL)
        return BAD_FUNC_ARG;

    extension = TLSX_Find(extensions, TLSX_APPLICATION_LAYER_PROTOCOL);
    if (extension == NULL) {
        WOLFSSL_MSG("TLS extension not found");
        return WOLFSSL_ALPN_NOT_FOUND;
    }

    alpn = (ALPN *)extension->data;
    if (alpn == NULL) {
        WOLFSSL_MSG("ALPN extension not found");
        *data = NULL;
        *dataSz = 0;
        return WOLFSSL_FATAL_ERROR;
    }

    if (alpn->negotiated != 1) {

        /* consider as an error */
        if (alpn->options & WOLFSSL_ALPN_FAILED_ON_MISMATCH) {
            WOLFSSL_MSG("No protocol match with peer -> Failed");
            return WOLFSSL_FATAL_ERROR;
        }

        /* continue without negotiated protocol */
        WOLFSSL_MSG("No protocol match with peer -> Continue");
        return WOLFSSL_ALPN_NOT_FOUND;
    }

    if (alpn->next != NULL) {
        WOLFSSL_MSG("Only one protocol name must be accepted");
        return WOLFSSL_FATAL_ERROR;
    }

    *data = alpn->protocol_name;
    *dataSz = (word16)XSTRLEN((char*)*data);

    return WOLFSSL_SUCCESS;
}

#define ALPN_FREE_ALL     TLSX_ALPN_FreeAll
#define ALPN_GET_SIZE     TLSX_ALPN_GetSize
#define ALPN_WRITE        TLSX_ALPN_Write
#define ALPN_PARSE        TLSX_ALPN_ParseAndSet

#else /* HAVE_ALPN */

#define ALPN_FREE_ALL(list, heap)
#define ALPN_GET_SIZE(list)     0
#define ALPN_WRITE(a, b)        0
#define ALPN_PARSE(a, b, c, d)  0

#endif /* HAVE_ALPN */

/******************************************************************************/
/* Server Name Indication                                                     */
/******************************************************************************/

#ifdef HAVE_SNI

/** Creates a new SNI object. */
static SNI* TLSX_SNI_New(byte type, const void* data, word16 size, void* heap)
{
    SNI* sni = (SNI*)XMALLOC(sizeof(SNI), heap, DYNAMIC_TYPE_TLSX);

    (void)heap;

    if (sni) {
        sni->type = type;
        sni->next = NULL;

    #ifndef NO_WOLFSSL_SERVER
        sni->options = 0;
        sni->status  = WOLFSSL_SNI_NO_MATCH;
    #endif

        switch (sni->type) {
            case WOLFSSL_SNI_HOST_NAME:
                sni->data.host_name = (char*)XMALLOC(size + 1, heap,
                                                     DYNAMIC_TYPE_TLSX);
                if (sni->data.host_name) {
                    XSTRNCPY(sni->data.host_name, (const char*)data, size);
                    sni->data.host_name[size] = '\0';
                } else {
                    XFREE(sni, heap, DYNAMIC_TYPE_TLSX);
                    sni = NULL;
                }
            break;

            default: /* invalid type */
                XFREE(sni, heap, DYNAMIC_TYPE_TLSX);
                sni = NULL;
        }
    }

    return sni;
}

/** Releases a SNI object. */
static void TLSX_SNI_Free(SNI* sni, void* heap)
{
    if (sni) {
        switch (sni->type) {
            case WOLFSSL_SNI_HOST_NAME:
                XFREE(sni->data.host_name, heap, DYNAMIC_TYPE_TLSX);
            break;
        }

        XFREE(sni, heap, DYNAMIC_TYPE_TLSX);
    }
    (void)heap;
}

/** Releases all SNI objects in the provided list. */
static void TLSX_SNI_FreeAll(SNI* list, void* heap)
{
    SNI* sni;

    while ((sni = list)) {
        list = sni->next;
        TLSX_SNI_Free(sni, heap);
    }
}

/** Tells the buffered size of the SNI objects in a list. */
static word16 TLSX_SNI_GetSize(SNI* list)
{
    SNI* sni;
    word16 length = OPAQUE16_LEN; /* list length */

    while ((sni = list)) {
        list = sni->next;

        length += ENUM_LEN + OPAQUE16_LEN; /* sni type + sni length */

        switch (sni->type) {
            case WOLFSSL_SNI_HOST_NAME:
                length += (word16)XSTRLEN((char*)sni->data.host_name);
            break;
        }
    }

    return length;
}

/** Writes the SNI objects of a list in a buffer. */
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
                length = (word16)XSTRLEN((char*)sni->data.host_name);

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

/** Finds a SNI object in the provided list. */
static SNI* TLSX_SNI_Find(SNI *list, byte type)
{
    SNI* sni = list;

    while (sni && sni->type != type)
        sni = sni->next;

    return sni;
}

/** Sets the status of a SNI object. */
static void TLSX_SNI_SetStatus(TLSX* extensions, byte type, byte status)
{
    TLSX* extension = TLSX_Find(extensions, TLSX_SERVER_NAME);
    SNI* sni = TLSX_SNI_Find(extension ? (SNI*)extension->data : NULL, type);

    if (sni)
        sni->status = status;
}

/** Gets the status of a SNI object. */
byte TLSX_SNI_Status(TLSX* extensions, byte type)
{
    TLSX* extension = TLSX_Find(extensions, TLSX_SERVER_NAME);
    SNI* sni = TLSX_SNI_Find(extension ? (SNI*)extension->data : NULL, type);

    if (sni)
        return sni->status;

    return 0;
}

/** Parses a buffer of SNI extensions. */
static int TLSX_SNI_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                                                 byte isRequest)
{
#ifndef NO_WOLFSSL_SERVER
    word16 size = 0;
    word16 offset = 0;
    int cacheOnly = 0;
    SNI *sni = NULL;
    byte type;
    int matchStat;
    byte matched;
#endif

    TLSX *extension = TLSX_Find(ssl->extensions, TLSX_SERVER_NAME);

    if (!extension)
        extension = TLSX_Find(ssl->ctx->extensions, TLSX_SERVER_NAME);

    if (!isRequest) {
        #ifndef NO_WOLFSSL_CLIENT
            if (!extension || !extension->data)
                return TLSX_HandleUnsupportedExtension(ssl);

            if (length > 0)
                return BUFFER_ERROR; /* SNI response MUST be empty. */

            /* This call enables wolfSSL_SNI_GetRequest() to be called in the
             * client side to fetch the used SNI. It will only work if the SNI
             * was set at the SSL object level. Right now we only support one
             * name type, WOLFSSL_SNI_HOST_NAME, but in the future, the
             * inclusion of other name types will turn this method inaccurate,
             * as the extension response doesn't contains information of which
             * name was accepted.
             */
            TLSX_SNI_SetStatus(ssl->extensions, WOLFSSL_SNI_HOST_NAME,
                                                        WOLFSSL_SNI_REAL_MATCH);

            return 0;
        #endif
    }

#ifndef NO_WOLFSSL_SERVER
    if (!extension || !extension->data) {
        #if defined(WOLFSSL_ALWAYS_KEEP_SNI) && !defined(NO_WOLFSSL_SERVER)
            /* This will keep SNI even though TLSX_UseSNI has not been called.
            * Enable it so that the received sni is available to functions
            * that use a custom callback when SNI is received.
            */

            cacheOnly = 1;
            WOLFSSL_MSG("Forcing SSL object to store SNI parameter");
        #else
            /* Skipping, SNI not enabled at server side. */
            return 0;
        #endif
    }

    if (OPAQUE16_LEN > length)
        return BUFFER_ERROR;

    ato16(input, &size);
    offset += OPAQUE16_LEN;

    /* validating sni list length */
    if (length != OPAQUE16_LEN + size || size == 0)
        return BUFFER_ERROR;

    /* SNI was badly specified and only one type is now recognized and allowed.
     * Only one SNI value per type (RFC6066), so, no loop. */
    type = input[offset++];
    if (type != WOLFSSL_SNI_HOST_NAME)
        return BUFFER_ERROR;

    if (offset + OPAQUE16_LEN > length)
        return BUFFER_ERROR;
    ato16(input + offset, &size);
    offset += OPAQUE16_LEN;

    if (offset + size != length || size == 0)
        return BUFFER_ERROR;

    if (!cacheOnly && !(sni = TLSX_SNI_Find((SNI*)extension->data, type)))
        return 0; /* not using this type of SNI. */

#ifdef WOLFSSL_TLS13
    /* Don't process the second ClientHello SNI extension if there
     * was problems with the first.
     */
    if (!cacheOnly && sni->status != 0)
        return 0;
#endif
    matched = cacheOnly || (XSTRLEN(sni->data.host_name) == size &&
         XSTRNCMP(sni->data.host_name, (const char*)input + offset, size) == 0);

    if (matched || sni->options & WOLFSSL_SNI_ANSWER_ON_MISMATCH) {
        int r = TLSX_UseSNI(&ssl->extensions, type, input + offset, size,
                                                                     ssl->heap);
        if (r != WOLFSSL_SUCCESS)
            return r; /* throws error. */

        if (cacheOnly) {
            WOLFSSL_MSG("Forcing storage of SNI, Fake match");
            matchStat = WOLFSSL_SNI_FORCE_KEEP;
        }
        else if (matched) {
            WOLFSSL_MSG("SNI did match!");
            matchStat = WOLFSSL_SNI_REAL_MATCH;
        }
        else {
            WOLFSSL_MSG("fake SNI match from ANSWER_ON_MISMATCH");
            matchStat = WOLFSSL_SNI_FAKE_MATCH;
        }

        TLSX_SNI_SetStatus(ssl->extensions, type, (byte)matchStat);

        if(!cacheOnly)
            TLSX_SetResponse(ssl, TLSX_SERVER_NAME);
    }
    else if (!(sni->options & WOLFSSL_SNI_CONTINUE_ON_MISMATCH)) {
        SendAlert(ssl, alert_fatal, unrecognized_name);

        return UNKNOWN_SNI_HOST_NAME_E;
    }
#else
    (void)input;
#endif

    return 0;
}

static int TLSX_SNI_VerifyParse(WOLFSSL* ssl,  byte isRequest)
{
    (void)ssl;

    if (isRequest) {
    #ifndef NO_WOLFSSL_SERVER
        TLSX* ctx_ext = TLSX_Find(ssl->ctx->extensions, TLSX_SERVER_NAME);
        TLSX* ssl_ext = TLSX_Find(ssl->extensions,      TLSX_SERVER_NAME);
        SNI* ctx_sni = ctx_ext ? (SNI*)ctx_ext->data : NULL;
        SNI* ssl_sni = ssl_ext ? (SNI*)ssl_ext->data : NULL;
        SNI* sni = NULL;

        for (; ctx_sni; ctx_sni = ctx_sni->next) {
            if (ctx_sni->options & WOLFSSL_SNI_ABORT_ON_ABSENCE) {
                sni = TLSX_SNI_Find(ssl_sni, ctx_sni->type);

                if (sni) {
                    if (sni->status != WOLFSSL_SNI_NO_MATCH)
                        continue;

                    /* if ssl level overrides ctx level, it is ok. */
                    if ((sni->options & WOLFSSL_SNI_ABORT_ON_ABSENCE) == 0)
                        continue;
                }

                SendAlert(ssl, alert_fatal, handshake_failure);
                return SNI_ABSENT_ERROR;
            }
        }

        for (; ssl_sni; ssl_sni = ssl_sni->next) {
            if (ssl_sni->options & WOLFSSL_SNI_ABORT_ON_ABSENCE) {
                if (ssl_sni->status != WOLFSSL_SNI_NO_MATCH)
                    continue;

                SendAlert(ssl, alert_fatal, handshake_failure);
                return SNI_ABSENT_ERROR;
            }
        }
    #endif /* NO_WOLFSSL_SERVER */
    }

    return 0;
}

int TLSX_UseSNI(TLSX** extensions, byte type, const void* data, word16 size,
                                                                     void* heap)
{
    TLSX* extension;
    SNI* sni = NULL;

    if (extensions == NULL || data == NULL)
        return BAD_FUNC_ARG;

    if ((sni = TLSX_SNI_New(type, data, size, heap)) == NULL)
        return MEMORY_E;

    extension = TLSX_Find(*extensions, TLSX_SERVER_NAME);
    if (!extension) {
        int ret = TLSX_Push(extensions, TLSX_SERVER_NAME, (void*)sni, heap);

        if (ret != 0) {
            TLSX_SNI_Free(sni, heap);
            return ret;
        }
    }
    else {
        /* push new SNI object to extension data. */
        sni->next = (SNI*)extension->data;
        extension->data = (void*)sni;

        /* remove duplicate SNI, there should be only one of each type. */
        do {
            if (sni->next && sni->next->type == type) {
                SNI* next = sni->next;

                sni->next = next->next;
                TLSX_SNI_Free(next, heap);

                /* there is no way to occur more than
                 * two SNIs of the same type.
                 */
                break;
            }
        } while ((sni = sni->next));
    }

    return WOLFSSL_SUCCESS;
}

#ifndef NO_WOLFSSL_SERVER

/** Tells the SNI requested by the client. */
word16 TLSX_SNI_GetRequest(TLSX* extensions, byte type, void** data)
{
    TLSX* extension = TLSX_Find(extensions, TLSX_SERVER_NAME);
    SNI* sni = TLSX_SNI_Find(extension ? (SNI*)extension->data : NULL, type);

    if (sni && sni->status != WOLFSSL_SNI_NO_MATCH) {
        switch (sni->type) {
            case WOLFSSL_SNI_HOST_NAME:
                if (data) {
                    *data = sni->data.host_name;
                    return (word16)XSTRLEN((char*)*data);
                }
        }
    }

    return 0;
}

/** Sets the options for a SNI object. */
void TLSX_SNI_SetOptions(TLSX* extensions, byte type, byte options)
{
    TLSX* extension = TLSX_Find(extensions, TLSX_SERVER_NAME);
    SNI* sni = TLSX_SNI_Find(extension ? (SNI*)extension->data : NULL, type);

    if (sni)
        sni->options = options;
}

/** Retrieves a SNI request from a client hello buffer. */
int TLSX_SNI_GetFromBuffer(const byte* clientHello, word32 helloSz,
                           byte type, byte* sni, word32* inOutSz)
{
    word32 offset = 0;
    word32 len32 = 0;
    word16 len16 = 0;

    if (helloSz < RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ + CLIENT_HELLO_FIRST)
        return INCOMPLETE_DATA;

    /* TLS record header */
    if ((enum ContentType) clientHello[offset++] != handshake) {

        /* checking for SSLv2.0 client hello according to: */
        /* http://tools.ietf.org/html/rfc4346#appendix-E.1 */
        if ((enum HandShakeType) clientHello[++offset] == client_hello) {
            offset += ENUM_LEN + VERSION_SZ; /* skip version */

            ato16(clientHello + offset, &len16);
            offset += OPAQUE16_LEN;

            if (len16 % 3) /* cipher_spec_length must be multiple of 3 */
                return BUFFER_ERROR;

            ato16(clientHello + offset, &len16);
            /* Returning SNI_UNSUPPORTED do not increment offset here */

            if (len16 != 0) /* session_id_length must be 0 */
                return BUFFER_ERROR;

            return SNI_UNSUPPORTED;
        }

        return BUFFER_ERROR;
    }

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

        if (extType != TLSX_SERVER_NAME) {
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

                return WOLFSSL_SUCCESS;
            }
        }

        len16 -= min(2 * OPAQUE16_LEN + extLen, len16);
    }

    return len16 ? BUFFER_ERROR : 0;
}

#endif

#define SNI_FREE_ALL     TLSX_SNI_FreeAll
#define SNI_GET_SIZE     TLSX_SNI_GetSize
#define SNI_WRITE        TLSX_SNI_Write
#define SNI_PARSE        TLSX_SNI_Parse
#define SNI_VERIFY_PARSE TLSX_SNI_VerifyParse

#else

#define SNI_FREE_ALL(list, heap)
#define SNI_GET_SIZE(list)     0
#define SNI_WRITE(a, b)        0
#define SNI_PARSE(a, b, c, d)  0
#define SNI_VERIFY_PARSE(a, b) 0

#endif /* HAVE_SNI */

/******************************************************************************/
/* Trusted CA Key Indication                                                  */
/******************************************************************************/

#ifdef HAVE_TRUSTED_CA

/** Creates a new TCA object. */
static TCA* TLSX_TCA_New(byte type, const byte* id, word16 idSz, void* heap)
{
    TCA* tca = (TCA*)XMALLOC(sizeof(TCA), heap, DYNAMIC_TYPE_TLSX);

    if (tca) {
        XMEMSET(tca, 0, sizeof(TCA));
        tca->type = type;

        switch (type) {
            case WOLFSSL_TRUSTED_CA_PRE_AGREED:
                break;

            #ifndef NO_SHA
            case WOLFSSL_TRUSTED_CA_KEY_SHA1:
            case WOLFSSL_TRUSTED_CA_CERT_SHA1:
                if (idSz == WC_SHA_DIGEST_SIZE &&
                        (tca->id =
                            (byte*)XMALLOC(idSz, heap, DYNAMIC_TYPE_TLSX))) {
                    XMEMCPY(tca->id, id, idSz);
                    tca->idSz = idSz;
                }
                else {
                    XFREE(tca, heap, DYNAMIC_TYPE_TLSX);
                    tca = NULL;
                }
                break;
            #endif

            case WOLFSSL_TRUSTED_CA_X509_NAME:
                if (idSz > 0 &&
                        (tca->id =
                            (byte*)XMALLOC(idSz, heap, DYNAMIC_TYPE_TLSX))) {
                    XMEMCPY(tca->id, id, idSz);
                    tca->idSz = idSz;
                }
                else {
                    XFREE(tca, heap, DYNAMIC_TYPE_TLSX);
                    tca = NULL;
                }
                break;

            default: /* invalid type */
                XFREE(tca, heap, DYNAMIC_TYPE_TLSX);
                tca = NULL;
        }
    }

    (void)heap;

    return tca;
}

/** Releases a TCA object. */
static void TLSX_TCA_Free(TCA* tca, void* heap)
{
    (void)heap;

    if (tca) {
        if (tca->id)
            XFREE(tca->id, heap, DYNAMIC_TYPE_TLSX);
        XFREE(tca, heap, DYNAMIC_TYPE_TLSX);
    }
}

/** Releases all TCA objects in the provided list. */
static void TLSX_TCA_FreeAll(TCA* list, void* heap)
{
    TCA* tca;

    while ((tca = list)) {
        list = tca->next;
        TLSX_TCA_Free(tca, heap);
    }
}

/** Tells the buffered size of the TCA objects in a list. */
static word16 TLSX_TCA_GetSize(TCA* list)
{
    TCA* tca;
    word16 length = OPAQUE16_LEN; /* list length */

    while ((tca = list)) {
        list = tca->next;

        length += ENUM_LEN; /* tca type */

        switch (tca->type) {
            case WOLFSSL_TRUSTED_CA_PRE_AGREED:
                break;
            case WOLFSSL_TRUSTED_CA_KEY_SHA1:
            case WOLFSSL_TRUSTED_CA_CERT_SHA1:
                length += tca->idSz;
                break;
            case WOLFSSL_TRUSTED_CA_X509_NAME:
                length += OPAQUE16_LEN + tca->idSz;
                break;
        }
    }

    return length;
}

/** Writes the TCA objects of a list in a buffer. */
static word16 TLSX_TCA_Write(TCA* list, byte* output)
{
    TCA* tca;
    word16 offset = OPAQUE16_LEN; /* list length offset */

    while ((tca = list)) {
        list = tca->next;

        output[offset++] = tca->type; /* tca type */

        switch (tca->type) {
            case WOLFSSL_TRUSTED_CA_PRE_AGREED:
                break;
            #ifndef NO_SHA
            case WOLFSSL_TRUSTED_CA_KEY_SHA1:
            case WOLFSSL_TRUSTED_CA_CERT_SHA1:
                if (tca->id != NULL) {
                    XMEMCPY(output + offset, tca->id, tca->idSz);
                    offset += tca->idSz;
                }
                else {
                    /* ID missing. Set to an empty string. */
                    c16toa(0, output + offset);
                    offset += OPAQUE16_LEN;
                }
                break;
            #endif
            case WOLFSSL_TRUSTED_CA_X509_NAME:
                if (tca->id != NULL) {
                    c16toa(tca->idSz, output + offset); /* tca length */
                    offset += OPAQUE16_LEN;
                    XMEMCPY(output + offset, tca->id, tca->idSz);
                    offset += tca->idSz;
                }
                else {
                    /* ID missing. Set to an empty string. */
                    c16toa(0, output + offset);
                    offset += OPAQUE16_LEN;
                }
                break;
            default:
                /* ID unknown. Set to an empty string. */
                c16toa(0, output + offset);
                offset += OPAQUE16_LEN;
        }
    }

    c16toa(offset - OPAQUE16_LEN, output); /* writing list length */

    return offset;
}

#ifndef NO_WOLFSSL_SERVER
static TCA* TLSX_TCA_Find(TCA *list, byte type, const byte* id, word16 idSz)
{
    TCA* tca = list;

    while (tca && tca->type != type && type != WOLFSSL_TRUSTED_CA_PRE_AGREED &&
           idSz != tca->idSz && !XMEMCMP(id, tca->id, idSz))
        tca = tca->next;

    return tca;
}
#endif /* NO_WOLFSSL_SERVER */

/** Parses a buffer of TCA extensions. */
static int TLSX_TCA_Parse(WOLFSSL* ssl, const byte* input, word16 length,
                          byte isRequest)
{
#ifndef NO_WOLFSSL_SERVER
    word16 size = 0;
    word16 offset = 0;
#endif

    TLSX *extension = TLSX_Find(ssl->extensions, TLSX_TRUSTED_CA_KEYS);

    if (!extension)
        extension = TLSX_Find(ssl->ctx->extensions, TLSX_TRUSTED_CA_KEYS);

    if (!isRequest) {
        #ifndef NO_WOLFSSL_CLIENT
            if (!extension || !extension->data)
                return TLSX_HandleUnsupportedExtension(ssl);

            if (length > 0)
                return BUFFER_ERROR; /* TCA response MUST be empty. */

            /* Set the flag that we're good for keys */
            TLSX_SetResponse(ssl, TLSX_TRUSTED_CA_KEYS);

            return 0;
        #endif
    }

#ifndef NO_WOLFSSL_SERVER
    if (!extension || !extension->data) {
        /* Skipping, TCA not enabled at server side. */
        return 0;
    }

    if (OPAQUE16_LEN > length)
        return BUFFER_ERROR;

    ato16(input, &size);
    offset += OPAQUE16_LEN;

    /* validating tca list length */
    if (length != OPAQUE16_LEN + size)
        return BUFFER_ERROR;

    for (size = 0; offset < length; offset += size) {
        TCA *tca = NULL;
        byte type;
        const byte* id = NULL;
        word16 idSz = 0;

        if (offset + ENUM_LEN > length)
            return BUFFER_ERROR;

        type = input[offset++];

        switch (type) {
            case WOLFSSL_TRUSTED_CA_PRE_AGREED:
                break;
            #ifndef NO_SHA
            case WOLFSSL_TRUSTED_CA_KEY_SHA1:
            case WOLFSSL_TRUSTED_CA_CERT_SHA1:
                if (offset + WC_SHA_DIGEST_SIZE > length)
                    return BUFFER_ERROR;
                idSz = WC_SHA_DIGEST_SIZE;
                id = input + offset;
                offset += idSz;
                break;
            #endif
            case WOLFSSL_TRUSTED_CA_X509_NAME:
                if (offset + OPAQUE16_LEN > length)
                    return BUFFER_ERROR;
                ato16(input + offset, &idSz);
                offset += OPAQUE16_LEN;
                if ((offset > length) || (idSz > length - offset))
                    return BUFFER_ERROR;
                id = input + offset;
                offset += idSz;
                break;
            default:
                return TCA_INVALID_ID_TYPE;
        }

        /* Find the type/ID in the TCA list. */
        tca = TLSX_TCA_Find((TCA*)extension->data, type, id, idSz);
        if (tca != NULL) {
            /* Found it. Set the response flag and break out of the loop. */
            TLSX_SetResponse(ssl, TLSX_TRUSTED_CA_KEYS);
            break;
        }
    }
#else
    (void)input;
#endif

    return 0;
}

/* Checks to see if the server sent a response for the TCA. */
static int TLSX_TCA_VerifyParse(WOLFSSL* ssl, byte isRequest)
{
    (void)ssl;

    if (!isRequest) {
    #ifndef NO_WOLFSSL_CLIENT
        TLSX* extension = TLSX_Find(ssl->extensions, TLSX_TRUSTED_CA_KEYS);

        if (extension && !extension->resp) {
            SendAlert(ssl, alert_fatal, handshake_failure);
            return TCA_ABSENT_ERROR;
        }
    #endif /* NO_WOLFSSL_CLIENT */
    }

    return 0;
}

int TLSX_UseTrustedCA(TLSX** extensions, byte type,
                    const byte* id, word16 idSz, void* heap)
{
    TLSX* extension;
    TCA* tca = NULL;

    if (extensions == NULL)
        return BAD_FUNC_ARG;

    if ((tca = TLSX_TCA_New(type, id, idSz, heap)) == NULL)
        return MEMORY_E;

    extension = TLSX_Find(*extensions, TLSX_TRUSTED_CA_KEYS);
    if (!extension) {
        int ret = TLSX_Push(extensions, TLSX_TRUSTED_CA_KEYS, (void*)tca, heap);

        if (ret != 0) {
            TLSX_TCA_Free(tca, heap);
            return ret;
        }
    }
    else {
        /* push new TCA object to extension data. */
        tca->next = (TCA*)extension->data;
        extension->data = (void*)tca;
    }

    return WOLFSSL_SUCCESS;
}

#define TCA_FREE_ALL     TLSX_TCA_FreeAll
#define TCA_GET_SIZE     TLSX_TCA_GetSize
#define TCA_WRITE        TLSX_TCA_Write
#define TCA_PARSE        TLSX_TCA_Parse
#define TCA_VERIFY_PARSE TLSX_TCA_VerifyParse

#else /* HAVE_TRUSTED_CA */

#define TCA_FREE_ALL(list, heap)
#define TCA_GET_SIZE(list)     0
#define TCA_WRITE(a, b)        0
#define TCA_PARSE(a, b, c, d)  0
#define TCA_VERIFY_PARSE(a, b) 0

#endif /* HAVE_TRUSTED_CA */

/******************************************************************************/
/* Max Fragment Length Negotiation                                            */
/******************************************************************************/

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

#ifdef WOLFSSL_OLD_UNSUPPORTED_EXTENSION
    (void) isRequest;
#else
    if (!isRequest)
        if (TLSX_CheckUnsupportedExtension(ssl, TLSX_MAX_FRAGMENT_LENGTH))
            return TLSX_HandleUnsupportedExtension(ssl);
#endif

    switch (*input) {
        case WOLFSSL_MFL_2_8 : ssl->max_fragment =  256; break;
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
        int ret = TLSX_UseMaxFragment(&ssl->extensions, *input, ssl->heap);

        if (ret != WOLFSSL_SUCCESS)
            return ret; /* throw error */

        TLSX_SetResponse(ssl, TLSX_MAX_FRAGMENT_LENGTH);
    }
#endif

    return 0;
}

int TLSX_UseMaxFragment(TLSX** extensions, byte mfl, void* heap)
{
    byte* data = NULL;
    int ret = 0;

    if (extensions == NULL || mfl < WOLFSSL_MFL_MIN || mfl > WOLFSSL_MFL_MAX)
        return BAD_FUNC_ARG;

    data = (byte*)XMALLOC(ENUM_LEN, heap, DYNAMIC_TYPE_TLSX);
    if (data == NULL)
        return MEMORY_E;

    data[0] = mfl;

    ret = TLSX_Push(extensions, TLSX_MAX_FRAGMENT_LENGTH, data, heap);
    if (ret != 0) {
        XFREE(data, heap, DYNAMIC_TYPE_TLSX);
        return ret;
    }

    return WOLFSSL_SUCCESS;
}


#define MFL_FREE_ALL(data, heap) XFREE(data, (heap), DYNAMIC_TYPE_TLSX)
#define MFL_GET_SIZE(data) ENUM_LEN
#define MFL_WRITE          TLSX_MFL_Write
#define MFL_PARSE          TLSX_MFL_Parse

#else

#define MFL_FREE_ALL(a, b)
#define MFL_GET_SIZE(a)       0
#define MFL_WRITE(a, b)       0
#define MFL_PARSE(a, b, c, d) 0

#endif /* HAVE_MAX_FRAGMENT */

/******************************************************************************/
/* Truncated HMAC                                                             */
/******************************************************************************/

#ifdef HAVE_TRUNCATED_HMAC

static int TLSX_THM_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                                                 byte isRequest)
{
    if (length != 0 || input == NULL)
        return BUFFER_ERROR;

    if (!isRequest) {
    #ifndef WOLFSSL_OLD_UNSUPPORTED_EXTENSION
        if (TLSX_CheckUnsupportedExtension(ssl, TLSX_TRUNCATED_HMAC))
            return TLSX_HandleUnsupportedExtension(ssl);
    #endif
    }
    else {
        #ifndef NO_WOLFSSL_SERVER
            int ret = TLSX_UseTruncatedHMAC(&ssl->extensions, ssl->heap);

            if (ret != WOLFSSL_SUCCESS)
                return ret; /* throw error */

            TLSX_SetResponse(ssl, TLSX_TRUNCATED_HMAC);
        #endif
    }

    ssl->truncated_hmac = 1;

    return 0;
}

int TLSX_UseTruncatedHMAC(TLSX** extensions, void* heap)
{
    int ret = 0;

    if (extensions == NULL)
        return BAD_FUNC_ARG;

    ret = TLSX_Push(extensions, TLSX_TRUNCATED_HMAC, NULL, heap);
    if (ret != 0)
        return ret;

    return WOLFSSL_SUCCESS;
}

#define THM_PARSE TLSX_THM_Parse

#else

#define THM_PARSE(a, b, c, d) 0

#endif /* HAVE_TRUNCATED_HMAC */

/******************************************************************************/
/* Certificate Status Request                                                 */
/******************************************************************************/

#ifdef HAVE_CERTIFICATE_STATUS_REQUEST

static void TLSX_CSR_Free(CertificateStatusRequest* csr, void* heap)
{
    switch (csr->status_type) {
        case WOLFSSL_CSR_OCSP:
            FreeOcspRequest(&csr->request.ocsp);
        break;
    }

    XFREE(csr, heap, DYNAMIC_TYPE_TLSX);
    (void)heap;
}

static word16 TLSX_CSR_GetSize(CertificateStatusRequest* csr, byte isRequest)
{
    word16 size = 0;

    /* shut up compiler warnings */
    (void) csr; (void) isRequest;

#ifndef NO_WOLFSSL_CLIENT
    if (isRequest) {
        switch (csr->status_type) {
            case WOLFSSL_CSR_OCSP:
                size += ENUM_LEN + 2 * OPAQUE16_LEN;

                if (csr->request.ocsp.nonceSz)
                    size += OCSP_NONCE_EXT_SZ;
            break;
        }
    }
#endif
#if defined(WOLFSSL_TLS13) && !defined(NO_WOLFSSL_SERVER)
    if (!isRequest && csr->ssl->options.tls1_3)
        return OPAQUE8_LEN + OPAQUE24_LEN + csr->response.length;
#endif

    return size;
}

static word16 TLSX_CSR_Write(CertificateStatusRequest* csr, byte* output,
                                                                 byte isRequest)
{
    /* shut up compiler warnings */
    (void) csr; (void) output; (void) isRequest;

#ifndef NO_WOLFSSL_CLIENT
    if (isRequest) {
        word16 offset = 0;
        word16 length = 0;

        /* type */
        output[offset++] = csr->status_type;

        switch (csr->status_type) {
            case WOLFSSL_CSR_OCSP:
                /* responder id list */
                c16toa(0, output + offset);
                offset += OPAQUE16_LEN;

                /* request extensions */
                if (csr->request.ocsp.nonceSz)
                    length = (word16)EncodeOcspRequestExtensions(
                                                 &csr->request.ocsp,
                                                 output + offset + OPAQUE16_LEN,
                                                 OCSP_NONCE_EXT_SZ);

                c16toa(length, output + offset);
                offset += OPAQUE16_LEN + length;

            break;
        }

        return offset;
    }
#endif
#if defined(WOLFSSL_TLS13) && !defined(NO_WOLFSSL_SERVER)
    if (!isRequest && csr->ssl->options.tls1_3) {
        word16 offset = 0;
        output[offset++] = csr->status_type;
        c32to24(csr->response.length, output + offset);
        offset += OPAQUE24_LEN;
        XMEMCPY(output + offset, csr->response.buffer, csr->response.length);
        offset += csr->response.length;
        return offset;
    }
#endif

    return 0;
}

static int TLSX_CSR_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                                                 byte isRequest)
{
    int ret;

    /* shut up compiler warnings */
    (void) ssl; (void) input;

    if (!isRequest) {
#ifndef NO_WOLFSSL_CLIENT
        TLSX* extension = TLSX_Find(ssl->extensions, TLSX_STATUS_REQUEST);
        CertificateStatusRequest* csr = extension ?
                              (CertificateStatusRequest*)extension->data : NULL;

        if (!csr) {
            /* look at context level */
            extension = TLSX_Find(ssl->ctx->extensions, TLSX_STATUS_REQUEST);
            csr = extension ? (CertificateStatusRequest*)extension->data : NULL;

            if (!csr) /* unexpected extension */
                return TLSX_HandleUnsupportedExtension(ssl);

            /* enable extension at ssl level */
            ret = TLSX_UseCertificateStatusRequest(&ssl->extensions,
                                     csr->status_type, csr->options, ssl,
                                     ssl->heap, ssl->devId);
            if (ret != WOLFSSL_SUCCESS)
                return ret;

            switch (csr->status_type) {
                case WOLFSSL_CSR_OCSP:
                    /* propagate nonce */
                    if (csr->request.ocsp.nonceSz) {
                        OcspRequest* request =
                             (OcspRequest*)TLSX_CSR_GetRequest(ssl->extensions);

                        if (request) {
                            XMEMCPY(request->nonce, csr->request.ocsp.nonce,
                                                    csr->request.ocsp.nonceSz);
                            request->nonceSz = csr->request.ocsp.nonceSz;
                        }
                    }
                break;
            }
        }

        ssl->status_request = 1;

    #ifdef WOLFSSL_TLS13
        if (ssl->options.tls1_3) {
            word32       resp_length;
            word32       offset = 0;

            /* Get the new extension potentially created above. */
            extension = TLSX_Find(ssl->extensions, TLSX_STATUS_REQUEST);
            csr = extension ? (CertificateStatusRequest*)extension->data : NULL;
            if (csr == NULL)
                return MEMORY_ERROR;

            ret = 0;
            if (OPAQUE8_LEN + OPAQUE24_LEN > length)
                ret = BUFFER_ERROR;
            if (ret == 0 && input[offset++] != WOLFSSL_CSR_OCSP)
                ret = BAD_CERTIFICATE_STATUS_ERROR;
            if (ret == 0) {
                c24to32(input + offset, &resp_length);
                offset += OPAQUE24_LEN;
                if (offset + resp_length != length)
                    ret = BUFFER_ERROR;
            }
        #if !defined(NO_WOLFSSL_SERVER)
            if (ret == 0) {
                csr->response.buffer = input + offset;
                csr->response.length = resp_length;
            }
        #endif

            return ret;
        }
        else
    #endif
        {
            /* extension_data MUST be empty. */
            return length ? BUFFER_ERROR : 0;
        }
#endif
    }
    else {
#ifndef NO_WOLFSSL_SERVER
        byte   status_type;
        word16 offset = 0;
        word16 size = 0;

        if (length == 0)
            return 0;

        status_type = input[offset++];

        switch (status_type) {
            case WOLFSSL_CSR_OCSP: {

                /* skip responder_id_list */
                if (length - offset < OPAQUE16_LEN)
                    return BUFFER_ERROR;

                ato16(input + offset, &size);
                offset += OPAQUE16_LEN + size;

                /* skip request_extensions */
                if (length - offset < OPAQUE16_LEN)
                    return BUFFER_ERROR;

                ato16(input + offset, &size);
                offset += OPAQUE16_LEN + size;

                if (offset > length)
                    return BUFFER_ERROR;

                /* is able to send OCSP response? */
                if (ssl->ctx->cm == NULL || !ssl->ctx->cm->ocspStaplingEnabled)
                    return 0;
            }
            break;

            /* unknown status type */
            default:
                return 0;
        }

        /* if using status_request and already sending it, skip this one */
        #ifdef HAVE_CERTIFICATE_STATUS_REQUEST_V2
        if (ssl->status_request_v2)
            return 0;
        #endif

        /* accept the first good status_type and return */
        ret = TLSX_UseCertificateStatusRequest(&ssl->extensions, status_type,
                                                 0, ssl, ssl->heap, ssl->devId);
        if (ret != WOLFSSL_SUCCESS)
            return ret; /* throw error */

    #if defined(WOLFSSL_TLS13) && !defined(NO_WOLFSSL_SERVER)
        if (ssl->options.tls1_3) {
            OcspRequest* request;
            TLSX* extension = TLSX_Find(ssl->extensions, TLSX_STATUS_REQUEST);
            CertificateStatusRequest* csr = extension ?
                (CertificateStatusRequest*)extension->data : NULL;
            if (csr == NULL)
                return MEMORY_ERROR;

            request = &csr->request.ocsp;
            ret = CreateOcspResponse(ssl, &request, &csr->response);
            if (ret != 0)
                return ret;
            if (csr->response.buffer)
                TLSX_SetResponse(ssl, TLSX_STATUS_REQUEST);
        }
        else
    #endif
            TLSX_SetResponse(ssl, TLSX_STATUS_REQUEST);
        ssl->status_request = status_type;
#endif
    }

    return 0;
}

int TLSX_CSR_InitRequest(TLSX* extensions, DecodedCert* cert, void* heap)
{
    TLSX* extension = TLSX_Find(extensions, TLSX_STATUS_REQUEST);
    CertificateStatusRequest* csr = extension ?
        (CertificateStatusRequest*)extension->data : NULL;
    int ret = 0;

    if (csr) {
        switch (csr->status_type) {
            case WOLFSSL_CSR_OCSP: {
                byte nonce[MAX_OCSP_NONCE_SZ];
                int  nonceSz = csr->request.ocsp.nonceSz;

                /* preserve nonce */
                XMEMCPY(nonce, csr->request.ocsp.nonce, nonceSz);

                if ((ret = InitOcspRequest(&csr->request.ocsp, cert, 0, heap))
                                                                           != 0)
                    return ret;

                /* restore nonce */
                XMEMCPY(csr->request.ocsp.nonce, nonce, nonceSz);
                csr->request.ocsp.nonceSz = nonceSz;
            }
            break;
        }
    }

    return ret;
}

void* TLSX_CSR_GetRequest(TLSX* extensions)
{
    TLSX* extension = TLSX_Find(extensions, TLSX_STATUS_REQUEST);
    CertificateStatusRequest* csr = extension ?
                              (CertificateStatusRequest*)extension->data : NULL;

    if (csr) {
        switch (csr->status_type) {
            case WOLFSSL_CSR_OCSP:
                return &csr->request.ocsp;
            break;
        }
    }

    return NULL;
}

int TLSX_CSR_ForceRequest(WOLFSSL* ssl)
{
    TLSX* extension = TLSX_Find(ssl->extensions, TLSX_STATUS_REQUEST);
    CertificateStatusRequest* csr = extension ?
                              (CertificateStatusRequest*)extension->data : NULL;

    if (csr) {
        switch (csr->status_type) {
            case WOLFSSL_CSR_OCSP:
                if (ssl->ctx->cm->ocspEnabled) {
                    csr->request.ocsp.ssl = ssl;
                    return CheckOcspRequest(ssl->ctx->cm->ocsp,
                                                      &csr->request.ocsp, NULL);
                }
                else
                    return OCSP_LOOKUP_FAIL;
        }
    }

    return 0;
}

int TLSX_UseCertificateStatusRequest(TLSX** extensions, byte status_type,
                                         byte options, WOLFSSL* ssl, void* heap,
                                                                      int devId)
{
    CertificateStatusRequest* csr = NULL;
    int ret = 0;

    if (!extensions || status_type != WOLFSSL_CSR_OCSP)
        return BAD_FUNC_ARG;

    csr = (CertificateStatusRequest*)
             XMALLOC(sizeof(CertificateStatusRequest), heap, DYNAMIC_TYPE_TLSX);
    if (!csr)
        return MEMORY_E;

    ForceZero(csr, sizeof(CertificateStatusRequest));

    csr->status_type = status_type;
    csr->options     = options;
    csr->ssl         = ssl;

    switch (csr->status_type) {
        case WOLFSSL_CSR_OCSP:
            if (options & WOLFSSL_CSR_OCSP_USE_NONCE) {
                WC_RNG rng;

            #ifndef HAVE_FIPS
                ret = wc_InitRng_ex(&rng, heap, devId);
            #else
                ret = wc_InitRng(&rng);
                (void)devId;
            #endif
                if (ret == 0) {
                    if (wc_RNG_GenerateBlock(&rng, csr->request.ocsp.nonce,
                                                        MAX_OCSP_NONCE_SZ) == 0)
                        csr->request.ocsp.nonceSz = MAX_OCSP_NONCE_SZ;

                    wc_FreeRng(&rng);
                }
            }
        break;
    }

    if ((ret = TLSX_Push(extensions, TLSX_STATUS_REQUEST, csr, heap)) != 0) {
        XFREE(csr, heap, DYNAMIC_TYPE_TLSX);
        return ret;
    }

    return WOLFSSL_SUCCESS;
}

#define CSR_FREE_ALL TLSX_CSR_Free
#define CSR_GET_SIZE TLSX_CSR_GetSize
#define CSR_WRITE    TLSX_CSR_Write
#define CSR_PARSE    TLSX_CSR_Parse

#else

#define CSR_FREE_ALL(data, heap)
#define CSR_GET_SIZE(a, b)    0
#define CSR_WRITE(a, b, c)    0
#define CSR_PARSE(a, b, c, d) 0

#endif /* HAVE_CERTIFICATE_STATUS_REQUEST */

/******************************************************************************/
/* Certificate Status Request v2                                              */
/******************************************************************************/

#ifdef HAVE_CERTIFICATE_STATUS_REQUEST_V2

static void TLSX_CSR2_FreeAll(CertificateStatusRequestItemV2* csr2, void* heap)
{
    CertificateStatusRequestItemV2* next;

    for (; csr2; csr2 = next) {
        next = csr2->next;

        switch (csr2->status_type) {
            case WOLFSSL_CSR2_OCSP:
            case WOLFSSL_CSR2_OCSP_MULTI:
                while(csr2->requests--)
                    FreeOcspRequest(&csr2->request.ocsp[csr2->requests]);
            break;
        }

        XFREE(csr2, heap, DYNAMIC_TYPE_TLSX);
    }
    (void)heap;
}

static word16 TLSX_CSR2_GetSize(CertificateStatusRequestItemV2* csr2,
                                                                 byte isRequest)
{
    word16 size = 0;

    /* shut up compiler warnings */
    (void) csr2; (void) isRequest;

#ifndef NO_WOLFSSL_CLIENT
    if (isRequest) {
        CertificateStatusRequestItemV2* next;

        for (size = OPAQUE16_LEN; csr2; csr2 = next) {
            next = csr2->next;

            switch (csr2->status_type) {
                case WOLFSSL_CSR2_OCSP:
                case WOLFSSL_CSR2_OCSP_MULTI:
                    size += ENUM_LEN + 3 * OPAQUE16_LEN;

                    if (csr2->request.ocsp[0].nonceSz)
                        size += OCSP_NONCE_EXT_SZ;
                break;
            }
        }
    }
#endif

    return size;
}

static word16 TLSX_CSR2_Write(CertificateStatusRequestItemV2* csr2,
                                                   byte* output, byte isRequest)
{
    /* shut up compiler warnings */
    (void) csr2; (void) output; (void) isRequest;

#ifndef NO_WOLFSSL_CLIENT
    if (isRequest) {
        word16 offset;
        word16 length;

        for (offset = OPAQUE16_LEN; csr2 != NULL; csr2 = csr2->next) {
            /* status_type */
            output[offset++] = csr2->status_type;

            /* request */
            switch (csr2->status_type) {
                case WOLFSSL_CSR2_OCSP:
                case WOLFSSL_CSR2_OCSP_MULTI:
                    /* request_length */
                    length = 2 * OPAQUE16_LEN;

                    if (csr2->request.ocsp[0].nonceSz)
                        length += OCSP_NONCE_EXT_SZ;

                    c16toa(length, output + offset);
                    offset += OPAQUE16_LEN;

                    /* responder id list */
                    c16toa(0, output + offset);
                    offset += OPAQUE16_LEN;

                    /* request extensions */
                    length = 0;

                    if (csr2->request.ocsp[0].nonceSz)
                        length = (word16)EncodeOcspRequestExtensions(
                                                 &csr2->request.ocsp[0],
                                                 output + offset + OPAQUE16_LEN,
                                                 OCSP_NONCE_EXT_SZ);

                    c16toa(length, output + offset);
                    offset += OPAQUE16_LEN + length;
                break;
            }
        }

        /* list size */
        c16toa(offset - OPAQUE16_LEN, output);

        return offset;
    }
#endif

    return 0;
}

static int TLSX_CSR2_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                                                 byte isRequest)
{
    int ret;

    /* shut up compiler warnings */
    (void) ssl; (void) input;

    if (!isRequest) {
#ifndef NO_WOLFSSL_CLIENT
        TLSX* extension = TLSX_Find(ssl->extensions, TLSX_STATUS_REQUEST_V2);
        CertificateStatusRequestItemV2* csr2 = extension ?
                        (CertificateStatusRequestItemV2*)extension->data : NULL;

        if (!csr2) {
            /* look at context level */
            extension = TLSX_Find(ssl->ctx->extensions, TLSX_STATUS_REQUEST_V2);
            csr2 = extension ?
                        (CertificateStatusRequestItemV2*)extension->data : NULL;

            if (!csr2) /* unexpected extension */
                return TLSX_HandleUnsupportedExtension(ssl);

            /* enable extension at ssl level */
            for (; csr2; csr2 = csr2->next) {
                ret = TLSX_UseCertificateStatusRequestV2(&ssl->extensions,
                                    csr2->status_type, csr2->options, ssl->heap,
                                                                    ssl->devId);
                if (ret != WOLFSSL_SUCCESS)
                    return ret;

                switch (csr2->status_type) {
                    case WOLFSSL_CSR2_OCSP:
                        /* followed by */
                    case WOLFSSL_CSR2_OCSP_MULTI:
                        /* propagate nonce */
                        if (csr2->request.ocsp[0].nonceSz) {
                            OcspRequest* request =
                             (OcspRequest*)TLSX_CSR2_GetRequest(ssl->extensions,
                                                          csr2->status_type, 0);

                            if (request) {
                                XMEMCPY(request->nonce,
                                        csr2->request.ocsp[0].nonce,
                                        csr2->request.ocsp[0].nonceSz);

                                request->nonceSz =
                                                  csr2->request.ocsp[0].nonceSz;
                            }
                        }
                    break;
                }
            }
        }

        ssl->status_request_v2 = 1;

        return length ? BUFFER_ERROR : 0; /* extension_data MUST be empty. */
#endif
    }
    else {
#ifndef NO_WOLFSSL_SERVER
        byte   status_type;
        word16 request_length;
        word16 offset = 0;
        word16 size = 0;

        /* list size */
        if (offset + OPAQUE16_LEN >= length) {
            return BUFFER_E;
        }

        ato16(input + offset, &request_length);
        offset += OPAQUE16_LEN;

        if (length - OPAQUE16_LEN != request_length)
            return BUFFER_ERROR;

        while (length > offset) {
            if (length - offset < ENUM_LEN + OPAQUE16_LEN)
                return BUFFER_ERROR;

            status_type = input[offset++];

            ato16(input + offset, &request_length);
            offset += OPAQUE16_LEN;

            if (length - offset < request_length)
                return BUFFER_ERROR;

            switch (status_type) {
                case WOLFSSL_CSR2_OCSP:
                case WOLFSSL_CSR2_OCSP_MULTI:
                    /* skip responder_id_list */
                    if (length - offset < OPAQUE16_LEN)
                        return BUFFER_ERROR;

                    ato16(input + offset, &size);
                    if (length - offset < size)
                        return BUFFER_ERROR;

                    offset += OPAQUE16_LEN + size;
                    /* skip request_extensions */
                    if (length - offset < OPAQUE16_LEN)
                        return BUFFER_ERROR;

                    ato16(input + offset, &size);
                    if (length - offset < size)
                        return BUFFER_ERROR;

                    offset += OPAQUE16_LEN + size;
                    if (offset > length)
                        return BUFFER_ERROR;

                    /* is able to send OCSP response? */
                    if (ssl->ctx->cm == NULL
                    || !ssl->ctx->cm->ocspStaplingEnabled)
                        continue;
                break;

                default:
                    /* unknown status type, skipping! */
                    offset += request_length;
                    continue;
            }

            /* if using status_request and already sending it, skip this one */
            #ifdef HAVE_CERTIFICATE_STATUS_REQUEST
            if (ssl->status_request)
                return 0;
            #endif

            /* TLS 1.3 servers MUST NOT act upon presence or information in
             * this extension (RFC 8448 Section 4.4.2.1).
             */
            if (!IsAtLeastTLSv1_3(ssl->version)) {
                /* accept the first good status_type and return */
                ret = TLSX_UseCertificateStatusRequestV2(&ssl->extensions,
                                         status_type, 0, ssl->heap, ssl->devId);
                if (ret != WOLFSSL_SUCCESS)
                    return ret; /* throw error */

                TLSX_SetResponse(ssl, TLSX_STATUS_REQUEST_V2);
                ssl->status_request_v2 = status_type;
            }

            return 0;
        }
#endif
    }

    return 0;
}

int TLSX_CSR2_InitRequests(TLSX* extensions, DecodedCert* cert, byte isPeer,
                                                                     void* heap)
{
    TLSX* extension = TLSX_Find(extensions, TLSX_STATUS_REQUEST_V2);
    CertificateStatusRequestItemV2* csr2 = extension ?
        (CertificateStatusRequestItemV2*)extension->data : NULL;
    int ret = 0;

    for (; csr2; csr2 = csr2->next) {
        switch (csr2->status_type) {
            case WOLFSSL_CSR2_OCSP:
                if (!isPeer || csr2->requests != 0)
                    break;

                FALL_THROUGH; /* followed by */

            case WOLFSSL_CSR2_OCSP_MULTI: {
                if (csr2->requests < 1 + MAX_CHAIN_DEPTH) {
                    byte nonce[MAX_OCSP_NONCE_SZ];
                    int  nonceSz = csr2->request.ocsp[0].nonceSz;

                    /* preserve nonce, replicating nonce of ocsp[0] */
                    XMEMCPY(nonce, csr2->request.ocsp[0].nonce, nonceSz);

                    if ((ret = InitOcspRequest(
                                      &csr2->request.ocsp[csr2->requests], cert,
                                                                 0, heap)) != 0)
                        return ret;

                    /* restore nonce */
                    XMEMCPY(csr2->request.ocsp[csr2->requests].nonce,
                                                                nonce, nonceSz);
                    csr2->request.ocsp[csr2->requests].nonceSz = nonceSz;
                    csr2->requests++;
                }
            }
            break;
        }
    }

    (void)cert;
    return ret;
}

void* TLSX_CSR2_GetRequest(TLSX* extensions, byte status_type, byte idx)
{
    TLSX* extension = TLSX_Find(extensions, TLSX_STATUS_REQUEST_V2);
    CertificateStatusRequestItemV2* csr2 = extension ?
                        (CertificateStatusRequestItemV2*)extension->data : NULL;

    for (; csr2; csr2 = csr2->next) {
        if (csr2->status_type == status_type) {
            switch (csr2->status_type) {
                case WOLFSSL_CSR2_OCSP:
                    /* followed by */

                case WOLFSSL_CSR2_OCSP_MULTI:
                    /* requests are initialized in the reverse order */
                    return idx < csr2->requests
                         ? &csr2->request.ocsp[csr2->requests - idx - 1]
                         : NULL;
                break;
            }
        }
    }

    return NULL;
}

int TLSX_CSR2_ForceRequest(WOLFSSL* ssl)
{
    TLSX* extension = TLSX_Find(ssl->extensions, TLSX_STATUS_REQUEST_V2);
    CertificateStatusRequestItemV2* csr2 = extension ?
                        (CertificateStatusRequestItemV2*)extension->data : NULL;

    /* forces only the first one */
    if (csr2) {
        switch (csr2->status_type) {
            case WOLFSSL_CSR2_OCSP:
                /* followed by */

            case WOLFSSL_CSR2_OCSP_MULTI:
                if (ssl->ctx->cm->ocspEnabled) {
                    csr2->request.ocsp[0].ssl = ssl;
                    return CheckOcspRequest(ssl->ctx->cm->ocsp,
                                                  &csr2->request.ocsp[0], NULL);
                }
                else
                    return OCSP_LOOKUP_FAIL;
        }
    }

    return 0;
}

int TLSX_UseCertificateStatusRequestV2(TLSX** extensions, byte status_type,
                                           byte options, void* heap, int devId)
{
    TLSX* extension = NULL;
    CertificateStatusRequestItemV2* csr2 = NULL;
    int ret = 0;

    if (!extensions)
        return BAD_FUNC_ARG;

    if (status_type != WOLFSSL_CSR2_OCSP
    &&  status_type != WOLFSSL_CSR2_OCSP_MULTI)
        return BAD_FUNC_ARG;

    csr2 = (CertificateStatusRequestItemV2*)
       XMALLOC(sizeof(CertificateStatusRequestItemV2), heap, DYNAMIC_TYPE_TLSX);
    if (!csr2)
        return MEMORY_E;

    ForceZero(csr2, sizeof(CertificateStatusRequestItemV2));

    csr2->status_type = status_type;
    csr2->options     = options;
    csr2->next        = NULL;

    switch (csr2->status_type) {
        case WOLFSSL_CSR2_OCSP:
        case WOLFSSL_CSR2_OCSP_MULTI:
            if (options & WOLFSSL_CSR2_OCSP_USE_NONCE) {
                WC_RNG rng;

            #ifndef HAVE_FIPS
                ret = wc_InitRng_ex(&rng, heap, devId);
            #else
                ret = wc_InitRng(&rng);
                (void)devId;
            #endif
                if (ret == 0) {
                    if (wc_RNG_GenerateBlock(&rng, csr2->request.ocsp[0].nonce,
                                                        MAX_OCSP_NONCE_SZ) == 0)
                        csr2->request.ocsp[0].nonceSz = MAX_OCSP_NONCE_SZ;

                    wc_FreeRng(&rng);
                }
            }
        break;
    }

    /* append new item */
    if ((extension = TLSX_Find(*extensions, TLSX_STATUS_REQUEST_V2))) {
        CertificateStatusRequestItemV2* last =
                               (CertificateStatusRequestItemV2*)extension->data;

        for (; last->next; last = last->next);

        last->next = csr2;
    }
    else if ((ret = TLSX_Push(extensions, TLSX_STATUS_REQUEST_V2, csr2,heap))) {
        XFREE(csr2, heap, DYNAMIC_TYPE_TLSX);
        return ret;
    }

    return WOLFSSL_SUCCESS;
}

#define CSR2_FREE_ALL TLSX_CSR2_FreeAll
#define CSR2_GET_SIZE TLSX_CSR2_GetSize
#define CSR2_WRITE    TLSX_CSR2_Write
#define CSR2_PARSE    TLSX_CSR2_Parse

#else

#define CSR2_FREE_ALL(data, heap)
#define CSR2_GET_SIZE(a, b)    0
#define CSR2_WRITE(a, b, c)    0
#define CSR2_PARSE(a, b, c, d) 0

#endif /* HAVE_CERTIFICATE_STATUS_REQUEST_V2 */

/******************************************************************************/
/* Supported Elliptic Curves                                                  */
/******************************************************************************/

#ifdef HAVE_SUPPORTED_CURVES

#if !defined(HAVE_ECC) && !defined(HAVE_CURVE25519) && !defined(HAVE_CURVE448) \
                       && !defined(HAVE_FFDHE)
#error Elliptic Curves Extension requires Elliptic Curve Cryptography. \
       Use --enable-ecc in the configure script or define HAVE_ECC. \
       Alternatively use FFDHE for DH ciphersuites.
#endif

static int TLSX_SupportedCurve_New(SupportedCurve** curve, word16 name,
                                                                     void* heap)
{
    if (curve == NULL)
        return BAD_FUNC_ARG;

    (void)heap;

    *curve = (SupportedCurve*)XMALLOC(sizeof(SupportedCurve), heap,
                                                             DYNAMIC_TYPE_TLSX);
    if (*curve == NULL)
        return MEMORY_E;

    (*curve)->name = name;
    (*curve)->next = NULL;

    return 0;
}

static int TLSX_PointFormat_New(PointFormat** point, byte format, void* heap)
{
    if (point == NULL)
        return BAD_FUNC_ARG;

    (void)heap;

    *point = (PointFormat*)XMALLOC(sizeof(PointFormat), heap,
                                                             DYNAMIC_TYPE_TLSX);
    if (*point == NULL)
        return MEMORY_E;

    (*point)->format = format;
    (*point)->next = NULL;

    return 0;
}

static void TLSX_SupportedCurve_FreeAll(SupportedCurve* list, void* heap)
{
    SupportedCurve* curve;

    while ((curve = list)) {
        list = curve->next;
        XFREE(curve, heap, DYNAMIC_TYPE_TLSX);
    }
    (void)heap;
}

static void TLSX_PointFormat_FreeAll(PointFormat* list, void* heap)
{
    PointFormat* point;

    while ((point = list)) {
        list = point->next;
        XFREE(point, heap, DYNAMIC_TYPE_TLSX);
    }
    (void)heap;
}

static int TLSX_SupportedCurve_Append(SupportedCurve* list, word16 name,
                                                                     void* heap)
{
    int ret = BAD_FUNC_ARG;

    while (list) {
        if (list->name == name) {
            ret = 0; /* curve already in use */
            break;
        }

        if (list->next == NULL) {
            ret = TLSX_SupportedCurve_New(&list->next, name, heap);
            break;
        }

        list = list->next;
    }

    return ret;
}

static int TLSX_PointFormat_Append(PointFormat* list, byte format, void* heap)
{
    int ret = BAD_FUNC_ARG;

    while (list) {
        if (list->format == format) {
            ret = 0; /* format already in use */
            break;
        }

        if (list->next == NULL) {
            ret = TLSX_PointFormat_New(&list->next, format, heap);
            break;
        }

        list = list->next;
    }

    return ret;
}

#if defined(WOLFSSL_TLS13) || !defined(NO_WOLFSSL_CLIENT)

static void TLSX_SupportedCurve_ValidateRequest(WOLFSSL* ssl, byte* semaphore)
{
    word16 i;

    for (i = 0; i < ssl->suites->suiteSz; i+= 2) {
        if (ssl->suites->suites[i] == TLS13_BYTE)
            return;
        if (ssl->suites->suites[i] == ECC_BYTE ||
                ssl->suites->suites[i] == CHACHA_BYTE) {
        #if defined(HAVE_ECC) || defined(HAVE_CURVE25519) || \
                                                          defined(HAVE_CURVE448)
            return;
        #endif
        }
        else {
        #ifdef HAVE_FFDHE
            return;
        #endif
        }
    }

    /* turns semaphore on to avoid sending this extension. */
    TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_SUPPORTED_GROUPS));
}

static void TLSX_PointFormat_ValidateRequest(WOLFSSL* ssl, byte* semaphore)
{
    word16 i;

    for (i = 0; i < ssl->suites->suiteSz; i+= 2) {
        if (ssl->suites->suites[i] == TLS13_BYTE)
            return;
        if (ssl->suites->suites[i] == ECC_BYTE ||
                ssl->suites->suites[i] == CHACHA_BYTE) {
        #if defined(HAVE_ECC) || defined(HAVE_CURVE25519) || \
                                                          defined(HAVE_CURVE448)
            return;
        #endif
        }
    }
 #ifdef HAVE_FFDHE
        return;
 #endif
    /* turns semaphore on to avoid sending this extension. */
    TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_EC_POINT_FORMATS));
}

#endif /* WOLFSSL_TLS13 || !NO_WOLFSSL_CLIENT */

#ifndef NO_WOLFSSL_SERVER

static void TLSX_PointFormat_ValidateResponse(WOLFSSL* ssl, byte* semaphore)
{
#if defined(HAVE_FFDHE) || defined(HAVE_ECC) || defined(HAVE_CURVE25519) || \
                                                          defined(HAVE_CURVE448)
    (void)semaphore;
#endif

    if (ssl->options.cipherSuite0 == TLS13_BYTE)
        return;
    if (ssl->options.cipherSuite0 == ECC_BYTE ||
        ssl->options.cipherSuite0 == CHACHA_BYTE) {
#if defined(HAVE_ECC) || defined(HAVE_CURVE25519) || defined(HAVE_CURVE448)
        return;
#endif
    }
    else {
#ifdef HAVE_FFDHE
        return;
#endif
    }

#if !defined(HAVE_FFDHE) || (!defined(HAVE_ECC) && !defined(HAVE_CURVE25519) \
                                                     && !defined(HAVE_CURVE448))
    /* turns semaphore on to avoid sending this extension. */
    TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_EC_POINT_FORMATS));
#endif
}

#endif /* !NO_WOLFSSL_SERVER */

#ifndef NO_WOLFSSL_CLIENT

static word16 TLSX_SupportedCurve_GetSize(SupportedCurve* list)
{
    SupportedCurve* curve;
    word16 length = OPAQUE16_LEN; /* list length */

    while ((curve = list)) {
        list = curve->next;
        length += OPAQUE16_LEN; /* curve length */
    }

    return length;
}

#endif

static word16 TLSX_PointFormat_GetSize(PointFormat* list)
{
    PointFormat* point;
    word16 length = ENUM_LEN; /* list length */

    while ((point = list)) {
        list = point->next;
        length += ENUM_LEN; /* format length */
    }

    return length;
}

#ifndef NO_WOLFSSL_CLIENT

static word16 TLSX_SupportedCurve_Write(SupportedCurve* list, byte* output)
{
    word16 offset = OPAQUE16_LEN;

    while (list) {
        c16toa(list->name, output + offset);
        offset += OPAQUE16_LEN;
        list = list->next;
    }

    c16toa(offset - OPAQUE16_LEN, output); /* writing list length */

    return offset;
}

#endif

static word16 TLSX_PointFormat_Write(PointFormat* list, byte* output)
{
    word16 offset = ENUM_LEN;

    while (list) {
        output[offset++] = list->format;
        list = list->next;
    }

    output[0] = (byte)(offset - ENUM_LEN);

    return offset;
}

#if !defined(NO_WOLFSSL_SERVER) || (defined(WOLFSSL_TLS13) && \
                                         !defined(WOLFSSL_NO_SERVER_GROUPS_EXT))

static int TLSX_SupportedCurve_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                                                 byte isRequest)
{
    word16 offset;
    word16 name;
    int ret;

    if(!isRequest && !IsAtLeastTLSv1_3(ssl->version)) {
#ifdef WOLFSSL_ALLOW_SERVER_SC_EXT
        return 0;
#else
        return BUFFER_ERROR; /* servers doesn't send this extension. */
#endif
    }

    if (OPAQUE16_LEN > length || length % OPAQUE16_LEN)
        return BUFFER_ERROR;

    ato16(input, &offset);

    /* validating curve list length */
    if (length != OPAQUE16_LEN + offset)
        return BUFFER_ERROR;

    offset = OPAQUE16_LEN;
    if (offset == length)
        return 0;

#if defined(WOLFSSL_TLS13) && !defined(WOLFSSL_NO_SERVER_GROUPS_EXT)
    if (!isRequest) {
        TLSX* extension;
        SupportedCurve* curve;

        extension = TLSX_Find(ssl->extensions, TLSX_SUPPORTED_GROUPS);
        if (extension != NULL) {
            /* Replace client list with server list of supported groups. */
            curve = (SupportedCurve*)extension->data;
            extension->data = NULL;
            TLSX_SupportedCurve_FreeAll(curve, ssl->heap);

            ato16(input + offset, &name);
            offset += OPAQUE16_LEN;

            ret = TLSX_SupportedCurve_New(&curve, name, ssl->heap);
            if (ret != 0)
                return ret; /* throw error */
            extension->data = (void*)curve;
        }
    }
#endif

    for (; offset < length; offset += OPAQUE16_LEN) {
        ato16(input + offset, &name);

        ret = TLSX_UseSupportedCurve(&ssl->extensions, name, ssl->heap);
        if (ret != WOLFSSL_SUCCESS)
            return ret; /* throw error */
    }

    return 0;
}

#endif

#if !defined(NO_WOLFSSL_SERVER)

#if defined(WOLFSSL_TLS13) && !defined(WOLFSSL_NO_SERVER_GROUPS_EXT)

/* Checks the priority of the groups on the server and set the supported groups
 * response if there is a group not advertised by the client that is preferred.
 *
 * ssl  SSL/TLS object.
 * returns 0 on success, otherwise an error.
 */
int TLSX_SupportedCurve_CheckPriority(WOLFSSL* ssl)
{
    int ret;
    TLSX* extension;
    TLSX* priority = NULL;
    TLSX* ext = NULL;
    word16 name;
    SupportedCurve* curve;

    extension = TLSX_Find(ssl->extensions, TLSX_SUPPORTED_GROUPS);
    /* May be doing PSK with no key exchange. */
    if (extension == NULL)
        return 0;

    if ((ret = TLSX_PopulateSupportedGroups(ssl, &priority)) != WOLFSSL_SUCCESS)
        return ret;

    ext = TLSX_Find(priority, TLSX_SUPPORTED_GROUPS);
    curve = (SupportedCurve*)ext->data;
    name = curve->name;

    curve = (SupportedCurve*)extension->data;
    while (curve != NULL) {
        if (curve->name == name)
            break;
        curve = curve->next;
    }

    if (curve == NULL) {
        /* Couldn't find the preferred group in client list. */
        extension->resp = 1;

        /* Send server list back and free client list. */
        curve = (SupportedCurve*)extension->data;
        extension->data = ext->data;
        ext->data = curve;
    }

    TLSX_FreeAll(priority, ssl->heap);

    return 0;
}

#endif /* WOLFSSL_TLS13 && !WOLFSSL_NO_SERVER_GROUPS_EXT */

#if defined(HAVE_FFDHE) && !defined(WOLFSSL_NO_TLS12)
/* Set the highest priority common FFDHE group on the server as compared to
 * client extensions.
 *
 * ssl    SSL/TLS object.
 * returns 0 on success, otherwise an error.
 */
int TLSX_SupportedFFDHE_Set(WOLFSSL* ssl)
{
    int ret = 0;
    TLSX* extension;
    TLSX* priority = NULL;
    TLSX* ext = NULL;
    SupportedCurve* serverGroup;
    SupportedCurve* clientGroup;
    SupportedCurve* group;
    const DhParams* params = NULL;
    int found = 0;

    extension = TLSX_Find(ssl->extensions, TLSX_SUPPORTED_GROUPS);
    /* May be doing PSK with no key exchange. */
    if (extension == NULL)
        return 0;
    clientGroup = (SupportedCurve*)extension->data;
    for (group = clientGroup; group != NULL; group = group->next) {
        if (group->name >= MIN_FFHDE_GROUP && group->name <= MAX_FFHDE_GROUP) {
            found = 1;
            break;
        }
    }
    if (!found)
        return 0;

    if (ssl->buffers.serverDH_P.buffer && ssl->buffers.weOwnDH) {
        XFREE(ssl->buffers.serverDH_P.buffer, ssl->heap,
                                                       DYNAMIC_TYPE_PUBLIC_KEY);
    }
    if (ssl->buffers.serverDH_G.buffer && ssl->buffers.weOwnDH) {
        XFREE(ssl->buffers.serverDH_G.buffer, ssl->heap,
                                                       DYNAMIC_TYPE_PUBLIC_KEY);
    }
    ssl->buffers.serverDH_P.buffer = NULL;
    ssl->buffers.serverDH_G.buffer = NULL;
    ssl->buffers.weOwnDH = 0;
    ssl->options.haveDH = 0;


    if ((ret = TLSX_PopulateSupportedGroups(ssl, &priority)) != WOLFSSL_SUCCESS) {
        TLSX_FreeAll(priority, ssl->heap);
        return ret;
    }
    ret = 0;

    ext = TLSX_Find(priority, TLSX_SUPPORTED_GROUPS);
    serverGroup = (SupportedCurve*)ext->data;

    for (; serverGroup != NULL; serverGroup = serverGroup->next) {
        if ((serverGroup->name & NAMED_DH_MASK) != NAMED_DH_MASK)
            continue;

        for (group = clientGroup; group != NULL; group = group->next) {
            if (serverGroup->name != group->name)
                continue;

            switch (serverGroup->name) {
            #ifdef HAVE_FFDHE_2048
                case WOLFSSL_FFDHE_2048:
                    params = wc_Dh_ffdhe2048_Get();
                    break;
            #endif
            #ifdef HAVE_FFDHE_3072
                case WOLFSSL_FFDHE_3072:
                    params = wc_Dh_ffdhe3072_Get();
                    break;
            #endif
            #ifdef HAVE_FFDHE_4096
                case WOLFSSL_FFDHE_4096:
                    params = wc_Dh_ffdhe4096_Get();
                    break;
            #endif
            #ifdef HAVE_FFDHE_6144
                case WOLFSSL_FFDHE_6144:
                    params = wc_Dh_ffdhe6144_Get();
                    break;
            #endif
            #ifdef HAVE_FFDHE_8192
                case WOLFSSL_FFDHE_8192:
                    params = wc_Dh_ffdhe8192_Get();
                    break;
            #endif
            }
            if (params == NULL)
                return BAD_FUNC_ARG;
            if (params->p_len >= ssl->options.minDhKeySz &&
                                     params->p_len <= ssl->options.maxDhKeySz) {
                break;
            }
        }

        if (group != NULL && serverGroup->name == group->name)
            break;
    }

    if (serverGroup) {
        ssl->buffers.serverDH_P.buffer = (unsigned char *)params->p;
        ssl->buffers.serverDH_P.length = params->p_len;
        ssl->buffers.serverDH_G.buffer = (unsigned char *)params->g;
        ssl->buffers.serverDH_G.length = params->g_len;
        ssl->namedGroup = serverGroup->name;
    #if !defined(WOLFSSL_OLD_PRIME_CHECK) && \
        !defined(HAVE_FIPS) && !defined(HAVE_SELFTEST)
        ssl->options.dhDoKeyTest = 0;
    #endif
        ssl->options.haveDH = 1;
    }

    TLSX_FreeAll(priority, ssl->heap);

    return ret;
}
#endif /* HAVE_FFDHE && !WOLFSSL_NO_TLS12 */

#endif /* !NO_WOLFSSL_SERVER */

#if defined(WOLFSSL_TLS13) && !defined(WOLFSSL_NO_SERVER_GROUPS_EXT)
/* Return the preferred group.
 *
 * ssl             SSL/TLS object.
 * checkSupported  Whether to check for the first supported group.
 * returns BAD_FUNC_ARG if no group found, otherwise the group.
 */
int TLSX_SupportedCurve_Preferred(WOLFSSL* ssl, int checkSupported)
{
    TLSX* extension;
    SupportedCurve* curve;

    extension = TLSX_Find(ssl->extensions, TLSX_SUPPORTED_GROUPS);
    if (extension == NULL)
        return BAD_FUNC_ARG;

    curve = (SupportedCurve*)extension->data;
    while (curve != NULL) {
        if (!checkSupported || TLSX_KeyShare_IsSupported(curve->name))
            return curve->name;
        curve = curve->next;
    }

    return BAD_FUNC_ARG;
}

#endif /* HAVE_SUPPORTED_CURVES */

#ifndef NO_WOLFSSL_SERVER

static int TLSX_PointFormat_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                                                 byte isRequest)
{
    int ret;

    /* validating formats list length */
    if (ENUM_LEN > length || length != (word16)ENUM_LEN + input[0])
        return BUFFER_ERROR;

    if (isRequest) {
        /* adding uncompressed point format to response */
        ret = TLSX_UsePointFormat(&ssl->extensions, WOLFSSL_EC_PF_UNCOMPRESSED,
                                                                     ssl->heap);
        if (ret != WOLFSSL_SUCCESS)
            return ret; /* throw error */

        TLSX_SetResponse(ssl, TLSX_EC_POINT_FORMATS);
    }

    return 0;
}

#if defined(HAVE_ECC) || defined(HAVE_CURVE25519) || defined(HAVE_CURVE448)
int TLSX_ValidateSupportedCurves(WOLFSSL* ssl, byte first, byte second) {
    TLSX*           extension = NULL;
    SupportedCurve* curve     = NULL;
    word32          oid       = 0;
#if defined(HAVE_ECC) || defined(HAVE_CURVE25519) || defined(HAVE_ED25519) || \
                              defined(HAVE_CURVE448) || defined(HAVE_ED448) || \
                                (!defined(NO_RSA) && defined(WOLFSSL_STATIC_DH))
    word32          pkOid     = 0;
#endif /* HAVE_ECC || HAVE_ED25519 || HAVE_ED448 || (!NO_RSA && STATIC_DH) */
    word32          defOid    = 0;
    word32          defSz     = 80; /* Maximum known curve size is 66. */
    word32          nextOid   = 0;
    word32          nextSz    = 80; /* Maximum known curve size is 66. */
    word32          currOid   = ssl->ecdhCurveOID;
    int             ephmSuite = 0;
    word16          octets    = 0; /* according to 'ecc_set_type ecc_sets[];' */
    int             sig       = 0; /* validate signature */
    int             key       = 0; /* validate key       */

    (void)oid;
    (void)pkOid;

    if (first == CHACHA_BYTE) {
        switch (second) {
            case TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256:
            case TLS_PSK_WITH_CHACHA20_POLY1305_SHA256:
            case TLS_DHE_PSK_WITH_CHACHA20_POLY1305_SHA256:
            case TLS_DHE_RSA_WITH_CHACHA20_OLD_POLY1305_SHA256:
                return 1; /* no suite restriction */
            case TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256:
            case TLS_ECDHE_RSA_WITH_CHACHA20_OLD_POLY1305_SHA256:
            case TLS_ECDHE_PSK_WITH_CHACHA20_POLY1305_SHA256:
                break;
        }
    }
    if (first == ECC_BYTE || first == CHACHA_BYTE)
        extension = TLSX_Find(ssl->extensions, TLSX_SUPPORTED_GROUPS);
    if (!extension)
        return 1; /* no suite restriction */

    for (curve = (SupportedCurve*)extension->data;
         curve && !(sig && key);
         curve = curve->next) {

    #ifdef OPENSSL_EXTRA
        /* skip if name is not in supported ECC range */
        if (curve->name > WOLFSSL_ECC_X448)
            continue;
        /* skip if curve is disabled by user */
        if (ssl->ctx->disabledCurves & (1 << curve->name))
            continue;
    #endif

        /* find supported curve */
        switch (curve->name) {
#ifdef HAVE_ECC
    #if defined(HAVE_ECC160) || defined(HAVE_ALL_CURVES)
        #ifndef NO_ECC_SECP
            case WOLFSSL_ECC_SECP160R1:
                pkOid = oid = ECC_SECP160R1_OID;
                octets = 20;
                break;
        #endif /* !NO_ECC_SECP */
        #ifdef HAVE_ECC_SECPR2
            case WOLFSSL_ECC_SECP160R2:
                pkOid = oid = ECC_SECP160R2_OID;
                octets = 20;
                break;
        #endif /* HAVE_ECC_SECPR2 */
        #ifdef HAVE_ECC_KOBLITZ
            case WOLFSSL_ECC_SECP160K1:
                pkOid = oid = ECC_SECP160K1_OID;
                octets = 20;
                break;
        #endif /* HAVE_ECC_KOBLITZ */
    #endif
    #if defined(HAVE_ECC192) || defined(HAVE_ALL_CURVES)
        #ifndef NO_ECC_SECP
            case WOLFSSL_ECC_SECP192R1:
                pkOid = oid = ECC_SECP192R1_OID;
                octets = 24;
                break;
        #endif /* !NO_ECC_SECP */
        #ifdef HAVE_ECC_KOBLITZ
            case WOLFSSL_ECC_SECP192K1:
                pkOid = oid = ECC_SECP192K1_OID;
                octets = 24;
                break;
        #endif /* HAVE_ECC_KOBLITZ */
    #endif
    #if defined(HAVE_ECC224) || defined(HAVE_ALL_CURVES)
        #ifndef NO_ECC_SECP
            case WOLFSSL_ECC_SECP224R1:
                pkOid = oid = ECC_SECP224R1_OID;
                octets = 28;
                break;
        #endif /* !NO_ECC_SECP */
        #ifdef HAVE_ECC_KOBLITZ
            case WOLFSSL_ECC_SECP224K1:
                pkOid = oid = ECC_SECP224K1_OID;
                octets = 28;
                break;
        #endif /* HAVE_ECC_KOBLITZ */
    #endif
    #if !defined(NO_ECC256) || defined(HAVE_ALL_CURVES)
        #ifndef NO_ECC_SECP
            case WOLFSSL_ECC_SECP256R1:
                pkOid = oid = ECC_SECP256R1_OID;
                octets = 32;
                break;
        #endif /* !NO_ECC_SECP */
    #endif /* !NO_ECC256 || HAVE_ALL_CURVES */
#endif
        #if defined(HAVE_CURVE25519) || defined(HAVE_ED25519)
            case WOLFSSL_ECC_X25519:
                oid = ECC_X25519_OID;
            #ifdef HAVE_ED25519
                pkOid = ECC_ED25519_OID;
            #else
                pkOid = ECC_X25519_OID;
            #endif
                octets = 32;
                break;
        #endif /* HAVE_CURVE25519 */
#ifdef HAVE_ECC
    #if !defined(NO_ECC256) || defined(HAVE_ALL_CURVES)
        #ifdef HAVE_ECC_KOBLITZ
            case WOLFSSL_ECC_SECP256K1:
                pkOid = oid = ECC_SECP256K1_OID;
                octets = 32;
                break;
        #endif /* HAVE_ECC_KOBLITZ */
        #ifdef HAVE_ECC_BRAINPOOL
            case WOLFSSL_ECC_BRAINPOOLP256R1:
                pkOid = oid = ECC_BRAINPOOLP256R1_OID;
                octets = 32;
                break;
        #endif /* HAVE_ECC_BRAINPOOL */
    #endif
#endif
        #if defined(HAVE_CURVE448) || defined(HAVE_ED448)
            case WOLFSSL_ECC_X448:
                oid = ECC_X448_OID;
            #ifdef HAVE_ED448
                pkOid = ECC_ED448_OID;
            #else
                pkOid = ECC_X448_OID;
            #endif
                octets = 57;
                break;
        #endif /* HAVE_CURVE448 */
#ifdef HAVE_ECC
    #if defined(HAVE_ECC384) || defined(HAVE_ALL_CURVES)
        #ifndef NO_ECC_SECP
            case WOLFSSL_ECC_SECP384R1:
                pkOid = oid = ECC_SECP384R1_OID;
                octets = 48;
                break;
        #endif /* !NO_ECC_SECP */
        #ifdef HAVE_ECC_BRAINPOOL
            case WOLFSSL_ECC_BRAINPOOLP384R1:
                pkOid = oid = ECC_BRAINPOOLP384R1_OID;
                octets = 48;
                break;
        #endif /* HAVE_ECC_BRAINPOOL */
    #endif
    #if defined(HAVE_ECC512) || defined(HAVE_ALL_CURVES)
        #ifdef HAVE_ECC_BRAINPOOL
            case WOLFSSL_ECC_BRAINPOOLP512R1:
                pkOid = oid = ECC_BRAINPOOLP512R1_OID;
                octets = 64;
                break;
        #endif /* HAVE_ECC_BRAINPOOL */
    #endif
    #if defined(HAVE_ECC521) || defined(HAVE_ALL_CURVES)
        #ifndef NO_ECC_SECP
            case WOLFSSL_ECC_SECP521R1:
                pkOid = oid = ECC_SECP521R1_OID;
                octets = 66;
                break;
        #endif /* !NO_ECC_SECP */
    #endif
#endif
            default: continue; /* unsupported curve */
        }

    #ifdef HAVE_ECC
        /* Set default Oid */
        if (defOid == 0 && ssl->eccTempKeySz <= octets && defSz > octets) {
            defOid = oid;
            defSz = octets;
        }

        /* The eccTempKeySz is the preferred ephemeral key size */
        if (currOid == 0 && ssl->eccTempKeySz == octets)
            currOid = oid;
        if ((nextOid == 0 || nextSz > octets) && ssl->eccTempKeySz <= octets) {
            nextOid = oid;
            nextSz  = octets;
        }
    #else
        if (defOid == 0 && defSz > octets) {
            defOid = oid;
            defSz = octets;
        }

        if (currOid == 0)
            currOid = oid;
        if (nextOid == 0 || nextSz > octets) {
            nextOid = oid;
            nextSz  = octets;
        }
    #endif

        if (first == ECC_BYTE) {
            switch (second) {
#if defined(HAVE_ECC) || defined(HAVE_ED25519) || defined(HAVE_ED448)
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
                    sig |= ssl->pkCurveOID == pkOid;
                    key |= ssl->ecdhCurveOID == oid;
                    ephmSuite = 1;
                break;

    #ifdef WOLFSSL_STATIC_DH
                /* ECDH_ECDSA */
                case TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA:
                case TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA:
                case TLS_ECDH_ECDSA_WITH_RC4_128_SHA:
                case TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA:
                case TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA256:
                case TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA384:
                case TLS_ECDH_ECDSA_WITH_AES_128_GCM_SHA256:
                case TLS_ECDH_ECDSA_WITH_AES_256_GCM_SHA384:
                    if (oid == ECC_X25519_OID && defOid == oid) {
                        defOid = 0;
                        defSz = 80;
                    }
                    if (oid == ECC_X448_OID && defOid == oid) {
                        defOid = 0;
                        defSz = 80;
                    }
                    sig |= ssl->pkCurveOID == pkOid;
                    key |= ssl->pkCurveOID == oid;
                break;
    #endif /* WOLFSSL_STATIC_DH */
#endif /* HAVE_ECC || HAVE_ED25519 || HAVE_ED448 */
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
                    key |= ssl->ecdhCurveOID == oid;
                    ephmSuite = 1;
                break;

    #ifdef WOLFSSL_STATIC_DH
                /* ECDH_RSA */
                case TLS_ECDH_RSA_WITH_AES_256_CBC_SHA:
                case TLS_ECDH_RSA_WITH_AES_128_CBC_SHA:
                case TLS_ECDH_RSA_WITH_RC4_128_SHA:
                case TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA:
                case TLS_ECDH_RSA_WITH_AES_128_CBC_SHA256:
                case TLS_ECDH_RSA_WITH_AES_256_CBC_SHA384:
                case TLS_ECDH_RSA_WITH_AES_128_GCM_SHA256:
                case TLS_ECDH_RSA_WITH_AES_256_GCM_SHA384:
                    if (oid == ECC_X25519_OID && defOid == oid) {
                        defOid = 0;
                        defSz = 80;
                    }
                    if (oid == ECC_X448_OID && defOid == oid) {
                        defOid = 0;
                        defSz = 80;
                    }
                    sig = 1;
                    key |= ssl->pkCurveOID == pkOid;
                break;
    #endif /* WOLFSSL_STATIC_DH */
#endif
                default:
                    if (oid == ECC_X25519_OID && defOid == oid) {
                        defOid = 0;
                        defSz = 80;
                    }
                    if (oid == ECC_X448_OID && defOid == oid) {
                        defOid = 0;
                        defSz = 80;
                    }
                    if (oid != ECC_X25519_OID && oid != ECC_X448_OID) {
                        sig = 1;
                    }
                    key = 1;
                break;
            }
        }

        /* ChaCha20-Poly1305 ECC cipher suites */
        if (first == CHACHA_BYTE) {
            switch (second) {
#if defined(HAVE_ECC) || defined(HAVE_ED25519) || defined(HAVE_ED448)
                /* ECDHE_ECDSA */
                case TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 :
                case TLS_ECDHE_ECDSA_WITH_CHACHA20_OLD_POLY1305_SHA256 :
                    sig |= ssl->pkCurveOID == pkOid;
                    key |= ssl->ecdhCurveOID == oid;
                    ephmSuite = 1;
                break;
#endif /* HAVE_ECC || HAVE_ED25519 || HAVE_ED448 */
#ifndef NO_RSA
                /* ECDHE_RSA */
                case TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256 :
                case TLS_ECDHE_RSA_WITH_CHACHA20_OLD_POLY1305_SHA256 :
                    sig = 1;
                    key |= ssl->ecdhCurveOID == oid;
                    ephmSuite = 1;
                break;
#endif
                default:
                    sig = 1;
                    key = 1;
                break;
            }
        }
    }

    /* Choose the default if it is at the required strength. */
#ifdef HAVE_ECC
    if (ssl->ecdhCurveOID == 0 && defSz == ssl->eccTempKeySz)
#else
    if (ssl->ecdhCurveOID == 0)
#endif
    {
        key = 1;
        ssl->ecdhCurveOID = defOid;
    }
    /* Choose any curve at the required strength. */
    if (ssl->ecdhCurveOID == 0) {
        key = 1;
        ssl->ecdhCurveOID = currOid;
    }
    /* Choose the default if it is at the next highest strength. */
    if (ssl->ecdhCurveOID == 0 && defSz == nextSz)
        ssl->ecdhCurveOID = defOid;
    /* Choose any curve at the next highest strength. */
    if (ssl->ecdhCurveOID == 0)
        ssl->ecdhCurveOID = nextOid;
    /* No curve and ephemeral ECC suite requires a matching curve. */
    if (ssl->ecdhCurveOID == 0 && ephmSuite)
        key = 0;

    return sig && key;
}
#endif

#endif /* NO_WOLFSSL_SERVER */

int TLSX_UseSupportedCurve(TLSX** extensions, word16 name, void* heap)
{
    TLSX* extension = NULL;
    SupportedCurve* curve = NULL;
    int ret;

    if (extensions == NULL)
        return BAD_FUNC_ARG;

    extension = TLSX_Find(*extensions, TLSX_SUPPORTED_GROUPS);

    if (!extension) {
        ret = TLSX_SupportedCurve_New(&curve, name, heap);
        if (ret != 0)
            return ret;

        ret = TLSX_Push(extensions, TLSX_SUPPORTED_GROUPS, curve, heap);
        if (ret != 0) {
            XFREE(curve, heap, DYNAMIC_TYPE_TLSX);
            return ret;
        }
    }
    else {
        ret = TLSX_SupportedCurve_Append((SupportedCurve*)extension->data, name,
                                                                          heap);
        if (ret != 0)
            return ret;
    }

    return WOLFSSL_SUCCESS;
}

int TLSX_UsePointFormat(TLSX** extensions, byte format, void* heap)
{
    TLSX* extension = NULL;
    PointFormat* point = NULL;
    int ret = 0;

    if (extensions == NULL)
        return BAD_FUNC_ARG;

    extension = TLSX_Find(*extensions, TLSX_EC_POINT_FORMATS);

    if (!extension) {
        ret = TLSX_PointFormat_New(&point, format, heap);
        if (ret != 0)
            return ret;

        ret = TLSX_Push(extensions, TLSX_EC_POINT_FORMATS, point, heap);
        if (ret != 0) {
            XFREE(point, heap, DYNAMIC_TYPE_TLSX);
            return ret;
        }
    }
    else {
        ret = TLSX_PointFormat_Append((PointFormat*)extension->data, format,
                                                                          heap);
        if (ret != 0)
            return ret;
    }

    return WOLFSSL_SUCCESS;
}

#define EC_FREE_ALL         TLSX_SupportedCurve_FreeAll
#define EC_VALIDATE_REQUEST TLSX_SupportedCurve_ValidateRequest

#ifndef NO_WOLFSSL_CLIENT
#define EC_GET_SIZE TLSX_SupportedCurve_GetSize
#define EC_WRITE    TLSX_SupportedCurve_Write
#else
#define EC_GET_SIZE(list)         0
#define EC_WRITE(a, b)            0
#endif

#if !defined(NO_WOLFSSL_SERVER) || (defined(WOLFSSL_TLS13) && \
                                         !defined(WOLFSSL_NO_SERVER_GROUPS_EXT))
#define EC_PARSE TLSX_SupportedCurve_Parse
#else
#define EC_PARSE(a, b, c, d)      0
#endif

#define PF_FREE_ALL          TLSX_PointFormat_FreeAll
#define PF_VALIDATE_REQUEST  TLSX_PointFormat_ValidateRequest
#define PF_VALIDATE_RESPONSE TLSX_PointFormat_ValidateResponse

#define PF_GET_SIZE TLSX_PointFormat_GetSize
#define PF_WRITE    TLSX_PointFormat_Write

#ifndef NO_WOLFSSL_SERVER
#define PF_PARSE TLSX_PointFormat_Parse
#else
#define PF_PARSE(a, b, c, d)      0
#endif

#else

#define EC_FREE_ALL(list, heap)
#define EC_GET_SIZE(list)         0
#define EC_WRITE(a, b)            0
#define EC_PARSE(a, b, c, d)      0
#define EC_VALIDATE_REQUEST(a, b)

#define PF_FREE_ALL(list, heap)
#define PF_GET_SIZE(list)         0
#define PF_WRITE(a, b)            0
#define PF_PARSE(a, b, c, d)      0
#define PF_VALIDATE_REQUEST(a, b)
#define PF_VALIDATE_RESPONSE(a, b)

#endif /* HAVE_SUPPORTED_CURVES */

/******************************************************************************/
/* Renegotiation Indication                                                   */
/******************************************************************************/

#if defined(HAVE_SECURE_RENEGOTIATION) \
 || defined(HAVE_SERVER_RENEGOTIATION_INFO)

static byte TLSX_SecureRenegotiation_GetSize(SecureRenegotiation* data,
                                                                  int isRequest)
{
    byte length = OPAQUE8_LEN; /* empty info length */

    /* data will be NULL for HAVE_SERVER_RENEGOTIATION_INFO only */
    if (data && data->enabled && data->verifySet) {
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
    if (data && data->enabled && data->verifySet) {
        /* client sends client_verify_data only */
        XMEMCPY(output + offset, data->client_verify_data, TLS_FINISHED_SZ);
        offset += TLS_FINISHED_SZ;

        /* server also sends server_verify_data */
        if (!isRequest) {
            XMEMCPY(output + offset, data->server_verify_data, TLS_FINISHED_SZ);
            offset += TLS_FINISHED_SZ;
        }
    }

    output[0] = (byte)(offset - 1);  /* info length - self */

    return offset;
}

static int TLSX_SecureRenegotiation_Parse(WOLFSSL* ssl, byte* input,
                                                  word16 length, byte isRequest)
{
    int ret = SECURE_RENEGOTIATION_E;

    if (length >= OPAQUE8_LEN) {
        if (isRequest) {
        #ifndef NO_WOLFSSL_SERVER
            if (ssl->secure_renegotiation == NULL) {
                ret = wolfSSL_UseSecureRenegotiation(ssl);
                if (ret == WOLFSSL_SUCCESS)
                    ret = 0;
            }
            if (ret != 0 && ret != SECURE_RENEGOTIATION_E) {
            }
            else if (!ssl->secure_renegotiation->enabled) {
                if (*input == 0) {
                    input++; /* get past size */

                    ssl->secure_renegotiation->enabled = 1;
                    TLSX_SetResponse(ssl, TLSX_RENEGOTIATION_INFO);
                    ret = 0;
                }
                else {
                    /* already in error state */
                    WOLFSSL_MSG("SCR client verify data present");
                }
            }
            else if (*input == TLS_FINISHED_SZ) {
                if (length < TLS_FINISHED_SZ + 1) {
                    WOLFSSL_MSG("SCR malformed buffer");
                    ret = BUFFER_E;
                }
                else {
                    input++; /* get past size */

                    /* validate client verify data */
                    if (XMEMCMP(input,
                            ssl->secure_renegotiation->client_verify_data,
                            TLS_FINISHED_SZ) == 0) {
                        WOLFSSL_MSG("SCR client verify data match");
                        TLSX_SetResponse(ssl, TLSX_RENEGOTIATION_INFO);
                        ret = 0;  /* verified */
                    } else {
                        /* already in error state */
                        WOLFSSL_MSG("SCR client verify data Failure");
                    }
                }
            }
        #endif
        }
        else if (ssl->secure_renegotiation != NULL) {
        #ifndef NO_WOLFSSL_CLIENT
            if (!ssl->secure_renegotiation->enabled) {
                if (*input == 0) {
                    ssl->secure_renegotiation->enabled = 1;
                    ret = 0;
                }
            }
            else if (*input == 2 * TLS_FINISHED_SZ &&
                     length == 2 * TLS_FINISHED_SZ + OPAQUE8_LEN) {
                input++;  /* get past size */

                /* validate client and server verify data */
                if (XMEMCMP(input,
                            ssl->secure_renegotiation->client_verify_data,
                            TLS_FINISHED_SZ) == 0 &&
                    XMEMCMP(input + TLS_FINISHED_SZ,
                            ssl->secure_renegotiation->server_verify_data,
                            TLS_FINISHED_SZ) == 0) {
                    WOLFSSL_MSG("SCR client and server verify data match");
                    ret = 0;  /* verified */
                } else {
                    /* already in error state */
                    WOLFSSL_MSG("SCR client and server verify data Failure");
                }
            }
        #endif
        }
    }

    if (ret != 0) {
        SendAlert(ssl, alert_fatal, handshake_failure);
    }

    return ret;
}

int TLSX_UseSecureRenegotiation(TLSX** extensions, void* heap)
{
    int ret = 0;
    SecureRenegotiation* data;

    data = (SecureRenegotiation*)XMALLOC(sizeof(SecureRenegotiation), heap,
                                                             DYNAMIC_TYPE_TLSX);
    if (data == NULL)
        return MEMORY_E;

    XMEMSET(data, 0, sizeof(SecureRenegotiation));

    ret = TLSX_Push(extensions, TLSX_RENEGOTIATION_INFO, data, heap);
    if (ret != 0) {
        XFREE(data, heap, DYNAMIC_TYPE_TLSX);
        return ret;
    }

    return WOLFSSL_SUCCESS;
}

#ifdef HAVE_SERVER_RENEGOTIATION_INFO

int TLSX_AddEmptyRenegotiationInfo(TLSX** extensions, void* heap)
{
    int ret;

    /* send empty renegotiation_info extension */
    TLSX* ext = TLSX_Find(*extensions, TLSX_RENEGOTIATION_INFO);
    if (ext == NULL) {
        ret = TLSX_UseSecureRenegotiation(extensions, heap);
        if (ret != WOLFSSL_SUCCESS)
            return ret;

        ext = TLSX_Find(*extensions, TLSX_RENEGOTIATION_INFO);
    }
    if (ext)
        ext->resp = 1;

    return WOLFSSL_SUCCESS;
}

#endif /* HAVE_SERVER_RENEGOTIATION_INFO */


#define SCR_FREE_ALL(data, heap) XFREE(data, (heap), DYNAMIC_TYPE_TLSX)
#define SCR_GET_SIZE       TLSX_SecureRenegotiation_GetSize
#define SCR_WRITE          TLSX_SecureRenegotiation_Write
#define SCR_PARSE          TLSX_SecureRenegotiation_Parse

#else

#define SCR_FREE_ALL(a, heap)
#define SCR_GET_SIZE(a, b)    0
#define SCR_WRITE(a, b, c)    0
#define SCR_PARSE(a, b, c, d) 0

#endif /* HAVE_SECURE_RENEGOTIATION */

/******************************************************************************/
/* Session Tickets                                                            */
/******************************************************************************/

#ifdef HAVE_SESSION_TICKET

#if defined(WOLFSSL_TLS13) || !defined(NO_WOLFSSL_CLIENT)
static void TLSX_SessionTicket_ValidateRequest(WOLFSSL* ssl)
{
    TLSX*          extension = TLSX_Find(ssl->extensions, TLSX_SESSION_TICKET);
    SessionTicket* ticket    = extension ?
                                         (SessionTicket*)extension->data : NULL;

    if (ticket) {
        /* TODO validate ticket timeout here! */
        if (ticket->lifetime == 0xfffffff) {
            /* send empty ticket on timeout */
            TLSX_UseSessionTicket(&ssl->extensions, NULL, ssl->heap);
        }
    }
}
#endif /* WLFSSL_TLS13 || !NO_WOLFSSL_CLIENT */


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

    (void) input; /* avoid unused parameter if NO_WOLFSSL_SERVER defined */

    if (!isRequest) {
        if (TLSX_CheckUnsupportedExtension(ssl, TLSX_SESSION_TICKET))
            return TLSX_HandleUnsupportedExtension(ssl);

        if (length != 0)
            return BUFFER_ERROR;

#ifndef NO_WOLFSSL_CLIENT
        ssl->expect_session_ticket = 1;
#endif
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
            ret = TLSX_UseSessionTicket(&ssl->extensions, NULL, ssl->heap);
            if (ret == WOLFSSL_SUCCESS) {
                ret = 0;
                TLSX_SetResponse(ssl, TLSX_SESSION_TICKET);  /* send blank ticket */
                ssl->options.createTicket = 1;  /* will send ticket msg */
                ssl->options.useTicket    = 1;
                ssl->options.resuming     = 0;  /* no standard resumption */
                ssl->arrays->sessionIDSz  = 0;  /* no echo on blank ticket */
            }
        } else {
            /* got actual ticket from client */
            ret = DoClientTicket(ssl, input, length);
            if (ret == WOLFSSL_TICKET_RET_OK) {    /* use ticket to resume */
                WOLFSSL_MSG("Using existing client ticket");
                ssl->options.useTicket = 1;
                ssl->options.resuming  = 1;
            } else if (ret == WOLFSSL_TICKET_RET_CREATE) {
                WOLFSSL_MSG("Using existing client ticket, creating new one");
                ret = TLSX_UseSessionTicket(&ssl->extensions, NULL, ssl->heap);
                if (ret == WOLFSSL_SUCCESS) {
                    ret = 0;
                    TLSX_SetResponse(ssl, TLSX_SESSION_TICKET);
                                                    /* send blank ticket */
                    ssl->options.createTicket = 1;  /* will send ticket msg */
                    ssl->options.useTicket    = 1;
                    ssl->options.resuming     = 1;
                }
            } else if (ret == WOLFSSL_TICKET_RET_REJECT) {
                WOLFSSL_MSG("Process client ticket rejected, not using");
                ssl->options.rejectTicket = 1;
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
                                            byte* data, word16 size, void* heap)
{
    SessionTicket* ticket = (SessionTicket*)XMALLOC(sizeof(SessionTicket),
                                                       heap, DYNAMIC_TYPE_TLSX);
    if (ticket) {
        ticket->data = (byte*)XMALLOC(size, heap, DYNAMIC_TYPE_TLSX);
        if (ticket->data == NULL) {
            XFREE(ticket, heap, DYNAMIC_TYPE_TLSX);
            return NULL;
        }

        XMEMCPY(ticket->data, data, size);
        ticket->size     = size;
        ticket->lifetime = lifetime;
    }

    (void)heap;

    return ticket;
}
WOLFSSL_LOCAL void TLSX_SessionTicket_Free(SessionTicket* ticket, void* heap)
{
    if (ticket) {
        XFREE(ticket->data, heap, DYNAMIC_TYPE_TLSX);
        XFREE(ticket,       heap, DYNAMIC_TYPE_TLSX);
    }

    (void)heap;
}

int TLSX_UseSessionTicket(TLSX** extensions, SessionTicket* ticket, void* heap)
{
    int ret = 0;

    if (extensions == NULL)
        return BAD_FUNC_ARG;

    /* If the ticket is NULL, the client will request a new ticket from the
       server. Otherwise, the client will use it in the next client hello. */
    if ((ret = TLSX_Push(extensions, TLSX_SESSION_TICKET, (void*)ticket, heap))
                                                                           != 0)
        return ret;

    return WOLFSSL_SUCCESS;
}

#define WOLF_STK_VALIDATE_REQUEST TLSX_SessionTicket_ValidateRequest
#define WOLF_STK_GET_SIZE         TLSX_SessionTicket_GetSize
#define WOLF_STK_WRITE            TLSX_SessionTicket_Write
#define WOLF_STK_PARSE            TLSX_SessionTicket_Parse
#define WOLF_STK_FREE(stk, heap)  TLSX_SessionTicket_Free((SessionTicket*)stk,(heap))

#else

#define WOLF_STK_FREE(a, b)
#define WOLF_STK_VALIDATE_REQUEST(a)
#define WOLF_STK_GET_SIZE(a, b)      0
#define WOLF_STK_WRITE(a, b, c)      0
#define WOLF_STK_PARSE(a, b, c, d)   0

#endif /* HAVE_SESSION_TICKET */

/******************************************************************************/
/* Quantum-Safe-Hybrid                                                        */
/******************************************************************************/

#ifdef HAVE_QSH
#if defined(HAVE_NTRU)
static WC_RNG* gRng;
static wolfSSL_Mutex* gRngMutex;
#endif

static void TLSX_QSH_FreeAll(QSHScheme* list, void* heap)
{
    QSHScheme* current;

    while ((current = list)) {
        list = current->next;
        XFREE(current, heap, DYNAMIC_TYPE_TLSX);
    }

    (void)heap;
}

static int TLSX_QSH_Append(QSHScheme** list, word16 name, byte* pub,
                                                                  word16 pubLen)
{
    QSHScheme* temp;

    if (list == NULL)
        return BAD_FUNC_ARG;

    if ((temp = (QSHScheme*)XMALLOC(sizeof(QSHScheme), NULL,
                                                    DYNAMIC_TYPE_TLSX)) == NULL)
        return MEMORY_E;

    temp->name  = name;
    temp->PK    = pub;
    temp->PKLen = pubLen;
    temp->next  = *list;

    *list = temp;

    return 0;
}


/* request for server's public key : 02 indicates 0-2 requested */
static byte TLSX_QSH_SerPKReq(byte* output, byte isRequest)
{
    if (isRequest) {
        /* only request one public key from the server */
        output[0] = 0x01;

        return OPAQUE8_LEN;
    }
    else {
        return 0;
    }
}

#ifndef NO_WOLFSSL_CLIENT

/* check for TLS_QSH suite */
static void TLSX_QSH_ValidateRequest(WOLFSSL* ssl, byte* semaphore)
{
    int i;

    for (i = 0; i < ssl->suites->suiteSz; i+= 2)
        if (ssl->suites->suites[i] == QSH_BYTE)
            return;

    /* No QSH suite found */
    TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_QUANTUM_SAFE_HYBRID));
}


/* return the size of the QSH hello extension
   list      the list of QSHScheme structs containing id and key
   isRequest if 1 then is being sent to the server
 */
word16 TLSX_QSH_GetSize(QSHScheme* list, byte isRequest)
{
    QSHScheme* temp = list;
    word16 length = 0;

    /* account for size of scheme list and public key list */
    if (isRequest)
        length = OPAQUE16_LEN;
    length += OPAQUE24_LEN;

    /* for each non null element in list add size */
    while ((temp)) {
        /* add public key info Scheme | Key Length | Key */
        length += OPAQUE16_LEN;
        length += OPAQUE16_LEN;
        length += temp->PKLen;

        /* if client add name size for scheme list
           advance to next QSHScheme struct in list */
        if (isRequest)
            length += OPAQUE16_LEN;
        temp = temp->next;
    }

    /* add length for request server public keys */
    if (isRequest)
        length += OPAQUE8_LEN;

    return length;
}


/* write out a list of QSHScheme IDs */
static word16 TLSX_QSH_Write(QSHScheme* list, byte* output)
{
    QSHScheme* current = list;
    word16 length      = 0;

    length += OPAQUE16_LEN;

    while (current) {
        c16toa(current->name, output + length);
        length += OPAQUE16_LEN;
        current = (QSHScheme*)current->next;
    }

    c16toa(length - OPAQUE16_LEN, output); /* writing list length */

    return length;
}


/* write public key list in extension */
static word16 TLSX_QSHPK_WriteR(QSHScheme* format, byte* output)
{
    word32 offset = 0;
    word16 public_len = 0;

    if (!format)
        return offset;

    /* write scheme ID */
    c16toa(format->name, output + offset);
    offset += OPAQUE16_LEN;

    /* write public key matching scheme */
    public_len = format->PKLen;
    c16toa(public_len, output + offset);
    offset += OPAQUE16_LEN;
    if (format->PK) {
        XMEMCPY(output+offset, format->PK, public_len);
    }

    return public_len + offset;
}

word16 TLSX_QSHPK_Write(QSHScheme* list, byte* output)
{
    QSHScheme* current = list;
    word32 length = 0;
    word24 toWire;

    length += OPAQUE24_LEN;

    while (current) {
        length += TLSX_QSHPK_WriteR(current, output + length);
        current = (QSHScheme*)current->next;
    }
    /* length of public keys sent */
    c32to24(length - OPAQUE24_LEN, toWire);
    output[0] = toWire[0];
    output[1] = toWire[1];
    output[2] = toWire[2];

    return length;
}

#endif /* NO_WOLFSSL_CLIENT */
#ifndef NO_WOLFSSL_SERVER

static void TLSX_QSHAgreement(TLSX** extensions, void* heap)
{
    TLSX* extension = TLSX_Find(*extensions, TLSX_QUANTUM_SAFE_HYBRID);
    QSHScheme* format = NULL;
    QSHScheme* del    = NULL;
    QSHScheme* prev   = NULL;

    if (extension == NULL)
        return;

    format = (QSHScheme*)extension->data;
    while (format) {
        if (format->PKLen == 0) {
            /* case of head */
            if (format == extension->data) {
                extension->data = format->next;
            }
            if (prev)
                prev->next = format->next;
            del = format;
            format = format->next;
            XFREE(del, heap, DYNAMIC_TYPE_TMP_BUFFER);
            del = NULL;
        } else {
            prev   = format;
            format = format->next;
        }
    }

    (void)heap;
}


/* Parse in hello extension
   input     the byte stream to process
   length    length of total extension found
   isRequest set to 1 if being sent to the server
 */
static int TLSX_QSH_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                                                 byte isRequest)
{
    byte   numKeys    = 0;
    word16 offset     = 0;
    word16 schemSz    = 0;
    word16 offset_len = 0;
    word32 offset_pk  = 0;
    word16 name  = 0;
    word16 PKLen = 0;
    byte*  PK = NULL;
    int r;


    if (OPAQUE16_LEN > length)
        return BUFFER_ERROR;

    if (isRequest) {
        ato16(input, &schemSz);

        /* list of public keys available for QSH schemes */
        offset_len = schemSz + OPAQUE16_LEN;
    }

    offset_pk = ((input[offset_len] << 16)   & 0xFF00000) |
                (((input[offset_len + 1]) << 8) & 0xFF00) |
                (input[offset_len + 2] & 0xFF);
    offset_len += OPAQUE24_LEN;

    /* check buffer size */
    if (offset_pk > length)
        return BUFFER_ERROR;

    /* set maximum number of keys the client will accept */
    if (!isRequest)
        numKeys = (ssl->maxRequest < 1)? 1 : ssl->maxRequest;

    /* hello extension read list of scheme ids */
    if (isRequest) {

        /* read in request for public keys */
        ssl->minRequest = (input[length -1] >> 4) & 0xFF;
        ssl->maxRequest = input[length -1] & 0x0F;

        /* choose the min between min requested by client and 1 */
        numKeys = (ssl->minRequest > 1) ? ssl->minRequest : 1;

        if (ssl->minRequest > ssl->maxRequest)
            return BAD_FUNC_ARG;

        offset  += OPAQUE16_LEN;
        schemSz += offset;

        /* check buffer size */
        if (schemSz > length)
            return BUFFER_ERROR;

        while ((offset < schemSz) && numKeys) {
            /* Scheme ID list */
            ato16(input + offset, &name);
            offset += OPAQUE16_LEN;

            /* validate we have scheme id */
            if (ssl->user_set_QSHSchemes &&
                    !TLSX_ValidateQSHScheme(&ssl->extensions, name)) {
                continue;
            }

            /* server create keys on demand */
            if ((r = TLSX_CreateNtruKey(ssl, name)) != 0) {
                WOLFSSL_MSG("Error creating ntru keys");
                return r;
            }

            /* peer sent an agreed upon scheme */
            r = TLSX_UseQSHScheme(&ssl->extensions, name, NULL, 0, ssl->heap);

            if (r != WOLFSSL_SUCCESS) return r; /* throw error */

            numKeys--;
        }

        /* choose the min between min requested by client and 1 */
        numKeys = (ssl->minRequest > 1) ? ssl->minRequest : 1;
    }

    /* QSHPK struct */
    offset_pk += offset_len;
    while ((offset_len < offset_pk) && numKeys) {
        QSHKey * temp;

        if ((temp = (QSHKey*)XMALLOC(sizeof(QSHKey), ssl->heap,
                                                    DYNAMIC_TYPE_TLSX)) == NULL)
            return MEMORY_E;

        /* initialize */
        temp->next = NULL;
        temp->pub.buffer = NULL;
        temp->pub.length = 0;
        temp->pri.buffer = NULL;
        temp->pri.length = 0;

        /* scheme id */
        ato16(input + offset_len, &(temp->name));
        offset_len += OPAQUE16_LEN;

        /* public key length */
        ato16(input + offset_len, &PKLen);
        temp->pub.length = PKLen;
        offset_len += OPAQUE16_LEN;


        if (isRequest) {
            /* validate we have scheme id */
            if (ssl->user_set_QSHSchemes &&
                    (!TLSX_ValidateQSHScheme(&ssl->extensions, temp->name))) {
                offset_len += PKLen;
                XFREE(temp, ssl->heap, DYNAMIC_TYPE_TLSX);
                continue;
            }
        }

        /* read in public key */
        if (PKLen > 0) {
            temp->pub.buffer = (byte*)XMALLOC(temp->pub.length,
                                            ssl->heap, DYNAMIC_TYPE_PUBLIC_KEY);
            XMEMCPY(temp->pub.buffer, input + offset_len, temp->pub.length);
            offset_len += PKLen;
        }
        else {
            PK = NULL;
        }

        /* use own key when adding to extensions list for sending reply */
        PKLen = 0;
        PK = TLSX_QSHKeyFind_Pub(ssl->QSH_Key, &PKLen, temp->name);
        r  = TLSX_UseQSHScheme(&ssl->extensions, temp->name, PK, PKLen,
                                                                     ssl->heap);

        /* store peers key */
        ssl->peerQSHKeyPresent = 1;
        if (TLSX_AddQSHKey(&ssl->peerQSHKey, temp) != 0)
            return MEMORY_E;

        if (temp->pub.length == 0) {
            XFREE(temp, ssl->heap, DYNAMIC_TYPE_TLSX);
        }

        if (r != WOLFSSL_SUCCESS) {return r;} /* throw error */

        numKeys--;
    }

    /* reply to a QSH extension sent from client */
    if (isRequest) {
        TLSX_SetResponse(ssl, TLSX_QUANTUM_SAFE_HYBRID);
        /* only use schemes we have key generated for -- free the rest */
        TLSX_QSHAgreement(&ssl->extensions, ssl->heap);
    }

    return 0;
}


/* Used for parsing in QSHCipher structs on Key Exchange */
int TLSX_QSHCipher_Parse(WOLFSSL* ssl, const byte* input, word16 length,
                                                                  byte isServer)
{
    QSHKey* key;
    word16 Max_Secret_Len = 48;
    word16 offset     = 0;
    word16 offset_len = 0;
    word32 offset_pk  = 0;
    word16 name       = 0;
    word16 secretLen  = 0;
    byte*  secret     = NULL;
    word16 buffLen    = 0;
    byte buff[145]; /* size enough for 3 secrets */
    buffer* buf;

    /* pointer to location where secret should be stored */
    if (isServer) {
        buf = ssl->QSH_secret->CliSi;
    }
    else {
        buf = ssl->QSH_secret->SerSi;
    }

    offset_pk = ((input[offset_len] << 16)    & 0xFF0000) |
                (((input[offset_len + 1]) << 8) & 0xFF00) |
                (input[offset_len + 2] & 0xFF);
    offset_len += OPAQUE24_LEN;

    /* validating extension list length -- check if trying to read over edge
       of buffer */
    if (length < (offset_pk + OPAQUE24_LEN)) {
        return BUFFER_ERROR;
    }

    /* QSHCipherList struct */
    offset_pk += offset_len;
    while (offset_len < offset_pk) {

        /* scheme id */
        ato16(input + offset_len, &name);
        offset_len += OPAQUE16_LEN;

        /* public key length */
        ato16(input + offset_len, &secretLen);
        offset_len += OPAQUE16_LEN;

        /* read in public key */
        if (secretLen > 0) {
            secret = (byte*)(input + offset_len);
            offset_len += secretLen;
        }
        else {
            secret = NULL;
        }

        /* no secret sent */
        if (secret == NULL)
            continue;

        /* find corresponding key */
        key = ssl->QSH_Key;
        while (key) {
            if (key->name == name)
                break;
            else
                key = (QSHKey*)key->next;
        }

        /* if we do not have the key than there was a big issue negotiation */
        if (key == NULL) {
            WOLFSSL_MSG("key was null for decryption!!!\n");
            return MEMORY_E;
        }

        /* Decrypt sent secret */
        buffLen = Max_Secret_Len;
        QSH_Decrypt(key, secret, secretLen, buff + offset, &buffLen);
        offset += buffLen;
    }

    /* allocate memory for buffer */
    buf->length = offset;
    buf->buffer = (byte*)XMALLOC(offset, ssl->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (buf->buffer == NULL)
        return MEMORY_E;

    /* store secrets */
    XMEMCPY(buf->buffer, buff, offset);
    ForceZero(buff, offset);

    return offset_len;
}


/* return 1 on success */
int TLSX_ValidateQSHScheme(TLSX** extensions, word16 theirs) {
    TLSX* extension = TLSX_Find(*extensions, TLSX_QUANTUM_SAFE_HYBRID);
    QSHScheme* format    = NULL;

    /* if no extension is sent then do not use QSH */
    if (!extension) {
        WOLFSSL_MSG("No QSH Extension");
        return 0;
    }

    for (format = (QSHScheme*)extension->data; format; format = format->next) {
        if (format->name == theirs) {
            WOLFSSL_MSG("Found Matching QSH Scheme");
            return 1; /* have QSH */
        }
    }

    return 0;
}
#endif /* NO_WOLFSSL_SERVER */

/* test if the QSH Scheme is implemented
   return 1 if yes 0 if no */
static int TLSX_HaveQSHScheme(word16 name)
{
    switch(name) {
        #ifdef HAVE_NTRU
            case WOLFSSL_NTRU_EESS439:
            case WOLFSSL_NTRU_EESS593:
            case WOLFSSL_NTRU_EESS743:
                    return 1;
        #endif
            case WOLFSSL_LWE_XXX:
            case WOLFSSL_HFE_XXX:
                    return 0; /* not supported yet */

        default:
            return 0;
    }
}


/* Add a QSHScheme struct to list of usable ones */
int TLSX_UseQSHScheme(TLSX** extensions, word16 name, byte* pKey, word16 pkeySz,
                                                                     void* heap)
{
    TLSX*      extension = NULL;
    QSHScheme* format    = NULL;
    int        ret       = 0;

    /* sanity check */
    if (extensions == NULL || (pKey == NULL && pkeySz != 0))
        return BAD_FUNC_ARG;

    extension = TLSX_Find(*extensions, TLSX_QUANTUM_SAFE_HYBRID);

    /* if scheme is implemented than add */
    if (TLSX_HaveQSHScheme(name)) {
        if ((ret = TLSX_QSH_Append(&format, name, pKey, pkeySz)) != 0)
            return ret;

        extension = TLSX_Find(*extensions, TLSX_QUANTUM_SAFE_HYBRID);
        if (!extension) {
            if ((ret = TLSX_Push(extensions, TLSX_QUANTUM_SAFE_HYBRID, format,
                                                                  heap)) != 0) {
                XFREE(format, 0, DYNAMIC_TYPE_TLSX);
                return ret;
            }
        }
        else {
            /* push new QSH object to extension data. */
            format->next = (QSHScheme*)extension->data;
            extension->data = (void*)format;

            /* look for another format of the same name to remove (replacement) */
            do {
                if (format->next && (format->next->name == name)) {
                    QSHScheme* next = format->next;

                    format->next = next->next;
                    XFREE(next, 0, DYNAMIC_TYPE_TLSX);

                    break;
                }
            } while ((format = format->next));
        }
    }
    return WOLFSSL_SUCCESS;
}

#define QSH_FREE_ALL         TLSX_QSH_FreeAll
#define QSH_VALIDATE_REQUEST TLSX_QSH_ValidateRequest

#ifndef NO_WOLFSSL_CLIENT
#define QSH_GET_SIZE TLSX_QSH_GetSize
#define QSH_WRITE    TLSX_QSH_Write
#else
#define QSH_GET_SIZE(list, a)      0
#define QSH_WRITE(a, b)            0
#endif

#ifndef NO_WOLFSSL_SERVER
#define QSH_PARSE TLSX_QSH_Parse
#else
#define QSH_PARSE(a, b, c, d)      0
#endif

#define QSHPK_WRITE TLSX_QSHPK_Write
#define QSH_SERREQ TLSX_QSH_SerPKReq
#else

#define QSH_FREE_ALL(list, heap)
#define QSH_GET_SIZE(list, a)      0
#define QSH_WRITE(a, b)            0
#define QSH_PARSE(a, b, c, d)      0
#define QSHPK_WRITE(a, b)          0
#define QSH_SERREQ(a, b)           0
#define QSH_VALIDATE_REQUEST(a, b)

#endif /* HAVE_QSH */

#if defined(HAVE_ENCRYPT_THEN_MAC) && !defined(WOLFSSL_AEAD_ONLY)
/******************************************************************************/
/* Encrypt-then-MAC                                                           */
/******************************************************************************/

#ifndef WOLFSSL_NO_TLS12
static int TLSX_EncryptThenMac_Use(WOLFSSL* ssl);

/**
 * Get the size of the Encrypt-Then-MAC extension.
 *
 * msgType  Type of message to put extension into.
 * pSz      Size of extension data.
 * return SANITY_MSG_E when the message is not allowed to have extension and
 *        0 otherwise.
 */
static int TLSX_EncryptThenMac_GetSize(byte msgType, word16* pSz)
{
    (void)pSz;

    if (msgType != client_hello && msgType != server_hello) {
        return SANITY_MSG_E;
    }

    /* Empty extension */

    return 0;
}

/**
 * Write the Encrypt-Then-MAC extension.
 *
 * data     Unused
 * output   Extension data buffer. Unused.
 * msgType  Type of message to put extension into.
 * pSz      Size of extension data.
 * return SANITY_MSG_E when the message is not allowed to have extension and
 *        0 otherwise.
 */
static int TLSX_EncryptThenMac_Write(void* data, byte* output, byte msgType,
                                     word16* pSz)
{
    (void)data;
    (void)output;
    (void)pSz;

    if (msgType != client_hello && msgType != server_hello) {
        return SANITY_MSG_E;
    }

    /* Empty extension */

    return 0;
}

/**
 * Parse the Encrypt-Then-MAC extension.
 *
 * ssl      SSL object
 * input    Extension data buffer.
 * length   Length of this extension's data.
 * msgType  Type of message to extension appeared in.
 * return SANITY_MSG_E when the message is not allowed to have extension,
 *        BUFFER_ERROR when the extension's data is invalid,
 *        MEMORY_E when unable to allocate memory and
 *        0 otherwise.
 */
static int TLSX_EncryptThenMac_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                     byte msgType)
{
    int ret;

    (void)input;

    if (msgType != client_hello && msgType != server_hello) {
        return SANITY_MSG_E;
    }

    /* Empty extension */
    if (length != 0)
        return BUFFER_ERROR;

    if (msgType == client_hello) {
        /* Check the user hasn't disallowed use of Encrypt-Then-Mac. */
        if (!ssl->options.disallowEncThenMac) {
            ssl->options.encThenMac = 1;
            /* Set the extension reply. */
            ret = TLSX_EncryptThenMac_Use(ssl);
            if (ret != 0)
                return ret;
            TLSX_SetResponse(ssl, TLSX_ENCRYPT_THEN_MAC);
        }
        return 0;
    }

    /* Server Hello */
    if (ssl->options.disallowEncThenMac)
        return SANITY_MSG_E;

    ssl->options.encThenMac = 1;
    return 0;

}

/**
 * Add the Encrypt-Then-MAC extension to list.
 *
 * ssl      SSL object
 * return MEMORY_E when unable to allocate memory and 0 otherwise.
 */
static int TLSX_EncryptThenMac_Use(WOLFSSL* ssl)
{
    int   ret = 0;
    TLSX* extension;

    /* Find the Encrypt-Then-Mac extension if it exists. */
    extension = TLSX_Find(ssl->extensions, TLSX_ENCRYPT_THEN_MAC);
    if (extension == NULL) {
        /* Push new Encrypt-Then-Mac extension. */
        ret = TLSX_Push(&ssl->extensions, TLSX_ENCRYPT_THEN_MAC, NULL,
            ssl->heap);
        if (ret != 0)
            return ret;
    }

    return 0;
}

#define ETM_GET_SIZE  TLSX_EncryptThenMac_GetSize
#define ETM_WRITE     TLSX_EncryptThenMac_Write
#define ETM_PARSE     TLSX_EncryptThenMac_Parse

#else

#define ETM_GET_SIZE(a, b)    0
#define ETM_WRITE(a, b, c, d) 0
#define ETM_PARSE(a, b, c, d) 0

#endif /* !WOLFSSL_NO_TLS12 */

#endif /* HAVE_ENCRYPT_THEN_MAC && !WOLFSSL_AEAD_ONLY */

/******************************************************************************/
/* Supported Versions                                                         */
/******************************************************************************/

#ifdef WOLFSSL_TLS13
/* Return the size of the SupportedVersions extension's data.
 *
 * data       The SSL/TLS object.
 * msgType The type of the message this extension is being written into.
 * returns the length of data that will be in the extension.
 */
static int TLSX_SupportedVersions_GetSize(void* data, byte msgType, word16* pSz)
{
    WOLFSSL* ssl = (WOLFSSL*)data;

    if (msgType == client_hello) {
        /* TLS v1.2 and TLS v1.3  */
        int cnt = 0;

        #if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
            if ((ssl->options.mask & SSL_OP_NO_TLSv1_3) == 0)
        #endif
                cnt++;

        if (ssl->options.downgrade) {
#ifndef WOLFSSL_NO_TLS12
        #if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
            if ((ssl->options.mask & SSL_OP_NO_TLSv1_2) == 0)
        #endif
                cnt++;
#endif

#ifndef NO_OLD_TLS
        #if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
            if ((ssl->options.mask & SSL_OP_NO_TLSv1_1) == 0)
        #endif
                cnt++;
    #ifdef WOLFSSL_ALLOW_TLSV10
        #if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
            if ((ssl->options.mask & SSL_OP_NO_TLSv1) == 0)
        #endif
                cnt++;
    #endif
#endif
        }

        *pSz += (word16)(OPAQUE8_LEN + cnt * OPAQUE16_LEN);
    }
    else if (msgType == server_hello || msgType == hello_retry_request)
        *pSz += OPAQUE16_LEN;
    else
        return SANITY_MSG_E;

    return 0;
}

/* Writes the SupportedVersions extension into the buffer.
 *
 * data    The SSL/TLS object.
 * output  The buffer to write the extension into.
 * msgType The type of the message this extension is being written into.
 * returns the length of data that was written.
 */
static int TLSX_SupportedVersions_Write(void* data, byte* output,
                                        byte msgType, word16* pSz)
{
    WOLFSSL* ssl = (WOLFSSL*)data;
    byte major;
    byte* cnt;

    if (msgType == client_hello) {
        major = ssl->ctx->method->version.major;


        cnt = output++;
        *cnt = 0;
        #if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
            if ((ssl->options.mask & SSL_OP_NO_TLSv1_3) == 0)
        #endif
            {
                *cnt += OPAQUE16_LEN;
#ifdef WOLFSSL_TLS13_DRAFT
                /* The TLS draft major number. */
                *(output++) = TLS_DRAFT_MAJOR;
                /* Version of draft supported. */
                *(output++) = TLS_DRAFT_MINOR;
#else
                *(output++) = major;
                *(output++) = (byte)TLSv1_3_MINOR;
#endif
            }
        if (ssl->options.downgrade) {
#ifndef WOLFSSL_NO_TLS12
        #if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
            if ((ssl->options.mask & SSL_OP_NO_TLSv1_2) == 0)
        #endif
            {
                *cnt += OPAQUE16_LEN;
                *(output++) = major;
                *(output++) = (byte)TLSv1_2_MINOR;
            }
#endif

#ifndef NO_OLD_TLS
        #if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
            if ((ssl->options.mask & SSL_OP_NO_TLSv1_1) == 0)
        #endif
            {
                *cnt += OPAQUE16_LEN;
                *(output++) = major;
                *(output++) = (byte)TLSv1_1_MINOR;
            }
    #ifdef WOLFSSL_ALLOW_TLSV10
        #if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
            if ((ssl->options.mask & SSL_OP_NO_TLSv1) == 0)
        #endif
            {
                *cnt += OPAQUE16_LEN;
                *(output++) = major;
                *(output++) = (byte)TLSv1_MINOR;
            }
    #endif
#endif
        }

        *pSz += (word16)(OPAQUE8_LEN + *cnt);
    }
    else if (msgType == server_hello || msgType == hello_retry_request) {
        output[0] = ssl->version.major;
        output[1] = ssl->version.minor;

        *pSz += OPAQUE16_LEN;
    }
    else
        return SANITY_MSG_E;

    return 0;
}

/* Parse the SupportedVersions extension.
 *
 * ssl     The SSL/TLS object.
 * input   The buffer with the extension data.
 * length  The length of the extension data.
 * msgType The type of the message this extension is being parsed from.
 * returns 0 on success, otherwise failure.
 */
static int TLSX_SupportedVersions_Parse(WOLFSSL* ssl, byte* input,
                                        word16 length, byte msgType)
{
    ProtocolVersion pv = ssl->ctx->method->version;
    int i;
    int len;
    byte major, minor;
    int newMinor = 0;
    int set = 0;
    int ret;

    if (msgType == client_hello) {
        /* Must contain a length and at least one version. */
        if (length < OPAQUE8_LEN + OPAQUE16_LEN || (length & 1) != 1)
            return BUFFER_ERROR;

        len = *input;

        /* Protocol version array must fill rest of data. */
        if (length != (word16)OPAQUE8_LEN + len)
            return BUFFER_ERROR;

        input++;

        /* Find first match. */
        for (i = 0; i < len; i += OPAQUE16_LEN) {
            major = input[i];
            minor = input[i + OPAQUE8_LEN];

#ifdef WOLFSSL_TLS13_DRAFT
            if (major == TLS_DRAFT_MAJOR && minor == TLS_DRAFT_MINOR) {
                major = SSLv3_MAJOR;
                minor = TLSv1_3_MINOR;
            }
#else
            if (major == TLS_DRAFT_MAJOR)
                continue;
#endif

            if (major != pv.major)
                continue;

            /* No upgrade allowed. */
            if (minor > ssl->version.minor)
                    continue;
            /* Check downgrade. */
            if (minor < ssl->version.minor) {
                if (!ssl->options.downgrade)
                    continue;

                if (minor < ssl->options.minDowngrade)
                    continue;

                if (newMinor == 0 && minor > ssl->options.oldMinor) {
                    /* Downgrade the version. */
                    ssl->version.minor = minor;
                }
            }

            if (minor >= TLSv1_3_MINOR) {
                if (!ssl->options.tls1_3) {
                    ssl->options.tls1_3 = 1;
                    ret = TLSX_Prepend(&ssl->extensions,
                              TLSX_SUPPORTED_VERSIONS, ssl, ssl->heap);
                    if (ret != 0) {
                        return ret;
                    }
                    TLSX_SetResponse(ssl, TLSX_SUPPORTED_VERSIONS);
                }
                if (minor > newMinor) {
                    ssl->version.minor = minor;
                    newMinor = minor;
                }
            }
            else if (minor > ssl->options.oldMinor)
                ssl->options.oldMinor = minor;

            set = 1;
        }
        if (!set) {
 #ifdef WOLFSSL_MYSQL_COMPATIBLE
            SendAlert(ssl, alert_fatal, wc_protocol_version);
 #else
            SendAlert(ssl, alert_fatal, protocol_version);
 #endif
            return VERSION_ERROR;
        }
    }
    else if (msgType == server_hello || msgType == hello_retry_request) {
        /* Must contain one version. */
        if (length != OPAQUE16_LEN)
            return BUFFER_ERROR;

        major = input[0];
        minor = input[OPAQUE8_LEN];

        if (major != pv.major)
            return VERSION_ERROR;

        /* Can't downgrade with this extension below TLS v1.3. */
        if (minor < TLSv1_3_MINOR)
            return VERSION_ERROR;

        /* Version is TLS v1.2 to handle downgrading from TLS v1.3+. */
        if (ssl->options.downgrade && ssl->version.minor == TLSv1_2_MINOR) {
            /* Set minor version back to TLS v1.3+ */
            ssl->version.minor = ssl->ctx->method->version.minor;
        }

        /* No upgrade allowed. */
        if (ssl->version.minor < minor)
            return VERSION_ERROR;

        /* Check downgrade. */
        if (ssl->version.minor > minor) {
            if (!ssl->options.downgrade)
                return VERSION_ERROR;

            if (minor < ssl->options.minDowngrade)
                return VERSION_ERROR;

            /* Downgrade the version. */
            ssl->version.minor = minor;
        }
    }
    else
        return SANITY_MSG_E;

    return 0;
}

/* Sets a new SupportedVersions extension into the extension list.
 *
 * extensions  The list of extensions.
 * data        The extensions specific data.
 * heap        The heap used for allocation.
 * returns 0 on success, otherwise failure.
 */
static int TLSX_SetSupportedVersions(TLSX** extensions, const void* data,
                                     void* heap)
{
    if (extensions == NULL || data == NULL)
        return BAD_FUNC_ARG;

    return TLSX_Push(extensions, TLSX_SUPPORTED_VERSIONS, (void *)data, heap);
}

#define SV_GET_SIZE  TLSX_SupportedVersions_GetSize
#define SV_WRITE     TLSX_SupportedVersions_Write
#define SV_PARSE     TLSX_SupportedVersions_Parse

#else

#define SV_GET_SIZE(a, b, c) 0
#define SV_WRITE(a, b, c, d) 0
#define SV_PARSE(a, b, c, d) 0

#endif /* WOLFSSL_TLS13 */

#if defined(WOLFSSL_TLS13)

/******************************************************************************/
/* Cookie                                                                     */
/******************************************************************************/

/* Free the cookie data.
 *
 * cookie  Cookie data.
 * heap    The heap used for allocation.
 */
static void TLSX_Cookie_FreeAll(Cookie* cookie, void* heap)
{
    (void)heap;

    if (cookie != NULL)
        XFREE(cookie, heap, DYNAMIC_TYPE_TLSX);
}

/* Get the size of the encoded Cookie extension.
 * In messages: ClientHello and HelloRetryRequest.
 *
 * cookie   The cookie to write.
 * msgType  The type of the message this extension is being written into.
 * returns the number of bytes of the encoded Cookie extension.
 */
static int TLSX_Cookie_GetSize(Cookie* cookie, byte msgType, word16* pSz)
{
    if (msgType == client_hello || msgType == hello_retry_request)
        *pSz += OPAQUE16_LEN + cookie->len;
    else
        return SANITY_MSG_E;
    return 0;
}

/* Writes the Cookie extension into the output buffer.
 * Assumes that the the output buffer is big enough to hold data.
 * In messages: ClientHello and HelloRetryRequest.
 *
 * cookie   The cookie to write.
 * output   The buffer to write into.
 * msgType  The type of the message this extension is being written into.
 * returns the number of bytes written into the buffer.
 */
static int TLSX_Cookie_Write(Cookie* cookie, byte* output, byte msgType,
                             word16* pSz)
{
    if (msgType == client_hello || msgType == hello_retry_request) {
        c16toa(cookie->len, output);
        output += OPAQUE16_LEN;
        XMEMCPY(output, &cookie->data, cookie->len);
        *pSz += OPAQUE16_LEN + cookie->len;
    }
    else
        return SANITY_MSG_E;
    return 0;
}

/* Parse the Cookie extension.
 * In messages: ClientHello and HelloRetryRequest.
 *
 * ssl      The SSL/TLS object.
 * input    The extension data.
 * length   The length of the extension data.
 * msgType  The type of the message this extension is being parsed from.
 * returns 0 on success and other values indicate failure.
 */
static int TLSX_Cookie_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                 byte msgType)
{
    word16  len;
    word16  idx = 0;
    TLSX*   extension;
    Cookie* cookie;

    if (msgType != client_hello && msgType != hello_retry_request)
        return SANITY_MSG_E;

    /* Message contains length and Cookie which must be at least one byte
     * in length.
     */
    if (length < OPAQUE16_LEN + 1)
        return BUFFER_E;
    ato16(input + idx, &len);
    idx += OPAQUE16_LEN;
    if (length - idx != len)
        return BUFFER_E;

    if (msgType == hello_retry_request)
        return TLSX_Cookie_Use(ssl, input + idx, len, NULL, 0, 0);

    /* client_hello */
    extension = TLSX_Find(ssl->extensions, TLSX_COOKIE);
    if (extension == NULL)
        return HRR_COOKIE_ERROR;

    cookie = (Cookie*)extension->data;
    if (cookie->len != len || XMEMCMP(&cookie->data, input + idx, len) != 0)
        return HRR_COOKIE_ERROR;

    /* Request seen. */
    extension->resp = 0;

    return 0;
}

/* Use the data to create a new Cookie object in the extensions.
 *
 * ssl    SSL/TLS object.
 * data   Cookie data.
 * len    Length of cookie data in bytes.
 * mac    MAC data.
 * macSz  Length of MAC data in bytes.
 * resp   Indicates the extension will go into a response (HelloRetryRequest).
 * returns 0 on success and other values indicate failure.
 */
int TLSX_Cookie_Use(WOLFSSL* ssl, byte* data, word16 len, byte* mac,
                    byte macSz, int resp)
{
    int     ret = 0;
    TLSX*   extension;
    Cookie* cookie;

    /* Find the cookie extension if it exists. */
    extension = TLSX_Find(ssl->extensions, TLSX_COOKIE);
    if (extension == NULL) {
        /* Push new cookie extension. */
        ret = TLSX_Push(&ssl->extensions, TLSX_COOKIE, NULL, ssl->heap);
        if (ret != 0)
            return ret;

        extension = TLSX_Find(ssl->extensions, TLSX_COOKIE);
        if (extension == NULL)
            return MEMORY_E;
    }

    /* The Cookie structure has one byte for cookie data already. */
    cookie = (Cookie*)XMALLOC(sizeof(Cookie) + len + macSz - 1, ssl->heap,
                              DYNAMIC_TYPE_TLSX);
    if (cookie == NULL)
        return MEMORY_E;

    cookie->len = len + macSz;
    XMEMCPY(&cookie->data, data, len);
    if (mac != NULL)
        XMEMCPY(&cookie->data + len, mac, macSz);

    extension->data = (void*)cookie;
    extension->resp = (byte)resp;

    return 0;
}

#define CKE_FREE_ALL  TLSX_Cookie_FreeAll
#define CKE_GET_SIZE  TLSX_Cookie_GetSize
#define CKE_WRITE     TLSX_Cookie_Write
#define CKE_PARSE     TLSX_Cookie_Parse

#else

#define CKE_FREE_ALL(a, b)    0
#define CKE_GET_SIZE(a, b, c) 0
#define CKE_WRITE(a, b, c, d) 0
#define CKE_PARSE(a, b, c, d) 0

#endif
#if !defined(WOLFSSL_NO_SIGALG)
/******************************************************************************/
/* Signature Algorithms                                                       */
/******************************************************************************/

/* Return the size of the SignatureAlgorithms extension's data.
 *
 * data  Unused
 * returns the length of data that will be in the extension.
 */

static word16 TLSX_SignatureAlgorithms_GetSize(void* data)
{
    WOLFSSL* ssl = (WOLFSSL*)data;

    return OPAQUE16_LEN + ssl->suites->hashSigAlgoSz;
}

/* Creates a bit string of supported hash algorithms with RSA PSS.
 * The bit string is used when determining which signature algorithm to use
 * when creating the CertificateVerify message.
 * Note: Valid data has an even length as each signature algorithm is two bytes.
 *
 * ssl     The SSL/TLS object.
 * input   The buffer with the list of supported signature algorithms.
 * length  The length of the list in bytes.
 * returns 0 on success, BUFFER_ERROR when the length is not even.
 */
static int TLSX_SignatureAlgorithms_MapPss(WOLFSSL *ssl, byte* input,
                                                                  word16 length)
{
    word16 i;

    if ((length & 1) == 1)
        return BUFFER_ERROR;

    ssl->pssAlgo = 0;
    for (i = 0; i < length; i += 2) {
        if (input[i] == rsa_pss_sa_algo && input[i + 1] <= sha512_mac)
            ssl->pssAlgo |= 1 << input[i + 1];
    #ifdef WOLFSSL_TLS13
        if (input[i] == rsa_pss_sa_algo && input[i + 1] >= pss_sha256 &&
                                                   input[i + 1] <= pss_sha512) {
            ssl->pssAlgo |= 1 << input[i + 1];
        }
    #endif
    }

    return 0;
}

/* Writes the SignatureAlgorithms extension into the buffer.
 *
 * data    Unused
 * output  The buffer to write the extension into.
 * returns the length of data that was written.
 */
static word16 TLSX_SignatureAlgorithms_Write(void* data, byte* output)
{
    WOLFSSL* ssl = (WOLFSSL*)data;

    c16toa(ssl->suites->hashSigAlgoSz, output);
    XMEMCPY(output + OPAQUE16_LEN, ssl->suites->hashSigAlgo,
            ssl->suites->hashSigAlgoSz);

    TLSX_SignatureAlgorithms_MapPss(ssl, output + OPAQUE16_LEN,
                                    ssl->suites->hashSigAlgoSz);

    return OPAQUE16_LEN + ssl->suites->hashSigAlgoSz;
}

/* Parse the SignatureAlgorithms extension.
 *
 * ssl     The SSL/TLS object.
 * input   The buffer with the extension data.
 * length  The length of the extension data.
 * returns 0 on success, otherwise failure.
 */
static int TLSX_SignatureAlgorithms_Parse(WOLFSSL *ssl, byte* input,
                                  word16 length, byte isRequest, Suites* suites)
{
    word16 len;

    if (!isRequest)
        return BUFFER_ERROR;

    /* Must contain a length and at least algorithm. */
    if (length < OPAQUE16_LEN + OPAQUE16_LEN || (length & 1) != 0)
        return BUFFER_ERROR;

    ato16(input, &len);
    input += OPAQUE16_LEN;

    /* Algorithm array must fill rest of data. */
    if (length != OPAQUE16_LEN + len)
        return BUFFER_ERROR;

    /* Sig Algo list size must be even. */
    if (suites->hashSigAlgoSz % 2 != 0)
        return BUFFER_ERROR;

    /* truncate hashSigAlgo list if too long */
    suites->hashSigAlgoSz = len;
    if (suites->hashSigAlgoSz > WOLFSSL_MAX_SIGALGO) {
        WOLFSSL_MSG("TLSX SigAlgo list exceeds max, truncating");
        suites->hashSigAlgoSz = WOLFSSL_MAX_SIGALGO;
    }
    XMEMCPY(suites->hashSigAlgo, input, suites->hashSigAlgoSz);

    return TLSX_SignatureAlgorithms_MapPss(ssl, input, len);
}

/* Sets a new SignatureAlgorithms extension into the extension list.
 *
 * extensions  The list of extensions.
 * data        The extensions specific data.
 * heap        The heap used for allocation.
 * returns 0 on success, otherwise failure.
 */
static int TLSX_SetSignatureAlgorithms(TLSX** extensions, const void* data,
                                       void* heap)
{
    if (extensions == NULL)
        return BAD_FUNC_ARG;

    return TLSX_Push(extensions, TLSX_SIGNATURE_ALGORITHMS, (void *)data, heap);
}

#define SA_GET_SIZE  TLSX_SignatureAlgorithms_GetSize
#define SA_WRITE     TLSX_SignatureAlgorithms_Write
#define SA_PARSE     TLSX_SignatureAlgorithms_Parse
#endif
/******************************************************************************/
/* Signature Algorithms Certificate                                           */
/******************************************************************************/

#ifdef WOLFSSL_TLS13
/* Return the size of the SignatureAlgorithms extension's data.
 *
 * data  Unused
 * returns the length of data that will be in the extension.
 */
static word16 TLSX_SignatureAlgorithmsCert_GetSize(void* data)
{
    WOLFSSL* ssl = (WOLFSSL*)data;

    return OPAQUE16_LEN + ssl->certHashSigAlgoSz;
}

/* Writes the SignatureAlgorithmsCert extension into the buffer.
 *
 * data    Unused
 * output  The buffer to write the extension into.
 * returns the length of data that was written.
 */
static word16 TLSX_SignatureAlgorithmsCert_Write(void* data, byte* output)
{
    WOLFSSL* ssl = (WOLFSSL*)data;

    c16toa(ssl->certHashSigAlgoSz, output);
    XMEMCPY(output + OPAQUE16_LEN, ssl->certHashSigAlgo,
            ssl->certHashSigAlgoSz);

    return OPAQUE16_LEN + ssl->certHashSigAlgoSz;
}

/* Parse the SignatureAlgorithmsCert extension.
 *
 * ssl     The SSL/TLS object.
 * input   The buffer with the extension data.
 * length  The length of the extension data.
 * returns 0 on success, otherwise failure.
 */
static int TLSX_SignatureAlgorithmsCert_Parse(WOLFSSL *ssl, byte* input,
                                              word16 length, byte isRequest)
{
    word16 len;

    if (!isRequest)
        return BUFFER_ERROR;

    /* Must contain a length and at least algorithm. */
    if (length < OPAQUE16_LEN + OPAQUE16_LEN || (length & 1) != 0)
        return BUFFER_ERROR;

    ato16(input, &len);
    input += OPAQUE16_LEN;

    /* Algorithm array must fill rest of data. */
    if (length != OPAQUE16_LEN + len)
        return BUFFER_ERROR;

    /* truncate hashSigAlgo list if too long */
    ssl->certHashSigAlgoSz = len;
    if (ssl->certHashSigAlgoSz > WOLFSSL_MAX_SIGALGO) {
        WOLFSSL_MSG("TLSX SigAlgo list exceeds max, truncating");
        ssl->certHashSigAlgoSz = WOLFSSL_MAX_SIGALGO;
    }
    XMEMCPY(ssl->certHashSigAlgo, input, ssl->certHashSigAlgoSz);

    return 0;
}

/* Sets a new SignatureAlgorithmsCert extension into the extension list.
 *
 * extensions  The list of extensions.
 * data        The extensions specific data.
 * heap        The heap used for allocation.
 * returns 0 on success, otherwise failure.
 */
static int TLSX_SetSignatureAlgorithmsCert(TLSX** extensions, const void* data,
                                                                     void* heap)
{
    if (extensions == NULL)
        return BAD_FUNC_ARG;

    return TLSX_Push(extensions, TLSX_SIGNATURE_ALGORITHMS_CERT, (void *)data,
                                                                          heap);
}

#define SAC_GET_SIZE  TLSX_SignatureAlgorithmsCert_GetSize
#define SAC_WRITE     TLSX_SignatureAlgorithmsCert_Write
#define SAC_PARSE     TLSX_SignatureAlgorithmsCert_Parse
#endif /* WOLFSSL_TLS13 */


/******************************************************************************/
/* Key Share                                                                  */
/******************************************************************************/

#ifdef WOLFSSL_TLS13
/* Create a key share entry using named Diffie-Hellman parameters group.
 * Generates a key pair.
 *
 * ssl   The SSL/TLS object.
 * kse   The key share entry object.
 * returns 0 on success, otherwise failure.
 */
static int TLSX_KeyShare_GenDhKey(WOLFSSL *ssl, KeyShareEntry* kse)
{
    int             ret;
#ifndef NO_DH
    byte*           keyData;
    void*           key = NULL;
    word32          keySz;
    word32          dataSz;
    const DhParams* params;
#ifdef WOLFSSL_SMALL_STACK
    DhKey*          dhKey = NULL;
#else
    DhKey           dhKey[1];
#endif

    /* TODO: [TLS13] The key size should come from wolfcrypt. */
    /* Pick the parameters from the named group. */
    switch (kse->group) {
    #ifdef HAVE_FFDHE_2048
        case WOLFSSL_FFDHE_2048:
            params = wc_Dh_ffdhe2048_Get();
            keySz = 29;
            break;
    #endif
    #ifdef HAVE_FFDHE_3072
        case WOLFSSL_FFDHE_3072:
            params = wc_Dh_ffdhe3072_Get();
            keySz = 34;
            break;
    #endif
    #ifdef HAVE_FFDHE_4096
        case WOLFSSL_FFDHE_4096:
            params = wc_Dh_ffdhe4096_Get();
            keySz = 39;
            break;
    #endif
    #ifdef HAVE_FFDHE_6144
        case WOLFSSL_FFDHE_6144:
            params = wc_Dh_ffdhe6144_Get();
            keySz = 46;
            break;
    #endif
    #ifdef HAVE_FFDHE_8192
        case WOLFSSL_FFDHE_8192:
            params = wc_Dh_ffdhe8192_Get();
            keySz = 52;
            break;
    #endif
        default:
            return BAD_FUNC_ARG;
    }

#ifdef WOLFSSL_SMALL_STACK
    dhKey = (DhKey*)XMALLOC(sizeof(DhKey), ssl->heap, DYNAMIC_TYPE_DH);
    if (dhKey == NULL)
        return MEMORY_E;
#endif

    ret = wc_InitDhKey_ex(dhKey, ssl->heap, ssl->devId);
    if (ret != 0) {
    #ifdef WOLFSSL_SMALL_STACK
        XFREE(dhKey, ssl->heap, DYNAMIC_TYPE_DH);
    #endif
        return ret;
    }

    /* Allocate space for the public key */
    dataSz = params->p_len;
    keyData = (byte*)XMALLOC(dataSz, ssl->heap, DYNAMIC_TYPE_PUBLIC_KEY);
    if (keyData == NULL) {
        ret = MEMORY_E;
        goto end;
    }
    /* Allocate space for the private key */
    key = (byte*)XMALLOC(keySz, ssl->heap, DYNAMIC_TYPE_PRIVATE_KEY);
    if (key == NULL) {
        ret = MEMORY_E;
        goto end;
    }

    /* Set key */
    ret = wc_DhSetKey(dhKey,
        (byte*)params->p, params->p_len,
        (byte*)params->g, params->g_len);
    if (ret != 0)
        goto end;

#if defined(WOLFSSL_STATIC_EPHEMERAL) && defined(WOLFSSL_DH_EXTRA)
    if (ssl->staticKE.key && ssl->staticKE.keyAlgo == WC_PK_TYPE_DH) {
        DerBuffer* keyDer = ssl->staticKE.key;
        word32 idx = 0;
        WOLFSSL_MSG("Using static DH key");
        ret = wc_DhKeyDecode(keyDer->buffer, &idx, dhKey, keyDer->length);
        if (ret == 0) {
            ret = wc_DhExportKeyPair(dhKey, (byte*)key, &keySz, keyData, &dataSz);
        }
    }
    else
#endif
    {
        /* Generate a new key pair */
        ret = wc_DhGenerateKeyPair(dhKey, ssl->rng, (byte*)key, &keySz, keyData,
                                &dataSz);
    #ifdef WOLFSSL_ASYNC_CRYPT
        /* TODO: Make this function non-blocking */
        if (ret == WC_PENDING_E) {
            ret = wc_AsyncWait(ret, &dhKey->asyncDev, WC_ASYNC_FLAG_NONE);
        }
    #endif
    }
    if (ret != 0)
        goto end;

    if (params->p_len != dataSz) {
        /* Zero pad the front of the public key to match prime "p" size */
        XMEMMOVE(keyData + params->p_len - dataSz, keyData, dataSz);
        XMEMSET(keyData, 0, params->p_len - dataSz);
    }

    kse->pubKey = keyData;
    kse->pubKeyLen = params->p_len;
    kse->key = key;
    kse->keyLen = keySz;

#ifdef WOLFSSL_DEBUG_TLS
    WOLFSSL_MSG("Public DH Key");
    WOLFSSL_BUFFER(keyData, params->p_len);
#endif

end:

    wc_FreeDhKey(dhKey);
#ifdef WOLFSSL_SMALL_STACK
    XFREE(dhKey, ssl->heap, DYNAMIC_TYPE_DH);
#endif

    if (ret != 0) {
        /* Data owned by key share entry otherwise. */
        if (keyData != NULL)
            XFREE(keyData, ssl->heap, DYNAMIC_TYPE_PUBLIC_KEY);
        if (key != NULL)
            XFREE(key, ssl->heap, DYNAMIC_TYPE_PRIVATE_KEY);
    }
#else
    (void)ssl;
    (void)kse;

    ret = NOT_COMPILED_IN;
#endif

    return ret;
}

/* Create a key share entry using X25519 parameters group.
 * Generates a key pair.
 *
 * ssl   The SSL/TLS object.
 * kse   The key share entry object.
 * returns 0 on success, otherwise failure.
 */
static int TLSX_KeyShare_GenX25519Key(WOLFSSL *ssl, KeyShareEntry* kse)
{
    int             ret;
#ifdef HAVE_CURVE25519
    byte*           keyData = NULL;
    word32          dataSize = CURVE25519_KEYSIZE;
    curve25519_key* key;

    /* Allocate an ECC key to hold private key. */
    key = (curve25519_key*)XMALLOC(sizeof(curve25519_key), ssl->heap,
                                                      DYNAMIC_TYPE_PRIVATE_KEY);
    if (key == NULL) {
        WOLFSSL_MSG("EccTempKey Memory error");
        return MEMORY_E;
    }

    /* Make an ECC key. */
    ret = wc_curve25519_init(key);
    if (ret != 0)
        goto end;
    ret = wc_curve25519_make_key(ssl->rng, CURVE25519_KEYSIZE, key);
    if (ret != 0)
        goto end;

    /* Allocate space for the public key. */
    keyData = (byte*)XMALLOC(CURVE25519_KEYSIZE, ssl->heap,
                                                       DYNAMIC_TYPE_PUBLIC_KEY);
    if (keyData == NULL) {
        WOLFSSL_MSG("Key data Memory error");
        ret = MEMORY_E;
        goto end;
    }

    /* Export public key. */
    if (wc_curve25519_export_public_ex(key, keyData, &dataSize,
                                                  EC25519_LITTLE_ENDIAN) != 0) {
        ret = ECC_EXPORT_ERROR;
        goto end;
    }

    kse->pubKey = keyData;
    kse->pubKeyLen = CURVE25519_KEYSIZE;
    kse->key = key;

#ifdef WOLFSSL_DEBUG_TLS
    WOLFSSL_MSG("Public Curve25519 Key");
    WOLFSSL_BUFFER(keyData, dataSize);
#endif

end:
    if (ret != 0) {
        /* Data owned by key share entry otherwise. */
        if (keyData != NULL)
            XFREE(keyData, ssl->heap, DYNAMIC_TYPE_PUBLIC_KEY);
        wc_curve25519_free(key);
        XFREE(key, ssl->heap, DYNAMIC_TYPE_PRIVATE_KEY);
    }
#else
    (void)ssl;
    (void)kse;

    ret = NOT_COMPILED_IN;
#endif /* HAVE_CURVE25519 */

    return ret;
}

/* Create a key share entry using X448 parameters group.
 * Generates a key pair.
 *
 * ssl   The SSL/TLS object.
 * kse   The key share entry object.
 * returns 0 on success, otherwise failure.
 */
static int TLSX_KeyShare_GenX448Key(WOLFSSL *ssl, KeyShareEntry* kse)
{
    int             ret;
#ifdef HAVE_CURVE448
    byte*           keyData = NULL;
    word32          dataSize = CURVE448_KEY_SIZE;
    curve448_key*   key;

    /* Allocate an ECC key to hold private key. */
    key = (curve448_key*)XMALLOC(sizeof(curve448_key), ssl->heap,
                                                      DYNAMIC_TYPE_PRIVATE_KEY);
    if (key == NULL) {
        WOLFSSL_MSG("EccTempKey Memory error");
        return MEMORY_E;
    }

    /* Make an ECC key. */
    ret = wc_curve448_init(key);
    if (ret != 0)
        goto end;
    ret = wc_curve448_make_key(ssl->rng, CURVE448_KEY_SIZE, key);
    if (ret != 0)
        goto end;

    /* Allocate space for the public key. */
    keyData = (byte*)XMALLOC(CURVE448_KEY_SIZE, ssl->heap,
                                                       DYNAMIC_TYPE_PUBLIC_KEY);
    if (keyData == NULL) {
        WOLFSSL_MSG("Key data Memory error");
        ret = MEMORY_E;
        goto end;
    }

    /* Export public key. */
    if (wc_curve448_export_public_ex(key, keyData, &dataSize,
                                                    EC448_LITTLE_ENDIAN) != 0) {
        ret = ECC_EXPORT_ERROR;
        goto end;
    }

    kse->pubKey = keyData;
    kse->pubKeyLen = CURVE448_KEY_SIZE;
    kse->key = key;

#ifdef WOLFSSL_DEBUG_TLS
    WOLFSSL_MSG("Public Curve448 Key");
    WOLFSSL_BUFFER(keyData, dataSize);
#endif

end:
    if (ret != 0) {
        /* Data owned by key share entry otherwise. */
        if (keyData != NULL)
            XFREE(keyData, ssl->heap, DYNAMIC_TYPE_PUBLIC_KEY);
        wc_curve448_free(key);
        XFREE(key, ssl->heap, DYNAMIC_TYPE_PRIVATE_KEY);
    }
#else
    (void)ssl;
    (void)kse;

    ret = NOT_COMPILED_IN;
#endif /* HAVE_CURVE448 */

    return ret;
}

/* Create a key share entry using named elliptic curve parameters group.
 * Generates a key pair.
 *
 * ssl   The SSL/TLS object.
 * kse   The key share entry object.
 * returns 0 on success, otherwise failure.
 */
static int TLSX_KeyShare_GenEccKey(WOLFSSL *ssl, KeyShareEntry* kse)
{
    int      ret;
#ifdef HAVE_ECC
    byte*    keyData = NULL;
    word32   dataSize;
    byte*    keyPtr = NULL;
    word32   keySize;
    ecc_key* eccKey;
    word16   curveId;

    /* TODO: [TLS13] The key sizes should come from wolfcrypt. */
    /* Translate named group to a curve id. */
    switch (kse->group) {
    #if !defined(NO_ECC256)  || defined(HAVE_ALL_CURVES)
        #ifndef NO_ECC_SECP
        case WOLFSSL_ECC_SECP256R1:
            curveId = ECC_SECP256R1;
            keySize = 32;
            dataSize = keySize * 2 + 1;
            break;
        #endif /* !NO_ECC_SECP */
    #endif
    #if defined(HAVE_ECC384) || defined(HAVE_ALL_CURVES)
        #ifndef NO_ECC_SECP
        case WOLFSSL_ECC_SECP384R1:
            curveId = ECC_SECP384R1;
            keySize = 48;
            dataSize = keySize * 2 + 1;
            break;
        #endif /* !NO_ECC_SECP */
    #endif
    #if defined(HAVE_ECC521) || defined(HAVE_ALL_CURVES)
        #ifndef NO_ECC_SECP
        case WOLFSSL_ECC_SECP521R1:
            curveId = ECC_SECP521R1;
            keySize = 66;
            dataSize = keySize * 2 + 1;
            break;
        #endif /* !NO_ECC_SECP */
    #endif
    #ifdef HAVE_X448
        case WOLFSSL_ECC_X448:
            curveId = ECC_X448;
            dataSize = keySize = 56;
            break;
    #endif
        default:
            return BAD_FUNC_ARG;
    }

    /* Allocate an ECC key to hold private key. */
    keyPtr = (byte*)XMALLOC(sizeof(ecc_key), ssl->heap,
                                                      DYNAMIC_TYPE_PRIVATE_KEY);
    if (keyPtr == NULL) {
        WOLFSSL_MSG("EccTempKey Memory error");
        return MEMORY_E;
    }
    eccKey = (ecc_key*)keyPtr;

    /* Make an ECC key. */
    ret = wc_ecc_init_ex(eccKey, ssl->heap, ssl->devId);
    if (ret != 0)
        goto end;

#ifdef WOLFSSL_STATIC_EPHEMERAL
    if (ssl->staticKE.key && ssl->staticKE.keyAlgo == WC_PK_TYPE_ECDH) {
        DerBuffer* keyDer = ssl->staticKE.key;
        word32 idx = 0;
        WOLFSSL_MSG("Using static ECDH key");
        ret = wc_EccPrivateKeyDecode(keyDer->buffer, &idx, eccKey, keyDer->length);
    }
    else
#endif
    {
        /* Generate ephemeral ECC key */
        ret = wc_ecc_make_key_ex(ssl->rng, keySize, eccKey, curveId);
    #ifdef WOLFSSL_ASYNC_CRYPT
        /* TODO: Make this function non-blocking */
        if (ret == WC_PENDING_E) {
            ret = wc_AsyncWait(ret, &eccKey->asyncDev, WC_ASYNC_FLAG_NONE);
        }
    #endif
    }
    if (ret != 0)
        goto end;

    /* Allocate space for the public key. */
    keyData = (byte*)XMALLOC(dataSize, ssl->heap, DYNAMIC_TYPE_PUBLIC_KEY);
    if (keyData == NULL) {
        WOLFSSL_MSG("Key data Memory error");
        ret = MEMORY_E;
        goto end;
    }

    /* Export public key. */
    if (wc_ecc_export_x963(eccKey, keyData, &dataSize) != 0) {
        ret = ECC_EXPORT_ERROR;
        goto end;
    }

    kse->pubKey = keyData;
    kse->pubKeyLen = dataSize;
    kse->key = keyPtr;

#ifdef WOLFSSL_DEBUG_TLS
    WOLFSSL_MSG("Public ECC Key");
    WOLFSSL_BUFFER(keyData, dataSize);
#endif

end:
    if (ret != 0) {
        /* Data owned by key share entry otherwise. */
        if (keyPtr != NULL)
            XFREE(keyPtr, ssl->heap, DYNAMIC_TYPE_PRIVATE_KEY);
        if (keyData != NULL)
            XFREE(keyData, ssl->heap, DYNAMIC_TYPE_PUBLIC_KEY);
    }
#else
    (void)ssl;
    (void)kse;

    ret = NOT_COMPILED_IN;
#endif /* HAVE_ECC */

    return ret;
}

/* Generate a secret/key using the key share entry.
 *
 * ssl  The SSL/TLS object.
 * kse  The key share entry holding peer data.
 */
static int TLSX_KeyShare_GenKey(WOLFSSL *ssl, KeyShareEntry *kse)
{
    /* Named FFHE groups have a bit set to identify them. */
    if ((kse->group & NAMED_DH_MASK) == NAMED_DH_MASK)
        return TLSX_KeyShare_GenDhKey(ssl, kse);
    if (kse->group == WOLFSSL_ECC_X25519)
        return TLSX_KeyShare_GenX25519Key(ssl, kse);
    if (kse->group == WOLFSSL_ECC_X448)
        return TLSX_KeyShare_GenX448Key(ssl, kse);
    return TLSX_KeyShare_GenEccKey(ssl, kse);
}

/* Free the key share dynamic data.
 *
 * list  The linked list of key share entry objects.
 * heap  The heap used for allocation.
 */
static void TLSX_KeyShare_FreeAll(KeyShareEntry* list, void* heap)
{
    KeyShareEntry* current;

    while ((current = list) != NULL) {
        list = current->next;
        if ((current->group & NAMED_DH_MASK) == 0) {
            if (current->group == WOLFSSL_ECC_X25519) {
#ifdef HAVE_CURVE25519
                wc_curve25519_free((curve25519_key*)current->key);
#endif
            }
            else if (current->group == WOLFSSL_ECC_X448) {
#ifdef HAVE_CURVE448
                wc_curve448_free((curve448_key*)current->key);
#endif
            }
            else {
#ifdef HAVE_ECC
                wc_ecc_free((ecc_key*)(current->key));
#endif
            }
        }
        if (current->key != NULL)
            XFREE(current->key, heap, DYNAMIC_TYPE_PRIVATE_KEY);
        XFREE(current->pubKey, heap, DYNAMIC_TYPE_PUBLIC_KEY);
        XFREE(current->ke, heap, DYNAMIC_TYPE_PUBLIC_KEY);
        XFREE(current, heap, DYNAMIC_TYPE_TLSX);
    }

    (void)heap;
}

/* Get the size of the encoded key share extension.
 *
 * list     The linked list of key share extensions.
 * msgType  The type of the message this extension is being written into.
 * returns the number of bytes of the encoded key share extension.
 */
static word16 TLSX_KeyShare_GetSize(KeyShareEntry* list, byte msgType)
{
    word16         len = 0;
    byte           isRequest = (msgType == client_hello);
    KeyShareEntry* current;

    /* The named group the server wants to use. */
    if (msgType == hello_retry_request)
        return OPAQUE16_LEN;

    /* List of key exchange groups. */
    if (isRequest)
        len += OPAQUE16_LEN;
    while ((current = list) != NULL) {
        list = current->next;

        if (!isRequest && current->key == NULL)
            continue;

        len += KE_GROUP_LEN + OPAQUE16_LEN + current->pubKeyLen;
    }

    return len;
}

/* Writes the key share extension into the output buffer.
 * Assumes that the the output buffer is big enough to hold data.
 *
 * list     The linked list of key share entries.
 * output   The buffer to write into.
 * msgType  The type of the message this extension is being written into.
 * returns the number of bytes written into the buffer.
 */
static word16 TLSX_KeyShare_Write(KeyShareEntry* list, byte* output,
                                  byte msgType)
{
    word16         i = 0;
    byte           isRequest = (msgType == client_hello);
    KeyShareEntry* current;

    if (msgType == hello_retry_request) {
        c16toa(list->group, output);
        return OPAQUE16_LEN;
    }

    /* ClientHello has a list but ServerHello is only the chosen. */
    if (isRequest)
        i += OPAQUE16_LEN;

    /* Write out all in the list. */
    while ((current = list) != NULL) {
        list = current->next;

        if (!isRequest && current->key == NULL)
            continue;

        c16toa(current->group, &output[i]);
        i += KE_GROUP_LEN;
        c16toa((word16)(current->pubKeyLen), &output[i]);
        i += OPAQUE16_LEN;
        XMEMCPY(&output[i], current->pubKey, current->pubKeyLen);
        i += (word16)current->pubKeyLen;
    }
    /* Write the length of the list if required. */
    if (isRequest)
        c16toa(i - OPAQUE16_LEN, output);

    return i;
}

/* Process the DH key share extension on the client side.
 *
 * ssl            The SSL/TLS object.
 * keyShareEntry  The key share entry object to use to calculate shared secret.
 * returns 0 on success and other values indicate failure.
 */
static int TLSX_KeyShare_ProcessDh(WOLFSSL* ssl, KeyShareEntry* keyShareEntry)
{
#ifndef NO_DH
    int             ret;
    const DhParams* params;
#ifdef WOLFSSL_SMALL_STACK
    DhKey*          dhKey = NULL;
#else
    DhKey           dhKey[1];
#endif

    switch (keyShareEntry->group) {
    #ifdef HAVE_FFDHE_2048
        case WOLFSSL_FFDHE_2048:
            params = wc_Dh_ffdhe2048_Get();
            break;
    #endif
    #ifdef HAVE_FFDHE_3072
        case WOLFSSL_FFDHE_3072:
            params = wc_Dh_ffdhe3072_Get();
            break;
    #endif
    #ifdef HAVE_FFDHE_4096
        case WOLFSSL_FFDHE_4096:
            params = wc_Dh_ffdhe4096_Get();
            break;
    #endif
    #ifdef HAVE_FFDHE_6144
        case WOLFSSL_FFDHE_6144:
            params = wc_Dh_ffdhe6144_Get();
            break;
    #endif
    #ifdef HAVE_FFDHE_8192
        case WOLFSSL_FFDHE_8192:
            params = wc_Dh_ffdhe8192_Get();
            break;
    #endif
        default:
            return PEER_KEY_ERROR;
    }

#ifdef WOLFSSL_DEBUG_TLS
    WOLFSSL_MSG("Peer DH Key");
    WOLFSSL_BUFFER(keyShareEntry->ke, keyShareEntry->keLen);
#endif

#ifdef WOLFSSL_SMALL_STACK
    dhKey = (DhKey*)XMALLOC(sizeof(DhKey), ssl->heap, DYNAMIC_TYPE_DH);
    if (dhKey == NULL)
        return MEMORY_E;
#endif

    ret = wc_InitDhKey_ex(dhKey, ssl->heap, ssl->devId);
    if (ret != 0) {
    #ifdef WOLFSSL_SMALL_STACK
        XFREE(dhKey, ssl->heap, DYNAMIC_TYPE_DH);
    #endif
        return ret;
    }

    /* Set key */
    ret = wc_DhSetKey(dhKey, (byte*)params->p, params->p_len, (byte*)params->g,
                                                                 params->g_len);
    if (ret != 0) {
        wc_FreeDhKey(dhKey);
    #ifdef WOLFSSL_SMALL_STACK
        XFREE(dhKey, ssl->heap, DYNAMIC_TYPE_DH);
    #endif
        return ret;
    }

    ret = wc_DhCheckPubKey(dhKey, keyShareEntry->ke, keyShareEntry->keLen);
    if (ret != 0) {
        wc_FreeDhKey(dhKey);
    #ifdef WOLFSSL_SMALL_STACK
        XFREE(dhKey, ssl->heap, DYNAMIC_TYPE_DH);
    #endif
        return PEER_KEY_ERROR;
    }

    /* Derive secret from private key and peer's public key. */
    ret = wc_DhAgree(dhKey,
        ssl->arrays->preMasterSecret, &ssl->arrays->preMasterSz,
        (const byte*)keyShareEntry->key, keyShareEntry->keyLen,
        keyShareEntry->ke, keyShareEntry->keLen);
#ifdef WOLFSSL_ASYNC_CRYPT
    /* TODO: Make this function non-blocking */
    if (ret == WC_PENDING_E) {
        ret = wc_AsyncWait(ret, &dhKey->asyncDev, WC_ASYNC_FLAG_NONE);
    }
#endif
    /* RFC 8446 Section 7.4.1:
     *     ... left-padded with zeros up to the size of the prime. ...
     */
    if (params->p_len > ssl->arrays->preMasterSz) {
        word32 diff = params->p_len - ssl->arrays->preMasterSz;
        XMEMMOVE(ssl->arrays->preMasterSecret + diff,
                        ssl->arrays->preMasterSecret, ssl->arrays->preMasterSz);
        XMEMSET(ssl->arrays->preMasterSecret, 0, diff);
        ssl->arrays->preMasterSz = params->p_len;
    }

    ssl->options.dhKeySz = params->p_len;

    wc_FreeDhKey(dhKey);
#ifdef WOLFSSL_SMALL_STACK
    XFREE(dhKey, ssl->heap, DYNAMIC_TYPE_DH);
#endif
    if (keyShareEntry->key != NULL) {
        XFREE(keyShareEntry->key, ssl->heap, DYNAMIC_TYPE_PRIVATE_KEY);
        keyShareEntry->key = NULL;
    }
    XFREE(keyShareEntry->pubKey, ssl->heap, DYNAMIC_TYPE_PUBLIC_KEY);
    keyShareEntry->pubKey = NULL;
    XFREE(keyShareEntry->ke, ssl->heap, DYNAMIC_TYPE_PUBLIC_KEY);
    keyShareEntry->ke = NULL;

    return ret;
#else
    (void)ssl;
    (void)keyShareEntry;
    return PEER_KEY_ERROR;
#endif
}

/* Process the X25519 key share extension on the client side.
 *
 * ssl            The SSL/TLS object.
 * keyShareEntry  The key share entry object to use to calculate shared secret.
 * returns 0 on success and other values indicate failure.
 */
static int TLSX_KeyShare_ProcessX25519(WOLFSSL* ssl,
                                       KeyShareEntry* keyShareEntry)
{
    int ret;

#ifdef HAVE_CURVE25519
    curve25519_key* key = (curve25519_key*)keyShareEntry->key;
    curve25519_key* peerX25519Key;

#ifdef HAVE_ECC
    if (ssl->peerEccKey != NULL) {
        wc_ecc_free(ssl->peerEccKey);
        ssl->peerEccKey = NULL;
    }
#endif

    peerX25519Key = (curve25519_key*)XMALLOC(sizeof(curve25519_key), ssl->heap,
                                                             DYNAMIC_TYPE_TLSX);
    if (peerX25519Key == NULL) {
        WOLFSSL_MSG("PeerEccKey Memory error");
        return MEMORY_ERROR;
    }
    ret = wc_curve25519_init(peerX25519Key);
    if (ret != 0) {
        XFREE(peerX25519Key, ssl->heap, DYNAMIC_TYPE_TLSX);
        return ret;
    }
#ifdef WOLFSSL_DEBUG_TLS
    WOLFSSL_MSG("Peer Curve25519 Key");
    WOLFSSL_BUFFER(keyShareEntry->ke, keyShareEntry->keLen);
#endif

    if (wc_curve25519_check_public(keyShareEntry->ke, keyShareEntry->keLen,
                                                  EC25519_LITTLE_ENDIAN) != 0) {
        ret = ECC_PEERKEY_ERROR;
    }

    if (ret == 0) {
        if (wc_curve25519_import_public_ex(keyShareEntry->ke,
                                            keyShareEntry->keLen, peerX25519Key,
                                            EC25519_LITTLE_ENDIAN) != 0) {
            ret = ECC_PEERKEY_ERROR;
        }
    }

    if (ret == 0) {
        ssl->ecdhCurveOID = ECC_X25519_OID;

        ret = wc_curve25519_shared_secret_ex(key, peerX25519Key,
                                                   ssl->arrays->preMasterSecret,
                                                   &ssl->arrays->preMasterSz,
                                                   EC25519_LITTLE_ENDIAN);
    }

    wc_curve25519_free(peerX25519Key);
    XFREE(peerX25519Key, ssl->heap, DYNAMIC_TYPE_TLSX);
    wc_curve25519_free((curve25519_key*)keyShareEntry->key);
    if (keyShareEntry->key != NULL) {
        XFREE(keyShareEntry->key, ssl->heap, DYNAMIC_TYPE_PRIVATE_KEY);
        keyShareEntry->key = NULL;
    }
#else
    (void)ssl;
    (void)keyShareEntry;

    ret = PEER_KEY_ERROR;
#endif /* HAVE_CURVE25519 */

    return ret;
}

/* Process the X448 key share extension on the client side.
 *
 * ssl            The SSL/TLS object.
 * keyShareEntry  The key share entry object to use to calculate shared secret.
 * returns 0 on success and other values indicate failure.
 */
static int TLSX_KeyShare_ProcessX448(WOLFSSL* ssl, KeyShareEntry* keyShareEntry)
{
    int ret;

#ifdef HAVE_CURVE448
    curve448_key* key = (curve448_key*)keyShareEntry->key;
    curve448_key* peerX448Key;

#ifdef HAVE_ECC
    if (ssl->peerEccKey != NULL) {
        wc_ecc_free(ssl->peerEccKey);
        ssl->peerEccKey = NULL;
    }
#endif

    peerX448Key = (curve448_key*)XMALLOC(sizeof(curve448_key), ssl->heap,
                                                             DYNAMIC_TYPE_TLSX);
    if (peerX448Key == NULL) {
        WOLFSSL_MSG("PeerEccKey Memory error");
        return MEMORY_ERROR;
    }
    ret = wc_curve448_init(peerX448Key);
    if (ret != 0) {
        XFREE(peerX448Key, ssl->heap, DYNAMIC_TYPE_TLSX);
        return ret;
    }
#ifdef WOLFSSL_DEBUG_TLS
    WOLFSSL_MSG("Peer Curve448 Key");
    WOLFSSL_BUFFER(keyShareEntry->ke, keyShareEntry->keLen);
#endif

    if (wc_curve448_check_public(keyShareEntry->ke, keyShareEntry->keLen,
                                                    EC448_LITTLE_ENDIAN) != 0) {
        ret = ECC_PEERKEY_ERROR;
    }

    if (ret == 0) {
        if (wc_curve448_import_public_ex(keyShareEntry->ke,
                                              keyShareEntry->keLen, peerX448Key,
                                              EC448_LITTLE_ENDIAN) != 0) {
            ret = ECC_PEERKEY_ERROR;
        }
    }

    if (ret == 0) {
        ssl->ecdhCurveOID = ECC_X448_OID;

        ret = wc_curve448_shared_secret_ex(key, peerX448Key,
                                                   ssl->arrays->preMasterSecret,
                                                   &ssl->arrays->preMasterSz,
                                                   EC448_LITTLE_ENDIAN);
    }

    wc_curve448_free(peerX448Key);
    XFREE(peerX448Key, ssl->heap, DYNAMIC_TYPE_TLSX);
    wc_curve448_free((curve448_key*)keyShareEntry->key);
    if (keyShareEntry->key != NULL) {
        XFREE(keyShareEntry->key, ssl->heap, DYNAMIC_TYPE_PRIVATE_KEY);
        keyShareEntry->key = NULL;
    }
#else
    (void)ssl;
    (void)keyShareEntry;

    ret = PEER_KEY_ERROR;
#endif /* HAVE_CURVE448 */

    return ret;
}

/* Process the ECC key share extension on the client side.
 *
 * ssl            The SSL/TLS object.
 * keyShareEntry  The key share entry object to use to calculate shared secret.
 * returns 0 on success and other values indicate failure.
 */
static int TLSX_KeyShare_ProcessEcc(WOLFSSL* ssl, KeyShareEntry* keyShareEntry)
{
    int ret;

#ifdef HAVE_ECC
    int curveId;
    ecc_key* keyShareKey = (ecc_key*)keyShareEntry->key;

    if (ssl->peerEccKey != NULL)
        wc_ecc_free(ssl->peerEccKey);

    ssl->peerEccKey = (ecc_key*)XMALLOC(sizeof(ecc_key), ssl->heap,
                                        DYNAMIC_TYPE_ECC);
    if (ssl->peerEccKey == NULL) {
        WOLFSSL_MSG("PeerEccKey Memory error");
        return MEMORY_ERROR;
    }
    ret = wc_ecc_init_ex(ssl->peerEccKey, ssl->heap, ssl->devId);
    if (ret != 0)
        return ret;

    /* find supported curve */
    switch (keyShareEntry->group) {
    #if !defined(NO_ECC256)  || defined(HAVE_ALL_CURVES)
        #ifndef NO_ECC_SECP
        case WOLFSSL_ECC_SECP256R1:
            curveId = ECC_SECP256R1;
            break;
        #endif /* !NO_ECC_SECP */
    #endif
    #if defined(HAVE_ECC384) || defined(HAVE_ALL_CURVES)
        #ifndef NO_ECC_SECP
        case WOLFSSL_ECC_SECP384R1:
            curveId = ECC_SECP384R1;
            break;
        #endif /* !NO_ECC_SECP */
    #endif
    #if defined(HAVE_ECC521) || defined(HAVE_ALL_CURVES)
        #ifndef NO_ECC_SECP
        case WOLFSSL_ECC_SECP521R1:
            curveId = ECC_SECP521R1;
            break;
        #endif /* !NO_ECC_SECP */
    #endif
    #ifdef HAVE_X448
        case WOLFSSL_ECC_X448:
            curveId = ECC_X448;
            break;
    #endif
        default:
            /* unsupported curve */
            return ECC_PEERKEY_ERROR;
    }

#ifdef WOLFSSL_DEBUG_TLS
    WOLFSSL_MSG("Peer ECC Key");
    WOLFSSL_BUFFER(keyShareEntry->ke, keyShareEntry->keLen);
#endif

    /* Point is validated by import function. */
    if (wc_ecc_import_x963_ex(keyShareEntry->ke, keyShareEntry->keLen,
                              ssl->peerEccKey, curveId) != 0) {
        return ECC_PEERKEY_ERROR;
    }
    ssl->ecdhCurveOID = ssl->peerEccKey->dp->oidSum;

#if defined(ECC_TIMING_RESISTANT) && (!defined(HAVE_FIPS) || \
    (!defined(HAVE_FIPS_VERSION) || (HAVE_FIPS_VERSION != 2))) && \
    !defined(HAVE_SELFTEST)
    ret = wc_ecc_set_rng(keyShareKey, ssl->rng);
    if (ret != 0) {
        return ret;
    }
#endif

    do {
    #if defined(WOLFSSL_ASYNC_CRYPT)
        ret = wc_AsyncWait(ret, &keyShareKey->asyncDev, WC_ASYNC_FLAG_CALL_AGAIN);
    #endif
        if (ret >= 0)
            ret = wc_ecc_shared_secret(keyShareKey, ssl->peerEccKey,
                ssl->arrays->preMasterSecret, &ssl->arrays->preMasterSz);
    } while (ret == WC_PENDING_E);

#if 0
    /* TODO: Switch to support async here and use: */
    ret = EccSharedSecret(ssl, keyShareEntry->key, ssl->peerEccKey,
        keyShareEntry->ke, &keyShareEntry->keLen,
        ssl->arrays->preMasterSecret, &ssl->arrays->preMasterSz,
        ssl->options.side
    );
#endif

    wc_ecc_free(ssl->peerEccKey);
    XFREE(ssl->peerEccKey, ssl->heap, DYNAMIC_TYPE_ECC);
    ssl->peerEccKey = NULL;
    wc_ecc_free((ecc_key*)(keyShareEntry->key));
    if (keyShareEntry->key != NULL) {
        XFREE(keyShareEntry->key, ssl->heap, DYNAMIC_TYPE_PRIVATE_KEY);
        keyShareEntry->key = NULL;
    }

#else
    (void)ssl;
    (void)keyShareEntry;

    ret = PEER_KEY_ERROR;
#endif /* HAVE_ECC */

    return ret;
}

/* Process the key share extension on the client side.
 *
 * ssl            The SSL/TLS object.
 * keyShareEntry  The key share entry object to use to calculate shared secret.
 * returns 0 on success and other values indicate failure.
 */
static int TLSX_KeyShare_Process(WOLFSSL* ssl, KeyShareEntry* keyShareEntry)
{
    int ret;

#if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
    ssl->session.namedGroup = (byte)keyShareEntry->group;
#endif
    /* Use Key Share Data from server. */
    if (keyShareEntry->group & NAMED_DH_MASK)
        ret = TLSX_KeyShare_ProcessDh(ssl, keyShareEntry);
    else if (keyShareEntry->group == WOLFSSL_ECC_X25519)
        ret = TLSX_KeyShare_ProcessX25519(ssl, keyShareEntry);
    else if (keyShareEntry->group == WOLFSSL_ECC_X448)
        ret = TLSX_KeyShare_ProcessX448(ssl, keyShareEntry);
    else
        ret = TLSX_KeyShare_ProcessEcc(ssl, keyShareEntry);

#ifdef WOLFSSL_DEBUG_TLS
    WOLFSSL_MSG("KE Secret");
    WOLFSSL_BUFFER(ssl->arrays->preMasterSecret, ssl->arrays->preMasterSz);
#endif

    return ret;
}

/* Parse an entry of the KeyShare extension.
 *
 * ssl     The SSL/TLS object.
 * input   The extension data.
 * length  The length of the extension data.
 * kse     The new key share entry object.
 * returns a positive number to indicate amount of data parsed and a negative
 * number on error.
 */
static int TLSX_KeyShareEntry_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                    KeyShareEntry **kse)
{
    int    ret;
    word16 group;
    word16 keLen;
    int    offset = 0;
    byte*  ke;

    if (length < OPAQUE16_LEN + OPAQUE16_LEN)
        return BUFFER_ERROR;
    /* Named group */
    ato16(&input[offset], &group);
    offset += OPAQUE16_LEN;
    /* Key exchange data - public key. */
    ato16(&input[offset], &keLen);
    offset += OPAQUE16_LEN;
    if (keLen == 0)
        return INVALID_PARAMETER;
    if (keLen > length - offset)
        return BUFFER_ERROR;

    /* Store a copy in the key share object. */
    ke = (byte*)XMALLOC(keLen, ssl->heap, DYNAMIC_TYPE_PUBLIC_KEY);
    if (ke == NULL)
        return MEMORY_E;
    XMEMCPY(ke, &input[offset], keLen);

    /* Populate a key share object in the extension. */
    ret = TLSX_KeyShare_Use(ssl, group, keLen, ke, kse);
    if (ret != 0) {
        XFREE(ke, ssl->heap, DYNAMIC_TYPE_PUBLIC_KEY);
        return ret;
    }

    /* Total length of the parsed data. */
    return offset + keLen;
}

/* Searches the groups sent for the specified named group.
 *
 * ssl    SSL/TLS object.
 * name   Group name to match.
 * returns 1 when the extension has the group name and 0 otherwise.
 */
static int TLSX_KeyShare_Find(WOLFSSL* ssl, word16 group)
{
    TLSX*          extension;
    KeyShareEntry* list;

    extension = TLSX_Find(ssl->extensions, TLSX_KEY_SHARE);
    if (extension == NULL) {
        extension = TLSX_Find(ssl->ctx->extensions, TLSX_KEY_SHARE);
        if (extension == NULL)
            return 0;
    }

    list = (KeyShareEntry*)extension->data;
    while (list != NULL) {
        if (list->group == group)
            return 1;
        list = list->next;
    }

    return 0;
}


/* Searches the supported groups extension for the specified named group.
 *
 * ssl   The SSL/TLS object.
 * name  The group name to match.
 * returns 1 when the extension has the group name and 0 otherwise.
 */
static int TLSX_SupportedGroups_Find(WOLFSSL* ssl, word16 name)
{
#ifdef HAVE_SUPPORTED_CURVES
    TLSX*          extension;
    SupportedCurve* curve = NULL;

    if ((extension = TLSX_Find(ssl->extensions,
                                              TLSX_SUPPORTED_GROUPS)) == NULL) {
        if ((extension = TLSX_Find(ssl->ctx->extensions,
                                              TLSX_SUPPORTED_GROUPS)) == NULL) {
            return 0;
        }
    }

    for (curve = (SupportedCurve*)extension->data; curve; curve = curve->next) {
        if (curve->name == name)
            return 1;
    }
#endif

    (void)ssl;
    (void)name;

    return 0;
}


/* Parse the KeyShare extension.
 * Different formats in different messages.
 *
 * ssl      The SSL/TLS object.
 * input    The extension data.
 * length   The length of the extension data.
 * msgType  The type of the message this extension is being parsed from.
 * returns 0 on success and other values indicate failure.
 */
static int TLSX_KeyShare_Parse(WOLFSSL* ssl, byte* input, word16 length,
                               byte msgType)
{
    int ret;
    KeyShareEntry *keyShareEntry = NULL;
    word16 group;

    if (msgType == client_hello) {
        int    offset = 0;
        word16 len;
        TLSX*  extension;

        /* Add a KeyShare extension if it doesn't exist. */
        extension = TLSX_Find(ssl->extensions, TLSX_KEY_SHARE);
        if (extension == NULL) {
            /* Push new KeyShare extension. */
            ret = TLSX_Push(&ssl->extensions, TLSX_KEY_SHARE, NULL, ssl->heap);
            if (ret != 0)
                return ret;
        }

        if (length < OPAQUE16_LEN)
            return BUFFER_ERROR;

        /* ClientHello contains zero or more key share entries. */
        ato16(input, &len);
        if (len != length - OPAQUE16_LEN)
            return BUFFER_ERROR;
        offset += OPAQUE16_LEN;

        while (offset < (int)length) {
            ret = TLSX_KeyShareEntry_Parse(ssl, &input[offset], length - offset,
                                                                &keyShareEntry);
            if (ret < 0)
                return ret;

            offset += ret;
        }

        ret = 0;
    }
    else if (msgType == server_hello) {
        int len;

        if (length < OPAQUE16_LEN)
            return BUFFER_ERROR;

        /* The data is the named group the server wants to use. */
        ato16(input, &group);

        /* Check the selected group was supported by ClientHello extensions. */
        if (!TLSX_SupportedGroups_Find(ssl, group))
            return BAD_KEY_SHARE_DATA;

        /* Check if the group was sent. */
        if (!TLSX_KeyShare_Find(ssl, group))
            return BAD_KEY_SHARE_DATA;

        /* ServerHello contains one key share entry. */
        len = TLSX_KeyShareEntry_Parse(ssl, input, length, &keyShareEntry);
        if (len != (int)length)
            return BUFFER_ERROR;

        /* Not in list sent if there isn't a private key. */
        if (keyShareEntry == NULL || keyShareEntry->key == NULL)
            return BAD_KEY_SHARE_DATA;

        /* Process the entry to calculate the secret. */
        ret = TLSX_KeyShare_Process(ssl, keyShareEntry);
        if (ret == 0)
            ssl->session.namedGroup = ssl->namedGroup = group;
    }
    else if (msgType == hello_retry_request) {
        if (length != OPAQUE16_LEN)
            return BUFFER_ERROR;

        /* The data is the named group the server wants to use. */
        ato16(input, &group);

        /* Check the selected group was supported by ClientHello extensions. */
        if (!TLSX_SupportedGroups_Find(ssl, group))
            return BAD_KEY_SHARE_DATA;

        /* Check if the group was sent. */
        if (TLSX_KeyShare_Find(ssl, group))
            return BAD_KEY_SHARE_DATA;

        /* Clear out unusable key shares. */
        ret = TLSX_KeyShare_Empty(ssl);
        if (ret != 0)
            return ret;

        /* Try to use the server's group. */
        ret = TLSX_KeyShare_Use(ssl, group, 0, NULL, NULL);
    }
    else {
        /* Not a message type that is allowed to have this extension. */
        return SANITY_MSG_E;
    }

    return ret;
}

/* Create a new key share entry and put it into the list.
 *
 * list           The linked list of key share entries.
 * group          The named group.
 * heap           The memory to allocate with.
 * keyShareEntry  The new key share entry object.
 * returns 0 on success and other values indicate failure.
 */
static int TLSX_KeyShare_New(KeyShareEntry** list, int group, void *heap,
                             KeyShareEntry** keyShareEntry)
{
    KeyShareEntry* kse;
    KeyShareEntry** next;

    kse = (KeyShareEntry*)XMALLOC(sizeof(KeyShareEntry), heap,
                                  DYNAMIC_TYPE_TLSX);
    if (kse == NULL)
        return MEMORY_E;

    XMEMSET(kse, 0, sizeof(*kse));
    kse->group = (word16)group;

    /* Add it to the back and maintain the links. */
    while (*list != NULL) {
        /* Assign to temporary to work around compiler bug found by customer. */
        next = &((*list)->next);
        list = next;
    }
    *list = kse;
    *keyShareEntry = kse;

    (void)heap;

    return 0;
}

/* Use the data to create a new key share object in the extensions.
 *
 * ssl    The SSL/TLS object.
 * group  The named group.
 * len    The length of the public key data.
 * data   The public key data.
 * kse    The new key share entry object.
 * returns 0 on success and other values indicate failure.
 */
int TLSX_KeyShare_Use(WOLFSSL* ssl, word16 group, word16 len, byte* data,
                      KeyShareEntry **kse)
{
    int            ret = 0;
    TLSX*          extension;
    KeyShareEntry* keyShareEntry = NULL;

    /* Find the KeyShare extension if it exists. */
    extension = TLSX_Find(ssl->extensions, TLSX_KEY_SHARE);
    if (extension == NULL) {
        /* Push new KeyShare extension. */
        ret = TLSX_Push(&ssl->extensions, TLSX_KEY_SHARE, NULL, ssl->heap);
        if (ret != 0)
            return ret;

        extension = TLSX_Find(ssl->extensions, TLSX_KEY_SHARE);
        if (extension == NULL)
            return MEMORY_E;
    }
    extension->resp = 0;

    /* Try to find the key share entry with this group. */
    keyShareEntry = (KeyShareEntry*)extension->data;
    while (keyShareEntry != NULL) {
        if (keyShareEntry->group == group)
            break;
        keyShareEntry = keyShareEntry->next;
    }

    /* Create a new key share entry if not found. */
    if (keyShareEntry == NULL) {
        ret = TLSX_KeyShare_New((KeyShareEntry**)&extension->data, group,
                                ssl->heap, &keyShareEntry);
        if (ret != 0)
            return ret;
    }

    if (data != NULL) {
        if (keyShareEntry->ke != NULL) {
            XFREE(keyShareEntry->ke, ssl->heap, DYNAMIC_TYPE_PUBLIC_KEY);
        }
        keyShareEntry->ke = data;
        keyShareEntry->keLen = len;
    }
    else {
        /* Generate a key pair. */
        ret = TLSX_KeyShare_GenKey(ssl, keyShareEntry);
        if (ret != 0)
            return ret;
    }

    if (kse != NULL)
        *kse = keyShareEntry;

    return 0;
}

/* Set an empty Key Share extension.
 *
 * ssl  The SSL/TLS object.
 * returns 0 on success and other values indicate failure.
 */
int TLSX_KeyShare_Empty(WOLFSSL* ssl)
{
    int   ret = 0;
    TLSX* extension;

    /* Find the KeyShare extension if it exists. */
    extension = TLSX_Find(ssl->extensions, TLSX_KEY_SHARE);
    if (extension == NULL) {
        /* Push new KeyShare extension. */
        ret = TLSX_Push(&ssl->extensions, TLSX_KEY_SHARE, NULL, ssl->heap);
    }
    else if (extension->data != NULL) {
        TLSX_KeyShare_FreeAll((KeyShareEntry*)extension->data, ssl->heap);
        extension->data = NULL;
    }

    return ret;
}

/* Returns whether this group is supported.
 *
 * namedGroup  The named group to check.
 * returns 1 when supported or 0 otherwise.
 */
static int TLSX_KeyShare_IsSupported(int namedGroup)
{
    switch (namedGroup) {
    #ifdef HAVE_FFDHE_2048
        case WOLFSSL_FFDHE_2048:
            break;
    #endif
    #ifdef HAVE_FFDHE_3072
        case WOLFSSL_FFDHE_3072:
            break;
    #endif
    #ifdef HAVE_FFDHE_4096
        case WOLFSSL_FFDHE_4096:
            break;
    #endif
    #ifdef HAVE_FFDHE_6144
        case WOLFSSL_FFDHE_6144:
            break;
    #endif
    #ifdef HAVE_FFDHE_8192
        case WOLFSSL_FFDHE_8192:
            break;
    #endif
    #if !defined(NO_ECC256)  || defined(HAVE_ALL_CURVES)
        #ifndef NO_ECC_SECP
        case WOLFSSL_ECC_SECP256R1:
            break;
        #endif /* !NO_ECC_SECP */
    #endif
    #ifdef HAVE_CURVE25519
        case WOLFSSL_ECC_X25519:
            break;
    #endif
    #ifdef HAVE_CURVE448
        case WOLFSSL_ECC_X448:
            break;
    #endif
    #if defined(HAVE_ECC384) || defined(HAVE_ALL_CURVES)
        #ifndef NO_ECC_SECP
        case WOLFSSL_ECC_SECP384R1:
            break;
        #endif /* !NO_ECC_SECP */
    #endif
    #if defined(HAVE_ECC521) || defined(HAVE_ALL_CURVES)
        #ifndef NO_ECC_SECP
        case WOLFSSL_ECC_SECP521R1:
            break;
        #endif /* !NO_ECC_SECP */
    #endif
        default:
            return 0;
    }

    return 1;
}

/* Examines the application specified group ranking and returns the rank of the
 * group.
 * If no group ranking set then all groups are rank 0 (highest).
 *
 * ssl    The SSL/TLS object.
 * group  The group to check ranking for.
 * returns ranking from 0 to MAX_GROUP_COUNT-1 or -1 when group not in list.
 */
static int TLSX_KeyShare_GroupRank(WOLFSSL* ssl, int group)
{
    byte i;

    if (ssl->numGroups == 0) {
#if defined(HAVE_ECC) && defined(HAVE_SUPPORTED_CURVES)
    #if !defined(NO_ECC256)  || defined(HAVE_ALL_CURVES)
        #ifndef NO_ECC_SECP
            ssl->group[ssl->numGroups++] = WOLFSSL_ECC_SECP256R1;
        #endif
    #endif
#endif
    #ifndef HAVE_FIPS
        #if defined(HAVE_CURVE25519)
            ssl->group[ssl->numGroups++] = WOLFSSL_ECC_X25519;
        #endif
    #endif
    #ifndef HAVE_FIPS
        #if defined(HAVE_CURVE448)
            ssl->group[ssl->numGroups++] = WOLFSSL_ECC_X448;
        #endif
    #endif
#if defined(HAVE_ECC) && defined(HAVE_SUPPORTED_CURVES)
    #if defined(HAVE_ECC384) || defined(HAVE_ALL_CURVES)
        #ifndef NO_ECC_SECP
            ssl->group[ssl->numGroups++] = WOLFSSL_ECC_SECP384R1;
        #endif
    #endif
    #if defined(HAVE_ECC521) || defined(HAVE_ALL_CURVES)
        #ifndef NO_ECC_SECP
            ssl->group[ssl->numGroups++] = WOLFSSL_ECC_SECP521R1;
        #endif
    #endif
#endif
            /* Add FFDHE supported groups. */
        #ifdef HAVE_FFDHE_2048
            ssl->group[ssl->numGroups++] = WOLFSSL_FFDHE_2048;
        #endif
        #ifdef HAVE_FFDHE_3072
            ssl->group[ssl->numGroups++] = WOLFSSL_FFDHE_3072;
        #endif
        #ifdef HAVE_FFDHE_4096
            ssl->group[ssl->numGroups++] = WOLFSSL_FFDHE_4096;
        #endif
        #ifdef HAVE_FFDHE_6144
            ssl->group[ssl->numGroups++] = WOLFSSL_FFDHE_6144;
        #endif
        #ifdef HAVE_FFDHE_8192
            ssl->group[ssl->numGroups++] = WOLFSSL_FFDHE_8192;
        #endif
    }

    for (i = 0; i < ssl->numGroups; i++)
        if (ssl->group[i] == (word16)group)
            return i;

    return -1;
}

/* Set a key share that is supported by the client into extensions.
 *
 * ssl  The SSL/TLS object.
 * returns BAD_KEY_SHARE_DATA if no supported group has a key share,
 * 0 if a supported group has a key share and other values indicate an error.
 */
static int TLSX_KeyShare_SetSupported(WOLFSSL* ssl)
{
    int             ret;
#ifdef HAVE_SUPPORTED_CURVES
    TLSX*           extension;
    SupportedCurve* curve = NULL;
    SupportedCurve* preferredCurve = NULL;
    int             preferredRank = WOLFSSL_MAX_GROUP_COUNT;
    int             rank;

    extension = TLSX_Find(ssl->extensions, TLSX_SUPPORTED_GROUPS);
    if (extension != NULL)
        curve = (SupportedCurve*)extension->data;
    /* Use server's preference order. */
    for (; curve != NULL; curve = curve->next) {
        if (!TLSX_KeyShare_IsSupported(curve->name))
            continue;

        rank = TLSX_KeyShare_GroupRank(ssl, curve->name);
        if (rank == -1)
            continue;
        if (rank < preferredRank) {
            preferredCurve = curve;
            preferredRank = rank;
        }
    }
    curve = preferredCurve;

    if (curve == NULL)
        return BAD_KEY_SHARE_DATA;

    /* Delete the old key share data list. */
    extension = TLSX_Find(ssl->extensions, TLSX_KEY_SHARE);
    if (extension != NULL) {
        TLSX_KeyShare_FreeAll((KeyShareEntry*)extension->data, ssl->heap);
        extension->data = NULL;
    }

    /* Add in the chosen group. */
    ret = TLSX_KeyShare_Use(ssl, curve->name, 0, NULL, NULL);
    if (ret != 0)
        return ret;

    /* Set extension to be in response. */
    extension = TLSX_Find(ssl->extensions, TLSX_KEY_SHARE);
    extension->resp = 1;
#else

    (void)ssl;
    ret = NOT_COMPILED_IN;
#endif

    return ret;
}

/* Ensure there is a key pair that can be used for key exchange.
 *
 * ssl  The SSL/TLS object.
 * returns 0 on success and other values indicate failure.
 */
int TLSX_KeyShare_Establish(WOLFSSL *ssl)
{
    int            ret;
    TLSX*          extension;
    KeyShareEntry* clientKSE = NULL;
    KeyShareEntry* serverKSE;
    KeyShareEntry* list = NULL;
    KeyShareEntry* preferredKSE = NULL;
    int preferredRank = WOLFSSL_MAX_GROUP_COUNT;
    int rank;

    /* Find the KeyShare extension if it exists. */
    extension = TLSX_Find(ssl->extensions, TLSX_KEY_SHARE);
    if (extension != NULL)
        list = (KeyShareEntry*)extension->data;

    if (extension && extension->resp == 1)
        return 0;

    /* Use server's preference order. */
    for (clientKSE = list; clientKSE != NULL; clientKSE = clientKSE->next) {
        if (clientKSE->ke == NULL)
            continue;

        /* Check consistency now - extensions in any order. */
        if (!TLSX_SupportedGroups_Find(ssl, clientKSE->group))
            return BAD_KEY_SHARE_DATA;

        if ((clientKSE->group & NAMED_DH_MASK) == 0) {
            /* Check max value supported. */
            if (clientKSE->group > WOLFSSL_ECC_MAX) {
                continue;
            }
        #ifdef OPENSSL_EXTRA
            /* Check if server supports group. */
            if (ssl->ctx->disabledCurves & ((word32)1 << clientKSE->group))
                continue;
        #endif
        }
        if (!TLSX_KeyShare_IsSupported(clientKSE->group))
            continue;

        rank = TLSX_KeyShare_GroupRank(ssl, clientKSE->group);
        if (rank == -1)
            continue;
        if (rank < preferredRank) {
            preferredKSE = clientKSE;
            preferredRank = rank;
        }
    }
    clientKSE = preferredKSE;

    /* No supported group found - send HelloRetryRequest. */
    if (clientKSE == NULL) {
        ret = TLSX_KeyShare_SetSupported(ssl);
        /* Return KEY_SHARE_ERROR to indicate HelloRetryRequest required. */
        if (ret == 0)
            return KEY_SHARE_ERROR;
        return ret;
    }

    list = NULL;
    /* Generate a new key pair. */
    ret = TLSX_KeyShare_New(&list, clientKSE->group, ssl->heap, &serverKSE);
    if (ret != 0)
        return ret;

    if (clientKSE->key == NULL) {
        ret = TLSX_KeyShare_GenKey(ssl, serverKSE);
        if (ret != 0)
            return ret;
    }
    else {
        serverKSE->key = clientKSE->key;
        serverKSE->keyLen = clientKSE->keyLen;
        serverKSE->pubKey = clientKSE->pubKey;
        serverKSE->pubKeyLen = clientKSE->pubKeyLen;
        clientKSE->key = NULL;
        clientKSE->pubKey = NULL;
    }
    serverKSE->ke = clientKSE->ke;
    serverKSE->keLen = clientKSE->keLen;
    clientKSE->ke = NULL;
    clientKSE->keLen = 0;

    TLSX_KeyShare_FreeAll((KeyShareEntry*)extension->data, ssl->heap);
    extension->data = (void *)serverKSE;

    extension->resp = 1;

    return 0;
}

/* Derive the shared secret of the key exchange.
 *
 * ssl  The SSL/TLS object.
 * returns 0 on success and other values indicate failure.
 */
int TLSX_KeyShare_DeriveSecret(WOLFSSL *ssl)
{
    int            ret;
    TLSX*          extension;
    KeyShareEntry* list = NULL;

    /* Find the KeyShare extension if it exists. */
    extension = TLSX_Find(ssl->extensions, TLSX_KEY_SHARE);
    if (extension != NULL)
        list = (KeyShareEntry*)extension->data;

    if (list == NULL)
        return KEY_SHARE_ERROR;

    /* Calculate secret. */
    ret = TLSX_KeyShare_Process(ssl, list);
    if (ret != 0)
        return ret;

    return ret;
}

#define KS_FREE_ALL  TLSX_KeyShare_FreeAll
#define KS_GET_SIZE  TLSX_KeyShare_GetSize
#define KS_WRITE     TLSX_KeyShare_Write
#define KS_PARSE     TLSX_KeyShare_Parse

#else

#define KS_FREE_ALL(a, b)
#define KS_GET_SIZE(a, b)    0
#define KS_WRITE(a, b, c)    0
#define KS_PARSE(a, b, c, d) 0

#endif /* WOLFSSL_TLS13 */

/******************************************************************************/
/* Pre-Shared Key                                                             */
/******************************************************************************/

#if defined(WOLFSSL_TLS13) && (defined(HAVE_SESSION_TICKET) || !defined(NO_PSK))
/* Free the pre-shared key dynamic data.
 *
 * list  The linked list of key share entry objects.
 * heap  The heap used for allocation.
 */
static void TLSX_PreSharedKey_FreeAll(PreSharedKey* list, void* heap)
{
    PreSharedKey* current;

    while ((current = list) != NULL) {
        list = current->next;
        XFREE(current->identity, heap, DYNAMIC_TYPE_TLSX);
        XFREE(current, heap, DYNAMIC_TYPE_TLSX);
    }

    (void)heap;
}

/* Get the size of the encoded pre shared key extension.
 *
 * list     The linked list of pre-shared key extensions.
 * msgType  The type of the message this extension is being written into.
 * returns the number of bytes of the encoded pre-shared key extension or
 * SANITY_MSG_E to indicate invalid message type.
 */
static int TLSX_PreSharedKey_GetSize(PreSharedKey* list, byte msgType,
                                     word16* pSz)
{
    if (msgType == client_hello) {
        /* Length of identities + Length of binders. */
        word16 len = OPAQUE16_LEN + OPAQUE16_LEN;
        while (list != NULL) {
            /* Each entry has: identity, ticket age and binder. */
            len += OPAQUE16_LEN + list->identityLen + OPAQUE32_LEN +
                   OPAQUE8_LEN + list->binderLen;
            list = list->next;
        }
        *pSz += len;
        return 0;
    }

    if (msgType == server_hello) {
        *pSz += OPAQUE16_LEN;
        return 0;
    }

    return SANITY_MSG_E;
}

/* The number of bytes to be written for the binders.
 *
 * list     The linked list of pre-shared key extensions.
 * msgType  The type of the message this extension is being written into.
 * returns the number of bytes of the encoded pre-shared key extension or
 * SANITY_MSG_E to indicate invalid message type.
 */
int TLSX_PreSharedKey_GetSizeBinders(PreSharedKey* list, byte msgType,
                                     word16* pSz)
{
    word16 len;

    if (msgType != client_hello)
        return SANITY_MSG_E;

    /* Length of all binders. */
    len = OPAQUE16_LEN;
    while (list != NULL) {
        len += OPAQUE8_LEN + list->binderLen;
        list = list->next;
    }

    *pSz = len;
    return 0;
}

/* Writes the pre-shared key extension into the output buffer - binders only.
 * Assumes that the the output buffer is big enough to hold data.
 *
 * list     The linked list of key share entries.
 * output   The buffer to write into.
 * msgType  The type of the message this extension is being written into.
 * returns the number of bytes written into the buffer.
 */
int TLSX_PreSharedKey_WriteBinders(PreSharedKey* list, byte* output,
                                   byte msgType, word16* pSz)
{
    PreSharedKey* current = list;
    word16 idx = 0;
    word16 lenIdx;
    word16 len;

    if (msgType != client_hello)
        return SANITY_MSG_E;

    /* Skip length of all binders. */
    lenIdx = idx;
    idx += OPAQUE16_LEN;
    while (current != NULL) {
        /* Binder data length. */
        output[idx++] = current->binderLen;
        /* Binder data. */
        XMEMCPY(output + idx, current->binder, current->binderLen);
        idx += current->binderLen;

        current = current->next;
    }
    /* Length of the binders. */
    len = idx - lenIdx - OPAQUE16_LEN;
    c16toa(len, output + lenIdx);

    *pSz = idx;
    return 0;
}


/* Writes the pre-shared key extension into the output buffer.
 * Assumes that the the output buffer is big enough to hold data.
 *
 * list     The linked list of key share entries.
 * output   The buffer to write into.
 * msgType  The type of the message this extension is being written into.
 * returns the number of bytes written into the buffer.
 */
static int TLSX_PreSharedKey_Write(PreSharedKey* list, byte* output,
                                   byte msgType, word16* pSz)
{
    if (msgType == client_hello) {
        PreSharedKey* current = list;
        word16 idx = 0;
        word16 lenIdx;
        word16 len;
        int ret;

        /* Write identites only. Binders after HMACing over this. */
        lenIdx = idx;
        idx += OPAQUE16_LEN;
        while (current != NULL) {
            /* Identity length */
            c16toa(current->identityLen, output + idx);
            idx += OPAQUE16_LEN;
            /* Identity data */
            XMEMCPY(output + idx, current->identity, current->identityLen);
            idx += current->identityLen;

            /* Obfuscated ticket age. */
            c32toa(current->ticketAge, output + idx);
            idx += OPAQUE32_LEN;

            current = current->next;
        }
        /* Length of the identites. */
        len = idx - lenIdx - OPAQUE16_LEN;
        c16toa(len, output + lenIdx);

        /* Don't include binders here.
         * The binders are based on the hash of all the ClientHello data up to
         * and include the identities written above.
         */
        ret = TLSX_PreSharedKey_GetSizeBinders(list, msgType, &len);
        if (ret < 0)
            return ret;
        *pSz += idx + len;
    }
    else if (msgType == server_hello) {
        word16 i;

        /* Find the index of the chosen identity. */
        for (i=0; list != NULL && !list->chosen; i++)
            list = list->next;
        if (list == NULL)
            return BUILD_MSG_ERROR;

        /* The index of the identity chosen by the server from the list supplied
         * by the client.
         */
        c16toa(i, output);
        *pSz += OPAQUE16_LEN;
    }
    else
        return SANITY_MSG_E;

    return 0;
}

/* Parse the pre-shared key extension.
 * Different formats in different messages.
 *
 * ssl      The SSL/TLS object.
 * input    The extension data.
 * length   The length of the extension data.
 * msgType  The type of the message this extension is being parsed from.
 * returns 0 on success and other values indicate failure.
 */
static int TLSX_PreSharedKey_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                   byte msgType)
{
    TLSX*         extension;
    PreSharedKey* list;

    if (msgType == client_hello) {
        int    ret;
        word16 len;
        word16 idx = 0;

        TLSX_Remove(&ssl->extensions, TLSX_PRE_SHARED_KEY, ssl->heap);

        /* Length of identities and of binders. */
        if (length - idx < OPAQUE16_LEN + OPAQUE16_LEN)
            return BUFFER_E;

        /* Length of identities. */
        ato16(input + idx, &len);
        idx += OPAQUE16_LEN;
        if (len < MIN_PSK_ID_LEN || length - idx < len)
            return BUFFER_E;

        /* Create a pre-shared key object for each identity. */
        while (len > 0) {
            byte*  identity;
            word16 identityLen;
            word32 age;

            if (len < OPAQUE16_LEN)
                return BUFFER_E;

            /* Length of identity. */
            ato16(input + idx, &identityLen);
            idx += OPAQUE16_LEN;
            if (len < OPAQUE16_LEN + identityLen + OPAQUE32_LEN ||
                    identityLen > MAX_PSK_ID_LEN)
                return BUFFER_E;
            /* Cache identity pointer. */
            identity = input + idx;
            idx += identityLen;
            /* Ticket age. */
            ato32(input + idx, &age);
            idx += OPAQUE32_LEN;

            ret = TLSX_PreSharedKey_Use(ssl, identity, identityLen, age, no_mac,
                                        0, 0, 1, NULL);
            if (ret != 0)
                return ret;

            /* Done with this identity. */
            len -= OPAQUE16_LEN + identityLen + OPAQUE32_LEN;
        }

        /* Find the list of identities sent to server. */
        extension = TLSX_Find(ssl->extensions, TLSX_PRE_SHARED_KEY);
        if (extension == NULL)
            return PSK_KEY_ERROR;
        list = (PreSharedKey*)extension->data;

        /* Length of binders. */
        if (idx + OPAQUE16_LEN > length)
            return BUFFER_E;
        ato16(input + idx, &len);
        idx += OPAQUE16_LEN;
        if (len < MIN_PSK_BINDERS_LEN || length - idx < len)
            return BUFFER_E;

        /* Set binder for each identity. */
        while (list != NULL && len > 0) {
            /* Length of binder */
            list->binderLen = input[idx++];
            if (list->binderLen < WC_SHA256_DIGEST_SIZE ||
                    list->binderLen > WC_MAX_DIGEST_SIZE)
                return BUFFER_E;
            if (len < OPAQUE8_LEN + list->binderLen)
                return BUFFER_E;

            /* Copy binder into static buffer. */
            XMEMCPY(list->binder, input + idx, list->binderLen);
            idx += list->binderLen;

            /* Done with binder entry. */
            len -= OPAQUE8_LEN + list->binderLen;

            /* Next identity. */
            list = list->next;
        }
        if (list != NULL || len != 0)
            return BUFFER_E;

        return 0;
    }

    if (msgType == server_hello) {
        word16 idx;

        /* Index of identity chosen by server. */
        if (length != OPAQUE16_LEN)
            return BUFFER_E;
        ato16(input, &idx);

    #ifdef WOLFSSL_EARLY_DATA
        ssl->options.pskIdIndex = idx + 1;
    #endif

        /* Find the list of identities sent to server. */
        extension = TLSX_Find(ssl->extensions, TLSX_PRE_SHARED_KEY);
        if (extension == NULL)
            return PSK_KEY_ERROR;
        list = (PreSharedKey*)extension->data;

        /* Mark the identity as chosen. */
        for (; list != NULL && idx > 0; idx--)
            list = list->next;
        if (list == NULL)
            return PSK_KEY_ERROR;
        list->chosen = 1;

    #ifdef HAVE_SESSION_TICKET
        if (list->resumption) {
           /* Check that the session's details are the same as the server's. */
           if (ssl->options.cipherSuite0  != ssl->session.cipherSuite0       ||
               ssl->options.cipherSuite   != ssl->session.cipherSuite        ||
               ssl->session.version.major != ssl->ctx->method->version.major ||
               ssl->session.version.minor != ssl->ctx->method->version.minor) {
               return PSK_KEY_ERROR;
           }
        }
    #endif

        return 0;
    }

    return SANITY_MSG_E;
}

/* Create a new pre-shared key and put it into the list.
 *
 * list          The linked list of pre-shared key.
 * identity      The identity.
 * len           The length of the identity data.
 * heap          The memory to allocate with.
 * preSharedKey  The new pre-shared key object.
 * returns 0 on success and other values indicate failure.
 */
static int TLSX_PreSharedKey_New(PreSharedKey** list, byte* identity,
                                 word16 len, void *heap,
                                 PreSharedKey** preSharedKey)
{
    PreSharedKey* psk;
    PreSharedKey** next;

    psk = (PreSharedKey*)XMALLOC(sizeof(PreSharedKey), heap, DYNAMIC_TYPE_TLSX);
    if (psk == NULL)
        return MEMORY_E;
    XMEMSET(psk, 0, sizeof(*psk));

    /* Make a copy of the identity data. */
    psk->identity = (byte*)XMALLOC(len, heap, DYNAMIC_TYPE_TLSX);
    if (psk->identity == NULL) {
        XFREE(psk, heap, DYNAMIC_TYPE_TLSX);
        return MEMORY_E;
    }
    XMEMCPY(psk->identity, identity, len);
    psk->identityLen = len;

    /* Add it to the end and maintain the links. */
    while (*list != NULL) {
        /* Assign to temporary to work around compiler bug found by customer. */
        next = &((*list)->next);
        list = next;
    }
    *list = psk;
    *preSharedKey = psk;

    (void)heap;

    return 0;
}

static WC_INLINE byte GetHmacLength(int hmac)
{
    switch (hmac) {
    #ifndef NO_SHA256
        case sha256_mac:
            return WC_SHA256_DIGEST_SIZE;
    #endif
    #ifdef WOLFSSL_SHA384
        case sha384_mac:
            return WC_SHA384_DIGEST_SIZE;
    #endif
    #ifdef WOLFSSL_SHA512
        case sha512_mac:
            return WC_SHA512_DIGEST_SIZE;
    #endif
    }
    return 0;
}

/* Use the data to create a new pre-shared key object in the extensions.
 *
 * ssl           The SSL/TLS object.
 * identity      The identity.
 * len           The length of the identity data.
 * age           The age of the identity.
 * hmac          The HMAC algorithm.
 * ciphersuite0  The first byte of the ciphersuite to use.
 * ciphersuite   The second byte of the ciphersuite to use.
 * resumption    The PSK is for resumption of a session.
 * preSharedKey  The new pre-shared key object.
 * returns 0 on success and other values indicate failure.
 */
int TLSX_PreSharedKey_Use(WOLFSSL* ssl, byte* identity, word16 len, word32 age,
                          byte hmac, byte cipherSuite0,
                          byte cipherSuite, byte resumption,
                          PreSharedKey **preSharedKey)
{
    int           ret = 0;
    TLSX*         extension;
    PreSharedKey* psk = NULL;

    /* Find the pre-shared key extension if it exists. */
    extension = TLSX_Find(ssl->extensions, TLSX_PRE_SHARED_KEY);
    if (extension == NULL) {
        /* Push new pre-shared key extension. */
        ret = TLSX_Push(&ssl->extensions, TLSX_PRE_SHARED_KEY, NULL, ssl->heap);
        if (ret != 0)
            return ret;

        extension = TLSX_Find(ssl->extensions, TLSX_PRE_SHARED_KEY);
        if (extension == NULL)
            return MEMORY_E;
    }

    /* Try to find the pre-shared key with this identity. */
    psk = (PreSharedKey*)extension->data;
    while (psk != NULL) {
        if ((psk->identityLen == len) &&
               (XMEMCMP(psk->identity, identity, len) == 0)) {
            break;
        }
        psk = psk->next;
    }

    /* Create a new pre-shared key object if not found. */
    if (psk == NULL) {
        ret = TLSX_PreSharedKey_New((PreSharedKey**)&extension->data, identity,
                                    len, ssl->heap, &psk);
        if (ret != 0)
            return ret;
    }

    /* Update/set age and HMAC algorithm. */
    psk->ticketAge    = age;
    psk->hmac         = hmac;
    psk->cipherSuite0 = cipherSuite0;
    psk->cipherSuite  = cipherSuite;
    psk->resumption   = resumption;
    psk->binderLen    = GetHmacLength(psk->hmac);

    if (preSharedKey != NULL)
        *preSharedKey = psk;

    return 0;
}

#define PSK_FREE_ALL  TLSX_PreSharedKey_FreeAll
#define PSK_GET_SIZE  TLSX_PreSharedKey_GetSize
#define PSK_WRITE     TLSX_PreSharedKey_Write
#define PSK_PARSE     TLSX_PreSharedKey_Parse

#else

#define PSK_FREE_ALL(a, b)
#define PSK_GET_SIZE(a, b, c) 0
#define PSK_WRITE(a, b, c, d) 0
#define PSK_PARSE(a, b, c, d) 0

#endif

/******************************************************************************/
/* PSK Key Exchange Modes                                                     */
/******************************************************************************/

#if defined(WOLFSSL_TLS13) && (defined(HAVE_SESSION_TICKET) || !defined(NO_PSK))
/* Get the size of the encoded PSK KE modes extension.
 * Only in ClientHello.
 *
 * modes    The PSK KE mode bit string.
 * msgType  The type of the message this extension is being written into.
 * returns the number of bytes of the encoded PSK KE mode extension.
 */
static int TLSX_PskKeModes_GetSize(byte modes, byte msgType, word16* pSz)
{
    if (msgType == client_hello) {
        /* Format: Len | Modes* */
        word16 len = OPAQUE8_LEN;
        /* Check whether each possible mode is to be written. */
        if (modes & (1 << PSK_KE))
            len += OPAQUE8_LEN;
        if (modes & (1 << PSK_DHE_KE))
            len += OPAQUE8_LEN;
        *pSz += len;
        return 0;
    }

    return SANITY_MSG_E;
}

/* Writes the PSK KE modes extension into the output buffer.
 * Assumes that the the output buffer is big enough to hold data.
 * Only in ClientHello.
 *
 * modes    The PSK KE mode bit string.
 * output   The buffer to write into.
 * msgType  The type of the message this extension is being written into.
 * returns the number of bytes written into the buffer.
 */
static int TLSX_PskKeModes_Write(byte modes, byte* output, byte msgType,
                                 word16* pSz)
{
    if (msgType == client_hello) {
        /* Format: Len | Modes* */
        int idx = OPAQUE8_LEN;

        /* Write out each possible mode. */
        if (modes & (1 << PSK_KE))
            output[idx++] = PSK_KE;
        if (modes & (1 << PSK_DHE_KE))
            output[idx++] = PSK_DHE_KE;
        /* Write out length of mode list. */
        output[0] = idx - OPAQUE8_LEN;

        *pSz += idx;
        return 0;
    }

    return SANITY_MSG_E;
}

/* Parse the PSK KE modes extension.
 * Only in ClientHello.
 *
 * ssl      The SSL/TLS object.
 * input    The extension data.
 * length   The length of the extension data.
 * msgType  The type of the message this extension is being parsed from.
 * returns 0 on success and other values indicate failure.
 */
static int TLSX_PskKeModes_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                 byte msgType)
{
    int    ret;

    if (msgType == client_hello) {
        /* Format: Len | Modes* */
        int   idx = 0;
        word16 len;
        byte  modes = 0;

        /* Ensure length byte exists. */
        if (length < OPAQUE8_LEN)
            return BUFFER_E;

        /* Get length of mode list and ensure that is the only data. */
        len = input[0];
        if (length - OPAQUE8_LEN != len)
            return BUFFER_E;

        idx = OPAQUE8_LEN;
        /* Set a bit for each recognized modes. */
        while (len > 0) {
            /* Ignore unrecognized modes.  */
            if (input[idx] <= PSK_DHE_KE)
               modes |= 1 << input[idx];
            idx++;
            len--;
        }

        ret = TLSX_PskKeModes_Use(ssl, modes);
        if (ret != 0)
            return ret;

        return 0;
    }

    return SANITY_MSG_E;
}

/* Use the data to create a new PSK Key Exchange Modes object in the extensions.
 *
 * ssl    The SSL/TLS object.
 * modes  The PSK key exchange modes.
 * returns 0 on success and other values indicate failure.
 */
int TLSX_PskKeModes_Use(WOLFSSL* ssl, byte modes)
{
    int           ret = 0;
    TLSX*         extension;

    /* Find the PSK key exchange modes extension if it exists. */
    extension = TLSX_Find(ssl->extensions, TLSX_PSK_KEY_EXCHANGE_MODES);
    if (extension == NULL) {
        /* Push new PSK key exchange modes extension. */
        ret = TLSX_Push(&ssl->extensions, TLSX_PSK_KEY_EXCHANGE_MODES, NULL,
            ssl->heap);
        if (ret != 0)
            return ret;

        extension = TLSX_Find(ssl->extensions, TLSX_PSK_KEY_EXCHANGE_MODES);
        if (extension == NULL)
            return MEMORY_E;
    }

    extension->val = modes;

    return 0;
}

#define PKM_GET_SIZE  TLSX_PskKeModes_GetSize
#define PKM_WRITE     TLSX_PskKeModes_Write
#define PKM_PARSE     TLSX_PskKeModes_Parse

#else

#define PKM_GET_SIZE(a, b, c) 0
#define PKM_WRITE(a, b, c, d) 0
#define PKM_PARSE(a, b, c, d) 0

#endif

/******************************************************************************/
/* Post-Handshake Authentication                                              */
/******************************************************************************/

#if defined(WOLFSSL_TLS13) && defined(WOLFSSL_POST_HANDSHAKE_AUTH)
/* Get the size of the encoded Post-Handshake Authentication extension.
 * Only in ClientHello.
 *
 * msgType  The type of the message this extension is being written into.
 * returns the number of bytes of the encoded Post-Handshake Authentication
 * extension.
 */
static int TLSX_PostHandAuth_GetSize(byte msgType, word16* pSz)
{
    if (msgType == client_hello) {
        *pSz += 0;
        return 0;
    }

    return SANITY_MSG_E;
}

/* Writes the Post-Handshake Authentication extension into the output buffer.
 * Assumes that the the output buffer is big enough to hold data.
 * Only in ClientHello.
 *
 * output   The buffer to write into.
 * msgType  The type of the message this extension is being written into.
 * returns the number of bytes written into the buffer.
 */
static int TLSX_PostHandAuth_Write(byte* output, byte msgType, word16* pSz)
{
    (void)output;

    if (msgType == client_hello) {
        *pSz += 0;
        return 0;
    }

    return SANITY_MSG_E;
}

/* Parse the Post-Handshake Authentication extension.
 * Only in ClientHello.
 *
 * ssl      The SSL/TLS object.
 * input    The extension data.
 * length   The length of the extension data.
 * msgType  The type of the message this extension is being parsed from.
 * returns 0 on success and other values indicate failure.
 */
static int TLSX_PostHandAuth_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                 byte msgType)
{
    (void)input;

    if (msgType == client_hello) {
        /* Ensure extension is empty. */
        if (length != 0)
            return BUFFER_E;

        ssl->options.postHandshakeAuth = 1;
        return 0;
    }

    return SANITY_MSG_E;
}

/* Create a new Post-handshake authentication object in the extensions.
 *
 * ssl    The SSL/TLS object.
 * returns 0 on success and other values indicate failure.
 */
static int TLSX_PostHandAuth_Use(WOLFSSL* ssl)
{
    int   ret = 0;
    TLSX* extension;

    /* Find the PSK key exchange modes extension if it exists. */
    extension = TLSX_Find(ssl->extensions, TLSX_POST_HANDSHAKE_AUTH);
    if (extension == NULL) {
        /* Push new Post-handshake Authentication extension. */
        ret = TLSX_Push(&ssl->extensions, TLSX_POST_HANDSHAKE_AUTH, NULL,
            ssl->heap);
        if (ret != 0)
            return ret;
    }

    return 0;
}

#define PHA_GET_SIZE  TLSX_PostHandAuth_GetSize
#define PHA_WRITE     TLSX_PostHandAuth_Write
#define PHA_PARSE     TLSX_PostHandAuth_Parse

#else

#define PHA_GET_SIZE(a, b)    0
#define PHA_WRITE(a, b, c)    0
#define PHA_PARSE(a, b, c, d) 0

#endif

/******************************************************************************/
/* Early Data Indication                                                      */
/******************************************************************************/

#ifdef WOLFSSL_EARLY_DATA
/* Get the size of the encoded Early Data Indication extension.
 * In messages: ClientHello, EncryptedExtensions and NewSessionTicket.
 *
 * msgType  The type of the message this extension is being written into.
 * returns the number of bytes of the encoded Early Data Indication extension.
 */
static int TLSX_EarlyData_GetSize(byte msgType, word16* pSz)
{
    int ret = 0;

    if (msgType == client_hello || msgType == encrypted_extensions)
        *pSz += 0;
    else if (msgType == session_ticket)
        *pSz += OPAQUE32_LEN;
    else
        ret = SANITY_MSG_E;

    return ret;
}

/* Writes the Early Data Indicator extension into the output buffer.
 * Assumes that the the output buffer is big enough to hold data.
 * In messages: ClientHello, EncryptedExtensions and NewSessionTicket.
 *
 * max      The maximum early data size.
 * output   The buffer to write into.
 * msgType  The type of the message this extension is being written into.
 * returns the number of bytes written into the buffer.
 */
static int TLSX_EarlyData_Write(word32 max, byte* output, byte msgType,
                                word16* pSz)
{
    if (msgType == client_hello || msgType == encrypted_extensions)
        return 0;
    else if (msgType == session_ticket) {
        c32toa(max, output);
        *pSz += OPAQUE32_LEN;
        return 0;
    }

    return SANITY_MSG_E;
}

/* Parse the Early Data Indicator extension.
 * In messages: ClientHello, EncryptedExtensions and NewSessionTicket.
 *
 * ssl      The SSL/TLS object.
 * input    The extension data.
 * length   The length of the extension data.
 * msgType  The type of the message this extension is being parsed from.
 * returns 0 on success and other values indicate failure.
 */
static int TLSX_EarlyData_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                 byte msgType)
{
    if (msgType == client_hello) {
        if (length != 0)
            return BUFFER_E;

        if (ssl->earlyData == expecting_early_data)
            return TLSX_EarlyData_Use(ssl, 0);
        ssl->earlyData = early_data_ext;
        return 0;
    }
    if (msgType == encrypted_extensions) {
        if (length != 0)
            return BUFFER_E;

        /* Ensure the index of PSK identity chosen by server is 0.
         * Index is plus one to handle 'not set' value of 0.
         */
        if (ssl->options.pskIdIndex != 1)
            return PSK_KEY_ERROR;

        return TLSX_EarlyData_Use(ssl, 1);
    }
    if (msgType == session_ticket) {
        word32 maxSz;

        if (length != OPAQUE32_LEN)
            return BUFFER_E;
        ato32(input, &maxSz);

        ssl->session.maxEarlyDataSz = maxSz;
        return 0;
    }

    return SANITY_MSG_E;
}

/* Use the data to create a new Early Data object in the extensions.
 *
 * ssl  The SSL/TLS object.
 * max  The maximum early data size.
 * returns 0 on success and other values indicate failure.
 */
int TLSX_EarlyData_Use(WOLFSSL* ssl, word32 max)
{
    int   ret = 0;
    TLSX* extension;

    /* Find the early data extension if it exists. */
    extension = TLSX_Find(ssl->extensions, TLSX_EARLY_DATA);
    if (extension == NULL) {
        /* Push new early data extension. */
        ret = TLSX_Push(&ssl->extensions, TLSX_EARLY_DATA, NULL, ssl->heap);
        if (ret != 0)
            return ret;

        extension = TLSX_Find(ssl->extensions, TLSX_EARLY_DATA);
        if (extension == NULL)
            return MEMORY_E;
    }

    extension->resp = 1;
    extension->val  = max;

    return 0;
}

#define EDI_GET_SIZE  TLSX_EarlyData_GetSize
#define EDI_WRITE     TLSX_EarlyData_Write
#define EDI_PARSE     TLSX_EarlyData_Parse

#else

#define EDI_GET_SIZE(a, b)    0
#define EDI_WRITE(a, b, c, d) 0
#define EDI_PARSE(a, b, c, d) 0

#endif

/******************************************************************************/
/* TLS Extensions Framework                                                   */
/******************************************************************************/

/** Finds an extension in the provided list. */
TLSX* TLSX_Find(TLSX* list, TLSX_Type type)
{
    TLSX* extension = list;

    while (extension && extension->type != type)
        extension = extension->next;

    return extension;
}

/** Remove an extension. */
void TLSX_Remove(TLSX** list, TLSX_Type type, void* heap)
{
    TLSX* extension = *list;
    TLSX** next = list;

    while (extension && extension->type != type) {
        next = &extension->next;
        extension = extension->next;
    }

    if (extension) {
        *next = extension->next;
        extension->next = NULL;
        TLSX_FreeAll(extension, heap);
    }
}

/** Releases all extensions in the provided list. */
void TLSX_FreeAll(TLSX* list, void* heap)
{
    TLSX* extension;

    while ((extension = list)) {
        list = extension->next;

        switch (extension->type) {

            case TLSX_SERVER_NAME:
                SNI_FREE_ALL((SNI*)extension->data, heap);
                break;

            case TLSX_TRUSTED_CA_KEYS:
                TCA_FREE_ALL((TCA*)extension->data, heap);
                break;

            case TLSX_MAX_FRAGMENT_LENGTH:
                MFL_FREE_ALL(extension->data, heap);
                break;

            case TLSX_EXTENDED_MASTER_SECRET:
            case TLSX_TRUNCATED_HMAC:
                /* Nothing to do. */
                break;

            case TLSX_SUPPORTED_GROUPS:
                EC_FREE_ALL((SupportedCurve*)extension->data, heap);
                break;

            case TLSX_EC_POINT_FORMATS:
                PF_FREE_ALL((PointFormat*)extension->data, heap);
                break;

            case TLSX_STATUS_REQUEST:
                CSR_FREE_ALL((CertificateStatusRequest*)extension->data, heap);
                break;

            case TLSX_STATUS_REQUEST_V2:
                CSR2_FREE_ALL((CertificateStatusRequestItemV2*)extension->data,
                        heap);
                break;

            case TLSX_RENEGOTIATION_INFO:
                SCR_FREE_ALL(extension->data, heap);
                break;

            case TLSX_SESSION_TICKET:
                WOLF_STK_FREE(extension->data, heap);
                break;

            case TLSX_QUANTUM_SAFE_HYBRID:
                QSH_FREE_ALL((QSHScheme*)extension->data, heap);
                break;

            case TLSX_APPLICATION_LAYER_PROTOCOL:
                ALPN_FREE_ALL((ALPN*)extension->data, heap);
                break;
#if !defined(WOLFSSL_NO_SIGALG)
            case TLSX_SIGNATURE_ALGORITHMS:
                break;
#endif
#if defined(HAVE_ENCRYPT_THEN_MAC) && !defined(WOLFSSL_AEAD_ONLY)
            case TLSX_ENCRYPT_THEN_MAC:
                break;
#endif
#ifdef WOLFSSL_TLS13
            case TLSX_SUPPORTED_VERSIONS:
                break;

            case TLSX_COOKIE:
                CKE_FREE_ALL((Cookie*)extension->data, heap);
                break;

    #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
            case TLSX_PRE_SHARED_KEY:
                PSK_FREE_ALL((PreSharedKey*)extension->data, heap);
                break;

            case TLSX_PSK_KEY_EXCHANGE_MODES:
                break;
    #endif

    #ifdef WOLFSSL_EARLY_DATA
            case TLSX_EARLY_DATA:
                break;
    #endif

    #ifdef WOLFSSL_POST_HANDSHAKE_AUTH
            case TLSX_POST_HANDSHAKE_AUTH:
                break;
    #endif

            case TLSX_SIGNATURE_ALGORITHMS_CERT:
                break;

            case TLSX_KEY_SHARE:
                KS_FREE_ALL((KeyShareEntry*)extension->data, heap);
                break;
#endif
        }

        XFREE(extension, heap, DYNAMIC_TYPE_TLSX);
    }

    (void)heap;
}

/** Checks if the tls extensions are supported based on the protocol version. */
int TLSX_SupportExtensions(WOLFSSL* ssl) {
    return ssl && (IsTLS(ssl) || ssl->version.major == DTLS_MAJOR);
}

/** Tells the buffered size of the extensions in a list. */
static int TLSX_GetSize(TLSX* list, byte* semaphore, byte msgType,
                        word16* pLength)
{
    int    ret = 0;
    TLSX*  extension;
    word16 length = 0;
    byte   isRequest = (msgType == client_hello ||
                        msgType == certificate_request);

    while ((extension = list)) {
        list = extension->next;

        /* only extensions marked as response are sent back to the client. */
        if (!isRequest && !extension->resp)
            continue; /* skip! */

        /* ssl level extensions are expected to override ctx level ones. */
        if (!IS_OFF(semaphore, TLSX_ToSemaphore(extension->type)))
            continue; /* skip! */

        /* extension type + extension data length. */
        length += HELLO_EXT_TYPE_SZ + OPAQUE16_LEN;

        switch (extension->type) {

            case TLSX_SERVER_NAME:
                /* SNI only sends the name on the request. */
                if (isRequest)
                    length += SNI_GET_SIZE((SNI*)extension->data);
                break;

            case TLSX_TRUSTED_CA_KEYS:
                /* TCA only sends the list on the request. */
                if (isRequest)
                    length += TCA_GET_SIZE((TCA*)extension->data);
                break;

            case TLSX_MAX_FRAGMENT_LENGTH:
                length += MFL_GET_SIZE(extension->data);
                break;

            case TLSX_EXTENDED_MASTER_SECRET:
            case TLSX_TRUNCATED_HMAC:
                /* always empty. */
                break;

            case TLSX_SUPPORTED_GROUPS:
                length += EC_GET_SIZE((SupportedCurve*)extension->data);
                break;

            case TLSX_EC_POINT_FORMATS:
                length += PF_GET_SIZE((PointFormat*)extension->data);
                break;

            case TLSX_STATUS_REQUEST:
                length += CSR_GET_SIZE(
                         (CertificateStatusRequest*)extension->data, isRequest);
                break;

            case TLSX_STATUS_REQUEST_V2:
                length += CSR2_GET_SIZE(
                        (CertificateStatusRequestItemV2*)extension->data,
                        isRequest);
                break;

            case TLSX_RENEGOTIATION_INFO:
                length += SCR_GET_SIZE((SecureRenegotiation*)extension->data,
                        isRequest);
                break;

            case TLSX_SESSION_TICKET:
                length += WOLF_STK_GET_SIZE((SessionTicket*)extension->data,
                        isRequest);
                break;

            case TLSX_QUANTUM_SAFE_HYBRID:
                length += QSH_GET_SIZE((QSHScheme*)extension->data, isRequest);
                break;

            case TLSX_APPLICATION_LAYER_PROTOCOL:
                length += ALPN_GET_SIZE((ALPN*)extension->data);
                break;
#if !defined(WOLFSSL_NO_SIGALG)
            case TLSX_SIGNATURE_ALGORITHMS:
                length += SA_GET_SIZE(extension->data);
                break;
#endif
#if defined(HAVE_ENCRYPT_THEN_MAC) && !defined(WOLFSSL_AEAD_ONLY)
            case TLSX_ENCRYPT_THEN_MAC:
                ret = ETM_GET_SIZE(msgType, &length);
                break;
#endif /* HAVE_ENCRYPT_THEN_MAC */
#ifdef WOLFSSL_TLS13
            case TLSX_SUPPORTED_VERSIONS:
                ret = SV_GET_SIZE(extension->data, msgType, &length);
                break;

            case TLSX_COOKIE:
                ret = CKE_GET_SIZE((Cookie*)extension->data, msgType, &length);
                break;

    #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
            case TLSX_PRE_SHARED_KEY:
                ret = PSK_GET_SIZE((PreSharedKey*)extension->data, msgType,
                                                                       &length);
                break;

            case TLSX_PSK_KEY_EXCHANGE_MODES:
                ret = PKM_GET_SIZE(extension->val, msgType, &length);
                break;
    #endif

    #ifdef WOLFSSL_EARLY_DATA
            case TLSX_EARLY_DATA:
                ret = EDI_GET_SIZE(msgType, &length);
                break;
    #endif

    #ifdef WOLFSSL_POST_HANDSHAKE_AUTH
            case TLSX_POST_HANDSHAKE_AUTH:
                ret = PHA_GET_SIZE(msgType, &length);
                break;
    #endif

            case TLSX_SIGNATURE_ALGORITHMS_CERT:
                length += SAC_GET_SIZE(extension->data);
                break;

            case TLSX_KEY_SHARE:
                length += KS_GET_SIZE((KeyShareEntry*)extension->data, msgType);
                break;
#endif
        }

        /* marks the extension as processed so ctx level */
        /* extensions don't overlap with ssl level ones. */
        TURN_ON(semaphore, TLSX_ToSemaphore(extension->type));
    }

    *pLength += length;

    return ret;
}

/** Writes the extensions of a list in a buffer. */
static int TLSX_Write(TLSX* list, byte* output, byte* semaphore,
                         byte msgType, word16* pOffset)
{
    int    ret = 0;
    TLSX*  extension;
    word16 offset = 0;
    word16 length_offset = 0;
    byte   isRequest = (msgType == client_hello ||
                        msgType == certificate_request);

    while ((extension = list)) {
        list = extension->next;

        /* only extensions marked as response are written in a response. */
        if (!isRequest && !extension->resp)
            continue; /* skip! */

        /* ssl level extensions are expected to override ctx level ones. */
        if (!IS_OFF(semaphore, TLSX_ToSemaphore(extension->type)))
            continue; /* skip! */

        /* writes extension type. */
        c16toa(extension->type, output + offset);
        offset += HELLO_EXT_TYPE_SZ + OPAQUE16_LEN;
        length_offset = offset;

        /* extension data should be written internally. */
        switch (extension->type) {
            case TLSX_SERVER_NAME:
                if (isRequest) {
                    WOLFSSL_MSG("SNI extension to write");
                    offset += SNI_WRITE((SNI*)extension->data, output + offset);
                }
                break;

            case TLSX_TRUSTED_CA_KEYS:
                WOLFSSL_MSG("Trusted CA Indication extension to write");
                if (isRequest) {
                    offset += TCA_WRITE((TCA*)extension->data, output + offset);
                }
                break;

            case TLSX_MAX_FRAGMENT_LENGTH:
                WOLFSSL_MSG("Max Fragment Length extension to write");
                offset += MFL_WRITE((byte*)extension->data, output + offset);
                break;

            case TLSX_EXTENDED_MASTER_SECRET:
                WOLFSSL_MSG("Extended Master Secret");
                /* always empty. */
                break;

            case TLSX_TRUNCATED_HMAC:
                WOLFSSL_MSG("Truncated HMAC extension to write");
                /* always empty. */
                break;

            case TLSX_SUPPORTED_GROUPS:
                WOLFSSL_MSG("Supported Groups extension to write");
                offset += EC_WRITE((SupportedCurve*)extension->data,
                                    output + offset);
                break;

            case TLSX_EC_POINT_FORMATS:
                WOLFSSL_MSG("Point Formats extension to write");
                offset += PF_WRITE((PointFormat*)extension->data,
                                    output + offset);
                break;

            case TLSX_STATUS_REQUEST:
                WOLFSSL_MSG("Certificate Status Request extension to write");
                offset += CSR_WRITE((CertificateStatusRequest*)extension->data,
                        output + offset, isRequest);
                break;

            case TLSX_STATUS_REQUEST_V2:
                WOLFSSL_MSG("Certificate Status Request v2 extension to write");
                offset += CSR2_WRITE(
                        (CertificateStatusRequestItemV2*)extension->data,
                        output + offset, isRequest);
                break;

            case TLSX_RENEGOTIATION_INFO:
                WOLFSSL_MSG("Secure Renegotiation extension to write");
                offset += SCR_WRITE((SecureRenegotiation*)extension->data,
                        output + offset, isRequest);
                break;

            case TLSX_SESSION_TICKET:
                WOLFSSL_MSG("Session Ticket extension to write");
                offset += WOLF_STK_WRITE((SessionTicket*)extension->data,
                        output + offset, isRequest);
                break;

            case TLSX_QUANTUM_SAFE_HYBRID:
                WOLFSSL_MSG("Quantum-Safe-Hybrid extension to write");
                if (isRequest) {
                    offset += QSH_WRITE((QSHScheme*)extension->data, output + offset);
                }
                offset += QSHPK_WRITE((QSHScheme*)extension->data, output + offset);
                offset += QSH_SERREQ(output + offset, isRequest);
                break;

            case TLSX_APPLICATION_LAYER_PROTOCOL:
                WOLFSSL_MSG("ALPN extension to write");
                offset += ALPN_WRITE((ALPN*)extension->data, output + offset);
                break;
#if !defined(WOLFSSL_NO_SIGALG)
            case TLSX_SIGNATURE_ALGORITHMS:
                WOLFSSL_MSG("Signature Algorithms extension to write");
                offset += SA_WRITE(extension->data, output + offset);
                break;
#endif
#if defined(HAVE_ENCRYPT_THEN_MAC) && !defined(WOLFSSL_AEAD_ONLY)
            case TLSX_ENCRYPT_THEN_MAC:
                WOLFSSL_MSG("Encrypt-Then-Mac extension to write");
                ret = ETM_WRITE(extension->data, output, msgType, &offset);
                break;
#endif /* HAVE_ENCRYPT_THEN_MAC */
#ifdef WOLFSSL_TLS13
            case TLSX_SUPPORTED_VERSIONS:
                WOLFSSL_MSG("Supported Versions extension to write");
                ret = SV_WRITE(extension->data, output + offset, msgType, &offset);
                break;

            case TLSX_COOKIE:
                WOLFSSL_MSG("Cookie extension to write");
                ret = CKE_WRITE((Cookie*)extension->data, output + offset,
                                msgType, &offset);
                break;

    #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
            case TLSX_PRE_SHARED_KEY:
                WOLFSSL_MSG("Pre-Shared Key extension to write");
                ret = PSK_WRITE((PreSharedKey*)extension->data, output + offset,
                                                              msgType, &offset);
                break;

            case TLSX_PSK_KEY_EXCHANGE_MODES:
                WOLFSSL_MSG("PSK Key Exchange Modes extension to write");
                ret = PKM_WRITE(extension->val, output + offset, msgType,
                                                                       &offset);
                break;
    #endif

    #ifdef WOLFSSL_EARLY_DATA
            case TLSX_EARLY_DATA:
                WOLFSSL_MSG("Early Data extension to write");
                ret = EDI_WRITE(extension->val, output + offset, msgType,
                                                                       &offset);
                break;
    #endif

    #ifdef WOLFSSL_POST_HANDSHAKE_AUTH
            case TLSX_POST_HANDSHAKE_AUTH:
                WOLFSSL_MSG("Post-Handshake Authentication extension to write");
                ret = PHA_WRITE(output + offset, msgType, &offset);
                break;
    #endif

            case TLSX_SIGNATURE_ALGORITHMS_CERT:
                WOLFSSL_MSG("Signature Algorithms extension to write");
                offset += SAC_WRITE(extension->data, output + offset);
                break;

            case TLSX_KEY_SHARE:
                WOLFSSL_MSG("Key Share extension to write");
                offset += KS_WRITE((KeyShareEntry*)extension->data,
                                                      output + offset, msgType);
                break;
#endif
        }

        /* writes extension data length. */
        c16toa(offset - length_offset, output + length_offset - OPAQUE16_LEN);

        /* marks the extension as processed so ctx level */
        /* extensions don't overlap with ssl level ones. */
        TURN_ON(semaphore, TLSX_ToSemaphore(extension->type));
    }

    *pOffset += offset;

    return ret;
}


#if defined(HAVE_NTRU) && defined(HAVE_QSH)

static word32 GetEntropy(unsigned char* out, word32 num_bytes)
{
    int ret = 0;

    if (gRng == NULL) {
        if ((gRng = (WC_RNG*)XMALLOC(sizeof(WC_RNG), NULL,
                                                    DYNAMIC_TYPE_TLSX)) == NULL)
            return DRBG_OUT_OF_MEMORY;
        wc_InitRng(gRng);
    }

    if (gRngMutex == NULL) {
        if ((gRngMutex = (wolfSSL_Mutex*)XMALLOC(sizeof(wolfSSL_Mutex), NULL,
                                                    DYNAMIC_TYPE_TLSX)) == NULL)
            return DRBG_OUT_OF_MEMORY;
        wc_InitMutex(gRngMutex);
    }

    ret |= wc_LockMutex(gRngMutex);
    ret |= wc_RNG_GenerateBlock(gRng, out, num_bytes);
    ret |= wc_UnLockMutex(gRngMutex);

    if (ret != 0)
        return DRBG_ENTROPY_FAIL;

    return DRBG_OK;
}
#endif


#ifdef HAVE_QSH
static int TLSX_CreateQSHKey(WOLFSSL* ssl, int type)
{
    int ret = -1;

    (void)ssl;

    switch (type) {
#ifdef HAVE_NTRU
        case WOLFSSL_NTRU_EESS439:
        case WOLFSSL_NTRU_EESS593:
        case WOLFSSL_NTRU_EESS743:
            ret = TLSX_CreateNtruKey(ssl, type);
            break;
#endif
        default:
            WOLFSSL_MSG("Unknown type for creating NTRU key");
            break;
    }

    return ret;
}


static int TLSX_AddQSHKey(QSHKey** list, QSHKey* key)
{
    QSHKey* current;

    if (key == NULL)
        return BAD_FUNC_ARG;

    /* if no public key stored in key then do not add */
    if (key->pub.length == 0 || key->pub.buffer == NULL)
        return 0;

    /* first element to be added to the list */
    current = *list;
    if (current == NULL) {
        *list = key;
        return 0;
    }

    while (current->next) {
        /* can only have one of the key in the list */
        if (current->name == key->name)
            return -1;
        current = (QSHKey*)current->next;
    }

    current->next = (struct QSHKey*)key;

    return 0;
}


#if defined(HAVE_NTRU)
int TLSX_CreateNtruKey(WOLFSSL* ssl, int type)
{
    int ret = -1;
    int ntruType;

    /* variable declarations for NTRU*/
    QSHKey* temp = NULL;
    byte   public_key[1027];
    word16 public_key_len = sizeof(public_key);
    byte   private_key[1120];
    word16 private_key_len = sizeof(private_key);
    DRBG_HANDLE drbg;

    if (ssl == NULL)
        return BAD_FUNC_ARG;

    switch (type) {
        case WOLFSSL_NTRU_EESS439:
            ntruType = NTRU_EES439EP1;
            break;
        case WOLFSSL_NTRU_EESS593:
            ntruType = NTRU_EES593EP1;
            break;
        case WOLFSSL_NTRU_EESS743:
            ntruType = NTRU_EES743EP1;
            break;
        default:
            WOLFSSL_MSG("Unknown type for creating NTRU key");
            return -1;
    }
    ret = ntru_crypto_drbg_external_instantiate(GetEntropy, &drbg);
    if (ret != DRBG_OK) {
        WOLFSSL_MSG("NTRU drbg instantiate failed\n");
        return ret;
    }

    if ((ret = ntru_crypto_ntru_encrypt_keygen(drbg, ntruType,
                     &public_key_len, NULL, &private_key_len, NULL)) != NTRU_OK)
        return ret;

    if ((ret = ntru_crypto_ntru_encrypt_keygen(drbg, ntruType,
        &public_key_len, public_key, &private_key_len, private_key)) != NTRU_OK)
        return ret;

    ret = ntru_crypto_drbg_uninstantiate(drbg);
    if (ret != NTRU_OK) {
        WOLFSSL_MSG("NTRU drbg uninstantiate failed\n");
        return ret;
    }

    if ((temp = (QSHKey*)XMALLOC(sizeof(QSHKey), ssl->heap,
                                                    DYNAMIC_TYPE_TLSX)) == NULL)
        return MEMORY_E;
    temp->name = type;
    temp->pub.length = public_key_len;
    temp->pub.buffer = (byte*)XMALLOC(public_key_len, ssl->heap,
                                DYNAMIC_TYPE_PUBLIC_KEY);
    XMEMCPY(temp->pub.buffer, public_key, public_key_len);
    temp->pri.length = private_key_len;
    temp->pri.buffer = (byte*)XMALLOC(private_key_len, ssl->heap,
                                DYNAMIC_TYPE_ARRAYS);
    XMEMCPY(temp->pri.buffer, private_key, private_key_len);
    temp->next = NULL;

    TLSX_AddQSHKey(&ssl->QSH_Key, temp);

    (void)ssl;
    (void)type;

    return ret;
}
#endif


/*
    Used to find a public key from the list of keys
    pubLen length of array
    name   input the name of the scheme looking for ie WOLFSSL_NTRU_ESSXXX

    returns a pointer to public key byte* or NULL if not found
 */
static byte* TLSX_QSHKeyFind_Pub(QSHKey* qsh, word16* pubLen, word16 name)
{
    QSHKey* current = qsh;

    if (qsh == NULL || pubLen == NULL)
        return NULL;

    *pubLen = 0;

    while(current) {
        if (current->name == name) {
            *pubLen = current->pub.length;
            return current->pub.buffer;
        }
        current = (QSHKey*)current->next;
    }

    return NULL;
}
#endif /* HAVE_QSH */

#if (!defined(NO_WOLFSSL_SERVER) && defined(WOLFSSL_TLS13) && \
        !defined(WOLFSSL_NO_SERVER_GROUPS_EXT)) || \
    (defined(WOLFSSL_TLS13) && !defined(HAVE_ECC) && !defined(HAVE_CURVE25519) \
        && !defined(HAVE_CURVE448) && defined(HAVE_SUPPORTED_CURVES)) || \
    ((defined(HAVE_ECC) || defined(HAVE_CURVE25519) || \
        defined(HAVE_CURVE448)) && defined(HAVE_SUPPORTED_CURVES))

/* Populates the default supported groups / curves */
static int TLSX_PopulateSupportedGroups(WOLFSSL* ssl, TLSX** extensions)
{
    int ret = WOLFSSL_SUCCESS;
#ifdef WOLFSSL_TLS13
#if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
    if (ssl->options.resuming && ssl->session.namedGroup != 0) {
        return TLSX_UseSupportedCurve(extensions, ssl->session.namedGroup,
                                                                     ssl->heap);
    }
#endif

#ifdef HAVE_SUPPORTED_CURVES
    if (ssl->numGroups != 0) {
        int i;
        for (i = 0; i < ssl->numGroups; i++) {
            ret = TLSX_UseSupportedCurve(extensions, ssl->group[i], ssl->heap);
            if (ret != WOLFSSL_SUCCESS)
                return ret;
        }
        return WOLFSSL_SUCCESS;
    }
#endif /* HAVE_SUPPORTED_CURVES */
#endif /* WOLFSSL_TLS13 */

#if defined(HAVE_ECC) && defined(HAVE_SUPPORTED_CURVES)
        /* list in order by strength, since not all servers choose by strength */
        #if defined(HAVE_ECC521) || defined(HAVE_ALL_CURVES)
            #ifndef NO_ECC_SECP
                ret = TLSX_UseSupportedCurve(extensions,
                                              WOLFSSL_ECC_SECP521R1, ssl->heap);
                if (ret != WOLFSSL_SUCCESS) return ret;
            #endif
        #endif
        #if defined(HAVE_ECC512) || defined(HAVE_ALL_CURVES)
            #ifdef HAVE_ECC_BRAINPOOL
                ret = TLSX_UseSupportedCurve(extensions,
                                        WOLFSSL_ECC_BRAINPOOLP512R1, ssl->heap);
                if (ret != WOLFSSL_SUCCESS) return ret;
            #endif
        #endif
        #if defined(HAVE_ECC384) || defined(HAVE_ALL_CURVES)
            #ifndef NO_ECC_SECP
                ret = TLSX_UseSupportedCurve(extensions,
                                              WOLFSSL_ECC_SECP384R1, ssl->heap);
                if (ret != WOLFSSL_SUCCESS) return ret;
            #endif
            #ifdef HAVE_ECC_BRAINPOOL
                ret = TLSX_UseSupportedCurve(extensions,
                                        WOLFSSL_ECC_BRAINPOOLP384R1, ssl->heap);
                if (ret != WOLFSSL_SUCCESS) return ret;
            #endif
        #endif
#endif /* HAVE_ECC && HAVE_SUPPORTED_CURVES */

        #ifndef HAVE_FIPS
            #if defined(HAVE_CURVE448)
                ret = TLSX_UseSupportedCurve(extensions,
                                                   WOLFSSL_ECC_X448, ssl->heap);
                if (ret != WOLFSSL_SUCCESS) return ret;
            #endif
        #endif /* HAVE_FIPS */

#if defined(HAVE_ECC) && defined(HAVE_SUPPORTED_CURVES)
        #if !defined(NO_ECC256)  || defined(HAVE_ALL_CURVES)
            #ifndef NO_ECC_SECP
                ret = TLSX_UseSupportedCurve(extensions,
                                              WOLFSSL_ECC_SECP256R1, ssl->heap);
                if (ret != WOLFSSL_SUCCESS) return ret;
            #endif
            #ifdef HAVE_ECC_KOBLITZ
                ret = TLSX_UseSupportedCurve(extensions,
                                              WOLFSSL_ECC_SECP256K1, ssl->heap);
                if (ret != WOLFSSL_SUCCESS) return ret;
            #endif
            #ifdef HAVE_ECC_BRAINPOOL
                ret = TLSX_UseSupportedCurve(extensions,
                                        WOLFSSL_ECC_BRAINPOOLP256R1, ssl->heap);
                if (ret != WOLFSSL_SUCCESS) return ret;
            #endif
        #endif
#endif /* HAVE_ECC && HAVE_SUPPORTED_CURVES */

        #ifndef HAVE_FIPS
            #if defined(HAVE_CURVE25519)
                ret = TLSX_UseSupportedCurve(extensions,
                                                 WOLFSSL_ECC_X25519, ssl->heap);
                if (ret != WOLFSSL_SUCCESS) return ret;
            #endif
        #endif /* HAVE_FIPS */

#if defined(HAVE_ECC) && defined(HAVE_SUPPORTED_CURVES)
        #if defined(HAVE_ECC224) || defined(HAVE_ALL_CURVES)
            #ifndef NO_ECC_SECP
                ret = TLSX_UseSupportedCurve(extensions,
                                              WOLFSSL_ECC_SECP224R1, ssl->heap);
                if (ret != WOLFSSL_SUCCESS) return ret;
            #endif
            #ifdef HAVE_ECC_KOBLITZ
                ret = TLSX_UseSupportedCurve(extensions,
                                              WOLFSSL_ECC_SECP224K1, ssl->heap);
                if (ret != WOLFSSL_SUCCESS) return ret;
            #endif
        #endif

    #ifndef HAVE_FIPS
        #if defined(HAVE_ECC192) || defined(HAVE_ALL_CURVES)
            #ifndef NO_ECC_SECP
                ret = TLSX_UseSupportedCurve(extensions,
                                              WOLFSSL_ECC_SECP192R1, ssl->heap);
                if (ret != WOLFSSL_SUCCESS) return ret;
            #endif
            #ifdef HAVE_ECC_KOBLITZ
                ret = TLSX_UseSupportedCurve(extensions,
                                              WOLFSSL_ECC_SECP192K1, ssl->heap);
                if (ret != WOLFSSL_SUCCESS) return ret;
            #endif
        #endif
        #if defined(HAVE_ECC160) || defined(HAVE_ALL_CURVES)
            #ifndef NO_ECC_SECP
                ret = TLSX_UseSupportedCurve(extensions,
                                              WOLFSSL_ECC_SECP160R1, ssl->heap);
                if (ret != WOLFSSL_SUCCESS) return ret;
            #endif
            #ifdef HAVE_ECC_SECPR2
                ret = TLSX_UseSupportedCurve(extensions,
                                              WOLFSSL_ECC_SECP160R2, ssl->heap);
                if (ret != WOLFSSL_SUCCESS) return ret;
            #endif
            #ifdef HAVE_ECC_KOBLITZ
                ret = TLSX_UseSupportedCurve(extensions,
                                              WOLFSSL_ECC_SECP160K1, ssl->heap);
                if (ret != WOLFSSL_SUCCESS) return ret;
            #endif
        #endif
    #endif /* HAVE_FIPS */
#endif /* HAVE_ECC && HAVE_SUPPORTED_CURVES */

                /* Add FFDHE supported groups. */
        #ifdef HAVE_FFDHE_8192
            if (8192/8 >= ssl->options.minDhKeySz &&
                                            8192/8 <= ssl->options.maxDhKeySz) {
                ret = TLSX_UseSupportedCurve(extensions,
                                             WOLFSSL_FFDHE_8192, ssl->heap);
                if (ret != WOLFSSL_SUCCESS)
                    return ret;
            }
        #endif
        #ifdef HAVE_FFDHE_6144
            if (6144/8 >= ssl->options.minDhKeySz &&
                                            6144/8 <= ssl->options.maxDhKeySz) {
                ret = TLSX_UseSupportedCurve(extensions,
                                             WOLFSSL_FFDHE_6144, ssl->heap);
                if (ret != WOLFSSL_SUCCESS)
                    return ret;
            }
        #endif
        #ifdef HAVE_FFDHE_4096
            if (4096/8 >= ssl->options.minDhKeySz &&
                                            4096/8 <= ssl->options.maxDhKeySz) {
                ret = TLSX_UseSupportedCurve(extensions,
                                             WOLFSSL_FFDHE_4096, ssl->heap);
                if (ret != WOLFSSL_SUCCESS)
                    return ret;
            }
        #endif
        #ifdef HAVE_FFDHE_3072
            if (3072/8 >= ssl->options.minDhKeySz &&
                                            3072/8 <= ssl->options.maxDhKeySz) {
                ret = TLSX_UseSupportedCurve(extensions,
                                             WOLFSSL_FFDHE_3072, ssl->heap);
                if (ret != WOLFSSL_SUCCESS)
                    return ret;
            }
        #endif
        #ifdef HAVE_FFDHE_2048
            if (2048/8 >= ssl->options.minDhKeySz &&
                                            2048/8 <= ssl->options.maxDhKeySz) {
                ret = TLSX_UseSupportedCurve(extensions,
                                             WOLFSSL_FFDHE_2048, ssl->heap);
                if (ret != WOLFSSL_SUCCESS)
                    return ret;
            }
        #endif

    (void)ssl;
    (void)extensions;

    return ret;
}

#endif

int TLSX_PopulateExtensions(WOLFSSL* ssl, byte isServer)
{
    int ret = 0;
    byte* public_key      = NULL;
    word16 public_key_len = 0;
#if defined(WOLFSSL_TLS13) && (defined(HAVE_SESSION_TICKET) || !defined(NO_PSK))
    int usingPSK = 0;
#endif
#ifdef HAVE_QSH
    TLSX* extension;
    QSHScheme* qsh;
    QSHScheme* next;

    /* add supported QSHSchemes */
    WOLFSSL_MSG("Adding supported QSH Schemes");
#endif

    /* server will add extension depending on what is parsed from client */
    if (!isServer) {
#ifdef HAVE_QSH
        /* test if user has set a specific scheme already */
        if (!ssl->user_set_QSHSchemes) {
            if (ssl->sendQSHKeys && ssl->QSH_Key == NULL) {
                if ((ret = TLSX_CreateQSHKey(ssl, WOLFSSL_NTRU_EESS743)) != 0) {
                    WOLFSSL_MSG("Error creating ntru keys");
                    return ret;
                }
                if ((ret = TLSX_CreateQSHKey(ssl, WOLFSSL_NTRU_EESS593)) != 0) {
                    WOLFSSL_MSG("Error creating ntru keys");
                    return ret;
                }
                if ((ret = TLSX_CreateQSHKey(ssl, WOLFSSL_NTRU_EESS439)) != 0) {
                    WOLFSSL_MSG("Error creating ntru keys");
                    return ret;
                }

            /* add NTRU 256 */
            public_key = TLSX_QSHKeyFind_Pub(ssl->QSH_Key,
                    &public_key_len, WOLFSSL_NTRU_EESS743);
            }
            if (TLSX_UseQSHScheme(&ssl->extensions, WOLFSSL_NTRU_EESS743,
                                  public_key, public_key_len, ssl->heap)
                                  != WOLFSSL_SUCCESS)
                ret = -1;

            /* add NTRU 196 */
            if (ssl->sendQSHKeys) {
                public_key = TLSX_QSHKeyFind_Pub(ssl->QSH_Key,
                    &public_key_len, WOLFSSL_NTRU_EESS593);
            }
            if (TLSX_UseQSHScheme(&ssl->extensions, WOLFSSL_NTRU_EESS593,
                                  public_key, public_key_len, ssl->heap)
                                  != WOLFSSL_SUCCESS)
                ret = -1;

            /* add NTRU 128 */
            if (ssl->sendQSHKeys) {
                public_key = TLSX_QSHKeyFind_Pub(ssl->QSH_Key,
                    &public_key_len, WOLFSSL_NTRU_EESS439);
            }
            if (TLSX_UseQSHScheme(&ssl->extensions, WOLFSSL_NTRU_EESS439,
                                  public_key, public_key_len, ssl->heap)
                                  != WOLFSSL_SUCCESS)
                ret = -1;
        }
        else if (ssl->sendQSHKeys && ssl->QSH_Key == NULL) {
            /* for each scheme make a client key */
            extension = TLSX_Find(ssl->extensions, TLSX_QUANTUM_SAFE_HYBRID);
            if (extension) {
                qsh = (QSHScheme*)extension->data;

                while (qsh) {
                    if ((ret = TLSX_CreateQSHKey(ssl, qsh->name)) != 0)
                        return ret;

                    /* get next now because qsh could be freed */
                    next = qsh->next;

                    /* find the public key created and add to extension*/
                    public_key = TLSX_QSHKeyFind_Pub(ssl->QSH_Key,
                             &public_key_len, qsh->name);
                    if (TLSX_UseQSHScheme(&ssl->extensions, qsh->name,
                                          public_key, public_key_len,
                                          ssl->heap) != WOLFSSL_SUCCESS)
                        ret = -1;
                    qsh = next;
                }
            }
        }
#endif

#if defined(HAVE_ENCRYPT_THEN_MAC) && !defined(WOLFSSL_AEAD_ONLY)
        if (!ssl->options.disallowEncThenMac) {
            ret = TLSX_EncryptThenMac_Use(ssl);
            if (ret != 0)
                return ret;
        }
#endif

#if (defined(HAVE_ECC) || defined(HAVE_CURVE25519) || \
                       defined(HAVE_CURVE448)) && defined(HAVE_SUPPORTED_CURVES)
        if (!ssl->options.userCurves && !ssl->ctx->userCurves) {
            if (TLSX_Find(ssl->ctx->extensions,
                                               TLSX_SUPPORTED_GROUPS) == NULL) {
                ret = TLSX_PopulateSupportedGroups(ssl, &ssl->extensions);
                if (ret != WOLFSSL_SUCCESS)
                    return ret;
            }
        }
        if ((!IsAtLeastTLSv1_3(ssl->version) || ssl->options.downgrade) &&
               TLSX_Find(ssl->ctx->extensions, TLSX_EC_POINT_FORMATS) == NULL &&
               TLSX_Find(ssl->extensions, TLSX_EC_POINT_FORMATS) == NULL) {
             ret = TLSX_UsePointFormat(&ssl->extensions,
                                         WOLFSSL_EC_PF_UNCOMPRESSED, ssl->heap);
             if (ret != WOLFSSL_SUCCESS)
                 return ret;
        }
#endif /* (HAVE_ECC || CURVE25519 || CURVE448) && HAVE_SUPPORTED_CURVES */
    } /* is not server */

#if !defined(WOLFSSL_NO_SIGALG)
    WOLFSSL_MSG("Adding signature algorithms extension");
    if ((ret = TLSX_SetSignatureAlgorithms(&ssl->extensions, ssl, ssl->heap))
                                                                         != 0) {
            return ret;
    }
#else
    ret = 0;
#endif
    #ifdef WOLFSSL_TLS13
        if (!isServer && IsAtLeastTLSv1_3(ssl->version)) {
            /* Add mandatory TLS v1.3 extension: supported version */
            WOLFSSL_MSG("Adding supported versions extension");
            if ((ret = TLSX_SetSupportedVersions(&ssl->extensions, ssl,
                                                             ssl->heap)) != 0) {
                return ret;
            }

    #if !defined(HAVE_ECC) && !defined(HAVE_CURVE25519) && \
                       !defined(HAVE_CURVE448) && defined(HAVE_SUPPORTED_CURVES)
        if (TLSX_Find(ssl->ctx->extensions, TLSX_SUPPORTED_GROUPS) == NULL) {
            /* Put in DH groups for TLS 1.3 only. */
            ret = TLSX_PopulateSupportedGroups(ssl, &ssl->extensions);
            if (ret != WOLFSSL_SUCCESS)
                return ret;
            ret = 0;
        }
    #endif /* (HAVE_ECC || CURVE25519 || CURVE448) && HAVE_SUPPORTED_CURVES */

            if (ssl->certHashSigAlgoSz > 0) {
                WOLFSSL_MSG("Adding signature algorithms cert extension");
                if ((ret = TLSX_SetSignatureAlgorithmsCert(&ssl->extensions,
                                                        ssl, ssl->heap)) != 0) {
                    return ret;
                }
            }

            if (TLSX_Find(ssl->extensions, TLSX_KEY_SHARE) == NULL) {
                word16 namedGroup;

        #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
                if (ssl->options.resuming && ssl->session.namedGroup != 0)
                    namedGroup = ssl->session.namedGroup;
                else
        #endif
                {
        #if defined(HAVE_ECC) && (!defined(NO_ECC256) || \
                              defined(HAVE_ALL_CURVES)) && !defined(NO_ECC_SECP)
                    namedGroup = WOLFSSL_ECC_SECP256R1;
        #elif defined(HAVE_CURVE25519)
                    namedGroup = WOLFSSL_ECC_X25519;
        #elif defined(HAVE_CURVE448)
                    namedGroup = WOLFSSL_ECC_X448;
        #elif defined(HAVE_ECC) && (!defined(NO_ECC384) || \
                              defined(HAVE_ALL_CURVES)) && !defined(NO_ECC_SECP)
                    namedGroup = WOLFSSL_ECC_SECP384R1;
        #elif defined(HAVE_ECC) && (!defined(NO_ECC521) || \
                              defined(HAVE_ALL_CURVES)) && !defined(NO_ECC_SECP)
                    namedGroup = WOLFSSL_ECC_SECP521R1;
        #elif defined(HAVE_FFDHE_2048)
                    namedGroup = WOLFSSL_FFDHE_2048;
        #elif defined(HAVE_FFDHE_3072)
                    namedGroup = WOLFSSL_FFDHE_3072;
        #elif defined(HAVE_FFDHE_4096)
                    namedGroup = WOLFSSL_FFDHE_4096;
        #elif defined(HAVE_FFDHE_6144)
                    namedGroup = WOLFSSL_FFDHE_6144;
        #elif defined(HAVE_FFDHE_8192)
                    namedGroup = WOLFSSL_FFDHE_8192;
        #else
                    return KEY_SHARE_ERROR;
        #endif
                }
                ret = TLSX_KeyShare_Use(ssl, namedGroup, 0, NULL, NULL);
                if (ret != 0)
                    return ret;
            }

        #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
            TLSX_Remove(&ssl->extensions, TLSX_PRE_SHARED_KEY, ssl->heap);
        #endif
        #if defined(HAVE_SESSION_TICKET)
            if (ssl->options.resuming && ssl->session.ticketLen > 0) {
                WOLFSSL_SESSION* sess = &ssl->session;
                word32           milli;

                if (sess->ticketLen > MAX_PSK_ID_LEN) {
                    WOLFSSL_MSG("Session ticket length for PSK ext is too large");
                    return BUFFER_ERROR;
                }

                /* Determine the MAC algorithm for the cipher suite used. */
                ssl->options.cipherSuite0 = sess->cipherSuite0;
                ssl->options.cipherSuite  = sess->cipherSuite;
                ret = SetCipherSpecs(ssl);
                if (ret != 0)
                    return ret;
                milli = TimeNowInMilliseconds() - sess->ticketSeen +
                        sess->ticketAdd;
                /* Pre-shared key is mandatory extension for resumption. */
                ret = TLSX_PreSharedKey_Use(ssl, sess->ticket, sess->ticketLen,
                                            milli, ssl->specs.mac_algorithm,
                                            ssl->options.cipherSuite0,
                                            ssl->options.cipherSuite, 1,
                                            NULL);
                if (ret != 0)
                    return ret;

                usingPSK = 1;
            }
        #endif
        #ifndef NO_PSK
            if (ssl->options.client_psk_cb != NULL ||
                                     ssl->options.client_psk_tls13_cb != NULL) {
                /* Default ciphersuite. */
                byte cipherSuite0 = TLS13_BYTE;
                byte cipherSuite = WOLFSSL_DEF_PSK_CIPHER;
                const char* cipherName = NULL;

                if (ssl->options.client_psk_tls13_cb != NULL) {
                    ssl->arrays->psk_keySz = ssl->options.client_psk_tls13_cb(
                        ssl, ssl->arrays->server_hint,
                        ssl->arrays->client_identity, MAX_PSK_ID_LEN,
                        ssl->arrays->psk_key, MAX_PSK_KEY_LEN, &cipherName);
                    if (GetCipherSuiteFromName(cipherName, &cipherSuite0,
                                                           &cipherSuite) != 0) {
                        return PSK_KEY_ERROR;
                    }
                }
                else {
                    ssl->arrays->psk_keySz = ssl->options.client_psk_cb(ssl,
                        ssl->arrays->server_hint, ssl->arrays->client_identity,
                        MAX_PSK_ID_LEN, ssl->arrays->psk_key, MAX_PSK_KEY_LEN);
                }
                if (ssl->arrays->psk_keySz == 0 ||
                                     ssl->arrays->psk_keySz > MAX_PSK_KEY_LEN) {
                    return PSK_KEY_ERROR;
                }
                ssl->arrays->client_identity[MAX_PSK_ID_LEN] = '\0';
                /* TODO: Callback should be able to change ciphersuite. */
                ssl->options.cipherSuite0 = cipherSuite0;
                ssl->options.cipherSuite  = cipherSuite;
                ret = SetCipherSpecs(ssl);
                if (ret != 0)
                    return ret;

                ret = TLSX_PreSharedKey_Use(ssl,
                                  (byte*)ssl->arrays->client_identity,
                                  (word16)XSTRLEN(ssl->arrays->client_identity),
                                  0, ssl->specs.mac_algorithm,
                                  cipherSuite0, cipherSuite, 0,
                                  NULL);
                if (ret != 0)
                    return ret;

                usingPSK = 1;
            }
        #endif
        #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
            if (usingPSK) {
                byte modes;

                /* Pre-shared key modes: mandatory extension for resumption. */
                modes = 1 << PSK_KE;
            #if !defined(NO_DH) || defined(HAVE_ECC) || \
                              defined(HAVE_CURVE25519) || defined(HAVE_CURVE448)
                if (!ssl->options.noPskDheKe)
                    modes |= 1 << PSK_DHE_KE;
            #endif
                ret = TLSX_PskKeModes_Use(ssl, modes);
                if (ret != 0)
                    return ret;
            }
        #endif
        #if defined(WOLFSSL_POST_HANDSHAKE_AUTH)
            if (!isServer && ssl->options.postHandshakeAuth) {
                ret = TLSX_PostHandAuth_Use(ssl);
                if (ret != 0)
                    return ret;
            }
        #endif
        }

    #endif

    (void)isServer;
    (void)public_key;
    (void)public_key_len;
    (void)ssl;

    return ret;
}


#if defined(WOLFSSL_TLS13) || !defined(NO_WOLFSSL_CLIENT)

/** Tells the buffered size of extensions to be sent into the client hello. */
int TLSX_GetRequestSize(WOLFSSL* ssl, byte msgType, word16* pLength)
{
    int ret = 0;
    word16 length = 0;
    byte semaphore[SEMAPHORE_SIZE] = {0};

    if (!TLSX_SupportExtensions(ssl))
        return 0;
    if (msgType == client_hello) {
        EC_VALIDATE_REQUEST(ssl, semaphore);
        PF_VALIDATE_REQUEST(ssl, semaphore);
        QSH_VALIDATE_REQUEST(ssl, semaphore);
        WOLF_STK_VALIDATE_REQUEST(ssl);
#if !defined(WOLFSSL_NO_SIGALG)
        if (ssl->suites->hashSigAlgoSz == 0)
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_SIGNATURE_ALGORITHMS));
#endif
#if defined(WOLFSSL_TLS13)
        if (!IsAtLeastTLSv1_2(ssl))
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_SUPPORTED_VERSIONS));
        if (!IsAtLeastTLSv1_3(ssl->version)) {
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_KEY_SHARE));
    #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_PRE_SHARED_KEY));
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_PSK_KEY_EXCHANGE_MODES));
    #endif
    #ifdef WOLFSSL_EARLY_DATA
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_EARLY_DATA));
    #endif
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_COOKIE));
    #ifdef WOLFSSL_POST_HANDSHAKE_AUTH
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_POST_HANDSHAKE_AUTH));
    #endif
        }
#endif
    #if defined(HAVE_CERTIFICATE_STATUS_REQUEST) \
     || defined(HAVE_CERTIFICATE_STATUS_REQUEST_V2)
        if (!ssl->ctx->cm->ocspStaplingEnabled) {
            /* mark already sent, so it won't send it */
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_STATUS_REQUEST));
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_STATUS_REQUEST_V2));
        }
    #endif
    }

#ifdef WOLFSSL_TLS13
    #ifndef NO_CERTS
    else if (msgType == certificate_request) {
        /* Don't send out any extension except those that are turned off. */
        XMEMSET(semaphore, 0xff, SEMAPHORE_SIZE);
#if !defined(WOLFSSL_NO_SIGALG)
        TURN_OFF(semaphore, TLSX_ToSemaphore(TLSX_SIGNATURE_ALGORITHMS));
#endif
        /* TODO: TLSX_SIGNED_CERTIFICATE_TIMESTAMP,
         *       TLSX_CERTIFICATE_AUTHORITIES, OID_FILTERS
         *       TLSX_STATUS_REQUEST
         */
    }
    #endif
#endif
    if (ssl->extensions) {
        ret = TLSX_GetSize(ssl->extensions, semaphore, msgType, &length);
        if (ret != 0)
            return ret;
    }
    if (ssl->ctx && ssl->ctx->extensions) {
        ret = TLSX_GetSize(ssl->ctx->extensions, semaphore, msgType, &length);
        if (ret != 0)
            return ret;
    }

#ifdef HAVE_EXTENDED_MASTER
    if (msgType == client_hello && ssl->options.haveEMS &&
                  (!IsAtLeastTLSv1_3(ssl->version) || ssl->options.downgrade)) {
        length += HELLO_EXT_SZ;
    }
#endif

    if (length)
        length += OPAQUE16_LEN; /* for total length storage. */

    *pLength += length;

    return ret;
}

/** Writes the extensions to be sent into the client hello. */
int TLSX_WriteRequest(WOLFSSL* ssl, byte* output, byte msgType, word16* pOffset)
{
    int ret = 0;
    word16 offset = 0;
    byte semaphore[SEMAPHORE_SIZE] = {0};

    if (!TLSX_SupportExtensions(ssl) || output == NULL)
        return 0;

    offset += OPAQUE16_LEN; /* extensions length */

    if (msgType == client_hello) {
        EC_VALIDATE_REQUEST(ssl, semaphore);
        PF_VALIDATE_REQUEST(ssl, semaphore);
        WOLF_STK_VALIDATE_REQUEST(ssl);
        QSH_VALIDATE_REQUEST(ssl, semaphore);
#if !defined(WOLFSSL_NO_SIGALG)
        if (ssl->suites->hashSigAlgoSz == 0)
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_SIGNATURE_ALGORITHMS));
#endif
#ifdef WOLFSSL_TLS13
        if (!IsAtLeastTLSv1_2(ssl))
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_SUPPORTED_VERSIONS));
        if (!IsAtLeastTLSv1_3(ssl->version)) {
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_KEY_SHARE));
    #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_PSK_KEY_EXCHANGE_MODES));
    #endif
    #ifdef WOLFSSL_EARLY_DATA
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_EARLY_DATA));
    #endif
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_COOKIE));
    #ifdef WOLFSSL_POST_HANDSHAKE_AUTH
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_POST_HANDSHAKE_AUTH));
    #endif
        }
    #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
        /* Must write Pre-shared Key extension at the end in TLS v1.3.
         * Must not write out Pre-shared Key extension in earlier versions of
         * protocol.
         */
        TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_PRE_SHARED_KEY));
    #endif
#endif
    #if defined(HAVE_CERTIFICATE_STATUS_REQUEST) \
     || defined(HAVE_CERTIFICATE_STATUS_REQUEST_V2)
         /* mark already sent, so it won't send it */
        if (!ssl->ctx->cm->ocspStaplingEnabled) {
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_STATUS_REQUEST));
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_STATUS_REQUEST_V2));
        }
    #endif
    }
#ifdef WOLFSSL_TLS13
    #ifndef NO_CERTS
    else if (msgType == certificate_request) {
        /* Don't send out any extension except those that are turned off. */
        XMEMSET(semaphore, 0xff, SEMAPHORE_SIZE);
#if !defined(WOLFSSL_NO_SIGALG)
        TURN_OFF(semaphore, TLSX_ToSemaphore(TLSX_SIGNATURE_ALGORITHMS));
#endif
        /* TODO: TLSX_SIGNED_CERTIFICATE_TIMESTAMP,
         *       TLSX_CERTIFICATE_AUTHORITIES, TLSX_OID_FILTERS
         *       TLSX_STATUS_REQUEST
         */
    }
    #endif
#endif
    if (ssl->extensions) {
        ret = TLSX_Write(ssl->extensions, output + offset, semaphore,
                         msgType, &offset);
        if (ret != 0)
            return ret;
    }
    if (ssl->ctx && ssl->ctx->extensions) {
        ret = TLSX_Write(ssl->ctx->extensions, output + offset, semaphore,
                         msgType, &offset);
        if (ret != 0)
            return ret;
    }

#ifdef HAVE_EXTENDED_MASTER
    if (msgType == client_hello && ssl->options.haveEMS &&
                  (!IsAtLeastTLSv1_3(ssl->version) || ssl->options.downgrade)) {
        WOLFSSL_MSG("EMS extension to write");
        c16toa(HELLO_EXT_EXTMS, output + offset);
        offset += HELLO_EXT_TYPE_SZ;
        c16toa(0, output + offset);
        offset += HELLO_EXT_SZ_SZ;
    }
#endif

#ifdef WOLFSSL_TLS13
    #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
    if (msgType == client_hello && IsAtLeastTLSv1_3(ssl->version)) {
        /* Write out what we can of Pre-shared key extension.  */
        TURN_OFF(semaphore, TLSX_ToSemaphore(TLSX_PRE_SHARED_KEY));
        ret = TLSX_Write(ssl->extensions, output + offset, semaphore,
                         client_hello, &offset);
        if (ret != 0)
            return ret;
    }
    #endif
#endif

    if (offset > OPAQUE16_LEN || msgType != client_hello)
        c16toa(offset - OPAQUE16_LEN, output); /* extensions length */

     *pOffset += offset;

    return ret;
}

#endif /* WOLFSSL_TLS13 || !NO_WOLFSSL_CLIENT */

#if defined(WOLFSSL_TLS13) || !defined(NO_WOLFSSL_SERVER)

/** Tells the buffered size of extensions to be sent into the server hello. */
int TLSX_GetResponseSize(WOLFSSL* ssl, byte msgType, word16* pLength)
{
    int ret = 0;
    word16 length = 0;
    byte semaphore[SEMAPHORE_SIZE] = {0};

    switch (msgType) {
#ifndef NO_WOLFSSL_SERVER
        case server_hello:
            PF_VALIDATE_RESPONSE(ssl, semaphore);
    #ifdef WOLFSSL_TLS13
                if (IsAtLeastTLSv1_3(ssl->version)) {
                    XMEMSET(semaphore, 0xff, SEMAPHORE_SIZE);
                    TURN_OFF(semaphore,
                                     TLSX_ToSemaphore(TLSX_SUPPORTED_VERSIONS));
                    if (!ssl->options.noPskDheKe)
                        TURN_OFF(semaphore, TLSX_ToSemaphore(TLSX_KEY_SHARE));
        #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
                    TURN_OFF(semaphore, TLSX_ToSemaphore(TLSX_PRE_SHARED_KEY));
        #endif
                }
                else {
                    TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_KEY_SHARE));
        #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
                    TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_PRE_SHARED_KEY));
        #endif
                }
    #endif
            break;

    #ifdef WOLFSSL_TLS13
        case hello_retry_request:
            XMEMSET(semaphore, 0xff, SEMAPHORE_SIZE);
                TURN_OFF(semaphore, TLSX_ToSemaphore(TLSX_SUPPORTED_VERSIONS));
            if (!ssl->options.noPskDheKe)
                TURN_OFF(semaphore, TLSX_ToSemaphore(TLSX_KEY_SHARE));
            TURN_OFF(semaphore, TLSX_ToSemaphore(TLSX_COOKIE));
            break;
    #endif

    #ifdef WOLFSSL_TLS13
        case encrypted_extensions:
            /* Send out all extension except those that are turned on. */
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_EC_POINT_FORMATS));
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_SUPPORTED_VERSIONS));
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_SESSION_TICKET));
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_KEY_SHARE));
        #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_PRE_SHARED_KEY));
        #endif
        #ifdef HAVE_CERTIFICATE_STATUS_REQUEST
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_STATUS_REQUEST));
        #endif
        #ifdef HAVE_CERTIFICATE_STATUS_REQUEST_V2
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_STATUS_REQUEST_V2));
        #endif
        #if defined(HAVE_SECURE_RENEGOTIATION)
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_RENEGOTIATION_INFO));
        #endif
            break;

        #ifdef WOLFSSL_EARLY_DATA
        case session_ticket:
            if (ssl->options.tls1_3) {
                XMEMSET(semaphore, 0xff, SEMAPHORE_SIZE);
                TURN_OFF(semaphore, TLSX_ToSemaphore(TLSX_EARLY_DATA));
            }
            break;
        #endif
    #endif
#endif

#ifdef WOLFSSL_TLS13
    #ifndef NO_CERTS
        case certificate:
            /* Don't send out any extension except those that are turned off. */
            XMEMSET(semaphore, 0xff, SEMAPHORE_SIZE);
            TURN_OFF(semaphore, TLSX_ToSemaphore(TLSX_STATUS_REQUEST));
            /* TODO: TLSX_SIGNED_CERTIFICATE_TIMESTAMP,
             *       TLSX_SERVER_CERTIFICATE_TYPE
             */
            break;
    #endif
#endif
    }

    #ifdef HAVE_QSH
        /* change response if not using TLS_QSH */
        if (!ssl->options.haveQSH) {
            TLSX* ext = TLSX_Find(ssl->extensions, TLSX_QUANTUM_SAFE_HYBRID);
            if (ext)
                ext->resp = 0;
        }
    #endif

#ifdef HAVE_EXTENDED_MASTER
    if (ssl->options.haveEMS && msgType == server_hello &&
                                              !IsAtLeastTLSv1_3(ssl->version)) {
        length += HELLO_EXT_SZ;
    }
#endif

    if (TLSX_SupportExtensions(ssl)) {
        ret = TLSX_GetSize(ssl->extensions, semaphore, msgType, &length);
        if (ret != 0)
            return ret;
    }

    /* All the response data is set at the ssl object only, so no ctx here. */

    if (length || msgType != server_hello)
        length += OPAQUE16_LEN; /* for total length storage. */

    *pLength += length;

    return ret;
}

/** Writes the server hello extensions into a buffer. */
int TLSX_WriteResponse(WOLFSSL *ssl, byte* output, byte msgType, word16* pOffset)
{
    int ret = 0;
    word16 offset = 0;

    if (TLSX_SupportExtensions(ssl) && output) {
        byte semaphore[SEMAPHORE_SIZE] = {0};

        switch (msgType) {
#ifndef NO_WOLFSSL_SERVER
            case server_hello:
                PF_VALIDATE_RESPONSE(ssl, semaphore);
    #ifdef WOLFSSL_TLS13
                if (IsAtLeastTLSv1_3(ssl->version)) {
                    XMEMSET(semaphore, 0xff, SEMAPHORE_SIZE);
                    TURN_OFF(semaphore,
                                     TLSX_ToSemaphore(TLSX_SUPPORTED_VERSIONS));
                    if (!ssl->options.noPskDheKe)
                        TURN_OFF(semaphore, TLSX_ToSemaphore(TLSX_KEY_SHARE));
        #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
                    TURN_OFF(semaphore, TLSX_ToSemaphore(TLSX_PRE_SHARED_KEY));
        #endif
                }
                else {
                    TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_KEY_SHARE));
        #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
                    TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_PRE_SHARED_KEY));
        #endif
                }
    #endif
                break;

    #ifdef WOLFSSL_TLS13
            case hello_retry_request:
                XMEMSET(semaphore, 0xff, SEMAPHORE_SIZE);
                TURN_OFF(semaphore, TLSX_ToSemaphore(TLSX_SUPPORTED_VERSIONS));
                if (!ssl->options.noPskDheKe)
                    TURN_OFF(semaphore, TLSX_ToSemaphore(TLSX_KEY_SHARE));
                /* Cookie is written below as last extension. */
                break;
    #endif

    #ifdef WOLFSSL_TLS13
            case encrypted_extensions:
                /* Send out all extension except those that are turned on. */
                TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_EC_POINT_FORMATS));
                TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_SUPPORTED_VERSIONS));
                TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_SESSION_TICKET));
                TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_KEY_SHARE));
        #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
                TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_PRE_SHARED_KEY));
        #endif
        #ifdef HAVE_CERTIFICATE_STATUS_REQUEST
                TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_STATUS_REQUEST));
        #endif
        #ifdef HAVE_CERTIFICATE_STATUS_REQUEST_V2
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_STATUS_REQUEST_V2));
        #endif
        #if defined(HAVE_SECURE_RENEGOTIATION)
            TURN_ON(semaphore, TLSX_ToSemaphore(TLSX_RENEGOTIATION_INFO));
        #endif
                break;

        #ifdef WOLFSSL_EARLY_DATA
            case session_ticket:
                if (ssl->options.tls1_3) {
                    XMEMSET(semaphore, 0xff, SEMAPHORE_SIZE);
                    TURN_OFF(semaphore, TLSX_ToSemaphore(TLSX_EARLY_DATA));
                }
                break;
        #endif
    #endif
#endif

    #ifdef WOLFSSL_TLS13
        #ifndef NO_CERTS
            case certificate:
                /* Don't send out any extension except those that are turned
                 * off. */
                XMEMSET(semaphore, 0xff, SEMAPHORE_SIZE);
                TURN_OFF(semaphore, TLSX_ToSemaphore(TLSX_STATUS_REQUEST));
                /* TODO: TLSX_SIGNED_CERTIFICATE_TIMESTAMP,
                 *       TLSX_SERVER_CERTIFICATE_TYPE
                 */
                break;
        #endif
    #endif
        }

        offset += OPAQUE16_LEN; /* extensions length */

        ret = TLSX_Write(ssl->extensions, output + offset, semaphore,
                         msgType, &offset);
        if (ret != 0)
            return ret;

#ifdef WOLFSSL_TLS13
        if (msgType == hello_retry_request) {
            XMEMSET(semaphore, 0xff, SEMAPHORE_SIZE);
            TURN_OFF(semaphore, TLSX_ToSemaphore(TLSX_COOKIE));
            ret = TLSX_Write(ssl->extensions, output + offset, semaphore,
                             msgType, &offset);
            if (ret != 0)
                return ret;
        }
#endif

#ifdef HAVE_EXTENDED_MASTER
        if (ssl->options.haveEMS && msgType == server_hello &&
                                              !IsAtLeastTLSv1_3(ssl->version)) {
            WOLFSSL_MSG("EMS extension to write");
            c16toa(HELLO_EXT_EXTMS, output + offset);
            offset += HELLO_EXT_TYPE_SZ;
            c16toa(0, output + offset);
            offset += HELLO_EXT_SZ_SZ;
        }
#endif

        if (offset > OPAQUE16_LEN || msgType != server_hello)
            c16toa(offset - OPAQUE16_LEN, output); /* extensions length */
    }

    if (pOffset)
        *pOffset += offset;

    return ret;
}

#endif /* WOLFSSL_TLS13 || !NO_WOLFSSL_SERVER */

#ifdef WOLFSSL_TLS13
int TLSX_ParseVersion(WOLFSSL* ssl, byte* input, word16 length, byte msgType,
                      int* found)
{
    int ret = 0;
    int offset = 0;

    *found = 0;
    while (offset < (int)length) {
        word16 type;
        word16 size;

        if (offset + (2 * OPAQUE16_LEN) > length) {
            ret = BUFFER_ERROR;
            break;
        }

        ato16(input + offset, &type);
        offset += HELLO_EXT_TYPE_SZ;

        ato16(input + offset, &size);
        offset += OPAQUE16_LEN;

        if (offset + size > length) {
            ret = BUFFER_ERROR;
            break;
        }

        if (type == TLSX_SUPPORTED_VERSIONS) {
            *found = 1;

            WOLFSSL_MSG("Supported Versions extension received");

            ret = SV_PARSE(ssl, input + offset, size, msgType);
            break;
        }

        offset += size;
    }

    return ret;
}
#endif

/** Parses a buffer of TLS extensions. */
int TLSX_Parse(WOLFSSL* ssl, byte* input, word16 length, byte msgType,
                                                                 Suites *suites)
{
    int ret = 0;
    word16 offset = 0;
    byte isRequest = (msgType == client_hello ||
                      msgType == certificate_request);

#ifdef HAVE_EXTENDED_MASTER
    byte pendingEMS = 0;
#endif
#if defined(WOLFSSL_TLS13) && (defined(HAVE_SESSION_TICKET) || !defined(NO_PSK))
    int pskDone = 0;
#endif

    if (!ssl || !input || (isRequest && !suites))
        return BAD_FUNC_ARG;

    while (ret == 0 && offset < length) {
        word16 type;
        word16 size;

#if defined(WOLFSSL_TLS13) && (defined(HAVE_SESSION_TICKET) || !defined(NO_PSK))
        if (msgType == client_hello && pskDone)
            return PSK_KEY_ERROR;
#endif

        if (length - offset < HELLO_EXT_TYPE_SZ + OPAQUE16_LEN)
            return BUFFER_ERROR;

        ato16(input + offset, &type);
        offset += HELLO_EXT_TYPE_SZ;

        ato16(input + offset, &size);
        offset += OPAQUE16_LEN;

        if (offset + size > length)
            return BUFFER_ERROR;

        switch (type) {
            case TLSX_SERVER_NAME:
                WOLFSSL_MSG("SNI extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

#ifdef WOLFSSL_TLS13
                if (IsAtLeastTLSv1_3(ssl->version) &&
                        msgType != client_hello &&
                        msgType != server_hello &&
                        msgType != encrypted_extensions) {
                    return EXT_NOT_ALLOWED;
                }
                else if (!IsAtLeastTLSv1_3(ssl->version) &&
                         msgType == encrypted_extensions) {
                    return EXT_NOT_ALLOWED;
                }
#endif
                ret = SNI_PARSE(ssl, input + offset, size, isRequest);
                break;

            case TLSX_TRUSTED_CA_KEYS:
                WOLFSSL_MSG("Trusted CA extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

#ifdef WOLFSSL_TLS13
                if (IsAtLeastTLSv1_3(ssl->version) &&
                        msgType != client_hello &&
                        msgType != encrypted_extensions) {
                    return EXT_NOT_ALLOWED;
                }
#endif
                ret = TCA_PARSE(ssl, input + offset, size, isRequest);
                break;

            case TLSX_MAX_FRAGMENT_LENGTH:
                WOLFSSL_MSG("Max Fragment Length extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

#ifdef WOLFSSL_TLS13
                if (IsAtLeastTLSv1_3(ssl->version) &&
                        msgType != client_hello &&
                        msgType != encrypted_extensions) {
                    return EXT_NOT_ALLOWED;
                }
                else if (!IsAtLeastTLSv1_3(ssl->version) &&
                         msgType == encrypted_extensions) {
                    return EXT_NOT_ALLOWED;
                }
#endif
                ret = MFL_PARSE(ssl, input + offset, size, isRequest);
                break;

            case TLSX_TRUNCATED_HMAC:
                WOLFSSL_MSG("Truncated HMAC extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

#ifdef WOLFSSL_TLS13
                if (IsAtLeastTLSv1_3(ssl->version))
                    break;
#endif
                ret = THM_PARSE(ssl, input + offset, size, isRequest);
                break;

            case TLSX_SUPPORTED_GROUPS:
                WOLFSSL_MSG("Supported Groups extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

#ifdef WOLFSSL_TLS13
                if (IsAtLeastTLSv1_3(ssl->version) &&
                        msgType != client_hello &&
                        msgType != server_hello &&
                        msgType != encrypted_extensions) {
                    return EXT_NOT_ALLOWED;
                }
                else if (!IsAtLeastTLSv1_3(ssl->version) &&
                         msgType == encrypted_extensions) {
                    return EXT_NOT_ALLOWED;
                }
#endif
                ret = EC_PARSE(ssl, input + offset, size, isRequest);
                break;

            case TLSX_EC_POINT_FORMATS:
                WOLFSSL_MSG("Point Formats extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

#ifdef WOLFSSL_TLS13
                if (IsAtLeastTLSv1_3(ssl->version))
                    break;
#endif
                ret = PF_PARSE(ssl, input + offset, size, isRequest);
                break;

            case TLSX_STATUS_REQUEST:
                WOLFSSL_MSG("Certificate Status Request extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

 #ifdef WOLFSSL_TLS13
                if (IsAtLeastTLSv1_3(ssl->version) &&
                        msgType != client_hello &&
                        msgType != certificate_request &&
                        msgType != certificate) {
                     break;
                }
 #endif
                ret = CSR_PARSE(ssl, input + offset, size, isRequest);
                break;

            case TLSX_STATUS_REQUEST_V2:
                WOLFSSL_MSG("Certificate Status Request v2 extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

#ifdef WOLFSSL_TLS13
                if (IsAtLeastTLSv1_3(ssl->version) &&
                        msgType != client_hello &&
                        msgType != certificate_request &&
                        msgType != certificate) {
                    return EXT_NOT_ALLOWED;
                }
#endif
                ret = CSR2_PARSE(ssl, input + offset, size, isRequest);
                break;

#ifdef HAVE_EXTENDED_MASTER
            case HELLO_EXT_EXTMS:
                WOLFSSL_MSG("Extended Master Secret extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

#ifdef WOLFSSL_TLS13
                if (IsAtLeastTLSv1_3(ssl->version))
                    break;
#endif
                if (size != 0)
                    return BUFFER_ERROR;

#ifndef NO_WOLFSSL_SERVER
                if (isRequest)
                    ssl->options.haveEMS = 1;
#endif
                pendingEMS = 1;
                break;
#endif

            case TLSX_RENEGOTIATION_INFO:
                WOLFSSL_MSG("Secure Renegotiation extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

#ifdef WOLFSSL_TLS13
                if (IsAtLeastTLSv1_3(ssl->version))
                    break;
#endif
                ret = SCR_PARSE(ssl, input + offset, size, isRequest);
                break;

            case TLSX_SESSION_TICKET:
                WOLFSSL_MSG("Session Ticket extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

#ifdef WOLFSSL_TLS13
                if (IsAtLeastTLSv1_3(ssl->version) &&
                        msgType != client_hello) {
                    return EXT_NOT_ALLOWED;
                }
#endif
                ret = WOLF_STK_PARSE(ssl, input + offset, size, isRequest);
                break;

            case TLSX_QUANTUM_SAFE_HYBRID:
                WOLFSSL_MSG("Quantum-Safe-Hybrid extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

#ifdef WOLFSSL_TLS13
                if (IsAtLeastTLSv1_3(ssl->version))
                    break;
#endif
                ret = QSH_PARSE(ssl, input + offset, size, isRequest);
                break;

            case TLSX_APPLICATION_LAYER_PROTOCOL:
                WOLFSSL_MSG("ALPN extension received");

            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

#ifdef WOLFSSL_TLS13
                if (IsAtLeastTLSv1_3(ssl->version) &&
                        msgType != client_hello &&
                        msgType != server_hello &&
                        msgType != encrypted_extensions) {
                    return EXT_NOT_ALLOWED;
                }
                else if (!IsAtLeastTLSv1_3(ssl->version) &&
                         msgType == encrypted_extensions) {
                    return EXT_NOT_ALLOWED;
                }
#endif
                ret = ALPN_PARSE(ssl, input + offset, size, isRequest);
                break;
#if !defined(WOLFSSL_NO_SIGALG)
            case TLSX_SIGNATURE_ALGORITHMS:
                WOLFSSL_MSG("Signature Algorithms extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

                if (!IsAtLeastTLSv1_2(ssl))
                    break;
#ifdef WOLFSSL_TLS13
                if (IsAtLeastTLSv1_3(ssl->version) &&
                        msgType != client_hello &&
                        msgType != certificate_request) {
                    return EXT_NOT_ALLOWED;
                }
#endif
                ret = SA_PARSE(ssl, input + offset, size, isRequest, suites);
                break;
#endif

#if defined(HAVE_ENCRYPT_THEN_MAC) && !defined(WOLFSSL_AEAD_ONLY)
            case TLSX_ENCRYPT_THEN_MAC:
                WOLFSSL_MSG("Encrypt-Then-Mac extension received");

                /* Ignore for TLS 1.3+ */
                if (IsAtLeastTLSv1_3(ssl->version))
                    break;

                ret = ETM_PARSE(ssl, input + offset, size, msgType);
                break;
#endif /* HAVE_ENCRYPT_THEN_MAC */

#ifdef WOLFSSL_TLS13
            case TLSX_SUPPORTED_VERSIONS:
                WOLFSSL_MSG("Skipping Supported Versions - already processed");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

                break;

            case TLSX_COOKIE:
                WOLFSSL_MSG("Cookie extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

                if (!IsAtLeastTLSv1_3(ssl->version))
                    break;

                if (msgType != client_hello &&
                        msgType != hello_retry_request) {
                    return EXT_NOT_ALLOWED;
                }

                ret = CKE_PARSE(ssl, input + offset, size, msgType);
                break;

    #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
            case TLSX_PRE_SHARED_KEY:
                WOLFSSL_MSG("Pre-Shared Key extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

                if (!IsAtLeastTLSv1_3(ssl->version))
                    break;

                if (msgType != client_hello && msgType != server_hello)
                    return EXT_NOT_ALLOWED;

                ret = PSK_PARSE(ssl, input + offset, size, msgType);
                pskDone = 1;
                break;

            case TLSX_PSK_KEY_EXCHANGE_MODES:
                WOLFSSL_MSG("PSK Key Exchange Modes extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

                if (!IsAtLeastTLSv1_3(ssl->version))
                    break;

                if (msgType != client_hello)
                    return EXT_NOT_ALLOWED;

                ret = PKM_PARSE(ssl, input + offset, size, msgType);
                break;
    #endif

    #ifdef WOLFSSL_EARLY_DATA
            case TLSX_EARLY_DATA:
                WOLFSSL_MSG("Early Data extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

                if (!IsAtLeastTLSv1_3(ssl->version))
                    break;

                if (msgType != client_hello && msgType != session_ticket &&
                        msgType != encrypted_extensions) {
                    return EXT_NOT_ALLOWED;
                }
                if (!IsAtLeastTLSv1_3(ssl->version) &&
                        (msgType == session_ticket ||
                         msgType == encrypted_extensions)) {
                    return EXT_NOT_ALLOWED;
                }
                ret = EDI_PARSE(ssl, input + offset, size, msgType);
                break;
    #endif

    #ifdef WOLFSSL_POST_HANDSHAKE_AUTH
            case TLSX_POST_HANDSHAKE_AUTH:
                WOLFSSL_MSG("Post Handshake Authentication extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

                if (!IsAtLeastTLSv1_3(ssl->version))
                    break;

                if (msgType != client_hello)
                    return EXT_NOT_ALLOWED;

                ret = PHA_PARSE(ssl, input + offset, size, msgType);
                break;
    #endif

            case TLSX_SIGNATURE_ALGORITHMS_CERT:
                WOLFSSL_MSG("Signature Algorithms extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

                if (!IsAtLeastTLSv1_3(ssl->version))
                    break;

                if (msgType != client_hello &&
                        msgType != certificate_request) {
                    return EXT_NOT_ALLOWED;
                }
                if (!IsAtLeastTLSv1_3(ssl->version) &&
                        msgType == certificate_request) {
                    return EXT_NOT_ALLOWED;
                }

                ret = SAC_PARSE(ssl, input + offset, size, isRequest);
                break;

            case TLSX_KEY_SHARE:
                WOLFSSL_MSG("Key Share extension received");
            #ifdef WOLFSSL_DEBUG_TLS
                WOLFSSL_BUFFER(input + offset, size);
            #endif

                if (!IsAtLeastTLSv1_3(ssl->version))
                    break;

                if (msgType != client_hello && msgType != server_hello &&
                        msgType != hello_retry_request) {
                    return EXT_NOT_ALLOWED;
                }
                ret = KS_PARSE(ssl, input + offset, size, msgType);
                break;
#endif
            default:
                WOLFSSL_MSG("Unknown TLS extension type");
        }

        /* offset should be updated here! */
        offset += size;
    }

#ifdef HAVE_EXTENDED_MASTER
    if (!isRequest && ssl->options.haveEMS && !pendingEMS)
        ssl->options.haveEMS = 0;
#endif

    if (ret == 0)
        ret = SNI_VERIFY_PARSE(ssl, isRequest);
    if (ret == 0)
        ret = TCA_VERIFY_PARSE(ssl, isRequest);

    return ret;
}

/* undefining semaphore macros */
#undef IS_OFF
#undef TURN_ON
#undef SEMAPHORE_SIZE

#endif /* HAVE_TLS_EXTENSIONS */

#ifndef NO_WOLFSSL_CLIENT

    WOLFSSL_METHOD* wolfTLS_client_method(void)
    {
        return wolfTLS_client_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfTLS_client_method_ex(void* heap)
    {
        WOLFSSL_METHOD* method =
                              (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD),
                                                     heap, DYNAMIC_TYPE_METHOD);
        (void)heap;
        WOLFSSL_ENTER("TLS_client_method_ex");
        if (method) {
        #if defined(WOLFSSL_TLS13)
            InitSSL_Method(method, MakeTLSv1_3());
        #elif !defined(WOLFSSL_NO_TLS12)
            InitSSL_Method(method, MakeTLSv1_2());
        #elif !defined(NO_OLD_TLS)
            InitSSL_Method(method, MakeTLSv1_1());
        #elif defined(WOLFSSL_ALLOW_TLSV10)
            InitSSL_Method(method, MakeTLSv1());
        #else
            #error No TLS version enabled!
        #endif

            method->downgrade = 1;
            method->side      = WOLFSSL_CLIENT_END;
        }
        return method;
    }

#ifndef NO_OLD_TLS
    #ifdef WOLFSSL_ALLOW_TLSV10
    WOLFSSL_METHOD* wolfTLSv1_client_method(void)
    {
        return wolfTLSv1_client_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfTLSv1_client_method_ex(void* heap)
    {
        WOLFSSL_METHOD* method =
                             (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD),
                                                     heap, DYNAMIC_TYPE_METHOD);
        (void)heap;
        WOLFSSL_ENTER("TLSv1_client_method_ex");
        if (method)
            InitSSL_Method(method, MakeTLSv1());
        return method;
    }
    #endif /* WOLFSSL_ALLOW_TLSV10 */

    WOLFSSL_METHOD* wolfTLSv1_1_client_method(void)
    {
        return wolfTLSv1_1_client_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfTLSv1_1_client_method_ex(void* heap)
    {
        WOLFSSL_METHOD* method =
                              (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD),
                                                     heap, DYNAMIC_TYPE_METHOD);
        (void)heap;
        WOLFSSL_ENTER("TLSv1_1_client_method_ex");
        if (method)
            InitSSL_Method(method, MakeTLSv1_1());
        return method;
    }
#endif /* !NO_OLD_TLS */

#ifndef WOLFSSL_NO_TLS12
    WOLFSSL_ABI
    WOLFSSL_METHOD* wolfTLSv1_2_client_method(void)
    {
        return wolfTLSv1_2_client_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfTLSv1_2_client_method_ex(void* heap)
    {
        WOLFSSL_METHOD* method =
                              (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD),
                                                     heap, DYNAMIC_TYPE_METHOD);
        (void)heap;
        WOLFSSL_ENTER("TLSv1_2_client_method_ex");
        if (method)
            InitSSL_Method(method, MakeTLSv1_2());
        return method;
    }
#endif /* WOLFSSL_NO_TLS12 */

#ifdef WOLFSSL_TLS13
    /* The TLS v1.3 client method data.
     *
     * returns the method data for a TLS v1.3 client.
     */
    WOLFSSL_ABI
    WOLFSSL_METHOD* wolfTLSv1_3_client_method(void)
    {
        return wolfTLSv1_3_client_method_ex(NULL);
    }

    /* The TLS v1.3 client method data.
     *
     * heap  The heap used for allocation.
     * returns the method data for a TLS v1.3 client.
     */
    WOLFSSL_METHOD* wolfTLSv1_3_client_method_ex(void* heap)
    {
        WOLFSSL_METHOD* method = (WOLFSSL_METHOD*)
                                 XMALLOC(sizeof(WOLFSSL_METHOD), heap,
                                         DYNAMIC_TYPE_METHOD);
        (void)heap;
        WOLFSSL_ENTER("TLSv1_3_client_method_ex");
        if (method)
            InitSSL_Method(method, MakeTLSv1_3());
        return method;
    }
#endif /* WOLFSSL_TLS13 */

#ifdef WOLFSSL_DTLS

    WOLFSSL_METHOD* wolfDTLS_client_method(void)
    {
        return wolfDTLS_client_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfDTLS_client_method_ex(void* heap)
    {
        WOLFSSL_METHOD* method =
                              (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD),
                                                     heap, DYNAMIC_TYPE_METHOD);
        (void)heap;
        WOLFSSL_ENTER("DTLS_client_method_ex");
        if (method) {
        #if !defined(WOLFSSL_NO_TLS12)
            InitSSL_Method(method, MakeDTLSv1_2());
        #elif !defined(NO_OLD_TLS)
            InitSSL_Method(method, MakeDTLSv1());
        #else
            #error No DTLS version enabled!
        #endif

            method->downgrade = 1;
            method->side      = WOLFSSL_CLIENT_END;
        }
        return method;
    }

    #ifndef NO_OLD_TLS
    WOLFSSL_METHOD* wolfDTLSv1_client_method(void)
    {
        return wolfDTLSv1_client_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfDTLSv1_client_method_ex(void* heap)
    {
        WOLFSSL_METHOD* method =
                          (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD),
                                                 heap, DYNAMIC_TYPE_METHOD);
        (void)heap;
        WOLFSSL_ENTER("DTLSv1_client_method_ex");
        if (method)
            InitSSL_Method(method, MakeDTLSv1());
        return method;
    }
    #endif  /* NO_OLD_TLS */

    #ifndef WOLFSSL_NO_TLS12
    WOLFSSL_METHOD* wolfDTLSv1_2_client_method(void)
    {
        return wolfDTLSv1_2_client_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfDTLSv1_2_client_method_ex(void* heap)
    {
        WOLFSSL_METHOD* method =
                          (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD),
                                                 heap, DYNAMIC_TYPE_METHOD);
        (void)heap;
        WOLFSSL_ENTER("DTLSv1_2_client_method_ex");
        if (method)
            InitSSL_Method(method, MakeDTLSv1_2());
        (void)heap;
        return method;
    }
    #endif /* !WOLFSSL_NO_TLS12 */
#endif /* WOLFSSL_DTLS */

#endif /* NO_WOLFSSL_CLIENT */


/* EITHER SIDE METHODS */
#if defined(OPENSSL_EXTRA) || defined(WOLFSSL_EITHER_SIDE)
    #ifndef NO_OLD_TLS
    #ifdef WOLFSSL_ALLOW_TLSV10
    /* Gets a WOLFSL_METHOD type that is not set as client or server
     *
     * Returns a pointer to a WOLFSSL_METHOD struct
     */
    WOLFSSL_METHOD* wolfTLSv1_method(void)
    {
        return wolfTLSv1_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfTLSv1_method_ex(void* heap)
    {
        WOLFSSL_METHOD* m;
        WOLFSSL_ENTER("TLSv1_method");
    #ifndef NO_WOLFSSL_CLIENT
        m = wolfTLSv1_client_method_ex(heap);
    #else
        m = wolfTLSv1_server_method_ex(heap);
    #endif
        if (m != NULL) {
            m->side = WOLFSSL_NEITHER_END;
        }

        return m;
    }
    #endif /* WOLFSSL_ALLOW_TLSV10 */

    /* Gets a WOLFSL_METHOD type that is not set as client or server
     *
     * Returns a pointer to a WOLFSSL_METHOD struct
     */
    WOLFSSL_METHOD* wolfTLSv1_1_method(void)
    {
        return wolfTLSv1_1_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfTLSv1_1_method_ex(void* heap)
    {
        WOLFSSL_METHOD* m;
        WOLFSSL_ENTER("TLSv1_1_method");
    #ifndef NO_WOLFSSL_CLIENT
        m = wolfTLSv1_1_client_method_ex(heap);
    #else
        m = wolfTLSv1_1_server_method_ex(heap);
    #endif
        if (m != NULL) {
            m->side = WOLFSSL_NEITHER_END;
        }
        return m;
    }
    #endif /* !NO_OLD_TLS */

    #ifndef WOLFSSL_NO_TLS12
    /* Gets a WOLFSL_METHOD type that is not set as client or server
     *
     * Returns a pointer to a WOLFSSL_METHOD struct
     */
    WOLFSSL_METHOD* wolfTLSv1_2_method(void)
    {
        return wolfTLSv1_2_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfTLSv1_2_method_ex(void* heap)
    {
        WOLFSSL_METHOD* m;
        WOLFSSL_ENTER("TLSv1_2_method");
    #ifndef NO_WOLFSSL_CLIENT
        m = wolfTLSv1_2_client_method_ex(heap);
    #else
        m = wolfTLSv1_2_server_method_ex(heap);
    #endif
        if (m != NULL) {
            m->side = WOLFSSL_NEITHER_END;
        }
        return m;
    }
    #endif /* !WOLFSSL_NO_TLS12 */

    #ifdef WOLFSSL_TLS13
    /* Gets a WOLFSL_METHOD type that is not set as client or server
     *
     * Returns a pointer to a WOLFSSL_METHOD struct
     */
    WOLFSSL_METHOD* wolfTLSv1_3_method(void)
    {
        return wolfTLSv1_3_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfTLSv1_3_method_ex(void* heap)
    {
        WOLFSSL_METHOD* m;
        WOLFSSL_ENTER("TLSv1_3_method");
    #ifndef NO_WOLFSSL_CLIENT
        m = wolfTLSv1_3_client_method_ex(heap);
    #else
        m = wolfTLSv1_3_server_method_ex(heap);
    #endif
        if (m != NULL) {
            m->side = WOLFSSL_NEITHER_END;
        }
        return m;
    }
    #endif /* WOLFSSL_TLS13 */

#ifdef WOLFSSL_DTLS
    WOLFSSL_METHOD* wolfDTLS_method(void)
    {
        return wolfDTLS_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfDTLS_method_ex(void* heap)
    {
        WOLFSSL_METHOD* m;
        WOLFSSL_ENTER("DTLS_method_ex");
    #ifndef NO_WOLFSSL_CLIENT
        m = wolfDTLS_client_method_ex(heap);
    #else
        m = wolfDTLS_server_method_ex(heap);
    #endif
        if (m != NULL) {
            m->side = WOLFSSL_NEITHER_END;
        }
        return m;
    }

    #ifndef NO_OLD_TLS
    WOLFSSL_METHOD* wolfDTLSv1_method(void)
    {
        return wolfDTLSv1_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfDTLSv1_method_ex(void* heap)
    {
        WOLFSSL_METHOD* m;
        WOLFSSL_ENTER("DTLSv1_method_ex");
    #ifndef NO_WOLFSSL_CLIENT
        m = wolfDTLSv1_client_method_ex(heap);
    #else
        m = wolfDTLSv1_server_method_ex(heap);
    #endif
        if (m != NULL) {
            m->side = WOLFSSL_NEITHER_END;
        }
        return m;
    }
    #endif /* !NO_OLD_TLS */
    #ifndef WOLFSSL_NO_TLS12
    WOLFSSL_METHOD* wolfDTLSv1_2_method(void)
    {
        return wolfDTLSv1_2_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfDTLSv1_2_method_ex(void* heap)
    {
        WOLFSSL_METHOD* m;
        WOLFSSL_ENTER("DTLSv1_2_method");
    #ifndef NO_WOLFSSL_CLIENT
        m = wolfDTLSv1_2_client_method_ex(heap);
    #else
        m = wolfDTLSv1_2_server_method_ex(heap);
    #endif
        if (m != NULL) {
            m->side = WOLFSSL_NEITHER_END;
        }
        return m;
    }
    #endif /* !WOLFSSL_NO_TLS12 */
#endif /* WOLFSSL_DTLS */
#endif /* OPENSSL_EXTRA || WOLFSSL_EITHER_SIDE */


#ifndef NO_WOLFSSL_SERVER

    WOLFSSL_METHOD* wolfTLS_server_method(void)
    {
        return wolfTLS_server_method_ex(NULL);
    }

    WOLFSSL_METHOD* wolfTLS_server_method_ex(void* heap)
    {
        WOLFSSL_METHOD* method =
                              (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD),
                                                     heap, DYNAMIC_TYPE_METHOD);
        (void)heap;
        WOLFSSL_ENTER("TLS_server_method_ex");
        if (method) {
        #if defined(WOLFSSL_TLS13)
            InitSSL_Method(method, MakeTLSv1_3());
        #elif !defined(WOLFSSL_NO_TLS12)
            InitSSL_Method(method, MakeTLSv1_2());
        #elif !defined(NO_OLD_TLS)
            InitSSL_Method(method, MakeTLSv1_1());
        #elif defined(WOLFSSL_ALLOW_TLSV10)
            InitSSL_Method(method, MakeTLSv1());
        #else
            #error No TLS version enabled!
        #endif

            method->downgrade = 1;
            method->side      = WOLFSSL_SERVER_END;
        }
        return method;
    }

#ifndef NO_OLD_TLS
    #ifdef WOLFSSL_ALLOW_TLSV10
    WOLFSSL_METHOD* wolfTLSv1_server_method(void)
    {
        return wolfTLSv1_server_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfTLSv1_server_method_ex(void* heap)
    {
        WOLFSSL_METHOD* method =
                              (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD),
                                                     heap, DYNAMIC_TYPE_METHOD);
        (void)heap;
        WOLFSSL_ENTER("TLSv1_server_method_ex");
        if (method) {
            InitSSL_Method(method, MakeTLSv1());
            method->side = WOLFSSL_SERVER_END;
        }
        return method;
    }
    #endif /* WOLFSSL_ALLOW_TLSV10 */

    WOLFSSL_METHOD* wolfTLSv1_1_server_method(void)
    {
        return wolfTLSv1_1_server_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfTLSv1_1_server_method_ex(void* heap)
    {
        WOLFSSL_METHOD* method =
                              (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD),
                                                     heap, DYNAMIC_TYPE_METHOD);
        (void)heap;
        WOLFSSL_ENTER("TLSv1_1_server_method_ex");
        if (method) {
            InitSSL_Method(method, MakeTLSv1_1());
            method->side = WOLFSSL_SERVER_END;
        }
        return method;
    }
#endif /* !NO_OLD_TLS */


#ifndef WOLFSSL_NO_TLS12
    WOLFSSL_ABI
    WOLFSSL_METHOD* wolfTLSv1_2_server_method(void)
    {
        return wolfTLSv1_2_server_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfTLSv1_2_server_method_ex(void* heap)
    {
        WOLFSSL_METHOD* method =
                              (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD),
                                                     heap, DYNAMIC_TYPE_METHOD);
        (void)heap;
        WOLFSSL_ENTER("TLSv1_2_server_method_ex");
        if (method) {
            InitSSL_Method(method, MakeTLSv1_2());
            method->side = WOLFSSL_SERVER_END;
        }
        return method;
    }
#endif /* !WOLFSSL_NO_TLS12 */

#ifdef WOLFSSL_TLS13
    /* The TLS v1.3 server method data.
     *
     * returns the method data for a TLS v1.3 server.
     */
    WOLFSSL_ABI
    WOLFSSL_METHOD* wolfTLSv1_3_server_method(void)
    {
        return wolfTLSv1_3_server_method_ex(NULL);
    }

    /* The TLS v1.3 server method data.
     *
     * heap  The heap used for allocation.
     * returns the method data for a TLS v1.3 server.
     */
    WOLFSSL_METHOD* wolfTLSv1_3_server_method_ex(void* heap)
    {
        WOLFSSL_METHOD* method =
                              (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD),
                                                     heap, DYNAMIC_TYPE_METHOD);
        (void)heap;
        WOLFSSL_ENTER("TLSv1_3_server_method_ex");
        if (method) {
            InitSSL_Method(method, MakeTLSv1_3());
            method->side = WOLFSSL_SERVER_END;
        }
        return method;
    }
#endif /* WOLFSSL_TLS13 */

#ifdef WOLFSSL_DTLS
    WOLFSSL_METHOD* wolfDTLS_server_method(void)
    {
        return wolfDTLS_server_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfDTLS_server_method_ex(void* heap)
    {
        WOLFSSL_METHOD* method =
                              (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD),
                                                     heap, DYNAMIC_TYPE_METHOD);
        (void)heap;
        WOLFSSL_ENTER("DTLS_server_method_ex");
        if (method) {
        #if !defined(WOLFSSL_NO_TLS12)
            InitSSL_Method(method, MakeDTLSv1_2());
        #elif !defined(NO_OLD_TLS)
            InitSSL_Method(method, MakeDTLSv1());
        #else
            #error No DTLS version enabled!
        #endif

            method->downgrade = 1;
            method->side      = WOLFSSL_SERVER_END;
        }
        return method;
    }

    #ifndef NO_OLD_TLS
    WOLFSSL_METHOD* wolfDTLSv1_server_method(void)
    {
        return wolfDTLSv1_server_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfDTLSv1_server_method_ex(void* heap)
    {
        WOLFSSL_METHOD* method =
                          (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD),
                                                 heap, DYNAMIC_TYPE_METHOD);
        (void)heap;
        WOLFSSL_ENTER("DTLSv1_server_method_ex");
        if (method) {
            InitSSL_Method(method, MakeDTLSv1());
            method->side = WOLFSSL_SERVER_END;
        }
        return method;
    }
    #endif /* !NO_OLD_TLS */

    #ifndef WOLFSSL_NO_TLS12
    WOLFSSL_METHOD* wolfDTLSv1_2_server_method(void)
    {
        return wolfDTLSv1_2_server_method_ex(NULL);
    }
    WOLFSSL_METHOD* wolfDTLSv1_2_server_method_ex(void* heap)
    {
        WOLFSSL_METHOD* method =
                          (WOLFSSL_METHOD*) XMALLOC(sizeof(WOLFSSL_METHOD),
                                                 heap, DYNAMIC_TYPE_METHOD);
        WOLFSSL_ENTER("DTLSv1_2_server_method_ex");
        (void)heap;
        if (method) {
            InitSSL_Method(method, MakeDTLSv1_2());
            method->side = WOLFSSL_SERVER_END;
        }
        (void)heap;
        return method;
    }
    #endif /* !WOLFSSL_NO_TLS12 */
#endif /* WOLFSSL_DTLS */

#endif /* NO_WOLFSSL_SERVER */

#endif /* NO_TLS */
#endif /* WOLFCRYPT_ONLY */
