/* tls.c
 *
 * Copyright (C) 2006-2012 Sawtooth Consulting Ltd.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <cyassl/ssl.h>
#include <cyassl/internal.h>
#include <cyassl/error.h>
#include <cyassl/ctaocrypt/hmac.h>



#ifndef NO_TLS


#ifndef min

    static INLINE word32 min(word32 a, word32 b)
    {
        return a > b ? b : a;
    }

#endif /* min */


/* calculate XOR for TLSv1 PRF */
static INLINE void get_xor(byte *digest, word32 digLen, byte* md5, byte* sha)
{
    word32 i;

    for (i = 0; i < digLen; i++) 
        digest[i] = md5[i] ^ sha[i];
}


#ifdef CYASSL_SHA384
    #define PHASH_MAX_DIGEST_SIZE SHA384_DIGEST_SIZE
#else
    #define PHASH_MAX_DIGEST_SIZE SHA256_DIGEST_SIZE
#endif

/* compute p_hash for MD5, SHA-1, SHA-256, or SHA-384 for TLSv1 PRF */
static void p_hash(byte* result, word32 resLen, const byte* secret,
                   word32 secLen, const byte* seed, word32 seedLen, int hash)
{
    word32   len = MD5_DIGEST_SIZE;
    word32   times;
    word32   lastLen;
    word32   lastTime;
    word32   i;
    word32   idx = 0;
    byte     previous[PHASH_MAX_DIGEST_SIZE];  /* max size */
    byte     current[PHASH_MAX_DIGEST_SIZE];   /* max size */

    Hmac hmac;

    if (hash == md5_mac) {
        hash = MD5;
    }
    else if (hash == sha_mac) {
        len = SHA_DIGEST_SIZE;
        hash = SHA;
    } else if (hash == sha256_mac) {
        len = SHA256_DIGEST_SIZE;
        hash = SHA256;
    }
#ifdef CYASSL_SHA384
    else if (hash == sha384_mac)
    {
        len = SHA384_DIGEST_SIZE;
        hash = SHA384;
    }
#endif

    times = resLen / len;
    lastLen = resLen % len;
    if (lastLen) times += 1;
    lastTime = times - 1;

    HmacSetKey(&hmac, hash, secret, secLen);
    HmacUpdate(&hmac, seed, seedLen);       /* A0 = seed */
    HmacFinal(&hmac, previous);             /* A1 */

    for (i = 0; i < times; i++) {
        HmacUpdate(&hmac, previous, len);
        HmacUpdate(&hmac, seed, seedLen);
        HmacFinal(&hmac, current);

        if ( (i == lastTime) && lastLen)
            XMEMCPY(&result[idx], current, min(lastLen, sizeof(current)));
        else {
            XMEMCPY(&result[idx], current, len);
            idx += len;
            HmacUpdate(&hmac, previous, len);
            HmacFinal(&hmac, previous);
        }
    }
}



/* compute TLSv1 PRF (pseudo random function using HMAC) */
static void PRF(byte* digest, word32 digLen, const byte* secret, word32 secLen,
            const byte* label, word32 labLen, const byte* seed, word32 seedLen,
            int useAtLeastSha256, int hash_type)
{
    word32 half = (secLen + 1) / 2;

    byte md5_half[MAX_PRF_HALF];        /* half is real size */
    byte sha_half[MAX_PRF_HALF];        /* half is real size */
    byte labelSeed[MAX_PRF_LABSEED];    /* labLen + seedLen is real size */
    byte md5_result[MAX_PRF_DIG];       /* digLen is real size */
    byte sha_result[MAX_PRF_DIG];       /* digLen is real size */

    if (half > MAX_PRF_HALF)
        return;
    if (labLen + seedLen > MAX_PRF_LABSEED)
        return;
    if (digLen > MAX_PRF_DIG)
        return;
    
    XMEMCPY(md5_half, secret, half);
    XMEMCPY(sha_half, secret + half - secLen % 2, half);

    XMEMCPY(labelSeed, label, labLen);
    XMEMCPY(labelSeed + labLen, seed, seedLen);

    if (useAtLeastSha256) {
        /* If a cipher suite wants an algorithm better than sha256, it
         * should use better. */
        if (hash_type < sha256_mac)
            hash_type = sha256_mac;
        p_hash(digest, digLen, secret, secLen, labelSeed, labLen + seedLen,
               hash_type);
        return;
    }

    p_hash(md5_result, digLen, md5_half, half, labelSeed, labLen + seedLen,
           md5_mac);
    p_hash(sha_result, digLen, sha_half, half, labelSeed, labLen + seedLen,
           sha_mac);
    get_xor(digest, digLen, md5_result, sha_result);
}


#ifdef CYASSL_SHA384
    #define HSHASH_SZ SHA384_DIGEST_SIZE
#else
    #define HSHASH_SZ FINISHED_SZ
#endif


void BuildTlsFinished(CYASSL* ssl, Hashes* hashes, const byte* sender)
{
    const byte* side;
    byte        handshake_hash[HSHASH_SZ];
    word32      hashSz = FINISHED_SZ;

    Md5Final(&ssl->hashMd5, handshake_hash);
    ShaFinal(&ssl->hashSha, &handshake_hash[MD5_DIGEST_SIZE]);
    if (IsAtLeastTLSv1_2(ssl)) {
#ifndef NO_SHA256
        if (ssl->specs.mac_algorithm <= sha256_mac) {
            Sha256Final(&ssl->hashSha256, handshake_hash);
            hashSz = SHA256_DIGEST_SIZE;
        }
#endif
#ifdef CYASSL_SHA384
        if (ssl->specs.mac_algorithm == sha384_mac) {
            Sha384Final(&ssl->hashSha384, handshake_hash);
            hashSz = SHA384_DIGEST_SIZE;
        }
#endif
    }
   
    if ( XSTRNCMP((const char*)sender, (const char*)client, SIZEOF_SENDER) == 0)
        side = tls_client;
    else
        side = tls_server;

    PRF(hashes->md5, TLS_FINISHED_SZ, ssl->arrays.masterSecret, SECRET_LEN,
        side, FINISHED_LABEL_SZ, handshake_hash, hashSz, IsAtLeastTLSv1_2(ssl),
        ssl->specs.mac_algorithm);
}


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


ProtocolVersion MakeTLSv1_2(void)
{
    ProtocolVersion pv;
    pv.major = SSLv3_MAJOR;
    pv.minor = TLSv1_2_MINOR;

    return pv;
}


static const byte master_label[MASTER_LABEL_SZ + 1] = "master secret";
static const byte key_label   [KEY_LABEL_SZ + 1]    = "key expansion";


int DeriveTlsKeys(CYASSL* ssl)
{
    int length = 2 * ssl->specs.hash_size + 
                 2 * ssl->specs.key_size  +
                 2 * ssl->specs.iv_size;
    byte         seed[SEED_LEN];
    byte         key_data[MAX_PRF_DIG];

    XMEMCPY(seed, ssl->arrays.serverRandom, RAN_LEN);
    XMEMCPY(&seed[RAN_LEN], ssl->arrays.clientRandom, RAN_LEN);

    PRF(key_data, length, ssl->arrays.masterSecret, SECRET_LEN, key_label,
        KEY_LABEL_SZ, seed, SEED_LEN, IsAtLeastTLSv1_2(ssl),
        ssl->specs.mac_algorithm);

    return StoreKeys(ssl, key_data);
}


int MakeTlsMasterSecret(CYASSL* ssl)
{
    byte seed[SEED_LEN];
    
    XMEMCPY(seed, ssl->arrays.clientRandom, RAN_LEN);
    XMEMCPY(&seed[RAN_LEN], ssl->arrays.serverRandom, RAN_LEN);

    PRF(ssl->arrays.masterSecret, SECRET_LEN,
        ssl->arrays.preMasterSecret, ssl->arrays.preMasterSz,
        master_label, MASTER_LABEL_SZ, 
        seed, SEED_LEN, IsAtLeastTLSv1_2(ssl), ssl->specs.mac_algorithm);

#ifdef SHOW_SECRETS
    {
        int i;
        printf("master secret: ");
        for (i = 0; i < SECRET_LEN; i++)
            printf("%02x", ssl->arrays.masterSecret[i]);
        printf("\n");
    }
#endif

    return DeriveTlsKeys(ssl);
}


/*** next for static INLINE s copied from cyassl_int.c ***/

/* convert 16 bit integer to opaque */
INLINE static void c16toa(word16 u16, byte* c)
{
    c[0] = (u16 >> 8) & 0xff;
    c[1] =  u16 & 0xff;
}


/* convert 32 bit integer to opaque */
static INLINE void c32toa(word32 u32, byte* c)
{
    c[0] = (u32 >> 24) & 0xff;
    c[1] = (u32 >> 16) & 0xff;
    c[2] = (u32 >>  8) & 0xff;
    c[3] =  u32 & 0xff;
}


static INLINE word32 GetSEQIncrement(CYASSL* ssl, int verify)
{
#ifdef CYASSL_DTLS
    if (ssl->options.dtls) {
        if (verify)
            return ssl->keys.dtls_peer_sequence_number; /* explicit from peer */
        else
            return ssl->keys.dtls_sequence_number - 1; /* already incremented */
    }
#endif
    if (verify)
        return ssl->keys.peer_sequence_number++; 
    else
        return ssl->keys.sequence_number++; 
}


#ifdef CYASSL_DTLS

static INLINE word32 GetEpoch(CYASSL* ssl, int verify)
{
    if (verify)
        return ssl->keys.dtls_peer_epoch; 
    else
        return ssl->keys.dtls_epoch; 
}

#endif /* CYASSL_DTLS */


static INLINE const byte* GetMacSecret(CYASSL* ssl, int verify)
{
    if ( (ssl->options.side == CLIENT_END && !verify) ||
         (ssl->options.side == SERVER_END &&  verify) )
        return ssl->keys.client_write_MAC_secret;
    else
        return ssl->keys.server_write_MAC_secret;
}

/*** end copy ***/


/* TLS type HMAC */
void TLS_hmac(CYASSL* ssl, byte* digest, const byte* in, word32 sz,
              int content, int verify)
{
    Hmac hmac;
    byte seq[SEQ_SZ] = { 0x00, 0x00, 0x00, 0x00 };
    byte length[LENGTH_SZ];
    byte inner[ENUM_LEN + VERSION_SZ + LENGTH_SZ]; /* type + version +len */
    int  type;

    c16toa((word16)sz, length);
#ifdef CYASSL_DTLS
    if (ssl->options.dtls)
        c16toa(GetEpoch(ssl, verify), seq);
#endif
    c32toa(GetSEQIncrement(ssl, verify), &seq[sizeof(word32)]);
    
    if (ssl->specs.mac_algorithm == md5_mac)
        type = MD5;
    else if (ssl->specs.mac_algorithm == sha_mac)
        type = SHA;
    else
        type = SHA256;
    HmacSetKey(&hmac, type, GetMacSecret(ssl, verify), ssl->specs.hash_size);
    
    HmacUpdate(&hmac, seq, SEQ_SZ);                               /* seq_num */
    inner[0] = (byte)content;                                     /* type */
    inner[ENUM_LEN] = ssl->version.major;
    inner[ENUM_LEN + ENUM_LEN] = ssl->version.minor;              /* version */
    XMEMCPY(&inner[ENUM_LEN + VERSION_SZ], length, LENGTH_SZ);     /* length */
    HmacUpdate(&hmac, inner, sizeof(inner));
    HmacUpdate(&hmac, in, sz);                                /* content */
    HmacFinal(&hmac, digest);
}


#ifndef NO_CYASSL_CLIENT

    CYASSL_METHOD* CyaTLSv1_client_method(void)
    {
        CYASSL_METHOD* method =
                             (CYASSL_METHOD*) XMALLOC(sizeof(CYASSL_METHOD), 0,
                                                      DYNAMIC_TYPE_METHOD);
        if (method)
            InitSSL_Method(method, MakeTLSv1());
        return method;
    }


    CYASSL_METHOD* CyaTLSv1_1_client_method(void)
    {
        CYASSL_METHOD* method =
                              (CYASSL_METHOD*) XMALLOC(sizeof(CYASSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
        if (method)
            InitSSL_Method(method, MakeTLSv1_1());
        return method;
    }


#ifndef NO_SHA256   /* can't use without SHA256 */

    CYASSL_METHOD* CyaTLSv1_2_client_method(void)
    {
        CYASSL_METHOD* method =
                              (CYASSL_METHOD*) XMALLOC(sizeof(CYASSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
        if (method)
            InitSSL_Method(method, MakeTLSv1_2());
        return method;
    }

#endif


    CYASSL_METHOD* CyaSSLv23_client_method(void)
    {
        CYASSL_METHOD* method =
                              (CYASSL_METHOD*) XMALLOC(sizeof(CYASSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
        if (method) {
#ifndef NO_SHA256         /* 1.2 requires SHA256 */
            InitSSL_Method(method, MakeTLSv1_2());
#else
            InitSSL_Method(method, MakeTLSv1_1());
#endif
            method->downgrade = 1;
        }
        return method;
    }


#endif /* NO_CYASSL_CLIENT */



#ifndef NO_CYASSL_SERVER

    CYASSL_METHOD* CyaTLSv1_server_method(void)
    {
        CYASSL_METHOD* method =
                              (CYASSL_METHOD*) XMALLOC(sizeof(CYASSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
        if (method) {
            InitSSL_Method(method, MakeTLSv1());
            method->side = SERVER_END;
        }
        return method;
    }


    CYASSL_METHOD* CyaTLSv1_1_server_method(void)
    {
        CYASSL_METHOD* method =
                              (CYASSL_METHOD*) XMALLOC(sizeof(CYASSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
        if (method) {
            InitSSL_Method(method, MakeTLSv1_1());
            method->side = SERVER_END;
        }
        return method;
    }


#ifndef NO_SHA256   /* can't use without SHA256 */

    CYASSL_METHOD* CyaTLSv1_2_server_method(void)
    {
        CYASSL_METHOD* method =
                              (CYASSL_METHOD*) XMALLOC(sizeof(CYASSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
        if (method) {
            InitSSL_Method(method, MakeTLSv1_2());
            method->side = SERVER_END;
        }
        return method;
    }

#endif


    CYASSL_METHOD* CyaSSLv23_server_method(void)
    {
        CYASSL_METHOD* method =
                              (CYASSL_METHOD*) XMALLOC(sizeof(CYASSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
        if (method) {
#ifndef NO_SHA256         /* 1.2 requires SHA256 */
            InitSSL_Method(method, MakeTLSv1_2());
#else
            InitSSL_Method(method, MakeTLSv1_1());
#endif
            method->side      = SERVER_END;
            method->downgrade = 1;
        }
        return method;
    }



#endif /* NO_CYASSL_SERVER */

#else /* NO_TLS */

/* catch CyaSSL programming errors */
void BuildTlsFinished(CYASSL* ssl, Hashes* hashes, const byte* sender)
{
   
}


int DeriveTlsKeys(CYASSL* ssl)
{
    return NOT_COMPILED_IN;
}


int MakeTlsMasterSecret(CYASSL* ssl)
{ 
    return NOT_COMPILED_IN;
}

#endif /* NO_TLS */

