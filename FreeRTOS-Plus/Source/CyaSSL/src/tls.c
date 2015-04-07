/* tls.c
 *
 * Copyright (C) 2006-2014 wolfSSL Inc.
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <cyassl/ctaocrypt/settings.h>

#include <cyassl/ssl.h>
#include <cyassl/internal.h>
#include <cyassl/error-ssl.h>
#include <cyassl/ctaocrypt/hmac.h>



#ifndef NO_TLS


#ifndef min

    static INLINE word32 min(word32 a, word32 b)
    {
        return a > b ? b : a;
    }

#endif /* min */


#ifdef CYASSL_SHA384
    #define PHASH_MAX_DIGEST_SIZE SHA384_DIGEST_SIZE
#else
    #define PHASH_MAX_DIGEST_SIZE SHA256_DIGEST_SIZE
#endif

/* compute p_hash for MD5, SHA-1, SHA-256, or SHA-384 for TLSv1 PRF */
static int p_hash(byte* result, word32 resLen, const byte* secret,
                   word32 secLen, const byte* seed, word32 seedLen, int hash)
{
    word32   len = PHASH_MAX_DIGEST_SIZE;
    word32   times;
    word32   lastLen;
    word32   lastTime;
    word32   i;
    word32   idx = 0;
    int      ret;
    byte     previous[PHASH_MAX_DIGEST_SIZE];  /* max size */
    byte     current[PHASH_MAX_DIGEST_SIZE];   /* max size */

    Hmac hmac;

    switch (hash) {
        #ifndef NO_MD5
        case md5_mac:
        {
            len = MD5_DIGEST_SIZE;
            hash = MD5;
        }
        break;
        #endif
        #ifndef NO_SHA256
        case sha256_mac:
        {
            len = SHA256_DIGEST_SIZE;
            hash = SHA256;
        }
        break;
        #endif
        #ifdef CYASSL_SHA384
        case sha384_mac:
        {
            len = SHA384_DIGEST_SIZE;
            hash = SHA384;
        }
        break;
        #endif
#ifndef NO_SHA
        case sha_mac:
        default:
        {
            len = SHA_DIGEST_SIZE;
            hash = SHA;
        }
        break;
#endif
    }

    times = resLen / len;
    lastLen = resLen % len;
    if (lastLen) times += 1;
    lastTime = times - 1;

    ret = HmacSetKey(&hmac, hash, secret, secLen);
    if (ret != 0)
        return ret;
    ret = HmacUpdate(&hmac, seed, seedLen);       /* A0 = seed */
    if (ret != 0)
        return ret;
    ret = HmacFinal(&hmac, previous);             /* A1 */
    if (ret != 0)
        return ret;

    for (i = 0; i < times; i++) {
        ret = HmacUpdate(&hmac, previous, len);
        if (ret != 0)
            return ret;
        ret = HmacUpdate(&hmac, seed, seedLen);
        if (ret != 0)
            return ret;
        ret = HmacFinal(&hmac, current);
        if (ret != 0)
            return ret;

        if ( (i == lastTime) && lastLen)
            XMEMCPY(&result[idx], current, min(lastLen, sizeof(current)));
        else {
            XMEMCPY(&result[idx], current, len);
            idx += len;
            ret = HmacUpdate(&hmac, previous, len);
            if (ret != 0)
                return ret;
            ret = HmacFinal(&hmac, previous);
            if (ret != 0)
                return ret;
        }
    }
    XMEMSET(previous, 0, sizeof previous);
    XMEMSET(current, 0, sizeof current);
    XMEMSET(&hmac, 0, sizeof hmac);

    return 0;
}



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
    int    ret;
    word32 half = (secLen + 1) / 2;

    byte md5_half[MAX_PRF_HALF];        /* half is real size */
    byte sha_half[MAX_PRF_HALF];        /* half is real size */
    byte labelSeed[MAX_PRF_LABSEED];    /* labLen + seedLen is real size */
    byte md5_result[MAX_PRF_DIG];       /* digLen is real size */
    byte sha_result[MAX_PRF_DIG];       /* digLen is real size */

    if (half > MAX_PRF_HALF)
        return BUFFER_E;
    if (labLen + seedLen > MAX_PRF_LABSEED)
        return BUFFER_E;
    if (digLen > MAX_PRF_DIG)
        return BUFFER_E;

    XMEMSET(md5_result, 0, digLen);
    XMEMSET(sha_result, 0, digLen);
    
    XMEMCPY(md5_half, secret, half);
    XMEMCPY(sha_half, secret + half - secLen % 2, half);

    XMEMCPY(labelSeed, label, labLen);
    XMEMCPY(labelSeed + labLen, seed, seedLen);

    ret = p_hash(md5_result, digLen, md5_half, half, labelSeed,
                 labLen + seedLen, md5_mac);
    if (ret != 0)
        return ret;
    ret = p_hash(sha_result, digLen, sha_half, half, labelSeed,
                 labLen + seedLen, sha_mac);
    if (ret != 0)
        return ret;
    get_xor(digest, digLen, md5_result, sha_result);

    return 0;
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
        byte labelSeed[MAX_PRF_LABSEED];    /* labLen + seedLen is real size */

        if (labLen + seedLen > MAX_PRF_LABSEED)
            return BUFFER_E;

        XMEMCPY(labelSeed, label, labLen);
        XMEMCPY(labelSeed + labLen, seed, seedLen);

        /* If a cipher suite wants an algorithm better than sha256, it
         * should use better. */
        if (hash_type < sha256_mac)
            hash_type = sha256_mac;
        ret = p_hash(digest, digLen, secret, secLen, labelSeed,
                     labLen + seedLen, hash_type);
    }
#ifndef NO_OLD_TLS
    else {
        ret = doPRF(digest, digLen, secret, secLen, label, labLen, seed,
                    seedLen);
    }
#endif

    return ret;
}


#ifdef CYASSL_SHA384
    #define HSHASH_SZ SHA384_DIGEST_SIZE
#else
    #define HSHASH_SZ FINISHED_SZ
#endif


int BuildTlsFinished(CYASSL* ssl, Hashes* hashes, const byte* sender)
{
    const byte* side;
    byte        handshake_hash[HSHASH_SZ];
    word32      hashSz = FINISHED_SZ;

#ifndef NO_OLD_TLS
    Md5Final(&ssl->hashMd5, handshake_hash);
    ShaFinal(&ssl->hashSha, &handshake_hash[MD5_DIGEST_SIZE]);
#endif
    
    if (IsAtLeastTLSv1_2(ssl)) {
#ifndef NO_SHA256
        if (ssl->specs.mac_algorithm <= sha256_mac) {
            int ret = Sha256Final(&ssl->hashSha256, handshake_hash);

            if (ret != 0)
                return ret;

            hashSz = SHA256_DIGEST_SIZE;
        }
#endif
#ifdef CYASSL_SHA384
        if (ssl->specs.mac_algorithm == sha384_mac) {
            int ret = Sha384Final(&ssl->hashSha384, handshake_hash);

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


int DeriveTlsKeys(CYASSL* ssl)
{
    int ret;
    int length = 2 * ssl->specs.hash_size + 
                 2 * ssl->specs.key_size  +
                 2 * ssl->specs.iv_size;
    byte         seed[SEED_LEN];
    byte         key_data[MAX_PRF_DIG];

    XMEMCPY(seed, ssl->arrays->serverRandom, RAN_LEN);
    XMEMCPY(&seed[RAN_LEN], ssl->arrays->clientRandom, RAN_LEN);

    ret = PRF(key_data, length, ssl->arrays->masterSecret, SECRET_LEN, 
              key_label, KEY_LABEL_SZ, seed, SEED_LEN, IsAtLeastTLSv1_2(ssl),
              ssl->specs.mac_algorithm);
    if (ret != 0)
        return ret;

    return StoreKeys(ssl, key_data);
}


int MakeTlsMasterSecret(CYASSL* ssl)
{
    int  ret;
    byte seed[SEED_LEN];
    
    XMEMCPY(seed, ssl->arrays->clientRandom, RAN_LEN);
    XMEMCPY(&seed[RAN_LEN], ssl->arrays->serverRandom, RAN_LEN);

    ret = PRF(ssl->arrays->masterSecret, SECRET_LEN,
              ssl->arrays->preMasterSecret, ssl->arrays->preMasterSz,
              master_label, MASTER_LABEL_SZ, 
              seed, SEED_LEN, IsAtLeastTLSv1_2(ssl), ssl->specs.mac_algorithm);
    if (ret != 0)
        return ret;

#ifdef SHOW_SECRETS
    {
        int i;
        printf("master secret: ");
        for (i = 0; i < SECRET_LEN; i++)
            printf("%02x", ssl->arrays->masterSecret[i]);
        printf("\n");
    }
#endif

    return DeriveTlsKeys(ssl);
}


/* Used by EAP-TLS and EAP-TTLS to derive keying material from
 * the master_secret. */
int CyaSSL_make_eap_keys(CYASSL* ssl, void* msk, unsigned int len,
                                                              const char* label)
{
    byte seed[SEED_LEN];

    /*
     * As per RFC-5281, the order of the client and server randoms is reversed
     * from that used by the TLS protocol to derive keys.
     */
    XMEMCPY(seed, ssl->arrays->clientRandom, RAN_LEN);
    XMEMCPY(&seed[RAN_LEN], ssl->arrays->serverRandom, RAN_LEN);

    return PRF((byte*)msk, len,
               ssl->arrays->masterSecret, SECRET_LEN,
               (const byte *)label, (word32)strlen(label),
               seed, SEED_LEN, IsAtLeastTLSv1_2(ssl), ssl->specs.mac_algorithm);

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


static INLINE word32 GetSEQIncrement(CYASSL* ssl, int verify)
{
#ifdef CYASSL_DTLS
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


#ifdef CYASSL_DTLS

static INLINE word32 GetEpoch(CYASSL* ssl, int verify)
{
    if (verify)
        return ssl->keys.dtls_state.curEpoch;
    else
        return ssl->keys.dtls_epoch;
}

#endif /* CYASSL_DTLS */


/*** end copy ***/


/* return HMAC digest type in CyaSSL format */
int CyaSSL_GetHmacType(CYASSL* ssl)
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
        #ifdef CYASSL_SHA384
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


int CyaSSL_SetTlsHmacInner(CYASSL* ssl, byte* inner, word32 sz, int content,
                           int verify)
{
    if (ssl == NULL || inner == NULL)
        return BAD_FUNC_ARG;

    XMEMSET(inner, 0, CYASSL_TLS_HMAC_INNER_SZ);

#ifdef CYASSL_DTLS
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
int TLS_hmac(CYASSL* ssl, byte* digest, const byte* in, word32 sz,
              int content, int verify)
{
    Hmac hmac;
    int  ret;
    byte myInner[CYASSL_TLS_HMAC_INNER_SZ];

    if (ssl == NULL)
        return BAD_FUNC_ARG;
    
    CyaSSL_SetTlsHmacInner(ssl, myInner, sz, content, verify);

    ret = HmacSetKey(&hmac, CyaSSL_GetHmacType(ssl),
                     CyaSSL_GetMacSecret(ssl, verify), ssl->specs.hash_size);
    if (ret != 0)
        return ret;
    ret = HmacUpdate(&hmac, myInner, sizeof(myInner));
    if (ret != 0)
        return ret;
    ret = HmacUpdate(&hmac, in, sz);                                /* content */
    if (ret != 0)
        return ret;
    ret = HmacFinal(&hmac, digest);
    if (ret != 0)
        return ret;

    return 0;
}

#ifdef HAVE_TLS_EXTENSIONS

#define IS_OFF(semaphore, light) \
    ((semaphore)[(light) / 8] ^  (byte) (0x01 << ((light) % 8)))

#define TURN_ON(semaphore, light) \
    ((semaphore)[(light) / 8] |= (byte) (0x01 << ((light) % 8)))

static int TLSX_Append(TLSX** list, TLSX_Type type)
{
    TLSX* extension;

    if (list == NULL) /* won't check type since this function is static */
        return BAD_FUNC_ARG;

    if ((extension = XMALLOC(sizeof(TLSX), 0, DYNAMIC_TYPE_TLSX)) == NULL)
        return MEMORY_E;

    extension->type = type;
    extension->data = NULL;
    extension->resp = 0;
    extension->next = *list;
    *list = extension;

    return 0;
}

#ifndef NO_CYASSL_SERVER

void TLSX_SetResponse(CYASSL* ssl, TLSX_Type type);

void TLSX_SetResponse(CYASSL* ssl, TLSX_Type type)
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
            case CYASSL_SNI_HOST_NAME:
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
        case CYASSL_SNI_HOST_NAME: {
            sni->data.host_name = XMALLOC(size + 1, 0, DYNAMIC_TYPE_TLSX);

            if (sni->data.host_name) {
                XSTRNCPY(sni->data.host_name, (const char*) data, size);
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

#ifndef NO_CYASSL_SERVER
    sni->options = 0;
    sni->status  = CYASSL_SNI_NO_MATCH;
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
            case CYASSL_SNI_HOST_NAME:
                length += XSTRLEN((char*) sni->data.host_name);
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
            case CYASSL_SNI_HOST_NAME:
                length = XSTRLEN((char*) sni->data.host_name);

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

#ifndef NO_CYASSL_SERVER
static void TLSX_SNI_SetStatus(TLSX* extensions, byte type, byte status)
{
    TLSX* extension = TLSX_Find(extensions, SERVER_NAME_INDICATION);
    SNI* sni = TLSX_SNI_Find(extension ? extension->data : NULL, type);

    if (sni) {
        sni->status = status;
        CYASSL_MSG("SNI did match!");
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

static int TLSX_SNI_Parse(CYASSL* ssl, byte* input, word16 length,
                                                                 byte isRequest)
{
#ifndef NO_CYASSL_SERVER
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

#ifndef NO_CYASSL_SERVER

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

        if (!(sni = TLSX_SNI_Find((SNI *) extension->data, type))) {
            continue; /* not using this SNI type */
        }

        switch(type) {
            case CYASSL_SNI_HOST_NAME: {
                byte matched = (XSTRLEN(sni->data.host_name) == size)
                            && (XSTRNCMP(sni->data.host_name,
                                     (const char *) input + offset, size) == 0);

                if (matched || sni->options & CYASSL_SNI_ANSWER_ON_MISMATCH) {
                    int r = TLSX_UseSNI(&ssl->extensions,
                                                    type, input + offset, size);

                    if (r != SSL_SUCCESS) return r; /* throw error */

                    TLSX_SNI_SetStatus(ssl->extensions, type,
                      matched ? CYASSL_SNI_REAL_MATCH : CYASSL_SNI_FAKE_MATCH);

                } else if (!(sni->options & CYASSL_SNI_CONTINUE_ON_MISMATCH)) {
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
    TLSX* extension = NULL;
    SNI*  sni       = NULL;
    int   ret       = 0;

    if (extensions == NULL || data == NULL)
        return BAD_FUNC_ARG;

    if ((ret = TLSX_SNI_Append(&sni, type, data, size)) != 0)
        return ret;

    extension = *extensions;

    /* find SNI extension if it already exists. */
    while (extension && extension->type != SERVER_NAME_INDICATION)
        extension = extension->next;

    /* push new SNI extension if it doesn't exists. */
    if (!extension) {
        if ((ret = TLSX_Append(extensions, SERVER_NAME_INDICATION)) != 0) {
            TLSX_SNI_Free(sni);
            return ret;
        }

        extension = *extensions;
    }

    /* push new SNI object to extension data. */
    sni->next = (SNI*) extension->data;
    extension->data = (void*) sni;

    /* look for another server name of the same type to remove (replacement) */
    do {
        if (sni->next && sni->next->type == type) {
            SNI *next = sni->next;

            sni->next = next->next;
            TLSX_SNI_Free(next);

            break;
        }
    } while ((sni = sni->next));

    return SSL_SUCCESS;
}

#ifndef NO_CYASSL_SERVER
word16 TLSX_SNI_GetRequest(TLSX* extensions, byte type, void** data)
{
    TLSX* extension = TLSX_Find(extensions, SERVER_NAME_INDICATION);
    SNI* sni = TLSX_SNI_Find(extension ? extension->data : NULL, type);

    if (sni && sni->status != CYASSL_SNI_NO_MATCH) {
        switch (sni->type) {
            case CYASSL_SNI_HOST_NAME:
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
        return BUFFER_ERROR;

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

static int TLSX_MFL_Parse(CYASSL* ssl, byte* input, word16 length,
                                                                 byte isRequest)
{
    if (length != ENUM_LEN)
        return BUFFER_ERROR;

    switch (*input) {
        case CYASSL_MFL_2_9 : ssl->max_fragment =  512; break;
        case CYASSL_MFL_2_10: ssl->max_fragment = 1024; break;
        case CYASSL_MFL_2_11: ssl->max_fragment = 2048; break;
        case CYASSL_MFL_2_12: ssl->max_fragment = 4096; break;
        case CYASSL_MFL_2_13: ssl->max_fragment = 8192; break;

        default:
            SendAlert(ssl, alert_fatal, illegal_parameter);

            return UNKNOWN_MAX_FRAG_LEN_E;
    }

#ifndef NO_CYASSL_SERVER
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
    TLSX* extension = NULL;
    byte* data      = NULL;
    int   ret       = 0;

    if (extensions == NULL)
        return BAD_FUNC_ARG;

    if (mfl < CYASSL_MFL_2_9 || CYASSL_MFL_2_13 < mfl)
        return BAD_FUNC_ARG;

    if ((data = XMALLOC(ENUM_LEN, 0, DYNAMIC_TYPE_TLSX)) == NULL)
        return MEMORY_E;

    data[0] = mfl;

    /* push new MFL extension. */
    if ((ret = TLSX_Append(extensions, MAX_FRAGMENT_LENGTH)) != 0) {
        XFREE(data, 0, DYNAMIC_TYPE_TLSX);
        return ret;
    }

    /* place new mfl to extension data. */
    extension = *extensions;
    extension->data = (void*) data;

    /* remove duplicated extensions */
    do {
        if (extension->next && extension->next->type == MAX_FRAGMENT_LENGTH) {
            TLSX *next = extension->next;

            extension->next = next->next;
            next->next = NULL;

            TLSX_FreeAll(next);

            break;
        }
    } while ((extension = extension->next));

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

int TLSX_UseTruncatedHMAC(TLSX** extensions)
{
    int ret = 0;

    if (extensions == NULL)
        return BAD_FUNC_ARG;

    if (!TLSX_Find(*extensions, TRUNCATED_HMAC))
        if ((ret = TLSX_Append(extensions, TRUNCATED_HMAC)) != 0)
            return ret;

    return SSL_SUCCESS;
}

static int TLSX_THM_Parse(CYASSL* ssl, byte* input, word16 length,
                                                                 byte isRequest)
{
    if (length != 0 || input == NULL)
        return BUFFER_ERROR;

#ifndef NO_CYASSL_SERVER
    if (isRequest) {
        int r = TLSX_UseTruncatedHMAC(&ssl->extensions);

        if (r != SSL_SUCCESS) return r; /* throw error */

        TLSX_SetResponse(ssl, TRUNCATED_HMAC);
    }
#endif

    ssl->truncated_hmac = 1;

    return 0;
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

#ifndef NO_CYASSL_CLIENT

static void TLSX_EllipticCurve_ValidateRequest(CYASSL* ssl, byte* semaphore)
{
    int i;

    for (i = 0; i < ssl->suites->suiteSz; i+= 2)
        if (ssl->suites->suites[i] == ECC_BYTE)
            return;

    /* No elliptic curve suite found */
    TURN_ON(semaphore, ELLIPTIC_CURVES);
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

#endif /* NO_CYASSL_CLIENT */
#ifndef NO_CYASSL_SERVER

static int TLSX_EllipticCurve_Parse(CYASSL* ssl, byte* input, word16 length,
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

int TLSX_ValidateEllipticCurves(CYASSL* ssl, byte first, byte second) {
    TLSX*          extension = (first == ECC_BYTE)
                             ? TLSX_Find(ssl->extensions, ELLIPTIC_CURVES)
                             : NULL;
    EllipticCurve* curve     = NULL;
    word32         oid       = 0;
    word16         octets    = 0; /* acording to 'ecc_set_type ecc_sets[];' */
    int            sig       = 0; /* valitade signature */
    int            key       = 0; /* validate key       */

    if (!extension)
        return 1; /* no suite restriction */

    for (curve = extension->data; curve && !(sig && key); curve = curve->next) {

        switch (curve->name) {
            case CYASSL_ECC_SECP160R1: oid = ECC_160R1; octets = 20; break;
            case CYASSL_ECC_SECP192R1: oid = ECC_192R1; octets = 24; break;
            case CYASSL_ECC_SECP224R1: oid = ECC_224R1; octets = 28; break;
            case CYASSL_ECC_SECP256R1: oid = ECC_256R1; octets = 32; break;
            case CYASSL_ECC_SECP384R1: oid = ECC_384R1; octets = 48; break;
            case CYASSL_ECC_SECP521R1: oid = ECC_521R1; octets = 66; break;
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

#endif /* NO_CYASSL_SERVER */

int TLSX_UseSupportedCurve(TLSX** extensions, word16 name)
{
    TLSX*          extension = NULL;
    EllipticCurve* curve     = NULL;
    int            ret       = 0;

    if (extensions == NULL)
        return BAD_FUNC_ARG;

    if ((ret = TLSX_EllipticCurve_Append(&curve, name)) != 0)
        return ret;

    extension = *extensions;

    /* find EllipticCurve extension if it already exists. */
    while (extension && extension->type != ELLIPTIC_CURVES)
        extension = extension->next;

    /* push new EllipticCurve extension if it doesn't exists. */
    if (!extension) {
        if ((ret = TLSX_Append(extensions, ELLIPTIC_CURVES)) != 0) {
            XFREE(curve, 0, DYNAMIC_TYPE_TLSX);
            return ret;
        }

        extension = *extensions;
    }

    /* push new EllipticCurve object to extension data. */
    curve->next = (EllipticCurve*) extension->data;
    extension->data = (void*) curve;

    /* look for another curve of the same name to remove (replacement) */
    do {
        if (curve->next && curve->next->name == name) {
            EllipticCurve *next = curve->next;

            curve->next = next->next;
            XFREE(next, 0, DYNAMIC_TYPE_TLSX);

            break;
        }
    } while ((curve = curve->next));

    return SSL_SUCCESS;
}

#define EC_FREE_ALL         TLSX_EllipticCurve_FreeAll
#define EC_VALIDATE_REQUEST TLSX_EllipticCurve_ValidateRequest

#ifndef NO_CYASSL_CLIENT
#define EC_GET_SIZE TLSX_EllipticCurve_GetSize
#define EC_WRITE    TLSX_EllipticCurve_Write
#else
#define EC_GET_SIZE(list)         0
#define EC_WRITE(a, b)            0
#endif

#ifndef NO_CYASSL_SERVER
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
                SNI_FREE_ALL((SNI *) extension->data);
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
        }

        XFREE(extension, 0, DYNAMIC_TYPE_TLSX);
    }
}

int TLSX_SupportExtensions(CYASSL* ssl) {
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

        if (IS_OFF(semaphore, extension->type)) {
            /* type + data length */
            length += HELLO_EXT_TYPE_SZ + OPAQUE16_LEN;

            switch (extension->type) {
                case SERVER_NAME_INDICATION:
                    if (isRequest)
                        length += SNI_GET_SIZE((SNI *) extension->data);
                    break;
                case MAX_FRAGMENT_LENGTH:
                    length += MFL_GET_SIZE(extension->data);
                    break;

                case TRUNCATED_HMAC:
                    /* empty extension. */
                    break;

                case ELLIPTIC_CURVES:
                    length += EC_GET_SIZE((EllipticCurve *) extension->data);
                    break;
            }

            TURN_ON(semaphore, extension->type);
        }
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

        if (IS_OFF(semaphore, extension->type)) {
            /* extension type */
            c16toa(extension->type, output + offset);
            offset += HELLO_EXT_TYPE_SZ + OPAQUE16_LEN;
            length_offset = offset;

            /* extension data should be written internally */
            switch (extension->type) {
                case SERVER_NAME_INDICATION:
                    if (isRequest)
                        offset += SNI_WRITE((SNI *) extension->data,
                                                               output + offset);
                    break;

                case MAX_FRAGMENT_LENGTH:
                    offset += MFL_WRITE((byte *) extension->data,
                                                               output + offset);
                    break;

                case TRUNCATED_HMAC:
                    /* empty extension. */
                    break;

                case ELLIPTIC_CURVES:
                    offset += EC_WRITE((EllipticCurve *) extension->data,
                                                               output + offset);
                    break;
            }

            /* writing extension data length */
            c16toa(offset - length_offset,
                                         output + length_offset - OPAQUE16_LEN);

            TURN_ON(semaphore, extension->type);
        }
    }

    return offset;
}

#ifndef NO_CYASSL_CLIENT

word16 TLSX_GetRequestSize(CYASSL* ssl)
{
    word16 length = 0;

    if (TLSX_SupportExtensions(ssl)) {
        byte semaphore[16] = {0};

        EC_VALIDATE_REQUEST(ssl, semaphore);

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

word16 TLSX_WriteRequest(CYASSL* ssl, byte* output)
{
    word16 offset = 0;

    if (TLSX_SupportExtensions(ssl) && output) {
        byte semaphore[16] = {0};

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

#endif /* NO_CYASSL_CLIENT */

#ifndef NO_CYASSL_SERVER

word16 TLSX_GetResponseSize(CYASSL* ssl)
{
    word16 length = 0;
    byte semaphore[16] = {0};

    if (TLSX_SupportExtensions(ssl))
        length += TLSX_GetSize(ssl->extensions, semaphore, 0);

    /* All the response data is set at the ssl object only, so no ctx here. */

    if (length)
        length += OPAQUE16_LEN; /* for total length storage */

    return length;
}

word16 TLSX_WriteResponse(CYASSL *ssl, byte* output)
{
    word16 offset = 0;

    if (TLSX_SupportExtensions(ssl) && output) {
        byte semaphore[16] = {0};

        offset += OPAQUE16_LEN; /* extensions length */

        offset += TLSX_Write(ssl->extensions, output + offset, semaphore, 0);

        if (offset > OPAQUE16_LEN)
            c16toa(offset - OPAQUE16_LEN, output); /* extensions length */
    }

    return offset;
}

#endif /* NO_CYASSL_SERVER */

int TLSX_Parse(CYASSL* ssl, byte* input, word16 length, byte isRequest,
                                                                 Suites *suites)
{
    int ret = 0;
    word16 offset = 0;

    if (!ssl || !input || !suites)
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
                CYASSL_MSG("SNI extension received");

                ret = SNI_PARSE(ssl, input + offset, size, isRequest);
                break;

            case MAX_FRAGMENT_LENGTH:
                CYASSL_MSG("Max Fragment Length extension received");

                ret = MFL_PARSE(ssl, input + offset, size, isRequest);
                break;

            case TRUNCATED_HMAC:
                CYASSL_MSG("Truncated HMAC extension received");

                ret = THM_PARSE(ssl, input + offset, size, isRequest);
                break;

            case ELLIPTIC_CURVES:
                CYASSL_MSG("Elliptic Curves extension received");

                ret = EC_PARSE(ssl, input + offset, size, isRequest);
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
                    CYASSL_MSG("Servers MUST NOT send SIG ALGO extension.");
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

#elif defined(HAVE_SNI)             \
   || defined(HAVE_MAX_FRAGMENT)    \
   || defined(HAVE_TRUNCATED_HMAC)  \
   || defined(HAVE_SUPPORTED_CURVES)

#error Using TLS extensions requires HAVE_TLS_EXTENSIONS to be defined.

#endif /* HAVE_TLS_EXTENSIONS */


#ifndef NO_CYASSL_CLIENT

#ifndef NO_OLD_TLS

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

#endif /* !NO_OLD_TLS */

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
#ifndef NO_OLD_TLS
            method->downgrade = 1;
#endif 
        }
        return method;
    }


#endif /* NO_CYASSL_CLIENT */



#ifndef NO_CYASSL_SERVER

#ifndef NO_OLD_TLS

    CYASSL_METHOD* CyaTLSv1_server_method(void)
    {
        CYASSL_METHOD* method =
                              (CYASSL_METHOD*) XMALLOC(sizeof(CYASSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
        if (method) {
            InitSSL_Method(method, MakeTLSv1());
            method->side = CYASSL_SERVER_END;
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
            method->side = CYASSL_SERVER_END;
        }
        return method;
    }

#endif /* !NO_OLD_TLS */

#ifndef NO_SHA256   /* can't use without SHA256 */

    CYASSL_METHOD* CyaTLSv1_2_server_method(void)
    {
        CYASSL_METHOD* method =
                              (CYASSL_METHOD*) XMALLOC(sizeof(CYASSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
        if (method) {
            InitSSL_Method(method, MakeTLSv1_2());
            method->side = CYASSL_SERVER_END;
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
            method->side      = CYASSL_SERVER_END;
#ifndef NO_OLD_TLS
            method->downgrade = 1;
#endif /* !NO_OLD_TLS */
        }
        return method;
    }



#endif /* NO_CYASSL_SERVER */
#endif /* NO_TLS */

