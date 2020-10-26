/* tls13.c
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


/*
 * BUILD_GCM
 *    Enables AES-GCM ciphersuites.
 * HAVE_AESCCM
 *    Enables AES-CCM ciphersuites.
 * HAVE_SESSION_TICKET
 *    Enables session tickets - required for TLS 1.3 resumption.
 * NO_PSK
 *    Do not enable Pre-Shared Keys.
 * TLS13_SUPPORTS_EXPORTERS
 *    Guard to compile out any code for exporter keys.
 *    Feature not supported yet.
 * WOLFSSL_ASYNC_CRYPT
 *    Enables the use of asynchronous cryptographic operations.
 *    This is available for ciphers and certificates.
 * HAVE_CHACHA && HAVE_POLY1305
 *    Enables use of CHACHA20-POLY1305 ciphersuites.
 * WOLFSSL_DEBUG_TLS
 *    Writes out details of TLS 1.3 protocol including handshake message buffers
 *    and key generation input and output.
 * WOLFSSL_EARLY_DATA
 *    Allow 0-RTT Handshake using Early Data extensions and handshake message
 * WOLFSSL_EARLY_DATA_GROUP
 *    Group EarlyData message with ClientHello when sending
 * WOLFSSL_NO_SERVER_GROUPS_EXT
 *    Do not send the server's groups in an extension when the server's top
 *    preference is not in client's list.
 * WOLFSSL_POST_HANDSHAKE_AUTH
 *    Allow TLS v1.3 code to perform post-handshake authentication of the
 *    client.
 * WOLFSSL_SEND_HRR_COOKIE
 *    Send a cookie in hello_retry_request message to enable stateless tracking
 *    of ClientHello replies.
 * WOLFSSL_TLS13
 *    Enable TLS 1.3 protocol implementation.
 * WOLFSSL_TLS13_MIDDLEBOX_COMPAT
 *    Enable middlebox compatibility in the TLS 1.3 handshake.
 *    This includes sending ChangeCipherSpec before encrypted messages and
 *    including a session id.
 * WOLFSSL_TLS13_SHA512
 *    Allow generation of SHA-512 digests in handshake - no ciphersuite
 *    requires SHA-512 at this time.
 * WOLFSSL_TLS13_TICKET_BEFORE_FINISHED
 *    Allow a NewSessionTicket message to be sent by server before Client's
 *    Finished message.
 *    See TLS v1.3 specification, Section 4.6.1, Paragraph 4 (Note).
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#ifdef WOLFSSL_TLS13
#ifdef HAVE_SESSION_TICKET
    #include <wolfssl/wolfcrypt/wc_port.h>
#endif

#ifndef WOLFCRYPT_ONLY

#ifdef HAVE_ERRNO_H
    #include <errno.h>
#endif

#include <wolfssl/internal.h>
#include <wolfssl/error-ssl.h>
#include <wolfssl/wolfcrypt/asn.h>
#include <wolfssl/wolfcrypt/dh.h>
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

#ifdef HAVE_NTRU
    #include "libntruencrypt/ntru_crypto.h"
#endif

#ifdef __sun
    #include <sys/filio.h>
#endif

#ifndef TRUE
    #define TRUE  1
#endif
#ifndef FALSE
    #define FALSE 0
#endif

#ifndef HAVE_HKDF
    #ifndef _MSC_VER
        #error "The build option HAVE_HKDF is required for TLS 1.3"
    #else
        #pragma message("error: The build option HAVE_HKDF is required for TLS 1.3")
    #endif
#endif

#ifndef HAVE_TLS_EXTENSIONS
    #ifndef _MSC_VER
        #error "The build option HAVE_TLS_EXTENSIONS is required for TLS 1.3"
    #else
        #pragma message("error: The build option HAVE_TLS_EXTENSIONS is required for TLS 1.3")
    #endif
#endif


/* Set ret to error value and jump to label.
 *
 * err     The error value to set.
 * eLabel  The label to jump to.
 */
#define ERROR_OUT(err, eLabel) { ret = (err); goto eLabel; }


/* Extract data using HMAC, salt and input.
 * RFC 5869 - HMAC-based Extract-and-Expand Key Derivation Function (HKDF)
 *
 * prk      The generated pseudorandom key.
 * salt     The salt.
 * saltLen  The length of the salt.
 * ikm      The input keying material.
 * ikmLen   The length of the input keying material.
 * mac      The type of digest to use.
 * returns 0 on success, otherwise failure.
 */
static int Tls13_HKDF_Extract(byte* prk, const byte* salt, int saltLen,
                             byte* ikm, int ikmLen, int mac)
{
    int ret;
    int hash = 0;
    int len = 0;

    switch (mac) {
        #ifndef NO_SHA256
        case sha256_mac:
            hash = WC_SHA256;
            len = WC_SHA256_DIGEST_SIZE;
            break;
        #endif

        #ifdef WOLFSSL_SHA384
        case sha384_mac:
            hash = WC_SHA384;
            len = WC_SHA384_DIGEST_SIZE;
            break;
        #endif

        #ifdef WOLFSSL_TLS13_SHA512
        case sha512_mac:
            hash = WC_SHA512;
            len = WC_SHA512_DIGEST_SIZE;
            break;
        #endif
    }

    /* When length is 0 then use zeroed data of digest length. */
    if (ikmLen == 0) {
        ikmLen = len;
        XMEMSET(ikm, 0, len);
    }

#ifdef WOLFSSL_DEBUG_TLS
    WOLFSSL_MSG("  Salt");
    WOLFSSL_BUFFER(salt, saltLen);
    WOLFSSL_MSG("  IKM");
    WOLFSSL_BUFFER(ikm, ikmLen);
#endif

    ret = wc_HKDF_Extract(hash, salt, saltLen, ikm, ikmLen, prk);

#ifdef WOLFSSL_DEBUG_TLS
    WOLFSSL_MSG("  PRK");
    WOLFSSL_BUFFER(prk, len);
#endif

    return ret;
}

/* Expand data using HMAC, salt and label and info.
 * TLS v1.3 defines this function.
 *
 * okm          The generated pseudorandom key - output key material.
 * okmLen       The length of generated pseudorandom key - output key material.
 * prk          The salt - pseudo-random key.
 * prkLen       The length of the salt - pseudo-random key.
 * protocol     The TLS protocol label.
 * protocolLen  The length of the TLS protocol label.
 * info         The information to expand.
 * infoLen      The length of the information.
 * digest       The type of digest to use.
 * returns 0 on success, otherwise failure.
 */
static int HKDF_Expand_Label(byte* okm, word32 okmLen,
                             const byte* prk, word32 prkLen,
                             const byte* protocol, word32 protocolLen,
                             const byte* label, word32 labelLen,
                             const byte* info, word32 infoLen,
                             int digest)
{
    int    ret = 0;
    int    idx = 0;
    byte   data[MAX_HKDF_LABEL_SZ];

    /* Output length. */
    data[idx++] = (byte)(okmLen >> 8);
    data[idx++] = (byte)okmLen;
    /* Length of protocol | label. */
    data[idx++] = (byte)(protocolLen + labelLen);
    /* Protocol */
    XMEMCPY(&data[idx], protocol, protocolLen);
    idx += protocolLen;
    /* Label */
    XMEMCPY(&data[idx], label, labelLen);
    idx += labelLen;
    /* Length of hash of messages */
    data[idx++] = (byte)infoLen;
    /* Hash of messages */
    XMEMCPY(&data[idx], info, infoLen);
    idx += infoLen;

#ifdef WOLFSSL_DEBUG_TLS
    WOLFSSL_MSG("  PRK");
    WOLFSSL_BUFFER(prk, prkLen);
    WOLFSSL_MSG("  Info");
    WOLFSSL_BUFFER(data, idx);
#endif

    ret = wc_HKDF_Expand(digest, prk, prkLen, data, idx, okm, okmLen);

#ifdef WOLFSSL_DEBUG_TLS
    WOLFSSL_MSG("  OKM");
    WOLFSSL_BUFFER(okm, okmLen);
#endif

    ForceZero(data, idx);

    return ret;
}

/* Size of the TLS v1.3 label use when deriving keys. */
#define TLS13_PROTOCOL_LABEL_SZ    6
/* The protocol label for TLS v1.3. */
static const byte tls13ProtocolLabel[TLS13_PROTOCOL_LABEL_SZ + 1] = "tls13 ";

/* Derive a key from a message.
 *
 * ssl        The SSL/TLS object.
 * output     The buffer to hold the derived key.
 * outputLen  The length of the derived key.
 * secret     The secret used to derive the key (HMAC secret).
 * label      The label used to distinguish the context.
 * labelLen   The length of the label.
 * msg        The message data to derive key from.
 * msgLen     The length of the message data to derive key from.
 * hashAlgo   The hash algorithm to use in the HMAC.
 * returns 0 on success, otherwise failure.
 */
static int DeriveKeyMsg(WOLFSSL* ssl, byte* output, int outputLen,
                        const byte* secret, const byte* label, word32 labelLen,
                        byte* msg, int msgLen, int hashAlgo)
{
    byte        hash[WC_MAX_DIGEST_SIZE];
    Digest      digest;
    word32      hashSz = 0;
    const byte* protocol;
    word32      protocolLen;
    int         digestAlg = -1;
    int         ret = BAD_FUNC_ARG;

    switch (hashAlgo) {
#ifndef NO_WOLFSSL_SHA256
        case sha256_mac:
            ret = wc_InitSha256_ex(&digest.sha256, ssl->heap, INVALID_DEVID);
            if (ret == 0) {
                    ret = wc_Sha256Update(&digest.sha256, msg, msgLen);
                if (ret == 0)
                    ret = wc_Sha256Final(&digest.sha256, hash);
                wc_Sha256Free(&digest.sha256);
            }
            hashSz = WC_SHA256_DIGEST_SIZE;
            digestAlg = WC_SHA256;
            break;
#endif
#ifdef WOLFSSL_SHA384
        case sha384_mac:
            ret = wc_InitSha384_ex(&digest.sha384, ssl->heap, INVALID_DEVID);
            if (ret == 0) {
                ret = wc_Sha384Update(&digest.sha384, msg, msgLen);
                if (ret == 0)
                    ret = wc_Sha384Final(&digest.sha384, hash);
                wc_Sha384Free(&digest.sha384);
            }
            hashSz = WC_SHA384_DIGEST_SIZE;
            digestAlg = WC_SHA384;
            break;
#endif
#ifdef WOLFSSL_TLS13_SHA512
        case sha512_mac:
            ret = wc_InitSha512_ex(&digest.sha512, ssl->heap, INVALID_DEVID);
            if (ret == 0) {
                ret = wc_Sha512Update(&digest.sha512, msg, msgLen);
                if (ret == 0)
                    ret = wc_Sha512Final(&digest.sha512, hash);
                wc_Sha512Free(&digest.sha512);
            }
            hashSz = WC_SHA512_DIGEST_SIZE;
            digestAlg = WC_SHA512;
            break;
#endif
        default:
            digestAlg = -1;
            break;
    }

    if (digestAlg < 0)
        return HASH_TYPE_E;

    if (ret != 0)
        return ret;

    switch (ssl->version.minor) {
        case TLSv1_3_MINOR:
            protocol = tls13ProtocolLabel;
            protocolLen = TLS13_PROTOCOL_LABEL_SZ;
            break;

        default:
            return VERSION_ERROR;
    }
    if (outputLen == -1)
        outputLen = hashSz;

    return HKDF_Expand_Label(output, outputLen, secret, hashSz,
                             protocol, protocolLen, label, labelLen,
                             hash, hashSz, digestAlg);
}

/* Derive a key.
 *
 * ssl          The SSL/TLS object.
 * output       The buffer to hold the derived key.
 * outputLen    The length of the derived key.
 * secret       The secret used to derive the key (HMAC secret).
 * label        The label used to distinguish the context.
 * labelLen     The length of the label.
 * hashAlgo     The hash algorithm to use in the HMAC.
 * includeMsgs  Whether to include a hash of the handshake messages so far.
 * returns 0 on success, otherwise failure.
 */
static int DeriveKey(WOLFSSL* ssl, byte* output, int outputLen,
                     const byte* secret, const byte* label, word32 labelLen,
                     int hashAlgo, int includeMsgs)
{
    int         ret = 0;
    byte        hash[WC_MAX_DIGEST_SIZE];
    word32      hashSz = 0;
    word32      hashOutSz = 0;
    const byte* protocol;
    word32      protocolLen;
    int         digestAlg = 0;

    switch (hashAlgo) {
        #ifndef NO_SHA256
            case sha256_mac:
                hashSz    = WC_SHA256_DIGEST_SIZE;
                digestAlg = WC_SHA256;
                if (includeMsgs)
                    ret = wc_Sha256GetHash(&ssl->hsHashes->hashSha256, hash);
            break;
        #endif

        #ifdef WOLFSSL_SHA384
            case sha384_mac:
                hashSz    = WC_SHA384_DIGEST_SIZE;
                digestAlg = WC_SHA384;
                if (includeMsgs)
                    ret = wc_Sha384GetHash(&ssl->hsHashes->hashSha384, hash);
            break;
        #endif

        #ifdef WOLFSSL_TLS13_SHA512
            case sha512_mac:
                hashSz    = WC_SHA512_DIGEST_SIZE;
                digestAlg = WC_SHA512;
                if (includeMsgs)
                    ret = wc_Sha512GetHash(&ssl->hsHashes->hashSha512, hash);
            break;
        #endif
    }
    if (ret != 0)
        return ret;

    /* Only one protocol version defined at this time. */
    protocol = tls13ProtocolLabel;
    protocolLen = TLS13_PROTOCOL_LABEL_SZ;

    if (outputLen == -1)
        outputLen = hashSz;
    if (includeMsgs)
        hashOutSz = hashSz;

    return HKDF_Expand_Label(output, outputLen, secret, hashSz,
                             protocol, protocolLen, label, labelLen,
                             hash, hashOutSz, digestAlg);
}

#ifndef NO_PSK
/* The length of the binder key label. */
#define BINDER_KEY_LABEL_SZ         10
/* The binder key label. */
static const byte binderKeyLabel[BINDER_KEY_LABEL_SZ + 1] =
    "ext binder";

/* Derive the binder key.
 *
 * ssl  The SSL/TLS object.
 * key  The derived key.
 * returns 0 on success, otherwise failure.
 */
static int DeriveBinderKey(WOLFSSL* ssl, byte* key)
{
    WOLFSSL_MSG("Derive Binder Key");
    if (ssl == NULL || ssl->arrays == NULL) {
        return BAD_FUNC_ARG;
    }
    return DeriveKeyMsg(ssl, key, -1, ssl->arrays->secret,
                        binderKeyLabel, BINDER_KEY_LABEL_SZ,
                        NULL, 0, ssl->specs.mac_algorithm);
}
#endif /* !NO_PSK */

#ifdef HAVE_SESSION_TICKET

/* The length of the binder key resume label. */
#define BINDER_KEY_RESUME_LABEL_SZ  10
/* The binder key resume label. */
static const byte binderKeyResumeLabel[BINDER_KEY_RESUME_LABEL_SZ + 1] =
    "res binder";

/* Derive the binder resumption key.
 *
 * ssl  The SSL/TLS object.
 * key  The derived key.
 * returns 0 on success, otherwise failure.
 */
static int DeriveBinderKeyResume(WOLFSSL* ssl, byte* key)
{
    WOLFSSL_MSG("Derive Binder Key - Resumption");
    if (ssl == NULL || ssl->arrays == NULL) {
        return BAD_FUNC_ARG;
    }
    return DeriveKeyMsg(ssl, key, -1, ssl->arrays->secret,
                        binderKeyResumeLabel, BINDER_KEY_RESUME_LABEL_SZ,
                        NULL, 0, ssl->specs.mac_algorithm);
}
#endif /* HAVE_SESSION_TICKET */

#ifdef WOLFSSL_EARLY_DATA

/* The length of the early traffic label. */
#define EARLY_TRAFFIC_LABEL_SZ      11
/* The early traffic label. */
static const byte earlyTrafficLabel[EARLY_TRAFFIC_LABEL_SZ + 1] =
    "c e traffic";

/* Derive the early traffic key.
 *
 * ssl  The SSL/TLS object.
 * key  The derived key.
 * returns 0 on success, otherwise failure.
 */
static int DeriveEarlyTrafficSecret(WOLFSSL* ssl, byte* key)
{
    int ret;
    WOLFSSL_MSG("Derive Early Traffic Secret");
    if (ssl == NULL || ssl->arrays == NULL) {
        return BAD_FUNC_ARG;
    }
    ret = DeriveKey(ssl, key, -1, ssl->arrays->secret,
                    earlyTrafficLabel, EARLY_TRAFFIC_LABEL_SZ,
                    ssl->specs.mac_algorithm, 1);
#ifdef HAVE_SECRET_CALLBACK
    if (ret == 0 && ssl->tls13SecretCb != NULL) {
        ret = ssl->tls13SecretCb(ssl, CLIENT_EARLY_TRAFFIC_SECRET, key,
                                 ssl->specs.hash_size, ssl->tls13SecretCtx);
        if (ret != 0) {
            return TLS13_SECRET_CB_E;
        }
    }
#endif /* HAVE_SECRET_CALLBACK */
    return ret;
}

#ifdef TLS13_SUPPORTS_EXPORTERS
/* The length of the early exporter label. */
#define EARLY_EXPORTER_LABEL_SZ     12
/* The early exporter label. */
static const byte earlyExporterLabel[EARLY_EXPORTER_LABEL_SZ + 1] =
    "e exp master";

/* Derive the early exporter key.
 *
 * ssl  The SSL/TLS object.
 * key  The derived key.
 * returns 0 on success, otherwise failure.
 */
static int DeriveEarlyExporterSecret(WOLFSSL* ssl, byte* key)
{
    int ret;
    WOLFSSL_MSG("Derive Early Exporter Secret");
    if (ssl == NULL || ssl->arrays == NULL) {
        return BAD_FUNC_ARG;
    }
    ret = DeriveKey(ssl, key, -1, ssl->arrays->secret,
                    earlyExporterLabel, EARLY_EXPORTER_LABEL_SZ,
                    ssl->specs.mac_algorithm, 1);
#ifdef HAVE_SECRET_CALLBACK
    if (ret == 0 && ssl->tls13SecretCb != NULL) {
        ret = ssl->tls13SecretCb(ssl, EARLY_EXPORTER_SECRET, key
                                 ssl->specs.hash_size, ssl->tls13SecretCtx);
        if (ret != 0) {
            return TLS13_SECRET_CB_E;
        }
    }
#endif /* HAVE_SECRET_CALLBACK */
    return ret;
}
#endif
#endif

/* The length of the client handshake label. */
#define CLIENT_HANDSHAKE_LABEL_SZ   12
/* The client handshake label. */
static const byte clientHandshakeLabel[CLIENT_HANDSHAKE_LABEL_SZ + 1] =
    "c hs traffic";

/* Derive the client handshake key.
 *
 * ssl  The SSL/TLS object.
 * key  The derived key.
 * returns 0 on success, otherwise failure.
 */
static int DeriveClientHandshakeSecret(WOLFSSL* ssl, byte* key)
{
    int ret;
    WOLFSSL_MSG("Derive Client Handshake Secret");
    if (ssl == NULL || ssl->arrays == NULL) {
        return BAD_FUNC_ARG;
    }
    ret = DeriveKey(ssl, key, -1, ssl->arrays->preMasterSecret,
                    clientHandshakeLabel, CLIENT_HANDSHAKE_LABEL_SZ,
                    ssl->specs.mac_algorithm, 1);
#ifdef HAVE_SECRET_CALLBACK
    if (ret == 0 && ssl->tls13SecretCb != NULL) {
        ret = ssl->tls13SecretCb(ssl, CLIENT_HANDSHAKE_TRAFFIC_SECRET, key,
                                 ssl->specs.hash_size, ssl->tls13SecretCtx);
        if (ret != 0) {
            return TLS13_SECRET_CB_E;
        }
    }
#endif /* HAVE_SECRET_CALLBACK */
    return ret;
}

/* The length of the server handshake label. */
#define SERVER_HANDSHAKE_LABEL_SZ   12
/* The server handshake label. */
static const byte serverHandshakeLabel[SERVER_HANDSHAKE_LABEL_SZ + 1] =
    "s hs traffic";

/* Derive the server handshake key.
 *
 * ssl  The SSL/TLS object.
 * key  The derived key.
 * returns 0 on success, otherwise failure.
 */
static int DeriveServerHandshakeSecret(WOLFSSL* ssl, byte* key)
{
    int ret;
    WOLFSSL_MSG("Derive Server Handshake Secret");
    if (ssl == NULL || ssl->arrays == NULL) {
        return BAD_FUNC_ARG;
    }
    ret = DeriveKey(ssl, key, -1, ssl->arrays->preMasterSecret,
                    serverHandshakeLabel, SERVER_HANDSHAKE_LABEL_SZ,
                    ssl->specs.mac_algorithm, 1);
#ifdef HAVE_SECRET_CALLBACK
    if (ret == 0 && ssl->tls13SecretCb != NULL) {
        ret = ssl->tls13SecretCb(ssl, SERVER_HANDSHAKE_TRAFFIC_SECRET, key,
                                 ssl->specs.hash_size, ssl->tls13SecretCtx);
        if (ret != 0) {
            return TLS13_SECRET_CB_E;
        }
    }
#endif /* HAVE_SECRET_CALLBACK */
    return ret;
}

/* The length of the client application traffic label. */
#define CLIENT_APP_LABEL_SZ         12
/* The client application traffic label. */
static const byte clientAppLabel[CLIENT_APP_LABEL_SZ + 1] =
    "c ap traffic";

/* Derive the client application traffic key.
 *
 * ssl  The SSL/TLS object.
 * key  The derived key.
 * returns 0 on success, otherwise failure.
 */
static int DeriveClientTrafficSecret(WOLFSSL* ssl, byte* key)
{
    int ret;
    WOLFSSL_MSG("Derive Client Traffic Secret");
    if (ssl == NULL || ssl->arrays == NULL) {
        return BAD_FUNC_ARG;
    }
    ret = DeriveKey(ssl, key, -1, ssl->arrays->masterSecret,
                    clientAppLabel, CLIENT_APP_LABEL_SZ,
                    ssl->specs.mac_algorithm, 1);
#ifdef HAVE_SECRET_CALLBACK
    if (ret == 0 && ssl->tls13SecretCb != NULL) {
        ret = ssl->tls13SecretCb(ssl, CLIENT_TRAFFIC_SECRET, key,
                                 ssl->specs.hash_size, ssl->tls13SecretCtx);
        if (ret != 0) {
            return TLS13_SECRET_CB_E;
        }
    }
#endif /* HAVE_SECRET_CALLBACK */
    return ret;
}

/* The length of the server application traffic label. */
#define SERVER_APP_LABEL_SZ         12
/* The  server application traffic label. */
static const byte serverAppLabel[SERVER_APP_LABEL_SZ + 1] =
    "s ap traffic";

/* Derive the server application traffic key.
 *
 * ssl  The SSL/TLS object.
 * key  The derived key.
 * returns 0 on success, otherwise failure.
 */
static int DeriveServerTrafficSecret(WOLFSSL* ssl, byte* key)
{
    int ret;
    WOLFSSL_MSG("Derive Server Traffic Secret");
    if (ssl == NULL || ssl->arrays == NULL) {
        return BAD_FUNC_ARG;
    }
    ret = DeriveKey(ssl, key, -1, ssl->arrays->masterSecret,
                    serverAppLabel, SERVER_APP_LABEL_SZ,
                    ssl->specs.mac_algorithm, 1);
#ifdef HAVE_SECRET_CALLBACK
    if (ret == 0 && ssl->tls13SecretCb != NULL) {
        ret = ssl->tls13SecretCb(ssl, SERVER_TRAFFIC_SECRET, key,
                                 ssl->specs.hash_size, ssl->tls13SecretCtx);
        if (ret != 0) {
            return TLS13_SECRET_CB_E;
        }
    }
#endif /* HAVE_SECRET_CALLBACK */
    return ret;
}

#ifdef TLS13_SUPPORTS_EXPORTERS
/* The length of the exporter master secret label. */
#define EXPORTER_MASTER_LABEL_SZ    10
/* The exporter master secret label. */
static const byte exporterMasterLabel[EXPORTER_MASTER_LABEL_SZ + 1] =
    "exp master";

/* Derive the exporter secret.
 *
 * ssl  The SSL/TLS object.
 * key  The derived key.
 * returns 0 on success, otherwise failure.
 */
static int DeriveExporterSecret(WOLFSSL* ssl, byte* key)
{
    int ret;
    WOLFSSL_MSG("Derive Exporter Secret");
    if (ssl == NULL || ssl->arrays == NULL) {
        return BAD_FUNC_ARG;
    }
    ret = DeriveKey(ssl, key, -1, ssl->arrays->masterSecret,
                    exporterMasterLabel, EXPORTER_MASTER_LABEL_SZ,
                    ssl->specs.mac_algorithm, 1);
#ifdef HAVE_SECRET_CALLBACK
    if (ret == 0 && ssl->tls13SecretCb != NULL) {
        ret = ssl->tls13SecretCb(ssl, EXPORTER_SECRET, key,
                                 ssl->specs.hash_size, ssl->tls13SecretCtx);
        if (ret != 0) {
            return TLS13_SECRET_CB_E;
        }
    }
#endif /* HAVE_SECRET_CALLBACK */
    return ret;
}
#endif

#if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
/* The length of the resumption master secret label. */
#define RESUME_MASTER_LABEL_SZ      10
/* The resumption master secret label. */
static const byte resumeMasterLabel[RESUME_MASTER_LABEL_SZ + 1] =
    "res master";

/* Derive the resumption secret.
 *
 * ssl  The SSL/TLS object.
 * key  The derived key.
 * returns 0 on success, otherwise failure.
 */
int DeriveResumptionSecret(WOLFSSL* ssl, byte* key)
{
    WOLFSSL_MSG("Derive Resumption Secret");
    if (ssl == NULL || ssl->arrays == NULL) {
        return BAD_FUNC_ARG;
    }
    return DeriveKey(ssl, key, -1, ssl->arrays->masterSecret,
                     resumeMasterLabel, RESUME_MASTER_LABEL_SZ,
                     ssl->specs.mac_algorithm, 1);
}
#endif

/* Length of the finished label. */
#define FINISHED_LABEL_SZ           8
/* Finished label for generating finished key. */
static const byte finishedLabel[FINISHED_LABEL_SZ+1] = "finished";
/* Derive the finished secret.
 *
 * ssl     The SSL/TLS object.
 * key     The key to use with the HMAC.
 * secret  The derived secret.
 * returns 0 on success, otherwise failure.
 */
static int DeriveFinishedSecret(WOLFSSL* ssl, byte* key, byte* secret)
{
    WOLFSSL_MSG("Derive Finished Secret");
    return DeriveKey(ssl, secret, -1, key, finishedLabel, FINISHED_LABEL_SZ,
                     ssl->specs.mac_algorithm, 0);
}

/* The length of the application traffic label. */
#define APP_TRAFFIC_LABEL_SZ        11
/* The application traffic label. */
static const byte appTrafficLabel[APP_TRAFFIC_LABEL_SZ + 1] =
    "traffic upd";

/* Update the traffic secret.
 *
 * ssl     The SSL/TLS object.
 * secret  The previous secret and derived secret.
 * returns 0 on success, otherwise failure.
 */
static int DeriveTrafficSecret(WOLFSSL* ssl, byte* secret)
{
    WOLFSSL_MSG("Derive New Application Traffic Secret");
    return DeriveKey(ssl, secret, -1, secret,
                     appTrafficLabel, APP_TRAFFIC_LABEL_SZ,
                     ssl->specs.mac_algorithm, 0);
}

/* Derive the early secret using HKDF Extract.
 *
 * ssl  The SSL/TLS object.
 */
int DeriveEarlySecret(WOLFSSL* ssl)
{
    WOLFSSL_MSG("Derive Early Secret");
    if (ssl == NULL || ssl->arrays == NULL) {
        return BAD_FUNC_ARG;
    }
#if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
    return Tls13_HKDF_Extract(ssl->arrays->secret, NULL, 0,
            ssl->arrays->psk_key, ssl->arrays->psk_keySz,
            ssl->specs.mac_algorithm);
#else
    return Tls13_HKDF_Extract(ssl->arrays->secret, NULL, 0,
            ssl->arrays->masterSecret, 0, ssl->specs.mac_algorithm);
#endif
}

/* The length of the derived label. */
#define DERIVED_LABEL_SZ        7
/* The derived label. */
static const byte derivedLabel[DERIVED_LABEL_SZ + 1] =
    "derived";

/* Derive the handshake secret using HKDF Extract.
 *
 * ssl  The SSL/TLS object.
 */
int DeriveHandshakeSecret(WOLFSSL* ssl)
{
    byte key[WC_MAX_DIGEST_SIZE];
    int ret;
    WOLFSSL_MSG("Derive Handshake Secret");
    if (ssl == NULL || ssl->arrays == NULL) {
        return BAD_FUNC_ARG;
    }
    ret = DeriveKeyMsg(ssl, key, -1, ssl->arrays->secret,
                        derivedLabel, DERIVED_LABEL_SZ,
                        NULL, 0, ssl->specs.mac_algorithm);
    if (ret != 0)
        return ret;

    return Tls13_HKDF_Extract(ssl->arrays->preMasterSecret,
            key, ssl->specs.hash_size,
            ssl->arrays->preMasterSecret, ssl->arrays->preMasterSz,
            ssl->specs.mac_algorithm);
}

/* Derive the master secret using HKDF Extract.
 *
 * ssl  The SSL/TLS object.
 */
int DeriveMasterSecret(WOLFSSL* ssl)
{
    byte key[WC_MAX_DIGEST_SIZE];
    int ret;
    WOLFSSL_MSG("Derive Master Secret");
    if (ssl == NULL || ssl->arrays == NULL) {
        return BAD_FUNC_ARG;
    }
    ret = DeriveKeyMsg(ssl, key, -1, ssl->arrays->preMasterSecret,
                        derivedLabel, DERIVED_LABEL_SZ,
                        NULL, 0, ssl->specs.mac_algorithm);
    if (ret != 0)
        return ret;

    return Tls13_HKDF_Extract(ssl->arrays->masterSecret,
            key, ssl->specs.hash_size,
            ssl->arrays->masterSecret, 0, ssl->specs.mac_algorithm);
}

#if defined(HAVE_SESSION_TICKET)
/* Length of the resumption label. */
#define RESUMPTION_LABEL_SZ         10
/* Resumption label for generating PSK associated with the ticket. */
static const byte resumptionLabel[RESUMPTION_LABEL_SZ+1] = "resumption";
/* Derive the PSK associated with the ticket.
 *
 * ssl       The SSL/TLS object.
 * nonce     The nonce to derive with.
 * nonceLen  The length of the nonce to derive with.
 * secret    The derived secret.
 * returns 0 on success, otherwise failure.
 */
int DeriveResumptionPSK(WOLFSSL* ssl, byte* nonce, byte nonceLen, byte* secret)
{
    int         digestAlg;
    /* Only one protocol version defined at this time. */
    const byte* protocol    = tls13ProtocolLabel;
    word32      protocolLen = TLS13_PROTOCOL_LABEL_SZ;

    WOLFSSL_MSG("Derive Resumption PSK");

    switch (ssl->specs.mac_algorithm) {
        #ifndef NO_SHA256
        case sha256_mac:
            digestAlg = WC_SHA256;
            break;
        #endif

        #ifdef WOLFSSL_SHA384
        case sha384_mac:
            digestAlg = WC_SHA384;
            break;
        #endif

        #ifdef WOLFSSL_TLS13_SHA512
        case sha512_mac:
            digestAlg = WC_SHA512;
            break;
        #endif

        default:
            return BAD_FUNC_ARG;
    }

    return HKDF_Expand_Label(secret, ssl->specs.hash_size,
                             ssl->session.masterSecret, ssl->specs.hash_size,
                             protocol, protocolLen, resumptionLabel,
                             RESUMPTION_LABEL_SZ, nonce, nonceLen, digestAlg);
}
#endif /* HAVE_SESSION_TICKET */


/* Calculate the HMAC of message data to this point.
 *
 * ssl   The SSL/TLS object.
 * key   The HMAC key.
 * hash  The hash result - verify data.
 * returns length of verify data generated.
 */
static int BuildTls13HandshakeHmac(WOLFSSL* ssl, byte* key, byte* hash,
    word32* pHashSz)
{
    Hmac verifyHmac;
    int  hashType = WC_SHA256;
    int  hashSz = WC_SHA256_DIGEST_SIZE;
    int  ret = BAD_FUNC_ARG;

    if (ssl == NULL || key == NULL || hash == NULL) {
        return BAD_FUNC_ARG;
    }

    /* Get the hash of the previous handshake messages. */
    switch (ssl->specs.mac_algorithm) {
    #ifndef NO_SHA256
        case sha256_mac:
            hashType = WC_SHA256;
            hashSz = WC_SHA256_DIGEST_SIZE;
            ret = wc_Sha256GetHash(&ssl->hsHashes->hashSha256, hash);
            break;
    #endif /* !NO_SHA256 */
    #ifdef WOLFSSL_SHA384
        case sha384_mac:
            hashType = WC_SHA384;
            hashSz = WC_SHA384_DIGEST_SIZE;
            ret = wc_Sha384GetHash(&ssl->hsHashes->hashSha384, hash);
            break;
    #endif /* WOLFSSL_SHA384 */
    #ifdef WOLFSSL_TLS13_SHA512
        case sha512_mac:
            hashType = WC_SHA512;
            hashSz = WC_SHA512_DIGEST_SIZE;
            ret = wc_Sha512GetHash(&ssl->hsHashes->hashSha512, hash);
            break;
    #endif /* WOLFSSL_TLS13_SHA512 */
    }
    if (ret != 0)
        return ret;

    /* Calculate the verify data. */
    ret = wc_HmacInit(&verifyHmac, ssl->heap, ssl->devId);
    if (ret == 0) {
        ret = wc_HmacSetKey(&verifyHmac, hashType, key, ssl->specs.hash_size);
        if (ret == 0)
            ret = wc_HmacUpdate(&verifyHmac, hash, hashSz);
        if (ret == 0)
            ret = wc_HmacFinal(&verifyHmac, hash);
        wc_HmacFree(&verifyHmac);
    }

    if (pHashSz)
        *pHashSz = hashSz;

    return ret;
}

/* The length of the label to use when deriving keys. */
#define WRITE_KEY_LABEL_SZ     3
/* The length of the label to use when deriving IVs. */
#define WRITE_IV_LABEL_SZ      2
/* The label to use when deriving keys. */
static const byte writeKeyLabel[WRITE_KEY_LABEL_SZ+1] = "key";
/* The label to use when deriving IVs. */
static const byte writeIVLabel[WRITE_IV_LABEL_SZ+1]   = "iv";

/* Derive the keys and IVs for TLS v1.3.
 *
 * ssl      The SSL/TLS object.
 * sercret  early_data_key when deriving the key and IV for encrypting early
 *          data application data and end_of_early_data messages.
 *          handshake_key when deriving keys and IVs for encrypting handshake
 *          messages.
 *          traffic_key when deriving first keys and IVs for encrypting
 *          traffic messages.
 *          update_traffic_key when deriving next keys and IVs for encrypting
 *          traffic messages.
 * side     ENCRYPT_SIDE_ONLY when only encryption secret needs to be derived.
 *          DECRYPT_SIDE_ONLY when only decryption secret needs to be derived.
 *          ENCRYPT_AND_DECRYPT_SIDE when both secret needs to be derived.
 * store    1 indicates to derive the keys and IVs from derived secret and
 *          store ready for provisioning.
 * returns 0 on success, otherwise failure.
 */
int DeriveTls13Keys(WOLFSSL* ssl, int secret, int side, int store)
{
    int   ret = BAD_FUNC_ARG; /* Assume failure */
    int   i = 0;
#ifdef WOLFSSL_SMALL_STACK
    byte* key_dig;
#else
    byte  key_dig[MAX_PRF_DIG];
#endif
    int   provision;

#ifdef WOLFSSL_SMALL_STACK
    key_dig = (byte*)XMALLOC(MAX_PRF_DIG, ssl->heap, DYNAMIC_TYPE_DIGEST);
    if (key_dig == NULL)
        return MEMORY_E;
#endif

    if (side == ENCRYPT_AND_DECRYPT_SIDE) {
        provision = PROVISION_CLIENT_SERVER;
    }
    else {
        provision = ((ssl->options.side != WOLFSSL_CLIENT_END) ^
                     (side == ENCRYPT_SIDE_ONLY)) ? PROVISION_CLIENT :
                                                    PROVISION_SERVER;
    }

    /* Derive the appropriate secret to use in the HKDF. */
    switch (secret) {
#ifdef WOLFSSL_EARLY_DATA
        case early_data_key:
            ret = DeriveEarlyTrafficSecret(ssl, ssl->clientSecret);
            if (ret != 0)
                goto end;
            break;
#endif

        case handshake_key:
            if (provision & PROVISION_CLIENT) {
                ret = DeriveClientHandshakeSecret(ssl,
                                                  ssl->clientSecret);
                if (ret != 0)
                    goto end;
            }
            if (provision & PROVISION_SERVER) {
                ret = DeriveServerHandshakeSecret(ssl,
                                                  ssl->serverSecret);
                if (ret != 0)
                    goto end;
            }
            break;

        case traffic_key:
            if (provision & PROVISION_CLIENT) {
                ret = DeriveClientTrafficSecret(ssl, ssl->clientSecret);
                if (ret != 0)
                    goto end;
            }
            if (provision & PROVISION_SERVER) {
                ret = DeriveServerTrafficSecret(ssl, ssl->serverSecret);
                if (ret != 0)
                    goto end;
            }
            break;

        case update_traffic_key:
            if (provision & PROVISION_CLIENT) {
                ret = DeriveTrafficSecret(ssl, ssl->clientSecret);
                if (ret != 0)
                    goto end;
            }
            if (provision & PROVISION_SERVER) {
                ret = DeriveTrafficSecret(ssl, ssl->serverSecret);
                if (ret != 0)
                    goto end;
            }
            break;
    }

    if (!store)
        goto end;

    /* Key data = client key | server key | client IV | server IV */

    if (provision & PROVISION_CLIENT) {
        /* Derive the client key.  */
        WOLFSSL_MSG("Derive Client Key");
        ret = DeriveKey(ssl, &key_dig[i], ssl->specs.key_size,
                        ssl->clientSecret, writeKeyLabel,
                        WRITE_KEY_LABEL_SZ, ssl->specs.mac_algorithm, 0);
        if (ret != 0)
            goto end;
        i += ssl->specs.key_size;
    }

    if (provision & PROVISION_SERVER) {
        /* Derive the server key.  */
        WOLFSSL_MSG("Derive Server Key");
        ret = DeriveKey(ssl, &key_dig[i], ssl->specs.key_size,
                        ssl->serverSecret, writeKeyLabel,
                        WRITE_KEY_LABEL_SZ, ssl->specs.mac_algorithm, 0);
        if (ret != 0)
            goto end;
        i += ssl->specs.key_size;
    }

    if (provision & PROVISION_CLIENT) {
        /* Derive the client IV.  */
        WOLFSSL_MSG("Derive Client IV");
        ret = DeriveKey(ssl, &key_dig[i], ssl->specs.iv_size,
                        ssl->clientSecret, writeIVLabel,
                        WRITE_IV_LABEL_SZ, ssl->specs.mac_algorithm, 0);
        if (ret != 0)
            goto end;
        i += ssl->specs.iv_size;
    }

    if (provision & PROVISION_SERVER) {
        /* Derive the server IV.  */
        WOLFSSL_MSG("Derive Server IV");
        ret = DeriveKey(ssl, &key_dig[i], ssl->specs.iv_size,
                        ssl->serverSecret, writeIVLabel,
                        WRITE_IV_LABEL_SZ, ssl->specs.mac_algorithm, 0);
        if (ret != 0)
            goto end;
    }

    /* Store keys and IVs but don't activate them. */
    ret = StoreKeys(ssl, key_dig, provision);

end:
#ifdef WOLFSSL_SMALL_STACK
    XFREE(key_dig, ssl->heap, DYNAMIC_TYPE_DIGEST);
#endif

    return ret;
}

#ifdef HAVE_SESSION_TICKET
#if defined(USER_TICKS)
#if 0
    word32 TimeNowInMilliseconds(void)
    {
        /*
        write your own clock tick function if don't want gettimeofday()
        needs millisecond accuracy but doesn't have to correlated to EPOCH
        */
    }
#endif

#elif defined(TIME_OVERRIDES)
    #ifndef HAVE_TIME_T_TYPE
        typedef long time_t;
    #endif
    extern time_t XTIME(time_t * timer);

    /* The time in milliseconds.
     * Used for tickets to represent difference between when first seen and when
     * sending.
     *
     * returns the time in milliseconds as a 32-bit value.
     */
    word32 TimeNowInMilliseconds(void)
    {
        return (word32) XTIME(0) * 1000;
    }

#elif defined(XTIME_MS)
    word32 TimeNowInMilliseconds(void)
    {
        return (word32)XTIME_MS(0);
    }

#elif defined(USE_WINDOWS_API)
    /* The time in milliseconds.
     * Used for tickets to represent difference between when first seen and when
     * sending.
     *
     * returns the time in milliseconds as a 32-bit value.
     */
    word32 TimeNowInMilliseconds(void)
    {
        static int           init = 0;
        static LARGE_INTEGER freq;
        LARGE_INTEGER        count;

        if (!init) {
            QueryPerformanceFrequency(&freq);
            init = 1;
        }

        QueryPerformanceCounter(&count);

        return (word32)(count.QuadPart / (freq.QuadPart / 1000));
    }

#elif defined(HAVE_RTP_SYS)
    #include "rtptime.h"

    /* The time in milliseconds.
     * Used for tickets to represent difference between when first seen and when
     * sending.
     *
     * returns the time in milliseconds as a 32-bit value.
     */
    word32 TimeNowInMilliseconds(void)
    {
        return (word32)rtp_get_system_sec() * 1000;
    }
#elif defined(WOLFSSL_DEOS)
    word32 TimeNowInMilliseconds(void)
    {
        const uint32_t systemTickTimeInHz = 1000000 / systemTickInMicroseconds();
        uint32_t *systemTickPtr = systemTickPointer();

        return (word32) (*systemTickPtr/systemTickTimeInHz) * 1000;
    }
#elif defined(MICRIUM)
    /* The time in milliseconds.
     * Used for tickets to represent difference between when first seen and when
     * sending.
     *
     * returns the time in milliseconds as a 32-bit value.
     */
    word32 TimeNowInMilliseconds(void)
    {
        OS_TICK ticks = 0;
        OS_ERR  err;

        ticks = OSTimeGet(&err);

        return (word32) (ticks / OSCfg_TickRate_Hz) * 1000;
    }
#elif defined(MICROCHIP_TCPIP_V5)
    /* The time in milliseconds.
     * Used for tickets to represent difference between when first seen and when
     * sending.
     *
     * returns the time in milliseconds as a 32-bit value.
     */
    word32 TimeNowInMilliseconds(void)
    {
        return (word32) (TickGet() / (TICKS_PER_SECOND / 1000));
    }
#elif defined(MICROCHIP_TCPIP)
    #if defined(MICROCHIP_MPLAB_HARMONY)
        #include <system/tmr/sys_tmr.h>

    /* The time in milliseconds.
     * Used for tickets to represent difference between when first seen and when
     * sending.
     *
     * returns the time in milliseconds as a 32-bit value.
     */
    word32 TimeNowInMilliseconds(void)
    {
        return (word32)(SYS_TMR_TickCountGet() /
                        (SYS_TMR_TickCounterFrequencyGet() / 1000));
    }
    #else
    /* The time in milliseconds.
     * Used for tickets to represent difference between when first seen and when
     * sending.
     *
     * returns the time in milliseconds as a 32-bit value.
     */
    word32 TimeNowInMilliseconds(void)
    {
        return (word32)(SYS_TICK_Get() / (SYS_TICK_TicksPerSecondGet() / 1000));
    }

    #endif

#elif defined(FREESCALE_MQX) || defined(FREESCALE_KSDK_MQX)
    /* The time in milliseconds.
     * Used for tickets to represent difference between when first seen and when
     * sending.
     *
     * returns the time in milliseconds as a 32-bit value.
     */
    word32 TimeNowInMilliseconds(void)
    {
        TIME_STRUCT mqxTime;

        _time_get_elapsed(&mqxTime);

        return (word32) mqxTime.SECONDS * 1000;
    }
#elif defined(FREESCALE_FREE_RTOS) || defined(FREESCALE_KSDK_FREERTOS)
    #include "include/task.h"

    /* The time in milliseconds.
     * Used for tickets to represent difference between when first seen and when
     * sending.
     *
     * returns the time in milliseconds as a 32-bit value.
     */
    word32 TimeNowInMilliseconds(void)
    {
        return (unsigned int)(((float)xTaskGetTickCount()) /
                              (configTICK_RATE_HZ / 1000));
    }
#elif defined(FREESCALE_KSDK_BM)
    #include "lwip/sys.h" /* lwIP */

    /* The time in milliseconds.
     * Used for tickets to represent difference between when first seen and when
     * sending.
     *
     * returns the time in milliseconds as a 32-bit value.
     */
    word32 TimeNowInMilliseconds(void)
    {
        return sys_now();
    }
#elif defined(WOLFSSL_TIRTOS)
    /* The time in milliseconds.
     * Used for tickets to represent difference between when first seen and when
     * sending.
     *
     * returns the time in milliseconds as a 32-bit value.
     */
    word32 TimeNowInMilliseconds(void)
    {
        return (word32) Seconds_get() * 1000;
    }
#elif defined(WOLFSSL_UTASKER)
    /* The time in milliseconds.
     * Used for tickets to represent difference between when first seen and when
     * sending.
     *
     * returns the time in milliseconds as a 32-bit value.
     */
    word32 TimeNowInMilliseconds(void)
    {
        return (word32)(uTaskerSystemTick / (TICK_RESOLUTION / 1000));
    }
#else
    /* The time in milliseconds.
     * Used for tickets to represent difference between when first seen and when
     * sending.
     *
     * returns the time in milliseconds as a 32-bit value.
     */
    word32 TimeNowInMilliseconds(void)
    {
        struct timeval now;

        if (gettimeofday(&now, 0) < 0)
            return GETTIME_ERROR;
        /* Convert to milliseconds number. */
        return (word32)(now.tv_sec * 1000 + now.tv_usec / 1000);
    }
#endif
#endif /* HAVE_SESSION_TICKET || !NO_PSK */


/* Extract the handshake header information.
 *
 * ssl       The SSL/TLS object.
 * input     The buffer holding the message data.
 * inOutIdx  On entry, the index into the buffer of the handshake data.
 *           On exit, the start of the handshake data.
 * type      Type of handshake message.
 * size      The length of the handshake message data.
 * totalSz   The total size of data in the buffer.
 * returns BUFFER_E if there is not enough input data and 0 on success.
 */
static int GetHandshakeHeader(WOLFSSL* ssl, const byte* input, word32* inOutIdx,
                              byte* type, word32* size, word32 totalSz)
{
    const byte* ptr = input + *inOutIdx;
    (void)ssl;

    *inOutIdx += HANDSHAKE_HEADER_SZ;
    if (*inOutIdx > totalSz)
        return BUFFER_E;

    *type = ptr[0];
    c24to32(&ptr[1], size);

    return 0;
}

/* Add record layer header to message.
 *
 * output  The buffer to write the record layer header into.
 * length  The length of the record data.
 * type    The type of record message.
 * ssl     The SSL/TLS object.
 */
static void AddTls13RecordHeader(byte* output, word32 length, byte type,
                                 WOLFSSL* ssl)
{
    RecordLayerHeader* rl;

    rl = (RecordLayerHeader*)output;
    rl->type    = type;
    rl->pvMajor = ssl->version.major;
    /* NOTE: May be TLSv1_MINOR when sending first ClientHello. */
    rl->pvMinor = TLSv1_2_MINOR;
    c16toa((word16)length, rl->length);
}

/* Add handshake header to message.
 *
 * output      The buffer to write the handshake header into.
 * length      The length of the handshake data.
 * fragOffset  The offset of the fragment data. (DTLS)
 * fragLength  The length of the fragment data. (DTLS)
 * type        The type of handshake message.
 * ssl         The SSL/TLS object. (DTLS)
 */
static void AddTls13HandShakeHeader(byte* output, word32 length,
                                    word32 fragOffset, word32 fragLength,
                                    byte type, WOLFSSL* ssl)
{
    HandShakeHeader* hs;
    (void)fragOffset;
    (void)fragLength;
    (void)ssl;

    /* handshake header */
    hs = (HandShakeHeader*)output;
    hs->type = type;
    c32to24(length, hs->length);
}


/* Add both record layer and handshake header to message.
 *
 * output      The buffer to write the headers into.
 * length      The length of the handshake data.
 * type        The type of record layer message.
 * ssl         The SSL/TLS object. (DTLS)
 */
static void AddTls13Headers(byte* output, word32 length, byte type,
                            WOLFSSL* ssl)
{
    word32 lengthAdj = HANDSHAKE_HEADER_SZ;
    word32 outputAdj = RECORD_HEADER_SZ;

    AddTls13RecordHeader(output, length + lengthAdj, handshake, ssl);
    AddTls13HandShakeHeader(output + outputAdj, length, 0, length, type, ssl);
}


#ifndef NO_CERTS
/* Add both record layer and fragment handshake header to message.
 *
 * output      The buffer to write the headers into.
 * fragOffset  The offset of the fragment data. (DTLS)
 * fragLength  The length of the fragment data. (DTLS)
 * length      The length of the handshake data.
 * type        The type of record layer message.
 * ssl         The SSL/TLS object. (DTLS)
 */
static void AddTls13FragHeaders(byte* output, word32 fragSz, word32 fragOffset,
                                word32 length, byte type, WOLFSSL* ssl)
{
    word32 lengthAdj = HANDSHAKE_HEADER_SZ;
    word32 outputAdj = RECORD_HEADER_SZ;
    (void)fragSz;

    AddTls13RecordHeader(output, fragSz + lengthAdj, handshake, ssl);
    AddTls13HandShakeHeader(output + outputAdj, length, fragOffset, fragSz,
                            type, ssl);
}
#endif /* NO_CERTS */

/* Write the sequence number into the buffer.
 * No DTLS v1.3 support.
 *
 * ssl          The SSL/TLS object.
 * verifyOrder  Which set of sequence numbers to use.
 * out          The buffer to write into.
 */
static WC_INLINE void WriteSEQTls13(WOLFSSL* ssl, int verifyOrder, byte* out)
{
    word32 seq[2] = {0, 0};

    if (verifyOrder) {
        seq[0] = ssl->keys.peer_sequence_number_hi;
        seq[1] = ssl->keys.peer_sequence_number_lo++;
        /* handle rollover */
        if (seq[1] > ssl->keys.peer_sequence_number_lo)
            ssl->keys.peer_sequence_number_hi++;
    }
    else {
        seq[0] = ssl->keys.sequence_number_hi;
        seq[1] = ssl->keys.sequence_number_lo++;
        /* handle rollover */
        if (seq[1] > ssl->keys.sequence_number_lo)
            ssl->keys.sequence_number_hi++;
    }

    c32toa(seq[0], out);
    c32toa(seq[1], out + OPAQUE32_LEN);
}

/* Build the nonce for TLS v1.3 encryption and decryption.
 *
 * ssl    The SSL/TLS object.
 * nonce  The nonce data to use when encrypting or decrypting.
 * iv     The derived IV.
 * order  The side on which the message is to be or was sent.
 */
static WC_INLINE void BuildTls13Nonce(WOLFSSL* ssl, byte* nonce, const byte* iv,
                                   int order)
{
    int  i;

    /* The nonce is the IV with the sequence XORed into the last bytes. */
    WriteSEQTls13(ssl, order, nonce + AEAD_NONCE_SZ - SEQ_SZ);
    for (i = 0; i < AEAD_NONCE_SZ - SEQ_SZ; i++)
        nonce[i] = iv[i];
    for (; i < AEAD_NONCE_SZ; i++)
        nonce[i] ^= iv[i];
}

#if defined(HAVE_CHACHA) && defined(HAVE_POLY1305)
/* Encrypt with ChaCha20 and create authenication tag with Poly1305.
 *
 * ssl     The SSL/TLS object.
 * output  The buffer to write encrypted data and authentication tag into.
 *         May be the same pointer as input.
 * input   The data to encrypt.
 * sz      The number of bytes to encrypt.
 * nonce   The nonce to use with ChaCha20.
 * aad     The additional authentication data.
 * aadSz   The size of the addition authentication data.
 * tag     The authentication tag buffer.
 * returns 0 on success, otherwise failure.
 */
static int ChaCha20Poly1305_Encrypt(WOLFSSL* ssl, byte* output,
                                    const byte* input, word16 sz, byte* nonce,
                                    const byte* aad, word16 aadSz, byte* tag)
{
    int    ret    = 0;
    byte   poly[CHACHA20_256_KEY_SIZE];

    /* Poly1305 key is 256 bits of zero encrypted with ChaCha20. */
    XMEMSET(poly, 0, sizeof(poly));

    /* Set the nonce for ChaCha and get Poly1305 key. */
    ret = wc_Chacha_SetIV(ssl->encrypt.chacha, nonce, 0);
    if (ret != 0)
        return ret;
    /* Create Poly1305 key using ChaCha20 keystream. */
    ret = wc_Chacha_Process(ssl->encrypt.chacha, poly, poly, sizeof(poly));
    if (ret != 0)
        return ret;
    ret = wc_Chacha_SetIV(ssl->encrypt.chacha, nonce, 1);
    if (ret != 0)
        return ret;
    /* Encrypt the plain text. */
    ret = wc_Chacha_Process(ssl->encrypt.chacha, output, input, sz);
    if (ret != 0) {
        ForceZero(poly, sizeof(poly));
        return ret;
    }

    /* Set key for Poly1305. */
    ret = wc_Poly1305SetKey(ssl->auth.poly1305, poly, sizeof(poly));
    ForceZero(poly, sizeof(poly)); /* done with poly1305 key, clear it */
    if (ret != 0)
        return ret;
    /* Add authentication code of encrypted data to end. */
    ret = wc_Poly1305_MAC(ssl->auth.poly1305, (byte*)aad, aadSz, output, sz,
                          tag, POLY1305_AUTH_SZ);

    return ret;
}
#endif

#ifdef HAVE_NULL_CIPHER
/* Create authenication tag and copy data over input.
 *
 * ssl     The SSL/TLS object.
 * output  The buffer to copy data into.
 *         May be the same pointer as input.
 * input   The data.
 * sz      The number of bytes of data.
 * nonce   The nonce to use with authentication.
 * aad     The additional authentication data.
 * aadSz   The size of the addition authentication data.
 * tag     The authentication tag buffer.
 * returns 0 on success, otherwise failure.
 */
static int Tls13IntegrityOnly_Encrypt(WOLFSSL* ssl, byte* output,
                                      const byte* input, word16 sz,
                                      const byte* nonce,
                                      const byte* aad, word16 aadSz, byte* tag)
{
    int ret;

    /* HMAC: nonce | aad | input  */
    ret = wc_HmacUpdate(ssl->encrypt.hmac, nonce, HMAC_NONCE_SZ);
    if (ret == 0)
        ret = wc_HmacUpdate(ssl->encrypt.hmac, aad, aadSz);
    if (ret == 0)
        ret = wc_HmacUpdate(ssl->encrypt.hmac, input, sz);
    if (ret == 0)
        ret = wc_HmacFinal(ssl->encrypt.hmac, tag);
    /* Copy the input to output if not the same buffer */
    if (ret == 0 && output != input)
        XMEMCPY(output, input, sz);

    return ret;
}
#endif

/* Encrypt data for TLS v1.3.
 *
 * ssl     The SSL/TLS object.
 * output  The buffer to write encrypted data and authentication tag into.
 *         May be the same pointer as input.
 * input   The record header and data to encrypt.
 * sz      The number of bytes to encrypt.
 * aad     The additional authentication data.
 * aadSz   The size of the addition authentication data.
 * asyncOkay If non-zero can return WC_PENDING_E, otherwise blocks on crypto
 * returns 0 on success, otherwise failure.
 */
static int EncryptTls13(WOLFSSL* ssl, byte* output, const byte* input,
                        word16 sz, const byte* aad, word16 aadSz, int asyncOkay)
{
    int    ret    = 0;
    word16 dataSz = sz - ssl->specs.aead_mac_size;
    word16 macSz  = ssl->specs.aead_mac_size;
    word32 nonceSz = 0;
#ifdef WOLFSSL_ASYNC_CRYPT
    WC_ASYNC_DEV* asyncDev = NULL;
    word32 event_flags = WC_ASYNC_FLAG_CALL_AGAIN;
#endif

    WOLFSSL_ENTER("EncryptTls13");

    (void)output;
    (void)input;
    (void)sz;
    (void)dataSz;
    (void)macSz;
    (void)asyncOkay;
    (void)nonceSz;

#ifdef WOLFSSL_ASYNC_CRYPT
    if (ssl->error == WC_PENDING_E) {
        ssl->error = 0; /* clear async */
    }
#endif

    switch (ssl->encrypt.state) {
        case CIPHER_STATE_BEGIN:
        {
        #ifdef WOLFSSL_DEBUG_TLS
            WOLFSSL_MSG("Data to encrypt");
            WOLFSSL_BUFFER(input, dataSz);
            WOLFSSL_MSG("Additional Authentication Data");
            WOLFSSL_BUFFER(aad, aadSz);
        #endif

        #ifdef CIPHER_NONCE
            if (ssl->encrypt.nonce == NULL)
                ssl->encrypt.nonce = (byte*)XMALLOC(AEAD_NONCE_SZ,
                                            ssl->heap, DYNAMIC_TYPE_AES_BUFFER);
            if (ssl->encrypt.nonce == NULL)
                return MEMORY_E;

            BuildTls13Nonce(ssl, ssl->encrypt.nonce, ssl->keys.aead_enc_imp_IV,
                            CUR_ORDER);
        #endif

            /* Advance state and proceed */
            ssl->encrypt.state = CIPHER_STATE_DO;
        }
        FALL_THROUGH;

        case CIPHER_STATE_DO:
        {
            switch (ssl->specs.bulk_cipher_algorithm) {
            #ifdef BUILD_AESGCM
                case wolfssl_aes_gcm:
                #ifdef WOLFSSL_ASYNC_CRYPT
                    /* initialize event */
                    asyncDev = &ssl->encrypt.aes->asyncDev;
                    ret = wolfSSL_AsyncInit(ssl, asyncDev, event_flags);
                    if (ret != 0)
                        break;
                #endif

                    nonceSz = AESGCM_NONCE_SZ;
                #if ((defined(HAVE_FIPS) || defined(HAVE_SELFTEST)) && \
                    (!defined(HAVE_FIPS_VERSION) || (HAVE_FIPS_VERSION < 2)))
                    ret = wc_AesGcmEncrypt(ssl->encrypt.aes, output, input,
                        dataSz, ssl->encrypt.nonce, nonceSz,
                        output + dataSz, macSz, aad, aadSz);
                #else
                    ret = wc_AesGcmSetExtIV(ssl->encrypt.aes,
                            ssl->encrypt.nonce, nonceSz);
                    if (ret == 0) {
                        ret = wc_AesGcmEncrypt_ex(ssl->encrypt.aes, output,
                                input, dataSz, ssl->encrypt.nonce, nonceSz,
                                output + dataSz, macSz, aad, aadSz);
                    }
                #endif
                    break;
            #endif

            #ifdef HAVE_AESCCM
                case wolfssl_aes_ccm:
                #ifdef WOLFSSL_ASYNC_CRYPT
                    /* initialize event */
                    asyncDev = &ssl->encrypt.aes->asyncDev;
                    ret = wolfSSL_AsyncInit(ssl, asyncDev, event_flags);
                    if (ret != 0)
                        break;
                #endif

                    nonceSz = AESCCM_NONCE_SZ;
                #if ((defined(HAVE_FIPS) || defined(HAVE_SELFTEST)) && \
                    (!defined(HAVE_FIPS_VERSION) || (HAVE_FIPS_VERSION < 2)))
                    ret = wc_AesCcmEncrypt(ssl->encrypt.aes, output, input,
                        dataSz, ssl->encrypt.nonce, nonceSz,
                        output + dataSz, macSz, aad, aadSz);
                #else
                    ret = wc_AesCcmSetNonce(ssl->encrypt.aes,
                            ssl->encrypt.nonce, nonceSz);
                    if (ret == 0) {
                        ret = wc_AesCcmEncrypt_ex(ssl->encrypt.aes, output,
                                input, dataSz, ssl->encrypt.nonce, nonceSz,
                                output + dataSz, macSz, aad, aadSz);
                    }
                #endif
                    break;
            #endif

            #if defined(HAVE_CHACHA) && defined(HAVE_POLY1305)
                case wolfssl_chacha:
                    ret = ChaCha20Poly1305_Encrypt(ssl, output, input, dataSz,
                        ssl->encrypt.nonce, aad, aadSz, output + dataSz);
                    break;
            #endif

            #ifdef HAVE_NULL_CIPHER
                case wolfssl_cipher_null:
                    ret = Tls13IntegrityOnly_Encrypt(ssl, output, input, dataSz,
                        ssl->encrypt.nonce, aad, aadSz, output + dataSz);
                    break;
            #endif

                default:
                    WOLFSSL_MSG("wolfSSL Encrypt programming error");
                    return ENCRYPT_ERROR;
            }

            /* Advance state */
            ssl->encrypt.state = CIPHER_STATE_END;

        #ifdef WOLFSSL_ASYNC_CRYPT
            if (ret == WC_PENDING_E) {
                /* if async is not okay, then block */
                if (!asyncOkay) {
                    ret = wc_AsyncWait(ret, asyncDev, event_flags);
                }
                else {
                    /* If pending, then leave and return will resume below */
                    return wolfSSL_AsyncPush(ssl, asyncDev);
                }
            }
        #endif
        }
        FALL_THROUGH;

        case CIPHER_STATE_END:
        {
        #ifdef WOLFSSL_DEBUG_TLS
            #ifdef CIPHER_NONCE
                WOLFSSL_MSG("Nonce");
                WOLFSSL_BUFFER(ssl->encrypt.nonce, ssl->specs.iv_size);
            #endif
                WOLFSSL_MSG("Encrypted data");
                WOLFSSL_BUFFER(output, dataSz);
                WOLFSSL_MSG("Authentication Tag");
                WOLFSSL_BUFFER(output + dataSz, macSz);
        #endif

        #ifdef CIPHER_NONCE
            ForceZero(ssl->encrypt.nonce, AEAD_NONCE_SZ);
        #endif

            break;
        }
    }

    /* Reset state */
    ssl->encrypt.state = CIPHER_STATE_BEGIN;

    return ret;
}

#if defined(HAVE_CHACHA) && defined(HAVE_POLY1305)
/* Decrypt with ChaCha20 and check authenication tag with Poly1305.
 *
 * ssl     The SSL/TLS object.
 * output  The buffer to write decrypted data into.
 *         May be the same pointer as input.
 * input   The data to decrypt.
 * sz      The number of bytes to decrypt.
 * nonce   The nonce to use with ChaCha20.
 * aad     The additional authentication data.
 * aadSz   The size of the addition authentication data.
 * tagIn   The authentication tag data from packet.
 * returns 0 on success, otherwise failure.
 */
static int ChaCha20Poly1305_Decrypt(WOLFSSL* ssl, byte* output,
                                    const byte* input, word16 sz, byte* nonce,
                                    const byte* aad, word16 aadSz,
                                    const byte* tagIn)
{
    int ret;
    byte tag[POLY1305_AUTH_SZ];
    byte poly[CHACHA20_256_KEY_SIZE]; /* generated key for mac */

    /* Poly1305 key is 256 bits of zero encrypted with ChaCha20. */
    XMEMSET(poly, 0, sizeof(poly));

    /* Set nonce and get Poly1305 key. */
    ret = wc_Chacha_SetIV(ssl->decrypt.chacha, nonce, 0);
    if (ret != 0)
        return ret;
    /* Use ChaCha20 keystream to get Poly1305 key for tag. */
    ret = wc_Chacha_Process(ssl->decrypt.chacha, poly, poly, sizeof(poly));
    if (ret != 0)
        return ret;
    ret = wc_Chacha_SetIV(ssl->decrypt.chacha, nonce, 1);
    if (ret != 0)
        return ret;

    /* Set key for Poly1305. */
    ret = wc_Poly1305SetKey(ssl->auth.poly1305, poly, sizeof(poly));
    ForceZero(poly, sizeof(poly)); /* done with poly1305 key, clear it */
    if (ret != 0)
        return ret;
    /* Generate authentication tag for encrypted data. */
    if ((ret = wc_Poly1305_MAC(ssl->auth.poly1305, (byte*)aad, aadSz,
                                    (byte*)input, sz, tag, sizeof(tag))) != 0) {
        return ret;
    }

    /* Check tag sent along with packet. */
    if (ConstantCompare(tagIn, tag, POLY1305_AUTH_SZ) != 0) {
        WOLFSSL_MSG("MAC did not match");
        return VERIFY_MAC_ERROR;
    }

    /* If the tag was good decrypt message. */
    ret = wc_Chacha_Process(ssl->decrypt.chacha, output, input, sz);

    return ret;
}
#endif

#ifdef HAVE_NULL_CIPHER
/* Check HMAC tag and copy over input.
 *
 * ssl     The SSL/TLS object.
 * output  The buffer to copy data into.
 *         May be the same pointer as input.
 * input   The data.
 * sz      The number of bytes of data.
 * nonce   The nonce to use with authentication.
 * aad     The additional authentication data.
 * aadSz   The size of the addition authentication data.
 * tagIn   The authentication tag data from packet.
 * returns 0 on success, otherwise failure.
 */
static int Tls13IntegrityOnly_Decrypt(WOLFSSL* ssl, byte* output,
                                      const byte* input, word16 sz,
                                      const byte* nonce,
                                      const byte* aad, word16 aadSz,
                                      const byte* tagIn)
{
    int ret;
    byte hmac[WC_MAX_DIGEST_SIZE];

    /* HMAC: nonce | aad | input  */
    ret = wc_HmacUpdate(ssl->decrypt.hmac, nonce, HMAC_NONCE_SZ);
    if (ret == 0)
        ret = wc_HmacUpdate(ssl->decrypt.hmac, aad, aadSz);
    if (ret == 0)
        ret = wc_HmacUpdate(ssl->decrypt.hmac, input, sz);
    if (ret == 0)
        ret = wc_HmacFinal(ssl->decrypt.hmac, hmac);
    /* Check authentication tag matches */
    if (ret == 0 && ConstantCompare(tagIn, hmac, ssl->specs.hash_size) != 0)
        ret = DECRYPT_ERROR;
    /* Copy the input to output if not the same buffer */
    if (ret == 0 && output != input)
        XMEMCPY(output, input, sz);

    return ret;
}
#endif

/* Decrypt data for TLS v1.3.
 *
 * ssl     The SSL/TLS object.
 * output  The buffer to write decrypted data into.
 *         May be the same pointer as input.
 * input   The data to decrypt and authentication tag.
 * sz      The length of the encrypted data plus authentication tag.
 * aad     The additional authentication data.
 * aadSz   The size of the addition authentication data.
 * returns 0 on success, otherwise failure.
 */
int DecryptTls13(WOLFSSL* ssl, byte* output, const byte* input, word16 sz,
                 const byte* aad, word16 aadSz)
{
    int    ret    = 0;
    word16 dataSz = sz - ssl->specs.aead_mac_size;
    word16 macSz  = ssl->specs.aead_mac_size;
    word32 nonceSz = 0;

    WOLFSSL_ENTER("DecryptTls13");

#ifdef WOLFSSL_ASYNC_CRYPT
    ret = wolfSSL_AsyncPop(ssl, &ssl->decrypt.state);
    if (ret != WC_NOT_PENDING_E) {
        /* check for still pending */
        if (ret == WC_PENDING_E)
            return ret;

        ssl->error = 0; /* clear async */

        /* let failures through so CIPHER_STATE_END logic is run */
    }
    else
#endif
    {
        /* Reset state */
        ret = 0;
        ssl->decrypt.state = CIPHER_STATE_BEGIN;
    }

    (void)output;
    (void)input;
    (void)sz;
    (void)dataSz;
    (void)macSz;
    (void)nonceSz;

    switch (ssl->decrypt.state) {
        case CIPHER_STATE_BEGIN:
        {
        #ifdef WOLFSSL_DEBUG_TLS
            WOLFSSL_MSG("Data to decrypt");
            WOLFSSL_BUFFER(input, dataSz);
            WOLFSSL_MSG("Additional Authentication Data");
            WOLFSSL_BUFFER(aad, aadSz);
            WOLFSSL_MSG("Authentication tag");
            WOLFSSL_BUFFER(input + dataSz, macSz);
        #endif

        #ifdef CIPHER_NONCE
            if (ssl->decrypt.nonce == NULL)
                ssl->decrypt.nonce = (byte*)XMALLOC(AEAD_NONCE_SZ,
                                            ssl->heap, DYNAMIC_TYPE_AES_BUFFER);
            if (ssl->decrypt.nonce == NULL)
                return MEMORY_E;

            BuildTls13Nonce(ssl, ssl->decrypt.nonce, ssl->keys.aead_dec_imp_IV,
                            PEER_ORDER);
        #endif

            /* Advance state and proceed */
            ssl->decrypt.state = CIPHER_STATE_DO;
        }
        FALL_THROUGH;

        case CIPHER_STATE_DO:
        {
            switch (ssl->specs.bulk_cipher_algorithm) {
            #ifdef BUILD_AESGCM
                case wolfssl_aes_gcm:
                #ifdef WOLFSSL_ASYNC_CRYPT
                    /* initialize event */
                    ret = wolfSSL_AsyncInit(ssl, &ssl->decrypt.aes->asyncDev,
                        WC_ASYNC_FLAG_CALL_AGAIN);
                    if (ret != 0)
                        break;
                #endif

                    nonceSz = AESGCM_NONCE_SZ;
                    ret = wc_AesGcmDecrypt(ssl->decrypt.aes, output, input,
                        dataSz, ssl->decrypt.nonce, nonceSz,
                        input + dataSz, macSz, aad, aadSz);
                #ifdef WOLFSSL_ASYNC_CRYPT
                    if (ret == WC_PENDING_E) {
                        ret = wolfSSL_AsyncPush(ssl,
                                                   &ssl->decrypt.aes->asyncDev);
                    }
                #endif
                    break;
            #endif

            #ifdef HAVE_AESCCM
                case wolfssl_aes_ccm:
                #ifdef WOLFSSL_ASYNC_CRYPT
                    /* initialize event */
                    ret = wolfSSL_AsyncInit(ssl, &ssl->decrypt.aes->asyncDev,
                        WC_ASYNC_FLAG_CALL_AGAIN);
                    if (ret != 0)
                        break;
                #endif

                    nonceSz = AESCCM_NONCE_SZ;
                    ret = wc_AesCcmDecrypt(ssl->decrypt.aes, output, input,
                        dataSz, ssl->decrypt.nonce, nonceSz,
                        input + dataSz, macSz, aad, aadSz);
                #ifdef WOLFSSL_ASYNC_CRYPT
                    if (ret == WC_PENDING_E) {
                        ret = wolfSSL_AsyncPush(ssl,
                                                   &ssl->decrypt.aes->asyncDev);
                    }
                #endif
                    break;
            #endif

            #if defined(HAVE_CHACHA) && defined(HAVE_POLY1305)
                case wolfssl_chacha:
                    ret = ChaCha20Poly1305_Decrypt(ssl, output, input, dataSz,
                        ssl->decrypt.nonce, aad, aadSz, input + dataSz);
                    break;
            #endif

            #ifdef HAVE_NULL_CIPHER
                case wolfssl_cipher_null:
                    ret = Tls13IntegrityOnly_Decrypt(ssl, output, input, dataSz,
                        ssl->decrypt.nonce, aad, aadSz, input + dataSz);
                    break;
            #endif
                default:
                    WOLFSSL_MSG("wolfSSL Decrypt programming error");
                    return DECRYPT_ERROR;
            }

            /* Advance state */
            ssl->decrypt.state = CIPHER_STATE_END;

        #ifdef WOLFSSL_ASYNC_CRYPT
            /* If pending, leave now */
            if (ret == WC_PENDING_E) {
                return ret;
            }
        #endif
        }
        FALL_THROUGH;

        case CIPHER_STATE_END:
        {
        #ifdef WOLFSSL_DEBUG_TLS
            #ifdef CIPHER_NONCE
                WOLFSSL_MSG("Nonce");
                WOLFSSL_BUFFER(ssl->decrypt.nonce, ssl->specs.iv_size);
            #endif
                WOLFSSL_MSG("Decrypted data");
                WOLFSSL_BUFFER(output, dataSz);
        #endif

        #ifdef CIPHER_NONCE
            ForceZero(ssl->decrypt.nonce, AEAD_NONCE_SZ);
        #endif

            break;
        }
    }

#ifndef WOLFSSL_EARLY_DATA
    if (ret < 0) {
        SendAlert(ssl, alert_fatal, bad_record_mac);
        ret = VERIFY_MAC_ERROR;
    }
#endif

    return ret;
}

/* Persistable BuildTls13Message arguments */
typedef struct BuildMsg13Args {
    word32 sz;
    word32 idx;
    word32 headerSz;
    word16 size;
} BuildMsg13Args;

static void FreeBuildMsg13Args(WOLFSSL* ssl, void* pArgs)
{
    BuildMsg13Args* args = (BuildMsg13Args*)pArgs;

    (void)ssl;
    (void)args;

    /* no allocations in BuildTls13Message */
}

/* Build SSL Message, encrypted.
 * TLS v1.3 encryption is AEAD only.
 *
 * ssl         The SSL/TLS object.
 * output      The buffer to write record message to.
 * outSz       Size of the buffer being written into.
 * input       The record data to encrypt (excluding record header).
 * inSz        The size of the record data.
 * type        The recorder header content type.
 * hashOutput  Whether to hash the unencrypted record data.
 * sizeOnly    Only want the size of the record message.
 * asyncOkay   If non-zero can return WC_PENDING_E, otherwise blocks on crypto
 * returns the size of the encrypted record message or negative value on error.
 */
int BuildTls13Message(WOLFSSL* ssl, byte* output, int outSz, const byte* input,
                int inSz, int type, int hashOutput, int sizeOnly, int asyncOkay)
{
    int ret = 0;
    BuildMsg13Args* args;
    BuildMsg13Args  lcl_args;
#ifdef WOLFSSL_ASYNC_CRYPT
    args = (BuildMsg13Args*)ssl->async.args;
    typedef char args_test[sizeof(ssl->async.args) >= sizeof(*args) ? 1 : -1];
    (void)sizeof(args_test);
#endif

    WOLFSSL_ENTER("BuildTls13Message");

    ret = WC_NOT_PENDING_E;
#ifdef WOLFSSL_ASYNC_CRYPT
    if (asyncOkay) {
        ret = wolfSSL_AsyncPop(ssl, &ssl->options.buildMsgState);
        if (ret != WC_NOT_PENDING_E) {
            /* Check for error */
            if (ret < 0)
                goto exit_buildmsg;
        }
    }
    else
#endif
    {
        args = &lcl_args;
    }

    /* Reset state */
    if (ret == WC_NOT_PENDING_E) {
        ret = 0;
        ssl->options.buildMsgState = BUILD_MSG_BEGIN;
        XMEMSET(args, 0, sizeof(BuildMsg13Args));

        args->sz = RECORD_HEADER_SZ + inSz;
        args->idx  = RECORD_HEADER_SZ;
        args->headerSz = RECORD_HEADER_SZ;
    #ifdef WOLFSSL_ASYNC_CRYPT
        ssl->async.freeArgs = FreeBuildMsg13Args;
    #endif
    }

    switch (ssl->options.buildMsgState) {
        case BUILD_MSG_BEGIN:
        {
           /* catch mistaken sizeOnly parameter */
            if (sizeOnly) {
                if (output || input) {
                    WOLFSSL_MSG("BuildTls13Message with sizeOnly "
                                "doesn't need input or output");
                    return BAD_FUNC_ARG;
                }
            }
            else if (output == NULL || input == NULL) {
                return BAD_FUNC_ARG;
            }

            /* Record layer content type at the end of record data. */
            args->sz++;
            /* Authentication data at the end. */
            args->sz += ssl->specs.aead_mac_size;

            if (sizeOnly)
                return args->sz;

            if (args->sz > (word32)outSz) {
                WOLFSSL_MSG("Oops, want to write past output buffer size");
                return BUFFER_E;
            }

            /* Record data length. */
            args->size = (word16)(args->sz - args->headerSz);
            /* Write/update the record header with the new size.
             * Always have the content type as application data for encrypted
             * messages in TLS v1.3.
             */
            AddTls13RecordHeader(output, args->size, application_data, ssl);

            /* TLS v1.3 can do in place encryption. */
            if (input != output + args->idx)
                XMEMCPY(output + args->idx, input, inSz);
            args->idx += inSz;

            ssl->options.buildMsgState = BUILD_MSG_HASH;
        }
        FALL_THROUGH;

        case BUILD_MSG_HASH:
        {
            if (hashOutput) {
                ret = HashOutput(ssl, output, args->headerSz + inSz, 0);
                if (ret != 0)
                    goto exit_buildmsg;
            }

            /* The real record content type goes at the end of the data. */
            output[args->idx++] = (byte)type;

            ssl->options.buildMsgState = BUILD_MSG_ENCRYPT;
        }
        FALL_THROUGH;

        case BUILD_MSG_ENCRYPT:
        {
        #ifdef ATOMIC_USER
            if (ssl->ctx->MacEncryptCb) {
                /* User Record Layer Callback handling */
                byte* mac = output + args->idx;
                output += args->headerSz;

                ret = ssl->ctx->MacEncryptCb(ssl, mac, output, inSz, type, 0,
                        output, output, args->size, ssl->MacEncryptCtx);
            }
            else
        #endif
            {
                const byte* aad = output;
                output += args->headerSz;
                ret = EncryptTls13(ssl, output, output, args->size, aad,
                                   RECORD_HEADER_SZ, asyncOkay);
            }
            break;
        }
    }

exit_buildmsg:

    WOLFSSL_LEAVE("BuildTls13Message", ret);

#ifdef WOLFSSL_ASYNC_CRYPT
    if (ret == WC_PENDING_E) {
        return ret;
    }
#endif

    /* make sure build message state is reset */
    ssl->options.buildMsgState = BUILD_MSG_BEGIN;

    /* return sz on success */
    if (ret == 0)
        ret = args->sz;

    /* Final cleanup */
    FreeBuildMsg13Args(ssl, args);
#ifdef WOLFSSL_ASYNC_CRYPT
    ssl->async.freeArgs = NULL;
#endif

    return ret;
}

#if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
/* Find the cipher suite in the suites set in the SSL.
 *
 * ssl    SSL/TLS object.
 * suite  Cipher suite to look for.
 * returns 1 when suite is found in SSL/TLS object's list and 0 otherwise.
 */
static int FindSuiteSSL(WOLFSSL* ssl, byte* suite)
{
    word16 i;

    for (i = 0; i < ssl->suites->suiteSz; i += 2) {
        if (ssl->suites->suites[i+0] == suite[0] &&
            ssl->suites->suites[i+1] == suite[1]) {
            return 1;
        }
    }

    return 0;
}
#endif

#if defined(WOLFSSL_SEND_HRR_COOKIE) && !defined(NO_WOLFSSL_SERVER)
/* Create Cookie extension using the hash of the first ClientHello.
 *
 * ssl     SSL/TLS object.
 * hash    The hash data.
 * hashSz  The size of the hash data in bytes.
 * returns 0 on success, otherwise failure.
 */
static int CreateCookie(WOLFSSL* ssl, byte* hash, byte hashSz)
{
    int  ret;
    byte mac[WC_MAX_DIGEST_SIZE] = {0};
    Hmac cookieHmac;
    byte cookieType = 0;
    byte macSz = 0;

#if !defined(NO_SHA) && defined(NO_SHA256)
    cookieType = SHA;
    macSz = WC_SHA_DIGEST_SIZE;
#endif /* NO_SHA */
#ifndef NO_SHA256
    cookieType = WC_SHA256;
    macSz = WC_SHA256_DIGEST_SIZE;
#endif /* NO_SHA256 */
    XMEMSET(&cookieHmac, 0, sizeof(Hmac));

    ret = wc_HmacSetKey(&cookieHmac, cookieType,
                        ssl->buffers.tls13CookieSecret.buffer,
                        ssl->buffers.tls13CookieSecret.length);
    if (ret != 0)
        return ret;
    if ((ret = wc_HmacUpdate(&cookieHmac, hash, hashSz)) != 0)
        return ret;
    if ((ret = wc_HmacFinal(&cookieHmac, mac)) != 0)
        return ret;

    /* The cookie data is the hash and the integrity check. */
    return TLSX_Cookie_Use(ssl, hash, hashSz, mac, macSz, 1);
}
#endif

/* Restart the handshake hash with a hash of the previous messages.
 *
 * ssl The SSL/TLS object.
 * returns 0 on success, otherwise failure.
 */
static int RestartHandshakeHash(WOLFSSL* ssl)
{
    int    ret;
    Hashes hashes;
    byte   header[HANDSHAKE_HEADER_SZ] = {0};
    byte*  hash = NULL;
    byte   hashSz = 0;

    ret = BuildCertHashes(ssl, &hashes);
    if (ret != 0)
        return ret;
    switch (ssl->specs.mac_algorithm) {
    #ifndef NO_SHA256
        case sha256_mac:
            hash = hashes.sha256;
            break;
    #endif
    #ifdef WOLFSSL_SHA384
        case sha384_mac:
            hash = hashes.sha384;
            break;
    #endif
    #ifdef WOLFSSL_TLS13_SHA512
        case sha512_mac:
            hash = hashes.sha512;
            break;
    #endif
    }
    hashSz = ssl->specs.hash_size;

    /* check hash */
    if (hash == NULL && hashSz > 0)
        return BAD_FUNC_ARG;

    AddTls13HandShakeHeader(header, hashSz, 0, 0, message_hash, ssl);

    WOLFSSL_MSG("Restart Hash");
    WOLFSSL_BUFFER(hash, hashSz);

#if defined(WOLFSSL_SEND_HRR_COOKIE) && !defined(NO_WOLFSSL_SERVER)
    if (ssl->options.sendCookie) {
        byte   cookie[OPAQUE8_LEN + WC_MAX_DIGEST_SIZE + OPAQUE16_LEN * 2];
        TLSX*  ext;
        word32 idx = 0;

        /* Cookie Data = Hash Len | Hash | CS | KeyShare Group */
        cookie[idx++] = hashSz;
        if (hash)
            XMEMCPY(cookie + idx, hash, hashSz);
        idx += hashSz;
        cookie[idx++] = ssl->options.cipherSuite0;
        cookie[idx++] = ssl->options.cipherSuite;
        if ((ext = TLSX_Find(ssl->extensions, TLSX_KEY_SHARE)) != NULL) {
            KeyShareEntry* kse = (KeyShareEntry*)ext->data;
            c16toa(kse->group, cookie + idx);
            idx += OPAQUE16_LEN;
        }
        return CreateCookie(ssl, cookie, idx);
    }
#endif

    ret = InitHandshakeHashes(ssl);
    if (ret != 0)
        return ret;
    ret = HashRaw(ssl, header, sizeof(header));
    if (ret != 0)
        return ret;
    return HashRaw(ssl, hash, hashSz);
}

/* The value in the random field of a ServerHello to indicate
 * HelloRetryRequest.
 */
static byte helloRetryRequestRandom[] = {
    0xCF, 0x21, 0xAD, 0x74, 0xE5, 0x9A, 0x61, 0x11,
    0xBE, 0x1D, 0x8C, 0x02, 0x1E, 0x65, 0xB8, 0x91,
    0xC2, 0xA2, 0x11, 0x16, 0x7A, 0xBB, 0x8C, 0x5E,
    0x07, 0x9E, 0x09, 0xE2, 0xC8, 0xA8, 0x33, 0x9C
};


#ifndef NO_WOLFSSL_CLIENT
#if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
/* Setup pre-shared key based on the details in the extension data.
 *
 * ssl  SSL/TLS object.
 * psk  Pre-shared key extension data.
 * returns 0 on success, PSK_KEY_ERROR when the client PSK callback fails and
 * other negative value on failure.
 */
static int SetupPskKey(WOLFSSL* ssl, PreSharedKey* psk)
{
    int ret;
    byte suite[2];

    if (psk == NULL)
        return BAD_FUNC_ARG;

    suite[0] = psk->cipherSuite0;
    suite[1] = psk->cipherSuite;
    if (!FindSuiteSSL(ssl, suite))
        return PSK_KEY_ERROR;

    ssl->options.cipherSuite0 = psk->cipherSuite0;
    ssl->options.cipherSuite  = psk->cipherSuite;
    if ((ret = SetCipherSpecs(ssl)) != 0)
        return ret;

#ifdef HAVE_SESSION_TICKET
    if (psk->resumption) {
    #ifdef WOLFSSL_EARLY_DATA
        if (ssl->session.maxEarlyDataSz == 0)
            ssl->earlyData = no_early_data;
    #endif
        /* Resumption PSK is master secret. */
        ssl->arrays->psk_keySz = ssl->specs.hash_size;
        if ((ret = DeriveResumptionPSK(ssl, ssl->session.ticketNonce.data,
                    ssl->session.ticketNonce.len, ssl->arrays->psk_key)) != 0) {
            return ret;
        }
    }
#endif
#ifndef NO_PSK
    if (!psk->resumption) {
    #ifndef WOLFSSL_PSK_ONE_ID
        const char* cipherName = NULL;
        byte cipherSuite0 = TLS13_BYTE, cipherSuite = WOLFSSL_DEF_PSK_CIPHER;

        /* Get the pre-shared key. */
        if (ssl->options.client_psk_tls13_cb != NULL) {
            ssl->arrays->psk_keySz = ssl->options.client_psk_tls13_cb(ssl,
                    (char *)psk->identity, ssl->arrays->client_identity,
                    MAX_PSK_ID_LEN, ssl->arrays->psk_key, MAX_PSK_KEY_LEN,
                    &cipherName);
            if (GetCipherSuiteFromName(cipherName, &cipherSuite0,
                                                           &cipherSuite) != 0) {
                return PSK_KEY_ERROR;
            }
        }
        else {
            ssl->arrays->psk_keySz = ssl->options.client_psk_cb(ssl,
                    (char *)psk->identity, ssl->arrays->client_identity,
                    MAX_PSK_ID_LEN, ssl->arrays->psk_key, MAX_PSK_KEY_LEN);
        }
        if (ssl->arrays->psk_keySz == 0 ||
                                     ssl->arrays->psk_keySz > MAX_PSK_KEY_LEN) {
            return PSK_KEY_ERROR;
        }

        if (psk->cipherSuite0 != cipherSuite0 ||
                                              psk->cipherSuite != cipherSuite) {
            return PSK_KEY_ERROR;
        }
    #else
        /* PSK information loaded during setting of default TLS extensions. */
    #endif
    }
#endif

    if (ssl->options.noPskDheKe)
        ssl->arrays->preMasterSz = 0;

    /* Derive the early secret using the PSK. */
    return DeriveEarlySecret(ssl);
}

/* Derive and write the binders into the ClientHello in space left when
 * writing the Pre-Shared Key extension.
 *
 * ssl     The SSL/TLS object.
 * output  The buffer containing the ClientHello.
 * idx     The index at the end of the completed ClientHello.
 * returns 0 on success and otherwise failure.
 */
static int WritePSKBinders(WOLFSSL* ssl, byte* output, word32 idx)
{
    int           ret;
    TLSX*         ext;
    PreSharedKey* current;
    byte          binderKey[WC_MAX_DIGEST_SIZE];
    word16        len;

    WOLFSSL_ENTER("WritePSKBinders");

    ext = TLSX_Find(ssl->extensions, TLSX_PRE_SHARED_KEY);
    if (ext == NULL)
        return SANITY_MSG_E;

    /* Get the size of the binders to determine where to write binders. */
    ret = TLSX_PreSharedKey_GetSizeBinders((PreSharedKey*)ext->data,
                                                            client_hello, &len);
    if (ret < 0)
        return ret;
    idx -= len;

    /* Hash truncated ClientHello - up to binders. */
    ret = HashOutput(ssl, output, idx, 0);
    if (ret != 0)
        return ret;

    current = (PreSharedKey*)ext->data;
    /* Calculate the binder for each identity based on previous handshake data.
     */
    while (current != NULL) {
        if ((ret = SetupPskKey(ssl, current)) != 0)
            return ret;

    #ifdef HAVE_SESSION_TICKET
        if (current->resumption)
            ret = DeriveBinderKeyResume(ssl, binderKey);
    #endif
    #ifndef NO_PSK
        if (!current->resumption)
            ret = DeriveBinderKey(ssl, binderKey);
    #endif
        if (ret != 0)
            return ret;

        /* Derive the Finished message secret. */
        ret = DeriveFinishedSecret(ssl, binderKey,
                                             ssl->keys.client_write_MAC_secret);
        if (ret != 0)
            return ret;

        /* Build the HMAC of the handshake message data = binder. */
        ret = BuildTls13HandshakeHmac(ssl, ssl->keys.client_write_MAC_secret,
            current->binder, &current->binderLen);
        if (ret != 0)
            return ret;

        current = current->next;
    }

    /* Data entered into extension, now write to message. */
    ret = TLSX_PreSharedKey_WriteBinders((PreSharedKey*)ext->data, output + idx,
                                                            client_hello, &len);
    if (ret < 0)
        return ret;

    /* Hash binders to complete the hash of the ClientHello. */
    ret = HashRaw(ssl, output + idx, len);
    if (ret < 0)
        return ret;

    #ifdef WOLFSSL_EARLY_DATA
    if (ssl->earlyData != no_early_data) {
        if ((ret = SetupPskKey(ssl, (PreSharedKey*)ext->data)) != 0)
            return ret;

        /* Derive early data encryption key. */
        ret = DeriveTls13Keys(ssl, early_data_key, ENCRYPT_SIDE_ONLY, 1);
        if (ret != 0)
            return ret;
        if ((ret = SetKeysSide(ssl, ENCRYPT_SIDE_ONLY)) != 0)
            return ret;
    }
    #endif

    WOLFSSL_LEAVE("WritePSKBinders", ret);

    return ret;
}
#endif

/* handle generation of TLS 1.3 client_hello (1) */
/* Send a ClientHello message to the server.
 * Include the information required to start a handshake with servers using
 * protocol versions less than TLS v1.3.
 * Only a client will send this message.
 *
 * ssl  The SSL/TLS object.
 * returns 0 on success and otherwise failure.
 */
int SendTls13ClientHello(WOLFSSL* ssl)
{
    byte*  output;
    word16 length;
    word32 idx = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
    int    sendSz;
    int    ret;

    WOLFSSL_START(WC_FUNC_CLIENT_HELLO_SEND);
    WOLFSSL_ENTER("SendTls13ClientHello");

#ifdef HAVE_SESSION_TICKET
    if (ssl->options.resuming &&
            (ssl->session.version.major != ssl->version.major ||
             ssl->session.version.minor != ssl->version.minor)) {
    #ifndef WOLFSSL_NO_TLS12
        if (ssl->session.version.major == ssl->version.major &&
            ssl->session.version.minor < ssl->version.minor) {
            /* Cannot resume with a different protocol version. */
            ssl->options.resuming = 0;
            ssl->version.major = ssl->session.version.major;
            ssl->version.minor = ssl->session.version.minor;
            return SendClientHello(ssl);
        }
        else
    #endif
            return VERSION_ERROR;
    }
#endif

    if (ssl->suites == NULL) {
        WOLFSSL_MSG("Bad suites pointer in SendTls13ClientHello");
        return SUITES_ERROR;
    }

    /* Version | Random | Session Id | Cipher Suites | Compression */
    length = VERSION_SZ + RAN_LEN + ENUM_LEN + ssl->suites->suiteSz +
             SUITE_LEN + COMP_LEN + ENUM_LEN;
    #if defined(WOLFSSL_TLS13_MIDDLEBOX_COMPAT)
    length += ID_LEN;
    #else
    if (ssl->session.sessionIDSz > 0)
        length += ssl->session.sessionIDSz;
    #endif

    /* Auto populate extensions supported unless user defined. */
    if ((ret = TLSX_PopulateExtensions(ssl, 0)) != 0)
        return ret;
#ifdef WOLFSSL_EARLY_DATA
    #ifndef NO_PSK
        if (!ssl->options.resuming &&
                                     ssl->options.client_psk_tls13_cb == NULL &&
                                     ssl->options.client_psk_cb == NULL)
    #else
        if (!ssl->options.resuming)
    #endif
            ssl->earlyData = no_early_data;
    if (ssl->options.serverState == SERVER_HELLO_RETRY_REQUEST_COMPLETE)
        ssl->earlyData = no_early_data;
    if (ssl->earlyData == no_early_data)
        TLSX_Remove(&ssl->extensions, TLSX_EARLY_DATA, ssl->heap);
    if (ssl->earlyData != no_early_data &&
                                       (ret = TLSX_EarlyData_Use(ssl, 0)) < 0) {
        return ret;
    }
#endif
    /* Include length of TLS extensions. */
    ret = TLSX_GetRequestSize(ssl, client_hello, &length);
    if (ret != 0)
        return ret;

    /* Total message size. */
    sendSz = length + HANDSHAKE_HEADER_SZ + RECORD_HEADER_SZ;

    /* Check buffers are big enough and grow if needed. */
    if ((ret = CheckAvailableSize(ssl, sendSz)) != 0)
        return ret;

    /* Get position in output buffer to write new message to. */
    output = ssl->buffers.outputBuffer.buffer +
             ssl->buffers.outputBuffer.length;

    /* Put the record and handshake headers on. */
    AddTls13Headers(output, length, client_hello, ssl);

    /* Protocol version - negotiation now in extension: supported_versions. */
    output[idx++] = SSLv3_MAJOR;
    output[idx++] = TLSv1_2_MINOR;
    /* Keep for downgrade. */
    ssl->chVersion = ssl->version;

    /* Client Random */
    if (ssl->options.connectState == CONNECT_BEGIN) {
        ret = wc_RNG_GenerateBlock(ssl->rng, output + idx, RAN_LEN);
        if (ret != 0)
            return ret;

        /* Store random for possible second ClientHello. */
        XMEMCPY(ssl->arrays->clientRandom, output + idx, RAN_LEN);
    }
    else
        XMEMCPY(output + idx, ssl->arrays->clientRandom, RAN_LEN);
    idx += RAN_LEN;

    if (ssl->session.sessionIDSz > 0) {
        /* Session resumption for old versions of protocol. */
        output[idx++] = ID_LEN;
        XMEMCPY(output + idx, ssl->session.sessionID, ssl->session.sessionIDSz);
        idx += ID_LEN;
    }
    else {
    #ifdef WOLFSSL_TLS13_MIDDLEBOX_COMPAT
        output[idx++] = ID_LEN;
        XMEMCPY(output + idx, ssl->arrays->clientRandom, ID_LEN);
        idx += ID_LEN;
    #else
        /* TLS v1.3 does not use session id - 0 length. */
        output[idx++] = 0;
    #endif /* WOLFSSL_TLS13_MIDDLEBOX_COMPAT */
    }

    /* Cipher suites */
    c16toa(ssl->suites->suiteSz, output + idx);
    idx += OPAQUE16_LEN;
    XMEMCPY(output + idx, &ssl->suites->suites, ssl->suites->suiteSz);
    idx += ssl->suites->suiteSz;

    /* Compression not supported in TLS v1.3. */
    output[idx++] = COMP_LEN;
    output[idx++] = NO_COMPRESSION;

    /* Write out extensions for a request. */
    length = 0;
    ret = TLSX_WriteRequest(ssl, output + idx, client_hello, &length);
    if (ret != 0)
        return ret;
    idx += length;

#if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
    /* Resumption has a specific set of extensions and binder is calculated
     * for each identity.
     */
    if (TLSX_Find(ssl->extensions, TLSX_PRE_SHARED_KEY))
        ret = WritePSKBinders(ssl, output, idx);
    else
#endif
        ret = HashOutput(ssl, output, idx, 0);
    if (ret != 0)
        return ret;

    ssl->options.clientState = CLIENT_HELLO_COMPLETE;

#ifdef WOLFSSL_CALLBACKS
    if (ssl->hsInfoOn) AddPacketName(ssl, "ClientHello");
    if (ssl->toInfoOn) {
        AddPacketInfo(ssl, "ClientHello", handshake, output, sendSz,
                      WRITE_PROTO, ssl->heap);
    }
#endif

    ssl->buffers.outputBuffer.length += sendSz;

#ifdef WOLFSSL_EARLY_DATA_GROUP
    if (ssl->earlyData == no_early_data)
#endif
        ret = SendBuffered(ssl);


    WOLFSSL_LEAVE("SendTls13ClientHello", ret);
    WOLFSSL_END(WC_FUNC_CLIENT_HELLO_SEND);

    return ret;
}

/* handle processing of TLS 1.3 server_hello (2) and hello_retry_request (6) */
/* Handle the ServerHello message from the server.
 * Only a client will receive this message.
 *
 * ssl       The SSL/TLS object.
 * input     The message buffer.
 * inOutIdx  On entry, the index into the message buffer of ServerHello.
 *           On exit, the index of byte after the ServerHello message.
 * helloSz   The length of the current handshake message.
 * returns 0 on success and otherwise failure.
 */
int DoTls13ServerHello(WOLFSSL* ssl, const byte* input, word32* inOutIdx,
                       word32 helloSz, byte* extMsgType)
{
    ProtocolVersion pv;
    word32          i = *inOutIdx;
    word32          begin = i;
    int             ret;
    byte            sessIdSz;
    const byte*     sessId;
    byte            b;
    int             foundVersion;
    word16          totalExtSz;
#if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
    TLSX*           ext;
    PreSharedKey*   psk = NULL;
#endif

    WOLFSSL_START(WC_FUNC_SERVER_HELLO_DO);
    WOLFSSL_ENTER("DoTls13ServerHello");

#ifdef WOLFSSL_CALLBACKS
    if (ssl->hsInfoOn) AddPacketName(ssl, "ServerHello");
    if (ssl->toInfoOn) AddLateName("ServerHello", &ssl->timeoutInfo);
#endif

    /* Protocol version length check. */
    if (OPAQUE16_LEN > helloSz)
        return BUFFER_ERROR;

    /* Protocol version */
    XMEMCPY(&pv, input + i, OPAQUE16_LEN);
    i += OPAQUE16_LEN;

#ifndef WOLFSSL_NO_TLS12
    if (pv.major == ssl->version.major  && pv.minor < TLSv1_2_MINOR &&
                                                       ssl->options.downgrade) {
        /* Force client hello version 1.2 to work for static RSA. */
        ssl->chVersion.minor = TLSv1_2_MINOR;
        ssl->version.minor = TLSv1_2_MINOR;
        return DoServerHello(ssl, input, inOutIdx, helloSz);
    }
#endif
    if (pv.major != ssl->version.major || pv.minor != TLSv1_2_MINOR)
        return VERSION_ERROR;

    /* Random and session id length check */
    if ((i - begin) + RAN_LEN + ENUM_LEN > helloSz)
        return BUFFER_ERROR;

    if (XMEMCMP(input + i, helloRetryRequestRandom, RAN_LEN) == 0)
        *extMsgType = hello_retry_request;

    /* Server random - keep for debugging. */
    XMEMCPY(ssl->arrays->serverRandom, input + i, RAN_LEN);
    i += RAN_LEN;

    /* Session id */
    sessIdSz = input[i++];
    if ((i - begin) + sessIdSz > helloSz)
        return BUFFER_ERROR;
    sessId = input + i;
    i += sessIdSz;

    ssl->options.haveSessionId = 1;

    /* Ciphersuite and compression check */
    if ((i - begin) + OPAQUE16_LEN + OPAQUE8_LEN > helloSz)
        return BUFFER_ERROR;

    /* Set the cipher suite from the message. */
    ssl->options.cipherSuite0 = input[i++];
    ssl->options.cipherSuite  = input[i++];

    /* Compression */
    b = input[i++];
    if (b != 0) {
        WOLFSSL_MSG("Must be no compression types in list");
        return INVALID_PARAMETER;
    }

    if ((i - begin) + OPAQUE16_LEN > helloSz) {
        if (!ssl->options.downgrade)
            return BUFFER_ERROR;
#ifndef WOLFSSL_NO_TLS12
        ssl->version.minor = TLSv1_2_MINOR;
#endif
        ssl->options.haveEMS = 0;
    }
    if ((i - begin) < helloSz) {
        /* Get extension length and length check. */
        if ((i - begin) + OPAQUE16_LEN > helloSz)
            return BUFFER_ERROR;
        ato16(&input[i], &totalExtSz);
        i += OPAQUE16_LEN;
        if ((i - begin) + totalExtSz > helloSz)
            return BUFFER_ERROR;

        /* Need to negotiate version first. */
        if ((ret = TLSX_ParseVersion(ssl, (byte*)input + i, totalExtSz,
                                                 *extMsgType, &foundVersion))) {
            return ret;
        }
        if (!foundVersion) {
            if (!ssl->options.downgrade) {
                WOLFSSL_MSG("Server trying to downgrade to version less than "
                            "TLS v1.3");
                return VERSION_ERROR;
            }

            if (pv.minor < ssl->options.minDowngrade)
                return VERSION_ERROR;
            ssl->version.minor = pv.minor;
        }

        /* Parse and handle extensions. */
        ret = TLSX_Parse(ssl, (byte *) input + i, totalExtSz, *extMsgType,
                                                                          NULL);
        if (ret != 0)
            return ret;

        i += totalExtSz;
    }
    *inOutIdx = i;

    ssl->options.serverState = SERVER_HELLO_COMPLETE;

#ifdef HAVE_SECRET_CALLBACK
    if (ssl->sessionSecretCb != NULL) {
        int secretSz = SECRET_LEN;
        ret = ssl->sessionSecretCb(ssl, ssl->session.masterSecret,
                                   &secretSz, ssl->sessionSecretCtx);
        if (ret != 0 || secretSz != SECRET_LEN) {
            return SESSION_SECRET_CB_E;
        }
    }
#endif /* HAVE_SECRET_CALLBACK */

    /* Version only negotiated in extensions for TLS v1.3.
     * Only now do we know how to deal with session id.
     */
    if (!IsAtLeastTLSv1_3(ssl->version)) {
#ifndef WOLFSSL_NO_TLS12
        ssl->arrays->sessionIDSz = sessIdSz;

        if (ssl->arrays->sessionIDSz > ID_LEN) {
            WOLFSSL_MSG("Invalid session ID size");
            ssl->arrays->sessionIDSz = 0;
            return BUFFER_ERROR;
        }
        else if (ssl->arrays->sessionIDSz) {
            XMEMCPY(ssl->arrays->sessionID, sessId, ssl->arrays->sessionIDSz);
            ssl->options.haveSessionId = 1;
        }

        /* Force client hello version 1.2 to work for static RSA. */
        ssl->chVersion.minor = TLSv1_2_MINOR;
        /* Complete TLS v1.2 processing of ServerHello. */
        ret = CompleteServerHello(ssl);
#else
        WOLFSSL_MSG("Client using higher version, fatal error");
        ret = VERSION_ERROR;
#endif

        WOLFSSL_LEAVE("DoTls13ServerHello", ret);

        return ret;
    }

    #ifdef WOLFSSL_TLS13_MIDDLEBOX_COMPAT
    if (sessIdSz == 0)
        return INVALID_PARAMETER;
    if (ssl->session.sessionIDSz != 0) {
        if (ssl->session.sessionIDSz != sessIdSz ||
                   XMEMCMP(ssl->session.sessionID, sessId, sessIdSz) != 0) {
            return INVALID_PARAMETER;
        }
    }
    else if (XMEMCMP(ssl->arrays->clientRandom, sessId, sessIdSz) != 0)
        return INVALID_PARAMETER;
    #else
    if (sessIdSz != ssl->session.sessionIDSz || (sessIdSz > 0 &&
                  XMEMCMP(ssl->session.sessionID, sessId, sessIdSz) != 0)) {
        WOLFSSL_MSG("Server sent different session id");
        return INVALID_PARAMETER;
    }
    #endif /* WOLFSSL_TLS13_MIDDLEBOX_COMPAT */

    ret = SetCipherSpecs(ssl);
    if (ret != 0)
        return ret;
#ifdef HAVE_NULL_CIPHER
    if (ssl->options.cipherSuite0 == ECC_BYTE &&
                              (ssl->options.cipherSuite == TLS_SHA256_SHA256 ||
                               ssl->options.cipherSuite == TLS_SHA384_SHA384)) {
        ;
    }
    else
#endif
    /* Check that the negotiated ciphersuite matches protocol version. */
    if (ssl->options.cipherSuite0 != TLS13_BYTE) {
        WOLFSSL_MSG("Server sent non-TLS13 cipher suite in TLS 1.3 packet");
        return INVALID_PARAMETER;
    }

#if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
    if (*extMsgType == server_hello) {
        ext = TLSX_Find(ssl->extensions, TLSX_PRE_SHARED_KEY);
        if (ext != NULL)
            psk = (PreSharedKey*)ext->data;
        while (psk != NULL && !psk->chosen)
            psk = psk->next;
        if (psk == NULL) {
            ssl->options.resuming = 0;
            ssl->arrays->psk_keySz = 0;
            XMEMSET(ssl->arrays->psk_key, 0, MAX_PSK_KEY_LEN);
        }
        else if ((ret = SetupPskKey(ssl, psk)) != 0)
            return ret;
    }
#endif

    if (*extMsgType == server_hello) {
        ssl->keys.encryptionOn = 1;
        ssl->options.serverState = SERVER_HELLO_COMPLETE;
    }
    else {
        ssl->options.tls1_3 = 1;
        ssl->options.serverState = SERVER_HELLO_RETRY_REQUEST_COMPLETE;

        ret = RestartHandshakeHash(ssl);
    }

    WOLFSSL_LEAVE("DoTls13ServerHello", ret);
    WOLFSSL_END(WC_FUNC_SERVER_HELLO_DO);

    return ret;
}

/* handle processing TLS 1.3 encrypted_extensions (8) */
/* Parse and handle an EncryptedExtensions message.
 * Only a client will receive this message.
 *
 * ssl       The SSL/TLS object.
 * input     The message buffer.
 * inOutIdx  On entry, the index into the message buffer of
 *           EncryptedExtensions.
 *           On exit, the index of byte after the EncryptedExtensions
 *           message.
 * totalSz   The length of the current handshake message.
 * returns 0 on success and otherwise failure.
 */
static int DoTls13EncryptedExtensions(WOLFSSL* ssl, const byte* input,
                                      word32* inOutIdx, word32 totalSz)
{
    int    ret;
    word32 begin = *inOutIdx;
    word32 i = begin;
    word16 totalExtSz;

    WOLFSSL_START(WC_FUNC_ENCRYPTED_EXTENSIONS_DO);
    WOLFSSL_ENTER("DoTls13EncryptedExtensions");

#ifdef WOLFSSL_CALLBACKS
    if (ssl->hsInfoOn) AddPacketName(ssl, "EncryptedExtensions");
    if (ssl->toInfoOn) AddLateName("EncryptedExtensions", &ssl->timeoutInfo);
#endif

    /* Length field of extension data. */
    if (totalSz < i - begin + OPAQUE16_LEN)
        return BUFFER_ERROR;
    ato16(&input[i], &totalExtSz);
    i += OPAQUE16_LEN;

    /* Extension data. */
    if (i - begin + totalExtSz > totalSz)
        return BUFFER_ERROR;
    if ((ret = TLSX_Parse(ssl, (byte *)(input + i), totalExtSz,
                          encrypted_extensions, NULL)))
        return ret;

    /* Move index to byte after message. */
    *inOutIdx = i + totalExtSz;

    /* Always encrypted. */
    *inOutIdx += ssl->keys.padSz;

#ifdef WOLFSSL_EARLY_DATA
    if (ssl->earlyData != no_early_data) {
        TLSX* ext = TLSX_Find(ssl->extensions, TLSX_EARLY_DATA);
        if (ext == NULL || !ext->val)
            ssl->earlyData = no_early_data;
    }
#endif

#ifdef WOLFSSL_EARLY_DATA
    if (ssl->earlyData == no_early_data) {
        ret = SetKeysSide(ssl, ENCRYPT_SIDE_ONLY);
        if (ret != 0)
            return ret;
    }
#endif

    ssl->options.serverState = SERVER_ENCRYPTED_EXTENSIONS_COMPLETE;

    WOLFSSL_LEAVE("DoTls13EncryptedExtensions", ret);
    WOLFSSL_END(WC_FUNC_ENCRYPTED_EXTENSIONS_DO);

    return ret;
}

#ifndef NO_CERTS
/* handle processing TLS v1.3 certificate_request (13) */
/* Handle a TLS v1.3 CertificateRequest message.
 * This message is always encrypted.
 * Only a client will receive this message.
 *
 * ssl       The SSL/TLS object.
 * input     The message buffer.
 * inOutIdx  On entry, the index into the message buffer of CertificateRequest.
 *           On exit, the index of byte after the CertificateRequest message.
 * size      The length of the current handshake message.
 * returns 0 on success and otherwise failure.
 */
static int DoTls13CertificateRequest(WOLFSSL* ssl, const byte* input,
                                     word32* inOutIdx, word32 size)
{
    word16      len;
    word32      begin = *inOutIdx;
    int         ret = 0;
    Suites      peerSuites;
#ifdef WOLFSSL_POST_HANDSHAKE_AUTH
    CertReqCtx* certReqCtx;
#endif

    WOLFSSL_START(WC_FUNC_CERTIFICATE_REQUEST_DO);
    WOLFSSL_ENTER("DoTls13CertificateRequest");

    XMEMSET(&peerSuites, 0, sizeof(Suites));

#ifdef WOLFSSL_CALLBACKS
    if (ssl->hsInfoOn) AddPacketName(ssl, "CertificateRequest");
    if (ssl->toInfoOn) AddLateName("CertificateRequest", &ssl->timeoutInfo);
#endif

    if ((*inOutIdx - begin) + OPAQUE8_LEN > size)
        return BUFFER_ERROR;

    /* Length of the request context. */
    len = input[(*inOutIdx)++];
    if ((*inOutIdx - begin) + len > size)
        return BUFFER_ERROR;
    if (ssl->options.connectState < FINISHED_DONE && len > 0)
        return BUFFER_ERROR;

#ifdef WOLFSSL_POST_HANDSHAKE_AUTH
    /* CertReqCtx has one byte at end for context value.
     * Increase size to handle other implementations sending more than one byte.
     * That is, allocate extra space, over one byte, to hold the context value.
     */
    certReqCtx = (CertReqCtx*)XMALLOC(sizeof(CertReqCtx) + len - 1, ssl->heap,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (certReqCtx == NULL)
        return MEMORY_E;
    certReqCtx->next = ssl->certReqCtx;
    certReqCtx->len = len;
    XMEMCPY(&certReqCtx->ctx, input + *inOutIdx, len);
    ssl->certReqCtx = certReqCtx;
#endif
    *inOutIdx += len;

    /* TODO: Add support for more extensions:
     *   signed_certificate_timestamp, certificate_authorities, oid_filters.
     */
    /* Certificate extensions */
    if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
        return BUFFER_ERROR;
    ato16(input + *inOutIdx, &len);
    *inOutIdx += OPAQUE16_LEN;
    if ((*inOutIdx - begin) + len > size)
        return BUFFER_ERROR;
    if (len == 0)
        return INVALID_PARAMETER;
    if ((ret = TLSX_Parse(ssl, (byte *)(input + *inOutIdx), len,
                                           certificate_request, &peerSuites))) {
        return ret;
    }
    *inOutIdx += len;

    if (ssl->buffers.certificate && ssl->buffers.certificate->buffer &&
        ((ssl->buffers.key && ssl->buffers.key->buffer)
        #ifdef HAVE_PK_CALLBACKS
            || wolfSSL_CTX_IsPrivatePkSet(ssl->ctx)
        #endif
    )) {
        if (PickHashSigAlgo(ssl, peerSuites.hashSigAlgo,
                                               peerSuites.hashSigAlgoSz) != 0) {
            return INVALID_PARAMETER;
        }
        ssl->options.sendVerify = SEND_CERT;
    }
    else {
#ifndef WOLFSSL_NO_CLIENT_CERT_ERROR
        ssl->options.sendVerify = SEND_BLANK_CERT;
#else
        WOLFSSL_MSG("Certificate required but none set on client");
        SendAlert(ssl, alert_fatal, illegal_parameter);
        return NO_CERT_ERROR;
#endif
    }

    /* This message is always encrypted so add encryption padding. */
    *inOutIdx += ssl->keys.padSz;

    WOLFSSL_LEAVE("DoTls13CertificateRequest", ret);
    WOLFSSL_END(WC_FUNC_CERTIFICATE_REQUEST_DO);

    return ret;
}
#endif /* !NO_CERTS */
#endif /* !NO_WOLFSSL_CLIENT */

#ifndef NO_WOLFSSL_SERVER
#if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
/* Refine list of supported cipher suites to those common to server and client.
 *
 * ssl         SSL/TLS object.
 * peerSuites  The peer's advertised list of supported cipher suites.
 */
static void RefineSuites(WOLFSSL* ssl, Suites* peerSuites)
{
    byte suites[WOLFSSL_MAX_SUITE_SZ];
    int suiteSz = 0;
    word16 i, j;

    XMEMSET(suites, 0, WOLFSSL_MAX_SUITE_SZ);

    for (i = 0; i < ssl->suites->suiteSz; i += 2) {
        for (j = 0; j < peerSuites->suiteSz; j += 2) {
            if (ssl->suites->suites[i+0] == peerSuites->suites[j+0] &&
                ssl->suites->suites[i+1] == peerSuites->suites[j+1]) {
                suites[suiteSz++] = peerSuites->suites[j+0];
                suites[suiteSz++] = peerSuites->suites[j+1];
            }
        }
    }

    ssl->suites->suiteSz = suiteSz;
    XMEMCPY(ssl->suites->suites, &suites, sizeof(suites));
}

/* Handle any Pre-Shared Key (PSK) extension.
 * Must do this in ClientHello as it requires a hash of the truncated message.
 * Don't know size of binders until Pre-Shared Key extension has been parsed.
 *
 * ssl       The SSL/TLS object.
 * input     The ClientHello message.
 * helloSz   The size of the ClientHello message (including binders if present).
 * usingPSK  Indicates handshake is using Pre-Shared Keys.
 * returns 0 on success and otherwise failure.
 */
static int DoPreSharedKeys(WOLFSSL* ssl, const byte* input, word32 helloSz,
                           int* usingPSK)
{
    int           ret;
    TLSX*         ext;
    word16        bindersLen;
    PreSharedKey* current;
    byte          binderKey[WC_MAX_DIGEST_SIZE];
    byte          binder[WC_MAX_DIGEST_SIZE];
    word32        binderLen;
    word16        modes;
    byte          suite[2];
#ifdef WOLFSSL_EARLY_DATA
    int           pskCnt = 0;
    TLSX*         extEarlyData;
#endif
#ifndef NO_PSK
    const char*   cipherName = NULL;
    byte          cipherSuite0 = TLS13_BYTE;
    byte          cipherSuite  = WOLFSSL_DEF_PSK_CIPHER;
#endif

    WOLFSSL_ENTER("DoPreSharedKeys");

    ext = TLSX_Find(ssl->extensions, TLSX_PRE_SHARED_KEY);
    if (ext == NULL) {
        /* Hash data up to binders for deriving binders in PSK extension. */
        ret = HashInput(ssl, input,  helloSz);
        return ret;
    }

    /* Extensions pushed on stack/list and PSK must be last. */
    if (ssl->extensions != ext)
        return PSK_KEY_ERROR;

    /* Assume we are going to resume with a pre-shared key. */
    ssl->options.resuming = 1;

    /* Find the pre-shared key extension and calculate hash of truncated
     * ClientHello for binders.
     */
    ret = TLSX_PreSharedKey_GetSizeBinders((PreSharedKey*)ext->data,
                                                     client_hello, &bindersLen);
    if (ret < 0)
        return ret;

    /* Hash data up to binders for deriving binders in PSK extension. */
    ret = HashInput(ssl, input,  helloSz - bindersLen);
    if (ret != 0)
        return ret;

    /* Look through all client's pre-shared keys for a match. */
    current = (PreSharedKey*)ext->data;
    while (current != NULL) {
    #ifdef WOLFSSL_EARLY_DATA
        pskCnt++;
    #endif

    #ifndef NO_PSK
        if (current->identityLen > MAX_PSK_ID_LEN) {
            return BUFFER_ERROR;
        }
        XMEMCPY(ssl->arrays->client_identity, current->identity,
                current->identityLen);
        ssl->arrays->client_identity[current->identityLen] = '\0';
    #endif

    #ifdef HAVE_SESSION_TICKET
        /* Decode the identity. */
        if ((ret = DoClientTicket(ssl, current->identity, current->identityLen))
                                                     == WOLFSSL_TICKET_RET_OK) {
            word32 now;
            int    diff;

            now = TimeNowInMilliseconds();
            if (now == (word32)GETTIME_ERROR)
                return now;
            diff = now - ssl->session.ticketSeen;
            diff -= current->ticketAge - ssl->session.ticketAdd;
            /* Check session and ticket age timeout.
             * Allow +/- 1000 milliseconds on ticket age.
             */
            if (diff > (int)ssl->timeout * 1000 || diff < -1000 ||
                                     diff - MAX_TICKET_AGE_SECS * 1000 > 1000) {
                /* Invalid difference, fallback to full handshake. */
                ssl->options.resuming = 0;
                break;
            }

            /* Check whether resumption is possible based on suites in SSL and
             * ciphersuite in ticket.
             */
            suite[0] = ssl->session.cipherSuite0;
            suite[1] = ssl->session.cipherSuite;
            if (!FindSuiteSSL(ssl, suite)) {
                current = current->next;
                continue;
            }

        #ifdef WOLFSSL_EARLY_DATA
            ssl->options.maxEarlyDataSz = ssl->session.maxEarlyDataSz;
        #endif
            /* Use the same cipher suite as before and set up for use. */
            ssl->options.cipherSuite0   = ssl->session.cipherSuite0;
            ssl->options.cipherSuite    = ssl->session.cipherSuite;
            ret = SetCipherSpecs(ssl);
            if (ret != 0)
                return ret;

            /* Resumption PSK is resumption master secret. */
            ssl->arrays->psk_keySz = ssl->specs.hash_size;
            if ((ret = DeriveResumptionPSK(ssl, ssl->session.ticketNonce.data,
                    ssl->session.ticketNonce.len, ssl->arrays->psk_key)) != 0) {
                return ret;
            }

            /* Derive the early secret using the PSK. */
            ret = DeriveEarlySecret(ssl);
            if (ret != 0)
                return ret;
            /* Derive the binder key to use to with HMAC. */
            ret = DeriveBinderKeyResume(ssl, binderKey);
            if (ret != 0)
                return ret;
        }
        else
    #endif
    #ifndef NO_PSK
        if ((ssl->options.server_psk_tls13_cb != NULL &&
             (ssl->arrays->psk_keySz = ssl->options.server_psk_tls13_cb(ssl,
                             ssl->arrays->client_identity, ssl->arrays->psk_key,
                             MAX_PSK_KEY_LEN, &cipherName)) != 0 &&
             GetCipherSuiteFromName(cipherName, &cipherSuite0,
                                                          &cipherSuite) == 0) ||
            (ssl->options.server_psk_cb != NULL &&
             (ssl->arrays->psk_keySz = ssl->options.server_psk_cb(ssl,
                             ssl->arrays->client_identity, ssl->arrays->psk_key,
                             MAX_PSK_KEY_LEN)) != 0)) {
            if (ssl->arrays->psk_keySz > MAX_PSK_KEY_LEN)
                return PSK_KEY_ERROR;

            /* Check whether PSK ciphersuite is in SSL. */
            suite[0] = cipherSuite0;
            suite[1] = cipherSuite;
            if (!FindSuiteSSL(ssl, suite)) {
                current = current->next;
                continue;
            }

            /* Default to ciphersuite if cb doesn't specify. */
            ssl->options.resuming = 0;
            /* Don't send certificate request when using PSK. */
            ssl->options.verifyPeer = 0;

            /* PSK age is always zero. */
            if (current->ticketAge != ssl->session.ticketAdd)
                return PSK_KEY_ERROR;

            /* Set PSK ciphersuite into SSL. */
            ssl->options.cipherSuite0 = cipherSuite0;
            ssl->options.cipherSuite  = cipherSuite;
            ret = SetCipherSpecs(ssl);
            if (ret != 0)
                return ret;

            /* Derive the early secret using the PSK. */
            ret = DeriveEarlySecret(ssl);
            if (ret != 0)
                return ret;
            /* Derive the binder key to use to with HMAC. */
            ret = DeriveBinderKey(ssl, binderKey);
            if (ret != 0)
                return ret;
        }
        else
    #endif
        {
            current = current->next;
            continue;
        }

        ssl->options.sendVerify = 0;

        /* Derive the Finished message secret. */
        ret = DeriveFinishedSecret(ssl, binderKey,
                                             ssl->keys.client_write_MAC_secret);
        if (ret != 0)
            return ret;

        /* Derive the binder and compare with the one in the extension. */
        ret = BuildTls13HandshakeHmac(ssl,
                         ssl->keys.client_write_MAC_secret, binder, &binderLen);
        if (ret != 0)
            return ret;
        if (binderLen != current->binderLen ||
                             XMEMCMP(binder, current->binder, binderLen) != 0) {
            return BAD_BINDER;
        }

        /* This PSK works, no need to try any more. */
        current->chosen = 1;
        ext->resp = 1;
        break;
    }

    /* Hash the rest of the ClientHello. */
    ret = HashRaw(ssl, input + helloSz - bindersLen, bindersLen);
    if (ret != 0)
        return ret;

    if (current == NULL) {
#ifdef WOLFSSL_PSK_ID_PROTECTION
    #ifndef NO_CERTS
        if (ssl->buffers.certChainCnt != 0)
            return 0;
    #endif
        return BAD_BINDER;
#else
        return 0;
#endif
    }

#ifdef WOLFSSL_EARLY_DATA
    extEarlyData = TLSX_Find(ssl->extensions, TLSX_EARLY_DATA);
    if (extEarlyData != NULL) {
        if (ssl->earlyData != no_early_data && current == ext->data) {
            extEarlyData->resp = 1;

            /* Derive early data decryption key. */
            ret = DeriveTls13Keys(ssl, early_data_key, DECRYPT_SIDE_ONLY, 1);
            if (ret != 0)
                return ret;
            if ((ret = SetKeysSide(ssl, DECRYPT_SIDE_ONLY)) != 0)
                return ret;

            ssl->earlyData = process_early_data;
        }
        else
            extEarlyData->resp = 0;
    }
#endif

    /* Get the PSK key exchange modes the client wants to negotiate. */
    ext = TLSX_Find(ssl->extensions, TLSX_PSK_KEY_EXCHANGE_MODES);
    if (ext == NULL)
        return MISSING_HANDSHAKE_DATA;
    modes = ext->val;

    ext = TLSX_Find(ssl->extensions, TLSX_KEY_SHARE);
    /* Use (EC)DHE for forward-security if possible. */
    if ((modes & (1 << PSK_DHE_KE)) != 0 && !ssl->options.noPskDheKe &&
                                                                  ext != NULL) {
        /* Only use named group used in last session. */
        ssl->namedGroup = ssl->session.namedGroup;

        /* Pick key share and Generate a new key if not present. */
        ret = TLSX_KeyShare_Establish(ssl);
        if (ret == KEY_SHARE_ERROR) {
            ssl->options.serverState = SERVER_HELLO_RETRY_REQUEST_COMPLETE;
            ret = 0;
        }
        else if (ret < 0)
            return ret;

        /* Send new public key to client. */
        ext->resp = 1;
    }
    else {
        if ((modes & (1 << PSK_KE)) == 0)
            return PSK_KEY_ERROR;
        ssl->options.noPskDheKe = 1;
        ssl->arrays->preMasterSz = 0;
    }

    *usingPSK = 1;

    WOLFSSL_LEAVE("DoPreSharedKeys", ret);

    return ret;
}
#endif

#if defined(WOLFSSL_SEND_HRR_COOKIE)
/* Check that the Cookie data's integrity.
 *
 * ssl       SSL/TLS object.
 * cookie    The cookie data - hash and MAC.
 * cookieSz  The length of the cookie data in bytes.
 * returns Length of the hash on success, otherwise failure.
 */
static int CheckCookie(WOLFSSL* ssl, byte* cookie, byte cookieSz)
{
    int  ret;
    byte mac[WC_MAX_DIGEST_SIZE] = {0};
    Hmac cookieHmac;
    byte cookieType = 0;
    byte macSz = 0;

#if !defined(NO_SHA) && defined(NO_SHA256)
    cookieType = SHA;
    macSz = WC_SHA_DIGEST_SIZE;
#endif /* NO_SHA */
#ifndef NO_SHA256
    cookieType = WC_SHA256;
    macSz = WC_SHA256_DIGEST_SIZE;
#endif /* NO_SHA256 */

    if (cookieSz < ssl->specs.hash_size + macSz)
        return HRR_COOKIE_ERROR;
    cookieSz -= macSz;
    XMEMSET(&cookieHmac, 0, sizeof(Hmac));

    ret = wc_HmacSetKey(&cookieHmac, cookieType,
                        ssl->buffers.tls13CookieSecret.buffer,
                        ssl->buffers.tls13CookieSecret.length);
    if (ret != 0)
        return ret;
    if ((ret = wc_HmacUpdate(&cookieHmac, cookie, cookieSz)) != 0)
        return ret;
    if ((ret = wc_HmacFinal(&cookieHmac, mac)) != 0)
        return ret;

    if (ConstantCompare(cookie + cookieSz, mac, macSz) != 0)
        return HRR_COOKIE_ERROR;
    return cookieSz;
}

/* Length of the KeyShare Extension */
#define HRR_KEY_SHARE_SZ   (OPAQUE16_LEN + OPAQUE16_LEN + OPAQUE16_LEN)
/* Length of the Supported Vresions Extension */
#define HRR_VERSIONS_SZ    (OPAQUE16_LEN + OPAQUE16_LEN + OPAQUE16_LEN)
/* Length of the Cookie Extension excluding cookie data */
#define HRR_COOKIE_HDR_SZ  (OPAQUE16_LEN + OPAQUE16_LEN + OPAQUE16_LEN)
/* PV | Random | Session Id | CipherSuite | Compression | Ext Len */
#define HRR_BODY_SZ        (VERSION_SZ + RAN_LEN + ENUM_LEN + ID_LEN + \
                            SUITE_LEN + COMP_LEN + OPAQUE16_LEN)
/* HH | PV | CipherSuite | Ext Len | Key Share | Supported Version | Cookie */
#define MAX_HRR_SZ   (HANDSHAKE_HEADER_SZ   + \
                        HRR_BODY_SZ         + \
                          HRR_KEY_SHARE_SZ  + \
                          HRR_VERSIONS_SZ   + \
                          HRR_COOKIE_HDR_SZ)


/* Restart the handshake hash from the cookie value.
 *
 * ssl     SSL/TLS object.
 * cookie  Cookie data from client.
 * returns 0 on success, otherwise failure.
 */
static int RestartHandshakeHashWithCookie(WOLFSSL* ssl, Cookie* cookie)
{
    byte   header[HANDSHAKE_HEADER_SZ] = {0};
    byte   hrr[MAX_HRR_SZ] = {0};
    int    hrrIdx;
    word32 idx;
    byte   hashSz;
    byte*  cookieData;
    byte   cookieDataSz;
    word16 length;
    int    keyShareExt = 0;
    int    ret;

    cookieDataSz = ret = CheckCookie(ssl, &cookie->data, cookie->len);
    if (ret < 0)
        return ret;
    hashSz = cookie->data;
    cookieData = &cookie->data;
    idx = OPAQUE8_LEN;

    /* Restart handshake hash with synthetic message hash. */
    AddTls13HandShakeHeader(header, hashSz, 0, 0, message_hash, ssl);
    if ((ret = InitHandshakeHashes(ssl)) != 0)
        return ret;
    if ((ret = HashRaw(ssl, header, sizeof(header))) != 0)
        return ret;
    if ((ret = HashRaw(ssl, cookieData + idx, hashSz)) != 0)
        return ret;

    /* Reconstruct the HelloRetryMessage for handshake hash. */
    length = HRR_BODY_SZ - ID_LEN + ssl->session.sessionIDSz +
             HRR_COOKIE_HDR_SZ + cookie->len;
    length += HRR_VERSIONS_SZ;
    if (cookieDataSz > hashSz + OPAQUE16_LEN) {
        keyShareExt = 1;
        length += HRR_KEY_SHARE_SZ;
    }

    AddTls13HandShakeHeader(hrr, length, 0, 0, server_hello, ssl);

    idx += hashSz;
    hrrIdx = HANDSHAKE_HEADER_SZ;

    /* The negotiated protocol version. */
    hrr[hrrIdx++] = ssl->version.major;
    hrr[hrrIdx++] = TLSv1_2_MINOR;

    /* HelloRetryRequest message has fixed value for random. */
    XMEMCPY(hrr + hrrIdx, helloRetryRequestRandom, RAN_LEN);
    hrrIdx += RAN_LEN;

    hrr[hrrIdx++] = ssl->session.sessionIDSz;
    if (ssl->session.sessionIDSz > 0) {
        XMEMCPY(hrr + hrrIdx, ssl->session.sessionID, ssl->session.sessionIDSz);
        hrrIdx += ssl->session.sessionIDSz;
    }

    /* Cipher Suite */
    hrr[hrrIdx++] = cookieData[idx++];
    hrr[hrrIdx++] = cookieData[idx++];

    /* Compression not supported in TLS v1.3. */
    hrr[hrrIdx++] = 0;

    /* Extensions' length */
    length -= HRR_BODY_SZ - ID_LEN + ssl->session.sessionIDSz;
    c16toa(length, hrr + hrrIdx);
    hrrIdx += 2;

    /* Optional KeyShare Extension */
    if (keyShareExt) {
        c16toa(TLSX_KEY_SHARE, hrr + hrrIdx);
        hrrIdx += 2;
        c16toa(OPAQUE16_LEN, hrr + hrrIdx);
        hrrIdx += 2;
        hrr[hrrIdx++] = cookieData[idx++];
        hrr[hrrIdx++] = cookieData[idx++];
    }
    c16toa(TLSX_SUPPORTED_VERSIONS, hrr + hrrIdx);
    hrrIdx += 2;
    c16toa(OPAQUE16_LEN, hrr + hrrIdx);
    hrrIdx += 2;
    #ifdef WOLFSSL_TLS13_DRAFT
        hrr[hrrIdx++] = TLS_DRAFT_MAJOR;
        hrr[hrrIdx++] = TLS_DRAFT_MINOR;
    #else
        hrr[hrrIdx++] = ssl->version.major;
        hrr[hrrIdx++] = ssl->version.minor;
    #endif

    /* Mandatory Cookie Extension */
    c16toa(TLSX_COOKIE, hrr + hrrIdx);
    hrrIdx += 2;
    c16toa(cookie->len + OPAQUE16_LEN, hrr + hrrIdx);
    hrrIdx += 2;
    c16toa(cookie->len, hrr + hrrIdx);
    hrrIdx += 2;

#ifdef WOLFSSL_DEBUG_TLS
    WOLFSSL_MSG("Reconstucted HelloRetryRequest");
    WOLFSSL_BUFFER(hrr, hrrIdx);
    WOLFSSL_MSG("Cookie");
    WOLFSSL_BUFFER(cookieData, cookie->len);
#endif

    if ((ret = HashRaw(ssl, hrr, hrrIdx)) != 0)
        return ret;
    return HashRaw(ssl, cookieData, cookie->len);
}
#endif

/* Do SupportedVersion extension for TLS v1.3+ otherwise it is not.
 *
 * ssl       The SSL/TLS object.
 * input     The message buffer.
 * i         The index into the message buffer of ClientHello.
 * helloSz   The length of the current handshake message.
 * returns 0 on success and otherwise failure.
 */
static int DoTls13SupportedVersions(WOLFSSL* ssl, const byte* input, word32 i,
                                    word32 helloSz, int* wantDowngrade)
{
    int    ret;
    byte   b;
    word16 suiteSz;
    word16 totalExtSz;
    int    foundVersion = 0;

    /* Client random */
    i += RAN_LEN;
    /* Session id - not used in TLS v1.3 */
    b = input[i++];
    if (i + b > helloSz) {
        return BUFFER_ERROR;
    }
    i += b;
    /* Cipher suites */
    if (i + OPAQUE16_LEN > helloSz)
        return BUFFER_ERROR;
    ato16(input + i, &suiteSz);
    i += OPAQUE16_LEN;
    if (i + suiteSz + 1 > helloSz)
        return BUFFER_ERROR;
    i += suiteSz;
    /* Compression */
    b = input[i++];
    if (i + b > helloSz)
        return BUFFER_ERROR;
    i += b;

    /* TLS 1.3 must have extensions */
    if (i < helloSz) {
        if (i + OPAQUE16_LEN > helloSz)
            return BUFFER_ERROR;
        ato16(&input[i], &totalExtSz);
        i += OPAQUE16_LEN;
        if (totalExtSz != helloSz - i)
            return BUFFER_ERROR;

        /* Need to negotiate version first. */
        if ((ret = TLSX_ParseVersion(ssl, (byte*)input + i, totalExtSz,
                                                client_hello, &foundVersion))) {
            return ret;
        }
    }
    *wantDowngrade = !foundVersion || !IsAtLeastTLSv1_3(ssl->version);

    return 0;
}

/* Handle a ClientHello handshake message.
 * If the protocol version in the message is not TLS v1.3 or higher, use
 * DoClientHello()
 * Only a server will receive this message.
 *
 * ssl       The SSL/TLS object.
 * input     The message buffer.
 * inOutIdx  On entry, the index into the message buffer of ClientHello.
 *           On exit, the index of byte after the ClientHello message and
 *           padding.
 * helloSz   The length of the current handshake message.
 * returns 0 on success and otherwise failure.
 */
int DoTls13ClientHello(WOLFSSL* ssl, const byte* input, word32* inOutIdx,
                       word32 helloSz)
{
    int             ret = VERSION_ERROR;
    byte            b = 0;
    ProtocolVersion pv;
    Suites          clSuites;
    word32          i = *inOutIdx;
    word32          begin = i;
    word16          totalExtSz = 0;
    int             usingPSK = 0;
    byte            sessIdSz = 0;
    int             wantDowngrade = 0;

    WOLFSSL_START(WC_FUNC_CLIENT_HELLO_DO);
    WOLFSSL_ENTER("DoTls13ClientHello");

    XMEMSET(&pv, 0, sizeof(ProtocolVersion));
    XMEMSET(&clSuites, 0, sizeof(Suites));

#ifdef WOLFSSL_CALLBACKS
    if (ssl->hsInfoOn) AddPacketName(ssl, "ClientHello");
    if (ssl->toInfoOn) AddLateName("ClientHello", &ssl->timeoutInfo);
#endif

    /* protocol version, random and session id length check */
    if ((i - begin) + OPAQUE16_LEN + RAN_LEN + OPAQUE8_LEN > helloSz)
        return BUFFER_ERROR;

    /* Protocol version */
    XMEMCPY(&pv, input + i, OPAQUE16_LEN);
    ssl->chVersion = pv;   /* store */
    i += OPAQUE16_LEN;
    if (pv.major < SSLv3_MAJOR) {
        WOLFSSL_MSG("Legacy version field contains unsupported value");
 #ifdef WOLFSSL_MYSQL_COMPATIBLE
        SendAlert(ssl, alert_fatal, wc_protocol_version);
 #else
        SendAlert(ssl, alert_fatal, protocol_version);
 #endif
        return INVALID_PARAMETER;
    }
    /* Legacy protocol version cannot negotiate TLS 1.3 or higher. */
    if (pv.major > SSLv3_MAJOR || (pv.major == SSLv3_MAJOR &&
                                                   pv.minor >= TLSv1_3_MINOR)) {
        pv.major = SSLv3_MAJOR;
        pv.minor = TLSv1_2_MINOR;
        wantDowngrade = 1;
        ssl->version.minor = pv.minor;
    }
    /* Legacy version must be [ SSLv3_MAJOR, TLSv1_2_MINOR ] for TLS v1.3 */
    else if (pv.major == SSLv3_MAJOR && pv.minor < TLSv1_2_MINOR) {
        wantDowngrade = 1;
        ssl->version.minor = pv.minor;
    }
    else {
        ret = DoTls13SupportedVersions(ssl, input + begin, i - begin, helloSz,
                                                                &wantDowngrade);
        if (ret < 0)
            return ret;
    }
    if (wantDowngrade) {
#ifndef WOLFSSL_NO_TLS12
        if (!ssl->options.downgrade) {
            WOLFSSL_MSG("Client trying to connect with lesser version than "
                        "TLS v1.3");
            return VERSION_ERROR;
        }

        if (pv.minor < ssl->options.minDowngrade)
            return VERSION_ERROR;

        if ((ret = HashInput(ssl, input + begin, helloSz)) != 0)
            return ret;
        return DoClientHello(ssl, input, inOutIdx, helloSz);
#else
        WOLFSSL_MSG("Client trying to connect with lesser version than "
                    "TLS v1.3");
        return VERSION_ERROR;
#endif
    }

    /* Client random */
    XMEMCPY(ssl->arrays->clientRandom, input + i, RAN_LEN);
    i += RAN_LEN;

#ifdef WOLFSSL_DEBUG_TLS
    WOLFSSL_MSG("client random");
    WOLFSSL_BUFFER(ssl->arrays->clientRandom, RAN_LEN);
#endif

    sessIdSz = input[i++];
    if (sessIdSz != ID_LEN && sessIdSz != 0)
        return INVALID_PARAMETER;

    if (sessIdSz + i > helloSz) {
        return BUFFER_ERROR;
    }

    ssl->session.sessionIDSz = sessIdSz;
    if (sessIdSz == ID_LEN) {
        XMEMCPY(ssl->session.sessionID, input + i, sessIdSz);
        i += ID_LEN;
    }

    /* Cipher suites */
    if ((i - begin) + OPAQUE16_LEN > helloSz)
        return BUFFER_ERROR;
    ato16(&input[i], &clSuites.suiteSz);
    i += OPAQUE16_LEN;
    /* suites and compression length check */
    if ((i - begin) + clSuites.suiteSz + OPAQUE8_LEN > helloSz)
        return BUFFER_ERROR;
    if (clSuites.suiteSz > WOLFSSL_MAX_SUITE_SZ)
        return BUFFER_ERROR;
    XMEMCPY(clSuites.suites, input + i, clSuites.suiteSz);
    i += clSuites.suiteSz;
    clSuites.hashSigAlgoSz = 0;

#ifdef HAVE_SERVER_RENEGOTIATION_INFO
    ret = FindSuite(&clSuites, 0, TLS_EMPTY_RENEGOTIATION_INFO_SCSV);
    if (ret == SUITES_ERROR)
        return BUFFER_ERROR;
    if (ret >= 0) {
        TLSX* extension;

        /* check for TLS_EMPTY_RENEGOTIATION_INFO_SCSV suite */
        ret = TLSX_AddEmptyRenegotiationInfo(&ssl->extensions, ssl->heap);
        if (ret != WOLFSSL_SUCCESS)
            return ret;

        extension = TLSX_Find(ssl->extensions, TLSX_RENEGOTIATION_INFO);
        if (extension) {
            ssl->secure_renegotiation = (SecureRenegotiation*)extension->data;
            ssl->secure_renegotiation->enabled = 1;
        }
    }
#endif /* HAVE_SERVER_RENEGOTIATION_INFO */

    /* Compression */
    b = input[i++];
    if ((i - begin) + b > helloSz)
        return BUFFER_ERROR;
    if (b != COMP_LEN) {
        WOLFSSL_MSG("Must be one compression type in list");
        return INVALID_PARAMETER;
    }
    b = input[i++];
    if (b != NO_COMPRESSION) {
        WOLFSSL_MSG("Must be no compression type in list");
        return INVALID_PARAMETER;
    }

    /* Extensions */
    if ((i - begin) == helloSz)
        return BUFFER_ERROR;
    if ((i - begin) + OPAQUE16_LEN > helloSz)
        return BUFFER_ERROR;

    ato16(&input[i], &totalExtSz);
    i += OPAQUE16_LEN;
    if ((i - begin) + totalExtSz > helloSz)
        return BUFFER_ERROR;

    /* Auto populate extensions supported unless user defined. */
    if ((ret = TLSX_PopulateExtensions(ssl, 1)) != 0)
        return ret;

    /* Parse extensions */
    if ((ret = TLSX_Parse(ssl, (byte*)input + i, totalExtSz, client_hello,
                                                                  &clSuites))) {
        return ret;
    }

#if defined(OPENSSL_ALL) || defined(HAVE_STUNNEL) || defined(WOLFSSL_NGINX) || \
                                                        defined(WOLFSSL_HAPROXY)
        if ((ret = SNI_Callback(ssl)) != 0)
            return ret;
        ssl->options.side = WOLFSSL_SERVER_END;
#endif /* OPENSSL_ALL || HAVE_STUNNEL || WOLFSSL_NGINX || WOLFSSL_HAPROXY */

    i += totalExtSz;
    *inOutIdx = i;

    ssl->options.sendVerify = SEND_CERT;

    ssl->options.clientState = CLIENT_HELLO_COMPLETE;
    ssl->options.haveSessionId = 1;

#if defined(WOLFSSL_SEND_HRR_COOKIE)
    if (ssl->options.sendCookie &&
              ssl->options.serverState == SERVER_HELLO_RETRY_REQUEST_COMPLETE) {
        TLSX* ext;

        if ((ext = TLSX_Find(ssl->extensions, TLSX_COOKIE)) == NULL)
            return HRR_COOKIE_ERROR;
        /* Ensure the cookie came from client and isn't the one in the
         * response - HelloRetryRequest.
         */
        if (ext->resp == 1)
            return HRR_COOKIE_ERROR;
        ret = RestartHandshakeHashWithCookie(ssl, (Cookie*)ext->data);
        if (ret != 0)
            return ret;
    }
#endif

#if (defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)) && \
     defined(HAVE_TLS_EXTENSIONS)
    if (TLSX_Find(ssl->extensions, TLSX_PRE_SHARED_KEY) != NULL) {
        /* Refine list for PSK processing. */
        RefineSuites(ssl, &clSuites);

        /* Process the Pre-Shared Key extension if present. */
        ret = DoPreSharedKeys(ssl, input + begin, helloSz, &usingPSK);
        if (ret != 0)
            return ret;
    }
    else
#endif
    {
#ifdef WOLFSSL_EARLY_DATA
        ssl->earlyData = no_early_data;
#endif
        if ((ret = HashInput(ssl, input + begin, helloSz)) != 0)
            return ret;

    }

    if (!usingPSK) {
        if (TLSX_Find(ssl->extensions, TLSX_KEY_SHARE) == NULL) {
            WOLFSSL_MSG("Client did not send a KeyShare extension");
            SendAlert(ssl, alert_fatal, missing_extension);
            return INCOMPLETE_DATA;
        }
        if (TLSX_Find(ssl->extensions, TLSX_SIGNATURE_ALGORITHMS) == NULL) {
            WOLFSSL_MSG("Client did not send a SignatureAlgorithms extension");
            SendAlert(ssl, alert_fatal, missing_extension);
            return INCOMPLETE_DATA;
        }

        if ((ret = MatchSuite(ssl, &clSuites)) < 0) {
            WOLFSSL_MSG("Unsupported cipher suite, ClientHello");
            SendAlert(ssl, alert_fatal, handshake_failure);
            return ret;
        }

#ifdef HAVE_NULL_CIPHER
        if (ssl->options.cipherSuite0 == ECC_BYTE &&
                              (ssl->options.cipherSuite == TLS_SHA256_SHA256 ||
                               ssl->options.cipherSuite == TLS_SHA384_SHA384)) {
            ;
        }
        else
#endif
        /* Check that the negotiated ciphersuite matches protocol version. */
        if (ssl->options.cipherSuite0 != TLS13_BYTE) {
            WOLFSSL_MSG("Negotiated ciphersuite from lesser version than "
                        "TLS v1.3");
            SendAlert(ssl, alert_fatal, handshake_failure);
            return VERSION_ERROR;
        }

#ifdef HAVE_SESSION_TICKET
        if (ssl->options.resuming) {
            ssl->options.resuming = 0;
            XMEMSET(ssl->arrays->psk_key, 0, ssl->specs.hash_size);
        }
#endif

        /* Derive early secret for handshake secret. */
        if ((ret = DeriveEarlySecret(ssl)) != 0)
            return ret;
    }

    WOLFSSL_LEAVE("DoTls13ClientHello", ret);
    WOLFSSL_END(WC_FUNC_CLIENT_HELLO_DO);

    return ret;
}

/* Send TLS v1.3 ServerHello message to client.
 * Only a server will send this message.
 *
 * ssl  The SSL/TLS object.
 * returns 0 on success, otherwise failure.
 */
/* handle generation of TLS 1.3 server_hello (2) */
int SendTls13ServerHello(WOLFSSL* ssl, byte extMsgType)
{
    int    ret;
    byte*  output;
    word16 length;
    word32 idx = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
    int    sendSz;

    WOLFSSL_START(WC_FUNC_SERVER_HELLO_SEND);
    WOLFSSL_ENTER("SendTls13ServerHello");

    if (extMsgType == hello_retry_request) {
        WOLFSSL_MSG("wolfSSL Doing HelloRetryRequest");
        if ((ret = RestartHandshakeHash(ssl)) < 0)
            return ret;
    }

    /* Protocol version, server random, session id, cipher suite, compression
     * and extensions.
     */
    length = VERSION_SZ + RAN_LEN + ENUM_LEN + ssl->session.sessionIDSz +
             SUITE_LEN + COMP_LEN;
    ret = TLSX_GetResponseSize(ssl, extMsgType, &length);
    if (ret != 0)
        return ret;
    sendSz = idx + length;

    /* Check buffers are big enough and grow if needed. */
    if ((ret = CheckAvailableSize(ssl, sendSz)) != 0)
        return ret;

    /* Get position in output buffer to write new message to. */
    output = ssl->buffers.outputBuffer.buffer +
             ssl->buffers.outputBuffer.length;

    /* Put the record and handshake headers on. */
    AddTls13Headers(output, length, server_hello, ssl);

    /* The protocol version must be TLS v1.2 for middleboxes. */
    output[idx++] = ssl->version.major;
    output[idx++] = TLSv1_2_MINOR;

    if (extMsgType == server_hello) {
        /* Generate server random. */
        if ((ret = wc_RNG_GenerateBlock(ssl->rng, output + idx, RAN_LEN)) != 0)
            return ret;
    }
    else {
        /* HelloRetryRequest message has fixed value for random. */
        XMEMCPY(output + idx, helloRetryRequestRandom, RAN_LEN);
    }

    /* Store in SSL for debugging. */
    XMEMCPY(ssl->arrays->serverRandom, output + idx, RAN_LEN);
    idx += RAN_LEN;

#ifdef WOLFSSL_DEBUG_TLS
    WOLFSSL_MSG("Server random");
    WOLFSSL_BUFFER(ssl->arrays->serverRandom, RAN_LEN);
#endif

    output[idx++] = ssl->session.sessionIDSz;
    if (ssl->session.sessionIDSz > 0) {
        XMEMCPY(output + idx, ssl->session.sessionID, ssl->session.sessionIDSz);
        idx += ssl->session.sessionIDSz;
    }

    /* Chosen cipher suite */
    output[idx++] = ssl->options.cipherSuite0;
    output[idx++] = ssl->options.cipherSuite;

    /* Compression not supported in TLS v1.3. */
    output[idx++] = 0;

    /* Extensions */
    ret = TLSX_WriteResponse(ssl, output + idx, extMsgType, NULL);
    if (ret != 0)
        return ret;

    ssl->buffers.outputBuffer.length += sendSz;

    if ((ret = HashOutput(ssl, output, sendSz, 0)) != 0)
        return ret;

    #ifdef WOLFSSL_CALLBACKS
    if (ssl->hsInfoOn)
        AddPacketName(ssl, "ServerHello");
    if (ssl->toInfoOn) {
        AddPacketInfo(ssl, "ServerHello", handshake, output, sendSz,
                      WRITE_PROTO, ssl->heap);
    }
    #endif

    if (extMsgType == server_hello)
        ssl->options.serverState = SERVER_HELLO_COMPLETE;

    if (!ssl->options.groupMessages || extMsgType != server_hello)

        ret = SendBuffered(ssl);

    WOLFSSL_LEAVE("SendTls13ServerHello", ret);
    WOLFSSL_END(WC_FUNC_SERVER_HELLO_SEND);

    return ret;
}

/* handle generation of TLS 1.3 encrypted_extensions (8) */
/* Send the rest of the extensions encrypted under the handshake key.
 * This message is always encrypted in TLS v1.3.
 * Only a server will send this message.
 *
 * ssl  The SSL/TLS object.
 * returns 0 on success, otherwise failure.
 */
static int SendTls13EncryptedExtensions(WOLFSSL* ssl)
{
    int    ret;
    byte*  output;
    word16 length = 0;
    word32 idx = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
    int    sendSz;

    WOLFSSL_START(WC_FUNC_ENCRYPTED_EXTENSIONS_SEND);
    WOLFSSL_ENTER("SendTls13EncryptedExtensions");

    ssl->keys.encryptionOn = 1;

#if defined(HAVE_SUPPORTED_CURVES) && !defined(WOLFSSL_NO_SERVER_GROUPS_EXT)
    if ((ret = TLSX_SupportedCurve_CheckPriority(ssl)) != 0)
        return ret;
#endif

    /* Derive the handshake secret now that we are at first message to be
     * encrypted under the keys.
     */
    if ((ret = DeriveHandshakeSecret(ssl)) != 0)
        return ret;
    if ((ret = DeriveTls13Keys(ssl, handshake_key,
                               ENCRYPT_AND_DECRYPT_SIDE, 1)) != 0)
        return ret;

    /* Setup encrypt/decrypt keys for following messages. */
#ifdef WOLFSSL_EARLY_DATA
    if ((ret = SetKeysSide(ssl, ENCRYPT_SIDE_ONLY)) != 0)
        return ret;
    if (ssl->earlyData != process_early_data) {
        if ((ret = SetKeysSide(ssl, DECRYPT_SIDE_ONLY)) != 0)
            return ret;
    }
#else
    if ((ret = SetKeysSide(ssl, ENCRYPT_AND_DECRYPT_SIDE)) != 0)
        return ret;
#endif

    ret = TLSX_GetResponseSize(ssl, encrypted_extensions, &length);
    if (ret != 0)
        return ret;

    sendSz = idx + length;
    /* Encryption always on. */
    sendSz += MAX_MSG_EXTRA;

    /* Check buffers are big enough and grow if needed. */
    ret = CheckAvailableSize(ssl, sendSz);
    if (ret != 0)
        return ret;

    /* Get position in output buffer to write new message to. */
    output = ssl->buffers.outputBuffer.buffer +
             ssl->buffers.outputBuffer.length;

    /* Put the record and handshake headers on. */
    AddTls13Headers(output, length, encrypted_extensions, ssl);

    ret = TLSX_WriteResponse(ssl, output + idx, encrypted_extensions, NULL);
    if (ret != 0)
        return ret;
    idx += length;

#ifdef WOLFSSL_CALLBACKS
    if (ssl->hsInfoOn)
        AddPacketName(ssl, "EncryptedExtensions");
    if (ssl->toInfoOn) {
        AddPacketInfo(ssl, "EncryptedExtensions", handshake, output,
                      sendSz, WRITE_PROTO, ssl->heap);
    }
#endif

    /* This handshake message is always encrypted. */
    sendSz = BuildTls13Message(ssl, output, sendSz, output + RECORD_HEADER_SZ,
                               idx - RECORD_HEADER_SZ, handshake, 1, 0, 0);
    if (sendSz < 0)
        return sendSz;

    ssl->buffers.outputBuffer.length += sendSz;

    ssl->options.serverState = SERVER_ENCRYPTED_EXTENSIONS_COMPLETE;

    if (!ssl->options.groupMessages)
        ret = SendBuffered(ssl);

    WOLFSSL_LEAVE("SendTls13EncryptedExtensions", ret);
    WOLFSSL_END(WC_FUNC_ENCRYPTED_EXTENSIONS_SEND);

    return ret;
}

#ifndef NO_CERTS
/* handle generation TLS v1.3 certificate_request (13) */
/* Send the TLS v1.3 CertificateRequest message.
 * This message is always encrypted in TLS v1.3.
 * Only a server will send this message.
 *
 * ssl        SSL/TLS object.
 * reqCtx     Request context.
 * reqCtxLen  Length of context. 0 when sending as part of handshake.
 * returns 0 on success, otherwise failure.
 */
static int SendTls13CertificateRequest(WOLFSSL* ssl, byte* reqCtx,
                                       int reqCtxLen)
{
    byte*   output;
    int    ret;
    int    sendSz;
    word32 i;
    word16 reqSz;
    TLSX*  ext;

    WOLFSSL_START(WC_FUNC_CERTIFICATE_REQUEST_SEND);
    WOLFSSL_ENTER("SendTls13CertificateRequest");

    if (ssl->options.side == WOLFSSL_SERVER_END)
        InitSuitesHashSigAlgo(ssl->suites, 1, 1, 0, 1, ssl->buffers.keySz);

    ext = TLSX_Find(ssl->extensions, TLSX_SIGNATURE_ALGORITHMS);
    if (ext == NULL)
        return EXT_MISSING;
    ext->resp = 0;

    i = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
    reqSz = (word16)(OPAQUE8_LEN + reqCtxLen);
    ret = TLSX_GetRequestSize(ssl, certificate_request, &reqSz);
    if (ret != 0)
        return ret;

    sendSz = i + reqSz;
    /* Always encrypted and make room for padding. */
    sendSz += MAX_MSG_EXTRA;

    /* Check buffers are big enough and grow if needed. */
    if ((ret = CheckAvailableSize(ssl, sendSz)) != 0)
        return ret;

    /* Get position in output buffer to write new message to. */
    output = ssl->buffers.outputBuffer.buffer +
             ssl->buffers.outputBuffer.length;

    /* Put the record and handshake headers on. */
    AddTls13Headers(output, reqSz, certificate_request, ssl);

    /* Certificate request context. */
    output[i++] = (byte)reqCtxLen;
    if (reqCtxLen != 0) {
        XMEMCPY(output + i, reqCtx, reqCtxLen);
        i += reqCtxLen;
    }

    /* Certificate extensions. */
    reqSz = 0;
    ret = TLSX_WriteRequest(ssl, output + i, certificate_request, &reqSz);
    if (ret != 0)
        return ret;
    i += reqSz;

    /* Always encrypted. */
    sendSz = BuildTls13Message(ssl, output, sendSz, output + RECORD_HEADER_SZ,
                               i - RECORD_HEADER_SZ, handshake, 1, 0, 0);
    if (sendSz < 0)
        return sendSz;

    #ifdef WOLFSSL_CALLBACKS
        if (ssl->hsInfoOn)
            AddPacketName(ssl, "CertificateRequest");
        if (ssl->toInfoOn) {
            AddPacketInfo(ssl, "CertificateRequest", handshake, output,
                          sendSz, WRITE_PROTO, ssl->heap);
        }
    #endif

    ssl->buffers.outputBuffer.length += sendSz;
    if (!ssl->options.groupMessages)
        ret = SendBuffered(ssl);

    WOLFSSL_LEAVE("SendTls13CertificateRequest", ret);
    WOLFSSL_END(WC_FUNC_CERTIFICATE_REQUEST_SEND);

    return ret;
}
#endif /* NO_CERTS */
#endif /* NO_WOLFSSL_SERVER */

#ifndef NO_CERTS
#if !defined(NO_RSA) || defined(HAVE_ECC) || defined(HAVE_ED25519) || \
                                                             defined(HAVE_ED448)
/* Encode the signature algorithm into buffer.
 *
 * hashalgo  The hash algorithm.
 * hsType   The signature type.
 * output    The buffer to encode into.
 */
static WC_INLINE void EncodeSigAlg(byte hashAlgo, byte hsType, byte* output)
{
    switch (hsType) {
#ifdef HAVE_ECC
        case ecc_dsa_sa_algo:
            output[0] = hashAlgo;
            output[1] = ecc_dsa_sa_algo;
            break;
#endif
#ifdef HAVE_ED25519
        /* ED25519: 0x0807 */
        case ed25519_sa_algo:
            output[0] = ED25519_SA_MAJOR;
            output[1] = ED25519_SA_MINOR;
            (void)hashAlgo;
            break;
#endif
#ifdef HAVE_ED448
        /* ED448: 0x0808 */
        case ed448_sa_algo:
            output[0] = ED448_SA_MAJOR;
            output[1] = ED448_SA_MINOR;
            (void)hashAlgo;
            break;
#endif
#ifndef NO_RSA
        /* PSS signatures: 0x080[4-6] */
        case rsa_pss_sa_algo:
            output[0] = rsa_pss_sa_algo;
            output[1] = hashAlgo;
            break;
#endif
    }
}

/* Decode the signature algorithm.
 *
 * input     The encoded signature algorithm.
 * hashalgo  The hash algorithm.
 * hsType    The signature type.
 * returns INVALID_PARAMETER if not recognized and 0 otherwise.
 */
static WC_INLINE int DecodeTls13SigAlg(byte* input, byte* hashAlgo,
                                       byte* hsType)
{
    int ret = 0;

    switch (input[0]) {
        case NEW_SA_MAJOR:
            /* PSS signatures: 0x080[4-6] */
            if (input[1] >= sha256_mac && input[1] <= sha512_mac) {
                *hsType   = input[0];
                *hashAlgo = input[1];
            }
    #ifdef HAVE_ED25519
            /* ED25519: 0x0807 */
            else if (input[1] == ED25519_SA_MINOR) {
                *hsType = ed25519_sa_algo;
                /* Hash performed as part of sign/verify operation. */
                *hashAlgo = sha512_mac;
            }
    #endif
    #ifdef HAVE_ED448
            /* ED448: 0x0808 */
            else if (input[1] == ED448_SA_MINOR) {
                *hsType = ed448_sa_algo;
                /* Hash performed as part of sign/verify operation. */
                *hashAlgo = sha512_mac;
            }
    #endif
            else
                ret = INVALID_PARAMETER;
            break;
        default:
            *hashAlgo = input[0];
            *hsType   = input[1];
            break;
    }

    return ret;
}

/* Get the hash of the messages so far.
 *
 * ssl   The SSL/TLS object.
 * hash  The buffer to write the hash to.
 * returns the length of the hash.
 */
static WC_INLINE int GetMsgHash(WOLFSSL* ssl, byte* hash)
{
    int ret = 0;
    switch (ssl->specs.mac_algorithm) {
    #ifndef NO_SHA256
        case sha256_mac:
            ret = wc_Sha256GetHash(&ssl->hsHashes->hashSha256, hash);
            if (ret == 0)
                ret = WC_SHA256_DIGEST_SIZE;
            break;
    #endif /* !NO_SHA256 */
    #ifdef WOLFSSL_SHA384
        case sha384_mac:
            ret = wc_Sha384GetHash(&ssl->hsHashes->hashSha384, hash);
            if (ret == 0)
                ret = WC_SHA384_DIGEST_SIZE;
            break;
    #endif /* WOLFSSL_SHA384 */
    #ifdef WOLFSSL_TLS13_SHA512
        case sha512_mac:
            ret = wc_Sha512GetHash(&ssl->hsHashes->hashSha512, hash);
            if (ret == 0)
                ret = WC_SHA512_DIGEST_SIZE;
            break;
    #endif /* WOLFSSL_TLS13_SHA512 */
    }
    return ret;
}

/* The length of the certificate verification label - client and server. */
#define CERT_VFY_LABEL_SZ    34
/* The server certificate verification label. */
static const byte serverCertVfyLabel[CERT_VFY_LABEL_SZ] =
    "TLS 1.3, server CertificateVerify";
/* The client certificate verification label. */
static const byte clientCertVfyLabel[CERT_VFY_LABEL_SZ] =
    "TLS 1.3, client CertificateVerify";

/* The number of prefix bytes for signature data. */
#define SIGNING_DATA_PREFIX_SZ     64
/* The prefix byte in the signature data. */
#define SIGNING_DATA_PREFIX_BYTE   0x20
/* Maximum length of the signature data. */
#define MAX_SIG_DATA_SZ            (SIGNING_DATA_PREFIX_SZ + \
                                    CERT_VFY_LABEL_SZ      + \
                                    WC_MAX_DIGEST_SIZE)

/* Create the signature data for TLS v1.3 certificate verification.
 *
 * ssl        The SSL/TLS object.
 * sigData    The signature data.
 * sigDataSz  The length of the signature data.
 * check      Indicates this is a check not create.
 */
static int CreateSigData(WOLFSSL* ssl, byte* sigData, word16* sigDataSz,
                          int check)
{
    word16 idx;
    int side = ssl->options.side;
    int ret;

    /* Signature Data = Prefix | Label | Handshake Hash */
    XMEMSET(sigData, SIGNING_DATA_PREFIX_BYTE, SIGNING_DATA_PREFIX_SZ);
    idx = SIGNING_DATA_PREFIX_SZ;

    if ((side == WOLFSSL_SERVER_END && check) ||
        (side == WOLFSSL_CLIENT_END && !check)) {
        XMEMCPY(&sigData[idx], clientCertVfyLabel, CERT_VFY_LABEL_SZ);
    }
    if ((side == WOLFSSL_CLIENT_END && check) ||
        (side == WOLFSSL_SERVER_END && !check)) {
        XMEMCPY(&sigData[idx], serverCertVfyLabel, CERT_VFY_LABEL_SZ);
    }
    idx += CERT_VFY_LABEL_SZ;

    ret = GetMsgHash(ssl, &sigData[idx]);
    if (ret < 0)
        return ret;

    *sigDataSz = (word16)(idx + ret);
    ret = 0;

    return ret;
}

#ifndef NO_RSA
/* Encode the PKCS #1.5 RSA signature.
 *
 * sig        The buffer to place the encoded signature into.
 * sigData    The data to be signed.
 * sigDataSz  The size of the data to be signed.
 * hashAlgo   The hash algorithm to use when signing.
 * returns the length of the encoded signature or negative on error.
 */
static int CreateRSAEncodedSig(byte* sig, byte* sigData, int sigDataSz,
                               int sigAlgo, int hashAlgo)
{
    Digest digest;
    int    hashSz = 0;
    int    ret = BAD_FUNC_ARG;
    byte*  hash;

    (void)sigAlgo;

    hash = sig;

    /* Digest the signature data. */
    switch (hashAlgo) {
#ifndef NO_WOLFSSL_SHA256
        case sha256_mac:
            ret = wc_InitSha256(&digest.sha256);
            if (ret == 0) {
                ret = wc_Sha256Update(&digest.sha256, sigData, sigDataSz);
                if (ret == 0)
                    ret = wc_Sha256Final(&digest.sha256, hash);
                wc_Sha256Free(&digest.sha256);
            }
            hashSz = WC_SHA256_DIGEST_SIZE;
            break;
#endif
#ifdef WOLFSSL_SHA384
        case sha384_mac:
            ret = wc_InitSha384(&digest.sha384);
            if (ret == 0) {
                ret = wc_Sha384Update(&digest.sha384, sigData, sigDataSz);
                if (ret == 0)
                    ret = wc_Sha384Final(&digest.sha384, hash);
                wc_Sha384Free(&digest.sha384);
            }
            hashSz = WC_SHA384_DIGEST_SIZE;
            break;
#endif
#ifdef WOLFSSL_SHA512
        case sha512_mac:
            ret = wc_InitSha512(&digest.sha512);
            if (ret == 0) {
                ret = wc_Sha512Update(&digest.sha512, sigData, sigDataSz);
                if (ret == 0)
                    ret = wc_Sha512Final(&digest.sha512, hash);
                wc_Sha512Free(&digest.sha512);
            }
            hashSz = WC_SHA512_DIGEST_SIZE;
            break;
#endif
    }

    if (ret != 0)
        return ret;

    return hashSz;
}
#endif /* !NO_RSA */

#ifdef HAVE_ECC
/* Encode the ECC signature.
 *
 * sigData    The data to be signed.
 * sigDataSz  The size of the data to be signed.
 * hashAlgo   The hash algorithm to use when signing.
 * returns the length of the encoded signature or negative on error.
 */
static int CreateECCEncodedSig(byte* sigData, int sigDataSz, int hashAlgo)
{
    Digest digest;
    int    hashSz = 0;
    int    ret = BAD_FUNC_ARG;

    /* Digest the signature data. */
    switch (hashAlgo) {
#ifndef NO_WOLFSSL_SHA256
        case sha256_mac:
            ret = wc_InitSha256(&digest.sha256);
            if (ret == 0) {
                ret = wc_Sha256Update(&digest.sha256, sigData, sigDataSz);
                if (ret == 0)
                    ret = wc_Sha256Final(&digest.sha256, sigData);
                wc_Sha256Free(&digest.sha256);
            }
            hashSz = WC_SHA256_DIGEST_SIZE;
            break;
#endif
#ifdef WOLFSSL_SHA384
        case sha384_mac:
            ret = wc_InitSha384(&digest.sha384);
            if (ret == 0) {
                ret = wc_Sha384Update(&digest.sha384, sigData, sigDataSz);
                if (ret == 0)
                    ret = wc_Sha384Final(&digest.sha384, sigData);
                wc_Sha384Free(&digest.sha384);
            }
            hashSz = WC_SHA384_DIGEST_SIZE;
            break;
#endif
#ifdef WOLFSSL_SHA512
        case sha512_mac:
            ret = wc_InitSha512(&digest.sha512);
            if (ret == 0) {
                ret = wc_Sha512Update(&digest.sha512, sigData, sigDataSz);
                if (ret == 0)
                    ret = wc_Sha512Final(&digest.sha512, sigData);
                wc_Sha512Free(&digest.sha512);
            }
            hashSz = WC_SHA512_DIGEST_SIZE;
            break;
#endif
    }

    if (ret != 0)
        return ret;

    return hashSz;
}
#endif /* HAVE_ECC */

#if !defined(NO_RSA) && defined(WC_RSA_PSS)
/* Check that the decrypted signature matches the encoded signature
 * based on the digest of the signature data.
 *
 * ssl       The SSL/TLS object.
 * sigAlgo   The signature algorithm used to generate signature.
 * hashAlgo  The hash algorithm used to generate signature.
 * decSig    The decrypted signature.
 * decSigSz  The size of the decrypted signature.
 * returns 0 on success, otherwise failure.
 */
static int CheckRSASignature(WOLFSSL* ssl, int sigAlgo, int hashAlgo,
                             byte* decSig, word32 decSigSz)
{
    int    ret = 0;
    byte   sigData[MAX_SIG_DATA_SZ];
    word16 sigDataSz;
    word32 sigSz;

    ret = CreateSigData(ssl, sigData, &sigDataSz, 1);
    if (ret != 0)
        return ret;

    if (sigAlgo == rsa_pss_sa_algo) {
        enum wc_HashType hashType = WC_HASH_TYPE_NONE;

        ret = ConvertHashPss(hashAlgo, &hashType, NULL);
        if (ret < 0)
            return ret;

        /* PSS signature can be done in-place */
        ret = CreateRSAEncodedSig(sigData, sigData, sigDataSz,
                                  sigAlgo, hashAlgo);
        if (ret < 0)
            return ret;
        sigSz = ret;

        ret = wc_RsaPSS_CheckPadding(sigData, sigSz, decSig, decSigSz,
                                     hashType);
    }

    return ret;
}
#endif /* !NO_RSA && WC_RSA_PSS */
#endif /* !NO_RSA || HAVE_ECC */

/* Get the next certificate from the list for writing into the TLS v1.3
 * Certificate message.
 *
 * data    The certificate list.
 * length  The length of the certificate data in the list.
 * idx     The index of the next certificate.
 * returns the length of the certificate data. 0 indicates no more certificates
 * in the list.
 */
static word32 NextCert(byte* data, word32 length, word32* idx)
{
    word32 len;

    /* Is index at end of list. */
    if (*idx == length)
        return 0;

    /* Length of the current ASN.1 encoded certificate. */
    c24to32(data + *idx, &len);
    /* Include the length field. */
    len += 3;

    /* Move index to next certificate and return the current certificate's
     * length.
     */
    *idx += len;
    return len;
}

/* Add certificate data and empty extension to output up to the fragment size.
 *
 * ssl     SSL/TLS object.
 * cert    The certificate data to write out.
 * len     The length of the certificate data.
 * extSz   Length of the extension data with the certificate.
 * idx     The start of the certificate data to write out.
 * fragSz  The maximum size of this fragment.
 * output  The buffer to write to.
 * returns the number of bytes written.
 */
static word32 AddCertExt(WOLFSSL* ssl, byte* cert, word32 len, word16 extSz,
                         word32 idx, word32 fragSz, byte* output)
{
    word32 i = 0;
    word32 copySz = min(len - idx, fragSz);

    if (idx < len) {
        XMEMCPY(output, cert + idx, copySz);
        i = copySz;
        if (copySz == fragSz)
            return i;
    }
    copySz = len + extSz - idx - i;

    if (extSz == OPAQUE16_LEN) {
        if (copySz <= fragSz) {
            /* Empty extension */
            output[i++] = 0;
            output[i++] = 0;
        }
    }
    else {
        byte* certExts = ssl->buffers.certExts->buffer + idx + i - len;
        /* Put out as much of the extensions' data as will fit in fragment. */
        if (copySz > fragSz - i)
            copySz = fragSz - i;
        XMEMCPY(output + i, certExts, copySz);
        i += copySz;
    }

    return i;
}

/* handle generation TLS v1.3 certificate (11) */
/* Send the certificate for this end and any CAs that help with validation.
 * This message is always encrypted in TLS v1.3.
 *
 * ssl  The SSL/TLS object.
 * returns 0 on success, otherwise failure.
 */
static int SendTls13Certificate(WOLFSSL* ssl)
{
    int    ret = 0;
    word32 certSz, certChainSz, headerSz, listSz, payloadSz;
    word16 extSz = 0;
    word32 length, maxFragment;
    word32 len = 0;
    word32 idx = 0;
    word32 offset = OPAQUE16_LEN;
    byte*  p = NULL;
    byte   certReqCtxLen = 0;
    byte*  certReqCtx = NULL;

    WOLFSSL_START(WC_FUNC_CERTIFICATE_SEND);
    WOLFSSL_ENTER("SendTls13Certificate");

#ifdef WOLFSSL_POST_HANDSHAKE_AUTH
    if (ssl->options.side == WOLFSSL_CLIENT_END && ssl->certReqCtx != NULL) {
        certReqCtxLen = ssl->certReqCtx->len;
        certReqCtx = &ssl->certReqCtx->ctx;
    }
#endif

    if (ssl->options.sendVerify == SEND_BLANK_CERT) {
        certSz = 0;
        certChainSz = 0;
        headerSz = OPAQUE8_LEN + certReqCtxLen + CERT_HEADER_SZ;
        length = headerSz;
        listSz = 0;
    }
    else {
        if (!ssl->buffers.certificate) {
            WOLFSSL_MSG("Send Cert missing certificate buffer");
            return BUFFER_ERROR;
        }
        /* Certificate Data */
        certSz = ssl->buffers.certificate->length;
        /* Cert Req Ctx Len | Cert Req Ctx | Cert List Len | Cert Data Len */
        headerSz = OPAQUE8_LEN + certReqCtxLen + CERT_HEADER_SZ +
                   CERT_HEADER_SZ;

        ret = TLSX_GetResponseSize(ssl, certificate, &extSz);
        if (ret < 0)
            return ret;

        /* Create extensions' data if none already present. */
        if (extSz > OPAQUE16_LEN && ssl->buffers.certExts == NULL) {
            ret = AllocDer(&ssl->buffers.certExts, extSz, CERT_TYPE, ssl->heap);
            if (ret < 0)
                return ret;

            extSz = 0;
            ret = TLSX_WriteResponse(ssl, ssl->buffers.certExts->buffer,
                                                           certificate, &extSz);
            if (ret < 0)
                return ret;
        }

        /* Length of message data with one certificate and extensions. */
        length = headerSz + certSz + extSz;
        /* Length of list data with one certificate and extensions. */
        listSz = CERT_HEADER_SZ + certSz + extSz;

        /* Send rest of chain if sending cert (chain has leading size/s). */
        if (certSz > 0 && ssl->buffers.certChainCnt > 0) {
            p = ssl->buffers.certChain->buffer;
            /* Chain length including extensions. */
            certChainSz = ssl->buffers.certChain->length +
                          OPAQUE16_LEN * ssl->buffers.certChainCnt;
            length += certChainSz;
            listSz += certChainSz;
        }
        else
            certChainSz = 0;
    }

    payloadSz = length;

    if (ssl->fragOffset != 0)
        length -= (ssl->fragOffset + headerSz);

    maxFragment = wolfSSL_GetMaxRecordSize(ssl, MAX_RECORD_SIZE);

    while (length > 0 && ret == 0) {
        byte*  output = NULL;
        word32 fragSz = 0;
        word32 i = RECORD_HEADER_SZ;
        int    sendSz = RECORD_HEADER_SZ;

        if (ssl->fragOffset == 0)  {
            if (headerSz + certSz + extSz + certChainSz <=
                                            maxFragment - HANDSHAKE_HEADER_SZ) {
                fragSz = headerSz + certSz + extSz + certChainSz;
            }
            else
                fragSz = maxFragment - HANDSHAKE_HEADER_SZ;

            sendSz += fragSz + HANDSHAKE_HEADER_SZ;
            i += HANDSHAKE_HEADER_SZ;
        }
        else {
            fragSz = min(length, maxFragment);
            sendSz += fragSz;
        }

        sendSz += MAX_MSG_EXTRA;

        /* Check buffers are big enough and grow if needed. */
        if ((ret = CheckAvailableSize(ssl, sendSz)) != 0)
            return ret;

        /* Get position in output buffer to write new message to. */
        output = ssl->buffers.outputBuffer.buffer +
                 ssl->buffers.outputBuffer.length;

        if (ssl->fragOffset == 0) {
            AddTls13FragHeaders(output, fragSz, 0, payloadSz, certificate, ssl);

            /* Request context. */
            output[i++] = certReqCtxLen;
            if (certReqCtxLen > 0) {
                XMEMCPY(output + i, certReqCtx, certReqCtxLen);
                i += certReqCtxLen;
            }
            length -= OPAQUE8_LEN + certReqCtxLen;
            fragSz -= OPAQUE8_LEN + certReqCtxLen;
            /* Certificate list length. */
            c32to24(listSz, output + i);
            i += CERT_HEADER_SZ;
            length -= CERT_HEADER_SZ;
            fragSz -= CERT_HEADER_SZ;
            /* Leaf certificate data length. */
            if (certSz > 0) {
                c32to24(certSz, output + i);
                i += CERT_HEADER_SZ;
                length -= CERT_HEADER_SZ;
                fragSz -= CERT_HEADER_SZ;
            }
        }
        else
            AddTls13RecordHeader(output, fragSz, handshake, ssl);

        if (certSz > 0 && ssl->fragOffset < certSz + extSz) {
            /* Put in the leaf certificate with extensions. */
            word32 copySz = AddCertExt(ssl, ssl->buffers.certificate->buffer,
                            certSz, extSz, ssl->fragOffset, fragSz, output + i);
            i += copySz;
            ssl->fragOffset += copySz;
            length -= copySz;
            fragSz -= copySz;
            if (ssl->fragOffset == certSz + extSz)
                FreeDer(&ssl->buffers.certExts);
        }
        if (certChainSz > 0 && fragSz > 0) {
            /* Put in the CA certificates with empty extensions. */
            while (fragSz > 0) {
                word32 l;

                if (offset == len + OPAQUE16_LEN) {
                    /* Find next CA certificate to write out. */
                    offset = 0;
                    /* Point to the start of current cert in chain buffer. */
                    p = ssl->buffers.certChain->buffer + idx;
                    len = NextCert(ssl->buffers.certChain->buffer,
                                   ssl->buffers.certChain->length, &idx);
                    if (len == 0)
                        break;
                }

                /* Write out certificate and empty extension. */
                l = AddCertExt(ssl, p, len, OPAQUE16_LEN, offset, fragSz,
                                                                    output + i);
                i += l;
                ssl->fragOffset += l;
                length -= l;
                fragSz -= l;
                offset += l;
            }
        }

        if ((int)i - RECORD_HEADER_SZ < 0) {
            WOLFSSL_MSG("Send Cert bad inputSz");
            return BUFFER_E;
        }

        /* This message is always encrypted. */
        sendSz = BuildTls13Message(ssl, output, sendSz,
                                   output + RECORD_HEADER_SZ,
                                   i - RECORD_HEADER_SZ, handshake, 1, 0, 0);
        if (sendSz < 0)
            return sendSz;

        #ifdef WOLFSSL_CALLBACKS
            if (ssl->hsInfoOn)
                AddPacketName(ssl, "Certificate");
            if (ssl->toInfoOn) {
                AddPacketInfo(ssl, "Certificate", handshake, output,
                        sendSz, WRITE_PROTO, ssl->heap);
            }
        #endif

        ssl->buffers.outputBuffer.length += sendSz;
        if (!ssl->options.groupMessages)
            ret = SendBuffered(ssl);
    }

    if (ret != WANT_WRITE) {
        /* Clean up the fragment offset. */
        ssl->fragOffset = 0;
        if (ssl->options.side == WOLFSSL_SERVER_END)
            ssl->options.serverState = SERVER_CERT_COMPLETE;
    }

#ifdef WOLFSSL_POST_HANDSHAKE_AUTH
    if (ssl->options.side == WOLFSSL_CLIENT_END && ssl->certReqCtx != NULL) {
        CertReqCtx* ctx = ssl->certReqCtx;
        ssl->certReqCtx = ssl->certReqCtx->next;
        XFREE(ctx, ssl->heap, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    WOLFSSL_LEAVE("SendTls13Certificate", ret);
    WOLFSSL_END(WC_FUNC_CERTIFICATE_SEND);

    return ret;
}

#if !defined(NO_RSA) || defined(HAVE_ECC) || defined(HAVE_ED25519) || \
     defined(HAVE_ED448)
typedef struct Scv13Args {
    byte*  output; /* not allocated */
    byte*  verify; /* not allocated */
    word32 idx;
    word32 sigLen;
    int    sendSz;
    word16 length;

    byte   sigAlgo;
    byte*  sigData;
    word16 sigDataSz;
} Scv13Args;

static void FreeScv13Args(WOLFSSL* ssl, void* pArgs)
{
    Scv13Args* args = (Scv13Args*)pArgs;

    (void)ssl;

    if (args->sigData) {
        XFREE(args->sigData, ssl->heap, DYNAMIC_TYPE_SIGNATURE);
        args->sigData = NULL;
    }
}

/* handle generation TLS v1.3 certificate_verify (15) */
/* Send the TLS v1.3 CertificateVerify message.
 * A hash of all the message so far is used.
 * The signed data is:
 *     0x20 * 64 | context string | 0x00 | hash of messages
 * This message is always encrypted in TLS v1.3.
 *
 * ssl  The SSL/TLS object.
 * returns 0 on success, otherwise failure.
 */
static int SendTls13CertificateVerify(WOLFSSL* ssl)
{
    int ret = 0;
    buffer* sig = &ssl->buffers.sig;
#ifdef WOLFSSL_ASYNC_CRYPT
    Scv13Args* args = (Scv13Args*)ssl->async.args;
    typedef char args_test[sizeof(ssl->async.args) >= sizeof(*args) ? 1 : -1];
    (void)sizeof(args_test);
#else
    Scv13Args  args[1];
#endif

    WOLFSSL_START(WC_FUNC_CERTIFICATE_VERIFY_SEND);
    WOLFSSL_ENTER("SendTls13CertificateVerify");

#ifdef WOLFSSL_ASYNC_CRYPT
    ret = wolfSSL_AsyncPop(ssl, &ssl->options.asyncState);
    if (ret != WC_NOT_PENDING_E) {
        /* Check for error */
        if (ret < 0)
            goto exit_scv;
    }
    else
#endif
    {
        /* Reset state */
        ret = 0;
        ssl->options.asyncState = TLS_ASYNC_BEGIN;
        XMEMSET(args, 0, sizeof(Scv13Args));
    #ifdef WOLFSSL_ASYNC_CRYPT
        ssl->async.freeArgs = FreeScv13Args;
    #endif
    }

    switch(ssl->options.asyncState)
    {
        case TLS_ASYNC_BEGIN:
        {
            if (ssl->options.sendVerify == SEND_BLANK_CERT) {
                return 0;  /* sent blank cert, can't verify */
            }

            args->sendSz = MAX_CERT_VERIFY_SZ + MAX_MSG_EXTRA;
            /* Always encrypted.  */
            args->sendSz += MAX_MSG_EXTRA;

            /* check for available size */
            if ((ret = CheckAvailableSize(ssl, args->sendSz)) != 0) {
                goto exit_scv;
            }

            /* get output buffer */
            args->output = ssl->buffers.outputBuffer.buffer +
                           ssl->buffers.outputBuffer.length;

            /* Advance state and proceed */
            ssl->options.asyncState = TLS_ASYNC_BUILD;
        } /* case TLS_ASYNC_BEGIN */
        FALL_THROUGH;

        case TLS_ASYNC_BUILD:
        {
            /* idx is used to track verify pointer offset to output */
            args->idx = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
            args->verify =
                          &args->output[RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ];

            if (ssl->buffers.key == NULL) {
            #ifdef HAVE_PK_CALLBACKS
                if (wolfSSL_CTX_IsPrivatePkSet(ssl->ctx))
                    args->length = GetPrivateKeySigSize(ssl);
                else
            #endif
                    ERROR_OUT(NO_PRIVATE_KEY, exit_scv);
            }
            else {
                ret = DecodePrivateKey(ssl, &args->length);
                if (ret != 0)
                    goto exit_scv;
            }

            if (args->length <= 0) {
                ERROR_OUT(NO_PRIVATE_KEY, exit_scv);
            }

            /* Add signature algorithm. */
            if (ssl->hsType == DYNAMIC_TYPE_RSA)
                args->sigAlgo = rsa_pss_sa_algo;
        #ifdef HAVE_ECC
            else if (ssl->hsType == DYNAMIC_TYPE_ECC)
                args->sigAlgo = ecc_dsa_sa_algo;
        #endif
        #ifdef HAVE_ED25519
            else if (ssl->hsType == DYNAMIC_TYPE_ED25519)
                args->sigAlgo = ed25519_sa_algo;
        #endif
        #ifdef HAVE_ED448
            else if (ssl->hsType == DYNAMIC_TYPE_ED448)
                args->sigAlgo = ed448_sa_algo;
        #endif
            else {
                ERROR_OUT(ALGO_ID_E, exit_scv);
            }
            EncodeSigAlg(ssl->suites->hashAlgo, args->sigAlgo, args->verify);

            if (ssl->hsType == DYNAMIC_TYPE_RSA) {
                int sigLen = MAX_SIG_DATA_SZ;
                if (args->length > MAX_SIG_DATA_SZ)
                    sigLen = args->length;
                args->sigData = (byte*)XMALLOC(sigLen, ssl->heap,
                                                        DYNAMIC_TYPE_SIGNATURE);
            }
            else {
                args->sigData = (byte*)XMALLOC(MAX_SIG_DATA_SZ, ssl->heap,
                                                        DYNAMIC_TYPE_SIGNATURE);
            }
            if (args->sigData == NULL) {
                ERROR_OUT(MEMORY_E, exit_scv);
            }

            /* Create the data to be signed. */
            ret = CreateSigData(ssl, args->sigData, &args->sigDataSz, 0);
            if (ret != 0)
                goto exit_scv;

        #ifndef NO_RSA
            if (ssl->hsType == DYNAMIC_TYPE_RSA) {
                /* build encoded signature buffer */
                sig->length = WC_MAX_DIGEST_SIZE;
                sig->buffer = (byte*)XMALLOC(sig->length, ssl->heap,
                                                        DYNAMIC_TYPE_SIGNATURE);
                if (sig->buffer == NULL) {
                    ERROR_OUT(MEMORY_E, exit_scv);
                }

                ret = CreateRSAEncodedSig(sig->buffer, args->sigData,
                    args->sigDataSz, args->sigAlgo, ssl->suites->hashAlgo);
                if (ret < 0)
                    goto exit_scv;
                sig->length = ret;
                ret = 0;

                /* Maximum size of RSA Signature. */
                args->sigLen = args->length;
            }
        #endif /* !NO_RSA */
        #ifdef HAVE_ECC
            if (ssl->hsType == DYNAMIC_TYPE_ECC) {
                sig->length = args->sendSz - args->idx - HASH_SIG_SIZE -
                              VERIFY_HEADER;
                ret = CreateECCEncodedSig(args->sigData,
                    args->sigDataSz, ssl->suites->hashAlgo);
                if (ret < 0)
                    goto exit_scv;
                args->sigDataSz = (word16)ret;
                ret = 0;
            }
        #endif /* HAVE_ECC */
        #ifdef HAVE_ED25519
            if (ssl->hsType == DYNAMIC_TYPE_ED25519) {
                ret = Ed25519CheckPubKey(ssl);
                if (ret < 0) {
                    ERROR_OUT(ret, exit_scv);
                }
                sig->length = ED25519_SIG_SIZE;
            }
        #endif /* HAVE_ED25519 */
        #ifdef HAVE_ED448
            if (ssl->hsType == DYNAMIC_TYPE_ED448) {
                ret = Ed448CheckPubKey(ssl);
                if (ret < 0) {
                    ERROR_OUT(ret, exit_scv);
                }
                sig->length = ED448_SIG_SIZE;
            }
        #endif /* HAVE_ED448 */

            /* Advance state and proceed */
            ssl->options.asyncState = TLS_ASYNC_DO;
        } /* case TLS_ASYNC_BUILD */
        FALL_THROUGH;

        case TLS_ASYNC_DO:
        {
        #ifdef HAVE_ECC
           if (ssl->hsType == DYNAMIC_TYPE_ECC) {

                ret = EccSign(ssl, args->sigData, args->sigDataSz,
                    args->verify + HASH_SIG_SIZE + VERIFY_HEADER,
                    (word32*)&sig->length, (ecc_key*)ssl->hsKey,
            #ifdef HAVE_PK_CALLBACKS
                    ssl->buffers.key
            #else
                    NULL
            #endif
                );
                args->length = (word16)sig->length;
            }
        #endif /* HAVE_ECC */
        #ifdef HAVE_ED25519
            if (ssl->hsType == DYNAMIC_TYPE_ED25519) {
                ret = Ed25519Sign(ssl, args->sigData, args->sigDataSz,
                    args->verify + HASH_SIG_SIZE + VERIFY_HEADER,
                    (word32*)&sig->length, (ed25519_key*)ssl->hsKey,
            #ifdef HAVE_PK_CALLBACKS
                    ssl->buffers.key
            #else
                    NULL
            #endif
                );
                args->length = (word16)sig->length;
            }
        #endif
        #ifdef HAVE_ED448
            if (ssl->hsType == DYNAMIC_TYPE_ED448) {
                ret = Ed448Sign(ssl, args->sigData, args->sigDataSz,
                    args->verify + HASH_SIG_SIZE + VERIFY_HEADER,
                    (word32*)&sig->length, (ed448_key*)ssl->hsKey,
            #ifdef HAVE_PK_CALLBACKS
                    ssl->buffers.key
            #else
                    NULL
            #endif
                );
                args->length = (word16)sig->length;
            }
        #endif
        #ifndef NO_RSA
            if (ssl->hsType == DYNAMIC_TYPE_RSA) {
                ret = RsaSign(ssl, sig->buffer, (word32)sig->length,
                    args->verify + HASH_SIG_SIZE + VERIFY_HEADER, &args->sigLen,
                    args->sigAlgo, ssl->suites->hashAlgo,
                    (RsaKey*)ssl->hsKey,
                    ssl->buffers.key
                );
                if (ret == 0) {
                    args->length = (word16)args->sigLen;

                    XMEMCPY(args->sigData,
                        args->verify + HASH_SIG_SIZE + VERIFY_HEADER,
                        args->sigLen);
                }
            }
        #endif /* !NO_RSA */

            /* Check for error */
            if (ret != 0) {
                goto exit_scv;
            }

            /* Add signature length. */
            c16toa(args->length, args->verify + HASH_SIG_SIZE);

            /* Advance state and proceed */
            ssl->options.asyncState = TLS_ASYNC_VERIFY;
        } /* case TLS_ASYNC_DO */
        FALL_THROUGH;

        case TLS_ASYNC_VERIFY:
        {
        #ifndef NO_RSA
            if (ssl->hsType == DYNAMIC_TYPE_RSA) {
                /* check for signature faults */
                ret = VerifyRsaSign(ssl, args->sigData, args->sigLen,
                    sig->buffer, (word32)sig->length, args->sigAlgo,
                    ssl->suites->hashAlgo, (RsaKey*)ssl->hsKey,
                    ssl->buffers.key
                );
            }
        #endif /* !NO_RSA */

            /* Check for error */
            if (ret != 0) {
                goto exit_scv;
            }

            /* Advance state and proceed */
            ssl->options.asyncState = TLS_ASYNC_FINALIZE;
        } /* case TLS_ASYNC_VERIFY */
        FALL_THROUGH;

        case TLS_ASYNC_FINALIZE:
        {
            /* Put the record and handshake headers on. */
            AddTls13Headers(args->output, args->length + HASH_SIG_SIZE +
                            VERIFY_HEADER, certificate_verify, ssl);

            args->sendSz = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ +
                                   args->length + HASH_SIG_SIZE + VERIFY_HEADER;

            /* Advance state and proceed */
            ssl->options.asyncState = TLS_ASYNC_END;
        } /* case TLS_ASYNC_FINALIZE */
        FALL_THROUGH;

        case TLS_ASYNC_END:
        {
            /* This message is always encrypted. */
            ret = BuildTls13Message(ssl, args->output,
                                    MAX_CERT_VERIFY_SZ + MAX_MSG_EXTRA,
                                    args->output + RECORD_HEADER_SZ,
                                    args->sendSz - RECORD_HEADER_SZ, handshake,
                                    1, 0, 0);

            if (ret < 0) {
                goto exit_scv;
            }
            else {
                args->sendSz = ret;
                ret = 0;
            }

        #ifdef WOLFSSL_CALLBACKS
            if (ssl->hsInfoOn)
                AddPacketName(ssl, "CertificateVerify");
            if (ssl->toInfoOn) {
                AddPacketInfo(ssl, "CertificateVerify", handshake,
                            args->output, args->sendSz, WRITE_PROTO, ssl->heap);
            }
        #endif

            ssl->buffers.outputBuffer.length += args->sendSz;

            if (!ssl->options.groupMessages)
                ret = SendBuffered(ssl);
            break;
        }
        default:
            ret = INPUT_CASE_ERROR;
    } /* switch(ssl->options.asyncState) */

exit_scv:

    WOLFSSL_LEAVE("SendTls13CertificateVerify", ret);
    WOLFSSL_END(WC_FUNC_CERTIFICATE_VERIFY_SEND);

#ifdef WOLFSSL_ASYNC_CRYPT
    /* Handle async operation */
    if (ret == WC_PENDING_E) {
        return ret;
    }
#endif /* WOLFSSL_ASYNC_CRYPT */

    /* Final cleanup */
    FreeScv13Args(ssl, args);
    FreeKeyExchange(ssl);

    return ret;
}
#endif

/* handle processing TLS v1.3 certificate (11) */
/* Parse and handle a TLS v1.3 Certificate message.
 *
 * ssl       The SSL/TLS object.
 * input     The message buffer.
 * inOutIdx  On entry, the index into the message buffer of Certificate.
 *           On exit, the index of byte after the Certificate message.
 * totalSz   The length of the current handshake message.
 * returns 0 on success and otherwise failure.
 */
static int DoTls13Certificate(WOLFSSL* ssl, byte* input, word32* inOutIdx,
                              word32 totalSz)
{
    int ret;

    WOLFSSL_START(WC_FUNC_CERTIFICATE_DO);
    WOLFSSL_ENTER("DoTls13Certificate");

    ret = ProcessPeerCerts(ssl, input, inOutIdx, totalSz);
    if (ret == 0) {
#if !defined(NO_WOLFSSL_CLIENT)
        if (ssl->options.side == WOLFSSL_CLIENT_END)
            ssl->options.serverState = SERVER_CERT_COMPLETE;
#endif
#if !defined(NO_WOLFSSL_SERVER) && defined(WOLFSSL_POST_HANDSHAKE_AUTH)
        if (ssl->options.side == WOLFSSL_SERVER_END &&
                                ssl->options.handShakeState == HANDSHAKE_DONE) {
            /* reset handshake states */
            ssl->options.serverState = SERVER_FINISHED_COMPLETE;
            ssl->options.acceptState  = TICKET_SENT;
            ssl->options.handShakeState = SERVER_FINISHED_COMPLETE;
        }
#endif
    }

    WOLFSSL_LEAVE("DoTls13Certificate", ret);
    WOLFSSL_END(WC_FUNC_CERTIFICATE_DO);

    return ret;
}

#if !defined(NO_RSA) || defined(HAVE_ECC) || defined(HAVE_ED25519) || \
                                                             defined(HAVE_ED448)

typedef struct Dcv13Args {
    byte*  output; /* not allocated */
    word32 sendSz;
    word16 sz;
    word32 sigSz;
    word32 idx;
    word32 begin;
    byte   hashAlgo;
    byte   sigAlgo;

    byte*  sigData;
    word16 sigDataSz;
} Dcv13Args;

static void FreeDcv13Args(WOLFSSL* ssl, void* pArgs)
{
    Dcv13Args* args = (Dcv13Args*)pArgs;

    if (args->sigData != NULL) {
        XFREE(args->sigData, ssl->heap, DYNAMIC_TYPE_SIGNATURE);
        args->sigData = NULL;
    }

    (void)ssl;
}

/* handle processing TLS v1.3 certificate_verify (15) */
/* Parse and handle a TLS v1.3 CertificateVerify message.
 *
 * ssl       The SSL/TLS object.
 * input     The message buffer.
 * inOutIdx  On entry, the index into the message buffer of
 *           CertificateVerify.
 *           On exit, the index of byte after the CertificateVerify message.
 * totalSz   The length of the current handshake message.
 * returns 0 on success and otherwise failure.
 */
static int DoTls13CertificateVerify(WOLFSSL* ssl, byte* input,
                                    word32* inOutIdx, word32 totalSz)
{
    int         ret = 0;
    buffer*     sig = &ssl->buffers.sig;
#ifdef WOLFSSL_ASYNC_CRYPT
    Dcv13Args* args = (Dcv13Args*)ssl->async.args;
    typedef char args_test[sizeof(ssl->async.args) >= sizeof(*args) ? 1 : -1];
    (void)sizeof(args_test);
#else
    Dcv13Args  args[1];
#endif

    WOLFSSL_START(WC_FUNC_CERTIFICATE_VERIFY_DO);
    WOLFSSL_ENTER("DoTls13CertificateVerify");

#ifdef WOLFSSL_ASYNC_CRYPT
    ret = wolfSSL_AsyncPop(ssl, &ssl->options.asyncState);
    if (ret != WC_NOT_PENDING_E) {
        /* Check for error */
        if (ret < 0)
            goto exit_dcv;
    }
    else
#endif
    {
        /* Reset state */
        ret = 0;
        ssl->options.asyncState = TLS_ASYNC_BEGIN;
        XMEMSET(args, 0, sizeof(Dcv13Args));
        args->hashAlgo = sha_mac;
        args->sigAlgo = anonymous_sa_algo;
        args->idx = *inOutIdx;
        args->begin = *inOutIdx;
    #ifdef WOLFSSL_ASYNC_CRYPT
        ssl->async.freeArgs = FreeDcv13Args;
    #endif
    }

    switch(ssl->options.asyncState)
    {
        case TLS_ASYNC_BEGIN:
        {
        #ifdef WOLFSSL_CALLBACKS
            if (ssl->hsInfoOn) AddPacketName(ssl, "CertificateVerify");
            if (ssl->toInfoOn) AddLateName("CertificateVerify",
                                           &ssl->timeoutInfo);
        #endif

            /* Advance state and proceed */
            ssl->options.asyncState = TLS_ASYNC_BUILD;
        } /* case TLS_ASYNC_BEGIN */
        FALL_THROUGH;

        case TLS_ASYNC_BUILD:
        {
            /* Signature algorithm. */
            if ((args->idx - args->begin) + ENUM_LEN + ENUM_LEN > totalSz) {
                ERROR_OUT(BUFFER_ERROR, exit_dcv);
            }
            ret = DecodeTls13SigAlg(input + args->idx, &args->hashAlgo,
                                                                &args->sigAlgo);
            if (ret < 0)
                goto exit_dcv;
            args->idx += OPAQUE16_LEN;

            /* Signature length. */
            if ((args->idx - args->begin) + OPAQUE16_LEN > totalSz) {
                ERROR_OUT(BUFFER_ERROR, exit_dcv);
            }
            ato16(input + args->idx, &args->sz);
            args->idx += OPAQUE16_LEN;

            /* Signature data. */
            if ((args->idx - args->begin) + args->sz > totalSz ||
                                                       args->sz > ENCRYPT_LEN) {
                ERROR_OUT(BUFFER_ERROR, exit_dcv);
            }

            /* Check for public key of required type. */
        #ifdef HAVE_ED25519
            if (args->sigAlgo == ed25519_sa_algo &&
                                                  !ssl->peerEd25519KeyPresent) {
                WOLFSSL_MSG("Oops, peer sent ED25519 key but not in verify");
            }
        #endif
        #ifdef HAVE_ED448
            if (args->sigAlgo == ed448_sa_algo && !ssl->peerEd448KeyPresent) {
                WOLFSSL_MSG("Oops, peer sent ED448 key but not in verify");
            }
        #endif
        #ifdef HAVE_ECC
            if (args->sigAlgo == ecc_dsa_sa_algo &&
                                                   !ssl->peerEccDsaKeyPresent) {
                WOLFSSL_MSG("Oops, peer sent ECC key but not in verify");
            }
        #endif
        #ifndef NO_RSA
            if (args->sigAlgo == rsa_sa_algo) {
                WOLFSSL_MSG("Oops, peer sent PKCS#1.5 signature");
                ERROR_OUT(INVALID_PARAMETER, exit_dcv);
            }
            if (args->sigAlgo == rsa_pss_sa_algo &&
                         (ssl->peerRsaKey == NULL || !ssl->peerRsaKeyPresent)) {
                WOLFSSL_MSG("Oops, peer sent RSA key but not in verify");
            }
        #endif

            sig->buffer = (byte*)XMALLOC(args->sz, ssl->heap,
                                         DYNAMIC_TYPE_SIGNATURE);
            if (sig->buffer == NULL) {
                ERROR_OUT(MEMORY_E, exit_dcv);
            }
            sig->length = args->sz;
            XMEMCPY(sig->buffer, input + args->idx, args->sz);

        #ifdef HAVE_ECC
            if (ssl->peerEccDsaKeyPresent) {
                WOLFSSL_MSG("Doing ECC peer cert verify");

                args->sigData = (byte*)XMALLOC(MAX_SIG_DATA_SZ, ssl->heap,
                                                        DYNAMIC_TYPE_SIGNATURE);
                if (args->sigData == NULL) {
                    ERROR_OUT(MEMORY_E, exit_dcv);
                }

                ret = CreateSigData(ssl, args->sigData, &args->sigDataSz, 1);
                if (ret != 0)
                    goto exit_dcv;
                ret = CreateECCEncodedSig(args->sigData,
                    args->sigDataSz, args->hashAlgo);
                if (ret < 0)
                    goto exit_dcv;
                args->sigDataSz = (word16)ret;
                ret = 0;
            }
        #endif
        #ifdef HAVE_ED25519
            if (ssl->peerEd25519KeyPresent) {
                WOLFSSL_MSG("Doing ED25519 peer cert verify");

                args->sigData = (byte*)XMALLOC(MAX_SIG_DATA_SZ, ssl->heap,
                                                        DYNAMIC_TYPE_SIGNATURE);
                if (args->sigData == NULL) {
                    ERROR_OUT(MEMORY_E, exit_dcv);
                }

                CreateSigData(ssl, args->sigData, &args->sigDataSz, 1);
                ret = 0;
            }
        #endif
        #ifdef HAVE_ED448
            if (ssl->peerEd448KeyPresent) {
                WOLFSSL_MSG("Doing ED448 peer cert verify");

                args->sigData = (byte*)XMALLOC(MAX_SIG_DATA_SZ, ssl->heap,
                                                        DYNAMIC_TYPE_SIGNATURE);
                if (args->sigData == NULL) {
                    ERROR_OUT(MEMORY_E, exit_dcv);
                }

                CreateSigData(ssl, args->sigData, &args->sigDataSz, 1);
                ret = 0;
            }
       #endif

            /* Advance state and proceed */
            ssl->options.asyncState = TLS_ASYNC_DO;
        } /* case TLS_ASYNC_BUILD */
        FALL_THROUGH;

        case TLS_ASYNC_DO:
        {
        #ifndef NO_RSA
            if (ssl->peerRsaKey != NULL && ssl->peerRsaKeyPresent != 0) {
                WOLFSSL_MSG("Doing RSA peer cert verify");

                ret = RsaVerify(ssl, sig->buffer, (word32)sig->length, &args->output,
                    args->sigAlgo, args->hashAlgo, ssl->peerRsaKey,
                #ifdef HAVE_PK_CALLBACKS
                    &ssl->buffers.peerRsaKey
                #else
                    NULL
                #endif
                );
                if (ret >= 0) {
                    args->sendSz = ret;
                    ret = 0;
                }
            }
        #endif /* !NO_RSA */
        #ifdef HAVE_ECC
            if (ssl->peerEccDsaKeyPresent) {
                WOLFSSL_MSG("Doing ECC peer cert verify");

                ret = EccVerify(ssl, input + args->idx, args->sz,
                    args->sigData, args->sigDataSz,
                    ssl->peerEccDsaKey,
                #ifdef HAVE_PK_CALLBACKS
                    &ssl->buffers.peerEccDsaKey
                #else
                    NULL
                #endif
                );

                if (ret >= 0) {
                    FreeKey(ssl, DYNAMIC_TYPE_ECC, (void**)&ssl->peerEccDsaKey);
                    ssl->peerEccDsaKeyPresent = 0;
                }
            }
        #endif /* HAVE_ECC */
        #ifdef HAVE_ED25519
            if (ssl->peerEd25519KeyPresent) {
                WOLFSSL_MSG("Doing ED25519 peer cert verify");

                ret = Ed25519Verify(ssl, input + args->idx, args->sz,
                    args->sigData, args->sigDataSz,
                    ssl->peerEd25519Key,
                #ifdef HAVE_PK_CALLBACKS
                    &ssl->buffers.peerEd25519Key
                #else
                    NULL
                #endif
                );

                if (ret >= 0) {
                    FreeKey(ssl, DYNAMIC_TYPE_ED25519,
                                                  (void**)&ssl->peerEd25519Key);
                    ssl->peerEd25519KeyPresent = 0;
                }
            }
        #endif
        #ifdef HAVE_ED448
            if (ssl->peerEd448KeyPresent) {
                WOLFSSL_MSG("Doing ED448 peer cert verify");

                ret = Ed448Verify(ssl, input + args->idx, args->sz,
                    args->sigData, args->sigDataSz,
                    ssl->peerEd448Key,
                #ifdef HAVE_PK_CALLBACKS
                    &ssl->buffers.peerEd448Key
                #else
                    NULL
                #endif
                );

                if (ret >= 0) {
                    FreeKey(ssl, DYNAMIC_TYPE_ED448,
                                                    (void**)&ssl->peerEd448Key);
                    ssl->peerEd448KeyPresent = 0;
                }
            }
        #endif

            /* Check for error */
            if (ret != 0) {
                goto exit_dcv;
            }

            /* Advance state and proceed */
            ssl->options.asyncState = TLS_ASYNC_VERIFY;
        } /* case TLS_ASYNC_DO */
        FALL_THROUGH;

        case TLS_ASYNC_VERIFY:
        {
        #if !defined(NO_RSA) && defined(WC_RSA_PSS)
            if (ssl->peerRsaKey != NULL && ssl->peerRsaKeyPresent != 0) {
                ret = CheckRSASignature(ssl, args->sigAlgo, args->hashAlgo,
                                        args->output, args->sendSz);
                if (ret != 0)
                    goto exit_dcv;

                FreeKey(ssl, DYNAMIC_TYPE_RSA, (void**)&ssl->peerRsaKey);
                ssl->peerRsaKeyPresent = 0;
            }
        #endif /* !NO_RSA && WC_RSA_PSS */

            /* Advance state and proceed */
            ssl->options.asyncState = TLS_ASYNC_FINALIZE;
        } /* case TLS_ASYNC_VERIFY */
        FALL_THROUGH;

        case TLS_ASYNC_FINALIZE:
        {
            ssl->options.havePeerVerify = 1;

            /* Set final index */
            args->idx += args->sz;
            *inOutIdx = args->idx;

            /* Encryption is always on: add padding */
            *inOutIdx += ssl->keys.padSz;

            /* Advance state and proceed */
            ssl->options.asyncState = TLS_ASYNC_END;

        #if !defined(NO_WOLFSSL_CLIENT)
            if (ssl->options.side == WOLFSSL_CLIENT_END)
                ssl->options.serverState = SERVER_CERT_VERIFY_COMPLETE;
        #endif
        } /* case TLS_ASYNC_FINALIZE */

        case TLS_ASYNC_END:
        {
            break;
        }
        default:
            ret = INPUT_CASE_ERROR;
    } /* switch(ssl->options.asyncState) */

exit_dcv:

    WOLFSSL_LEAVE("DoTls13CertificateVerify", ret);
    WOLFSSL_END(WC_FUNC_CERTIFICATE_VERIFY_DO);

#ifdef WOLFSSL_ASYNC_CRYPT
    /* Handle async operation */
    if (ret == WC_PENDING_E) {
        /* Mark message as not received so it can process again */
        ssl->msgsReceived.got_certificate_verify = 0;

        return ret;
    }
    else
#endif /* WOLFSSL_ASYNC_CRYPT */
    if (ret != 0 && ret != INVALID_PARAMETER)
        SendAlert(ssl, alert_fatal, decrypt_error);

    /* Final cleanup */
    FreeDcv13Args(ssl, args);
    FreeKeyExchange(ssl);

    return ret;
}
#endif /* !NO_RSA || HAVE_ECC */
#endif /* !NO_CERTS */

/* Parse and handle a TLS v1.3 Finished message.
 *
 * ssl       The SSL/TLS object.
 * input     The message buffer.
 * inOutIdx  On entry, the index into the message buffer of Finished.
 *           On exit, the index of byte after the Finished message and padding.
 * size      Length of message data.
 * totalSz   Length of remaining data in the message buffer.
 * sniff     Indicates whether we are sniffing packets.
 * returns 0 on success and otherwise failure.
 */
int DoTls13Finished(WOLFSSL* ssl, const byte* input, word32* inOutIdx,
                           word32 size, word32 totalSz, int sniff)
{
    int    ret;
    word32 finishedSz = 0;
    byte*  secret;
    byte   mac[WC_MAX_DIGEST_SIZE];

    WOLFSSL_START(WC_FUNC_FINISHED_DO);
    WOLFSSL_ENTER("DoTls13Finished");

    /* check against totalSz */
    if (*inOutIdx + size + ssl->keys.padSz > totalSz)
        return BUFFER_E;

    if (ssl->options.handShakeDone) {
        ret = DeriveFinishedSecret(ssl, ssl->clientSecret,
                                   ssl->keys.client_write_MAC_secret);
        if (ret != 0)
            return ret;

        secret = ssl->keys.client_write_MAC_secret;
    }
    else if (ssl->options.side == WOLFSSL_CLIENT_END) {
        /* All the handshake messages have been received to calculate
         * client and server finished keys.
         */
        ret = DeriveFinishedSecret(ssl, ssl->clientSecret,
                                   ssl->keys.client_write_MAC_secret);
        if (ret != 0)
            return ret;

        ret = DeriveFinishedSecret(ssl, ssl->serverSecret,
                                   ssl->keys.server_write_MAC_secret);
        if (ret != 0)
            return ret;

        secret = ssl->keys.server_write_MAC_secret;
    }
    else {
        secret = ssl->keys.client_write_MAC_secret;
    }

    if (sniff == NO_SNIFF) {
        ret = BuildTls13HandshakeHmac(ssl, secret, mac, &finishedSz);
        if (ret != 0)
            return ret;
        if (size != finishedSz)
            return BUFFER_ERROR;
    }

#ifdef WOLFSSL_CALLBACKS
    if (ssl->hsInfoOn) AddPacketName(ssl, "Finished");
    if (ssl->toInfoOn) AddLateName("Finished", &ssl->timeoutInfo);
#endif

    if (sniff == NO_SNIFF) {
        /* Actually check verify data. */
        if (XMEMCMP(input + *inOutIdx, mac, size) != 0){
            WOLFSSL_MSG("Verify finished error on hashes");
            SendAlert(ssl, alert_fatal, decrypt_error);
            return VERIFY_FINISHED_ERROR;
        }
    }

    /* Force input exhaustion at ProcessReply by consuming padSz. */
    *inOutIdx += size + ssl->keys.padSz;

    if (ssl->options.side == WOLFSSL_SERVER_END &&
                                                  !ssl->options.handShakeDone) {
#ifdef WOLFSSL_EARLY_DATA
        if (ssl->earlyData != no_early_data) {
            if ((ret = DeriveTls13Keys(ssl, no_key, DECRYPT_SIDE_ONLY, 1)) != 0)
                return ret;
        }
#endif
        /* Setup keys for application data messages from client. */
        if ((ret = SetKeysSide(ssl, DECRYPT_SIDE_ONLY)) != 0)
            return ret;
    }

#ifndef NO_WOLFSSL_CLIENT
    if (ssl->options.side == WOLFSSL_CLIENT_END)
        ssl->options.serverState = SERVER_FINISHED_COMPLETE;
#endif
#ifndef NO_WOLFSSL_SERVER
    if (ssl->options.side == WOLFSSL_SERVER_END) {
        ssl->options.clientState = CLIENT_FINISHED_COMPLETE;
        ssl->options.handShakeState = HANDSHAKE_DONE;
        ssl->options.handShakeDone  = 1;
    }
#endif

    WOLFSSL_LEAVE("DoTls13Finished", 0);
    WOLFSSL_END(WC_FUNC_FINISHED_DO);

    return 0;
}

/* Send the TLS v1.3 Finished message.
 *
 * ssl  The SSL/TLS object.
 * returns 0 on success, otherwise failure.
 */
static int SendTls13Finished(WOLFSSL* ssl)
{
    int   sendSz;
    int   finishedSz = ssl->specs.hash_size;
    byte* input;
    byte* output;
    int   ret;
    int   headerSz = HANDSHAKE_HEADER_SZ;
    int   outputSz;
    byte* secret;

    WOLFSSL_START(WC_FUNC_FINISHED_SEND);
    WOLFSSL_ENTER("SendTls13Finished");

    outputSz = WC_MAX_DIGEST_SIZE + DTLS_HANDSHAKE_HEADER_SZ + MAX_MSG_EXTRA;
    /* Check buffers are big enough and grow if needed. */
    if ((ret = CheckAvailableSize(ssl, outputSz)) != 0)
        return ret;

    /* get output buffer */
    output = ssl->buffers.outputBuffer.buffer +
             ssl->buffers.outputBuffer.length;
    input = output + RECORD_HEADER_SZ;

    AddTls13HandShakeHeader(input, finishedSz, 0, finishedSz, finished, ssl);

    /* make finished hashes */
    if (ssl->options.handShakeDone) {
        ret = DeriveFinishedSecret(ssl, ssl->clientSecret,
                                   ssl->keys.client_write_MAC_secret);
        if (ret != 0)
            return ret;

        secret = ssl->keys.client_write_MAC_secret;
    }
    else if (ssl->options.side == WOLFSSL_CLIENT_END)
        secret = ssl->keys.client_write_MAC_secret;
    else {
        /* All the handshake messages have been done to calculate client and
         * server finished keys.
         */
        ret = DeriveFinishedSecret(ssl, ssl->clientSecret,
                                   ssl->keys.client_write_MAC_secret);
        if (ret != 0)
            return ret;

        ret = DeriveFinishedSecret(ssl, ssl->serverSecret,
                                   ssl->keys.server_write_MAC_secret);
        if (ret != 0)
            return ret;

        secret = ssl->keys.server_write_MAC_secret;
    }
    ret = BuildTls13HandshakeHmac(ssl, secret, &input[headerSz], NULL);
    if (ret != 0)
        return ret;

    /* This message is always encrypted. */
    sendSz = BuildTls13Message(ssl, output, outputSz, input,
                               headerSz + finishedSz, handshake, 1, 0, 0);
    if (sendSz < 0)
        return BUILD_MSG_ERROR;

#ifndef NO_SESSION_CACHE
    if (!ssl->options.resuming && (ssl->options.side == WOLFSSL_SERVER_END ||
            (ssl->options.side == WOLFSSL_SERVER_END && ssl->arrays != NULL))) {
        AddSession(ssl);    /* just try */
    }
#endif

    #ifdef WOLFSSL_CALLBACKS
        if (ssl->hsInfoOn) AddPacketName(ssl, "Finished");
        if (ssl->toInfoOn) {
            AddPacketInfo(ssl, "Finished", handshake, output, sendSz,
                          WRITE_PROTO, ssl->heap);
        }
    #endif

    ssl->buffers.outputBuffer.length += sendSz;

    if (ssl->options.side == WOLFSSL_SERVER_END) {
        /* Can send application data now. */
        if ((ret = DeriveMasterSecret(ssl)) != 0)
            return ret;
#ifdef WOLFSSL_EARLY_DATA
        if ((ret = DeriveTls13Keys(ssl, traffic_key, ENCRYPT_SIDE_ONLY, 1))
                                                                         != 0) {
            return ret;
        }
        if ((ret = DeriveTls13Keys(ssl, traffic_key, DECRYPT_SIDE_ONLY,
                                       ssl->earlyData == no_early_data)) != 0) {
            return ret;
        }
#else
        if ((ret = DeriveTls13Keys(ssl, traffic_key, ENCRYPT_AND_DECRYPT_SIDE,
                                                                     1)) != 0) {
            return ret;
        }
#endif
        if ((ret = SetKeysSide(ssl, ENCRYPT_SIDE_ONLY)) != 0)
            return ret;
    }

    if (ssl->options.side == WOLFSSL_CLIENT_END &&
                                                  !ssl->options.handShakeDone) {
#ifdef WOLFSSL_EARLY_DATA
        if (ssl->earlyData != no_early_data) {
            if ((ret = DeriveTls13Keys(ssl, no_key, ENCRYPT_AND_DECRYPT_SIDE,
                                                                     1)) != 0) {
                    return ret;
            }
        }
#endif
        /* Setup keys for application data messages. */
        if ((ret = SetKeysSide(ssl, ENCRYPT_AND_DECRYPT_SIDE)) != 0)
            return ret;

#if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
        ret = DeriveResumptionSecret(ssl, ssl->session.masterSecret);
        if (ret != 0)
            return ret;
#endif
    }

#ifndef NO_WOLFSSL_CLIENT
    if (ssl->options.side == WOLFSSL_CLIENT_END) {
        ssl->options.clientState = CLIENT_FINISHED_COMPLETE;
        ssl->options.handShakeState = HANDSHAKE_DONE;
        ssl->options.handShakeDone  = 1;
    }
#endif
#ifndef NO_WOLFSSL_SERVER
    if (ssl->options.side == WOLFSSL_SERVER_END) {
        ssl->options.serverState = SERVER_FINISHED_COMPLETE;
    }
#endif

    if ((ret = SendBuffered(ssl)) != 0)
        return ret;

    WOLFSSL_LEAVE("SendTls13Finished", ret);
    WOLFSSL_END(WC_FUNC_FINISHED_SEND);

    return ret;
}

/* handle generation TLS v1.3 key_update (24) */
/* Send the TLS v1.3 KeyUpdate message.
 *
 * ssl  The SSL/TLS object.
 * returns 0 on success, otherwise failure.
 */
static int SendTls13KeyUpdate(WOLFSSL* ssl)
{
    int    sendSz;
    byte*  input;
    byte*  output;
    int    ret;
    int    headerSz = HANDSHAKE_HEADER_SZ;
    int    outputSz;
    word32 i = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;

    WOLFSSL_START(WC_FUNC_KEY_UPDATE_SEND);
    WOLFSSL_ENTER("SendTls13KeyUpdate");

    outputSz = OPAQUE8_LEN + MAX_MSG_EXTRA;
    /* Check buffers are big enough and grow if needed. */
    if ((ret = CheckAvailableSize(ssl, outputSz)) != 0)
        return ret;

    /* get output buffer */
    output = ssl->buffers.outputBuffer.buffer +
             ssl->buffers.outputBuffer.length;
    input = output + RECORD_HEADER_SZ;

    AddTls13Headers(output, OPAQUE8_LEN, key_update, ssl);

    /* If:
     *   1. I haven't sent a KeyUpdate requesting a response and
     *   2. This isn't responding to peer KeyUpdate requiring a response then,
     * I want a response.
     */
    ssl->keys.updateResponseReq = output[i++] =
         !ssl->keys.updateResponseReq && !ssl->keys.keyUpdateRespond;
    /* Sent response, no longer need to respond. */
    ssl->keys.keyUpdateRespond = 0;

    /* This message is always encrypted. */
    sendSz = BuildTls13Message(ssl, output, outputSz, input,
                               headerSz + OPAQUE8_LEN, handshake, 0, 0, 0);
    if (sendSz < 0)
        return BUILD_MSG_ERROR;

    #ifdef WOLFSSL_CALLBACKS
        if (ssl->hsInfoOn) AddPacketName(ssl, "KeyUpdate");
        if (ssl->toInfoOn) {
            AddPacketInfo(ssl, "KeyUpdate", handshake, output, sendSz,
                          WRITE_PROTO, ssl->heap);
        }
    #endif

    ssl->buffers.outputBuffer.length += sendSz;

    ret = SendBuffered(ssl);
    if (ret != 0 && ret != WANT_WRITE)
        return ret;

    /* Future traffic uses new encryption keys. */
    if ((ret = DeriveTls13Keys(ssl, update_traffic_key, ENCRYPT_SIDE_ONLY, 1))
                                                                           != 0)
        return ret;
    if ((ret = SetKeysSide(ssl, ENCRYPT_SIDE_ONLY)) != 0)
        return ret;

    WOLFSSL_LEAVE("SendTls13KeyUpdate", ret);
    WOLFSSL_END(WC_FUNC_KEY_UPDATE_SEND);

    return ret;
}

/* handle processing TLS v1.3 key_update (24) */
/* Parse and handle a TLS v1.3 KeyUpdate message.
 *
 * ssl       The SSL/TLS object.
 * input     The message buffer.
 * inOutIdx  On entry, the index into the message buffer of Finished.
 *           On exit, the index of byte after the Finished message and padding.
 * totalSz   The length of the current handshake message.
 * returns 0 on success and otherwise failure.
 */
static int DoTls13KeyUpdate(WOLFSSL* ssl, const byte* input, word32* inOutIdx,
                            word32 totalSz)
{
    int    ret;
    word32 i = *inOutIdx;

    WOLFSSL_START(WC_FUNC_KEY_UPDATE_DO);
    WOLFSSL_ENTER("DoTls13KeyUpdate");

    /* check against totalSz */
    if (OPAQUE8_LEN != totalSz)
        return BUFFER_E;

    switch (input[i]) {
        case update_not_requested:
            /* This message in response to any outstanding request. */
            ssl->keys.keyUpdateRespond = 0;
            ssl->keys.updateResponseReq = 0;
            break;
        case update_requested:
            /* New key update requiring a response. */
            ssl->keys.keyUpdateRespond = 1;
            break;
        default:
            return INVALID_PARAMETER;
    }

    /* Move index to byte after message. */
    *inOutIdx += totalSz;
    /* Always encrypted. */
    *inOutIdx += ssl->keys.padSz;

    /* Future traffic uses new decryption keys. */
    if ((ret = DeriveTls13Keys(ssl, update_traffic_key, DECRYPT_SIDE_ONLY, 1))
                                                                         != 0) {
        return ret;
    }
    if ((ret = SetKeysSide(ssl, DECRYPT_SIDE_ONLY)) != 0)
        return ret;

    if (ssl->keys.keyUpdateRespond)
        return SendTls13KeyUpdate(ssl);

    WOLFSSL_LEAVE("DoTls13KeyUpdate", ret);
    WOLFSSL_END(WC_FUNC_KEY_UPDATE_DO);

    return 0;
}

#ifdef WOLFSSL_EARLY_DATA
#ifndef NO_WOLFSSL_CLIENT
/* Send the TLS v1.3 EndOfEarlyData message to indicate that there will be no
 * more early application data.
 * The encryption key now changes to the pre-calculated handshake key.
 *
 * ssl  The SSL/TLS object.
 * returns 0 on success and otherwise failure.
 */
static int SendTls13EndOfEarlyData(WOLFSSL* ssl)
{
    byte*  output;
    int    ret;
    int    sendSz;
    word32 length;
    word32 idx = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;

    WOLFSSL_START(WC_FUNC_END_OF_EARLY_DATA_SEND);
    WOLFSSL_ENTER("SendTls13EndOfEarlyData");

    length = 0;
    sendSz = idx + length + MAX_MSG_EXTRA;

    /* Check buffers are big enough and grow if needed. */
    if ((ret = CheckAvailableSize(ssl, sendSz)) != 0)
        return ret;

    /* Get position in output buffer to write new message to. */
    output = ssl->buffers.outputBuffer.buffer +
             ssl->buffers.outputBuffer.length;

    /* Put the record and handshake headers on. */
    AddTls13Headers(output, length, end_of_early_data, ssl);

    /* This message is always encrypted. */
    sendSz = BuildTls13Message(ssl, output, sendSz, output + RECORD_HEADER_SZ,
                               idx - RECORD_HEADER_SZ, handshake, 1, 0, 0);
    if (sendSz < 0)
        return sendSz;

    ssl->buffers.outputBuffer.length += sendSz;

    if ((ret = SetKeysSide(ssl, ENCRYPT_SIDE_ONLY)) != 0)
        return ret;

    if (!ssl->options.groupMessages)
        ret = SendBuffered(ssl);

    WOLFSSL_LEAVE("SendTls13EndOfEarlyData", ret);
    WOLFSSL_END(WC_FUNC_END_OF_EARLY_DATA_SEND);

    return ret;
}
#endif /* !NO_WOLFSSL_CLIENT */

#ifndef NO_WOLFSSL_SERVER
/* handle processing of TLS 1.3 end_of_early_data (5) */
/* Parse the TLS v1.3 EndOfEarlyData message that indicates that there will be
 * no more early application data.
 * The decryption key now changes to the pre-calculated handshake key.
 *
 * ssl  The SSL/TLS object.
 * returns 0 on success and otherwise failure.
 */
static int DoTls13EndOfEarlyData(WOLFSSL* ssl, const byte* input,
                                 word32* inOutIdx, word32 size)
{
    int    ret;
    word32 begin = *inOutIdx;

    (void)input;

    WOLFSSL_START(WC_FUNC_END_OF_EARLY_DATA_DO);
    WOLFSSL_ENTER("DoTls13EndOfEarlyData");

    if ((*inOutIdx - begin) != size)
        return BUFFER_ERROR;

    if (ssl->earlyData == no_early_data) {
        WOLFSSL_MSG("EndOfEarlyData received unexpectedly");
        SendAlert(ssl, alert_fatal, unexpected_message);
        return OUT_OF_ORDER_E;
    }

    ssl->earlyData = done_early_data;

    /* Always encrypted. */
    *inOutIdx += ssl->keys.padSz;

    ret = SetKeysSide(ssl, DECRYPT_SIDE_ONLY);

    WOLFSSL_LEAVE("DoTls13EndOfEarlyData", ret);
    WOLFSSL_END(WC_FUNC_END_OF_EARLY_DATA_DO);

    return ret;
}
#endif /* !NO_WOLFSSL_SERVER */
#endif /* WOLFSSL_EARLY_DATA */

#ifndef NO_WOLFSSL_CLIENT
/* Handle a New Session Ticket handshake message.
 * Message contains the information required to perform resumption.
 *
 * ssl       The SSL/TLS object.
 * input     The message buffer.
 * inOutIdx  On entry, the index into the message buffer of Finished.
 *           On exit, the index of byte after the Finished message and padding.
 * size      The length of the current handshake message.
 * returns 0 on success, otherwise failure.
 */
static int DoTls13NewSessionTicket(WOLFSSL* ssl, const byte* input,
                                   word32* inOutIdx, word32 size)
{
#ifdef HAVE_SESSION_TICKET
    int    ret;
    word32 begin = *inOutIdx;
    word32 lifetime;
    word32 ageAdd;
    word16 length;
    word32 now;
    const byte* nonce;
    byte        nonceLength;

    WOLFSSL_START(WC_FUNC_NEW_SESSION_TICKET_DO);
    WOLFSSL_ENTER("DoTls13NewSessionTicket");

    /* Lifetime hint. */
    if ((*inOutIdx - begin) + SESSION_HINT_SZ > size)
        return BUFFER_ERROR;
    ato32(input + *inOutIdx, &lifetime);
    *inOutIdx += SESSION_HINT_SZ;
    if (lifetime > MAX_LIFETIME)
        return SERVER_HINT_ERROR;

    /* Age add. */
    if ((*inOutIdx - begin) + SESSION_ADD_SZ > size)
        return BUFFER_ERROR;
    ato32(input + *inOutIdx, &ageAdd);
    *inOutIdx += SESSION_ADD_SZ;

    /* Ticket nonce. */
    if ((*inOutIdx - begin) + 1 > size)
        return BUFFER_ERROR;
    nonceLength = input[*inOutIdx];
    if (nonceLength > MAX_TICKET_NONCE_SZ) {
        WOLFSSL_MSG("Nonce length not supported");
        return INVALID_PARAMETER;
    }
    *inOutIdx += 1;
    if ((*inOutIdx - begin) + nonceLength > size)
        return BUFFER_ERROR;
    nonce = input + *inOutIdx;
    *inOutIdx += nonceLength;

    /* Ticket length. */
    if ((*inOutIdx - begin) + LENGTH_SZ > size)
        return BUFFER_ERROR;
    ato16(input + *inOutIdx, &length);
    *inOutIdx += LENGTH_SZ;
    if ((*inOutIdx - begin) + length > size)
        return BUFFER_ERROR;

    if ((ret = SetTicket(ssl, input + *inOutIdx, length)) != 0)
        return ret;
    *inOutIdx += length;

    now = TimeNowInMilliseconds();
    if (now == (word32)GETTIME_ERROR)
        return now;
    /* Copy in ticket data (server identity). */
    ssl->timeout                = lifetime;
    ssl->session.timeout        = lifetime;
    ssl->session.cipherSuite0   = ssl->options.cipherSuite0;
    ssl->session.cipherSuite    = ssl->options.cipherSuite;
    ssl->session.ticketSeen     = now;
    ssl->session.ticketAdd      = ageAdd;
    #ifdef WOLFSSL_EARLY_DATA
    ssl->session.maxEarlyDataSz = ssl->options.maxEarlyDataSz;
    #endif
    ssl->session.ticketNonce.len = nonceLength;
    if (nonceLength > 0)
        XMEMCPY(&ssl->session.ticketNonce.data, nonce, nonceLength);
    ssl->session.namedGroup     = ssl->namedGroup;

    if ((*inOutIdx - begin) + EXTS_SZ > size)
        return BUFFER_ERROR;
    ato16(input + *inOutIdx, &length);
    *inOutIdx += EXTS_SZ;
    if ((*inOutIdx - begin) + length != size)
        return BUFFER_ERROR;
    #ifdef WOLFSSL_EARLY_DATA
    ret = TLSX_Parse(ssl, (byte *)input + (*inOutIdx), length, session_ticket,
                     NULL);
    if (ret != 0)
        return ret;
    #endif
    *inOutIdx += length;

    #ifndef NO_SESSION_CACHE
    AddSession(ssl);
    #endif

    /* Always encrypted. */
    *inOutIdx += ssl->keys.padSz;

    ssl->expect_session_ticket = 0;
#else
    (void)ssl;
    (void)input;

    WOLFSSL_ENTER("DoTls13NewSessionTicket");

    *inOutIdx += size + ssl->keys.padSz;
#endif /* HAVE_SESSION_TICKET */

    WOLFSSL_LEAVE("DoTls13NewSessionTicket", 0);
    WOLFSSL_END(WC_FUNC_NEW_SESSION_TICKET_DO);

    return 0;
}
#endif /* NO_WOLFSSL_CLIENT */

#ifndef NO_WOLFSSL_SERVER
    #ifdef HAVE_SESSION_TICKET

#ifdef WOLFSSL_TLS13_TICKET_BEFORE_FINISHED
/* Offset of the MAC size in the finished message. */
#define FINISHED_MSG_SIZE_OFFSET    3

/* Calculate the resumption secret which includes the unseen client finished
 * message.
 *
 * ssl  The SSL/TLS object.
 * returns 0 on success, otherwise failure.
 */
static int ExpectedResumptionSecret(WOLFSSL* ssl)
{
    int         ret;
    word32      finishedSz = 0;
    byte        mac[WC_MAX_DIGEST_SIZE];
    Digest      digest;
    static byte header[] = { 0x14, 0x00, 0x00, 0x00 };

    /* Copy the running hash so we can restore it after. */
    switch (ssl->specs.mac_algorithm) {
    #ifndef NO_SHA256
        case sha256_mac:
            ret = wc_Sha256Copy(&ssl->hsHashes->hashSha256, &digest.sha256);
            if (ret != 0)
                return ret;
            break;
    #endif
    #ifdef WOLFSSL_SHA384
        case sha384_mac:
            ret = wc_Sha384Copy(&ssl->hsHashes->hashSha384, &digest.sha384);
            if (ret != 0)
                return ret;
            break;
    #endif
    #ifdef WOLFSSL_TLS13_SHA512
        case sha512_mac:
            ret = wc_Sha512Copy(&ssl->hsHashes->hashSha512, &digest.sha512);
            if (ret != 0)
                return ret;
            break;
    #endif
    }

    /* Generate the Client's Finished message and hash it. */
    ret = BuildTls13HandshakeHmac(ssl, ssl->keys.client_write_MAC_secret, mac,
                                  &finishedSz);
    if (ret != 0)
        return ret;
    header[FINISHED_MSG_SIZE_OFFSET] = finishedSz;
#ifdef WOLFSSL_EARLY_DATA
    if (ssl->earlyData != no_early_data) {
        static byte endOfEarlyData[] = { 0x05, 0x00, 0x00, 0x00 };
        ret = HashRaw(ssl, endOfEarlyData, sizeof(endOfEarlyData));
        if (ret != 0)
            return ret;
    }
#endif
    if ((ret = HashRaw(ssl, header, sizeof(header))) != 0)
        return ret;
    if ((ret = HashRaw(ssl, mac, finishedSz)) != 0)
        return ret;

    if ((ret = DeriveResumptionSecret(ssl, ssl->session.masterSecret)) != 0)
        return ret;

    /* Restore the hash inline with currently seen messages. */
    switch (ssl->specs.mac_algorithm) {
    #ifndef NO_SHA256
        case sha256_mac:
            ret = wc_Sha256Copy(&digest.sha256, &ssl->hsHashes->hashSha256);
            if (ret != 0)
                return ret;
            break;
    #endif
    #ifdef WOLFSSL_SHA384
        case sha384_mac:
            ret = wc_Sha384Copy(&digest.sha384, &ssl->hsHashes->hashSha384);
            if (ret != 0)
                return ret;
            break;
    #endif
    #ifdef WOLFSSL_TLS13_SHA512
        case sha512_mac:
            ret = wc_Sha512Copy(&digest.sha512, &ssl->hsHashes->hashSha384);
            if (ret != 0)
                return ret;
            break;
    #endif
    }

    return ret;
}
#endif

/* Send New Session Ticket handshake message.
 * Message contains the information required to perform resumption.
 *
 * ssl  The SSL/TLS object.
 * returns 0 on success, otherwise failure.
 */
static int SendTls13NewSessionTicket(WOLFSSL* ssl)
{
    byte*  output;
    int    ret;
    int    sendSz;
    word16 extSz;
    word32 length;
    word32 idx = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;

    WOLFSSL_START(WC_FUNC_NEW_SESSION_TICKET_SEND);
    WOLFSSL_ENTER("SendTls13NewSessionTicket");

#ifdef WOLFSSL_TLS13_TICKET_BEFORE_FINISHED
    if (!ssl->msgsReceived.got_finished) {
        if ((ret = ExpectedResumptionSecret(ssl)) != 0)
            return ret;
    }
#endif

    /* Start ticket nonce at 0 and go up to 255. */
    if (ssl->session.ticketNonce.len == 0) {
        ssl->session.ticketNonce.len = DEF_TICKET_NONCE_SZ;
        ssl->session.ticketNonce.data[0] = 0;
    }
    else
        ssl->session.ticketNonce.data[0]++;

    if (!ssl->options.noTicketTls13) {
        if ((ret = CreateTicket(ssl)) != 0)
            return ret;
    }

#ifdef WOLFSSL_EARLY_DATA
    ssl->session.maxEarlyDataSz = ssl->options.maxEarlyDataSz;
    if (ssl->session.maxEarlyDataSz > 0)
        TLSX_EarlyData_Use(ssl, ssl->session.maxEarlyDataSz);
    extSz = 0;
    ret = TLSX_GetResponseSize(ssl, session_ticket, &extSz);
    if (ret != 0)
        return ret;
#else
    extSz = EXTS_SZ;
#endif

    /* Lifetime | Age Add | Ticket | Extensions */
    length = SESSION_HINT_SZ + SESSION_ADD_SZ + LENGTH_SZ +
             ssl->session.ticketLen + extSz;
    /* Nonce */
    length += TICKET_NONCE_LEN_SZ + DEF_TICKET_NONCE_SZ;
    sendSz = idx + length + MAX_MSG_EXTRA;

    /* Check buffers are big enough and grow if needed. */
    if ((ret = CheckAvailableSize(ssl, sendSz)) != 0)
        return ret;

    /* Get position in output buffer to write new message to. */
    output = ssl->buffers.outputBuffer.buffer +
             ssl->buffers.outputBuffer.length;

    /* Put the record and handshake headers on. */
    AddTls13Headers(output, length, session_ticket, ssl);

    /* Lifetime hint */
    c32toa(ssl->ctx->ticketHint, output + idx);
    idx += SESSION_HINT_SZ;
    /* Age add - obfuscator */
    c32toa(ssl->session.ticketAdd, output + idx);
    idx += SESSION_ADD_SZ;

    output[idx++] = ssl->session.ticketNonce.len;
    output[idx++] = ssl->session.ticketNonce.data[0];

    /* length */
    c16toa(ssl->session.ticketLen, output + idx);
    idx += LENGTH_SZ;
    /* ticket */
    XMEMCPY(output + idx, ssl->session.ticket, ssl->session.ticketLen);
    idx += ssl->session.ticketLen;

#ifdef WOLFSSL_EARLY_DATA
    extSz = 0;
    ret = TLSX_WriteResponse(ssl, output + idx, session_ticket, &extSz);
    if (ret != 0)
        return ret;
    idx += extSz;
#else
    /* No extension support - empty extensions. */
    c16toa(0, output + idx);
    idx += EXTS_SZ;
#endif

    ssl->options.haveSessionId = 1;

#ifndef NO_SESSION_CACHE
    AddSession(ssl);
#endif

    /* This message is always encrypted. */
    sendSz = BuildTls13Message(ssl, output, sendSz, output + RECORD_HEADER_SZ,
                               idx - RECORD_HEADER_SZ, handshake, 0, 0, 0);
    if (sendSz < 0)
        return sendSz;

    ssl->buffers.outputBuffer.length += sendSz;

    if (!ssl->options.groupMessages)
        ret = SendBuffered(ssl);

    WOLFSSL_LEAVE("SendTls13NewSessionTicket", 0);
    WOLFSSL_END(WC_FUNC_NEW_SESSION_TICKET_SEND);

    return ret;
}
    #endif /* HAVE_SESSION_TICKET */
#endif /* NO_WOLFSSL_SERVER */

/* Make sure no duplicates, no fast forward, or other problems
 *
 * ssl   The SSL/TLS object.
 * type  Type of handshake message received.
 * returns 0 on success, otherwise failure.
 */
static int SanityCheckTls13MsgReceived(WOLFSSL* ssl, byte type)
{
    /* verify not a duplicate, mark received, check state */
    switch (type) {

#ifndef NO_WOLFSSL_SERVER
        case client_hello:
        #ifndef NO_WOLFSSL_CLIENT
            if (ssl->options.side == WOLFSSL_CLIENT_END) {
                WOLFSSL_MSG("ClientHello received by client");
                return OUT_OF_ORDER_E;
            }
        #endif
            if (ssl->options.clientState >= CLIENT_HELLO_COMPLETE) {
                WOLFSSL_MSG("ClientHello received out of order");
                return OUT_OF_ORDER_E;
            }
            if (ssl->msgsReceived.got_client_hello == 2) {
                WOLFSSL_MSG("Too many ClientHello received");
                return DUPLICATE_MSG_E;
            }
            ssl->msgsReceived.got_client_hello++;

            break;
#endif

#ifndef NO_WOLFSSL_CLIENT
        case server_hello:
        #ifndef NO_WOLFSSL_SERVER
            if (ssl->options.side == WOLFSSL_SERVER_END) {
                WOLFSSL_MSG("ServerHello received by server");
                return OUT_OF_ORDER_E;
            }
        #endif
            if (ssl->msgsReceived.got_server_hello == 2) {
                WOLFSSL_MSG("Duplicate ServerHello received");
                return DUPLICATE_MSG_E;
            }
            ssl->msgsReceived.got_server_hello++;

            break;
#endif

#ifndef NO_WOLFSSL_CLIENT
        case session_ticket:
        #ifndef NO_WOLFSSL_SERVER
            if (ssl->options.side == WOLFSSL_SERVER_END) {
                WOLFSSL_MSG("NewSessionTicket received by server");
                return OUT_OF_ORDER_E;
            }
        #endif
            if (ssl->options.clientState < CLIENT_FINISHED_COMPLETE) {
                WOLFSSL_MSG("NewSessionTicket received out of order");
                return OUT_OF_ORDER_E;
            }
            ssl->msgsReceived.got_session_ticket = 1;

            break;
#endif

#ifndef NO_WOLFSSL_SERVER
    #ifdef WOLFSSL_EARLY_DATA
        case end_of_early_data:
        #ifndef NO_WOLFSSL_CLIENT
            if (ssl->options.side == WOLFSSL_CLIENT_END) {
                WOLFSSL_MSG("EndOfEarlyData received by client");
                return OUT_OF_ORDER_E;
            }
        #endif
            if (ssl->options.serverState < SERVER_FINISHED_COMPLETE) {
                WOLFSSL_MSG("EndOfEarlyData received out of order");
                return OUT_OF_ORDER_E;
            }
            if (ssl->options.clientState >= CLIENT_FINISHED_COMPLETE) {
                WOLFSSL_MSG("EndOfEarlyData received out of order");
                return OUT_OF_ORDER_E;
            }
            if (ssl->msgsReceived.got_end_of_early_data == 1) {
                WOLFSSL_MSG("Too many EndOfEarlyData received");
                return DUPLICATE_MSG_E;
            }
            ssl->msgsReceived.got_end_of_early_data++;

            break;
    #endif
#endif

#ifndef NO_WOLFSSL_CLIENT
        case encrypted_extensions:
        #ifndef NO_WOLFSSL_SERVER
            if (ssl->options.side == WOLFSSL_SERVER_END) {
                WOLFSSL_MSG("EncryptedExtensions received by server");
                return OUT_OF_ORDER_E;
            }
        #endif
            if (ssl->options.serverState != SERVER_HELLO_COMPLETE) {
                WOLFSSL_MSG("EncryptedExtensions received out of order");
                return OUT_OF_ORDER_E;
            }
            if (ssl->msgsReceived.got_encrypted_extensions) {
                WOLFSSL_MSG("Duplicate EncryptedExtensions received");
                return DUPLICATE_MSG_E;
            }
            ssl->msgsReceived.got_encrypted_extensions = 1;

            break;
#endif

        case certificate:
    #ifndef NO_WOLFSSL_CLIENT
            if (ssl->options.side == WOLFSSL_CLIENT_END &&
                ssl->options.serverState !=
                                         SERVER_ENCRYPTED_EXTENSIONS_COMPLETE) {
                WOLFSSL_MSG("Certificate received out of order - Client");
                return OUT_OF_ORDER_E;
            }
        #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
            /* Server's authenticating with PSK must not send this. */
            if (ssl->options.side == WOLFSSL_CLIENT_END &&
                             ssl->options.serverState == SERVER_CERT_COMPLETE &&
                             ssl->arrays->psk_keySz != 0) {
                WOLFSSL_MSG("Certificate received while using PSK");
                return SANITY_MSG_E;
            }
        #endif
    #endif
    #ifndef NO_WOLFSSL_SERVER
            if (ssl->options.side == WOLFSSL_SERVER_END &&
                ssl->options.serverState < SERVER_FINISHED_COMPLETE) {
                WOLFSSL_MSG("Certificate received out of order - Server");
                return OUT_OF_ORDER_E;
            }
    #endif
            if (ssl->msgsReceived.got_certificate) {
                WOLFSSL_MSG("Duplicate Certificate received");
                return DUPLICATE_MSG_E;
            }
            ssl->msgsReceived.got_certificate = 1;

            break;

#ifndef NO_WOLFSSL_CLIENT
        case certificate_request:
        #ifndef NO_WOLFSSL_SERVER
            if (ssl->options.side == WOLFSSL_SERVER_END) {
                WOLFSSL_MSG("CertificateRequest received by server");
                return OUT_OF_ORDER_E;
            }
        #endif
        #ifndef WOLFSSL_POST_HANDSHAKE_AUTH
            if (ssl->options.serverState !=
                                         SERVER_ENCRYPTED_EXTENSIONS_COMPLETE) {
                WOLFSSL_MSG("CertificateRequest received out of order");
                return OUT_OF_ORDER_E;
            }
        #else
            if (ssl->options.serverState !=
                                         SERVER_ENCRYPTED_EXTENSIONS_COMPLETE &&
                       (ssl->options.serverState != SERVER_FINISHED_COMPLETE ||
                        ssl->options.clientState != CLIENT_FINISHED_COMPLETE)) {
                WOLFSSL_MSG("CertificateRequest received out of order");
                return OUT_OF_ORDER_E;
            }
        #endif
        #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
            /* Server's authenticating with PSK must not send this. */
            if (ssl->options.serverState ==
                                         SERVER_ENCRYPTED_EXTENSIONS_COMPLETE &&
                                                  ssl->arrays->psk_keySz != 0) {
                WOLFSSL_MSG("CertificateRequset received while using PSK");
                return SANITY_MSG_E;
            }
        #endif
        #ifndef WOLFSSL_POST_HANDSHAKE_AUTH
            if (ssl->msgsReceived.got_certificate_request) {
                WOLFSSL_MSG("Duplicate CertificateRequest received");
                return DUPLICATE_MSG_E;
            }
        #endif
            ssl->msgsReceived.got_certificate_request = 1;

            break;
#endif

        case certificate_verify:
    #ifndef NO_WOLFSSL_CLIENT
            if (ssl->options.side == WOLFSSL_CLIENT_END) {
                if (ssl->options.serverState != SERVER_CERT_COMPLETE) {
                    WOLFSSL_MSG("No Cert before CertVerify");
                    return OUT_OF_ORDER_E;
                }
            #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
                /* Server's authenticating with PSK must not send this. */
                if (ssl->options.serverState == SERVER_CERT_COMPLETE &&
                                                  ssl->arrays->psk_keySz != 0) {
                    WOLFSSL_MSG("CertificateVerify received while using PSK");
                    return SANITY_MSG_E;
                }
            #endif
            }
    #endif
    #ifndef NO_WOLFSSL_SERVER
            if (ssl->options.side == WOLFSSL_SERVER_END) {
                if (ssl->options.serverState < SERVER_FINISHED_COMPLETE) {
                    WOLFSSL_MSG("CertificateVerify received out of order");
                    return OUT_OF_ORDER_E;
                }
                if (ssl->options.clientState < CLIENT_HELLO_COMPLETE) {
                    WOLFSSL_MSG("CertificateVerify before ClientHello done");
                    return OUT_OF_ORDER_E;
                }
                if (!ssl->msgsReceived.got_certificate) {
                    WOLFSSL_MSG("No Cert before CertificateVerify");
                    return OUT_OF_ORDER_E;
                }
            }
    #endif
            if (ssl->msgsReceived.got_certificate_verify) {
                WOLFSSL_MSG("Duplicate CertificateVerify received");
                return DUPLICATE_MSG_E;
            }
            ssl->msgsReceived.got_certificate_verify = 1;

            break;

        case finished:
        #ifndef NO_WOLFSSL_CLIENT
            if (ssl->options.side == WOLFSSL_CLIENT_END) {
                if (ssl->options.clientState < CLIENT_HELLO_COMPLETE) {
                    WOLFSSL_MSG("Finished received out of order");
                    return OUT_OF_ORDER_E;
                }
                /* Must have seen certificate and verify from server except when
                 * using PSK. */
            #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
                if (ssl->arrays->psk_keySz != 0) {
                    if (ssl->options.serverState !=
                                         SERVER_ENCRYPTED_EXTENSIONS_COMPLETE) {
                        WOLFSSL_MSG("Finished received out of order");
                        return OUT_OF_ORDER_E;
                    }
                }
                else
            #endif
                if (ssl->options.serverState != SERVER_CERT_VERIFY_COMPLETE) {
                    WOLFSSL_MSG("Finished received out of order");
                    return OUT_OF_ORDER_E;
                }
            }
        #endif
        #ifndef NO_WOLFSSL_SERVER
            if (ssl->options.side == WOLFSSL_SERVER_END) {
                if (ssl->options.serverState != SERVER_FINISHED_COMPLETE) {
                    WOLFSSL_MSG("Finished received out of order");
                    return OUT_OF_ORDER_E;
                }
                if (ssl->options.clientState < CLIENT_HELLO_COMPLETE) {
                    WOLFSSL_MSG("Finished received out of order");
                    return OUT_OF_ORDER_E;
                }
            #ifdef WOLFSSL_EARLY_DATA
                if (ssl->earlyData == process_early_data) {
                    return OUT_OF_ORDER_E;
                }
            #endif
            }
        #endif
            if (ssl->msgsReceived.got_finished) {
                WOLFSSL_MSG("Duplicate Finished received");
                return DUPLICATE_MSG_E;
            }
            ssl->msgsReceived.got_finished = 1;

            break;

        case key_update:
            if (!ssl->msgsReceived.got_finished) {
                WOLFSSL_MSG("No KeyUpdate before Finished");
                return OUT_OF_ORDER_E;
            }
            break;

        default:
            WOLFSSL_MSG("Unknown message type");
            return SANITY_MSG_E;
    }

    return 0;
}

/* Handle a type of handshake message that has been received.
 *
 * ssl       The SSL/TLS object.
 * input     The message buffer.
 * inOutIdx  On entry, the index into the buffer of the current message.
 *           On exit, the index into the buffer of the next message.
 * size      The length of the current handshake message.
 * totalSz   Length of remaining data in the message buffer.
 * returns 0 on success and otherwise failure.
 */
int DoTls13HandShakeMsgType(WOLFSSL* ssl, byte* input, word32* inOutIdx,
                            byte type, word32 size, word32 totalSz)
{
    int ret = 0;
    word32 inIdx = *inOutIdx;

    (void)totalSz;

    WOLFSSL_ENTER("DoTls13HandShakeMsgType");

    /* make sure we can read the message */
    if (*inOutIdx + size > totalSz)
        return INCOMPLETE_DATA;

    /* sanity check msg received */
    if ((ret = SanityCheckTls13MsgReceived(ssl, type)) != 0) {
        WOLFSSL_MSG("Sanity Check on handshake message type received failed");
        SendAlert(ssl, alert_fatal, unexpected_message);
        return ret;
    }

#ifdef WOLFSSL_CALLBACKS
    /* add name later, add on record and handshake header part back on */
    if (ssl->toInfoOn) {
        int add = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
        AddPacketInfo(ssl, 0, handshake, input + *inOutIdx - add,
                      size + add, READ_PROTO, ssl->heap);
        AddLateRecordHeader(&ssl->curRL, &ssl->timeoutInfo);
    }
#endif

    if (ssl->options.handShakeState == HANDSHAKE_DONE &&
            type != session_ticket && type != certificate_request &&
            type != certificate && type != key_update) {
        WOLFSSL_MSG("HandShake message after handshake complete");
        SendAlert(ssl, alert_fatal, unexpected_message);
        return OUT_OF_ORDER_E;
    }

    if (ssl->options.side == WOLFSSL_CLIENT_END &&
               ssl->options.serverState == NULL_STATE &&
               type != server_hello && type != hello_retry_request) {
        WOLFSSL_MSG("First server message not server hello");
        SendAlert(ssl, alert_fatal, unexpected_message);
        return OUT_OF_ORDER_E;
    }

    if (ssl->options.side == WOLFSSL_SERVER_END &&
               ssl->options.clientState == NULL_STATE && type != client_hello) {
        WOLFSSL_MSG("First client message not client hello");
        SendAlert(ssl, alert_fatal, unexpected_message);
        return OUT_OF_ORDER_E;
    }

    /* above checks handshake state */
    switch (type) {
#ifndef NO_WOLFSSL_CLIENT
    /* Messages only received by client. */
    case server_hello:
        WOLFSSL_MSG("processing server hello");
        ret = DoTls13ServerHello(ssl, input, inOutIdx, size, &type);
    #if !defined(WOLFSSL_NO_CLIENT_AUTH) && \
               ((defined(HAVE_ED25519) && !defined(NO_ED25519_CLIENT_AUTH)) || \
                (defined(HAVE_ED448) && !defined(NO_ED448_CLIENT_AUTH)))
        if (ssl->options.resuming || !IsAtLeastTLSv1_2(ssl) ||
                                               IsAtLeastTLSv1_3(ssl->version)) {
            ssl->options.cacheMessages = 0;
            if ((ssl->hsHashes != NULL) && (ssl->hsHashes->messages != NULL)) {
                XFREE(ssl->hsHashes->messages, ssl->heap, DYNAMIC_TYPE_HASHES);
                ssl->hsHashes->messages = NULL;
            }
        }
    #endif
        break;

    case encrypted_extensions:
        WOLFSSL_MSG("processing encrypted extensions");
        ret = DoTls13EncryptedExtensions(ssl, input, inOutIdx, size);
        break;

    #ifndef NO_CERTS
    case certificate_request:
        WOLFSSL_MSG("processing certificate request");
        ret = DoTls13CertificateRequest(ssl, input, inOutIdx, size);
        break;
    #endif

    case session_ticket:
        WOLFSSL_MSG("processing new session ticket");
        ret = DoTls13NewSessionTicket(ssl, input, inOutIdx, size);
        break;
#endif /* !NO_WOLFSSL_CLIENT */

#ifndef NO_WOLFSSL_SERVER
    /* Messages only received by server. */
    case client_hello:
        WOLFSSL_MSG("processing client hello");
        ret = DoTls13ClientHello(ssl, input, inOutIdx, size);
        break;

    #ifdef WOLFSSL_EARLY_DATA
    case end_of_early_data:
        WOLFSSL_MSG("processing end of early data");
        ret = DoTls13EndOfEarlyData(ssl, input, inOutIdx, size);
        break;
    #endif
#endif /* !NO_WOLFSSL_SERVER */

    /* Messages received by both client and server. */
#ifndef NO_CERTS
    case certificate:
        WOLFSSL_MSG("processing certificate");
        ret = DoTls13Certificate(ssl, input, inOutIdx, size);
        break;
#endif

#if !defined(NO_RSA) || defined(HAVE_ECC) || defined(HAVE_ED25519) || \
                                                             defined(HAVE_ED448)
    case certificate_verify:
        WOLFSSL_MSG("processing certificate verify");
        ret = DoTls13CertificateVerify(ssl, input, inOutIdx, size);
        break;
#endif /* !NO_RSA || HAVE_ECC */

    case finished:
        WOLFSSL_MSG("processing finished");
        ret = DoTls13Finished(ssl, input, inOutIdx, size, totalSz, NO_SNIFF);
        break;

    case key_update:
        WOLFSSL_MSG("processing finished");
        ret = DoTls13KeyUpdate(ssl, input, inOutIdx, size);
        break;

    default:
        WOLFSSL_MSG("Unknown handshake message type");
        ret = UNKNOWN_HANDSHAKE_TYPE;
        break;
    }

    /* reset error */
    if (ret == 0 && ssl->error == WC_PENDING_E)
        ssl->error = 0;

    if (ret == 0 && type != client_hello && type != session_ticket &&
                                                           type != key_update) {
        ret = HashInput(ssl, input + inIdx, size);
    }
    if (ret == 0 && ssl->buffers.inputBuffer.dynamicFlag) {
        ShrinkInputBuffer(ssl, NO_FORCED_FREE);
    }

    if (ret == BUFFER_ERROR || ret == MISSING_HANDSHAKE_DATA)
        SendAlert(ssl, alert_fatal, decode_error);
    else if (ret == EXT_NOT_ALLOWED || ret == PEER_KEY_ERROR ||
                        ret == ECC_PEERKEY_ERROR || ret == BAD_KEY_SHARE_DATA ||
                        ret == PSK_KEY_ERROR || ret == INVALID_PARAMETER) {
        SendAlert(ssl, alert_fatal, illegal_parameter);
    }

    if (ret == 0 && ssl->options.tls1_3) {
        /* Need to hash input message before deriving secrets. */
    #ifndef NO_WOLFSSL_CLIENT
        if (ssl->options.side == WOLFSSL_CLIENT_END) {
            if (type == server_hello) {
                if ((ret = DeriveEarlySecret(ssl)) != 0)
                    return ret;
                if ((ret = DeriveHandshakeSecret(ssl)) != 0)
                    return ret;

                if ((ret = DeriveTls13Keys(ssl, handshake_key,
                                           ENCRYPT_AND_DECRYPT_SIDE, 1)) != 0) {
                    return ret;
                }
        #ifdef WOLFSSL_EARLY_DATA
                if ((ret = SetKeysSide(ssl, DECRYPT_SIDE_ONLY)) != 0)
                    return ret;
        #else
                if ((ret = SetKeysSide(ssl, ENCRYPT_AND_DECRYPT_SIDE)) != 0)
                    return ret;
        #endif
            }

            if (type == finished) {
                if ((ret = DeriveMasterSecret(ssl)) != 0)
                    return ret;
        #ifdef WOLFSSL_EARLY_DATA
                if ((ret = DeriveTls13Keys(ssl, traffic_key,
                                       ENCRYPT_AND_DECRYPT_SIDE,
                                       ssl->earlyData == no_early_data)) != 0) {
                    return ret;
                }
        #else
                if ((ret = DeriveTls13Keys(ssl, traffic_key,
                                           ENCRYPT_AND_DECRYPT_SIDE, 1)) != 0) {
                    return ret;
                }
        #endif
            }
        #ifdef WOLFSSL_POST_HANDSHAKE_AUTH
            if (type == certificate_request &&
                                ssl->options.handShakeState == HANDSHAKE_DONE) {
                /* reset handshake states */
                ssl->options.clientState = CLIENT_HELLO_COMPLETE;
                ssl->options.connectState  = FIRST_REPLY_DONE;
                ssl->options.handShakeState = CLIENT_HELLO_COMPLETE;

                if (wolfSSL_connect_TLSv13(ssl) != SSL_SUCCESS)
                    ret = POST_HAND_AUTH_ERROR;
            }
        #endif
        }
    #endif /* NO_WOLFSSL_CLIENT */

#ifndef NO_WOLFSSL_SERVER
    #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
        if (ssl->options.side == WOLFSSL_SERVER_END && type == finished) {
            ret = DeriveResumptionSecret(ssl, ssl->session.masterSecret);
            if (ret != 0)
                return ret;
        }
    #endif
#endif /* NO_WOLFSSL_SERVER */
    }

#ifdef WOLFSSL_ASYNC_CRYPT
    /* if async, offset index so this msg will be processed again */
    if (ret == WC_PENDING_E && *inOutIdx > 0) {
        *inOutIdx -= HANDSHAKE_HEADER_SZ;
    }
#endif

    WOLFSSL_LEAVE("DoTls13HandShakeMsgType()", ret);
    return ret;
}


/* Handle a handshake message that has been received.
 *
 * ssl       The SSL/TLS object.
 * input     The message buffer.
 * inOutIdx  On entry, the index into the buffer of the current message.
 *           On exit, the index into the buffer of the next message.
 * totalSz   Length of remaining data in the message buffer.
 * returns 0 on success and otherwise failure.
 */
int DoTls13HandShakeMsg(WOLFSSL* ssl, byte* input, word32* inOutIdx,
                        word32 totalSz)
{
    int    ret = 0;
    word32 inputLength;
    byte   type;
    word32 size = 0;

    WOLFSSL_ENTER("DoTls13HandShakeMsg()");

    if (ssl->arrays == NULL) {


        if (GetHandshakeHeader(ssl, input, inOutIdx, &type, &size,
                                                                totalSz) != 0) {
            SendAlert(ssl, alert_fatal, unexpected_message);
            return PARSE_ERROR;
        }

        return DoTls13HandShakeMsgType(ssl, input, inOutIdx, type, size,
                                       totalSz);
    }

    inputLength = ssl->buffers.inputBuffer.length - *inOutIdx - ssl->keys.padSz;

    /* If there is a pending fragmented handshake message,
     * pending message size will be non-zero. */
    if (ssl->arrays->pendingMsgSz == 0) {

        if (GetHandshakeHeader(ssl,input, inOutIdx, &type, &size, totalSz) != 0)
            return PARSE_ERROR;

        /* Cap the maximum size of a handshake message to something reasonable.
         * By default is the maximum size of a certificate message assuming
         * nine 2048-bit RSA certificates in the chain. */
        if (size > MAX_HANDSHAKE_SZ) {
            WOLFSSL_MSG("Handshake message too large");
            return HANDSHAKE_SIZE_ERROR;
        }

        /* size is the size of the certificate message payload */
        if (inputLength - HANDSHAKE_HEADER_SZ < size) {
            ssl->arrays->pendingMsgType = type;
            ssl->arrays->pendingMsgSz = size + HANDSHAKE_HEADER_SZ;
            ssl->arrays->pendingMsg = (byte*)XMALLOC(size + HANDSHAKE_HEADER_SZ,
                                                     ssl->heap,
                                                     DYNAMIC_TYPE_ARRAYS);
            if (ssl->arrays->pendingMsg == NULL)
                return MEMORY_E;
            XMEMCPY(ssl->arrays->pendingMsg,
                    input + *inOutIdx - HANDSHAKE_HEADER_SZ,
                    inputLength);
            ssl->arrays->pendingMsgOffset = inputLength;
            *inOutIdx += inputLength + ssl->keys.padSz - HANDSHAKE_HEADER_SZ;
            return 0;
        }

        ret = DoTls13HandShakeMsgType(ssl, input, inOutIdx, type, size,
                                      totalSz);
    }
    else {
        if (inputLength + ssl->arrays->pendingMsgOffset >
                                                    ssl->arrays->pendingMsgSz) {
            inputLength = ssl->arrays->pendingMsgSz -
                                                  ssl->arrays->pendingMsgOffset;
        }
        XMEMCPY(ssl->arrays->pendingMsg + ssl->arrays->pendingMsgOffset,
                input + *inOutIdx, inputLength);
        ssl->arrays->pendingMsgOffset += inputLength;
        *inOutIdx += inputLength + ssl->keys.padSz;

        if (ssl->arrays->pendingMsgOffset == ssl->arrays->pendingMsgSz)
        {
            word32 idx = 0;
            ret = DoTls13HandShakeMsgType(ssl,
                                ssl->arrays->pendingMsg + HANDSHAKE_HEADER_SZ,
                                &idx, ssl->arrays->pendingMsgType,
                                ssl->arrays->pendingMsgSz - HANDSHAKE_HEADER_SZ,
                                ssl->arrays->pendingMsgSz);
        #ifdef WOLFSSL_ASYNC_CRYPT
            if (ret == WC_PENDING_E) {
                /* setup to process fragment again */
                ssl->arrays->pendingMsgOffset -= inputLength;
                *inOutIdx -= inputLength + ssl->keys.padSz;
            }
            else
        #endif
            {
                XFREE(ssl->arrays->pendingMsg, ssl->heap, DYNAMIC_TYPE_ARRAYS);
                ssl->arrays->pendingMsg = NULL;
                ssl->arrays->pendingMsgSz = 0;
            }
        }
    }

    WOLFSSL_LEAVE("DoTls13HandShakeMsg()", ret);
    return ret;
}

#ifndef NO_WOLFSSL_CLIENT

/* The client connecting to the server.
 * The protocol version is expecting to be TLS v1.3.
 * If the server downgrades, and older versions of the protocol are compiled
 * in, the client will fallback to wolfSSL_connect().
 * Please see note at top of README if you get an error from connect.
 *
 * ssl  The SSL/TLS object.
 * returns WOLFSSL_SUCCESS on successful handshake, WOLFSSL_FATAL_ERROR when
 * unrecoverable error occurs and 0 otherwise.
 * For more error information use wolfSSL_get_error().
 */
int wolfSSL_connect_TLSv13(WOLFSSL* ssl)
{
    WOLFSSL_ENTER("wolfSSL_connect_TLSv13()");

    #ifdef HAVE_ERRNO_H
    errno = 0;
    #endif

    if (ssl->options.side != WOLFSSL_CLIENT_END) {
        WOLFSSL_ERROR(ssl->error = SIDE_ERROR);
        return WOLFSSL_FATAL_ERROR;
    }

    if (ssl->buffers.outputBuffer.length > 0
    #ifdef WOLFSSL_ASYNC_CRYPT
        /* do not send buffered or advance state if last error was an
            async pending operation */
        && ssl->error != WC_PENDING_E
    #endif
    ) {
        if ((ssl->error = SendBuffered(ssl)) == 0) {
            /* fragOffset is non-zero when sending fragments. On the last
             * fragment, fragOffset is zero again, and the state can be
             * advanced. */
            if (ssl->fragOffset == 0) {
                ssl->options.connectState++;
                WOLFSSL_MSG("connect state: "
                            "Advanced from last buffered fragment send");
            }
            else {
                WOLFSSL_MSG("connect state: "
                            "Not advanced, more fragments to send");
            }
        }
        else {
            WOLFSSL_ERROR(ssl->error);
            return WOLFSSL_FATAL_ERROR;
        }
    }

    switch (ssl->options.connectState) {

        case CONNECT_BEGIN:
            /* Always send client hello first. */
            if ((ssl->error = SendTls13ClientHello(ssl)) != 0) {
                WOLFSSL_ERROR(ssl->error);
                return WOLFSSL_FATAL_ERROR;
            }

            ssl->options.connectState = CLIENT_HELLO_SENT;
            WOLFSSL_MSG("connect state: CLIENT_HELLO_SENT");
    #ifdef WOLFSSL_EARLY_DATA
            if (ssl->earlyData != no_early_data) {
        #if defined(WOLFSSL_TLS13_MIDDLEBOX_COMPAT)
                if ((ssl->error = SendChangeCipher(ssl)) != 0) {
                    WOLFSSL_ERROR(ssl->error);
                    return WOLFSSL_FATAL_ERROR;
                }
                ssl->options.sentChangeCipher = 1;
        #endif
                ssl->options.handShakeState = CLIENT_HELLO_COMPLETE;
                return WOLFSSL_SUCCESS;
            }
    #endif
            FALL_THROUGH;

        case CLIENT_HELLO_SENT:
            /* Get the response/s from the server. */
            while (ssl->options.serverState <
                                          SERVER_HELLO_RETRY_REQUEST_COMPLETE) {
                if ((ssl->error = ProcessReply(ssl)) < 0) {
                    WOLFSSL_ERROR(ssl->error);
                    return WOLFSSL_FATAL_ERROR;
                }
            }

            ssl->options.connectState = HELLO_AGAIN;
            WOLFSSL_MSG("connect state: HELLO_AGAIN");
            FALL_THROUGH;

        case HELLO_AGAIN:
            if (ssl->options.certOnly)
                return WOLFSSL_SUCCESS;

            if (!ssl->options.tls1_3) {
    #ifndef WOLFSSL_NO_TLS12
                if (ssl->options.downgrade)
                    return wolfSSL_connect(ssl);
    #endif

                WOLFSSL_MSG("Client using higher version, fatal error");
                return VERSION_ERROR;
            }

            if (ssl->options.serverState ==
                                          SERVER_HELLO_RETRY_REQUEST_COMPLETE) {
        #if defined(WOLFSSL_TLS13_MIDDLEBOX_COMPAT)
                if (!ssl->options.sentChangeCipher) {
                    if ((ssl->error = SendChangeCipher(ssl)) != 0) {
                        WOLFSSL_ERROR(ssl->error);
                        return WOLFSSL_FATAL_ERROR;
                    }
                    ssl->options.sentChangeCipher = 1;
                }
        #endif
                /* Try again with different security parameters. */
                if ((ssl->error = SendTls13ClientHello(ssl)) != 0) {
                    WOLFSSL_ERROR(ssl->error);
                    return WOLFSSL_FATAL_ERROR;
                }
            }

            ssl->options.connectState = HELLO_AGAIN_REPLY;
            WOLFSSL_MSG("connect state: HELLO_AGAIN_REPLY");
            FALL_THROUGH;

        case HELLO_AGAIN_REPLY:
            /* Get the response/s from the server. */
            while (ssl->options.serverState < SERVER_FINISHED_COMPLETE) {
                if ((ssl->error = ProcessReply(ssl)) < 0) {
                    WOLFSSL_ERROR(ssl->error);
                    return WOLFSSL_FATAL_ERROR;
                }
            }

            ssl->options.connectState = FIRST_REPLY_DONE;
            WOLFSSL_MSG("connect state: FIRST_REPLY_DONE");
            FALL_THROUGH;

        case FIRST_REPLY_DONE:
        #ifdef WOLFSSL_EARLY_DATA
            if (ssl->earlyData != no_early_data) {
                if ((ssl->error = SendTls13EndOfEarlyData(ssl)) != 0) {
                    WOLFSSL_ERROR(ssl->error);
                    return WOLFSSL_FATAL_ERROR;
                }
                WOLFSSL_MSG("sent: end_of_early_data");
            }
        #endif

            ssl->options.connectState = FIRST_REPLY_FIRST;
            WOLFSSL_MSG("connect state: FIRST_REPLY_FIRST");
            FALL_THROUGH;

        case FIRST_REPLY_FIRST:
        #if defined(WOLFSSL_TLS13_MIDDLEBOX_COMPAT)
            if (!ssl->options.sentChangeCipher) {
                if ((ssl->error = SendChangeCipher(ssl)) != 0) {
                    WOLFSSL_ERROR(ssl->error);
                    return WOLFSSL_FATAL_ERROR;
                }
                ssl->options.sentChangeCipher = 1;
            }
        #endif

            ssl->options.connectState = FIRST_REPLY_SECOND;
            WOLFSSL_MSG("connect state: FIRST_REPLY_SECOND");
            FALL_THROUGH;

        case FIRST_REPLY_SECOND:
        #ifndef NO_CERTS
            if (!ssl->options.resuming && ssl->options.sendVerify) {
                ssl->error = SendTls13Certificate(ssl);
                if (ssl->error != 0) {
                    WOLFSSL_ERROR(ssl->error);
                    return WOLFSSL_FATAL_ERROR;
                }
                WOLFSSL_MSG("sent: certificate");
            }
        #endif

            ssl->options.connectState = FIRST_REPLY_THIRD;
            WOLFSSL_MSG("connect state: FIRST_REPLY_THIRD");
            FALL_THROUGH;

        case FIRST_REPLY_THIRD:
        #if !defined(NO_CERTS) && (!defined(NO_RSA) || defined(HAVE_ECC) || \
             defined(HAVE_ED25519) || defined(HAVE_ED448))
            if (!ssl->options.resuming && ssl->options.sendVerify) {
                ssl->error = SendTls13CertificateVerify(ssl);
                if (ssl->error != 0) {
                    WOLFSSL_ERROR(ssl->error);
                    return WOLFSSL_FATAL_ERROR;
                }
                WOLFSSL_MSG("sent: certificate verify");
            }
        #endif

            ssl->options.connectState = FIRST_REPLY_FOURTH;
            WOLFSSL_MSG("connect state: FIRST_REPLY_FOURTH");
            FALL_THROUGH;

        case FIRST_REPLY_FOURTH:
            if ((ssl->error = SendTls13Finished(ssl)) != 0) {
                WOLFSSL_ERROR(ssl->error);
                return WOLFSSL_FATAL_ERROR;
            }
            WOLFSSL_MSG("sent: finished");

            ssl->options.connectState = FINISHED_DONE;
            WOLFSSL_MSG("connect state: FINISHED_DONE");
            FALL_THROUGH;

        case FINISHED_DONE:
        #ifndef NO_HANDSHAKE_DONE_CB
            if (ssl->hsDoneCb != NULL) {
                int cbret = ssl->hsDoneCb(ssl, ssl->hsDoneCtx);
                if (cbret < 0) {
                    ssl->error = cbret;
                    WOLFSSL_MSG("HandShake Done Cb don't continue error");
                    return WOLFSSL_FATAL_ERROR;
                }
            }
        #endif /* NO_HANDSHAKE_DONE_CB */

            if (!ssl->options.keepResources) {
                FreeHandshakeResources(ssl);
            }

            WOLFSSL_LEAVE("wolfSSL_connect_TLSv13()", WOLFSSL_SUCCESS);
            return WOLFSSL_SUCCESS;

        default:
            WOLFSSL_MSG("Unknown connect state ERROR");
            return WOLFSSL_FATAL_ERROR; /* unknown connect state */
    }
}
#endif

#if defined(WOLFSSL_SEND_HRR_COOKIE)
/* Send a cookie with the HelloRetryRequest to avoid storing state.
 *
 * ssl       SSL/TLS object.
 * secret    Secret to use when generating integrity check for cookie.
 *           A value of NULL indicates to generate a new random secret.
 * secretSz  Size of secret data in bytes.
 *           Use a value of 0 to indicate use of default size.
 * returns BAD_FUNC_ARG when ssl is NULL or not using TLS v1.3, SIDE_ERROR when
 * called on a client; WOLFSSL_SUCCESS on success and otherwise failure.
 */
int wolfSSL_send_hrr_cookie(WOLFSSL* ssl, const unsigned char* secret,
                            unsigned int secretSz)
{
    int ret;

    if (ssl == NULL || !IsAtLeastTLSv1_3(ssl->version))
        return BAD_FUNC_ARG;
 #ifndef NO_WOLFSSL_SERVER
    if (ssl->options.side == WOLFSSL_CLIENT_END)
        return SIDE_ERROR;

    if (secretSz == 0) {
    #if !defined(NO_SHA) && defined(NO_SHA256)
        secretSz = WC_SHA_DIGEST_SIZE;
    #endif /* NO_SHA */
    #ifndef NO_SHA256
        secretSz = WC_SHA256_DIGEST_SIZE;
    #endif /* NO_SHA256 */
    }

    if (secretSz != ssl->buffers.tls13CookieSecret.length) {
        byte* newSecret;

        if (ssl->buffers.tls13CookieSecret.buffer != NULL) {
            ForceZero(ssl->buffers.tls13CookieSecret.buffer,
                      ssl->buffers.tls13CookieSecret.length);
            XFREE(ssl->buffers.tls13CookieSecret.buffer,
                  ssl->heap, DYNAMIC_TYPE_COOKIE_PWD);
        }

        newSecret = (byte*)XMALLOC(secretSz, ssl->heap,
                                   DYNAMIC_TYPE_COOKIE_PWD);
        if (newSecret == NULL) {
            ssl->buffers.tls13CookieSecret.buffer = NULL;
            ssl->buffers.tls13CookieSecret.length = 0;
            WOLFSSL_MSG("couldn't allocate new cookie secret");
            return MEMORY_ERROR;
        }
        ssl->buffers.tls13CookieSecret.buffer = newSecret;
        ssl->buffers.tls13CookieSecret.length = secretSz;
    }

    /* If the supplied secret is NULL, randomly generate a new secret. */
    if (secret == NULL) {
        ret = wc_RNG_GenerateBlock(ssl->rng,
                               ssl->buffers.tls13CookieSecret.buffer, secretSz);
        if (ret < 0)
            return ret;
    }
    else
        XMEMCPY(ssl->buffers.tls13CookieSecret.buffer, secret, secretSz);

    ssl->options.sendCookie = 1;

    ret = WOLFSSL_SUCCESS;
#else
    (void)secret;
    (void)secretSz;

    ret = SIDE_ERROR;
#endif

    return ret;
}
#endif

/* Create a key share entry from group.
 * Generates a key pair.
 *
 * ssl    The SSL/TLS object.
 * group  The named group.
 * returns 0 on success, otherwise failure.
 */
int wolfSSL_UseKeyShare(WOLFSSL* ssl, word16 group)
{
    int ret;

    if (ssl == NULL)
        return BAD_FUNC_ARG;

    ret = TLSX_KeyShare_Use(ssl, group, 0, NULL, NULL);
    if (ret != 0)
        return ret;

    return WOLFSSL_SUCCESS;
}

/* Send no key share entries - use HelloRetryRequest to negotiate shared group.
 *
 * ssl    The SSL/TLS object.
 * returns 0 on success, otherwise failure.
 */
int wolfSSL_NoKeyShares(WOLFSSL* ssl)
{
    int ret;

    if (ssl == NULL)
        return BAD_FUNC_ARG;
    if (ssl->options.side == WOLFSSL_SERVER_END)
        return SIDE_ERROR;

    ret = TLSX_KeyShare_Empty(ssl);
    if (ret != 0)
        return ret;

    return WOLFSSL_SUCCESS;
}

/* Do not send a ticket after TLS v1.3 handshake for resumption.
 *
 * ctx  The SSL/TLS CTX object.
 * returns BAD_FUNC_ARG when ctx is NULL and 0 on success.
 */
int wolfSSL_CTX_no_ticket_TLSv13(WOLFSSL_CTX* ctx)
{
    if (ctx == NULL || !IsAtLeastTLSv1_3(ctx->method->version))
        return BAD_FUNC_ARG;
    if (ctx->method->side == WOLFSSL_CLIENT_END)
        return SIDE_ERROR;

#ifdef HAVE_SESSION_TICKET
    ctx->noTicketTls13 = 1;
#endif

    return 0;
}

/* Do not send a ticket after TLS v1.3 handshake for resumption.
 *
 * ssl  The SSL/TLS object.
 * returns BAD_FUNC_ARG when ssl is NULL, not using TLS v1.3, or called on
 * a client and 0 on success.
 */
int wolfSSL_no_ticket_TLSv13(WOLFSSL* ssl)
{
    if (ssl == NULL || !IsAtLeastTLSv1_3(ssl->version))
        return BAD_FUNC_ARG;
    if (ssl->options.side == WOLFSSL_CLIENT_END)
        return SIDE_ERROR;

#ifdef HAVE_SESSION_TICKET
    ssl->options.noTicketTls13 = 1;
#endif

    return 0;
}

/* Disallow (EC)DHE key exchange when using pre-shared keys.
 *
 * ctx  The SSL/TLS CTX object.
 * returns BAD_FUNC_ARG when ctx is NULL and 0 on success.
 */
int wolfSSL_CTX_no_dhe_psk(WOLFSSL_CTX* ctx)
{
    if (ctx == NULL || !IsAtLeastTLSv1_3(ctx->method->version))
        return BAD_FUNC_ARG;

    ctx->noPskDheKe = 1;

    return 0;
}

/* Disallow (EC)DHE key exchange when using pre-shared keys.
 *
 * ssl  The SSL/TLS object.
 * returns BAD_FUNC_ARG when ssl is NULL, or not using TLS v1.3 and 0 on
 * success.
 */
int wolfSSL_no_dhe_psk(WOLFSSL* ssl)
{
    if (ssl == NULL || !IsAtLeastTLSv1_3(ssl->version))
        return BAD_FUNC_ARG;

    ssl->options.noPskDheKe = 1;

    return 0;
}

/* Update the keys for encryption and decryption.
 * If using non-blocking I/O and WOLFSSL_ERROR_WANT_WRITE is returned then
 * calling wolfSSL_write() will have the message sent when ready.
 *
 * ssl  The SSL/TLS object.
 * returns BAD_FUNC_ARG when ssl is NULL, or not using TLS v1.3,
 * WOLFSSL_ERROR_WANT_WRITE when non-blocking I/O is not ready to write,
 * WOLFSSL_SUCCESS on success and otherwise failure.
 */
int wolfSSL_update_keys(WOLFSSL* ssl)
{
    int ret;

    if (ssl == NULL || !IsAtLeastTLSv1_3(ssl->version))
        return BAD_FUNC_ARG;

    ret = SendTls13KeyUpdate(ssl);
    if (ret == WANT_WRITE)
        ret = WOLFSSL_ERROR_WANT_WRITE;
    else if (ret == 0)
        ret = WOLFSSL_SUCCESS;
    return ret;
}

#if !defined(NO_CERTS) && defined(WOLFSSL_POST_HANDSHAKE_AUTH)
/* Allow post-handshake authentication in TLS v1.3 connections.
 *
 * ctx  The SSL/TLS CTX object.
 * returns BAD_FUNC_ARG when ctx is NULL, SIDE_ERROR when not a client and
 * 0 on success.
 */
int wolfSSL_CTX_allow_post_handshake_auth(WOLFSSL_CTX* ctx)
{
    if (ctx == NULL || !IsAtLeastTLSv1_3(ctx->method->version))
        return BAD_FUNC_ARG;
    if (ctx->method->side == WOLFSSL_SERVER_END)
        return SIDE_ERROR;

    ctx->postHandshakeAuth = 1;

    return 0;
}

/* Allow post-handshake authentication in TLS v1.3 connection.
 *
 * ssl  The SSL/TLS object.
 * returns BAD_FUNC_ARG when ssl is NULL, or not using TLS v1.3,
 * SIDE_ERROR when not a client and 0 on success.
 */
int wolfSSL_allow_post_handshake_auth(WOLFSSL* ssl)
{
    if (ssl == NULL || !IsAtLeastTLSv1_3(ssl->version))
        return BAD_FUNC_ARG;
    if (ssl->options.side == WOLFSSL_SERVER_END)
        return SIDE_ERROR;

    ssl->options.postHandshakeAuth = 1;

    return 0;
}

/* Request a certificate of the client.
 * Can be called any time after handshake completion.
 * A maximum of 256 requests can be sent on a connection.
 *
 * ssl  SSL/TLS object.
 */
int wolfSSL_request_certificate(WOLFSSL* ssl)
{
    int         ret;
#ifndef NO_WOLFSSL_SERVER
    CertReqCtx* certReqCtx;
#endif

    if (ssl == NULL || !IsAtLeastTLSv1_3(ssl->version))
        return BAD_FUNC_ARG;
#ifndef NO_WOLFSSL_SERVER
    if (ssl->options.side == WOLFSSL_CLIENT_END)
        return SIDE_ERROR;
    if (ssl->options.handShakeState != HANDSHAKE_DONE)
        return NOT_READY_ERROR;
    if (!ssl->options.postHandshakeAuth)
        return POST_HAND_AUTH_ERROR;

    certReqCtx = (CertReqCtx*)XMALLOC(sizeof(CertReqCtx), ssl->heap,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (certReqCtx == NULL)
        return MEMORY_E;
    XMEMSET(certReqCtx, 0, sizeof(CertReqCtx));
    certReqCtx->next = ssl->certReqCtx;
    certReqCtx->len = 1;
    if (certReqCtx->next != NULL)
        certReqCtx->ctx = certReqCtx->next->ctx + 1;
    ssl->certReqCtx = certReqCtx;

    ssl->msgsReceived.got_certificate = 0;
    ssl->msgsReceived.got_certificate_verify = 0;
    ssl->msgsReceived.got_finished = 0;

    ret = SendTls13CertificateRequest(ssl, &certReqCtx->ctx, certReqCtx->len);
    if (ret == WANT_WRITE)
        ret = WOLFSSL_ERROR_WANT_WRITE;
    else if (ret == 0)
        ret = WOLFSSL_SUCCESS;
#else
    ret = SIDE_ERROR;
#endif

    return ret;
}
#endif /* !NO_CERTS && WOLFSSL_POST_HANDSHAKE_AUTH */

#if !defined(WOLFSSL_NO_SERVER_GROUPS_EXT)
/* Get the preferred key exchange group.
 *
 * ssl  The SSL/TLS object.
 * returns BAD_FUNC_ARG when ssl is NULL or not using TLS v1.3,
 * SIDE_ERROR when not a client, NOT_READY_ERROR when handshake not complete
 * and group number on success.
 */
int wolfSSL_preferred_group(WOLFSSL* ssl)
{
    if (ssl == NULL || !IsAtLeastTLSv1_3(ssl->version))
        return BAD_FUNC_ARG;
#ifndef NO_WOLFSSL_CLIENT
    if (ssl->options.side == WOLFSSL_SERVER_END)
        return SIDE_ERROR;
    if (ssl->options.handShakeState != HANDSHAKE_DONE)
        return NOT_READY_ERROR;

    /* Return supported groups only. */
    return TLSX_SupportedCurve_Preferred(ssl, 1);
#else
    return SIDE_ERROR;
#endif
}
#endif

/* Sets the key exchange groups in rank order on a context.
 *
 * ctx     SSL/TLS context object.
 * groups  Array of groups.
 * count   Number of groups in array.
 * returns BAD_FUNC_ARG when ctx or groups is NULL, not using TLS v1.3 or
 * count is greater than WOLFSSL_MAX_GROUP_COUNT and WOLFSSL_SUCCESS on success.
 */
int wolfSSL_CTX_set_groups(WOLFSSL_CTX* ctx, int* groups, int count)
{
    int i;

    if (ctx == NULL || groups == NULL || count > WOLFSSL_MAX_GROUP_COUNT)
        return BAD_FUNC_ARG;
    if (!IsAtLeastTLSv1_3(ctx->method->version))
        return BAD_FUNC_ARG;

    for (i = 0; i < count; i++)
        ctx->group[i] = (word16)groups[i];
    ctx->numGroups = (byte)count;

    return WOLFSSL_SUCCESS;
}

/* Sets the key exchange groups in rank order.
 *
 * ssl     SSL/TLS object.
 * groups  Array of groups.
 * count   Number of groups in array.
 * returns BAD_FUNC_ARG when ssl or groups is NULL, not using TLS v1.3 or
 * count is greater than WOLFSSL_MAX_GROUP_COUNT and WOLFSSL_SUCCESS on success.
 */
int wolfSSL_set_groups(WOLFSSL* ssl, int* groups, int count)
{
    int i;

    if (ssl == NULL || groups == NULL || count > WOLFSSL_MAX_GROUP_COUNT)
        return BAD_FUNC_ARG;
    if (!IsAtLeastTLSv1_3(ssl->version))
        return BAD_FUNC_ARG;

    for (i = 0; i < count; i++)
        ssl->group[i] = (word16)groups[i];
    ssl->numGroups = (byte)count;

    return WOLFSSL_SUCCESS;
}

#ifndef NO_PSK
void wolfSSL_CTX_set_psk_client_tls13_callback(WOLFSSL_CTX* ctx,
                                               wc_psk_client_tls13_callback cb)
{
    WOLFSSL_ENTER("SSL_CTX_set_psk_client_tls13_callback");

    if (ctx == NULL)
        return;

    ctx->havePSK = 1;
    ctx->client_psk_tls13_cb = cb;
}


void wolfSSL_set_psk_client_tls13_callback(WOLFSSL* ssl,
                                           wc_psk_client_tls13_callback cb)
{
    byte haveRSA = 1;
    int  keySz   = 0;

    WOLFSSL_ENTER("SSL_set_psk_client_tls13_callback");

    if (ssl == NULL)
        return;

    ssl->options.havePSK = 1;
    ssl->options.client_psk_tls13_cb = cb;

    #ifdef NO_RSA
        haveRSA = 0;
    #endif
    #ifndef NO_CERTS
        keySz = ssl->buffers.keySz;
    #endif
    InitSuites(ssl->suites, ssl->version, keySz, haveRSA, TRUE,
               ssl->options.haveDH, ssl->options.haveNTRU,
               ssl->options.haveECDSAsig, ssl->options.haveECC,
               ssl->options.haveStaticECC, ssl->options.side);
}


void wolfSSL_CTX_set_psk_server_tls13_callback(WOLFSSL_CTX* ctx,
                                               wc_psk_server_tls13_callback cb)
{
    WOLFSSL_ENTER("SSL_CTX_set_psk_server_tls13_callback");
    if (ctx == NULL)
        return;
    ctx->havePSK = 1;
    ctx->server_psk_tls13_cb = cb;
}


void wolfSSL_set_psk_server_tls13_callback(WOLFSSL* ssl,
                                           wc_psk_server_tls13_callback cb)
{
    byte haveRSA = 1;
    int  keySz   = 0;

    WOLFSSL_ENTER("SSL_set_psk_server_tls13_callback");
    if (ssl == NULL)
        return;

    ssl->options.havePSK = 1;
    ssl->options.server_psk_tls13_cb = cb;

    #ifdef NO_RSA
        haveRSA = 0;
    #endif
    #ifndef NO_CERTS
        keySz = ssl->buffers.keySz;
    #endif
    InitSuites(ssl->suites, ssl->version, keySz, haveRSA, TRUE,
               ssl->options.haveDH, ssl->options.haveNTRU,
               ssl->options.haveECDSAsig, ssl->options.haveECC,
               ssl->options.haveStaticECC, ssl->options.side);
}
#endif


#ifndef NO_WOLFSSL_SERVER
/* The server accepting a connection from a client.
 * The protocol version is expecting to be TLS v1.3.
 * If the client downgrades, and older versions of the protocol are compiled
 * in, the server will fallback to wolfSSL_accept().
 * Please see note at top of README if you get an error from accept.
 *
 * ssl  The SSL/TLS object.
 * returns WOLFSSL_SUCCESS on successful handshake, WOLFSSL_FATAL_ERROR when
 * unrecoverable error occurs and 0 otherwise.
 * For more error information use wolfSSL_get_error().
 */
int wolfSSL_accept_TLSv13(WOLFSSL* ssl)
{
    word16 havePSK = 0;
    WOLFSSL_ENTER("SSL_accept_TLSv13()");

#ifdef HAVE_ERRNO_H
    errno = 0;
#endif

#if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
    havePSK = ssl->options.havePSK;
#endif
    (void)havePSK;

    if (ssl->options.side != WOLFSSL_SERVER_END) {
        WOLFSSL_ERROR(ssl->error = SIDE_ERROR);
        return WOLFSSL_FATAL_ERROR;
    }

#ifndef NO_CERTS
    /* allow no private key if using PK callbacks and CB is set */
    if (!havePSK) {
        if (!ssl->buffers.certificate ||
            !ssl->buffers.certificate->buffer) {

            WOLFSSL_MSG("accept error: server cert required");
            WOLFSSL_ERROR(ssl->error = NO_PRIVATE_KEY);
            return WOLFSSL_FATAL_ERROR;
        }

    #ifdef HAVE_PK_CALLBACKS
        if (wolfSSL_CTX_IsPrivatePkSet(ssl->ctx)) {
            WOLFSSL_MSG("Using PK for server private key");
        }
        else
    #endif
        if (!ssl->buffers.key || !ssl->buffers.key->buffer) {
            WOLFSSL_MSG("accept error: server key required");
            WOLFSSL_ERROR(ssl->error = NO_PRIVATE_KEY);
            return WOLFSSL_FATAL_ERROR;
        }
    }
#endif

    if (ssl->buffers.outputBuffer.length > 0
    #ifdef WOLFSSL_ASYNC_CRYPT
        /* do not send buffered or advance state if last error was an
            async pending operation */
        && ssl->error != WC_PENDING_E
    #endif
    ) {
        if ((ssl->error = SendBuffered(ssl)) == 0) {
            /* fragOffset is non-zero when sending fragments. On the last
             * fragment, fragOffset is zero again, and the state can be
             * advanced. */
            if (ssl->fragOffset == 0) {
                ssl->options.acceptState++;
                WOLFSSL_MSG("accept state: "
                            "Advanced from last buffered fragment send");
            }
            else {
                WOLFSSL_MSG("accept state: "
                            "Not advanced, more fragments to send");
            }
        }
        else {
            WOLFSSL_ERROR(ssl->error);
            return WOLFSSL_FATAL_ERROR;
        }
    }

    switch (ssl->options.acceptState) {

#ifdef HAVE_SECURE_RENEGOTIATION
        case TLS13_ACCEPT_BEGIN_RENEG:
#endif
        case TLS13_ACCEPT_BEGIN :
            /* get client_hello */
            while (ssl->options.clientState < CLIENT_HELLO_COMPLETE) {
                if ((ssl->error = ProcessReply(ssl)) < 0) {
                    WOLFSSL_ERROR(ssl->error);
                    return WOLFSSL_FATAL_ERROR;
                }
            }

            ssl->options.acceptState = TLS13_ACCEPT_CLIENT_HELLO_DONE;
            WOLFSSL_MSG("accept state ACCEPT_CLIENT_HELLO_DONE");
            if (!IsAtLeastTLSv1_3(ssl->version))
                return wolfSSL_accept(ssl);
            FALL_THROUGH;

        case TLS13_ACCEPT_CLIENT_HELLO_DONE :
            if (ssl->options.serverState ==
                                          SERVER_HELLO_RETRY_REQUEST_COMPLETE) {
                if ((ssl->error = SendTls13ServerHello(ssl,
                                                   hello_retry_request)) != 0) {
                    WOLFSSL_ERROR(ssl->error);
                    return WOLFSSL_FATAL_ERROR;
                }
            }

            ssl->options.acceptState = TLS13_ACCEPT_HELLO_RETRY_REQUEST_DONE;
            WOLFSSL_MSG("accept state ACCEPT_HELLO_RETRY_REQUEST_DONE");
            FALL_THROUGH;

        case TLS13_ACCEPT_HELLO_RETRY_REQUEST_DONE :
    #ifdef WOLFSSL_TLS13_MIDDLEBOX_COMPAT
            if (ssl->options.serverState ==
                                          SERVER_HELLO_RETRY_REQUEST_COMPLETE) {
                if ((ssl->error = SendChangeCipher(ssl)) != 0) {
                    WOLFSSL_ERROR(ssl->error);
                    return WOLFSSL_FATAL_ERROR;
                }
                ssl->options.sentChangeCipher = 1;
                ssl->options.serverState = SERVER_HELLO_RETRY_REQUEST_COMPLETE;
            }
    #endif
            ssl->options.acceptState = TLS13_ACCEPT_FIRST_REPLY_DONE;
            WOLFSSL_MSG("accept state ACCEPT_FIRST_REPLY_DONE");
            FALL_THROUGH;

        case TLS13_ACCEPT_FIRST_REPLY_DONE :
            if (ssl->options.serverState ==
                                          SERVER_HELLO_RETRY_REQUEST_COMPLETE) {
                ssl->options.clientState = CLIENT_HELLO_RETRY;
                while (ssl->options.clientState < CLIENT_HELLO_COMPLETE) {
                    if ((ssl->error = ProcessReply(ssl)) < 0) {
                        WOLFSSL_ERROR(ssl->error);
                        return WOLFSSL_FATAL_ERROR;
                    }
                }
            }

            ssl->options.acceptState = TLS13_ACCEPT_SECOND_REPLY_DONE;
            WOLFSSL_MSG("accept state ACCEPT_SECOND_REPLY_DONE");
            FALL_THROUGH;

        case TLS13_ACCEPT_SECOND_REPLY_DONE :
            if ((ssl->error = SendTls13ServerHello(ssl, server_hello)) != 0) {
                WOLFSSL_ERROR(ssl->error);
                return WOLFSSL_FATAL_ERROR;
            }
            ssl->options.acceptState = TLS13_SERVER_HELLO_SENT;
            WOLFSSL_MSG("accept state SERVER_HELLO_SENT");
            FALL_THROUGH;

        case TLS13_SERVER_HELLO_SENT :
    #if defined(WOLFSSL_TLS13_MIDDLEBOX_COMPAT)
            if (!ssl->options.sentChangeCipher) {
                if ((ssl->error = SendChangeCipher(ssl)) != 0) {
                    WOLFSSL_ERROR(ssl->error);
                    return WOLFSSL_FATAL_ERROR;
                }
                ssl->options.sentChangeCipher = 1;
            }
    #endif

            ssl->options.acceptState = TLS13_ACCEPT_THIRD_REPLY_DONE;
            WOLFSSL_MSG("accept state ACCEPT_THIRD_REPLY_DONE");
            FALL_THROUGH;

        case TLS13_ACCEPT_THIRD_REPLY_DONE :
            if (!ssl->options.noPskDheKe) {
                ssl->error = TLSX_KeyShare_DeriveSecret(ssl);
                if (ssl->error != 0)
                    return WOLFSSL_FATAL_ERROR;
            }

            if ((ssl->error = SendTls13EncryptedExtensions(ssl)) != 0) {
                WOLFSSL_ERROR(ssl->error);
                return WOLFSSL_FATAL_ERROR;
            }
            ssl->options.acceptState = TLS13_SERVER_EXTENSIONS_SENT;
            WOLFSSL_MSG("accept state SERVER_EXTENSIONS_SENT");
            FALL_THROUGH;

        case TLS13_SERVER_EXTENSIONS_SENT :
#ifndef NO_CERTS
            if (!ssl->options.resuming) {
                if (ssl->options.verifyPeer) {
                    ssl->error = SendTls13CertificateRequest(ssl, NULL, 0);
                    if (ssl->error != 0) {
                        WOLFSSL_ERROR(ssl->error);
                        return WOLFSSL_FATAL_ERROR;
                    }
                }
            }
#endif
            ssl->options.acceptState = TLS13_CERT_REQ_SENT;
            WOLFSSL_MSG("accept state CERT_REQ_SENT");
            FALL_THROUGH;

        case TLS13_CERT_REQ_SENT :
#ifndef NO_CERTS
            if (!ssl->options.resuming && ssl->options.sendVerify) {
                if ((ssl->error = SendTls13Certificate(ssl)) != 0) {
                    WOLFSSL_ERROR(ssl->error);
                    return WOLFSSL_FATAL_ERROR;
                }
            }
#endif
            ssl->options.acceptState = TLS13_CERT_SENT;
            WOLFSSL_MSG("accept state CERT_SENT");
            FALL_THROUGH;

        case TLS13_CERT_SENT :
#if !defined(NO_CERTS) && (!defined(NO_RSA) || defined(HAVE_ECC) || \
     defined(HAVE_ED25519) || defined(HAVE_ED448))
            if (!ssl->options.resuming && ssl->options.sendVerify) {
                if ((ssl->error = SendTls13CertificateVerify(ssl)) != 0) {
                    WOLFSSL_ERROR(ssl->error);
                    return WOLFSSL_FATAL_ERROR;
                }
            }
#endif
            ssl->options.acceptState = TLS13_CERT_VERIFY_SENT;
            WOLFSSL_MSG("accept state CERT_VERIFY_SENT");
            FALL_THROUGH;

        case TLS13_CERT_VERIFY_SENT :
            if ((ssl->error = SendTls13Finished(ssl)) != 0) {
                WOLFSSL_ERROR(ssl->error);
                return WOLFSSL_FATAL_ERROR;
            }

            ssl->options.acceptState = TLS13_ACCEPT_FINISHED_SENT;
            WOLFSSL_MSG("accept state ACCEPT_FINISHED_SENT");
#ifdef WOLFSSL_EARLY_DATA
            if (ssl->earlyData != no_early_data) {
                ssl->options.handShakeState = SERVER_FINISHED_COMPLETE;
                return WOLFSSL_SUCCESS;
            }
#endif
            FALL_THROUGH;

        case TLS13_ACCEPT_FINISHED_SENT :
#ifdef HAVE_SESSION_TICKET
    #ifdef WOLFSSL_TLS13_TICKET_BEFORE_FINISHED
            if (!ssl->options.verifyPeer && !ssl->options.noTicketTls13 &&
                                                ssl->ctx->ticketEncCb != NULL) {
                if ((ssl->error = SendTls13NewSessionTicket(ssl)) != 0) {
                    WOLFSSL_ERROR(ssl->error);
                    return WOLFSSL_FATAL_ERROR;
                }
            }
    #endif
#endif /* HAVE_SESSION_TICKET */
            ssl->options.acceptState = TLS13_PRE_TICKET_SENT;
            WOLFSSL_MSG("accept state  TICKET_SENT");
            FALL_THROUGH;

        case TLS13_PRE_TICKET_SENT :
            while (ssl->options.clientState < CLIENT_FINISHED_COMPLETE)
                if ( (ssl->error = ProcessReply(ssl)) < 0) {
                    WOLFSSL_ERROR(ssl->error);
                    return WOLFSSL_FATAL_ERROR;
                }

            ssl->options.acceptState = TLS13_ACCEPT_FINISHED_DONE;
            WOLFSSL_MSG("accept state ACCEPT_FINISHED_DONE");
            FALL_THROUGH;

        case TLS13_ACCEPT_FINISHED_DONE :
#ifdef HAVE_SESSION_TICKET
    #ifdef WOLFSSL_TLS13_TICKET_BEFORE_FINISHED
            if (!ssl->options.verifyPeer) {
            }
            else
    #endif
            if (!ssl->options.noTicketTls13 && ssl->ctx->ticketEncCb != NULL) {
                if ((ssl->error = SendTls13NewSessionTicket(ssl)) != 0) {
                    WOLFSSL_ERROR(ssl->error);
                    return WOLFSSL_FATAL_ERROR;
                }
            }
#endif /* HAVE_SESSION_TICKET */
            ssl->options.acceptState = TLS13_TICKET_SENT;
            WOLFSSL_MSG("accept state TICKET_SENT");
            FALL_THROUGH;

        case TLS13_TICKET_SENT :
#ifndef NO_HANDSHAKE_DONE_CB
            if (ssl->hsDoneCb) {
                int cbret = ssl->hsDoneCb(ssl, ssl->hsDoneCtx);
                if (cbret < 0) {
                    ssl->error = cbret;
                    WOLFSSL_MSG("HandShake Done Cb don't continue error");
                    return WOLFSSL_FATAL_ERROR;
                }
            }
#endif /* NO_HANDSHAKE_DONE_CB */

            if (!ssl->options.keepResources) {
                FreeHandshakeResources(ssl);
            }

            WOLFSSL_LEAVE("SSL_accept()", WOLFSSL_SUCCESS);
            return WOLFSSL_SUCCESS;

        default :
            WOLFSSL_MSG("Unknown accept state ERROR");
            return WOLFSSL_FATAL_ERROR;
    }
}
#endif

#ifdef WOLFSSL_EARLY_DATA
/* Sets the maximum amount of early data that can be seen by server when using
 * session tickets for resumption.
 * A value of zero indicates no early data is to be sent by client using session
 * tickets.
 *
 * ctx  The SSL/TLS CTX object.
 * sz   Maximum size of the early data.
 * returns BAD_FUNC_ARG when ctx is NULL, SIDE_ERROR when not a server and
 * 0 on success.
 */
int wolfSSL_CTX_set_max_early_data(WOLFSSL_CTX* ctx, unsigned int sz)
{
    if (ctx == NULL || !IsAtLeastTLSv1_3(ctx->method->version))
        return BAD_FUNC_ARG;
    if (ctx->method->side == WOLFSSL_CLIENT_END)
        return SIDE_ERROR;

    ctx->maxEarlyDataSz = sz;

    return 0;
}

/* Sets the maximum amount of early data that can be seen by server when using
 * session tickets for resumption.
 * A value of zero indicates no early data is to be sent by client using session
 * tickets.
 *
 * ssl  The SSL/TLS object.
 * sz   Maximum size of the early data.
 * returns BAD_FUNC_ARG when ssl is NULL, or not using TLS v1.3,
 * SIDE_ERROR when not a server and 0 on success.
 */
int wolfSSL_set_max_early_data(WOLFSSL* ssl, unsigned int sz)
{
    if (ssl == NULL || !IsAtLeastTLSv1_3(ssl->version))
        return BAD_FUNC_ARG;
    if (ssl->options.side == WOLFSSL_CLIENT_END)
        return SIDE_ERROR;

    ssl->options.maxEarlyDataSz = sz;

    return 0;
}

/* Write early data to the server.
 *
 * ssl    The SSL/TLS object.
 * data   Early data to write
 * sz     The size of the eary data in bytes.
 * outSz  The number of early data bytes written.
 * returns BAD_FUNC_ARG when: ssl, data or outSz is NULL; sz is negative;
 * or not using TLS v1.3. SIDE ERROR when not a server. Otherwise the number of
 * early data bytes written.
 */
int wolfSSL_write_early_data(WOLFSSL* ssl, const void* data, int sz, int* outSz)
{
    int ret = 0;

    WOLFSSL_ENTER("SSL_write_early_data()");

    if (ssl == NULL || data == NULL || sz < 0 || outSz == NULL)
        return BAD_FUNC_ARG;
    if (!IsAtLeastTLSv1_3(ssl->version))
        return BAD_FUNC_ARG;

#ifndef NO_WOLFSSL_CLIENT
    if (ssl->options.side == WOLFSSL_SERVER_END)
        return SIDE_ERROR;

    if (ssl->options.handShakeState == NULL_STATE) {
        ssl->earlyData = expecting_early_data;
        ret = wolfSSL_connect_TLSv13(ssl);
        if (ret != WOLFSSL_SUCCESS)
            return WOLFSSL_FATAL_ERROR;
    }
    if (ssl->options.handShakeState == CLIENT_HELLO_COMPLETE) {
        ret = SendData(ssl, data, sz);
        if (ret > 0)
            *outSz = ret;
    }
#else
    return SIDE_ERROR;
#endif

    WOLFSSL_LEAVE("SSL_write_early_data()", ret);

    if (ret < 0)
        ret = WOLFSSL_FATAL_ERROR;
    return ret;
}

/* Read the any early data from the client.
 *
 * ssl    The SSL/TLS object.
 * data   Buffer to put the early data into.
 * sz     The size of the buffer in bytes.
 * outSz  The number of early data bytes read.
 * returns BAD_FUNC_ARG when: ssl, data or outSz is NULL; sz is negative;
 * or not using TLS v1.3. SIDE ERROR when not a server. Otherwise the number of
 * early data bytes read.
 */
int wolfSSL_read_early_data(WOLFSSL* ssl, void* data, int sz, int* outSz)
{
    int ret = 0;

    WOLFSSL_ENTER("wolfSSL_read_early_data()");


    if (ssl == NULL || data == NULL || sz < 0 || outSz == NULL)
        return BAD_FUNC_ARG;
    if (!IsAtLeastTLSv1_3(ssl->version))
        return BAD_FUNC_ARG;

#ifndef NO_WOLFSSL_SERVER
    if (ssl->options.side == WOLFSSL_CLIENT_END)
        return SIDE_ERROR;

    if (ssl->options.handShakeState == NULL_STATE) {
        ssl->earlyData = expecting_early_data;
        ret = wolfSSL_accept_TLSv13(ssl);
        if (ret <= 0)
            return WOLFSSL_FATAL_ERROR;
    }
    if (ssl->options.handShakeState == SERVER_FINISHED_COMPLETE) {
        ret = ReceiveData(ssl, (byte*)data, sz, FALSE);
        if (ret > 0)
            *outSz = ret;
        if (ssl->error == ZERO_RETURN)
            ssl->error = WOLFSSL_ERROR_NONE;
    }
    else
        ret = 0;
#else
    return SIDE_ERROR;
#endif

    WOLFSSL_LEAVE("wolfSSL_read_early_data()", ret);

    if (ret < 0)
        ret = WOLFSSL_FATAL_ERROR;
    return ret;
}
#endif

#ifdef HAVE_SECRET_CALLBACK
int wolfSSL_set_tls13_secret_cb(WOLFSSL* ssl, Tls13SecretCb cb, void* ctx)
{
    WOLFSSL_ENTER("wolfSSL_set_tls13_secret_cb");
    if (ssl == NULL)
        return WOLFSSL_FATAL_ERROR;

    ssl->tls13SecretCb = cb;
    ssl->tls13SecretCtx = ctx;

    return WOLFSSL_SUCCESS;
}
#endif

#undef ERROR_OUT

#endif /* !WOLFCRYPT_ONLY */

#endif /* WOLFSSL_TLS13 */
