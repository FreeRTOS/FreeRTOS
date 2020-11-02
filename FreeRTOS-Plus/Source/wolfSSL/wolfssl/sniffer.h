/* sniffer.h
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



#ifndef WOLFSSL_SNIFFER_H
#define WOLFSSL_SNIFFER_H

#include <wolfssl/wolfcrypt/settings.h>

#ifdef _WIN32
    #ifdef SSL_SNIFFER_EXPORTS
        #define SSL_SNIFFER_API __declspec(dllexport)
    #else
        #define SSL_SNIFFER_API __declspec(dllimport)
    #endif
#else
    #define SSL_SNIFFER_API
#endif /* _WIN32 */


#ifdef __cplusplus
    extern "C" {
#endif

/* @param typeK: (formerly keyType) was shadowing a global declaration in
 *                wolfssl/wolfcrypt/asn.h line 175
 */
WOLFSSL_API
SSL_SNIFFER_API int ssl_SetPrivateKey(const char* address, int port,
                                      const char* keyFile, int typeK,
                                      const char* password, char* error);

WOLFSSL_API
SSL_SNIFFER_API int ssl_SetPrivateKeyBuffer(const char* address, int port,
                                            const char* keyBuf, int keySz, 
                                            int typeK, const char* password, 
                                            char* error);


WOLFSSL_API
SSL_SNIFFER_API int ssl_SetNamedPrivateKey(const char* name,
                                           const char* address, int port,
                                           const char* keyFile, int typeK,
                                           const char* password, char* error);

WOLFSSL_API
SSL_SNIFFER_API int ssl_SetNamedPrivateKeyBuffer(const char* name,
                                                 const char* address, int port,
                                                 const char* keyBuf, int keySz, 
                                                 int typeK, const char* password, 
                                                 char* error);

WOLFSSL_API 
SSL_SNIFFER_API int ssl_SetEphemeralKey(const char* address, int port, 
                                        const char* keyFile, int typeKey, 
                                        const char* password, char* error);

WOLFSSL_API 
SSL_SNIFFER_API int ssl_SetEphemeralKeyBuffer(const char* address, int port, 
                                              const char* keyBuf, int keySz, int typeKey, 
                                              const char* password, char* error);


WOLFSSL_API 
SSL_SNIFFER_API int ssl_SetNamedEphemeralKey(const char* name,
                                             const char* address, int port,
                                             const char* keyFile, int typeKey,
                                             const char* password, char* error);

WOLFSSL_API 
SSL_SNIFFER_API int ssl_SetNamedEphemeralKeyBuffer(const char* name,
                                                   const char* address, int port,
                                                   const char* keyBuf, int keySz, int typeKey, 
                                                   const char* password, char* error);

WOLFSSL_API
SSL_SNIFFER_API int ssl_DecodePacket(const unsigned char* packet, int length,
                                     unsigned char** data, char* error);

WOLFSSL_API
SSL_SNIFFER_API int ssl_FreeDecodeBuffer(unsigned char** data, char* error);

WOLFSSL_API
SSL_SNIFFER_API int ssl_FreeZeroDecodeBuffer(unsigned char** data, int sz,
                                             char* error);

WOLFSSL_API
SSL_SNIFFER_API int ssl_Trace(const char* traceFile, char* error);

WOLFSSL_API
SSL_SNIFFER_API int ssl_EnableRecovery(int onOff, int maxMemory, char* error);

WOLFSSL_API
SSL_SNIFFER_API int ssl_GetSessionStats(unsigned int* active,
                                        unsigned int* total,
                                        unsigned int* peak,
                                        unsigned int* maxSessions,
                                        unsigned int* missedData,
                                        unsigned int* reassemblyMemory,
                                        char* error);

WOLFSSL_API void ssl_InitSniffer(void);

WOLFSSL_API void ssl_FreeSniffer(void);


/* ssl_SetPrivateKey typeKs */
enum {
    FILETYPE_PEM = 1,
    FILETYPE_DER = 2,
};


/*
 * New Sniffer API that provides read-only access to the TLS and cipher
 * information associated with the SSL session.
 */

typedef struct SSLInfo
{
    unsigned char  isValid;
            /* indicates if the info in this struct is valid: 0 = no, 1 = yes */
    unsigned char  protocolVersionMajor;    /* SSL Version: major */
    unsigned char  protocolVersionMinor;    /* SSL Version: minor */
    unsigned char  serverCipherSuite0;      /* first byte, normally 0 */
    unsigned char  serverCipherSuite;       /* second byte, actual suite */
    unsigned char  serverCipherSuiteName[256];
            /* cipher name, e.g., "TLS_RSA_..." */
    unsigned char  serverNameIndication[128];
    unsigned int   keySize;
} SSLInfo;


WOLFSSL_API
SSL_SNIFFER_API int ssl_DecodePacketWithSessionInfo(
                        const unsigned char* packet, int length,
                        unsigned char** data, SSLInfo* sslInfo, char* error);

typedef void (*SSLConnCb)(const void* session, SSLInfo* info, void* ctx);

WOLFSSL_API
SSL_SNIFFER_API int ssl_SetConnectionCb(SSLConnCb cb);

WOLFSSL_API
SSL_SNIFFER_API int ssl_SetConnectionCtx(void* ctx);


typedef struct SSLStats
{
    unsigned long int sslStandardConns;
    unsigned long int sslClientAuthConns;
    unsigned long int sslResumedConns;
    unsigned long int sslEphemeralMisses;
    unsigned long int sslResumeMisses;
    unsigned long int sslCiphersUnsupported;
    unsigned long int sslKeysUnmatched;
    unsigned long int sslKeyFails;
    unsigned long int sslDecodeFails;
    unsigned long int sslAlerts;
    unsigned long int sslDecryptedBytes;
    unsigned long int sslEncryptedBytes;
    unsigned long int sslEncryptedPackets;
    unsigned long int sslDecryptedPackets;
    unsigned long int sslKeyMatches;
    unsigned long int sslEncryptedConns;

    unsigned long int sslResumptionValid;
    unsigned long int sslResumptionInserts;
} SSLStats;


WOLFSSL_API
SSL_SNIFFER_API int ssl_ResetStatistics(void);


WOLFSSL_API
SSL_SNIFFER_API int ssl_ReadStatistics(SSLStats* stats);


WOLFSSL_API
SSL_SNIFFER_API int ssl_ReadResetStatistics(SSLStats* stats);


typedef int (*SSLWatchCb)(void* vSniffer,
                        const unsigned char* certHash,
                        unsigned int certHashSz,
                        const unsigned char* certChain,
                        unsigned int certChainSz,
                        void* ctx, char* error);

WOLFSSL_API
SSL_SNIFFER_API int ssl_SetWatchKeyCallback(SSLWatchCb cb, char* error);

WOLFSSL_API
SSL_SNIFFER_API int ssl_SetWatchKeyCallback_ex(SSLWatchCb cb, int devId,
                        char* error);

WOLFSSL_API
SSL_SNIFFER_API int ssl_SetWatchKeyCtx(void* ctx, char* error);

WOLFSSL_API
SSL_SNIFFER_API int ssl_SetWatchKey_buffer(void* vSniffer,
                        const unsigned char* key, unsigned int keySz,
                        int keyType, char* error);

WOLFSSL_API
SSL_SNIFFER_API int ssl_SetWatchKey_file(void* vSniffer,
                        const char* keyFile, int keyType,
                        const char* password, char* error);


typedef int (*SSLStoreDataCb)(const unsigned char* decryptBuf,
        unsigned int decryptBufSz, unsigned int decryptBufOffset, void* ctx);

WOLFSSL_API
SSL_SNIFFER_API int ssl_SetStoreDataCallback(SSLStoreDataCb cb);

WOLFSSL_API
SSL_SNIFFER_API int ssl_DecodePacketWithSessionInfoStoreData(
        const unsigned char* packet, int length, void* ctx,
        SSLInfo* sslInfo, char* error);


WOLFSSL_API
SSL_SNIFFER_API int ssl_DecodePacketWithChain(void* vChain,
        unsigned int chainSz, unsigned char** data, char* error);


WOLFSSL_API
SSL_SNIFFER_API int ssl_DecodePacketWithChainSessionInfoStoreData(
        void* vChain, unsigned int chainSz, void* ctx, SSLInfo* sslInfo,
        char* error);

#ifdef __cplusplus
    }  /* extern "C" */
#endif

#endif /* wolfSSL_SNIFFER_H */

