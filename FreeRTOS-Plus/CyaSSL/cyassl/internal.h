/* internal.h
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


#ifndef CYASSL_INT_H
#define CYASSL_INT_H


#include <cyassl/ssl.h>
#include <cyassl/crl.h>
#include <cyassl/ctaocrypt/types.h>
#include <cyassl/ctaocrypt/random.h>
#include <cyassl/ctaocrypt/des3.h>
#include <cyassl/ctaocrypt/hc128.h>
#include <cyassl/ctaocrypt/rabbit.h>
#include <cyassl/ctaocrypt/asn.h>
#include <cyassl/ctaocrypt/md5.h>
#include <cyassl/ctaocrypt/aes.h>
#include <cyassl/ctaocrypt/logging.h>
#ifdef HAVE_ECC
    #include <cyassl/ctaocrypt/ecc.h>
#endif
#ifndef NO_SHA256
    #include <cyassl/ctaocrypt/sha256.h>
#endif
#ifdef HAVE_OCSP
    #include <cyassl/ocsp.h>
#endif

#ifdef CYASSL_CALLBACKS
    #include <cyassl/openssl/cyassl_callbacks.h>
    #include <signal.h>
#endif

#ifdef USE_WINDOWS_API 
    #ifdef CYASSL_GAME_BUILD
        #include "system/xtl.h"
    #else
        #if defined(_WIN32_WCE) || defined(WIN32_LEAN_AND_MEAN)
            /* On WinCE winsock2.h must be included before windows.h */
            #include <winsock2.h>
        #endif
        #include <windows.h>
        #if defined(FREERTOS_WINSIM) && !defined(SINGLE_THREADED)
            #include "FreeRTOS.h"
            #include "semphr.h"
        #endif
    #endif
#elif defined(THREADX)
    #ifndef SINGLE_THREADED
        #include "tx_api.h"
    #endif
#elif defined(MICRIUM)
    /* do nothing, just don't pick Unix */
#elif defined(FREERTOS)
    #ifndef SINGLE_THREADED
		#include "FreeRTOS.h"
		#include "semphr.h"
    #endif
#else
    #ifndef SINGLE_THREADED
        #define CYASSL_PTHREADS
        #include <pthread.h>
    #endif
    #if defined(OPENSSL_EXTRA) || defined(GOAHEAD_WS)
        #include <unistd.h>      /* for close of BIO */
    #endif
#endif

#ifdef HAVE_LIBZ
    #include "zlib.h"
#endif

#ifdef _MSC_VER
    /* 4996 warning to use MS extensions e.g., strcpy_s instead of strncpy */
    #pragma warning(disable: 4996)
#endif

#ifdef NO_AES
    #if !defined (ALIGN16)
        #define ALIGN16
    #endif
#endif

#ifdef NO_SHA256
    #define SHA256_DIGEST_SIZE 32 
#endif

#ifdef __cplusplus
    extern "C" {
#endif


#ifdef USE_WINDOWS_API 
    typedef unsigned int SOCKET_T;
#else
    typedef int SOCKET_T;
#endif


typedef byte word24[3];

/* used by ssl.c and cyassl_int.c */
void c32to24(word32 in, word24 out);

/* Define or comment out the cipher suites you'd like to be compiled in
   make sure to use at least one BUILD_SSL_xxx or BUILD_TLS_xxx is defined

   When adding cipher suites, add name to cipher_names, idx to cipher_name_idx
*/
#ifndef NO_RC4
    #define BUILD_SSL_RSA_WITH_RC4_128_SHA
    #define BUILD_SSL_RSA_WITH_RC4_128_MD5
    #if !defined(NO_TLS) && defined(HAVE_NTRU)
        #define BUILD_TLS_NTRU_RSA_WITH_RC4_128_SHA
    #endif
#endif

#ifndef NO_DES3
    #define BUILD_SSL_RSA_WITH_3DES_EDE_CBC_SHA
    #if !defined(NO_TLS) && defined(HAVE_NTRU)
        #define BUILD_TLS_NTRU_RSA_WITH_3DES_EDE_CBC_SHA
    #endif
#endif

#if !defined(NO_AES) && !defined(NO_TLS)
    #define BUILD_TLS_RSA_WITH_AES_128_CBC_SHA
    #define BUILD_TLS_RSA_WITH_AES_256_CBC_SHA
    #if !defined (NO_PSK)
        #define BUILD_TLS_PSK_WITH_AES_128_CBC_SHA
        #define BUILD_TLS_PSK_WITH_AES_256_CBC_SHA
    #endif
    #if defined(HAVE_NTRU)
        #define BUILD_TLS_NTRU_RSA_WITH_AES_128_CBC_SHA
        #define BUILD_TLS_NTRU_RSA_WITH_AES_256_CBC_SHA
    #endif
    #if !defined (NO_SHA256)
        #define BUILD_TLS_RSA_WITH_AES_128_CBC_SHA256
        #define BUILD_TLS_RSA_WITH_AES_256_CBC_SHA256
    #endif
#endif

#if !defined(NO_HC128) && !defined(NO_TLS)
    #define BUILD_TLS_RSA_WITH_HC_128_CBC_MD5
    #define BUILD_TLS_RSA_WITH_HC_128_CBC_SHA
#endif

#if !defined(NO_RABBIT) && !defined(NO_TLS)
    #define BUILD_TLS_RSA_WITH_RABBIT_CBC_SHA
#endif

#if !defined(NO_DH) && !defined(NO_AES) && !defined(NO_TLS) && defined(OPENSSL_EXTRA)
    #define BUILD_TLS_DHE_RSA_WITH_AES_128_CBC_SHA
    #define BUILD_TLS_DHE_RSA_WITH_AES_256_CBC_SHA
    #if !defined (NO_SHA256)
        #define BUILD_TLS_DHE_RSA_WITH_AES_128_CBC_SHA256
        #define BUILD_TLS_DHE_RSA_WITH_AES_256_CBC_SHA256
    #endif
#endif

#if defined(HAVE_ECC) && !defined(NO_TLS)
    #if !defined(NO_AES)
        #define BUILD_TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA
        #define BUILD_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA
        #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA
        #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA

        #define BUILD_TLS_ECDH_RSA_WITH_AES_128_CBC_SHA
        #define BUILD_TLS_ECDH_RSA_WITH_AES_256_CBC_SHA
        #define BUILD_TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA
        #define BUILD_TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA
    #endif
    #if !defined(NO_RC4)
        #define BUILD_TLS_ECDHE_RSA_WITH_RC4_128_SHA
        #define BUILD_TLS_ECDHE_ECDSA_WITH_RC4_128_SHA

        #define BUILD_TLS_ECDH_RSA_WITH_RC4_128_SHA
        #define BUILD_TLS_ECDH_ECDSA_WITH_RC4_128_SHA
    #endif
    #if !defined(NO_DES3)
        #define BUILD_TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA
        #define BUILD_TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA

        #define BUILD_TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA
        #define BUILD_TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA
    #endif
#endif


#if defined(BUILD_SSL_RSA_WITH_RC4_128_SHA) || \
    defined(BUILD_SSL_RSA_WITH_RC4_128_MD5)
    #define BUILD_ARC4
#endif

#if defined(BUILD_SSL_RSA_WITH_3DES_EDE_CBC_SHA)
    #define BUILD_DES3
#endif

#if defined(BUILD_TLS_RSA_WITH_AES_128_CBC_SHA) || \
    defined(BUILD_TLS_RSA_WITH_AES_256_CBC_SHA)
    #define BUILD_AES
#endif

#if defined(BUILD_TLS_RSA_WITH_HC_128_CBC_SHA) || \
    defined(BUILD_TLS_RSA_WITH_HC_128_CBC_MD5)
    #define BUILD_HC128
#endif

#if defined(BUILD_TLS_RSA_WITH_RABBIT_CBC_SHA)
    #define BUILD_RABBIT
#endif

#ifdef NO_DES3
    #define DES_BLOCK_SIZE 8
#endif

#ifdef NO_AES
    #define AES_BLOCK_SIZE 16
#endif


/* actual cipher values, 2nd byte */
enum {
    TLS_DHE_RSA_WITH_AES_256_CBC_SHA  = 0x39,
    TLS_DHE_RSA_WITH_AES_128_CBC_SHA  = 0x33,
    TLS_RSA_WITH_AES_256_CBC_SHA      = 0x35,
    TLS_RSA_WITH_AES_128_CBC_SHA      = 0x2F,
    TLS_PSK_WITH_AES_256_CBC_SHA      = 0x8d,
    TLS_PSK_WITH_AES_128_CBC_SHA      = 0x8c,
    SSL_RSA_WITH_RC4_128_SHA          = 0x05,
    SSL_RSA_WITH_RC4_128_MD5          = 0x04,
    SSL_RSA_WITH_3DES_EDE_CBC_SHA     = 0x0A,

    /* ECC suites, first byte is 0xC0 (ECC_BYTE) */
    TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA    = 0x14,
    TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA    = 0x13,
    TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA  = 0x0A,
    TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA  = 0x09,
    TLS_ECDHE_RSA_WITH_RC4_128_SHA        = 0x11,
    TLS_ECDHE_ECDSA_WITH_RC4_128_SHA      = 0x07,
    TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA   = 0x12,
    TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA = 0x08,

        /* static ECDH, first byte is 0xC0 (ECC_BYTE) */
    TLS_ECDH_RSA_WITH_AES_256_CBC_SHA    = 0x0F,
    TLS_ECDH_RSA_WITH_AES_128_CBC_SHA    = 0x0E,
    TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA  = 0x05,
    TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA  = 0x04,
    TLS_ECDH_RSA_WITH_RC4_128_SHA        = 0x0C,
    TLS_ECDH_ECDSA_WITH_RC4_128_SHA      = 0x02,
    TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA   = 0x0D,
    TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA = 0x03,

    /* CyaSSL extension - eSTREAM */
    TLS_RSA_WITH_HC_128_CBC_MD5       = 0xFB,
    TLS_RSA_WITH_HC_128_CBC_SHA       = 0xFC,
    TLS_RSA_WITH_RABBIT_CBC_SHA       = 0xFD,

    /* CyaSSL extension - NTRU */
    TLS_NTRU_RSA_WITH_RC4_128_SHA      = 0xe5,
    TLS_NTRU_RSA_WITH_3DES_EDE_CBC_SHA = 0xe6,
    TLS_NTRU_RSA_WITH_AES_128_CBC_SHA  = 0xe7,  /* clases w/ official SHA-256 */
    TLS_NTRU_RSA_WITH_AES_256_CBC_SHA  = 0xe8,

    /* SHA256 */
    TLS_DHE_RSA_WITH_AES_256_CBC_SHA256 = 0x6b,
    TLS_DHE_RSA_WITH_AES_128_CBC_SHA256 = 0x67,
    TLS_RSA_WITH_AES_256_CBC_SHA256     = 0x3d,
    TLS_RSA_WITH_AES_128_CBC_SHA256     = 0x3c
};


enum Misc {
    SERVER_END = 0,
    CLIENT_END,

    ECC_BYTE =  0xC0,           /* ECC first cipher suite byte */

    SEND_CERT       = 1,
    SEND_BLANK_CERT = 2,

    DTLS_MAJOR      = 0xfe,     /* DTLS major version number */
    DTLS_MINOR      = 0xff,     /* DTLS minor version number */
    SSLv3_MAJOR     = 3,        /* SSLv3 and TLSv1+  major version number */
    SSLv3_MINOR     = 0,        /* TLSv1   minor version number */
    TLSv1_MINOR     = 1,        /* TLSv1   minor version number */
    TLSv1_1_MINOR   = 2,        /* TLSv1_1 minor version number */
    TLSv1_2_MINOR   = 3,        /* TLSv1_2 minor version number */
    NO_COMPRESSION  =  0,
    ZLIB_COMPRESSION = 221,     /* CyaSSL zlib compression */
    SECRET_LEN      = 48,       /* pre RSA and all master */
    ENCRYPT_LEN     = 512,      /* allow 4096 bit static buffer */
    SIZEOF_SENDER   =  4,       /* clnt or srvr           */
    FINISHED_SZ     = MD5_DIGEST_SIZE + SHA_DIGEST_SIZE,
    MAX_RECORD_SIZE = 16384,    /* 2^14, max size by standard */
    MAX_MSG_EXTRA   = 68,       /* max added to msg, mac + pad */
    MAX_COMP_EXTRA  = 1024,     /* max compression extra */
    MAX_MTU         = 1500,     /* max expected MTU */
    MAX_UDP_SIZE    = MAX_MTU - 100,   /* don't exceed MTU w/ 100 byte header */
    MAX_DH_SZ       = 612,      /* 2240 p, pub, g + 2 byte size for each */
    MAX_STR_VERSION = 8,        /* string rep of protocol version */

    PAD_MD5        = 48,       /* pad length for finished */
    PAD_SHA        = 40,       /* pad length for finished */
    PEM_LINE_LEN   = 80,       /* PEM line max + fudge */
    LENGTH_SZ      =  2,       /* length field for HMAC, data only */
    VERSION_SZ     =  2,       /* length of proctocol version */
    SEQ_SZ         =  8,       /* 64 bit sequence number  */
    BYTE3_LEN      =  3,       /* up to 24 bit byte lengths */
    ALERT_SIZE     =  2,       /* level + description     */
    REQUEST_HEADER =  2,       /* always use 2 bytes      */
    VERIFY_HEADER  =  2,       /* always use 2 bytes      */
    MAX_DH_SIZE    = 513,      /* 4096 bit plus possible leading 0 */

    MAX_SUITE_SZ = 200,        /* 100 suites for now! */
    RAN_LEN      = 32,         /* random length           */
    SEED_LEN     = RAN_LEN * 2, /* tls prf seed length    */
    ID_LEN       = 32,         /* session id length       */
    MAX_COOKIE_LEN = 32,       /* max dtls cookie size    */
    SUITE_LEN    =  2,         /* cipher suite sz length  */
    ENUM_LEN     =  1,         /* always a byte           */
    COMP_LEN     =  1,         /* compression length      */
    CURVE_LEN    =  2,         /* ecc named curve length  */
    
    HANDSHAKE_HEADER_SZ = 4,   /* type + length(3)        */
    RECORD_HEADER_SZ    = 5,   /* type + version + len(2) */
    CERT_HEADER_SZ      = 3,   /* always 3 bytes          */
    REQ_HEADER_SZ       = 2,   /* cert request header sz  */
    HINT_LEN_SZ         = 2,   /* length of hint size field */

    DTLS_HANDSHAKE_HEADER_SZ = 12, /* normal + seq(2) + offset(3) + length(3) */
    DTLS_RECORD_HEADER_SZ    = 13, /* normal + epoch(2) + seq_num(6) */
    DTLS_HANDSHAKE_EXTRA     = 8,  /* diff from normal */
    DTLS_RECORD_EXTRA        = 8,  /* diff from normal */

    FINISHED_LABEL_SZ   = 15,  /* TLS finished label size */
    TLS_FINISHED_SZ     = 12,  /* TLS has a shorter size  */
    MASTER_LABEL_SZ     = 13,  /* TLS master secret label sz */
    KEY_LABEL_SZ        = 13,  /* TLS key block expansion sz */
    MAX_PRF_HALF        = 128, /* Maximum half secret len */
    MAX_PRF_LABSEED     = 80,  /* Maximum label + seed len */
    MAX_PRF_DIG         = 224, /* Maximum digest len      */
    MAX_REQUEST_SZ      = 256, /* Maximum cert req len (no auth yet */
    SESSION_FLUSH_COUNT = 256, /* Flush session cache unless user turns off */ 

    RC4_KEY_SIZE        = 16,  /* always 128bit           */
    DES_KEY_SIZE        =  8,  /* des                     */
    DES3_KEY_SIZE       = 24,  /* 3 des ede               */
    DES_IV_SIZE         = DES_BLOCK_SIZE,
    AES_256_KEY_SIZE    = 32,  /* for 256 bit             */
    AES_192_KEY_SIZE    = 24,  /* for 192 bit             */
    AES_IV_SIZE         = 16,  /* always block size       */
    AES_128_KEY_SIZE    = 16,  /* for 128 bit             */

    HC_128_KEY_SIZE     = 16,  /* 128 bits                */
    HC_128_IV_SIZE      = 16,  /* also 128 bits           */

    RABBIT_KEY_SIZE     = 16,  /* 128 bits                */
    RABBIT_IV_SIZE      =  8,  /* 64 bits for iv          */

    EVP_SALT_SIZE       =  8,  /* evp salt size 64 bits   */

    ECDHE_SIZE          = 32,  /* ECHDE server size defaults to 256 bit */
    MAX_EXPORT_ECC_SZ   = 256, /* Export ANS X9.62 max future size */

    MAX_HELLO_SZ       = 128,  /* max client or server hello */
    MAX_CERT_VERIFY_SZ = 1024, /* max   */
    CLIENT_HELLO_FIRST =  35,  /* Protocol + RAN_LEN + sizeof(id_len) */
    MAX_SUITE_NAME     =  48,  /* maximum length of cipher suite string */
    DEFAULT_TIMEOUT    = 500,  /* default resumption timeout in seconds */

    MAX_PSK_ID_LEN     = 128,  /* max psk identity/hint supported */
    MAX_PSK_KEY_LEN    =  64,  /* max psk key supported */

#ifdef FORTRESS
    MAX_EX_DATA        =   3,  /* allow for three items of ex_data */
    MAX_CHAIN_DEPTH    =   9,  /* max cert chain peer depth, FORTRESS option */
#else
    MAX_CHAIN_DEPTH    =   4,  /* max cert chain peer depth */
#endif
    MAX_X509_SIZE      = 2048, /* max static x509 buffer size */
    CERT_MIN_SIZE      =  256, /* min PEM cert size with header/footer */
    MAX_FILENAME_SZ    =  256, /* max file name length */
    FILE_BUFFER_SIZE   = 1024, /* default static file buffer size for input,
                                  will use dynamic buffer if not big enough */

    MAX_NTRU_PUB_KEY_SZ = 1027, /* NTRU max for now */
    MAX_NTRU_ENCRYPT_SZ = 1027, /* NTRU max for now */
    MAX_NTRU_BITS       =  256, /* max symmetric bit strength */
    NO_SNIFF           =   0,  /* not sniffing */
    SNIFF              =   1,  /* currently sniffing */

    HASH_SIG_SIZE      =   2,  /* default SHA1 RSA */

    NO_COPY            =   0,  /* should we copy static buffer for write */
    COPY               =   1   /* should we copy static buffer for write */
};


/* states */
enum states {
    NULL_STATE = 0,

    SERVER_HELLOVERIFYREQUEST_COMPLETE,
    SERVER_HELLO_COMPLETE,
    SERVER_CERT_COMPLETE,
    SERVER_KEYEXCHANGE_COMPLETE,
    SERVER_HELLODONE_COMPLETE,
    SERVER_FINISHED_COMPLETE,

    CLIENT_HELLO_COMPLETE,
    CLIENT_KEYEXCHANGE_COMPLETE,
    CLIENT_FINISHED_COMPLETE,

    HANDSHAKE_DONE
};



/* SSL Version */
typedef struct ProtocolVersion {
    byte major;
    byte minor;
} ProtocolVersion;


CYASSL_LOCAL ProtocolVersion MakeSSLv3(void);
CYASSL_LOCAL ProtocolVersion MakeTLSv1(void);
CYASSL_LOCAL ProtocolVersion MakeTLSv1_1(void);
CYASSL_LOCAL ProtocolVersion MakeTLSv1_2(void);

#ifdef CYASSL_DTLS
    CYASSL_LOCAL ProtocolVersion MakeDTLSv1(void);
#endif


enum BIO_TYPE {
    BIO_BUFFER = 1,
    BIO_SOCKET = 2,
    BIO_SSL    = 3,
    BIO_MEMORY = 4
};


/* CyaSSL BIO_METHOD type */
struct CYASSL_BIO_METHOD {
    byte type;               /* method type */
};


/* CyaSSL BIO type */
struct CYASSL_BIO {
    byte        type;          /* method type */
    byte        close;         /* close flag */
    byte        eof;           /* eof flag */
    CYASSL*     ssl;           /* possible associated ssl */
    byte*       mem;           /* memory buffer */
    int         memLen;        /* memory buffer length */
    int         fd;            /* possible file descriptor */
    CYASSL_BIO* prev;          /* previous in chain */
    CYASSL_BIO* next;          /* next in chain */
};


/* CyaSSL method type */
struct CYASSL_METHOD {
    ProtocolVersion version;
    byte            side;         /* connection side, server or client */
    byte            verifyPeer;   /* request or send certificate       */
    byte            verifyNone;   /* whether to verify certificate     */
    byte            failNoCert;   /* fail if no certificate            */
    byte            downgrade;    /* whether to downgrade version, default no */
};


/* defautls to client */
CYASSL_LOCAL void InitSSL_Method(CYASSL_METHOD*, ProtocolVersion);

/* for sniffer */
CYASSL_LOCAL int DoFinished(CYASSL* ssl, const byte* input, word32* inOutIdx,
                            int sniff);
CYASSL_LOCAL int DoApplicationData(CYASSL* ssl, byte* input, word32* inOutIdx);


/* CyaSSL buffer type */
typedef struct buffer {
    word32 length;
    byte*  buffer;
} buffer;


enum {
    FORCED_FREE = 1,
    NO_FORCED_FREE = 0
};


/* only use compression extra if using compression */
#ifdef HAVE_LIBZ
    #define COMP_EXTRA MAX_COMP_EXTRA
#else
    #define COMP_EXTRA 0
#endif

/* only the sniffer needs space in the buffer for an extra MTU record */
#ifdef CYASSL_SNIFFER
    #define MTU_EXTRA MAX_MTU
#else
    #define MTU_EXTRA 0
#endif

/* give user option to use 16K static buffers, sniffer needs them too */
#if defined(LARGE_STATIC_BUFFERS) || defined(CYASSL_SNIFFER)
    #define RECORD_SIZE MAX_RECORD_SIZE
#else
    #ifdef CYASSL_DTLS
        #define RECORD_SIZE MAX_MTU 
    #else
        #define RECORD_SIZE 128 
    #endif
#endif


/* user option to turn off 16K output option */
/* if using small static buffers (default) and SSL_write tries to write data
   larger than the record we have, dynamically get it, unless user says only
   write in static buffer chuncks  */
#ifndef STATIC_CHUNKS_ONLY
    #define OUTPUT_RECORD_SIZE MAX_RECORD_SIZE
#else
    #define OUTPUT_RECORD_SIZE RECORD_SIZE
#endif

/* CyaSSL input buffer

   RFC 2246:

   length
       The length (in bytes) of the following TLSPlaintext.fragment.
       The length should not exceed 2^14.
*/
#define STATIC_BUFFER_LEN RECORD_HEADER_SZ + RECORD_SIZE + COMP_EXTRA + \
        MTU_EXTRA + MAX_MSG_EXTRA

typedef struct {
    word32 length;       /* total buffer length used */
    word32 idx;          /* idx to part of length already consumed */
    byte*  buffer;       /* place holder for static or dynamic buffer */
    ALIGN16 byte staticBuffer[STATIC_BUFFER_LEN];
    word32 bufferSize;   /* current buffer size */
    byte   dynamicFlag;  /* dynamic memory currently in use */
} bufferStatic;

/* Cipher Suites holder */
typedef struct Suites {
    int    setSuites;               /* user set suites from default */
    byte   suites[MAX_SUITE_SZ];  
    word16 suiteSz;                 /* suite length in bytes        */
} Suites;


CYASSL_LOCAL
void InitSuites(Suites*, ProtocolVersion, byte, byte, byte, byte, byte, int);
CYASSL_LOCAL
int  SetCipherList(Suites*, const char* list);

#ifndef PSK_TYPES_DEFINED
    typedef unsigned int (*psk_client_callback)(CYASSL*, const char*, char*,
                          unsigned int, unsigned char*, unsigned int);
    typedef unsigned int (*psk_server_callback)(CYASSL*, const char*,
                          unsigned char*, unsigned int);
#endif /* PSK_TYPES_DEFINED */


#ifndef CYASSL_USER_IO
    /* default IO callbacks */
    CYASSL_LOCAL
    int EmbedReceive(char *buf, int sz, void *ctx);
    CYASSL_LOCAL 
    int EmbedSend(char *buf, int sz, void *ctx);
#endif

#ifdef CYASSL_DTLS
    CYASSL_LOCAL
    int IsUDP(void*);
#endif


/* CyaSSL Cipher type just points back to SSL */
struct CYASSL_CIPHER {
    CYASSL* ssl;
};


#ifdef SINGLE_THREADED
    typedef int CyaSSL_Mutex;
#else /* MULTI_THREADED */
    /* Comes first to enable use of FreeRTOS Windows simulator only. */
    #ifdef FREERTOS
        typedef xSemaphoreHandle CyaSSL_Mutex;
    #elif defined(USE_WINDOWS_API)
        typedef CRITICAL_SECTION CyaSSL_Mutex;
    #elif defined(CYASSL_PTHREADS)
        typedef pthread_mutex_t CyaSSL_Mutex;
    #elif defined(THREADX)
        typedef TX_MUTEX CyaSSL_Mutex;
    #elif defined(MICRIUM)
        typedef OS_MUTEX CyaSSL_Mutex;
    #else
        #error Need a mutex type in multithreaded mode
    #endif /* USE_WINDOWS_API */
#endif /* SINGLE_THREADED */

CYASSL_LOCAL int InitMutex(CyaSSL_Mutex*);
CYASSL_LOCAL int FreeMutex(CyaSSL_Mutex*);
CYASSL_LOCAL int LockMutex(CyaSSL_Mutex*);
CYASSL_LOCAL int UnLockMutex(CyaSSL_Mutex*);



typedef struct CRL_Entry CRL_Entry;

/* Complete CRL */
struct CRL_Entry {
    CRL_Entry* next;                      /* next entry */
    byte    issuerHash[SHA_DIGEST_SIZE];  /* issuer hash                 */ 
    byte    crlHash[MD5_DIGEST_SIZE];     /* raw crl data hash           */ 
    byte    lastDate[MAX_DATE_SIZE]; /* last date updated  */
    byte    nextDate[MAX_DATE_SIZE]; /* next update date   */
    RevokedCert* certs;              /* revoked cert list  */
    int          totalCerts;         /* number on list     */
};


/* CyaSSL CRL controller */
struct CYASSL_CRL {
    CYASSL_CERT_MANAGER* cm;            /* pointer back to cert manager */
    CRL_Entry*           crlList;       /* our CRL list */
    CyaSSL_Mutex         crlLock;       /* CRL list lock */
};


/* CyaSSL Certificate Manager */
struct CYASSL_CERT_MANAGER {
    Signer*         caList;             /* the CA signer list */
    CyaSSL_Mutex    caLock;             /* CA list lock */
    CallbackCACache caCacheCallback;    /* CA cache addition callback */
    void*           heap;               /* heap helper */
    CYASSL_CRL*     crl;                /* CRL checker */
    byte            crlEnabled;         /* is CRL on ? */
    byte            crlCheckAll;        /* always leaf, but all ? */
    CbMissingCRL    cbMissingCRL;       /* notify through cb of missing crl */
};


/* CyaSSL context type */
struct CYASSL_CTX {
    CYASSL_METHOD* method;
    CyaSSL_Mutex   countMutex;    /* reference count mutex */
    int         refCount;         /* reference count */
    buffer      certificate;
    buffer      certChain;
                 /* chain after self, in DER, with leading size for each cert */
    buffer      privateKey;
    buffer      serverDH_P;
    buffer      serverDH_G;
    CYASSL_CERT_MANAGER* cm;      /* our cert manager, ctx owns SSL will use */
    Suites      suites;
    void*       heap;             /* for user memory overrides */
    byte        verifyPeer;
    byte        verifyNone;
    byte        failNoCert;
    byte        sessionCacheOff;
    byte        sessionCacheFlushOff;
    byte        sendVerify;       /* for client side */
    byte        haveDH;           /* server DH parms set by user */
    byte        haveNTRU;         /* server private NTRU  key loaded */
    byte        haveECDSA;        /* server cert signed w/ ECDSA loaded */
    byte        haveStaticECC;    /* static server ECC private key */
    byte        partialWrite;     /* only one msg per write call */
    byte        quietShutdown;    /* don't send close notify */
    byte        groupMessages;    /* group handshake messages before sending */
    CallbackIORecv CBIORecv;
    CallbackIOSend CBIOSend;
    VerifyCallback  verifyCallback;     /* cert verification callback */
    word32          timeout;            /* session timeout */
#ifdef HAVE_ECC
    word16          eccTempKeySz;       /* in octets 20 - 66 */
#endif
#ifndef NO_PSK
    byte        havePSK;                /* psk key set by user */
    psk_client_callback client_psk_cb;  /* client callback */
    psk_server_callback server_psk_cb;  /* server callback */
    char        server_hint[MAX_PSK_ID_LEN];
#endif /* NO_PSK */
#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
    pem_password_cb passwd_cb;
    void*            userdata;
#endif /* OPENSSL_EXTRA */
#ifdef HAVE_OCSP
    CYASSL_OCSP      ocsp;
#endif
};


CYASSL_LOCAL
int InitSSL_Ctx(CYASSL_CTX*, CYASSL_METHOD*);
CYASSL_LOCAL
void FreeSSL_Ctx(CYASSL_CTX*);
CYASSL_LOCAL
void SSL_CtxResourceFree(CYASSL_CTX*);

CYASSL_LOCAL
int DeriveTlsKeys(CYASSL* ssl);
CYASSL_LOCAL
int ProcessOldClientHello(CYASSL* ssl, const byte* input, word32* inOutIdx,
                          word32 inSz, word16 sz);
CYASSL_LOCAL
int AddCA(CYASSL_CERT_MANAGER* ctx, buffer der, int type, int verify);
CYASSL_LOCAL
int AlreadySigner(CYASSL_CERT_MANAGER* cm, byte* hash);

/* All cipher suite related info */
typedef struct CipherSpecs {
    byte bulk_cipher_algorithm;
    byte cipher_type;               /* block or stream */
    byte mac_algorithm;
    byte kea;                       /* key exchange algo */
    byte sig_algo;
    byte hash_size;
    byte pad_size;
    byte static_ecdh;
    word16 key_size;
    word16 iv_size;
    word16 block_size;
} CipherSpecs;



/* Supported Ciphers from page 43  */
enum BulkCipherAlgorithm { 
    cipher_null,
    rc4,
    rc2,
    des,
    triple_des,             /* leading 3 (3des) not valid identifier */
    des40,
    idea,
    aes,
    hc128,                  /* CyaSSL extensions */
    rabbit
};


/* Supported Message Authentication Codes from page 43 */
enum MACAlgorithm { 
    no_mac = 0,
    md5_mac,
    sha_mac,
    sha224_mac,
    sha256_mac,
    sha384_mac,
    sha512_mac,
    rmd_mac
};


/* Supported Key Exchange Protocols */
enum KeyExchangeAlgorithm { 
    no_kea = 0,
    rsa_kea, 
    diffie_hellman_kea, 
    fortezza_kea,
    psk_kea,
    ntru_kea,
    ecc_diffie_hellman_kea
};


/* Supported Authentication Schemes */
enum SignatureAlgorithm {
    anonymous_sa_algo = 0,
    rsa_sa_algo,
    dsa_sa_algo,
    ecc_dsa_sa_algo
};


/* Supprted ECC Curve Types */
enum EccCurves {
    named_curve = 3
};


/* Supprted ECC Named Curves */
enum EccNamedCurves {
    secp256r1 = 0x17,         /* default, OpenSSL also calls it prime256v1 */
    secp384r1 = 0x18,
    secp521r1 = 0x19,

    secp160r1 = 0x10,
    secp192r1 = 0x13,        /*           Openssl also call it prime192v1 */
    secp224r1 = 0x15
};


/* Valid client certificate request types from page 27 */
enum ClientCertificateType {    
    rsa_sign            = 1, 
    dss_sign            = 2,
    rsa_fixed_dh        = 3,
    dss_fixed_dh        = 4,
    rsa_ephemeral_dh    = 5,
    dss_ephemeral_dh    = 6,
    fortezza_kea_cert   = 20
};


enum CipherType { stream, block };


/* keys and secrets */
typedef struct Keys {
    byte client_write_MAC_secret[SHA256_DIGEST_SIZE];   /* max sizes */
    byte server_write_MAC_secret[SHA256_DIGEST_SIZE]; 
    byte client_write_key[AES_256_KEY_SIZE];         /* max sizes */
    byte server_write_key[AES_256_KEY_SIZE]; 
    byte client_write_IV[AES_IV_SIZE];               /* max sizes */
    byte server_write_IV[AES_IV_SIZE];

    word32 peer_sequence_number;
    word32 sequence_number;
    
#ifdef CYASSL_DTLS
    word32 dtls_sequence_number;
    word32 dtls_peer_sequence_number;
    word16 dtls_handshake_number;
    word16 dtls_epoch;
    word16 dtls_peer_epoch;
#endif

    word32 encryptSz;             /* last size of encrypted data   */
    byte   encryptionOn;          /* true after change cipher spec */
} Keys;


/* cipher for now */
typedef union {
#ifdef BUILD_ARC4
    Arc4   arc4;
#endif
#ifdef BUILD_DES3
    Des3   des3;
#endif
#ifdef BUILD_AES
    Aes    aes;
#endif
#ifdef HAVE_HC128
    HC128  hc128;
#endif
#ifdef BUILD_RABBIT
    Rabbit rabbit;
#endif
} Ciphers;


/* hashes type */
typedef struct Hashes {
    byte md5[MD5_DIGEST_SIZE];
    byte sha[SHA_DIGEST_SIZE];
} Hashes;


/* Static x509 buffer */
typedef struct x509_buffer {
    int  length;                  /* actual size */
    byte buffer[MAX_X509_SIZE];   /* max static cert size */
} x509_buffer;


/* CyaSSL X509_CHAIN, for no dynamic memory SESSION_CACHE */
struct CYASSL_X509_CHAIN {
    int         count;                    /* total number in chain */
    x509_buffer certs[MAX_CHAIN_DEPTH];   /* only allow max depth 4 for now */
};


/* CyaSSL session type */
struct CYASSL_SESSION {
    byte         sessionID[ID_LEN];
    byte         masterSecret[SECRET_LEN];
    word32       bornOn;                        /* create time in seconds   */
    word32       timeout;                       /* timeout in seconds       */
#ifdef SESSION_CERTS
    CYASSL_X509_CHAIN chain;                      /* peer cert chain, static  */
    ProtocolVersion version;
    byte            cipherSuite0;               /* first byte, normally 0 */
    byte            cipherSuite;                /* 2nd byte, actual suite */
#endif
};


CYASSL_LOCAL
CYASSL_SESSION* GetSession(CYASSL*, byte*);
CYASSL_LOCAL
int          SetSession(CYASSL*, CYASSL_SESSION*);

typedef void (*hmacfp) (CYASSL*, byte*, const byte*, word32, int, int);


/* client connect state for nonblocking restart */
enum ConnectState {
    CONNECT_BEGIN = 0,
    CLIENT_HELLO_SENT,
    HELLO_AGAIN,               /* HELLO_AGAIN s for DTLS case */
    HELLO_AGAIN_REPLY,
    FIRST_REPLY_DONE,
    FIRST_REPLY_FIRST,
    FIRST_REPLY_SECOND,
    FIRST_REPLY_THIRD,
    FIRST_REPLY_FOURTH,
    FINISHED_DONE,
    SECOND_REPLY_DONE
};


/* server accept state for nonblocking restart */
enum AcceptState {
    ACCEPT_BEGIN = 0,
    ACCEPT_CLIENT_HELLO_DONE,
    HELLO_VERIFY_SENT,
    ACCEPT_FIRST_REPLY_DONE,
    SERVER_HELLO_SENT,
    CERT_SENT,
    KEY_EXCHANGE_SENT,
    CERT_REQ_SENT,
    SERVER_HELLO_DONE,
    ACCEPT_SECOND_REPLY_DONE,
    CHANGE_CIPHER_SENT,
    ACCEPT_FINISHED_DONE,
    ACCEPT_THIRD_REPLY_DONE
};


typedef struct Buffers {
    buffer          certificate;            /* CYASSL_CTX owns, unless we own */
    buffer          key;                    /* CYASSL_CTX owns, unless we own */
    buffer          certChain;              /* CYASSL_CTX owns */
                 /* chain after self, in DER, with leading size for each cert */
    buffer          domainName;             /* for client check */
    buffer          serverDH_P;             /* CYASSL_CTX owns, unless we own */
    buffer          serverDH_G;             /* CYASSL_CTX owns, unless we own */
    buffer          serverDH_Pub;
    buffer          serverDH_Priv;
    bufferStatic    inputBuffer;
    bufferStatic    outputBuffer;
    buffer          clearOutputBuffer;
    int             prevSent;              /* previous plain text bytes sent
                                              when got WANT_WRITE            */
    int             plainSz;               /* plain text bytes in buffer to send
                                              when got WANT_WRITE            */
    byte            weOwnCert;             /* SSL own cert flag */
    byte            weOwnKey;              /* SSL own key  flag */
    byte            weOwnDH;               /* SSL own dh (p,g)  flag */
} Buffers;


typedef struct Options {
    byte            sessionCacheOff;
    byte            sessionCacheFlushOff;
    byte            cipherSuite0;           /* first byte, normally 0 */
    byte            cipherSuite;            /* second byte, actual suite */
    byte            serverState;
    byte            clientState;
    byte            handShakeState;
    byte            side;               /* client or server end */
    byte            verifyPeer;
    byte            verifyNone;
    byte            failNoCert;
    byte            downgrade;          /* allow downgrade of versions */
    byte            sendVerify;         /* false = 0, true = 1, sendBlank = 2 */
    byte            resuming;
    byte            haveSessionId;      /* server may not send */
    byte            tls;                /* using TLS ? */
    byte            tls1_1;             /* using TLSv1.1+ ? */
    byte            dtls;               /* using datagrams ? */
    byte            connReset;          /* has the peer reset */
    byte            isClosed;           /* if we consider conn closed */
    byte            closeNotify;        /* we've recieved a close notify */
    byte            sentNotify;         /* we've sent a close notify */
    byte            connectState;       /* nonblocking resume */
    byte            acceptState;        /* nonblocking resume */
    byte            usingCompression;   /* are we using compression */
    byte            haveDH;             /* server DH parms set by user */
    byte            haveNTRU;           /* server NTRU  private key loaded */
    byte            haveECDSA;          /* server ECDSA signed cert */
    byte            haveStaticECC;      /* static server ECC private key */
    byte            havePeerCert;       /* do we have peer's cert */
    byte            usingPSK_cipher;    /* whether we're using psk as cipher */
    byte            sendAlertState;     /* nonblocking resume */ 
    byte            processReply;       /* nonblocking resume */
    byte            partialWrite;       /* only one msg per write call */
    byte            quietShutdown;      /* don't send close notify */
    byte            certOnly;           /* stop once we get cert */
    byte            groupMessages;      /* group handshake messages */
#ifndef NO_PSK
    byte            havePSK;            /* psk key set by user */
    psk_client_callback client_psk_cb;
    psk_server_callback server_psk_cb;
#endif /* NO_PSK */
} Options;


typedef struct Arrays {
    byte            clientRandom[RAN_LEN];
    byte            serverRandom[RAN_LEN];
    byte            sessionID[ID_LEN];
    byte            preMasterSecret[ENCRYPT_LEN];
    byte            masterSecret[SECRET_LEN];
#ifdef CYASSL_DTLS
    byte            cookie[MAX_COOKIE_LEN];
#endif
#ifndef NO_PSK
    char            client_identity[MAX_PSK_ID_LEN];
    char            server_hint[MAX_PSK_ID_LEN];
    byte            psk_key[MAX_PSK_KEY_LEN];
    word32          psk_keySz;          /* acutal size */
#endif
    word32          preMasterSz;        /* differs for DH, actual size */
} Arrays;


struct CYASSL_X509_NAME {
    char  name[ASN_NAME_MAX];
    int   sz;
};


struct CYASSL_X509 {
    CYASSL_X509_NAME issuer;
    CYASSL_X509_NAME subject;
    int              serialSz;
    byte             serial[EXTERNAL_SERIAL_SIZE];
    char             subjectCN[ASN_NAME_MAX];        /* common name short cut */
    buffer           derCert;                        /* may need  */
};


/* record layer header for PlainText, Compressed, and CipherText */
typedef struct RecordLayerHeader {
    byte            type;
    ProtocolVersion version;
    byte            length[2];
} RecordLayerHeader;


/* record layer header for DTLS PlainText, Compressed, and CipherText */
typedef struct DtlsRecordLayerHeader {
    byte            type;
    ProtocolVersion version;
    byte            epoch[2];             /* increment on cipher state change */
    byte            sequence_number[6];   /* per record */
    byte            length[2];
} DtlsRecordLayerHeader;


/* CyaSSL ssl type */
struct CYASSL {
    CYASSL_CTX*     ctx;
    int             error;
    ProtocolVersion version;            /* negotiated version */
    ProtocolVersion chVersion;          /* client hello version */
    Suites          suites;
    Ciphers         encrypt;
    Ciphers         decrypt;
    CipherSpecs     specs;
    Keys            keys;
    int             rfd;                /* read  file descriptor */
    int             wfd;                /* write file descriptor */
    CYASSL_BIO*     biord;              /* socket bio read  to free/close */
    CYASSL_BIO*     biowr;              /* socket bio write to free/close */
    void*           IOCB_ReadCtx;
    void*           IOCB_WriteCtx;
    RNG             rng;
    Md5             hashMd5;            /* md5 hash of handshake msgs */
    Sha             hashSha;            /* sha hash of handshake msgs */
#ifndef NO_SHA256
    Sha256          hashSha256;         /* sha256 hash of handshake msgs */
#endif
    Hashes          verifyHashes;
    Hashes          certHashes;         /* for cert verify */
    Buffers         buffers;
    Options         options;
    Arrays          arrays;
    CYASSL_SESSION  session;
    VerifyCallback  verifyCallback;      /* cert verification callback */
    RsaKey          peerRsaKey;
    byte            peerRsaKeyPresent;
#ifdef HAVE_NTRU
    word16          peerNtruKeyLen;
    byte            peerNtruKey[MAX_NTRU_PUB_KEY_SZ];
    byte            peerNtruKeyPresent;
#endif
#ifdef HAVE_ECC
    ecc_key         peerEccKey;              /* peer's  ECDHE key */
    ecc_key         peerEccDsaKey;           /* peer's  ECDSA key */
    ecc_key         eccTempKey;              /* private ECDHE key */
    ecc_key         eccDsaKey;               /* private ECDSA key */
    word16          eccTempKeySz;            /* in octets 20 - 66 */
    byte            peerEccKeyPresent;
    byte            peerEccDsaKeyPresent;
    byte            eccTempKeyPresent;
    byte            eccDsaKeyPresent;
#endif
    hmacfp          hmac;
    void*           heap;               /* for user overrides */
    RecordLayerHeader curRL;
    word16            curSize;
    word32          timeout;            /* session timeout */
    CYASSL_CIPHER   cipher;
#ifdef HAVE_LIBZ
    z_stream        c_stream;           /* compression   stream */
    z_stream        d_stream;           /* decompression stream */
    byte            didStreamInit;      /* for stream init and end */
#endif
#ifdef CYASSL_CALLBACKS
    HandShakeInfo   handShakeInfo;      /* info saved during handshake */
    TimeoutInfo     timeoutInfo;        /* info saved during handshake */
    byte            hsInfoOn;           /* track handshake info        */
    byte            toInfoOn;           /* track timeout   info        */
#endif
#ifdef OPENSSL_EXTRA
    CYASSL_X509     peerCert;           /* X509 peer cert */
#endif
#ifdef FORTRESS
    void*           ex_data[MAX_EX_DATA]; /* external data, for Fortress */
#endif
};


CYASSL_LOCAL
int  InitSSL(CYASSL*, CYASSL_CTX*);
CYASSL_LOCAL
void FreeSSL(CYASSL*);
CYASSL_API void SSL_ResourceFree(CYASSL*);   /* Micrium uses */


enum {
    IV_SZ   = 32,          /* max iv sz */
    NAME_SZ = 80,          /* max one line */
};


typedef struct EncryptedInfo {
    char     name[NAME_SZ];    /* encryption name */
    byte     iv[IV_SZ];        /* encrypted IV */
    word32   ivSz;             /* encrypted IV size */
    long     consumed;         /* tracks PEM bytes consumed */
    byte     set;              /* if encryption set */
    CYASSL_CTX* ctx;              /* CTX owner */
} EncryptedInfo;

CYASSL_LOCAL int PemToDer(const unsigned char* buff, long sz, int type,
                          buffer* der, void* heap, EncryptedInfo* info,
                          int* eccKey);

CYASSL_LOCAL int ProcessFile(CYASSL_CTX* ctx, const char* fname, int format,
                             int type, CYASSL* ssl, int userChain,
                            CYASSL_CRL* crl);


#ifdef CYASSL_CALLBACKS
    CYASSL_LOCAL
    void InitHandShakeInfo(HandShakeInfo*);
    CYASSL_LOCAL 
    void FinishHandShakeInfo(HandShakeInfo*, const CYASSL*);
    CYASSL_LOCAL 
    void AddPacketName(const char*, HandShakeInfo*);

    CYASSL_LOCAL
    void InitTimeoutInfo(TimeoutInfo*);
    CYASSL_LOCAL 
    void FreeTimeoutInfo(TimeoutInfo*, void*);
    CYASSL_LOCAL 
    void AddPacketInfo(const char*, TimeoutInfo*, const byte*, int, void*);
    CYASSL_LOCAL 
    void AddLateName(const char*, TimeoutInfo*);
    CYASSL_LOCAL 
    void AddLateRecordHeader(const RecordLayerHeader* rl, TimeoutInfo* info);
#endif


/* Record Layer Header identifier from page 12 */
enum ContentType {
    no_type            = 0,
    change_cipher_spec = 20, 
    alert              = 21, 
    handshake          = 22, 
    application_data   = 23 
};


/* handshake header, same for each message type, pgs 20/21 */
typedef struct HandShakeHeader {
    byte            type;
    word24          length;
} HandShakeHeader;


/* DTLS handshake header, same for each message type */
typedef struct DtlsHandShakeHeader {
    byte            type;
    word24          length;
    byte            message_seq[2];    /* start at 0, restransmit gets same # */
    word24          fragment_offset;   /* bytes in previous fragments */
    word24          fragment_length;   /* length of this fragment */
} DtlsHandShakeHeader;


enum HandShakeType {
    no_shake            = -1,
    hello_request       = 0, 
    client_hello        = 1, 
    server_hello        = 2,
    hello_verify_request = 3,       /* DTLS addition */
    certificate         = 11, 
    server_key_exchange = 12,
    certificate_request = 13, 
    server_hello_done   = 14,
    certificate_verify  = 15, 
    client_key_exchange = 16,
    finished            = 20
};


/* Valid Alert types from page 16/17 */
enum AlertDescription {
    close_notify            = 0,
    unexpected_message      = 10,
    bad_record_mac          = 20,
    decompression_failure   = 30,
    handshake_failure       = 40,
    no_certificate          = 41,
    bad_certificate         = 42,
    unsupported_certificate = 43,
    certificate_revoked     = 44,
    certificate_expired     = 45,
    certificate_unknown     = 46,
    illegal_parameter       = 47,
    decrypt_error           = 51,
    protocol_version        = 70,
    no_renegotiation        = 100
};


/* I/O Callback default errors */
enum IOerrors {
    IO_ERR_GENERAL    = -1,     /* general unexpected err, not in below group */
    IO_ERR_WANT_READ  = -2,     /* need to call read  again */
    IO_ERR_WANT_WRITE = -2,     /* need to call write again */
    IO_ERR_CONN_RST   = -3,     /* connection reset */
    IO_ERR_ISR        = -4,     /* interrupt */
    IO_ERR_CONN_CLOSE = -5      /* connection closed or epipe */
};


enum AlertLevel { 
    alert_warning = 1, 
    alert_fatal = 2
};


static const byte client[SIZEOF_SENDER] = { 0x43, 0x4C, 0x4E, 0x54 };
static const byte server[SIZEOF_SENDER] = { 0x53, 0x52, 0x56, 0x52 };

static const byte tls_client[FINISHED_LABEL_SZ + 1] = "client finished";
static const byte tls_server[FINISHED_LABEL_SZ + 1] = "server finished";


/* internal functions */
CYASSL_LOCAL int SendChangeCipher(CYASSL*);
CYASSL_LOCAL int SendData(CYASSL*, const void*, int);
CYASSL_LOCAL int SendCertificate(CYASSL*);
CYASSL_LOCAL int SendCertificateRequest(CYASSL*);
CYASSL_LOCAL int SendServerKeyExchange(CYASSL*);
CYASSL_LOCAL int SendBuffered(CYASSL*);
CYASSL_LOCAL int ReceiveData(CYASSL*, byte*, int);
CYASSL_LOCAL int SendFinished(CYASSL*);
CYASSL_LOCAL int SendAlert(CYASSL*, int, int);
CYASSL_LOCAL int ProcessReply(CYASSL*);

CYASSL_LOCAL int SetCipherSpecs(CYASSL*);
CYASSL_LOCAL int MakeMasterSecret(CYASSL*);

CYASSL_LOCAL int  AddSession(CYASSL*);
CYASSL_LOCAL int  DeriveKeys(CYASSL* ssl);
CYASSL_LOCAL int  StoreKeys(CYASSL* ssl, const byte* keyData);

CYASSL_LOCAL int IsTLS(const CYASSL* ssl);
CYASSL_LOCAL int IsAtLeastTLSv1_2(const CYASSL* ssl);

CYASSL_LOCAL void ShrinkInputBuffer(CYASSL* ssl, int forcedFree);
CYASSL_LOCAL void ShrinkOutputBuffer(CYASSL* ssl);
CYASSL_LOCAL int SendHelloVerifyRequest(CYASSL* ssl);
CYASSL_LOCAL Signer* GetCA(void* cm, byte* hash);
CYASSL_LOCAL void BuildTlsFinished(CYASSL* ssl, Hashes* hashes,
                                   const byte* sender);
#ifndef NO_TLS
    CYASSL_LOCAL int  MakeTlsMasterSecret(CYASSL*);
    CYASSL_LOCAL void TLS_hmac(CYASSL* ssl, byte* digest, const byte* buffer,
                               word32 sz, int content, int verify);
#endif

#ifndef NO_CYASSL_CLIENT
    CYASSL_LOCAL int SendClientHello(CYASSL*);
    CYASSL_LOCAL int SendClientKeyExchange(CYASSL*);
    CYASSL_LOCAL int SendCertificateVerify(CYASSL*);
#endif /* NO_CYASSL_CLIENT */

#ifndef NO_CYASSL_SERVER
    CYASSL_LOCAL int SendServerHello(CYASSL*);
    CYASSL_LOCAL int SendServerHelloDone(CYASSL*);
    #ifdef CYASSL_DTLS
        CYASSL_LOCAL int SendHelloVerifyRequest(CYASSL*);
    #endif
#endif /* NO_CYASSL_SERVER */


#ifndef NO_TLS
    

#endif /* NO_TLS */



typedef double timer_d;

CYASSL_LOCAL timer_d Timer(void);
CYASSL_LOCAL word32  LowResTimer(void);



#ifdef __cplusplus
    }  /* extern "C" */
#endif

#endif /* CyaSSL_INT_H */

