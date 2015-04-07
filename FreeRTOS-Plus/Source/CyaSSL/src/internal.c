/* internal.c
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

#include <cyassl/internal.h>
#include <cyassl/error-ssl.h>
#include <cyassl/ctaocrypt/asn.h>

#ifdef HAVE_LIBZ
    #include "zlib.h"
#endif

#ifdef HAVE_NTRU
    #include "ntru_crypto.h"
#endif

#if defined(DEBUG_CYASSL) || defined(SHOW_SECRETS)
    #ifdef FREESCALE_MQX
        #include <fio.h>
    #else
        #include <stdio.h>
    #endif
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


#if defined(CYASSL_CALLBACKS) && !defined(LARGE_STATIC_BUFFERS)
    #error \
CYASSL_CALLBACKS needs LARGE_STATIC_BUFFERS, please add LARGE_STATIC_BUFFERS
#endif


#ifndef NO_CYASSL_CLIENT
    static int DoHelloVerifyRequest(CYASSL* ssl, const byte* input, word32*,
                                                                        word32);
    static int DoServerHello(CYASSL* ssl, const byte* input, word32*, word32);
    static int DoServerKeyExchange(CYASSL* ssl, const byte* input, word32*,
                                                                        word32);
    #ifndef NO_CERTS
        static int DoCertificateRequest(CYASSL* ssl, const byte* input, word32*,
                                                                        word32);
    #endif
#endif


#ifndef NO_CYASSL_SERVER
    static int DoClientHello(CYASSL* ssl, const byte* input, word32*, word32);
    static int DoClientKeyExchange(CYASSL* ssl, byte* input, word32*, word32);
    #if !defined(NO_RSA) || defined(HAVE_ECC)
        static int DoCertificateVerify(CYASSL* ssl, byte*, word32*, word32);
    #endif
#endif


#ifdef CYASSL_DTLS
    static INLINE int DtlsCheckWindow(DtlsState* state);
    static INLINE int DtlsUpdateWindow(DtlsState* state);
#endif


typedef enum {
    doProcessInit = 0,
#ifndef NO_CYASSL_SERVER
    runProcessOldClientHello,
#endif
    getRecordLayerHeader,
    getData,
    runProcessingOneMessage
} processReply;

#ifndef NO_OLD_TLS
static int SSL_hmac(CYASSL* ssl, byte* digest, const byte* in, word32 sz,
                    int content, int verify);

#endif

#ifndef NO_CERTS
static int BuildCertHashes(CYASSL* ssl, Hashes* hashes);
#endif

static void PickHashSigAlgo(CYASSL* ssl,
                                const byte* hashSigAlgo, word32 hashSigAlgoSz);

#ifndef min

    static INLINE word32 min(word32 a, word32 b)
    {
        return a > b ? b : a;
    }

#endif /* min */


int IsTLS(const CYASSL* ssl)
{
    if (ssl->version.major == SSLv3_MAJOR && ssl->version.minor >=TLSv1_MINOR)
        return 1;

    return 0;
}


int IsAtLeastTLSv1_2(const CYASSL* ssl)
{
    if (ssl->version.major == SSLv3_MAJOR && ssl->version.minor >=TLSv1_2_MINOR)
        return 1;
    if (ssl->version.major == DTLS_MAJOR && ssl->version.minor <= DTLSv1_2_MINOR)
        return 1;

    return 0;
}


#ifdef HAVE_NTRU

static byte GetEntropy(ENTROPY_CMD cmd, byte* out)
{
    /* TODO: add locking? */
    static RNG rng;

    if (cmd == INIT)
        return (InitRng(&rng) == 0) ? 1 : 0;

    if (out == NULL)
        return 0;

    if (cmd == GET_BYTE_OF_ENTROPY)
        return (RNG_GenerateBlock(&rng, out, 1) == 0) ? 1 : 0;

    if (cmd == GET_NUM_BYTES_PER_BYTE_OF_ENTROPY) {
        *out = 1;
        return 1;
    }

    return 0;
}

#endif /* HAVE_NTRU */

/* used by ssl.c too */
void c32to24(word32 in, word24 out)
{
    out[0] = (in >> 16) & 0xff;
    out[1] = (in >>  8) & 0xff;
    out[2] =  in & 0xff;
}


#ifdef CYASSL_DTLS

static INLINE void c32to48(word32 in, byte out[6])
{
    out[0] = 0;
    out[1] = 0;
    out[2] = (in >> 24) & 0xff;
    out[3] = (in >> 16) & 0xff;
    out[4] = (in >>  8) & 0xff;
    out[5] =  in & 0xff;
}

#endif /* CYASSL_DTLS */


/* convert 16 bit integer to opaque */
static INLINE void c16toa(word16 u16, byte* c)
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


/* convert a 24 bit integer into a 32 bit one */
static INLINE void c24to32(const word24 u24, word32* u32)
{
    *u32 = (u24[0] << 16) | (u24[1] << 8) | u24[2];
}


/* convert opaque to 16 bit integer */
static INLINE void ato16(const byte* c, word16* u16)
{
    *u16 = (word16) ((c[0] << 8) | (c[1]));
}


#ifdef CYASSL_DTLS

/* convert opaque to 32 bit integer */
static INLINE void ato32(const byte* c, word32* u32)
{
    *u32 = (c[0] << 24) | (c[1] << 16) | (c[2] << 8) | c[3];
}

#endif /* CYASSL_DTLS */


#ifdef HAVE_LIBZ

    /* alloc user allocs to work with zlib */
    static void* myAlloc(void* opaque, unsigned int item, unsigned int size)
    {
        (void)opaque;
        return XMALLOC(item * size, opaque, DYNAMIC_TYPE_LIBZ);
    }


    static void myFree(void* opaque, void* memory)
    {
        (void)opaque;
        XFREE(memory, opaque, DYNAMIC_TYPE_LIBZ);
    }


    /* init zlib comp/decomp streams, 0 on success */
    static int InitStreams(CYASSL* ssl)
    {
        ssl->c_stream.zalloc = (alloc_func)myAlloc;
        ssl->c_stream.zfree  = (free_func)myFree;
        ssl->c_stream.opaque = (voidpf)ssl->heap;

        if (deflateInit(&ssl->c_stream, Z_DEFAULT_COMPRESSION) != Z_OK)
            return ZLIB_INIT_ERROR;

        ssl->didStreamInit = 1;

        ssl->d_stream.zalloc = (alloc_func)myAlloc;
        ssl->d_stream.zfree  = (free_func)myFree;
        ssl->d_stream.opaque = (voidpf)ssl->heap;

        if (inflateInit(&ssl->d_stream) != Z_OK) return ZLIB_INIT_ERROR;

        return 0;
    }


    static void FreeStreams(CYASSL* ssl)
    {
        if (ssl->didStreamInit) {
            deflateEnd(&ssl->c_stream);
            inflateEnd(&ssl->d_stream);
        }
    }


    /* compress in to out, return out size or error */
    static int myCompress(CYASSL* ssl, byte* in, int inSz, byte* out, int outSz)
    {
        int    err;
        int    currTotal = (int)ssl->c_stream.total_out;

        ssl->c_stream.next_in   = in;
        ssl->c_stream.avail_in  = inSz;
        ssl->c_stream.next_out  = out;
        ssl->c_stream.avail_out = outSz;

        err = deflate(&ssl->c_stream, Z_SYNC_FLUSH);
        if (err != Z_OK && err != Z_STREAM_END) return ZLIB_COMPRESS_ERROR;

        return (int)ssl->c_stream.total_out - currTotal;
    }
        

    /* decompress in to out, returnn out size or error */
    static int myDeCompress(CYASSL* ssl, byte* in,int inSz, byte* out,int outSz)
    {
        int    err;
        int    currTotal = (int)ssl->d_stream.total_out;

        ssl->d_stream.next_in   = in;
        ssl->d_stream.avail_in  = inSz;
        ssl->d_stream.next_out  = out;
        ssl->d_stream.avail_out = outSz;

        err = inflate(&ssl->d_stream, Z_SYNC_FLUSH);
        if (err != Z_OK && err != Z_STREAM_END) return ZLIB_DECOMPRESS_ERROR;

        return (int)ssl->d_stream.total_out - currTotal;
    }
        
#endif /* HAVE_LIBZ */


void InitSSL_Method(CYASSL_METHOD* method, ProtocolVersion pv)
{
    method->version    = pv;
    method->side       = CYASSL_CLIENT_END;
    method->downgrade  = 0;
}


/* Initialze SSL context, return 0 on success */
int InitSSL_Ctx(CYASSL_CTX* ctx, CYASSL_METHOD* method)
{
    ctx->method = method;
    ctx->refCount = 1;          /* so either CTX_free or SSL_free can release */
#ifndef NO_CERTS
    ctx->certificate.buffer = 0;
    ctx->certChain.buffer   = 0;
    ctx->privateKey.buffer  = 0;
    ctx->serverDH_P.buffer  = 0;
    ctx->serverDH_G.buffer  = 0;
#endif
    ctx->haveDH             = 0;
    ctx->haveNTRU           = 0;    /* start off */
    ctx->haveECDSAsig       = 0;    /* start off */
    ctx->haveStaticECC      = 0;    /* start off */
    ctx->heap               = ctx;  /* defaults to self */
#ifndef NO_PSK
    ctx->havePSK            = 0;
    ctx->server_hint[0]     = 0;
    ctx->client_psk_cb      = 0;
    ctx->server_psk_cb      = 0;
#endif /* NO_PSK */
#ifdef HAVE_ECC
    ctx->eccTempKeySz       = ECDHE_SIZE;   
#endif

#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
    ctx->passwd_cb   = 0;
    ctx->userdata    = 0;
#endif /* OPENSSL_EXTRA */

    ctx->timeout = DEFAULT_TIMEOUT;

#ifndef CYASSL_USER_IO
    ctx->CBIORecv = EmbedReceive;
    ctx->CBIOSend = EmbedSend;
    #ifdef CYASSL_DTLS
        if (method->version.major == DTLS_MAJOR) {
            ctx->CBIORecv   = EmbedReceiveFrom;
            ctx->CBIOSend   = EmbedSendTo;
            ctx->CBIOCookie = EmbedGenerateCookie;
        }
    #endif
#else
    /* user will set */
    ctx->CBIORecv   = NULL;
    ctx->CBIOSend   = NULL;
    #ifdef CYASSL_DTLS
        ctx->CBIOCookie = NULL;
    #endif
#endif /* CYASSL_USER_IO */
#ifdef HAVE_NETX
    ctx->CBIORecv = NetX_Receive;
    ctx->CBIOSend = NetX_Send;
#endif
    ctx->partialWrite   = 0;
    ctx->verifyCallback = 0;

#ifndef NO_CERTS
    ctx->cm = CyaSSL_CertManagerNew();
#endif
#ifdef HAVE_NTRU
    if (method->side == CYASSL_CLIENT_END)
        ctx->haveNTRU = 1;           /* always on cliet side */
                                     /* server can turn on by loading key */
#endif
#ifdef HAVE_ECC
    if (method->side == CYASSL_CLIENT_END) {
        ctx->haveECDSAsig  = 1;        /* always on cliet side */
        ctx->haveStaticECC = 1;        /* server can turn on by loading key */
    }
#endif
    ctx->suites.setSuites = 0;  /* user hasn't set yet */
    /* remove DH later if server didn't set, add psk later */
    InitSuites(&ctx->suites, method->version, TRUE, FALSE, TRUE, ctx->haveNTRU,
               ctx->haveECDSAsig, ctx->haveStaticECC, method->side);  
    ctx->verifyPeer = 0;
    ctx->verifyNone = 0;
    ctx->failNoCert = 0;
    ctx->sessionCacheOff      = 0;  /* initially on */
    ctx->sessionCacheFlushOff = 0;  /* initially on */
    ctx->sendVerify = 0;
    ctx->quietShutdown = 0;
    ctx->groupMessages = 0;
#ifdef HAVE_CAVIUM
    ctx->devId = NO_CAVIUM_DEVICE; 
#endif
#ifdef HAVE_TLS_EXTENSIONS
    ctx->extensions = NULL;
#endif
#ifdef ATOMIC_USER
    ctx->MacEncryptCb    = NULL;
    ctx->DecryptVerifyCb = NULL;
#endif
#ifdef HAVE_PK_CALLBACKS
    #ifdef HAVE_ECC
        ctx->EccSignCb   = NULL;
        ctx->EccVerifyCb = NULL;
    #endif /* HAVE_ECC */
    #ifndef NO_RSA 
        ctx->RsaSignCb   = NULL;
        ctx->RsaVerifyCb = NULL;
        ctx->RsaEncCb    = NULL;
        ctx->RsaDecCb    = NULL;
    #endif /* NO_RSA */
#endif /* HAVE_PK_CALLBACKS */

    if (InitMutex(&ctx->countMutex) < 0) {
        CYASSL_MSG("Mutex error on CTX init");
        return BAD_MUTEX_E;
    } 
#ifndef NO_CERTS
    if (ctx->cm == NULL) {
        CYASSL_MSG("Bad Cert Manager New");
        return BAD_CERT_MANAGER_ERROR;
    }
#endif
    return 0;
}


/* In case contexts are held in array and don't want to free actual ctx */
void SSL_CtxResourceFree(CYASSL_CTX* ctx)
{
    XFREE(ctx->method, ctx->heap, DYNAMIC_TYPE_METHOD);

#ifndef NO_CERTS
    XFREE(ctx->serverDH_G.buffer, ctx->heap, DYNAMIC_TYPE_DH);
    XFREE(ctx->serverDH_P.buffer, ctx->heap, DYNAMIC_TYPE_DH);
    XFREE(ctx->privateKey.buffer, ctx->heap, DYNAMIC_TYPE_KEY);
    XFREE(ctx->certificate.buffer, ctx->heap, DYNAMIC_TYPE_CERT);
    XFREE(ctx->certChain.buffer, ctx->heap, DYNAMIC_TYPE_CERT);
    CyaSSL_CertManagerFree(ctx->cm);
#endif
#ifdef HAVE_TLS_EXTENSIONS
    TLSX_FreeAll(ctx->extensions);
#endif
}


void FreeSSL_Ctx(CYASSL_CTX* ctx)
{
    int doFree = 0;

    if (LockMutex(&ctx->countMutex) != 0) {
        CYASSL_MSG("Couldn't lock count mutex");
        return;
    }
    ctx->refCount--;
    if (ctx->refCount == 0)
        doFree = 1;
    UnLockMutex(&ctx->countMutex);

    if (doFree) {
        CYASSL_MSG("CTX ref count down to 0, doing full free");
        SSL_CtxResourceFree(ctx);
        FreeMutex(&ctx->countMutex);
        XFREE(ctx, ctx->heap, DYNAMIC_TYPE_CTX);
    }
    else {
        (void)ctx;
        CYASSL_MSG("CTX ref count not 0 yet, no free");
    }
}


/* Set cipher pointers to null */
void InitCiphers(CYASSL* ssl)
{
#ifdef BUILD_ARC4
    ssl->encrypt.arc4 = NULL;
    ssl->decrypt.arc4 = NULL;
#endif
#ifdef BUILD_DES3
    ssl->encrypt.des3 = NULL;
    ssl->decrypt.des3 = NULL;
#endif
#ifdef BUILD_AES
    ssl->encrypt.aes = NULL;
    ssl->decrypt.aes = NULL;
#endif
#ifdef HAVE_CAMELLIA
    ssl->encrypt.cam = NULL;
    ssl->decrypt.cam = NULL;
#endif
#ifdef HAVE_HC128
    ssl->encrypt.hc128 = NULL;
    ssl->decrypt.hc128 = NULL;
#endif
#ifdef BUILD_RABBIT
    ssl->encrypt.rabbit = NULL;
    ssl->decrypt.rabbit = NULL;
#endif
    ssl->encrypt.setup = 0;
    ssl->decrypt.setup = 0;
}


/* Free ciphers */
void FreeCiphers(CYASSL* ssl)
{
    (void)ssl;
#ifdef BUILD_ARC4
    #ifdef HAVE_CAVIUM
    if (ssl->devId != NO_CAVIUM_DEVICE) {
        Arc4FreeCavium(ssl->encrypt.arc4);
        Arc4FreeCavium(ssl->decrypt.arc4);
    }
    #endif
    XFREE(ssl->encrypt.arc4, ssl->heap, DYNAMIC_TYPE_CIPHER);
    XFREE(ssl->decrypt.arc4, ssl->heap, DYNAMIC_TYPE_CIPHER);
#endif
#ifdef BUILD_DES3
    #ifdef HAVE_CAVIUM
    if (ssl->devId != NO_CAVIUM_DEVICE) {
        Des3_FreeCavium(ssl->encrypt.des3);
        Des3_FreeCavium(ssl->decrypt.des3);
    }
    #endif
    XFREE(ssl->encrypt.des3, ssl->heap, DYNAMIC_TYPE_CIPHER);
    XFREE(ssl->decrypt.des3, ssl->heap, DYNAMIC_TYPE_CIPHER);
#endif
#ifdef BUILD_AES
    #ifdef HAVE_CAVIUM
    if (ssl->devId != NO_CAVIUM_DEVICE) {
        AesFreeCavium(ssl->encrypt.aes);
        AesFreeCavium(ssl->decrypt.aes);
    }
    #endif
    XFREE(ssl->encrypt.aes, ssl->heap, DYNAMIC_TYPE_CIPHER);
    XFREE(ssl->decrypt.aes, ssl->heap, DYNAMIC_TYPE_CIPHER);
#endif
#ifdef HAVE_CAMELLIA
    XFREE(ssl->encrypt.cam, ssl->heap, DYNAMIC_TYPE_CIPHER);
    XFREE(ssl->decrypt.cam, ssl->heap, DYNAMIC_TYPE_CIPHER);
#endif
#ifdef HAVE_HC128
    XFREE(ssl->encrypt.hc128, ssl->heap, DYNAMIC_TYPE_CIPHER);
    XFREE(ssl->decrypt.hc128, ssl->heap, DYNAMIC_TYPE_CIPHER);
#endif
#ifdef BUILD_RABBIT
    XFREE(ssl->encrypt.rabbit, ssl->heap, DYNAMIC_TYPE_CIPHER);
    XFREE(ssl->decrypt.rabbit, ssl->heap, DYNAMIC_TYPE_CIPHER);
#endif
}


void InitCipherSpecs(CipherSpecs* cs)
{
    cs->bulk_cipher_algorithm = INVALID_BYTE;
    cs->cipher_type           = INVALID_BYTE;
    cs->mac_algorithm         = INVALID_BYTE;
    cs->kea                   = INVALID_BYTE;
    cs->sig_algo              = INVALID_BYTE;

    cs->hash_size   = 0;
    cs->static_ecdh = 0;
    cs->key_size    = 0;
    cs->iv_size     = 0;
    cs->block_size  = 0;
}


void InitSuites(Suites* suites, ProtocolVersion pv, byte haveRSA, byte havePSK,
                byte haveDH, byte haveNTRU, byte haveECDSAsig,
                byte haveStaticECC, int side)
{
    word16 idx = 0;
    int    tls    = pv.major == SSLv3_MAJOR && pv.minor >= TLSv1_MINOR;
    int    tls1_2 = pv.major == SSLv3_MAJOR && pv.minor >= TLSv1_2_MINOR;
    int    haveRSAsig = 1;

    (void)tls;  /* shut up compiler */
    (void)tls1_2;
    (void)haveDH;
    (void)havePSK;
    (void)haveNTRU;
    (void)haveStaticECC;

    if (suites == NULL) {
        CYASSL_MSG("InitSuites pointer error");
        return; 
    }

    if (suites->setSuites)
        return;      /* trust user settings, don't override */

    if (side == CYASSL_SERVER_END && haveStaticECC) {
        haveRSA = 0;   /* can't do RSA with ECDSA key */
        (void)haveRSA; /* some builds won't read */
    }

    if (side == CYASSL_SERVER_END && haveECDSAsig) {
        haveRSAsig = 0;     /* can't have RSA sig if signed by ECDSA */
        (void)haveRSAsig;   /* non ecc builds won't read */
    }

#ifdef CYASSL_DTLS
    if (pv.major == DTLS_MAJOR) {
        tls    = 1;
        tls1_2 = pv.minor <= DTLSv1_2_MINOR;
    }
#endif

#ifdef HAVE_RENEGOTIATION_INDICATION
    if (side == CYASSL_CLIENT_END) {
        suites->suites[idx++] = 0;
        suites->suites[idx++] = TLS_EMPTY_RENEGOTIATION_INFO_SCSV;
    }
#endif

#ifdef BUILD_TLS_NTRU_RSA_WITH_AES_256_CBC_SHA
    if (tls && haveNTRU && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_NTRU_RSA_WITH_AES_256_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_NTRU_RSA_WITH_AES_128_CBC_SHA
    if (tls && haveNTRU && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_NTRU_RSA_WITH_AES_128_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_NTRU_RSA_WITH_RC4_128_SHA
    if (tls && haveNTRU && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_NTRU_RSA_WITH_RC4_128_SHA;
    }
#endif

#ifdef BUILD_TLS_NTRU_RSA_WITH_3DES_EDE_CBC_SHA
    if (tls && haveNTRU && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_NTRU_RSA_WITH_3DES_EDE_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256
    if (tls1_2 && haveRSAsig) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256;
    }
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256
    if (tls1_2 && haveECDSAsig) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256;
    }
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_128_CBC_SHA256
    if (tls1_2 && haveRSAsig && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_ECDH_RSA_WITH_AES_128_CBC_SHA256;
    }
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA256
    if (tls1_2 && haveECDSAsig && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA256;
    }
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384
    if (tls1_2 && haveRSAsig) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384;
    }
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA384
    if (tls1_2 && haveECDSAsig) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA384;
    }
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_256_CBC_SHA384
    if (tls1_2 && haveRSAsig && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_ECDH_RSA_WITH_AES_256_CBC_SHA384;
    }
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA384
    if (tls1_2 && haveECDSAsig && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA384;
    }
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384
    if (tls1_2 && haveECDSAsig) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384;
    }
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA
    if (tls && haveECDSAsig) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_256_GCM_SHA384
    if (tls1_2 && haveECDSAsig && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_ECDH_ECDSA_WITH_AES_256_GCM_SHA384;
    }
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA
    if (tls && haveECDSAsig && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256
    if (tls1_2 && haveECDSAsig) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256;
    }
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA
    if (tls && haveECDSAsig) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_128_GCM_SHA256
    if (tls1_2 && haveECDSAsig && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_ECDH_ECDSA_WITH_AES_128_GCM_SHA256;
    }
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA
    if (tls && haveECDSAsig && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_RC4_128_SHA
    if (tls && haveECDSAsig) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDHE_ECDSA_WITH_RC4_128_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_RC4_128_SHA
    if (tls && haveECDSAsig && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDH_ECDSA_WITH_RC4_128_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA
    if (tls && haveECDSAsig) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA
    if (tls && haveECDSAsig && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384
    if (tls1_2 && haveRSA) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384;
    }
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA
    if (tls && haveRSA) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_256_GCM_SHA384
    if (tls1_2 && haveRSAsig && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_ECDH_RSA_WITH_AES_256_GCM_SHA384;
    }
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_256_CBC_SHA
    if (tls && haveRSAsig && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDH_RSA_WITH_AES_256_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
    if (tls1_2 && haveRSA) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256;
    }
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA
    if (tls && haveRSA) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_128_GCM_SHA256
    if (tls1_2 && haveRSAsig && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_ECDH_RSA_WITH_AES_128_GCM_SHA256;
    }
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_128_CBC_SHA
    if (tls && haveRSAsig && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDH_RSA_WITH_AES_128_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_RC4_128_SHA
    if (tls && haveRSA) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDHE_RSA_WITH_RC4_128_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_RC4_128_SHA
    if (tls && haveRSAsig && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDH_RSA_WITH_RC4_128_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA
    if (tls && haveRSA) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA
    if (tls && haveRSAsig && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_256_GCM_SHA384
    if (tls1_2 && haveDH && haveRSA) {
        suites->suites[idx++] = 0;
        suites->suites[idx++] = TLS_DHE_RSA_WITH_AES_256_GCM_SHA384;
    }
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CCM_8
    if (tls1_2 && haveECDSAsig) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDHE_ECDSA_WITH_AES_128_CCM_8;
    }
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CCM_8
    if (tls1_2 && haveECDSAsig) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDHE_ECDSA_WITH_AES_256_CCM_8;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_CCM_8
    if (tls1_2 && haveRSA) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_RSA_WITH_AES_128_CCM_8;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_CCM_8
    if (tls1_2 && haveRSA) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_RSA_WITH_AES_256_CCM_8;
    }
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_256_CBC_SHA256
    if (tls1_2 && haveDH && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_DHE_RSA_WITH_AES_256_CBC_SHA256;
    }
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_128_GCM_SHA256
    if (tls1_2 && haveDH && haveRSA) {
        suites->suites[idx++] = 0;
        suites->suites[idx++] = TLS_DHE_RSA_WITH_AES_128_GCM_SHA256;
    }
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_128_CBC_SHA256
    if (tls1_2 && haveDH && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_DHE_RSA_WITH_AES_128_CBC_SHA256;
    }
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_256_CBC_SHA
    if (tls && haveDH && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_DHE_RSA_WITH_AES_256_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_128_CBC_SHA
    if (tls && haveDH && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_DHE_RSA_WITH_AES_128_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_GCM_SHA384
    if (tls1_2 && haveRSA) {
        suites->suites[idx++] = 0;
        suites->suites[idx++] = TLS_RSA_WITH_AES_256_GCM_SHA384;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_CBC_SHA256
    if (tls1_2 && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_AES_256_CBC_SHA256;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_GCM_SHA256
    if (tls1_2 && haveRSA) {
        suites->suites[idx++] = 0;
        suites->suites[idx++] = TLS_RSA_WITH_AES_128_GCM_SHA256;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_CBC_SHA256
    if (tls1_2 && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_AES_128_CBC_SHA256;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_CBC_SHA
    if (tls && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_AES_256_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_CBC_SHA
    if (tls && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_AES_128_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_NULL_SHA
    if (tls && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_NULL_SHA;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_NULL_SHA256
    if (tls && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_NULL_SHA256;
    }
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_256_GCM_SHA384
    if (tls1_2 && haveDH && havePSK) {
        suites->suites[idx++] = 0;
        suites->suites[idx++] = TLS_DHE_PSK_WITH_AES_256_GCM_SHA384;
    }
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_GCM_SHA384
    if (tls1_2 && havePSK) {
        suites->suites[idx++] = 0;
        suites->suites[idx++] = TLS_PSK_WITH_AES_256_GCM_SHA384;
    }
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_CBC_SHA
    if (tls && havePSK) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_PSK_WITH_AES_256_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_256_CBC_SHA384
    if (tls && haveDH && havePSK) {
        suites->suites[idx++] = 0;
        suites->suites[idx++] = TLS_DHE_PSK_WITH_AES_256_CBC_SHA384;
    }
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_CBC_SHA384
    if (tls && havePSK) {
        suites->suites[idx++] = 0;
        suites->suites[idx++] = TLS_PSK_WITH_AES_256_CBC_SHA384;
    }
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_128_GCM_SHA256
    if (tls1_2 && haveDH && havePSK) {
        suites->suites[idx++] = 0;
        suites->suites[idx++] = TLS_DHE_PSK_WITH_AES_128_GCM_SHA256;
    }
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_GCM_SHA256
    if (tls1_2 && havePSK) {
        suites->suites[idx++] = 0;
        suites->suites[idx++] = TLS_PSK_WITH_AES_128_GCM_SHA256;
    }
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_128_CBC_SHA256
    if (tls && haveDH && havePSK) {
        suites->suites[idx++] = 0;
        suites->suites[idx++] = TLS_DHE_PSK_WITH_AES_128_CBC_SHA256;
    }
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CBC_SHA256
    if (tls && havePSK) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_PSK_WITH_AES_128_CBC_SHA256;
    }
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CBC_SHA
    if (tls && havePSK) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_PSK_WITH_AES_128_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_128_CCM
    if (tls && haveDH && havePSK) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_DHE_PSK_WITH_AES_128_CCM;
    }
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_256_CCM
    if (tls && haveDH && havePSK) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_DHE_PSK_WITH_AES_256_CCM;
    }
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CCM
    if (tls && havePSK) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_PSK_WITH_AES_128_CCM;
    }
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_CCM
    if (tls && havePSK) {
        suites->suites[idx++] = ECC_BYTE;
        suites->suites[idx++] = TLS_PSK_WITH_AES_256_CCM;
    }
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CCM_8
    if (tls && havePSK) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_PSK_WITH_AES_128_CCM_8;
    }
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_CCM_8
    if (tls && havePSK) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_PSK_WITH_AES_256_CCM_8;
    }
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_NULL_SHA384
    if (tls && haveDH && havePSK) {
        suites->suites[idx++] = 0;
        suites->suites[idx++] = TLS_DHE_PSK_WITH_NULL_SHA384;
    }
#endif

#ifdef BUILD_TLS_PSK_WITH_NULL_SHA384
    if (tls && havePSK) {
        suites->suites[idx++] = 0;
        suites->suites[idx++] = TLS_PSK_WITH_NULL_SHA384;
    }
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_NULL_SHA256
    if (tls && haveDH && havePSK) {
        suites->suites[idx++] = 0;
        suites->suites[idx++] = TLS_DHE_PSK_WITH_NULL_SHA256;
    }
#endif

#ifdef BUILD_TLS_PSK_WITH_NULL_SHA256
    if (tls && havePSK) {
        suites->suites[idx++] = 0;
        suites->suites[idx++] = TLS_PSK_WITH_NULL_SHA256;
    }
#endif

#ifdef BUILD_TLS_PSK_WITH_NULL_SHA
    if (tls && havePSK) {
        suites->suites[idx++] = 0;
        suites->suites[idx++] = TLS_PSK_WITH_NULL_SHA;
    }
#endif

#ifdef BUILD_SSL_RSA_WITH_RC4_128_SHA
    if (haveRSA ) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = SSL_RSA_WITH_RC4_128_SHA;
    }
#endif

#ifdef BUILD_SSL_RSA_WITH_RC4_128_MD5
    if (haveRSA ) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = SSL_RSA_WITH_RC4_128_MD5;
    }
#endif

#ifdef BUILD_SSL_RSA_WITH_3DES_EDE_CBC_SHA
    if (haveRSA ) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = SSL_RSA_WITH_3DES_EDE_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_HC_128_MD5
    if (tls && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_HC_128_MD5;
    }
#endif
    
#ifdef BUILD_TLS_RSA_WITH_HC_128_SHA
    if (tls && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_HC_128_SHA;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_HC_128_B2B256
    if (tls && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_HC_128_B2B256;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_CBC_B2B256
    if (tls && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_AES_128_CBC_B2B256;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_CBC_B2B256
    if (tls && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_AES_256_CBC_B2B256;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_RABBIT_SHA
    if (tls && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_RABBIT_SHA;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_CAMELLIA_128_CBC_SHA
    if (tls && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_CAMELLIA_128_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA
    if (tls && haveDH && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_CAMELLIA_256_CBC_SHA
    if (tls && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_CAMELLIA_256_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_DHE_WITH_RSA_CAMELLIA_256_CBC_SHA
    if (tls && haveDH && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_CAMELLIA_128_CBC_SHA256
    if (tls && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_CAMELLIA_128_CBC_SHA256;
    }
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA256
    if (tls && haveDH && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA256;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_CAMELLIA_256_CBC_SHA256
    if (tls && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_CAMELLIA_256_CBC_SHA256;
    }
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA256
    if (tls && haveDH && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA256;
    }
#endif

    suites->suiteSz = idx;

    {
        idx = 0;
        
        if (haveECDSAsig) {
            #ifdef CYASSL_SHA384
                suites->hashSigAlgo[idx++] = sha384_mac;
                suites->hashSigAlgo[idx++] = ecc_dsa_sa_algo;
            #endif
            #ifndef NO_SHA256
                suites->hashSigAlgo[idx++] = sha256_mac;
                suites->hashSigAlgo[idx++] = ecc_dsa_sa_algo;
            #endif
            #ifndef NO_SHA
                suites->hashSigAlgo[idx++] = sha_mac;
                suites->hashSigAlgo[idx++] = ecc_dsa_sa_algo;
            #endif
        }

        if (haveRSAsig) {
            #ifdef CYASSL_SHA384
                suites->hashSigAlgo[idx++] = sha384_mac;
                suites->hashSigAlgo[idx++] = rsa_sa_algo;
            #endif
            #ifndef NO_SHA256
                suites->hashSigAlgo[idx++] = sha256_mac;
                suites->hashSigAlgo[idx++] = rsa_sa_algo;
            #endif
            #ifndef NO_SHA
                suites->hashSigAlgo[idx++] = sha_mac;
                suites->hashSigAlgo[idx++] = rsa_sa_algo;
            #endif
        }

        suites->hashSigAlgoSz = idx;
    }
}


#ifndef NO_CERTS


void InitX509Name(CYASSL_X509_NAME* name, int dynamicFlag)
{
    (void)dynamicFlag;

    if (name != NULL) {
        name->name        = name->staticName;
        name->dynamicName = 0;
#ifdef OPENSSL_EXTRA
        XMEMSET(&name->fullName, 0, sizeof(DecodedName));
#endif /* OPENSSL_EXTRA */
    }
}


void FreeX509Name(CYASSL_X509_NAME* name)
{
    if (name != NULL) {
        if (name->dynamicName)
            XFREE(name->name, NULL, DYNAMIC_TYPE_SUBJECT_CN);
#ifdef OPENSSL_EXTRA
        if (name->fullName.fullName != NULL)
            XFREE(name->fullName.fullName, NULL, DYNAMIC_TYPE_X509);
#endif /* OPENSSL_EXTRA */
    }
}


/* Initialize CyaSSL X509 type */
void InitX509(CYASSL_X509* x509, int dynamicFlag)
{
    InitX509Name(&x509->issuer, 0);
    InitX509Name(&x509->subject, 0);
    x509->version        = 0;
    x509->pubKey.buffer  = NULL;
    x509->sig.buffer     = NULL;
    x509->derCert.buffer = NULL;
    x509->altNames       = NULL;
    x509->altNamesNext   = NULL;
    x509->dynamicMemory  = (byte)dynamicFlag;
    x509->isCa           = 0;
#ifdef HAVE_ECC
    x509->pkCurveOID = 0;
#endif /* HAVE_ECC */
#ifdef OPENSSL_EXTRA
    x509->pathLength     = 0;
    x509->basicConstSet  = 0;
    x509->basicConstCrit = 0;
    x509->basicConstPlSet = 0;
    x509->subjAltNameSet = 0;
    x509->subjAltNameCrit = 0;
    x509->authKeyIdSet   = 0;
    x509->authKeyIdCrit  = 0;
    x509->authKeyId      = NULL;
    x509->authKeyIdSz    = 0;
    x509->subjKeyIdSet   = 0;
    x509->subjKeyIdCrit  = 0;
    x509->subjKeyId      = NULL;
    x509->subjKeyIdSz    = 0;
    x509->keyUsageSet    = 0;
    x509->keyUsageCrit   = 0;
    x509->keyUsage       = 0;
    #ifdef CYASSL_SEP
        x509->certPolicySet  = 0;
        x509->certPolicyCrit = 0;
    #endif /* CYASSL_SEP */
#endif /* OPENSSL_EXTRA */
}


/* Free CyaSSL X509 type */
void FreeX509(CYASSL_X509* x509)
{
    if (x509 == NULL)
        return;

    FreeX509Name(&x509->issuer);
    FreeX509Name(&x509->subject);
    if (x509->pubKey.buffer)
        XFREE(x509->pubKey.buffer, NULL, DYNAMIC_TYPE_PUBLIC_KEY);
    XFREE(x509->derCert.buffer, NULL, DYNAMIC_TYPE_SUBJECT_CN);
    XFREE(x509->sig.buffer, NULL, DYNAMIC_TYPE_SIGNATURE);
    #ifdef OPENSSL_EXTRA
        XFREE(x509->authKeyId, NULL, 0);
        XFREE(x509->subjKeyId, NULL, 0);
    #endif /* OPENSSL_EXTRA */
    if (x509->altNames)
        FreeAltNames(x509->altNames, NULL);
    if (x509->dynamicMemory)
        XFREE(x509, NULL, DYNAMIC_TYPE_X509);
}

#endif /* NO_CERTS */


/* init everything to 0, NULL, default values before calling anything that may
   fail so that desctructor has a "good" state to cleanup */
int InitSSL(CYASSL* ssl, CYASSL_CTX* ctx)
{
    int  ret;
    byte haveRSA = 0;
    byte havePSK = 0;

    ssl->ctx     = ctx; /* only for passing to calls, options could change */
    ssl->version = ctx->method->version;
    ssl->suites  = NULL;

#ifdef HAVE_LIBZ
    ssl->didStreamInit = 0;
#endif
#ifndef NO_RSA
    haveRSA = 1;
#endif
   
#ifndef NO_CERTS
    ssl->buffers.certificate.buffer   = 0;
    ssl->buffers.key.buffer           = 0;
    ssl->buffers.certChain.buffer     = 0;
#endif
    ssl->buffers.inputBuffer.length   = 0;
    ssl->buffers.inputBuffer.idx      = 0;
    ssl->buffers.inputBuffer.buffer = ssl->buffers.inputBuffer.staticBuffer;
    ssl->buffers.inputBuffer.bufferSize  = STATIC_BUFFER_LEN;
    ssl->buffers.inputBuffer.dynamicFlag = 0;
    ssl->buffers.inputBuffer.offset   = 0;
    ssl->buffers.outputBuffer.length  = 0;
    ssl->buffers.outputBuffer.idx     = 0;
    ssl->buffers.outputBuffer.buffer = ssl->buffers.outputBuffer.staticBuffer;
    ssl->buffers.outputBuffer.bufferSize  = STATIC_BUFFER_LEN;
    ssl->buffers.outputBuffer.dynamicFlag = 0;
    ssl->buffers.outputBuffer.offset      = 0;
    ssl->buffers.domainName.buffer    = 0;
#ifndef NO_CERTS
    ssl->buffers.serverDH_P.buffer    = 0;
    ssl->buffers.serverDH_G.buffer    = 0;
    ssl->buffers.serverDH_Pub.buffer  = 0;
    ssl->buffers.serverDH_Priv.buffer = 0;
#endif
    ssl->buffers.clearOutputBuffer.buffer  = 0;
    ssl->buffers.clearOutputBuffer.length  = 0;
    ssl->buffers.prevSent                  = 0;
    ssl->buffers.plainSz                   = 0;
#ifdef HAVE_PK_CALLBACKS
    #ifdef HAVE_ECC
        ssl->buffers.peerEccDsaKey.buffer = 0;
        ssl->buffers.peerEccDsaKey.length = 0;
    #endif /* HAVE_ECC */
    #ifndef NO_RSA 
        ssl->buffers.peerRsaKey.buffer = 0;
        ssl->buffers.peerRsaKey.length = 0;
    #endif /* NO_RSA */
#endif /* HAVE_PK_CALLBACKS */

#ifdef KEEP_PEER_CERT
    InitX509(&ssl->peerCert, 0);
#endif

#ifdef HAVE_ECC
    ssl->eccTempKeySz = ctx->eccTempKeySz;
    ssl->pkCurveOID = ctx->pkCurveOID;
    ssl->peerEccKeyPresent = 0;
    ssl->peerEccDsaKeyPresent = 0;
    ssl->eccDsaKeyPresent = 0;
    ssl->eccTempKeyPresent = 0;
    ssl->peerEccKey = NULL;
    ssl->peerEccDsaKey = NULL;
    ssl->eccDsaKey = NULL;
    ssl->eccTempKey = NULL;
#endif

    ssl->timeout = ctx->timeout;
    ssl->rfd = -1;   /* set to invalid descriptor */
    ssl->wfd = -1;
    ssl->rflags = 0;    /* no user flags yet */
    ssl->wflags = 0;    /* no user flags yet */
    ssl->biord = 0;
    ssl->biowr = 0;

    ssl->IOCB_ReadCtx  = &ssl->rfd;  /* prevent invalid pointer access if not */
    ssl->IOCB_WriteCtx = &ssl->wfd;  /* correctly set */
#ifdef HAVE_NETX
    ssl->nxCtx.nxSocket = NULL;
    ssl->nxCtx.nxPacket = NULL;
    ssl->nxCtx.nxOffset = 0;
    ssl->nxCtx.nxWait   = 0;
    ssl->IOCB_ReadCtx  = &ssl->nxCtx;  /* default NetX IO ctx, same for read */
    ssl->IOCB_WriteCtx = &ssl->nxCtx;  /* and write */
#endif
#ifdef CYASSL_DTLS
    ssl->IOCB_CookieCtx = NULL;      /* we don't use for default cb */
    ssl->dtls_expected_rx = MAX_MTU;
    ssl->keys.dtls_state.window = 0;
    ssl->keys.dtls_state.nextEpoch = 0;
    ssl->keys.dtls_state.nextSeq = 0;
#endif

#ifndef NO_OLD_TLS
#ifndef NO_MD5
    InitMd5(&ssl->hashMd5);
#endif
#ifndef NO_SHA
    ret = InitSha(&ssl->hashSha);
    if (ret != 0) {
        return ret;
    }
#endif
#endif
#ifndef NO_SHA256
    ret = InitSha256(&ssl->hashSha256);
    if (ret != 0) {
        return ret;
    }
#endif
#ifdef CYASSL_SHA384
    ret = InitSha384(&ssl->hashSha384);
    if (ret != 0) {
        return ret;
    }
#endif
#ifndef NO_RSA
    ssl->peerRsaKey = NULL;
    ssl->peerRsaKeyPresent = 0;
#endif
    ssl->verifyCallback    = ctx->verifyCallback;
    ssl->verifyCbCtx       = NULL;
    ssl->options.side      = ctx->method->side;
    ssl->options.downgrade = ctx->method->downgrade;
    ssl->error = 0;
    ssl->options.connReset = 0;
    ssl->options.isClosed  = 0;
    ssl->options.closeNotify  = 0;
    ssl->options.sentNotify   = 0;
    ssl->options.usingCompression = 0;
    if (ssl->options.side == CYASSL_SERVER_END)
        ssl->options.haveDH = ctx->haveDH;
    else
        ssl->options.haveDH = 0;
    ssl->options.haveNTRU      = ctx->haveNTRU;
    ssl->options.haveECDSAsig  = ctx->haveECDSAsig;
    ssl->options.haveStaticECC = ctx->haveStaticECC;
    ssl->options.havePeerCert    = 0; 
    ssl->options.havePeerVerify  = 0;
    ssl->options.usingPSK_cipher = 0;
    ssl->options.sendAlertState = 0;
#ifndef NO_PSK
    havePSK = ctx->havePSK;
    ssl->options.havePSK   = ctx->havePSK;
    ssl->options.client_psk_cb = ctx->client_psk_cb;
    ssl->options.server_psk_cb = ctx->server_psk_cb;
#endif /* NO_PSK */

    ssl->options.serverState = NULL_STATE;
    ssl->options.clientState = NULL_STATE;
    ssl->options.connectState = CONNECT_BEGIN;
    ssl->options.acceptState  = ACCEPT_BEGIN; 
    ssl->options.handShakeState  = NULL_STATE; 
    ssl->options.processReply = doProcessInit;

#ifdef CYASSL_DTLS
    ssl->keys.dtls_sequence_number      = 0;
    ssl->keys.dtls_state.curSeq         = 0;
    ssl->keys.dtls_state.nextSeq        = 0;
    ssl->keys.dtls_handshake_number     = 0;
    ssl->keys.dtls_expected_peer_handshake_number = 0;
    ssl->keys.dtls_epoch                = 0;
    ssl->keys.dtls_state.curEpoch       = 0;
    ssl->keys.dtls_state.nextEpoch      = 0;
    ssl->dtls_timeout_init              = DTLS_TIMEOUT_INIT;
    ssl->dtls_timeout_max               = DTLS_TIMEOUT_MAX;
    ssl->dtls_timeout                   = ssl->dtls_timeout_init;
    ssl->dtls_pool                      = NULL;
    ssl->dtls_msg_list                  = NULL;
#endif
    ssl->keys.encryptSz    = 0;
    ssl->keys.padSz        = 0;
    ssl->keys.encryptionOn = 0;     /* initially off */
    ssl->keys.decryptedCur = 0;     /* initially off */
    ssl->options.sessionCacheOff      = ctx->sessionCacheOff;
    ssl->options.sessionCacheFlushOff = ctx->sessionCacheFlushOff;

    ssl->options.verifyPeer = ctx->verifyPeer;
    ssl->options.verifyNone = ctx->verifyNone;
    ssl->options.failNoCert = ctx->failNoCert;
    ssl->options.sendVerify = ctx->sendVerify;
    
    ssl->options.resuming = 0;
    ssl->options.haveSessionId = 0;
    #ifndef NO_OLD_TLS
        ssl->hmac = SSL_hmac; /* default to SSLv3 */
    #else
        ssl->hmac = TLS_hmac;
    #endif
    ssl->heap = ctx->heap;    /* defaults to self */
    ssl->options.tls    = 0;
    ssl->options.tls1_1 = 0;
    ssl->options.dtls = ssl->version.major == DTLS_MAJOR;
    ssl->options.partialWrite  = ctx->partialWrite;
    ssl->options.quietShutdown = ctx->quietShutdown;
    ssl->options.certOnly = 0;
    ssl->options.groupMessages = ctx->groupMessages;
    ssl->options.usingNonblock = 0;
    ssl->options.saveArrays = 0;

#ifndef NO_CERTS
    /* ctx still owns certificate, certChain, key, dh, and cm */
    ssl->buffers.certificate = ctx->certificate;
    ssl->buffers.certChain = ctx->certChain;
    ssl->buffers.key = ctx->privateKey;
    if (ssl->options.side == CYASSL_SERVER_END) {
        ssl->buffers.serverDH_P = ctx->serverDH_P;
        ssl->buffers.serverDH_G = ctx->serverDH_G;
    }
#endif
    ssl->buffers.weOwnCert      = 0;
    ssl->buffers.weOwnCertChain = 0;
    ssl->buffers.weOwnKey       = 0;
    ssl->buffers.weOwnDH        = 0;

#ifdef CYASSL_DTLS
    ssl->buffers.dtlsCtx.fd = -1;
    ssl->buffers.dtlsCtx.peer.sa = NULL;
    ssl->buffers.dtlsCtx.peer.sz = 0;
#endif

#ifdef KEEP_PEER_CERT
    ssl->peerCert.issuer.sz    = 0;
    ssl->peerCert.subject.sz   = 0;
#endif
  
#ifdef SESSION_CERTS
    ssl->session.chain.count = 0;
#endif

#ifndef NO_CLIENT_CACHE
    ssl->session.idLen = 0;
#endif

    ssl->cipher.ssl = ssl;

#ifdef FORTRESS
    ssl->ex_data[0] = 0;
    ssl->ex_data[1] = 0;
    ssl->ex_data[2] = 0;
#endif

#ifdef CYASSL_CALLBACKS
    ssl->hsInfoOn = 0;
    ssl->toInfoOn = 0;
#endif

#ifdef HAVE_CAVIUM
    ssl->devId = ctx->devId; 
#endif

#ifdef HAVE_TLS_EXTENSIONS
    ssl->extensions = NULL;
#ifdef HAVE_MAX_FRAGMENT
    ssl->max_fragment = MAX_RECORD_SIZE;
#endif
#ifdef HAVE_TRUNCATED_HMAC
    ssl->truncated_hmac = 0;
#endif
#endif

    ssl->rng    = NULL;
    ssl->arrays = NULL;

    /* default alert state (none) */
    ssl->alert_history.last_rx.code  = -1;
    ssl->alert_history.last_rx.level = -1;
    ssl->alert_history.last_tx.code  = -1;
    ssl->alert_history.last_tx.level = -1;

    InitCiphers(ssl);
    InitCipherSpecs(&ssl->specs);
#ifdef ATOMIC_USER
    ssl->MacEncryptCtx    = NULL;
    ssl->DecryptVerifyCtx = NULL;
#endif
#ifdef HAVE_PK_CALLBACKS
    #ifdef HAVE_ECC
        ssl->EccSignCtx   = NULL;
        ssl->EccVerifyCtx = NULL;
    #endif /* HAVE_ECC */
    #ifndef NO_RSA 
        ssl->RsaSignCtx   = NULL;
        ssl->RsaVerifyCtx = NULL;
        ssl->RsaEncCtx    = NULL;
        ssl->RsaDecCtx    = NULL;
    #endif /* NO_RSA */
#endif /* HAVE_PK_CALLBACKS */

    /* all done with init, now can return errors, call other stuff */

    /* increment CTX reference count */
    if (LockMutex(&ctx->countMutex) != 0) {
        CYASSL_MSG("Couldn't lock CTX count mutex");
        return BAD_MUTEX_E;
    }
    ctx->refCount++;
    UnLockMutex(&ctx->countMutex);

    /* arrays */
    ssl->arrays = (Arrays*)XMALLOC(sizeof(Arrays), ssl->heap,
                                   DYNAMIC_TYPE_ARRAYS);
    if (ssl->arrays == NULL) {
        CYASSL_MSG("Arrays Memory error");
        return MEMORY_E;
    }
    XMEMSET(ssl->arrays, 0, sizeof(Arrays));

#ifndef NO_PSK
    ssl->arrays->client_identity[0] = 0;
    if (ctx->server_hint[0]) {   /* set in CTX */
        XSTRNCPY(ssl->arrays->server_hint, ctx->server_hint, MAX_PSK_ID_LEN);
        ssl->arrays->server_hint[MAX_PSK_ID_LEN - 1] = '\0';
    }
    else
        ssl->arrays->server_hint[0] = 0;
#endif /* NO_PSK */

#ifdef CYASSL_DTLS
    ssl->arrays->cookieSz = 0;
#endif

    /* RNG */
    ssl->rng = (RNG*)XMALLOC(sizeof(RNG), ssl->heap, DYNAMIC_TYPE_RNG);
    if (ssl->rng == NULL) {
        CYASSL_MSG("RNG Memory error");
        return MEMORY_E;
    }

    if ( (ret = InitRng(ssl->rng)) != 0) {
        CYASSL_MSG("RNG Init error");
        return ret;
    }

    /* suites */
    ssl->suites = (Suites*)XMALLOC(sizeof(Suites), ssl->heap,
                                   DYNAMIC_TYPE_SUITES);
    if (ssl->suites == NULL) {
        CYASSL_MSG("Suites Memory error");
        return MEMORY_E;
    }
    *ssl->suites = ctx->suites;

    /* peer key */
#ifndef NO_RSA
    ssl->peerRsaKey = (RsaKey*)XMALLOC(sizeof(RsaKey), ssl->heap,
                                       DYNAMIC_TYPE_RSA);
    if (ssl->peerRsaKey == NULL) {
        CYASSL_MSG("PeerRsaKey Memory error");
        return MEMORY_E;
    }
    ret = InitRsaKey(ssl->peerRsaKey, ctx->heap);
    if (ret != 0) return ret;
#endif
#ifndef NO_CERTS
    /* make sure server has cert and key unless using PSK */
    if (ssl->options.side == CYASSL_SERVER_END && !havePSK)
        if (!ssl->buffers.certificate.buffer || !ssl->buffers.key.buffer) {
            CYASSL_MSG("Server missing certificate and/or private key"); 
            return NO_PRIVATE_KEY;
        }
#endif
#ifdef HAVE_ECC
    ssl->peerEccKey = (ecc_key*)XMALLOC(sizeof(ecc_key),
                                                   ctx->heap, DYNAMIC_TYPE_ECC);
    if (ssl->peerEccKey == NULL) {
        CYASSL_MSG("PeerEccKey Memory error");
        return MEMORY_E;
    }
    ssl->peerEccDsaKey = (ecc_key*)XMALLOC(sizeof(ecc_key),
                                                   ctx->heap, DYNAMIC_TYPE_ECC);
    if (ssl->peerEccDsaKey == NULL) {
        CYASSL_MSG("PeerEccDsaKey Memory error");
        return MEMORY_E;
    }
    ssl->eccDsaKey = (ecc_key*)XMALLOC(sizeof(ecc_key),
                                                   ctx->heap, DYNAMIC_TYPE_ECC);
    if (ssl->eccDsaKey == NULL) {
        CYASSL_MSG("EccDsaKey Memory error");
        return MEMORY_E;
    }
    ssl->eccTempKey = (ecc_key*)XMALLOC(sizeof(ecc_key),
                                                   ctx->heap, DYNAMIC_TYPE_ECC);
    if (ssl->eccTempKey == NULL) {
        CYASSL_MSG("EccTempKey Memory error");
        return MEMORY_E;
    }
    ecc_init(ssl->peerEccKey);
    ecc_init(ssl->peerEccDsaKey);
    ecc_init(ssl->eccDsaKey);
    ecc_init(ssl->eccTempKey);
#endif

    /* make sure server has DH parms, and add PSK if there, add NTRU too */
    if (ssl->options.side == CYASSL_SERVER_END) 
        InitSuites(ssl->suites, ssl->version, haveRSA, havePSK,
                   ssl->options.haveDH, ssl->options.haveNTRU,
                   ssl->options.haveECDSAsig, ssl->options.haveStaticECC,
                   ssl->options.side);
    else 
        InitSuites(ssl->suites, ssl->version, haveRSA, havePSK, TRUE,
                   ssl->options.haveNTRU, ssl->options.haveECDSAsig,
                   ssl->options.haveStaticECC, ssl->options.side);

    return 0;
}


/* free use of temporary arrays */
void FreeArrays(CYASSL* ssl, int keep)
{
    if (ssl->arrays && keep) {
        /* keeps session id for user retrieval */
        XMEMCPY(ssl->session.sessionID, ssl->arrays->sessionID, ID_LEN);
    }
    XFREE(ssl->arrays, ssl->heap, DYNAMIC_TYPE_ARRAYS);
    ssl->arrays = NULL;
}


/* In case holding SSL object in array and don't want to free actual ssl */
void SSL_ResourceFree(CYASSL* ssl)
{
    FreeCiphers(ssl);
    FreeArrays(ssl, 0);
    XFREE(ssl->rng, ssl->heap, DYNAMIC_TYPE_RNG);
    XFREE(ssl->suites, ssl->heap, DYNAMIC_TYPE_SUITES);
    XFREE(ssl->buffers.domainName.buffer, ssl->heap, DYNAMIC_TYPE_DOMAIN);

#ifndef NO_CERTS
    XFREE(ssl->buffers.serverDH_Priv.buffer, ssl->heap, DYNAMIC_TYPE_DH);
    XFREE(ssl->buffers.serverDH_Pub.buffer, ssl->heap, DYNAMIC_TYPE_DH);
    /* parameters (p,g) may be owned by ctx */
    if (ssl->buffers.weOwnDH || ssl->options.side == CYASSL_CLIENT_END) {
        XFREE(ssl->buffers.serverDH_G.buffer, ssl->heap, DYNAMIC_TYPE_DH);
        XFREE(ssl->buffers.serverDH_P.buffer, ssl->heap, DYNAMIC_TYPE_DH);
    }

    if (ssl->buffers.weOwnCert)
        XFREE(ssl->buffers.certificate.buffer, ssl->heap, DYNAMIC_TYPE_CERT);
    if (ssl->buffers.weOwnCertChain)
        XFREE(ssl->buffers.certChain.buffer, ssl->heap, DYNAMIC_TYPE_CERT);
    if (ssl->buffers.weOwnKey)
        XFREE(ssl->buffers.key.buffer, ssl->heap, DYNAMIC_TYPE_KEY);
#endif
#ifndef NO_RSA
    if (ssl->peerRsaKey) {
        FreeRsaKey(ssl->peerRsaKey);
        XFREE(ssl->peerRsaKey, ssl->heap, DYNAMIC_TYPE_RSA);
    }
#endif
    if (ssl->buffers.inputBuffer.dynamicFlag)
        ShrinkInputBuffer(ssl, FORCED_FREE);
    if (ssl->buffers.outputBuffer.dynamicFlag)
        ShrinkOutputBuffer(ssl);
#ifdef CYASSL_DTLS
    if (ssl->dtls_pool != NULL) {
        DtlsPoolReset(ssl);
        XFREE(ssl->dtls_pool, ssl->heap, DYNAMIC_TYPE_NONE);
    }
    if (ssl->dtls_msg_list != NULL) {
        DtlsMsgListDelete(ssl->dtls_msg_list, ssl->heap);
        ssl->dtls_msg_list = NULL;
    }
    XFREE(ssl->buffers.dtlsCtx.peer.sa, ssl->heap, DYNAMIC_TYPE_SOCKADDR);
    ssl->buffers.dtlsCtx.peer.sa = NULL;
#endif
#if defined(KEEP_PEER_CERT) || defined(GOAHEAD_WS)
    FreeX509(&ssl->peerCert);
#endif
#if defined(OPENSSL_EXTRA) || defined(GOAHEAD_WS)
    CyaSSL_BIO_free(ssl->biord);
    if (ssl->biord != ssl->biowr)        /* in case same as write */
        CyaSSL_BIO_free(ssl->biowr);
#endif
#ifdef HAVE_LIBZ
    FreeStreams(ssl);
#endif
#ifdef HAVE_ECC
    if (ssl->peerEccKey) {
        if (ssl->peerEccKeyPresent)
            ecc_free(ssl->peerEccKey);
        XFREE(ssl->peerEccKey, ssl->heap, DYNAMIC_TYPE_ECC);
    }
    if (ssl->peerEccDsaKey) {
        if (ssl->peerEccDsaKeyPresent)
            ecc_free(ssl->peerEccDsaKey);
        XFREE(ssl->peerEccDsaKey, ssl->heap, DYNAMIC_TYPE_ECC);
    }
    if (ssl->eccTempKey) {
        if (ssl->eccTempKeyPresent)
            ecc_free(ssl->eccTempKey);
        XFREE(ssl->eccTempKey, ssl->heap, DYNAMIC_TYPE_ECC);
    }
    if (ssl->eccDsaKey) {
        if (ssl->eccDsaKeyPresent)
            ecc_free(ssl->eccDsaKey);
        XFREE(ssl->eccDsaKey, ssl->heap, DYNAMIC_TYPE_ECC);
    }
#endif
#ifdef HAVE_PK_CALLBACKS
    #ifdef HAVE_ECC
        XFREE(ssl->buffers.peerEccDsaKey.buffer, ssl->heap, DYNAMIC_TYPE_ECC);
    #endif /* HAVE_ECC */
    #ifndef NO_RSA 
        XFREE(ssl->buffers.peerRsaKey.buffer, ssl->heap, DYNAMIC_TYPE_RSA);
    #endif /* NO_RSA */
#endif /* HAVE_PK_CALLBACKS */
#ifdef HAVE_TLS_EXTENSIONS
    TLSX_FreeAll(ssl->extensions);
#endif
#ifdef HAVE_NETX
    if (ssl->nxCtx.nxPacket)
        nx_packet_release(ssl->nxCtx.nxPacket);
#endif
}


/* Free any handshake resources no longer needed */
void FreeHandshakeResources(CYASSL* ssl)
{
    /* input buffer */
    if (ssl->buffers.inputBuffer.dynamicFlag)
        ShrinkInputBuffer(ssl, NO_FORCED_FREE);

    /* suites */
    XFREE(ssl->suites, ssl->heap, DYNAMIC_TYPE_SUITES);
    ssl->suites = NULL;

    /* RNG */
    if (ssl->specs.cipher_type == stream || ssl->options.tls1_1 == 0) {
        XFREE(ssl->rng, ssl->heap, DYNAMIC_TYPE_RNG);
        ssl->rng = NULL;
    }

#ifdef CYASSL_DTLS
    /* DTLS_POOL */
    if (ssl->options.dtls && ssl->dtls_pool != NULL) {
        DtlsPoolReset(ssl);
        XFREE(ssl->dtls_pool, ssl->heap, DYNAMIC_TYPE_DTLS_POOL);
        ssl->dtls_pool = NULL;
    }
#endif

    /* arrays */
    if (ssl->options.saveArrays)
        FreeArrays(ssl, 1);

#ifndef NO_RSA
    /* peerRsaKey */
    if (ssl->peerRsaKey) {
        FreeRsaKey(ssl->peerRsaKey);
        XFREE(ssl->peerRsaKey, ssl->heap, DYNAMIC_TYPE_RSA);
        ssl->peerRsaKey = NULL;
    }
#endif

#ifdef HAVE_ECC
    if (ssl->peerEccKey)
    {
        if (ssl->peerEccKeyPresent) {
            ecc_free(ssl->peerEccKey);
            ssl->peerEccKeyPresent = 0;
        }
        XFREE(ssl->peerEccKey, ssl->heap, DYNAMIC_TYPE_ECC);
        ssl->peerEccKey = NULL;
    }
    if (ssl->peerEccDsaKey)
    {
        if (ssl->peerEccDsaKeyPresent) {
            ecc_free(ssl->peerEccDsaKey);
            ssl->peerEccDsaKeyPresent = 0;
        }
        XFREE(ssl->peerEccDsaKey, ssl->heap, DYNAMIC_TYPE_ECC);
        ssl->peerEccDsaKey = NULL;
    }
    if (ssl->eccTempKey)
    {
        if (ssl->eccTempKeyPresent) {
            ecc_free(ssl->eccTempKey);
            ssl->eccTempKeyPresent = 0;
        }
        XFREE(ssl->eccTempKey, ssl->heap, DYNAMIC_TYPE_ECC);
        ssl->eccTempKey = NULL;
    }
    if (ssl->eccDsaKey)
    {
        if (ssl->eccDsaKeyPresent) {
            ecc_free(ssl->eccDsaKey);
            ssl->eccDsaKeyPresent = 0;
        }
        XFREE(ssl->eccDsaKey, ssl->heap, DYNAMIC_TYPE_ECC);
        ssl->eccDsaKey = NULL;
    }
#endif
#ifdef HAVE_PK_CALLBACKS
    #ifdef HAVE_ECC
        XFREE(ssl->buffers.peerEccDsaKey.buffer, ssl->heap, DYNAMIC_TYPE_ECC);
        ssl->buffers.peerEccDsaKey.buffer = NULL;
    #endif /* HAVE_ECC */
    #ifndef NO_RSA 
        XFREE(ssl->buffers.peerRsaKey.buffer, ssl->heap, DYNAMIC_TYPE_RSA);
        ssl->buffers.peerRsaKey.buffer = NULL;
    #endif /* NO_RSA */
#endif /* HAVE_PK_CALLBACKS */
}


void FreeSSL(CYASSL* ssl)
{
    FreeSSL_Ctx(ssl->ctx);  /* will decrement and free underyling CTX if 0 */
    SSL_ResourceFree(ssl);
    XFREE(ssl, ssl->heap, DYNAMIC_TYPE_SSL);
}


#ifdef CYASSL_DTLS

int DtlsPoolInit(CYASSL* ssl)
{
    if (ssl->dtls_pool == NULL) {
        DtlsPool *pool = (DtlsPool*)XMALLOC(sizeof(DtlsPool),
                                             ssl->heap, DYNAMIC_TYPE_DTLS_POOL);
        if (pool == NULL) {
            CYASSL_MSG("DTLS Buffer Pool Memory error");
            return MEMORY_E;
        }
        else {
            int i;
            
            for (i = 0; i < DTLS_POOL_SZ; i++) {
                pool->buf[i].length = 0;
                pool->buf[i].buffer = NULL;
            }
            pool->used = 0;
            ssl->dtls_pool = pool;
        }
    }
    return 0;
}


int DtlsPoolSave(CYASSL* ssl, const byte *src, int sz)
{
    DtlsPool *pool = ssl->dtls_pool;
    if (pool != NULL && pool->used < DTLS_POOL_SZ) {
        buffer *pBuf = &pool->buf[pool->used];
        pBuf->buffer = (byte*)XMALLOC(sz, ssl->heap, DYNAMIC_TYPE_DTLS_POOL);
        if (pBuf->buffer == NULL) {
            CYASSL_MSG("DTLS Buffer Memory error");
            return MEMORY_ERROR;
        }
        XMEMCPY(pBuf->buffer, src, sz);
        pBuf->length = (word32)sz;
        pool->used++;
    }
    return 0;
}


void DtlsPoolReset(CYASSL* ssl)
{
    DtlsPool *pool = ssl->dtls_pool;
    if (pool != NULL) {
        buffer *pBuf;
        int i, used;

        used = pool->used;
        for (i = 0, pBuf = &pool->buf[0]; i < used; i++, pBuf++) {
            XFREE(pBuf->buffer, ssl->heap, DYNAMIC_TYPE_DTLS_POOL);
            pBuf->buffer = NULL;
            pBuf->length = 0;
        }
        pool->used = 0;
    }
    ssl->dtls_timeout = ssl->dtls_timeout_init;
}


int DtlsPoolTimeout(CYASSL* ssl)
{
    int result = -1;
    if (ssl->dtls_timeout <  ssl->dtls_timeout_max) {
        ssl->dtls_timeout *= DTLS_TIMEOUT_MULTIPLIER;
        result = 0;
    }
    return result;
}


int DtlsPoolSend(CYASSL* ssl)
{
    int ret;
    DtlsPool *pool = ssl->dtls_pool;

    if (pool != NULL && pool->used > 0) {
        int i;
        for (i = 0; i < pool->used; i++) {
            int sendResult;
            buffer* buf = &pool->buf[i];

            DtlsRecordLayerHeader* dtls = (DtlsRecordLayerHeader*)buf->buffer;

            word16 message_epoch;
            ato16(dtls->epoch, &message_epoch);
            if (message_epoch == ssl->keys.dtls_epoch) {
                /* Increment record sequence number on retransmitted handshake
                 * messages */
                c32to48(ssl->keys.dtls_sequence_number, dtls->sequence_number);
                ssl->keys.dtls_sequence_number++;
            }
            else {
                /* The Finished message is sent with the next epoch, keep its
                 * sequence number */
            }

            if ((ret = CheckAvailableSize(ssl, buf->length)) != 0)
                return ret;

            XMEMCPY(ssl->buffers.outputBuffer.buffer, buf->buffer, buf->length);
            ssl->buffers.outputBuffer.idx = 0;
            ssl->buffers.outputBuffer.length = buf->length;

            sendResult = SendBuffered(ssl);
            if (sendResult < 0) {
                return sendResult;
            }
        }
    }
    return 0;
}


/* functions for managing DTLS datagram reordering */

/* Need to allocate space for the handshake message header. The hashing
 * routines assume the message pointer is still within the buffer that
 * has the headers, and will include those headers in the hash. The store
 * routines need to take that into account as well. New will allocate
 * extra space for the headers. */
DtlsMsg* DtlsMsgNew(word32 sz, void* heap)
{
    DtlsMsg* msg = NULL;
    
    msg = (DtlsMsg*)XMALLOC(sizeof(DtlsMsg), heap, DYNAMIC_TYPE_DTLS_MSG);

    if (msg != NULL) {
        msg->buf = (byte*)XMALLOC(sz + DTLS_HANDSHAKE_HEADER_SZ,
                                                     heap, DYNAMIC_TYPE_NONE);
        if (msg->buf != NULL) {
            msg->next = NULL;
            msg->seq = 0;
            msg->sz = sz;
            msg->fragSz = 0;
            msg->msg = msg->buf + DTLS_HANDSHAKE_HEADER_SZ;
        }
        else {
            XFREE(msg, heap, DYNAMIC_TYPE_DTLS_MSG);
            msg = NULL;
        }
    }

    return msg;
}

void DtlsMsgDelete(DtlsMsg* item, void* heap)
{
    (void)heap;

    if (item != NULL) {
        if (item->buf != NULL)
            XFREE(item->buf, heap, DYNAMIC_TYPE_NONE);
        XFREE(item, heap, DYNAMIC_TYPE_DTLS_MSG);
    }
}


void DtlsMsgListDelete(DtlsMsg* head, void* heap)
{
    DtlsMsg* next;
    while (head) {
        next = head->next;
        DtlsMsgDelete(head, heap);
        head = next;
    }
}


void DtlsMsgSet(DtlsMsg* msg, word32 seq, const byte* data, byte type,
                                              word32 fragOffset, word32 fragSz)
{
    if (msg != NULL && data != NULL && msg->fragSz <= msg->sz) {
        msg->seq = seq;
        msg->type = type;
        msg->fragSz += fragSz;
        /* If fragOffset is zero, this is either a full message that is out
         * of order, or the first fragment of a fragmented message. Copy the
         * handshake message header as well as the message data. */
        if (fragOffset == 0)
            XMEMCPY(msg->buf, data - DTLS_HANDSHAKE_HEADER_SZ,
                                            fragSz + DTLS_HANDSHAKE_HEADER_SZ);
        else {
            /* If fragOffet is non-zero, this is an additional fragment that
             * needs to be copied to its location in the message buffer. Also
             * copy the total size of the message over the fragment size. The
             * hash routines look at a defragmented message if it had actually
             * come across as a single handshake message. */
            XMEMCPY(msg->msg + fragOffset, data, fragSz);
            c32to24(msg->sz, msg->msg - DTLS_HANDSHAKE_FRAG_SZ);
        }
    }
}


DtlsMsg* DtlsMsgFind(DtlsMsg* head, word32 seq)
{
    while (head != NULL && head->seq != seq) {
        head = head->next;
    }
    return head;
}


DtlsMsg* DtlsMsgStore(DtlsMsg* head, word32 seq, const byte* data, 
        word32 dataSz, byte type, word32 fragOffset, word32 fragSz, void* heap)
{

    /* See if seq exists in the list. If it isn't in the list, make
     * a new item of size dataSz, copy fragSz bytes from data to msg->msg
     * starting at offset fragOffset, and add fragSz to msg->fragSz. If
     * the seq is in the list and it isn't full, copy fragSz bytes from
     * data to msg->msg starting at offset fragOffset, and add fragSz to
     * msg->fragSz. The new item should be inserted into the list in its
     * proper position.
     *
     * 1. Find seq in list, or where seq should go in list. If seq not in
     *    list, create new item and insert into list. Either case, keep
     *    pointer to item.
     * 2. If msg->fragSz + fragSz < sz, copy data to msg->msg at offset
     *    fragOffset. Add fragSz to msg->fragSz.
     */

    if (head != NULL) {
        DtlsMsg* cur = DtlsMsgFind(head, seq);
        if (cur == NULL) {
            cur = DtlsMsgNew(dataSz, heap);
            if (cur != NULL) {
                DtlsMsgSet(cur, seq, data, type, fragOffset, fragSz);
                head = DtlsMsgInsert(head, cur);
            }
        }
        else {
            DtlsMsgSet(cur, seq, data, type, fragOffset, fragSz);
        }
    }
    else {
        head = DtlsMsgNew(dataSz, heap);
        DtlsMsgSet(head, seq, data, type, fragOffset, fragSz);
    }

    return head;
}


/* DtlsMsgInsert() is an in-order insert. */
DtlsMsg* DtlsMsgInsert(DtlsMsg* head, DtlsMsg* item)
{
    if (head == NULL || item->seq < head->seq) {
        item->next = head;
        head = item;
    }
    else if (head->next == NULL) {
        head->next = item;
    }
    else {
        DtlsMsg* cur = head->next;
        DtlsMsg* prev = head;
        while (cur) {
            if (item->seq < cur->seq) {
                item->next = cur;
                prev->next = item;
                break;
            }
            prev = cur;
            cur = cur->next;
        }
        if (cur == NULL) {
            prev->next = item;
        }
    }

    return head;
}

#endif /* CYASSL_DTLS */

#ifndef NO_OLD_TLS

ProtocolVersion MakeSSLv3(void)
{
    ProtocolVersion pv;
    pv.major = SSLv3_MAJOR;
    pv.minor = SSLv3_MINOR;

    return pv;
}

#endif /* NO_OLD_TLS */


#ifdef CYASSL_DTLS

ProtocolVersion MakeDTLSv1(void)
{
    ProtocolVersion pv;
    pv.major = DTLS_MAJOR;
    pv.minor = DTLS_MINOR;

    return pv;
}

ProtocolVersion MakeDTLSv1_2(void)
{
    ProtocolVersion pv;
    pv.major = DTLS_MAJOR;
    pv.minor = DTLSv1_2_MINOR;

    return pv;
}

#endif /* CYASSL_DTLS */




#ifdef USE_WINDOWS_API 

    word32 LowResTimer(void)
    {
        static int           init = 0;
        static LARGE_INTEGER freq;
        LARGE_INTEGER        count;
    
        if (!init) {
            QueryPerformanceFrequency(&freq);
            init = 1;
        }

        QueryPerformanceCounter(&count);

        return (word32)(count.QuadPart / freq.QuadPart);
    }

#elif defined(HAVE_RTP_SYS)

    #include "rtptime.h"

    word32 LowResTimer(void)
    {
        return (word32)rtp_get_system_sec();
    }


#elif defined(MICRIUM)

    word32 LowResTimer(void)
    {
        NET_SECURE_OS_TICK  clk;

        #if (NET_SECURE_MGR_CFG_EN == DEF_ENABLED)
            clk = NetSecure_OS_TimeGet();
        #endif
        return (word32)clk;
    }


#elif defined(MICROCHIP_TCPIP_V5)

    word32 LowResTimer(void)
    {
        return (word32) TickGet();
    }


#elif defined(MICROCHIP_TCPIP)

    #if defined(MICROCHIP_MPLAB_HARMONY)

        #include <system/tmr/sys_tmr.h>

        word32 LowResTimer(void)
        {
            return (word32) SYS_TMR_TickCountGet();
        }

    #else

        word32 LowResTimer(void)
        {
            return (word32) SYS_TICK_Get();
        }

    #endif

#elif defined(FREESCALE_MQX)

    word32 LowResTimer(void)
    {
        TIME_STRUCT mqxTime;

        _time_get_elapsed(&mqxTime);

        return (word32) mqxTime.SECONDS;
    }


#elif defined(USER_TICKS)
#if 0
    word32 LowResTimer(void)
    {
        /*
        write your own clock tick function if don't want time(0)
        needs second accuracy but doesn't have to correlated to EPOCH
        */
    }
#endif
#else /* !USE_WINDOWS_API && !HAVE_RTP_SYS && !MICRIUM && !USER_TICKS */

    #include <time.h>

    word32 LowResTimer(void)
    {
        return (word32)time(0); 
    }


#endif /* USE_WINDOWS_API */


/* add output to md5 and sha handshake hashes, exclude record header */
static int HashOutput(CYASSL* ssl, const byte* output, int sz, int ivSz)
{
    const byte* adj = output + RECORD_HEADER_SZ + ivSz;
    sz -= RECORD_HEADER_SZ;
    
#ifdef CYASSL_DTLS
    if (ssl->options.dtls) {
        adj += DTLS_RECORD_EXTRA;
        sz  -= DTLS_RECORD_EXTRA;
    }
#endif
#ifndef NO_OLD_TLS
#ifndef NO_SHA
    ShaUpdate(&ssl->hashSha, adj, sz);
#endif
#ifndef NO_MD5
    Md5Update(&ssl->hashMd5, adj, sz);
#endif
#endif

    if (IsAtLeastTLSv1_2(ssl)) {
        int ret;

#ifndef NO_SHA256
        ret = Sha256Update(&ssl->hashSha256, adj, sz);
        if (ret != 0)
            return ret;
#endif
#ifdef CYASSL_SHA384
        ret = Sha384Update(&ssl->hashSha384, adj, sz);
        if (ret != 0)
            return ret;
#endif
    }

    return 0;
}


/* add input to md5 and sha handshake hashes, include handshake header */
static int HashInput(CYASSL* ssl, const byte* input, int sz)
{
    const byte* adj = input - HANDSHAKE_HEADER_SZ;
    sz += HANDSHAKE_HEADER_SZ;
    
#ifdef CYASSL_DTLS
    if (ssl->options.dtls) {
        adj -= DTLS_HANDSHAKE_EXTRA;
        sz  += DTLS_HANDSHAKE_EXTRA;
    }
#endif

#ifndef NO_OLD_TLS
#ifndef NO_SHA
    ShaUpdate(&ssl->hashSha, adj, sz);
#endif
#ifndef NO_MD5
    Md5Update(&ssl->hashMd5, adj, sz);
#endif
#endif

    if (IsAtLeastTLSv1_2(ssl)) {
        int ret;

#ifndef NO_SHA256
        ret = Sha256Update(&ssl->hashSha256, adj, sz);
        if (ret != 0)
            return ret;
#endif
#ifdef CYASSL_SHA384
        ret = Sha384Update(&ssl->hashSha384, adj, sz);
        if (ret != 0)
            return ret;
#endif
    }

    return 0;
}


/* add record layer header for message */
static void AddRecordHeader(byte* output, word32 length, byte type, CYASSL* ssl)
{
    RecordLayerHeader* rl;
  
    /* record layer header */
    rl = (RecordLayerHeader*)output;
    rl->type    = type;
    rl->pvMajor = ssl->version.major;       /* type and version same in each */
    rl->pvMinor = ssl->version.minor;

    if (!ssl->options.dtls)
        c16toa((word16)length, rl->length);
    else {
#ifdef CYASSL_DTLS
        DtlsRecordLayerHeader* dtls;
    
        /* dtls record layer header extensions */
        dtls = (DtlsRecordLayerHeader*)output;
        c16toa(ssl->keys.dtls_epoch, dtls->epoch);
        c32to48(ssl->keys.dtls_sequence_number++, dtls->sequence_number);
        c16toa((word16)length, dtls->length);
#endif
    }
}


/* add handshake header for message */
static void AddHandShakeHeader(byte* output, word32 length, byte type,
                               CYASSL* ssl)
{
    HandShakeHeader* hs;
    (void)ssl;
 
    /* handshake header */
    hs = (HandShakeHeader*)output;
    hs->type = type;
    c32to24(length, hs->length);         /* type and length same for each */
#ifdef CYASSL_DTLS
    if (ssl->options.dtls) {
        DtlsHandShakeHeader* dtls;
    
        /* dtls handshake header extensions */
        dtls = (DtlsHandShakeHeader*)output;
        c16toa(ssl->keys.dtls_handshake_number++, dtls->message_seq);
        c32to24(0, dtls->fragment_offset);
        c32to24(length, dtls->fragment_length);
    }
#endif
}


/* add both headers for handshake message */
static void AddHeaders(byte* output, word32 length, byte type, CYASSL* ssl)
{
    if (!ssl->options.dtls) {
        AddRecordHeader(output, length + HANDSHAKE_HEADER_SZ, handshake, ssl);
        AddHandShakeHeader(output + RECORD_HEADER_SZ, length, type, ssl);
    }
#ifdef CYASSL_DTLS
    else  {
        AddRecordHeader(output, length+DTLS_HANDSHAKE_HEADER_SZ, handshake,ssl);
        AddHandShakeHeader(output + DTLS_RECORD_HEADER_SZ, length, type, ssl);
    }
#endif
}


/* return bytes received, -1 on error */
static int Receive(CYASSL* ssl, byte* buf, word32 sz)
{
    int recvd;

    if (ssl->ctx->CBIORecv == NULL) {
        CYASSL_MSG("Your IO Recv callback is null, please set");
        return -1;
    }

retry:
    recvd = ssl->ctx->CBIORecv(ssl, (char *)buf, (int)sz, ssl->IOCB_ReadCtx);
    if (recvd < 0)
        switch (recvd) {
            case CYASSL_CBIO_ERR_GENERAL:        /* general/unknown error */
                return -1;

            case CYASSL_CBIO_ERR_WANT_READ:      /* want read, would block */
                return WANT_READ;

            case CYASSL_CBIO_ERR_CONN_RST:       /* connection reset */
                #ifdef USE_WINDOWS_API
                if (ssl->options.dtls) {
                    goto retry;
                }
                #endif
                ssl->options.connReset = 1;
                return -1;

            case CYASSL_CBIO_ERR_ISR:            /* interrupt */
                /* see if we got our timeout */
                #ifdef CYASSL_CALLBACKS
                    if (ssl->toInfoOn) {
                        struct itimerval timeout;
                        getitimer(ITIMER_REAL, &timeout);
                        if (timeout.it_value.tv_sec == 0 && 
                                                timeout.it_value.tv_usec == 0) {
                            XSTRNCPY(ssl->timeoutInfo.timeoutName,
                                    "recv() timeout", MAX_TIMEOUT_NAME_SZ);
                            CYASSL_MSG("Got our timeout"); 
                            return WANT_READ;
                        }
                    }
                #endif
                goto retry;

            case CYASSL_CBIO_ERR_CONN_CLOSE:     /* peer closed connection */
                ssl->options.isClosed = 1;
                return -1;

            case CYASSL_CBIO_ERR_TIMEOUT:
#ifdef CYASSL_DTLS
                if (DtlsPoolTimeout(ssl) == 0 && DtlsPoolSend(ssl) == 0)
                    goto retry;
                else
#endif
                    return -1;

            default:
                return recvd;
        }

    return recvd;
}


/* Switch dynamic output buffer back to static, buffer is assumed clear */
void ShrinkOutputBuffer(CYASSL* ssl)
{
    CYASSL_MSG("Shrinking output buffer\n");
    XFREE(ssl->buffers.outputBuffer.buffer - ssl->buffers.outputBuffer.offset,
          ssl->heap, DYNAMIC_TYPE_OUT_BUFFER);
    ssl->buffers.outputBuffer.buffer = ssl->buffers.outputBuffer.staticBuffer;
    ssl->buffers.outputBuffer.bufferSize  = STATIC_BUFFER_LEN;
    ssl->buffers.outputBuffer.dynamicFlag = 0;
    ssl->buffers.outputBuffer.offset      = 0;
}


/* Switch dynamic input buffer back to static, keep any remaining input */
/* forced free means cleaning up */
void ShrinkInputBuffer(CYASSL* ssl, int forcedFree)
{
    int usedLength = ssl->buffers.inputBuffer.length -
                     ssl->buffers.inputBuffer.idx;
    if (!forcedFree && usedLength > STATIC_BUFFER_LEN)
        return;

    CYASSL_MSG("Shrinking input buffer\n");

    if (!forcedFree && usedLength)
        XMEMCPY(ssl->buffers.inputBuffer.staticBuffer,
               ssl->buffers.inputBuffer.buffer + ssl->buffers.inputBuffer.idx,
               usedLength);

    XFREE(ssl->buffers.inputBuffer.buffer - ssl->buffers.inputBuffer.offset,
          ssl->heap, DYNAMIC_TYPE_IN_BUFFER);
    ssl->buffers.inputBuffer.buffer = ssl->buffers.inputBuffer.staticBuffer;
    ssl->buffers.inputBuffer.bufferSize  = STATIC_BUFFER_LEN;
    ssl->buffers.inputBuffer.dynamicFlag = 0;
    ssl->buffers.inputBuffer.offset      = 0;
    ssl->buffers.inputBuffer.idx = 0;
    ssl->buffers.inputBuffer.length = usedLength;
}


int SendBuffered(CYASSL* ssl)
{
    if (ssl->ctx->CBIOSend == NULL) {
        CYASSL_MSG("Your IO Send callback is null, please set");
        return SOCKET_ERROR_E;
    }

    while (ssl->buffers.outputBuffer.length > 0) {
        int sent = ssl->ctx->CBIOSend(ssl,
                                      (char*)ssl->buffers.outputBuffer.buffer +
                                      ssl->buffers.outputBuffer.idx,
                                      (int)ssl->buffers.outputBuffer.length,
                                      ssl->IOCB_WriteCtx);
        if (sent < 0) {
            switch (sent) {

                case CYASSL_CBIO_ERR_WANT_WRITE:        /* would block */
                    return WANT_WRITE;

                case CYASSL_CBIO_ERR_CONN_RST:          /* connection reset */
                    ssl->options.connReset = 1;
                    break;

                case CYASSL_CBIO_ERR_ISR:               /* interrupt */
                    /* see if we got our timeout */
                    #ifdef CYASSL_CALLBACKS
                        if (ssl->toInfoOn) {
                            struct itimerval timeout;
                            getitimer(ITIMER_REAL, &timeout);
                            if (timeout.it_value.tv_sec == 0 && 
                                                timeout.it_value.tv_usec == 0) {
                                XSTRNCPY(ssl->timeoutInfo.timeoutName,
                                        "send() timeout", MAX_TIMEOUT_NAME_SZ);
                                CYASSL_MSG("Got our timeout"); 
                                return WANT_WRITE;
                            }
                        }
                    #endif
                    continue;

                case CYASSL_CBIO_ERR_CONN_CLOSE: /* epipe / conn closed */
                    ssl->options.connReset = 1;  /* treat same as reset */
                    break;

                default:
                    return SOCKET_ERROR_E;
            }

            return SOCKET_ERROR_E;
        }

        if (sent > (int)ssl->buffers.outputBuffer.length) {
            CYASSL_MSG("SendBuffered() out of bounds read");
            return SEND_OOB_READ_E;
        }

        ssl->buffers.outputBuffer.idx += sent;
        ssl->buffers.outputBuffer.length -= sent;
    }
      
    ssl->buffers.outputBuffer.idx = 0;

    if (ssl->buffers.outputBuffer.dynamicFlag)
        ShrinkOutputBuffer(ssl);

    return 0;
}


/* Grow the output buffer */
static INLINE int GrowOutputBuffer(CYASSL* ssl, int size)
{
    byte* tmp;
    byte  hdrSz = ssl->options.dtls ? DTLS_RECORD_HEADER_SZ :
                                      RECORD_HEADER_SZ; 
    byte  align = CYASSL_GENERAL_ALIGNMENT;
    /* the encrypted data will be offset from the front of the buffer by
       the header, if the user wants encrypted alignment they need
       to define their alignment requirement */

    if (align) {
       while (align < hdrSz)
           align *= 2;
    }

    tmp = (byte*) XMALLOC(size + ssl->buffers.outputBuffer.length + align,
                          ssl->heap, DYNAMIC_TYPE_OUT_BUFFER);
    CYASSL_MSG("growing output buffer\n");
   
    if (!tmp) return MEMORY_E;
    if (align)
        tmp += align - hdrSz;

    if (ssl->buffers.outputBuffer.length)
        XMEMCPY(tmp, ssl->buffers.outputBuffer.buffer,
               ssl->buffers.outputBuffer.length);

    if (ssl->buffers.outputBuffer.dynamicFlag)
        XFREE(ssl->buffers.outputBuffer.buffer -
              ssl->buffers.outputBuffer.offset, ssl->heap,
              DYNAMIC_TYPE_OUT_BUFFER);
    ssl->buffers.outputBuffer.dynamicFlag = 1;
    if (align)
        ssl->buffers.outputBuffer.offset = align - hdrSz;
    else
        ssl->buffers.outputBuffer.offset = 0;
    ssl->buffers.outputBuffer.buffer = tmp;
    ssl->buffers.outputBuffer.bufferSize = size +
                                           ssl->buffers.outputBuffer.length; 
    return 0;
}


/* Grow the input buffer, should only be to read cert or big app data */
int GrowInputBuffer(CYASSL* ssl, int size, int usedLength)
{
    byte* tmp;
    byte  hdrSz = DTLS_RECORD_HEADER_SZ;
    byte  align = ssl->options.dtls ? CYASSL_GENERAL_ALIGNMENT : 0;
    /* the encrypted data will be offset from the front of the buffer by
       the dtls record header, if the user wants encrypted alignment they need
       to define their alignment requirement. in tls we read record header
       to get size of record and put actual data back at front, so don't need */

    if (align) {
       while (align < hdrSz)
           align *= 2;
    }
    tmp = (byte*) XMALLOC(size + usedLength + align, ssl->heap,
                          DYNAMIC_TYPE_IN_BUFFER);
    CYASSL_MSG("growing input buffer\n");
   
    if (!tmp) return MEMORY_E;
    if (align)
        tmp += align - hdrSz;

    if (usedLength)
        XMEMCPY(tmp, ssl->buffers.inputBuffer.buffer +
                    ssl->buffers.inputBuffer.idx, usedLength);

    if (ssl->buffers.inputBuffer.dynamicFlag)
        XFREE(ssl->buffers.inputBuffer.buffer - ssl->buffers.inputBuffer.offset,
              ssl->heap,DYNAMIC_TYPE_IN_BUFFER);

    ssl->buffers.inputBuffer.dynamicFlag = 1;
    if (align)
        ssl->buffers.inputBuffer.offset = align - hdrSz;
    else
        ssl->buffers.inputBuffer.offset = 0;
    ssl->buffers.inputBuffer.buffer = tmp;
    ssl->buffers.inputBuffer.bufferSize = size + usedLength;
    ssl->buffers.inputBuffer.idx    = 0;
    ssl->buffers.inputBuffer.length = usedLength;

    return 0;
}


/* check available size into output buffer, make room if needed */
int CheckAvailableSize(CYASSL *ssl, int size)
{
    if (ssl->buffers.outputBuffer.bufferSize - ssl->buffers.outputBuffer.length
                                             < (word32)size) {
        if (GrowOutputBuffer(ssl, size) < 0)
            return MEMORY_E;
    }

    return 0;
}


/* do all verify and sanity checks on record header */
static int GetRecordHeader(CYASSL* ssl, const byte* input, word32* inOutIdx,
                           RecordLayerHeader* rh, word16 *size)
{
    if (!ssl->options.dtls) {
        XMEMCPY(rh, input + *inOutIdx, RECORD_HEADER_SZ);
        *inOutIdx += RECORD_HEADER_SZ;
        ato16(rh->length, size);
    }
    else {
#ifdef CYASSL_DTLS
        /* type and version in same sport */
        XMEMCPY(rh, input + *inOutIdx, ENUM_LEN + VERSION_SZ);
        *inOutIdx += ENUM_LEN + VERSION_SZ;
        ato16(input + *inOutIdx, &ssl->keys.dtls_state.curEpoch);
        *inOutIdx += 4; /* advance past epoch, skip first 2 seq bytes for now */
        ato32(input + *inOutIdx, &ssl->keys.dtls_state.curSeq);
        *inOutIdx += 4;  /* advance past rest of seq */
        ato16(input + *inOutIdx, size);
        *inOutIdx += LENGTH_SZ;
#endif
    }

    /* catch version mismatch */
    if (rh->pvMajor != ssl->version.major || rh->pvMinor != ssl->version.minor){
        if (ssl->options.side == CYASSL_SERVER_END &&
            ssl->options.acceptState == ACCEPT_BEGIN)
            CYASSL_MSG("Client attempting to connect with different version"); 
        else if (ssl->options.side == CYASSL_CLIENT_END &&
                                 ssl->options.downgrade &&
                                 ssl->options.connectState < FIRST_REPLY_DONE)
            CYASSL_MSG("Server attempting to accept with different version"); 
        else {
            CYASSL_MSG("SSL version error"); 
            return VERSION_ERROR;              /* only use requested version */
        }
    }

#ifdef CYASSL_DTLS
    if (ssl->options.dtls) {
        if (DtlsCheckWindow(&ssl->keys.dtls_state) != 1)
            return SEQUENCE_ERROR;
    }
#endif

    /* record layer length check */
#ifdef HAVE_MAX_FRAGMENT
    if (*size > (ssl->max_fragment + MAX_COMP_EXTRA + MAX_MSG_EXTRA))
        return LENGTH_ERROR;
#else
    if (*size > (MAX_RECORD_SIZE + MAX_COMP_EXTRA + MAX_MSG_EXTRA))
        return LENGTH_ERROR;
#endif

    /* verify record type here as well */
    switch (rh->type) {
        case handshake:
        case change_cipher_spec:
        case application_data:
        case alert:
            break;
        case no_type:
        default:
            CYASSL_MSG("Unknown Record Type"); 
            return UNKNOWN_RECORD_TYPE;
    }

    /* haven't decrypted this record yet */
    ssl->keys.decryptedCur = 0;

    return 0;
}


static int GetHandShakeHeader(CYASSL* ssl, const byte* input, word32* inOutIdx,
                              byte *type, word32 *size)
{
    const byte *ptr = input + *inOutIdx;
    (void)ssl;
    *inOutIdx += HANDSHAKE_HEADER_SZ;
    
    *type = ptr[0];
    c24to32(&ptr[1], size);

    return 0;
}


#ifdef CYASSL_DTLS
static int GetDtlsHandShakeHeader(CYASSL* ssl, const byte* input,
                                    word32* inOutIdx, byte *type, word32 *size,
                                    word32 *fragOffset, word32 *fragSz)
{
    word32 idx = *inOutIdx;

    *inOutIdx += HANDSHAKE_HEADER_SZ + DTLS_HANDSHAKE_EXTRA;
    
    *type = input[idx++];
    c24to32(input + idx, size);
    idx += BYTE3_LEN;

    ato16(input + idx, &ssl->keys.dtls_peer_handshake_number);
    idx += DTLS_HANDSHAKE_SEQ_SZ;

    c24to32(input + idx, fragOffset);
    idx += DTLS_HANDSHAKE_FRAG_SZ;
    c24to32(input + idx, fragSz);

    return 0;
}
#endif


#ifndef NO_OLD_TLS
/* fill with MD5 pad size since biggest required */
static const byte PAD1[PAD_MD5] = 
                              { 0x36, 0x36, 0x36, 0x36, 0x36, 0x36, 0x36, 0x36,
                                0x36, 0x36, 0x36, 0x36, 0x36, 0x36, 0x36, 0x36,
                                0x36, 0x36, 0x36, 0x36, 0x36, 0x36, 0x36, 0x36,
                                0x36, 0x36, 0x36, 0x36, 0x36, 0x36, 0x36, 0x36,
                                0x36, 0x36, 0x36, 0x36, 0x36, 0x36, 0x36, 0x36,
                                0x36, 0x36, 0x36, 0x36, 0x36, 0x36, 0x36, 0x36
                              };
static const byte PAD2[PAD_MD5] =
                              { 0x5c, 0x5c, 0x5c, 0x5c, 0x5c, 0x5c, 0x5c, 0x5c,
                                0x5c, 0x5c, 0x5c, 0x5c, 0x5c, 0x5c, 0x5c, 0x5c,
                                0x5c, 0x5c, 0x5c, 0x5c, 0x5c, 0x5c, 0x5c, 0x5c,
                                0x5c, 0x5c, 0x5c, 0x5c, 0x5c, 0x5c, 0x5c, 0x5c,
                                0x5c, 0x5c, 0x5c, 0x5c, 0x5c, 0x5c, 0x5c, 0x5c,
                                0x5c, 0x5c, 0x5c, 0x5c, 0x5c, 0x5c, 0x5c, 0x5c
                              };

/* calculate MD5 hash for finished */
static void BuildMD5(CYASSL* ssl, Hashes* hashes, const byte* sender)
{
    byte md5_result[MD5_DIGEST_SIZE];

    /* make md5 inner */    
    Md5Update(&ssl->hashMd5, sender, SIZEOF_SENDER);
    Md5Update(&ssl->hashMd5, ssl->arrays->masterSecret, SECRET_LEN);
    Md5Update(&ssl->hashMd5, PAD1, PAD_MD5);
    Md5Final(&ssl->hashMd5, md5_result);

    /* make md5 outer */
    Md5Update(&ssl->hashMd5, ssl->arrays->masterSecret, SECRET_LEN);
    Md5Update(&ssl->hashMd5, PAD2, PAD_MD5);
    Md5Update(&ssl->hashMd5, md5_result, MD5_DIGEST_SIZE);

    Md5Final(&ssl->hashMd5, hashes->md5);
}


/* calculate SHA hash for finished */
static void BuildSHA(CYASSL* ssl, Hashes* hashes, const byte* sender)
{
    byte sha_result[SHA_DIGEST_SIZE];

    /* make sha inner */
    ShaUpdate(&ssl->hashSha, sender, SIZEOF_SENDER);
    ShaUpdate(&ssl->hashSha, ssl->arrays->masterSecret, SECRET_LEN);
    ShaUpdate(&ssl->hashSha, PAD1, PAD_SHA);
    ShaFinal(&ssl->hashSha, sha_result);

    /* make sha outer */
    ShaUpdate(&ssl->hashSha, ssl->arrays->masterSecret, SECRET_LEN);
    ShaUpdate(&ssl->hashSha, PAD2, PAD_SHA);
    ShaUpdate(&ssl->hashSha, sha_result, SHA_DIGEST_SIZE);

    ShaFinal(&ssl->hashSha, hashes->sha);
}
#endif


static int BuildFinished(CYASSL* ssl, Hashes* hashes, const byte* sender)
{
    /* store current states, building requires get_digest which resets state */
#ifndef NO_OLD_TLS
#ifndef NO_MD5
    Md5 md5 = ssl->hashMd5;
#endif
#ifndef NO_SHA
    Sha sha = ssl->hashSha;
#endif
#endif
#ifndef NO_SHA256
    Sha256 sha256 = ssl->hashSha256;
#endif
#ifdef CYASSL_SHA384
    Sha384 sha384 = ssl->hashSha384;
#endif

    int ret = 0;

#ifndef NO_TLS
    if (ssl->options.tls) {
        ret = BuildTlsFinished(ssl, hashes, sender);
    }
#endif
#ifndef NO_OLD_TLS
    if (!ssl->options.tls) {
        BuildMD5(ssl, hashes, sender);
        BuildSHA(ssl, hashes, sender);
    }
#endif
    
    /* restore */
#ifndef NO_OLD_TLS
    #ifndef NO_MD5
        ssl->hashMd5 = md5;
    #endif
    #ifndef NO_SHA
    ssl->hashSha = sha;
    #endif
#endif
    if (IsAtLeastTLSv1_2(ssl)) {
    #ifndef NO_SHA256
        ssl->hashSha256 = sha256;
    #endif
    #ifdef CYASSL_SHA384
        ssl->hashSha384 = sha384;
    #endif
    }

    return ret;
}


    /* cipher requirements */
    enum {
        REQUIRES_RSA,
        REQUIRES_DHE,
        REQUIRES_ECC_DSA,
        REQUIRES_ECC_STATIC,
        REQUIRES_PSK,
        REQUIRES_NTRU,
        REQUIRES_RSA_SIG
    };



    /* Does this cipher suite (first, second) have the requirement
       an ephemeral key exchange will still require the key for signing
       the key exchange so ECHDE_RSA requires an rsa key thus rsa_kea */
    static int CipherRequires(byte first, byte second, int requirement)
    {
        /* ECC extensions */
        if (first == ECC_BYTE) {

        switch (second) {

#ifndef NO_RSA
        case TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_ECDH_RSA_WITH_AES_128_CBC_SHA :
            if (requirement == REQUIRES_ECC_STATIC)
                return 1;
            if (requirement == REQUIRES_RSA_SIG)
                return 1;
            break;

#ifndef NO_DES3
        case TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA :
            if (requirement == REQUIRES_ECC_STATIC)
                return 1;
            if (requirement == REQUIRES_RSA_SIG)
                return 1;
            break;
#endif

#ifndef NO_RC4
        case TLS_ECDHE_RSA_WITH_RC4_128_SHA :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_ECDH_RSA_WITH_RC4_128_SHA :
            if (requirement == REQUIRES_ECC_STATIC)
                return 1;
            if (requirement == REQUIRES_RSA_SIG)
                return 1;
            break;
#endif
#endif /* NO_RSA */

#ifndef NO_DES3
        case TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA :
            if (requirement == REQUIRES_ECC_DSA)
                return 1;
            break;

        case TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA :
            if (requirement == REQUIRES_ECC_STATIC)
                return 1;
            break;
#endif
#ifndef NO_RC4
        case TLS_ECDHE_ECDSA_WITH_RC4_128_SHA :
            if (requirement == REQUIRES_ECC_DSA)
                return 1;
            break;

        case TLS_ECDH_ECDSA_WITH_RC4_128_SHA :
            if (requirement == REQUIRES_ECC_STATIC)
                return 1;
            break;
#endif
#ifndef NO_RSA
        case TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_ECDH_RSA_WITH_AES_256_CBC_SHA :
            if (requirement == REQUIRES_ECC_STATIC)
                return 1;
            if (requirement == REQUIRES_RSA_SIG)
                return 1;
            break;
#endif

        case TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA :
            if (requirement == REQUIRES_ECC_DSA)
                return 1;
            break;

        case TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA :
            if (requirement == REQUIRES_ECC_STATIC)
                return 1;
            break;

        case TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA :
            if (requirement == REQUIRES_ECC_DSA)
                return 1;
            break;

        case TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA :
            if (requirement == REQUIRES_ECC_STATIC)
                return 1;
            break;

        case TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 :
            if (requirement == REQUIRES_ECC_DSA)
                return 1;
            break;

        case TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 :
            if (requirement == REQUIRES_ECC_DSA)
                return 1;
            break;

        case TLS_ECDH_ECDSA_WITH_AES_128_GCM_SHA256 :
            if (requirement == REQUIRES_ECC_STATIC)
                return 1;
            break;

        case TLS_ECDH_ECDSA_WITH_AES_256_GCM_SHA384 :
            if (requirement == REQUIRES_ECC_STATIC)
                return 1;
            break;

#ifndef NO_RSA
        case TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_ECDH_RSA_WITH_AES_128_GCM_SHA256 :
            if (requirement == REQUIRES_ECC_STATIC)
                return 1;
            if (requirement == REQUIRES_RSA_SIG)
                return 1;
            break;

        case TLS_ECDH_RSA_WITH_AES_256_GCM_SHA384 :
            if (requirement == REQUIRES_ECC_STATIC)
                return 1;
            if (requirement == REQUIRES_RSA_SIG)
                return 1;
            break;

        case TLS_RSA_WITH_AES_128_CCM_8 :
        case TLS_RSA_WITH_AES_256_CCM_8 :
            if (requirement == REQUIRES_RSA)
                return 1;
            if (requirement == REQUIRES_RSA_SIG)
                return 1;
            break;

        case TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256 :
        case TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384 :
            if (requirement == REQUIRES_RSA)
                return 1;
            if (requirement == REQUIRES_RSA_SIG)
                return 1;
            break;

        case TLS_ECDH_RSA_WITH_AES_128_CBC_SHA256 :
        case TLS_ECDH_RSA_WITH_AES_256_CBC_SHA384 :
            if (requirement == REQUIRES_RSA_SIG)
                return 1;
            if (requirement == REQUIRES_ECC_STATIC)
                return 1;
            break;
#endif

        case TLS_ECDHE_ECDSA_WITH_AES_128_CCM_8 :
        case TLS_ECDHE_ECDSA_WITH_AES_256_CCM_8 :
            if (requirement == REQUIRES_ECC_DSA)
                return 1;
            break;

        case TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA384 :
        case TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256 :
            if (requirement == REQUIRES_ECC_DSA)
                return 1;
            break;

        case TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA256 :
        case TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA384 :
            if (requirement == REQUIRES_ECC_DSA)
                return 1;
            if (requirement == REQUIRES_ECC_STATIC)
                return 1;
            break;

        case TLS_PSK_WITH_AES_128_CCM:
        case TLS_PSK_WITH_AES_256_CCM:
        case TLS_PSK_WITH_AES_128_CCM_8:
        case TLS_PSK_WITH_AES_256_CCM_8:
            if (requirement == REQUIRES_PSK)
                return 1;
            break;

        case TLS_DHE_PSK_WITH_AES_128_CCM:
        case TLS_DHE_PSK_WITH_AES_256_CCM:
            if (requirement == REQUIRES_PSK)
                return 1;
            if (requirement == REQUIRES_DHE)
                return 1;
            break;

        default:
            CYASSL_MSG("Unsupported cipher suite, CipherRequires ECC");
            return 0;
        }   /* switch */
        }   /* if     */
        if (first != ECC_BYTE) {   /* normal suites */
        switch (second) {

#ifndef NO_RSA
        case SSL_RSA_WITH_RC4_128_SHA :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_NTRU_RSA_WITH_RC4_128_SHA :
            if (requirement == REQUIRES_NTRU)
                return 1;
            break;

        case SSL_RSA_WITH_RC4_128_MD5 :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case SSL_RSA_WITH_3DES_EDE_CBC_SHA :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_NTRU_RSA_WITH_3DES_EDE_CBC_SHA :
            if (requirement == REQUIRES_NTRU)
                return 1;
            break;

        case TLS_RSA_WITH_AES_128_CBC_SHA :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_RSA_WITH_AES_128_CBC_SHA256 :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_NTRU_RSA_WITH_AES_128_CBC_SHA :
            if (requirement == REQUIRES_NTRU)
                return 1;
            break;

        case TLS_RSA_WITH_AES_256_CBC_SHA :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_RSA_WITH_AES_256_CBC_SHA256 :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_RSA_WITH_NULL_SHA :
        case TLS_RSA_WITH_NULL_SHA256 :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_NTRU_RSA_WITH_AES_256_CBC_SHA :
            if (requirement == REQUIRES_NTRU)
                return 1;
            break;
#endif

        case TLS_PSK_WITH_AES_128_GCM_SHA256 :
        case TLS_PSK_WITH_AES_256_GCM_SHA384 :
        case TLS_PSK_WITH_AES_128_CBC_SHA256 :
        case TLS_PSK_WITH_AES_256_CBC_SHA384 :
        case TLS_PSK_WITH_AES_128_CBC_SHA :
        case TLS_PSK_WITH_AES_256_CBC_SHA :
        case TLS_PSK_WITH_NULL_SHA384 :
        case TLS_PSK_WITH_NULL_SHA256 :
        case TLS_PSK_WITH_NULL_SHA :
            if (requirement == REQUIRES_PSK)
                return 1;
            break;

        case TLS_DHE_PSK_WITH_AES_128_GCM_SHA256 :
        case TLS_DHE_PSK_WITH_AES_256_GCM_SHA384 :
        case TLS_DHE_PSK_WITH_AES_128_CBC_SHA256 :
        case TLS_DHE_PSK_WITH_AES_256_CBC_SHA384 :
        case TLS_DHE_PSK_WITH_NULL_SHA384 :
        case TLS_DHE_PSK_WITH_NULL_SHA256 :
            if (requirement == REQUIRES_DHE)
                return 1;
            if (requirement == REQUIRES_PSK)
                return 1;
            break;

#ifndef NO_RSA
        case TLS_DHE_RSA_WITH_AES_128_CBC_SHA256 :
            if (requirement == REQUIRES_RSA)
                return 1;
            if (requirement == REQUIRES_DHE)
                return 1;
            break;

        case TLS_DHE_RSA_WITH_AES_256_CBC_SHA256 :
            if (requirement == REQUIRES_RSA)
                return 1;
            if (requirement == REQUIRES_DHE)
                return 1;
            break;

        case TLS_DHE_RSA_WITH_AES_128_CBC_SHA :
            if (requirement == REQUIRES_RSA)
                return 1;
            if (requirement == REQUIRES_DHE)
                return 1;
            break;

        case TLS_DHE_RSA_WITH_AES_256_CBC_SHA :
            if (requirement == REQUIRES_RSA)
                return 1;
            if (requirement == REQUIRES_DHE)
                return 1;
            break;

        case TLS_RSA_WITH_HC_128_MD5 :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_RSA_WITH_HC_128_SHA :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_RSA_WITH_HC_128_B2B256:
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_RSA_WITH_AES_128_CBC_B2B256:
        case TLS_RSA_WITH_AES_256_CBC_B2B256:
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_RSA_WITH_RABBIT_SHA :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_RSA_WITH_AES_128_GCM_SHA256 :
        case TLS_RSA_WITH_AES_256_GCM_SHA384 :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_DHE_RSA_WITH_AES_128_GCM_SHA256 :
        case TLS_DHE_RSA_WITH_AES_256_GCM_SHA384 :
            if (requirement == REQUIRES_RSA)
                return 1;
            if (requirement == REQUIRES_DHE)
                return 1;
            break;

        case TLS_RSA_WITH_CAMELLIA_128_CBC_SHA :
        case TLS_RSA_WITH_CAMELLIA_256_CBC_SHA :
        case TLS_RSA_WITH_CAMELLIA_128_CBC_SHA256 :
        case TLS_RSA_WITH_CAMELLIA_256_CBC_SHA256 :
            if (requirement == REQUIRES_RSA)
                return 1;
            break;

        case TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA :
        case TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA :
        case TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA256 :
        case TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA256 :
            if (requirement == REQUIRES_RSA)
                return 1;
            if (requirement == REQUIRES_RSA_SIG)
                return 1;
            if (requirement == REQUIRES_DHE)
                return 1;
            break;
#endif

        default:
            CYASSL_MSG("Unsupported cipher suite, CipherRequires");
            return 0;
        }  /* switch */
        }  /* if ECC / Normal suites else */

        return 0;
    }


#ifndef NO_CERTS


/* Match names with wildcards, each wildcard can represent a single name
   component or fragment but not mulitple names, i.e.,
   *.z.com matches y.z.com but not x.y.z.com

   return 1 on success */
static int MatchDomainName(const char* pattern, int len, const char* str)
{
    char p, s;

    if (pattern == NULL || str == NULL || len <= 0)
        return 0;

    while (len > 0) {

        p = (char)XTOLOWER(*pattern++);
        if (p == 0)
            break;

        if (p == '*') {
            while (--len > 0 && (p = (char)XTOLOWER(*pattern++)) == '*')
                ;

            if (len == 0)
                p = '\0';

            while ( (s = (char)XTOLOWER(*str)) != '\0') {
                if (s == p)
                    break;
                if (s == '.')
                    return 0;
                str++;
            }
        }
        else {
            if (p != (char)XTOLOWER(*str))
                return 0;
        }

        if (*str != '\0')
            str++;

        if (len > 0)
            len--;
    }

    return *str == '\0';
}


/* try to find an altName match to domain, return 1 on success */
static int CheckAltNames(DecodedCert* dCert, char* domain)
{
    int        match = 0;
    DNS_entry* altName = NULL;

    CYASSL_MSG("Checking AltNames");

    if (dCert)
        altName = dCert->altNames;

    while (altName) {
        CYASSL_MSG("    individual AltName check");

        if (MatchDomainName(altName->name,(int)XSTRLEN(altName->name), domain)){
            match = 1;
            break;
        }

        altName = altName->next;
    }

    return match;
}


#if defined(KEEP_PEER_CERT) || defined(SESSION_CERTS)

/* Copy parts X509 needs from Decoded cert, 0 on success */
int CopyDecodedToX509(CYASSL_X509* x509, DecodedCert* dCert)
{
    int ret = 0;

    if (x509 == NULL || dCert == NULL)
        return BAD_FUNC_ARG;

    x509->version = dCert->version + 1;

    XSTRNCPY(x509->issuer.name, dCert->issuer, ASN_NAME_MAX);
    x509->issuer.name[ASN_NAME_MAX - 1] = '\0';
    x509->issuer.sz = (int)XSTRLEN(x509->issuer.name) + 1;
#ifdef OPENSSL_EXTRA
    if (dCert->issuerName.fullName != NULL) {
        XMEMCPY(&x509->issuer.fullName,
                                       &dCert->issuerName, sizeof(DecodedName));
        x509->issuer.fullName.fullName = (char*)XMALLOC(
                        dCert->issuerName.fullNameLen, NULL, DYNAMIC_TYPE_X509);
        if (x509->issuer.fullName.fullName != NULL)
            XMEMCPY(x509->issuer.fullName.fullName,
                     dCert->issuerName.fullName, dCert->issuerName.fullNameLen);
    }
#endif /* OPENSSL_EXTRA */

    XSTRNCPY(x509->subject.name, dCert->subject, ASN_NAME_MAX);
    x509->subject.name[ASN_NAME_MAX - 1] = '\0';
    x509->subject.sz = (int)XSTRLEN(x509->subject.name) + 1;
#ifdef OPENSSL_EXTRA
    if (dCert->subjectName.fullName != NULL) {
        XMEMCPY(&x509->subject.fullName,
                                      &dCert->subjectName, sizeof(DecodedName));
        x509->subject.fullName.fullName = (char*)XMALLOC(
                       dCert->subjectName.fullNameLen, NULL, DYNAMIC_TYPE_X509);
        if (x509->subject.fullName.fullName != NULL)
            XMEMCPY(x509->subject.fullName.fullName,
                   dCert->subjectName.fullName, dCert->subjectName.fullNameLen);
    }
#endif /* OPENSSL_EXTRA */

    XMEMCPY(x509->serial, dCert->serial, EXTERNAL_SERIAL_SIZE);
    x509->serialSz = dCert->serialSz;
    if (dCert->subjectCNLen < ASN_NAME_MAX) {
        XMEMCPY(x509->subjectCN, dCert->subjectCN, dCert->subjectCNLen);
        x509->subjectCN[dCert->subjectCNLen] = '\0';
    }
    else
        x509->subjectCN[0] = '\0';

#ifdef CYASSL_SEP
    {
        int minSz = min(dCert->deviceTypeSz, EXTERNAL_SERIAL_SIZE);
        if (minSz > 0) {
            x509->deviceTypeSz = minSz;
            XMEMCPY(x509->deviceType, dCert->deviceType, minSz);
        }
        else
            x509->deviceTypeSz = 0;
        minSz = min(dCert->hwTypeSz, EXTERNAL_SERIAL_SIZE);
        if (minSz != 0) {
            x509->hwTypeSz = minSz;
            XMEMCPY(x509->hwType, dCert->hwType, minSz);
        }
        else
            x509->hwTypeSz = 0;
        minSz = min(dCert->hwSerialNumSz, EXTERNAL_SERIAL_SIZE);
        if (minSz != 0) {
            x509->hwSerialNumSz = minSz;
            XMEMCPY(x509->hwSerialNum, dCert->hwSerialNum, minSz);
        }
        else
            x509->hwSerialNumSz = 0;
    }
#endif /* CYASSL_SEP */
    {
        int minSz = min(dCert->beforeDateLen, MAX_DATE_SZ);
        if (minSz != 0) {
            x509->notBeforeSz = minSz;
            XMEMCPY(x509->notBefore, dCert->beforeDate, minSz);
        }
        else
            x509->notBeforeSz = 0;
        minSz = min(dCert->afterDateLen, MAX_DATE_SZ);
        if (minSz != 0) {
            x509->notAfterSz = minSz;
            XMEMCPY(x509->notAfter, dCert->afterDate, minSz);
        }
        else
            x509->notAfterSz = 0;
    }

    if (dCert->publicKey != NULL && dCert->pubKeySize != 0) {
        x509->pubKey.buffer = (byte*)XMALLOC(
                              dCert->pubKeySize, NULL, DYNAMIC_TYPE_PUBLIC_KEY);
        if (x509->pubKey.buffer != NULL) {
            x509->pubKeyOID = dCert->keyOID;
            x509->pubKey.length = dCert->pubKeySize;
            XMEMCPY(x509->pubKey.buffer, dCert->publicKey, dCert->pubKeySize);
        }
        else
            ret = MEMORY_E;
    }

    if (dCert->signature != NULL && dCert->sigLength != 0) {
        x509->sig.buffer = (byte*)XMALLOC(
                                dCert->sigLength, NULL, DYNAMIC_TYPE_SIGNATURE);
        if (x509->sig.buffer == NULL) {
            ret = MEMORY_E;
        }
        else {
            XMEMCPY(x509->sig.buffer, dCert->signature, dCert->sigLength);
            x509->sig.length = dCert->sigLength;
            x509->sigOID = dCert->signatureOID;
        }
    }

    /* store cert for potential retrieval */
    x509->derCert.buffer = (byte*)XMALLOC(dCert->maxIdx, NULL,
                                          DYNAMIC_TYPE_CERT);
    if (x509->derCert.buffer == NULL) {
        ret = MEMORY_E;
    }
    else {
        XMEMCPY(x509->derCert.buffer, dCert->source, dCert->maxIdx);
        x509->derCert.length = dCert->maxIdx;
    }

    x509->altNames     = dCert->altNames;
    dCert->altNames    = NULL;     /* takes ownership */
    x509->altNamesNext = x509->altNames;  /* index hint */

    x509->isCa = dCert->isCA;
#ifdef OPENSSL_EXTRA
    x509->pathLength = dCert->pathLength;
    x509->keyUsage = dCert->extKeyUsage;

    x509->basicConstSet = dCert->extBasicConstSet;
    x509->basicConstCrit = dCert->extBasicConstCrit;
    x509->basicConstPlSet = dCert->extBasicConstPlSet;
    x509->subjAltNameSet = dCert->extSubjAltNameSet;
    x509->subjAltNameCrit = dCert->extSubjAltNameCrit;
    x509->authKeyIdSet = dCert->extAuthKeyIdSet;
    x509->authKeyIdCrit = dCert->extAuthKeyIdCrit;
    if (dCert->extAuthKeyIdSrc != NULL && dCert->extAuthKeyIdSz != 0) {
        x509->authKeyId = (byte*)XMALLOC(dCert->extAuthKeyIdSz, NULL, 0);
        if (x509->authKeyId != NULL) {
            XMEMCPY(x509->authKeyId,
                                 dCert->extAuthKeyIdSrc, dCert->extAuthKeyIdSz);
            x509->authKeyIdSz = dCert->extAuthKeyIdSz;
        }
        else
            ret = MEMORY_E;
    }
    x509->subjKeyIdSet = dCert->extSubjKeyIdSet;
    x509->subjKeyIdCrit = dCert->extSubjKeyIdCrit;
    if (dCert->extSubjKeyIdSrc != NULL && dCert->extSubjKeyIdSz != 0) {
        x509->subjKeyId = (byte*)XMALLOC(dCert->extSubjKeyIdSz, NULL, 0);
        if (x509->subjKeyId != NULL) {
            XMEMCPY(x509->subjKeyId,
                                 dCert->extSubjKeyIdSrc, dCert->extSubjKeyIdSz);
            x509->subjKeyIdSz = dCert->extSubjKeyIdSz;
        }
        else
            ret = MEMORY_E;
    }
    x509->keyUsageSet = dCert->extKeyUsageSet;
    x509->keyUsageCrit = dCert->extKeyUsageCrit;
    #ifdef CYASSL_SEP
        x509->certPolicySet = dCert->extCertPolicySet;
        x509->certPolicyCrit = dCert->extCertPolicyCrit;
    #endif /* CYASSL_SEP */
#endif /* OPENSSL_EXTRA */
#ifdef HAVE_ECC
    x509->pkCurveOID = dCert->pkCurveOID;
#endif /* HAVE_ECC */

    return ret;
}

#endif /* KEEP_PEER_CERT || SESSION_CERTS */


static int DoCertificate(CYASSL* ssl, byte* input, word32* inOutIdx,
                                                                    word32 size)
{
    word32 listSz, begin = *inOutIdx;
    int    ret = 0;
    int    anyError = 0;
    int    totalCerts = 0;    /* number of certs in certs buffer */
    int    count;
    char   domain[ASN_NAME_MAX];
    buffer certs[MAX_CHAIN_DEPTH];

    #ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn) AddPacketName("Certificate", &ssl->handShakeInfo);
        if (ssl->toInfoOn) AddLateName("Certificate", &ssl->timeoutInfo);
    #endif

    if ((*inOutIdx - begin) + OPAQUE24_LEN > size)
        return BUFFER_ERROR;

    c24to32(input + *inOutIdx, &listSz);
    *inOutIdx += OPAQUE24_LEN;

#ifdef HAVE_MAX_FRAGMENT
    if (listSz > ssl->max_fragment)
        return BUFFER_E;
#else
    if (listSz > MAX_RECORD_SIZE)
        return BUFFER_E;
#endif

    if ((*inOutIdx - begin) + listSz != size)
        return BUFFER_ERROR;

    CYASSL_MSG("Loading peer's cert chain");
    /* first put cert chain into buffer so can verify top down
       we're sent bottom up */
    while (listSz) {
        word32 certSz;

        if (totalCerts >= MAX_CHAIN_DEPTH)
            return MAX_CHAIN_ERROR;

        if ((*inOutIdx - begin) + OPAQUE24_LEN > size)
            return BUFFER_ERROR;

        c24to32(input + *inOutIdx, &certSz);
        *inOutIdx += OPAQUE24_LEN;

        if ((*inOutIdx - begin) + certSz > size)
            return BUFFER_ERROR;

        certs[totalCerts].length = certSz;
        certs[totalCerts].buffer = input + *inOutIdx;

#ifdef SESSION_CERTS
        if (ssl->session.chain.count < MAX_CHAIN_DEPTH &&
                                       certSz < MAX_X509_SIZE) {
            ssl->session.chain.certs[ssl->session.chain.count].length = certSz;
            XMEMCPY(ssl->session.chain.certs[ssl->session.chain.count].buffer,
                    input + *inOutIdx, certSz);
            ssl->session.chain.count++;
        } else {
            CYASSL_MSG("Couldn't store chain cert for session");
        }
#endif

        *inOutIdx += certSz;
        listSz -= certSz + CERT_HEADER_SZ;

        totalCerts++;
        CYASSL_MSG("    Put another cert into chain");
    }

    count = totalCerts;

    /* verify up to peer's first */
    while (count > 1) {
        buffer myCert = certs[count - 1];
        DecodedCert dCert;
        byte* subjectHash;

        InitDecodedCert(&dCert, myCert.buffer, myCert.length, ssl->heap);
        ret = ParseCertRelative(&dCert, CERT_TYPE, !ssl->options.verifyNone,
                                ssl->ctx->cm);
        #ifndef NO_SKID
            subjectHash = dCert.extSubjKeyId;
        #else
            subjectHash = dCert.subjectHash;
        #endif

        if (ret == 0 && dCert.isCA == 0) {
            CYASSL_MSG("Chain cert is not a CA, not adding as one");
        }
        else if (ret == 0 && ssl->options.verifyNone) {
            CYASSL_MSG("Chain cert not verified by option, not adding as CA");
        }
        else if (ret == 0 && !AlreadySigner(ssl->ctx->cm, subjectHash)) {
            buffer add;
            add.length = myCert.length;
            add.buffer = (byte*)XMALLOC(myCert.length, ssl->heap,
                                        DYNAMIC_TYPE_CA);
            CYASSL_MSG("Adding CA from chain");

            if (add.buffer == NULL)
                return MEMORY_E;
            XMEMCPY(add.buffer, myCert.buffer, myCert.length);

            ret = AddCA(ssl->ctx->cm, add, CYASSL_CHAIN_CA,
                        ssl->ctx->verifyPeer);
            if (ret == 1) ret = 0;   /* SSL_SUCCESS for external */
        }
        else if (ret != 0) {
            CYASSL_MSG("Failed to verify CA from chain");
        }
        else {
            CYASSL_MSG("Verified CA from chain and already had it");
        }

#ifdef HAVE_CRL
        if (ret == 0 && ssl->ctx->cm->crlEnabled && ssl->ctx->cm->crlCheckAll) {
            CYASSL_MSG("Doing Non Leaf CRL check");
            ret = CheckCertCRL(ssl->ctx->cm->crl, &dCert);

            if (ret != 0) {
                CYASSL_MSG("\tCRL check not ok");
            }
        }
#endif /* HAVE_CRL */

        if (ret != 0 && anyError == 0)
            anyError = ret;   /* save error from last time */

        FreeDecodedCert(&dCert);
        count--;
    }

    /* peer's, may not have one if blank client cert sent by TLSv1.2 */
    if (count) {
        buffer myCert = certs[0];
        DecodedCert dCert;
        int         fatal = 0;

        CYASSL_MSG("Verifying Peer's cert");

        InitDecodedCert(&dCert, myCert.buffer, myCert.length, ssl->heap);
        ret = ParseCertRelative(&dCert, CERT_TYPE, !ssl->options.verifyNone,
                                ssl->ctx->cm);
        if (ret == 0) {
            CYASSL_MSG("Verified Peer's cert");
            fatal = 0;
        }
        else if (ret == ASN_PARSE_E) {
            CYASSL_MSG("Got Peer cert ASN PARSE ERROR, fatal");
            fatal = 1;
        }
        else {
            CYASSL_MSG("Failed to verify Peer's cert");
            if (ssl->verifyCallback) {
                CYASSL_MSG("\tCallback override available, will continue");
                fatal = 0;
            }
            else {
                CYASSL_MSG("\tNo callback override available, fatal");
                fatal = 1;
            }
        }

#ifdef HAVE_OCSP
        if (fatal == 0 && ssl->ctx->cm->ocspEnabled) {
            ret = CheckCertOCSP(ssl->ctx->cm->ocsp, &dCert);
            if (ret != 0) {
                CYASSL_MSG("\tOCSP Lookup not ok");
                fatal = 0;
            }
        }
#endif

#ifdef HAVE_CRL
        if (fatal == 0 && ssl->ctx->cm->crlEnabled) {
            int doCrlLookup = 1;

            #ifdef HAVE_OCSP
            if (ssl->ctx->cm->ocspEnabled) {
                doCrlLookup = (ret == OCSP_CERT_UNKNOWN);
            }
            #endif /* HAVE_OCSP */

            if (doCrlLookup) {
                CYASSL_MSG("Doing Leaf CRL check");
                ret = CheckCertCRL(ssl->ctx->cm->crl, &dCert);

                if (ret != 0) {
                    CYASSL_MSG("\tCRL check not ok");
                    fatal = 0;
                }
            }
        }

#endif /* HAVE_CRL */

#ifdef KEEP_PEER_CERT
        {
        /* set X509 format for peer cert even if fatal */
        int copyRet = CopyDecodedToX509(&ssl->peerCert, &dCert);
        if (copyRet == MEMORY_E)
            fatal = 1;
        }
#endif

#ifndef IGNORE_KEY_EXTENSIONS
        if (dCert.extKeyUsageSet) {
            if ((ssl->specs.kea == rsa_kea) &&
                (dCert.extKeyUsage & KEYUSE_KEY_ENCIPHER) == 0) {
                ret = KEYUSE_ENCIPHER_E;
            }
            if ((ssl->specs.sig_algo == rsa_sa_algo ||
                    ssl->specs.sig_algo == ecc_dsa_sa_algo) &&
                (dCert.extKeyUsage & KEYUSE_DIGITAL_SIG) == 0) {
                CYASSL_MSG("KeyUse Digital Sig not set");
                ret = KEYUSE_SIGNATURE_E;
            }
        }

        if (dCert.extExtKeyUsageSet) {
            if (ssl->options.side == CYASSL_CLIENT_END) {
                if ((dCert.extExtKeyUsage &
                        (EXTKEYUSE_ANY | EXTKEYUSE_SERVER_AUTH)) == 0) {
                    CYASSL_MSG("ExtKeyUse Server Auth not set");
                    ret = EXTKEYUSE_AUTH_E;
                }
            }
            else {
                if ((dCert.extExtKeyUsage &
                        (EXTKEYUSE_ANY | EXTKEYUSE_CLIENT_AUTH)) == 0) {
                    CYASSL_MSG("ExtKeyUse Client Auth not set");
                    ret = EXTKEYUSE_AUTH_E;
                }
            }
        }
#endif /* IGNORE_KEY_EXTENSIONS */

        if (fatal) {
            FreeDecodedCert(&dCert);
            ssl->error = ret;
            return ret;
        }
        ssl->options.havePeerCert = 1;

        /* store for callback use */
        if (dCert.subjectCNLen < ASN_NAME_MAX) {
            XMEMCPY(domain, dCert.subjectCN, dCert.subjectCNLen);
            domain[dCert.subjectCNLen] = '\0';
        }
        else
            domain[0] = '\0';

        if (!ssl->options.verifyNone && ssl->buffers.domainName.buffer) {
            if (MatchDomainName(dCert.subjectCN, dCert.subjectCNLen,
                                (char*)ssl->buffers.domainName.buffer) == 0) {
                CYASSL_MSG("DomainName match on common name failed");
                if (CheckAltNames(&dCert,
                                 (char*)ssl->buffers.domainName.buffer) == 0 ) {
                    CYASSL_MSG("DomainName match on alt names failed too");
                    ret = DOMAIN_NAME_MISMATCH; /* try to get peer key still */
                }
            }
        }

        /* decode peer key */
        switch (dCert.keyOID) {
        #ifndef NO_RSA
            case RSAk:
                {
                    word32 idx = 0;
                    if (RsaPublicKeyDecode(dCert.publicKey, &idx,
                                      ssl->peerRsaKey, dCert.pubKeySize) != 0) {
                        ret = PEER_KEY_ERROR;
                    }
                    else {
                        ssl->peerRsaKeyPresent = 1;
                        #ifdef HAVE_PK_CALLBACKS
                            #ifndef NO_RSA
                                ssl->buffers.peerRsaKey.buffer =
                                       XMALLOC(dCert.pubKeySize,
                                               ssl->heap, DYNAMIC_TYPE_RSA);
                                if (ssl->buffers.peerRsaKey.buffer == NULL)
                                    ret = MEMORY_ERROR;
                                else {
                                    XMEMCPY(ssl->buffers.peerRsaKey.buffer,
                                            dCert.publicKey, dCert.pubKeySize);
                                    ssl->buffers.peerRsaKey.length =
                                            dCert.pubKeySize;
                                }
                            #endif /* NO_RSA */
                        #endif /*HAVE_PK_CALLBACKS */
                    }
                }
                break;
        #endif /* NO_RSA */
        #ifdef HAVE_NTRU
            case NTRUk:
                {
                    if (dCert.pubKeySize > sizeof(ssl->peerNtruKey)) {
                        ret = PEER_KEY_ERROR;
                    }
                    else {
                        XMEMCPY(ssl->peerNtruKey, dCert.publicKey, dCert.pubKeySize);
                        ssl->peerNtruKeyLen = (word16)dCert.pubKeySize;
                        ssl->peerNtruKeyPresent = 1;
                    }
                }
                break;
        #endif /* HAVE_NTRU */
        #ifdef HAVE_ECC
            case ECDSAk:
                {
                    if (ecc_import_x963(dCert.publicKey, dCert.pubKeySize,
                                        ssl->peerEccDsaKey) != 0) {
                        ret = PEER_KEY_ERROR;
                    }
                    else {
                        ssl->peerEccDsaKeyPresent = 1;
                        #ifdef HAVE_PK_CALLBACKS
                            #ifdef HAVE_ECC
                                ssl->buffers.peerEccDsaKey.buffer =
                                       XMALLOC(dCert.pubKeySize,
                                               ssl->heap, DYNAMIC_TYPE_ECC);
                                if (ssl->buffers.peerEccDsaKey.buffer == NULL)
                                    ret = MEMORY_ERROR;
                                else {
                                    XMEMCPY(ssl->buffers.peerEccDsaKey.buffer,
                                            dCert.publicKey, dCert.pubKeySize);
                                    ssl->buffers.peerEccDsaKey.length =
                                            dCert.pubKeySize;
                                }
                            #endif /* HAVE_ECC */
                        #endif /*HAVE_PK_CALLBACKS */
                    }
                }
                break;
        #endif /* HAVE_ECC */
            default:
                break;
        }

        FreeDecodedCert(&dCert);
    }

    if (anyError != 0 && ret == 0)
        ret = anyError;


    if (ret != 0) {
        if (!ssl->options.verifyNone) {
            int why = bad_certificate;
            if (ret == ASN_AFTER_DATE_E || ret == ASN_BEFORE_DATE_E)
                why = certificate_expired;
            if (ssl->verifyCallback) {
                int            ok;
                CYASSL_X509_STORE_CTX store;

                store.error = ret;
                store.error_depth = totalCerts;
                store.discardSessionCerts = 0;
                store.domain = domain;
                store.userCtx = ssl->verifyCbCtx;
#ifdef KEEP_PEER_CERT
                store.current_cert = &ssl->peerCert;
#else
                store.current_cert = NULL;
#endif
#ifdef FORTRESS
                store.ex_data = ssl;
#endif
                ok = ssl->verifyCallback(0, &store);
                if (ok) {
                    CYASSL_MSG("Verify callback overriding error!");
                    ret = 0;
                }
                #ifdef SESSION_CERTS
                if (store.discardSessionCerts) {
                    CYASSL_MSG("Verify callback requested discard sess certs");
                    ssl->session.chain.count = 0;
                }
                #endif
            }
            if (ret != 0) {
                SendAlert(ssl, alert_fatal, why);   /* try to send */
                ssl->options.isClosed = 1;
            }
        }
        ssl->error = ret;
    }
#ifdef CYASSL_ALWAYS_VERIFY_CB
    else {
        if (ssl->verifyCallback) {
            int ok;
            CYASSL_X509_STORE_CTX store;

            store.error = ret;
            store.error_depth = totalCerts;
            store.discardSessionCerts = 0;
            store.domain = domain;
            store.userCtx = ssl->verifyCbCtx;
#ifdef KEEP_PEER_CERT
            store.current_cert = &ssl->peerCert;
#endif
            store.ex_data = ssl;

            ok = ssl->verifyCallback(1, &store);
            if (!ok) {
                CYASSL_MSG("Verify callback overriding valid certificate!");
                ret = -1;
                SendAlert(ssl, alert_fatal, bad_certificate);
                ssl->options.isClosed = 1;
            }
            #ifdef SESSION_CERTS
            if (store.discardSessionCerts) {
                CYASSL_MSG("Verify callback requested discard sess certs");
                ssl->session.chain.count = 0;
            }
            #endif
        }
    }
#endif

    if (ssl->options.verifyNone &&
                              (ret == CRL_MISSING || ret == CRL_CERT_REVOKED)) {
        CYASSL_MSG("Ignoring CRL problem based on verify setting");
        ret = ssl->error = 0;
    }

    if (ret == 0 && ssl->options.side == CYASSL_CLIENT_END)
        ssl->options.serverState = SERVER_CERT_COMPLETE;

    return ret;
}

#endif /* !NO_CERTS */


static int DoHelloRequest(CYASSL* ssl, const byte* input, word32* inOutIdx,
                                                    word32 size, word32 totalSz)
{
    int ret = 0;

    if (size) /* must be 0 */
        return BUFFER_ERROR;

    if (ssl->keys.encryptionOn) {
        byte verify[MAX_DIGEST_SIZE];
        int  padSz = ssl->keys.encryptSz - HANDSHAKE_HEADER_SZ -
                     ssl->specs.hash_size;

        ret = ssl->hmac(ssl, verify, input + *inOutIdx - HANDSHAKE_HEADER_SZ,
                        HANDSHAKE_HEADER_SZ, handshake, 1);
        if (ret != 0)
            return ret;

        if (ssl->options.tls1_1 && ssl->specs.cipher_type == block)
            padSz -= ssl->specs.block_size;

        /* access beyond input + size should be checked against totalSz */
        if ((word32) (*inOutIdx + ssl->specs.hash_size + padSz) > totalSz)
            return INCOMPLETE_DATA;

        /* verify */
        if (XMEMCMP(input + *inOutIdx, verify, ssl->specs.hash_size) != 0) {
            CYASSL_MSG("    hello_request verify mac error");
            return VERIFY_MAC_ERROR;
        }

        *inOutIdx += ssl->specs.hash_size + padSz;
    }

    if (ssl->options.side == CYASSL_SERVER_END) {
        SendAlert(ssl, alert_fatal, unexpected_message); /* try */
        return FATAL_ERROR;
    }
    else
        return SendAlert(ssl, alert_warning, no_renegotiation);
}


int DoFinished(CYASSL* ssl, const byte* input, word32* inOutIdx, word32 size,
                                                      word32 totalSz, int sniff)
{
    word32 finishedSz = (ssl->options.tls ? TLS_FINISHED_SZ : FINISHED_SZ);

    if (finishedSz != size)
        return BUFFER_ERROR;

    #ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn) AddPacketName("Finished", &ssl->handShakeInfo);
        if (ssl->toInfoOn) AddLateName("Finished", &ssl->timeoutInfo);
    #endif

    if (sniff == NO_SNIFF) {
        if (XMEMCMP(input + *inOutIdx, &ssl->verifyHashes, size) != 0) {
            CYASSL_MSG("Verify finished error on hashes");
            return VERIFY_FINISHED_ERROR;
        }
    }

    /* increment beyond input + size should be checked against totalSz */
    if (*inOutIdx + size + ssl->keys.padSz > totalSz)
        return INCOMPLETE_DATA;

    /* force input exhaustion at ProcessReply consuming padSz */
    *inOutIdx += size + ssl->keys.padSz;

    if (ssl->options.side == CYASSL_CLIENT_END) {
        ssl->options.serverState = SERVER_FINISHED_COMPLETE;
        if (!ssl->options.resuming) {
            ssl->options.handShakeState = HANDSHAKE_DONE;

#ifdef CYASSL_DTLS
            if (ssl->options.dtls) {
                /* Other side has received our Finished, go to next epoch */
                ssl->keys.dtls_epoch++;
                ssl->keys.dtls_sequence_number = 1;
            }
#endif
        }
    }
    else {
        ssl->options.clientState = CLIENT_FINISHED_COMPLETE;
        if (ssl->options.resuming) {
            ssl->options.handShakeState = HANDSHAKE_DONE;

#ifdef CYASSL_DTLS
            if (ssl->options.dtls) {
                /* Other side has received our Finished, go to next epoch */
                ssl->keys.dtls_epoch++;
                ssl->keys.dtls_sequence_number = 1;
            }
#endif
        }
    }

    return 0;
}


static int DoHandShakeMsgType(CYASSL* ssl, byte* input, word32* inOutIdx,
                          byte type, word32 size, word32 totalSz)
{
    int ret = 0;
    (void)totalSz;

    CYASSL_ENTER("DoHandShakeMsgType");

    /* make sure can read the message */
    if (*inOutIdx + size > totalSz)
        return INCOMPLETE_DATA;

    ret = HashInput(ssl, input + *inOutIdx, size);
    if (ret != 0)
        return ret;

#ifdef CYASSL_CALLBACKS
    /* add name later, add on record and handshake header part back on */
    if (ssl->toInfoOn) {
        int add = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
        AddPacketInfo(0, &ssl->timeoutInfo, input + *inOutIdx - add,
                      size + add, ssl->heap);
        AddLateRecordHeader(&ssl->curRL, &ssl->timeoutInfo);
    }
#endif

    if (ssl->options.handShakeState == HANDSHAKE_DONE && type != hello_request){
        CYASSL_MSG("HandShake message after handshake complete");
        SendAlert(ssl, alert_fatal, unexpected_message);
        return OUT_OF_ORDER_E;
    }

    if (ssl->options.side == CYASSL_CLIENT_END && ssl->options.dtls == 0 &&
               ssl->options.serverState == NULL_STATE && type != server_hello) {
        CYASSL_MSG("First server message not server hello");
        SendAlert(ssl, alert_fatal, unexpected_message);
        return OUT_OF_ORDER_E;
    }

    if (ssl->options.side == CYASSL_CLIENT_END && ssl->options.dtls &&
            type == server_hello_done &&
            ssl->options.serverState < SERVER_HELLO_COMPLETE) {
        CYASSL_MSG("Server hello done received before server hello in DTLS");
        SendAlert(ssl, alert_fatal, unexpected_message);
        return OUT_OF_ORDER_E;
    }

    if (ssl->options.side == CYASSL_SERVER_END &&
               ssl->options.clientState == NULL_STATE && type != client_hello) {
        CYASSL_MSG("First client message not client hello");
        SendAlert(ssl, alert_fatal, unexpected_message);
        return OUT_OF_ORDER_E;
    }


    switch (type) {

    case hello_request:
        CYASSL_MSG("processing hello request");
        ret = DoHelloRequest(ssl, input, inOutIdx, size, totalSz);
        break;

#ifndef NO_CYASSL_CLIENT
    case hello_verify_request:
        CYASSL_MSG("processing hello verify request");
        ret = DoHelloVerifyRequest(ssl, input,inOutIdx, size);
        break;

    case server_hello:
        CYASSL_MSG("processing server hello");
        ret = DoServerHello(ssl, input, inOutIdx, size);
        break;

#ifndef NO_CERTS
    case certificate_request:
        CYASSL_MSG("processing certificate request");
        ret = DoCertificateRequest(ssl, input, inOutIdx, size);
        break;
#endif

    case server_key_exchange:
        CYASSL_MSG("processing server key exchange");
        ret = DoServerKeyExchange(ssl, input, inOutIdx, size);
        break;
#endif

#ifndef NO_CERTS
    case certificate:
        CYASSL_MSG("processing certificate");
        ret =  DoCertificate(ssl, input, inOutIdx, size);
        break;
#endif

    case server_hello_done:
        CYASSL_MSG("processing server hello done");
        #ifdef CYASSL_CALLBACKS
            if (ssl->hsInfoOn)
                AddPacketName("ServerHelloDone", &ssl->handShakeInfo);
            if (ssl->toInfoOn)
                AddLateName("ServerHelloDone", &ssl->timeoutInfo);
        #endif
        ssl->options.serverState = SERVER_HELLODONE_COMPLETE;
        break;

    case finished:
        CYASSL_MSG("processing finished");
        ret = DoFinished(ssl, input, inOutIdx, size, totalSz, NO_SNIFF);
        break;

#ifndef NO_CYASSL_SERVER
    case client_hello:
        CYASSL_MSG("processing client hello");
        ret = DoClientHello(ssl, input, inOutIdx, size);
        break;

    case client_key_exchange:
        CYASSL_MSG("processing client key exchange");
        ret = DoClientKeyExchange(ssl, input, inOutIdx, size);
        break;

#if !defined(NO_RSA) || defined(HAVE_ECC)
    case certificate_verify:
        CYASSL_MSG("processing certificate verify");
        ret = DoCertificateVerify(ssl, input, inOutIdx, size);
        break;
#endif /* !NO_RSA || HAVE_ECC */

#endif /* !NO_CYASSL_SERVER */

    default:
        CYASSL_MSG("Unknown handshake message type");
        ret = UNKNOWN_HANDSHAKE_TYPE;
        break;
    }

    CYASSL_LEAVE("DoHandShakeMsgType()", ret);
    return ret;
}


static int DoHandShakeMsg(CYASSL* ssl, byte* input, word32* inOutIdx,
                          word32 totalSz)
{
    byte   type;
    word32 size;
    int    ret = 0;

    CYASSL_ENTER("DoHandShakeMsg()");

    if (GetHandShakeHeader(ssl, input, inOutIdx, &type, &size) != 0)
        return PARSE_ERROR;

    ret = DoHandShakeMsgType(ssl, input, inOutIdx, type, size, totalSz);

    CYASSL_LEAVE("DoHandShakeMsg()", ret);
    return ret;
}


#ifdef CYASSL_DTLS

static INLINE int DtlsCheckWindow(DtlsState* state)
{
    word32 cur;
    word32 next;
    DtlsSeq window;

    if (state->curEpoch == state->nextEpoch) {
        next = state->nextSeq;
        window = state->window;
    }
    else if (state->curEpoch < state->nextEpoch) {
        next = state->prevSeq;
        window = state->prevWindow;
    }
    else {
        return 0;
    }

    cur = state->curSeq;

    if ((next > DTLS_SEQ_BITS) && (cur < next - DTLS_SEQ_BITS)) {
        return 0;
    }
    else if ((cur < next) && (window & ((DtlsSeq)1 << (next - cur - 1)))) {
        return 0;
    }

    return 1;
}


static INLINE int DtlsUpdateWindow(DtlsState* state)
{
    word32 cur;
    word32* next;
    DtlsSeq* window;

    if (state->curEpoch == state->nextEpoch) {
        next = &state->nextSeq;
        window = &state->window;
    }
    else {
        next = &state->prevSeq;
        window = &state->prevWindow;
    }

    cur = state->curSeq;

    if (cur < *next) {
        *window |= ((DtlsSeq)1 << (*next - cur - 1));
    }
    else {
        *window <<= (1 + cur - *next);
        *window |= 1;
        *next = cur + 1;
    }

    return 1;
}


static int DtlsMsgDrain(CYASSL* ssl)
{
    DtlsMsg* item = ssl->dtls_msg_list;
    int ret = 0;

    /* While there is an item in the store list, and it is the expected
     * message, and it is complete, and there hasn't been an error in the
     * last messge... */
    while (item != NULL &&
            ssl->keys.dtls_expected_peer_handshake_number == item->seq &&
            item->fragSz == item->sz &&
            ret == 0) {
        word32 idx = 0;
        ssl->keys.dtls_expected_peer_handshake_number++;
        ret = DoHandShakeMsgType(ssl, item->msg,
                                 &idx, item->type, item->sz, item->sz);
        ssl->dtls_msg_list = item->next;
        DtlsMsgDelete(item, ssl->heap);
        item = ssl->dtls_msg_list;
    }

    return ret;
}


static int DoDtlsHandShakeMsg(CYASSL* ssl, byte* input, word32* inOutIdx,
                          word32 totalSz)
{
    byte type;
    word32 size;
    word32 fragOffset, fragSz;
    int ret = 0;

    CYASSL_ENTER("DoDtlsHandShakeMsg()");
    if (GetDtlsHandShakeHeader(ssl, input, inOutIdx, &type,
                                            &size, &fragOffset, &fragSz) != 0)
        return PARSE_ERROR;

    if (*inOutIdx + fragSz > totalSz)
        return INCOMPLETE_DATA;

    /* Check the handshake sequence number first. If out of order,
     * add the current message to the list. If the message is in order,
     * but it is a fragment, add the current message to the list, then
     * check the head of the list to see if it is complete, if so, pop
     * it out as the current message. If the message is complete and in
     * order, process it. Check the head of the list to see if it is in
     * order, if so, process it. (Repeat until list exhausted.) If the
     * head is out of order, return for more processing.
     */
    if (ssl->keys.dtls_peer_handshake_number >
                                ssl->keys.dtls_expected_peer_handshake_number) {
        /* Current message is out of order. It will get stored in the list.
         * Storing also takes care of defragmentation. */
        ssl->dtls_msg_list = DtlsMsgStore(ssl->dtls_msg_list,
                        ssl->keys.dtls_peer_handshake_number, input + *inOutIdx,
                        size, type, fragOffset, fragSz, ssl->heap);
        *inOutIdx += fragSz;
        ret = 0;
    }
    else if (ssl->keys.dtls_peer_handshake_number <
                                ssl->keys.dtls_expected_peer_handshake_number) {
        /* Already saw this message and processed it. It can be ignored. */
        *inOutIdx += fragSz;
        ret = 0;
    }
    else if (fragSz < size) {
        /* Since this branch is in order, but fragmented, dtls_msg_list will be
         * pointing to the message with this fragment in it. Check it to see
         * if it is completed. */
        ssl->dtls_msg_list = DtlsMsgStore(ssl->dtls_msg_list,
                        ssl->keys.dtls_peer_handshake_number, input + *inOutIdx,
                        size, type, fragOffset, fragSz, ssl->heap);
        *inOutIdx += fragSz;
        ret = 0;
        if (ssl->dtls_msg_list != NULL &&
            ssl->dtls_msg_list->fragSz >= ssl->dtls_msg_list->sz)
            ret = DtlsMsgDrain(ssl);
    }
    else {
        /* This branch is in order next, and a complete message. */
        ssl->keys.dtls_expected_peer_handshake_number++;
        ret = DoHandShakeMsgType(ssl, input, inOutIdx, type, size, totalSz);
        if (ret == 0 && ssl->dtls_msg_list != NULL)
            ret = DtlsMsgDrain(ssl);
    }

    CYASSL_LEAVE("DoDtlsHandShakeMsg()", ret);
    return ret;
}
#endif


static INLINE word32 GetSEQIncrement(CYASSL* ssl, int verify)
{
    if (verify)
        return ssl->keys.peer_sequence_number++;
    else
        return ssl->keys.sequence_number++;
}


#ifdef HAVE_AEAD
static INLINE void AeadIncrementExpIV(CYASSL* ssl)
{
    int i;
    for (i = AEAD_EXP_IV_SZ-1; i >= 0; i--) {
        if (++ssl->keys.aead_exp_IV[i]) return;
    }
}
#endif


static INLINE int Encrypt(CYASSL* ssl, byte* out, const byte* input, word16 sz)
{
    (void)out;
    (void)input;
    (void)sz;

    if (ssl->encrypt.setup == 0) {
        CYASSL_MSG("Encrypt ciphers not setup");
        return ENCRYPT_ERROR;
    }

    switch (ssl->specs.bulk_cipher_algorithm) {
        #ifdef BUILD_ARC4
            case cyassl_rc4:
                Arc4Process(ssl->encrypt.arc4, out, input, sz);
                break;
        #endif

        #ifdef BUILD_DES3
            case cyassl_triple_des:
                return Des3_CbcEncrypt(ssl->encrypt.des3, out, input, sz);
        #endif

        #ifdef BUILD_AES
            case cyassl_aes:
                return AesCbcEncrypt(ssl->encrypt.aes, out, input, sz);
        #endif

        #ifdef BUILD_AESGCM
            case cyassl_aes_gcm:
                {
                    byte additional[AEAD_AUTH_DATA_SZ];
                    byte nonce[AEAD_NONCE_SZ];
                    const byte* additionalSrc = input - 5;

                    XMEMSET(additional, 0, AEAD_AUTH_DATA_SZ);

                    /* sequence number field is 64-bits, we only use 32-bits */
                    c32toa(GetSEQIncrement(ssl, 0),
                                            additional + AEAD_SEQ_OFFSET);

                    /* Store the type, version. Unfortunately, they are in
                     * the input buffer ahead of the plaintext. */
                    #ifdef CYASSL_DTLS
                        if (ssl->options.dtls) {
                            c16toa(ssl->keys.dtls_epoch, additional);
                            additionalSrc -= DTLS_HANDSHAKE_EXTRA;
                        }
                    #endif
                    XMEMCPY(additional + AEAD_TYPE_OFFSET, additionalSrc, 3);

                    /* Store the length of the plain text minus the explicit
                     * IV length minus the authentication tag size. */
                    c16toa(sz - AEAD_EXP_IV_SZ - ssl->specs.aead_mac_size,
                                                additional + AEAD_LEN_OFFSET);
                    XMEMCPY(nonce,
                                 ssl->keys.aead_enc_imp_IV, AEAD_IMP_IV_SZ);
                    XMEMCPY(nonce + AEAD_IMP_IV_SZ,
                                     ssl->keys.aead_exp_IV, AEAD_EXP_IV_SZ);
                    AesGcmEncrypt(ssl->encrypt.aes,
                        out + AEAD_EXP_IV_SZ, input + AEAD_EXP_IV_SZ,
                            sz - AEAD_EXP_IV_SZ - ssl->specs.aead_mac_size,
                        nonce, AEAD_NONCE_SZ,
                        out + sz - ssl->specs.aead_mac_size,
                        ssl->specs.aead_mac_size,
                        additional, AEAD_AUTH_DATA_SZ);
                    AeadIncrementExpIV(ssl);
                    XMEMSET(nonce, 0, AEAD_NONCE_SZ);
                }
                break;
        #endif

        #ifdef HAVE_AESCCM
            case cyassl_aes_ccm:
                {
                    byte additional[AEAD_AUTH_DATA_SZ];
                    byte nonce[AEAD_NONCE_SZ];
                    const byte* additionalSrc = input - 5;

                    XMEMSET(additional, 0, AEAD_AUTH_DATA_SZ);

                    /* sequence number field is 64-bits, we only use 32-bits */
                    c32toa(GetSEQIncrement(ssl, 0),
                                            additional + AEAD_SEQ_OFFSET);

                    /* Store the type, version. Unfortunately, they are in
                     * the input buffer ahead of the plaintext. */
                    #ifdef CYASSL_DTLS
                        if (ssl->options.dtls) {
                            c16toa(ssl->keys.dtls_epoch, additional);
                            additionalSrc -= DTLS_HANDSHAKE_EXTRA;
                        }
                    #endif
                    XMEMCPY(additional + AEAD_TYPE_OFFSET, additionalSrc, 3);

                    /* Store the length of the plain text minus the explicit
                     * IV length minus the authentication tag size. */
                    c16toa(sz - AEAD_EXP_IV_SZ - ssl->specs.aead_mac_size,
                                                additional + AEAD_LEN_OFFSET);
                    XMEMCPY(nonce,
                                 ssl->keys.aead_enc_imp_IV, AEAD_IMP_IV_SZ);
                    XMEMCPY(nonce + AEAD_IMP_IV_SZ,
                                     ssl->keys.aead_exp_IV, AEAD_EXP_IV_SZ);
                    AesCcmEncrypt(ssl->encrypt.aes,
                        out + AEAD_EXP_IV_SZ, input + AEAD_EXP_IV_SZ,
                            sz - AEAD_EXP_IV_SZ - ssl->specs.aead_mac_size,
                        nonce, AEAD_NONCE_SZ,
                        out + sz - ssl->specs.aead_mac_size,
                        ssl->specs.aead_mac_size,
                        additional, AEAD_AUTH_DATA_SZ);
                    AeadIncrementExpIV(ssl);
                    XMEMSET(nonce, 0, AEAD_NONCE_SZ);
                }
                break;
        #endif

        #ifdef HAVE_CAMELLIA
            case cyassl_camellia:
                CamelliaCbcEncrypt(ssl->encrypt.cam, out, input, sz);
                break;
        #endif

        #ifdef HAVE_HC128
            case cyassl_hc128:
                return Hc128_Process(ssl->encrypt.hc128, out, input, sz);
        #endif

        #ifdef BUILD_RABBIT
            case cyassl_rabbit:
                return RabbitProcess(ssl->encrypt.rabbit, out, input, sz);
        #endif

        #ifdef HAVE_NULL_CIPHER
            case cyassl_cipher_null:
                if (input != out) {
                    XMEMMOVE(out, input, sz);
                }
                break;
        #endif

            default:
                CYASSL_MSG("CyaSSL Encrypt programming error");
                return ENCRYPT_ERROR;
    }

    return 0;
}



static INLINE int Decrypt(CYASSL* ssl, byte* plain, const byte* input,
                           word16 sz)
{
    (void)plain;
    (void)input;
    (void)sz;

    if (ssl->decrypt.setup == 0) {
        CYASSL_MSG("Decrypt ciphers not setup");
        return DECRYPT_ERROR;
    }

    switch (ssl->specs.bulk_cipher_algorithm) {
        #ifdef BUILD_ARC4
            case cyassl_rc4:
                Arc4Process(ssl->decrypt.arc4, plain, input, sz);
                break;
        #endif

        #ifdef BUILD_DES3
            case cyassl_triple_des:
                return Des3_CbcDecrypt(ssl->decrypt.des3, plain, input, sz);
        #endif

        #ifdef BUILD_AES
            case cyassl_aes:
                return AesCbcDecrypt(ssl->decrypt.aes, plain, input, sz);
        #endif

        #ifdef BUILD_AESGCM
            case cyassl_aes_gcm:
            {
                byte additional[AEAD_AUTH_DATA_SZ];
                byte nonce[AEAD_NONCE_SZ];

                XMEMSET(additional, 0, AEAD_AUTH_DATA_SZ);

                /* sequence number field is 64-bits, we only use 32-bits */
                c32toa(GetSEQIncrement(ssl, 1), additional + AEAD_SEQ_OFFSET);

                #ifdef CYASSL_DTLS
                    if (ssl->options.dtls)
                        c16toa(ssl->keys.dtls_state.curEpoch, additional);
                #endif

                additional[AEAD_TYPE_OFFSET] = ssl->curRL.type;
                additional[AEAD_VMAJ_OFFSET] = ssl->curRL.pvMajor;
                additional[AEAD_VMIN_OFFSET] = ssl->curRL.pvMinor;

                c16toa(sz - AEAD_EXP_IV_SZ - ssl->specs.aead_mac_size,
                                        additional + AEAD_LEN_OFFSET);
                XMEMCPY(nonce, ssl->keys.aead_dec_imp_IV, AEAD_IMP_IV_SZ);
                XMEMCPY(nonce + AEAD_IMP_IV_SZ, input, AEAD_EXP_IV_SZ);
                if (AesGcmDecrypt(ssl->decrypt.aes,
                            plain + AEAD_EXP_IV_SZ,
                            input + AEAD_EXP_IV_SZ,
                                sz - AEAD_EXP_IV_SZ - ssl->specs.aead_mac_size,
                            nonce, AEAD_NONCE_SZ,
                            input + sz - ssl->specs.aead_mac_size,
                            ssl->specs.aead_mac_size,
                            additional, AEAD_AUTH_DATA_SZ) < 0) {
                    SendAlert(ssl, alert_fatal, bad_record_mac);
                    XMEMSET(nonce, 0, AEAD_NONCE_SZ);
                    return VERIFY_MAC_ERROR;
                }
                XMEMSET(nonce, 0, AEAD_NONCE_SZ);
            }
            break;
        #endif

        #ifdef HAVE_AESCCM
            case cyassl_aes_ccm:
            {
                byte additional[AEAD_AUTH_DATA_SZ];
                byte nonce[AEAD_NONCE_SZ];

                XMEMSET(additional, 0, AEAD_AUTH_DATA_SZ);

                /* sequence number field is 64-bits, we only use 32-bits */
                c32toa(GetSEQIncrement(ssl, 1), additional + AEAD_SEQ_OFFSET);

                #ifdef CYASSL_DTLS
                    if (ssl->options.dtls)
                        c16toa(ssl->keys.dtls_state.curEpoch, additional);
                #endif

                additional[AEAD_TYPE_OFFSET] = ssl->curRL.type;
                additional[AEAD_VMAJ_OFFSET] = ssl->curRL.pvMajor;
                additional[AEAD_VMIN_OFFSET] = ssl->curRL.pvMinor;

                c16toa(sz - AEAD_EXP_IV_SZ - ssl->specs.aead_mac_size,
                                        additional + AEAD_LEN_OFFSET);
                XMEMCPY(nonce, ssl->keys.aead_dec_imp_IV, AEAD_IMP_IV_SZ);
                XMEMCPY(nonce + AEAD_IMP_IV_SZ, input, AEAD_EXP_IV_SZ);
                if (AesCcmDecrypt(ssl->decrypt.aes,
                            plain + AEAD_EXP_IV_SZ,
                            input + AEAD_EXP_IV_SZ,
                                sz - AEAD_EXP_IV_SZ - ssl->specs.aead_mac_size,
                            nonce, AEAD_NONCE_SZ,
                            input + sz - ssl->specs.aead_mac_size,
                            ssl->specs.aead_mac_size,
                            additional, AEAD_AUTH_DATA_SZ) < 0) {
                    SendAlert(ssl, alert_fatal, bad_record_mac);
                    XMEMSET(nonce, 0, AEAD_NONCE_SZ);
                    return VERIFY_MAC_ERROR;
                }
                XMEMSET(nonce, 0, AEAD_NONCE_SZ);
            }
            break;
        #endif

        #ifdef HAVE_CAMELLIA
            case cyassl_camellia:
                CamelliaCbcDecrypt(ssl->decrypt.cam, plain, input, sz);
                break;
        #endif

        #ifdef HAVE_HC128
            case cyassl_hc128:
                return Hc128_Process(ssl->decrypt.hc128, plain, input, sz);
        #endif

        #ifdef BUILD_RABBIT
            case cyassl_rabbit:
                return RabbitProcess(ssl->decrypt.rabbit, plain, input, sz);
        #endif

        #ifdef HAVE_NULL_CIPHER
            case cyassl_cipher_null:
                if (input != plain) {
                    XMEMMOVE(plain, input, sz);
                }
                break;
        #endif
                
            default:
                CYASSL_MSG("CyaSSL Decrypt programming error");
                return DECRYPT_ERROR;
    }
    return 0;
}


/* check cipher text size for sanity */
static int SanityCheckCipherText(CYASSL* ssl, word32 encryptSz)
{
#ifdef HAVE_TRUNCATED_HMAC
    word32 minLength = ssl->truncated_hmac ? TRUNCATED_HMAC_SZ
                                           : ssl->specs.hash_size;
#else
    word32 minLength = ssl->specs.hash_size; /* covers stream */
#endif

    if (ssl->specs.cipher_type == block) {
        if (encryptSz % ssl->specs.block_size) {
            CYASSL_MSG("Block ciphertext not block size");
            return SANITY_CIPHER_E;
        }

        minLength++;  /* pad byte */

        if (ssl->specs.block_size > minLength)
            minLength = ssl->specs.block_size;

        if (ssl->options.tls1_1)
            minLength += ssl->specs.block_size;  /* explicit IV */
    }
    else if (ssl->specs.cipher_type == aead) {
        minLength = ssl->specs.aead_mac_size + AEAD_EXP_IV_SZ;
                                               /* explicit IV + authTag size */
    }

    if (encryptSz < minLength) {
        CYASSL_MSG("Ciphertext not minimum size");
        return SANITY_CIPHER_E;
    }

    return 0;
}


#ifndef NO_OLD_TLS

static INLINE void Md5Rounds(int rounds, const byte* data, int sz)
{
    Md5 md5;
    int i;

    InitMd5(&md5);

    for (i = 0; i < rounds; i++)
        Md5Update(&md5, data, sz);
}



/* do a dummy sha round */
static INLINE void ShaRounds(int rounds, const byte* data, int sz)
{
    Sha sha;
    int i;

    InitSha(&sha);  /* no error check on purpose, dummy round */

    for (i = 0; i < rounds; i++)
        ShaUpdate(&sha, data, sz);
}
#endif


#ifndef NO_SHA256

static INLINE void Sha256Rounds(int rounds, const byte* data, int sz)
{
    Sha256 sha256;
    int i;

    InitSha256(&sha256);  /* no error check on purpose, dummy round */

    for (i = 0; i < rounds; i++) {
        Sha256Update(&sha256, data, sz);
        /* no error check on purpose, dummy round */
    }

}

#endif


#ifdef CYASSL_SHA384

static INLINE void Sha384Rounds(int rounds, const byte* data, int sz)
{
    Sha384 sha384;
    int i;

    InitSha384(&sha384);  /* no error check on purpose, dummy round */

    for (i = 0; i < rounds; i++) {
        Sha384Update(&sha384, data, sz);
        /* no error check on purpose, dummy round */
    }
}

#endif


#ifdef CYASSL_SHA512

static INLINE void Sha512Rounds(int rounds, const byte* data, int sz)
{
    Sha512 sha512;
    int i;

    InitSha512(&sha512);  /* no error check on purpose, dummy round */

    for (i = 0; i < rounds; i++) {
        Sha512Update(&sha512, data, sz);
        /* no error check on purpose, dummy round */
    }
}

#endif


#ifdef CYASSL_RIPEMD

static INLINE void RmdRounds(int rounds, const byte* data, int sz)
{
    RipeMd ripemd;
    int i;

    InitRipeMd(&ripemd);

    for (i = 0; i < rounds; i++)
        RipeMdUpdate(&ripemd, data, sz);
}

#endif


/* Do dummy rounds */
static INLINE void DoRounds(int type, int rounds, const byte* data, int sz)
{
    switch (type) {
    
        case no_mac :
            break;

#ifndef NO_OLD_TLS
#ifndef NO_MD5
        case md5_mac :
            Md5Rounds(rounds, data, sz);
            break;
#endif

#ifndef NO_SHA
        case sha_mac :
            ShaRounds(rounds, data, sz);
            break;
#endif
#endif

#ifndef NO_SHA256
        case sha256_mac :
            Sha256Rounds(rounds, data, sz);
            break;
#endif

#ifdef CYASSL_SHA384
        case sha384_mac :
            Sha384Rounds(rounds, data, sz);
            break;
#endif

#ifdef CYASSL_SHA512
        case sha512_mac :
            Sha512Rounds(rounds, data, sz);
            break;
#endif

#ifdef CYASSL_RIPEMD 
        case rmd_mac :
            RmdRounds(rounds, data, sz);
            break;
#endif

        default:
            CYASSL_MSG("Bad round type");
            break;
    }
}


/* do number of compression rounds on dummy data */
static INLINE void CompressRounds(CYASSL* ssl, int rounds, const byte* dummy)
{
    if (rounds)
        DoRounds(ssl->specs.mac_algorithm, rounds, dummy, COMPRESS_LOWER);
}


/* check all length bytes for equality, return 0 on success */
static int ConstantCompare(const byte* a, const byte* b, int length)
{
    int i;
    int good = 0;
    int bad  = 0;

    for (i = 0; i < length; i++) {
        if (a[i] == b[i])
            good++;
        else
            bad++;
    }

    if (good == length)
        return 0;
    else
        return 0 - bad;  /* compare failed */
}


/* check all length bytes for the pad value, return 0 on success */
static int PadCheck(const byte* input, byte pad, int length)
{
    int i;
    int good = 0;
    int bad  = 0;

    for (i = 0; i < length; i++) {
        if (input[i] == pad)
            good++;
        else
            bad++;
    }

    if (good == length)
        return 0;
    else
        return 0 - bad;  /* pad check failed */
}


/* get compression extra rounds */
static INLINE int GetRounds(int pLen, int padLen, int t)
{
    int  roundL1 = 1;  /* round up flags */
    int  roundL2 = 1;

    int L1 = COMPRESS_CONSTANT + pLen - t;
    int L2 = COMPRESS_CONSTANT + pLen - padLen - 1 - t;

    L1 -= COMPRESS_UPPER;
    L2 -= COMPRESS_UPPER;

    if ( (L1 % COMPRESS_LOWER) == 0)
        roundL1 = 0;
    if ( (L2 % COMPRESS_LOWER) == 0)
        roundL2 = 0;

    L1 /= COMPRESS_LOWER;
    L2 /= COMPRESS_LOWER;

    L1 += roundL1;
    L2 += roundL2;

    return L1 - L2;
}


/* timing resistant pad/verify check, return 0 on success */
static int TimingPadVerify(CYASSL* ssl, const byte* input, int padLen, int t,
                           int pLen, int content)
{
    byte verify[MAX_DIGEST_SIZE];
    byte dummy[MAX_PAD_SIZE];
    int  ret = 0;

    XMEMSET(dummy, 1, sizeof(dummy));

    if ( (t + padLen + 1) > pLen) {
        CYASSL_MSG("Plain Len not long enough for pad/mac");
        PadCheck(dummy, (byte)padLen, MAX_PAD_SIZE);
        ssl->hmac(ssl, verify, input, pLen - t, content, 1); /* still compare */
        ConstantCompare(verify, input + pLen - t, t);

        return VERIFY_MAC_ERROR;
    }

    if (PadCheck(input + pLen - (padLen + 1), (byte)padLen, padLen + 1) != 0) {
        CYASSL_MSG("PadCheck failed");
        PadCheck(dummy, (byte)padLen, MAX_PAD_SIZE - padLen - 1);
        ssl->hmac(ssl, verify, input, pLen - t, content, 1); /* still compare */
        ConstantCompare(verify, input + pLen - t, t);

        return VERIFY_MAC_ERROR;
    }

    PadCheck(dummy, (byte)padLen, MAX_PAD_SIZE - padLen - 1);
    ret = ssl->hmac(ssl, verify, input, pLen - padLen - 1 - t, content, 1);

    CompressRounds(ssl, GetRounds(pLen, padLen, t), dummy);

    if (ConstantCompare(verify, input + (pLen - padLen - 1 - t), t) != 0) {
        CYASSL_MSG("Verify MAC compare failed");
        return VERIFY_MAC_ERROR;
    }

    if (ret != 0)
        return VERIFY_MAC_ERROR;
    return 0;
}


int DoApplicationData(CYASSL* ssl, byte* input, word32* inOutIdx)
{
    word32 msgSz   = ssl->keys.encryptSz;
    word32 idx     = *inOutIdx;
    int    dataSz;
    int    ivExtra = 0;
    byte*  rawData = input + idx;  /* keep current  for hmac */
#ifdef HAVE_LIBZ
    byte   decomp[MAX_RECORD_SIZE + MAX_COMP_EXTRA];
#endif

    if (ssl->options.handShakeState != HANDSHAKE_DONE) {
        CYASSL_MSG("Received App data before handshake complete");
        SendAlert(ssl, alert_fatal, unexpected_message);
        return OUT_OF_ORDER_E;
    }

    if (ssl->specs.cipher_type == block) {
        if (ssl->options.tls1_1)
            ivExtra = ssl->specs.block_size;
    }
    else if (ssl->specs.cipher_type == aead) {
        ivExtra = AEAD_EXP_IV_SZ;
    }

    dataSz = msgSz - ivExtra - ssl->keys.padSz;
    if (dataSz < 0) {
        CYASSL_MSG("App data buffer error, malicious input?"); 
        return BUFFER_ERROR;
    }

    /* read data */
    if (dataSz) {
        int rawSz = dataSz;       /* keep raw size for idx adjustment */

#ifdef HAVE_LIBZ
        if (ssl->options.usingCompression) {
            dataSz = myDeCompress(ssl, rawData, dataSz, decomp, sizeof(decomp));
            if (dataSz < 0) return dataSz;
        }
#endif
        idx += rawSz;

        ssl->buffers.clearOutputBuffer.buffer = rawData;
        ssl->buffers.clearOutputBuffer.length = dataSz;
    }

    idx += ssl->keys.padSz;

#ifdef HAVE_LIBZ
    /* decompress could be bigger, overwrite after verify */
    if (ssl->options.usingCompression)
        XMEMMOVE(rawData, decomp, dataSz);
#endif

    *inOutIdx = idx;
    return 0;
}


/* process alert, return level */
static int DoAlert(CYASSL* ssl, byte* input, word32* inOutIdx, int* type,
                   word32 totalSz)
{
    byte level;
    byte code;

    #ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn)
            AddPacketName("Alert", &ssl->handShakeInfo);
        if (ssl->toInfoOn)
            /* add record header back on to info + 2 byte level, data */
            AddPacketInfo("Alert", &ssl->timeoutInfo, input + *inOutIdx -
                          RECORD_HEADER_SZ, 2 + RECORD_HEADER_SZ, ssl->heap);
    #endif

    /* make sure can read the message */
    if (*inOutIdx + ALERT_SIZE > totalSz)
        return BUFFER_E;

    level = input[(*inOutIdx)++];
    code  = input[(*inOutIdx)++];
    ssl->alert_history.last_rx.code = code;
    ssl->alert_history.last_rx.level = level;
    *type = code;
    if (level == alert_fatal) {
        ssl->options.isClosed = 1;  /* Don't send close_notify */
    }

    CYASSL_MSG("Got alert");
    if (*type == close_notify) {
        CYASSL_MSG("    close notify");
        ssl->options.closeNotify = 1;
    }
    CYASSL_ERROR(*type);

    if (ssl->keys.encryptionOn) {
        if (*inOutIdx + ssl->keys.padSz > totalSz)
            return BUFFER_E;
        *inOutIdx += ssl->keys.padSz;
    }

    return level;
}

static int GetInputData(CYASSL *ssl, word32 size)
{
    int in;
    int inSz;
    int maxLength;
    int usedLength;
    int dtlsExtra = 0;

    
    /* check max input length */
    usedLength = ssl->buffers.inputBuffer.length - ssl->buffers.inputBuffer.idx;
    maxLength  = ssl->buffers.inputBuffer.bufferSize - usedLength;
    inSz       = (int)(size - usedLength);      /* from last partial read */

#ifdef CYASSL_DTLS
    if (ssl->options.dtls) {
        if (size < ssl->dtls_expected_rx)
            dtlsExtra = (int)(ssl->dtls_expected_rx - size);
        inSz = ssl->dtls_expected_rx;  
    }
#endif
    
    if (inSz > maxLength) {
        if (GrowInputBuffer(ssl, size + dtlsExtra, usedLength) < 0)
            return MEMORY_E;
    }
           
    if (inSz <= 0)
        return BUFFER_ERROR;
    
    /* Put buffer data at start if not there */
    if (usedLength > 0 && ssl->buffers.inputBuffer.idx != 0)
        XMEMMOVE(ssl->buffers.inputBuffer.buffer,
                ssl->buffers.inputBuffer.buffer + ssl->buffers.inputBuffer.idx,
                usedLength);
    
    /* remove processed data */
    ssl->buffers.inputBuffer.idx    = 0;
    ssl->buffers.inputBuffer.length = usedLength;
  
    /* read data from network */
    do {
        in = Receive(ssl, 
                     ssl->buffers.inputBuffer.buffer +
                     ssl->buffers.inputBuffer.length, 
                     inSz);
        if (in == -1)
            return SOCKET_ERROR_E;
   
        if (in == WANT_READ)
            return WANT_READ;

        if (in > inSz)
            return RECV_OVERFLOW_E;
        
        ssl->buffers.inputBuffer.length += in;
        inSz -= in;

    } while (ssl->buffers.inputBuffer.length < size);

    return 0;
}


static INLINE int VerifyMac(CYASSL* ssl, const byte* input, word32 msgSz,
                            int content, word32* padSz)
{
    int    ivExtra = 0;
    int    ret;
    word32 pad     = 0;
    word32 padByte = 0;
#ifdef HAVE_TRUNCATED_HMAC
    word32 digestSz = ssl->truncated_hmac ? TRUNCATED_HMAC_SZ
                                          : ssl->specs.hash_size;
#else
    word32 digestSz = ssl->specs.hash_size;
#endif
    byte   verify[MAX_DIGEST_SIZE];

    if (ssl->specs.cipher_type == block) {
        if (ssl->options.tls1_1)
            ivExtra = ssl->specs.block_size;
        pad = *(input + msgSz - ivExtra - 1);
        padByte = 1;

        if (ssl->options.tls) {
            ret = TimingPadVerify(ssl, input, pad, digestSz, msgSz - ivExtra,
                                  content);
            if (ret != 0)
                return ret;
        }
        else {  /* sslv3, some implementations have bad padding, but don't
                 * allow bad read */ 
            int  badPadLen = 0;
            byte dummy[MAX_PAD_SIZE];

            XMEMSET(dummy, 1, sizeof(dummy));

            if (pad > (msgSz - digestSz - 1)) {
                CYASSL_MSG("Plain Len not long enough for pad/mac");
                pad       = 0;  /* no bad read */
                badPadLen = 1;
            }
            PadCheck(dummy, (byte)pad, MAX_PAD_SIZE);  /* timing only */
            ret = ssl->hmac(ssl, verify, input, msgSz - digestSz - pad - 1,
                            content, 1);
            if (ConstantCompare(verify, input + msgSz - digestSz - pad - 1,
                                digestSz) != 0)
                return VERIFY_MAC_ERROR;
            if (ret != 0 || badPadLen)
                return VERIFY_MAC_ERROR;
        }
    }
    else if (ssl->specs.cipher_type == stream) {
        ret = ssl->hmac(ssl, verify, input, msgSz - digestSz, content, 1);
        if (ConstantCompare(verify, input + msgSz - digestSz, digestSz) != 0){
            return VERIFY_MAC_ERROR;
        }
        if (ret != 0)
            return VERIFY_MAC_ERROR;
    }

    if (ssl->specs.cipher_type == aead) {
        *padSz = ssl->specs.aead_mac_size;
    }
    else {
        *padSz = digestSz + pad + padByte;
    }

    return 0;
}


/* process input requests, return 0 is done, 1 is call again to complete, and
   negative number is error */
int ProcessReply(CYASSL* ssl)
{
    int    ret = 0, type, readSz;
    int    atomicUser = 0;
    word32 startIdx = 0;
#ifndef NO_CYASSL_SERVER
    byte   b0, b1;
#endif
#ifdef CYASSL_DTLS
    int    used;
#endif

#ifdef ATOMIC_USER
    if (ssl->ctx->DecryptVerifyCb)
        atomicUser = 1;
#endif

    if (ssl->error != 0 && ssl->error != WANT_READ && ssl->error != WANT_WRITE){
        CYASSL_MSG("ProcessReply retry in error state, not allowed");
        return ssl->error;
    }

    for (;;) {
        switch (ssl->options.processReply) {

        /* in the CYASSL_SERVER case, get the first byte for detecting 
         * old client hello */
        case doProcessInit:
            
            readSz = RECORD_HEADER_SZ;
            
            #ifdef CYASSL_DTLS
                if (ssl->options.dtls)
                    readSz = DTLS_RECORD_HEADER_SZ;
            #endif

            /* get header or return error */
            if (!ssl->options.dtls) {
                if ((ret = GetInputData(ssl, readSz)) < 0)
                    return ret;
            } else {
            #ifdef CYASSL_DTLS
                /* read ahead may already have header */
                used = ssl->buffers.inputBuffer.length -
                       ssl->buffers.inputBuffer.idx;
                if (used < readSz)
                    if ((ret = GetInputData(ssl, readSz)) < 0)
                        return ret;
            #endif
            }

#ifndef NO_CYASSL_SERVER

            /* see if sending SSLv2 client hello */
            if ( ssl->options.side == CYASSL_SERVER_END &&
                 ssl->options.clientState == NULL_STATE &&
                 ssl->buffers.inputBuffer.buffer[ssl->buffers.inputBuffer.idx]
                         != handshake) {
                ssl->options.processReply = runProcessOldClientHello;

                /* how many bytes need ProcessOldClientHello */
                b0 =
                ssl->buffers.inputBuffer.buffer[ssl->buffers.inputBuffer.idx++];
                b1 =
                ssl->buffers.inputBuffer.buffer[ssl->buffers.inputBuffer.idx++];
                ssl->curSize = (word16)(((b0 & 0x7f) << 8) | b1);
            }
            else {
                ssl->options.processReply = getRecordLayerHeader;
                continue;
            }

        /* in the CYASSL_SERVER case, run the old client hello */
        case runProcessOldClientHello:     

            /* get sz bytes or return error */
            if (!ssl->options.dtls) {
                if ((ret = GetInputData(ssl, ssl->curSize)) < 0)
                    return ret;
            } else {
            #ifdef CYASSL_DTLS
                /* read ahead may already have */
                used = ssl->buffers.inputBuffer.length -
                       ssl->buffers.inputBuffer.idx;
                if (used < ssl->curSize)
                    if ((ret = GetInputData(ssl, ssl->curSize)) < 0)
                        return ret;
            #endif  /* CYASSL_DTLS */
            }

            ret = ProcessOldClientHello(ssl, ssl->buffers.inputBuffer.buffer,
                                        &ssl->buffers.inputBuffer.idx,
                                        ssl->buffers.inputBuffer.length -
                                        ssl->buffers.inputBuffer.idx,
                                        ssl->curSize);
            if (ret < 0)
                return ret;

            else if (ssl->buffers.inputBuffer.idx ==
                     ssl->buffers.inputBuffer.length) {
                ssl->options.processReply = doProcessInit;
                return 0;
            }

#endif  /* NO_CYASSL_SERVER */

        /* get the record layer header */
        case getRecordLayerHeader:

            ret = GetRecordHeader(ssl, ssl->buffers.inputBuffer.buffer,
                                       &ssl->buffers.inputBuffer.idx,
                                       &ssl->curRL, &ssl->curSize);
#ifdef CYASSL_DTLS
            if (ssl->options.dtls && ret == SEQUENCE_ERROR) {
                ssl->options.processReply = doProcessInit;
                ssl->buffers.inputBuffer.length = 0;
                ssl->buffers.inputBuffer.idx = 0;
                continue;
            }
#endif
            if (ret != 0)
                return ret;

            ssl->options.processReply = getData;

        /* retrieve record layer data */
        case getData:

            /* get sz bytes or return error */
            if (!ssl->options.dtls) {
                if ((ret = GetInputData(ssl, ssl->curSize)) < 0)
                    return ret;
            } else {
#ifdef CYASSL_DTLS
                /* read ahead may already have */
                used = ssl->buffers.inputBuffer.length -
                       ssl->buffers.inputBuffer.idx;
                if (used < ssl->curSize)
                    if ((ret = GetInputData(ssl, ssl->curSize)) < 0)
                        return ret;
#endif
            }
            
            ssl->options.processReply = runProcessingOneMessage;
            startIdx = ssl->buffers.inputBuffer.idx;  /* in case > 1 msg per */

        /* the record layer is here */
        case runProcessingOneMessage:

            #ifdef CYASSL_DTLS
            if (ssl->options.dtls &&
                ssl->keys.dtls_state.curEpoch < ssl->keys.dtls_state.nextEpoch)
                ssl->keys.decryptedCur = 1;
            #endif

            if (ssl->keys.encryptionOn && ssl->keys.decryptedCur == 0)
            {
                ret = SanityCheckCipherText(ssl, ssl->curSize);
                if (ret < 0)
                    return ret;

                if (atomicUser) {
                #ifdef ATOMIC_USER
                    ret = ssl->ctx->DecryptVerifyCb(ssl,
                                  ssl->buffers.inputBuffer.buffer + 
                                  ssl->buffers.inputBuffer.idx,
                                  ssl->buffers.inputBuffer.buffer +
                                  ssl->buffers.inputBuffer.idx,
                                  ssl->curSize, ssl->curRL.type, 1,
                                  &ssl->keys.padSz, ssl->DecryptVerifyCtx);
                    if (ssl->options.tls1_1 && ssl->specs.cipher_type == block)
                        ssl->buffers.inputBuffer.idx += ssl->specs.block_size;
                        /* go past TLSv1.1 IV */
                    if (ssl->specs.cipher_type == aead)
                        ssl->buffers.inputBuffer.idx += AEAD_EXP_IV_SZ;
                #endif /* ATOMIC_USER */
                }
                else {
                    ret = Decrypt(ssl, ssl->buffers.inputBuffer.buffer + 
                                  ssl->buffers.inputBuffer.idx,
                                  ssl->buffers.inputBuffer.buffer +
                                  ssl->buffers.inputBuffer.idx,
                                  ssl->curSize);
                    if (ret < 0) {
                        CYASSL_ERROR(ret);
                        return DECRYPT_ERROR;
                    }
                    if (ssl->options.tls1_1 && ssl->specs.cipher_type == block)
                        ssl->buffers.inputBuffer.idx += ssl->specs.block_size;
                        /* go past TLSv1.1 IV */
                    if (ssl->specs.cipher_type == aead)
                        ssl->buffers.inputBuffer.idx += AEAD_EXP_IV_SZ;

                    ret = VerifyMac(ssl, ssl->buffers.inputBuffer.buffer +
                                    ssl->buffers.inputBuffer.idx,
                                    ssl->curSize, ssl->curRL.type,
                                    &ssl->keys.padSz);
                }
                if (ret < 0) {
                    CYASSL_ERROR(ret);
                    return DECRYPT_ERROR;
                }
                ssl->keys.encryptSz    = ssl->curSize;
                ssl->keys.decryptedCur = 1;
            }

            if (ssl->options.dtls) {
            #ifdef CYASSL_DTLS
                DtlsUpdateWindow(&ssl->keys.dtls_state);
            #endif /* CYASSL_DTLS */
            }

            CYASSL_MSG("received record layer msg");

            switch (ssl->curRL.type) {
                case handshake :
                    /* debugging in DoHandShakeMsg */
                    if (!ssl->options.dtls) {
                        ret = DoHandShakeMsg(ssl, 
                                            ssl->buffers.inputBuffer.buffer,
                                            &ssl->buffers.inputBuffer.idx,
                                            ssl->buffers.inputBuffer.length);
                    }
                    else {
#ifdef CYASSL_DTLS
                        ret = DoDtlsHandShakeMsg(ssl, 
                                            ssl->buffers.inputBuffer.buffer,
                                            &ssl->buffers.inputBuffer.idx,
                                            ssl->buffers.inputBuffer.length);
#endif
                    }
                    if (ret != 0)
                        return ret;
                    break;

                case change_cipher_spec:
                    CYASSL_MSG("got CHANGE CIPHER SPEC");
                    #ifdef CYASSL_CALLBACKS
                        if (ssl->hsInfoOn)
                            AddPacketName("ChangeCipher", &ssl->handShakeInfo);
                        /* add record header back on info */
                        if (ssl->toInfoOn) {
                            AddPacketInfo("ChangeCipher", &ssl->timeoutInfo,
                                ssl->buffers.inputBuffer.buffer +
                                ssl->buffers.inputBuffer.idx - RECORD_HEADER_SZ,
                                1 + RECORD_HEADER_SZ, ssl->heap);
                            AddLateRecordHeader(&ssl->curRL, &ssl->timeoutInfo);
                        }
                    #endif

                    if (ssl->curSize != 1) {
                        CYASSL_MSG("Malicious or corrupted ChangeCipher msg");
                        return LENGTH_ERROR;
                    }
                    #ifndef NO_CERTS
                        if (ssl->options.side == CYASSL_SERVER_END &&
                                 ssl->options.verifyPeer &&
                                 ssl->options.havePeerCert)
                            if (!ssl->options.havePeerVerify) {
                                CYASSL_MSG("client didn't send cert verify");
                                return NO_PEER_VERIFY;
                            }
                    #endif


                    ssl->buffers.inputBuffer.idx++;
                    ssl->keys.encryptionOn = 1;

                    #ifdef CYASSL_DTLS
                        if (ssl->options.dtls) {
                            DtlsPoolReset(ssl);
                            ssl->keys.dtls_state.nextEpoch++;
                            ssl->keys.dtls_state.nextSeq = 0;
                        }
                    #endif

                    #ifdef HAVE_LIBZ
                        if (ssl->options.usingCompression)
                            if ( (ret = InitStreams(ssl)) != 0)
                                return ret;
                    #endif
                    if (ssl->options.resuming && ssl->options.side ==
                                                              CYASSL_CLIENT_END)
                        ret = BuildFinished(ssl, &ssl->verifyHashes, server);
                    else if (!ssl->options.resuming && ssl->options.side ==
                                                              CYASSL_SERVER_END)
                        ret = BuildFinished(ssl, &ssl->verifyHashes, client);
                    if (ret != 0)
                        return ret;
                    break;

                case application_data:
                    CYASSL_MSG("got app DATA");
                    if ((ret = DoApplicationData(ssl,
                                                ssl->buffers.inputBuffer.buffer,
                                               &ssl->buffers.inputBuffer.idx))
                                                                         != 0) {
                        CYASSL_ERROR(ret);
                        return ret;
                    }
                    break;

                case alert:
                    CYASSL_MSG("got ALERT!");
                    ret = DoAlert(ssl, ssl->buffers.inputBuffer.buffer,
                                  &ssl->buffers.inputBuffer.idx, &type,
                                   ssl->buffers.inputBuffer.length);
                    if (ret == alert_fatal)
                        return FATAL_ERROR;
                    else if (ret < 0)
                        return ret;

                    /* catch warnings that are handled as errors */
                    if (type == close_notify)
                        return ssl->error = ZERO_RETURN;
                           
                    if (type == decrypt_error)
                        return FATAL_ERROR;
                    break;
            
                default:
                    CYASSL_ERROR(UNKNOWN_RECORD_TYPE);
                    return UNKNOWN_RECORD_TYPE;
            }

            ssl->options.processReply = doProcessInit;

            /* input exhausted? */
            if (ssl->buffers.inputBuffer.idx == ssl->buffers.inputBuffer.length)
                return 0;
            /* more messages per record */
            else if ((ssl->buffers.inputBuffer.idx - startIdx) < ssl->curSize) {
                CYASSL_MSG("More messages in record");
                #ifdef CYASSL_DTLS
                    /* read-ahead but dtls doesn't bundle messages per record */
                    if (ssl->options.dtls) {
                        ssl->options.processReply = doProcessInit;
                        continue;
                    }
                #endif
                ssl->options.processReply = runProcessingOneMessage;
                continue;
            }
            /* more records */
            else {
                CYASSL_MSG("More records in input");
                ssl->options.processReply = doProcessInit;
                continue;
            }

        default:
            CYASSL_MSG("Bad process input state, programming error");
            return INPUT_CASE_ERROR;
        }
    }
}


int SendChangeCipher(CYASSL* ssl)
{
    byte              *output;
    int                sendSz = RECORD_HEADER_SZ + ENUM_LEN;
    int                idx    = RECORD_HEADER_SZ;
    int                ret;

    #ifdef CYASSL_DTLS
        if (ssl->options.dtls) {
            sendSz += DTLS_RECORD_EXTRA;
            idx    += DTLS_RECORD_EXTRA;
        }
    #endif

    /* check for avalaible size */
    if ((ret = CheckAvailableSize(ssl, sendSz)) != 0)
        return ret;

    /* get ouput buffer */
    output = ssl->buffers.outputBuffer.buffer + 
             ssl->buffers.outputBuffer.length;

    AddRecordHeader(output, 1, change_cipher_spec, ssl);

    output[idx] = 1;             /* turn it on */

    #ifdef CYASSL_DTLS
        if (ssl->options.dtls) {
            if ((ret = DtlsPoolSave(ssl, output, sendSz)) != 0)
                return ret;
        }
    #endif
    #ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn) AddPacketName("ChangeCipher", &ssl->handShakeInfo);
        if (ssl->toInfoOn)
            AddPacketInfo("ChangeCipher", &ssl->timeoutInfo, output, sendSz,
                           ssl->heap);
    #endif
    ssl->buffers.outputBuffer.length += sendSz;

    if (ssl->options.groupMessages)
        return 0;
    #ifdef CYASSL_DTLS
    else if (ssl->options.dtls) {
        /* If using DTLS, force the ChangeCipherSpec message to be in the
         * same datagram as the finished message. */
        return 0;
    }
    #endif
    else
        return SendBuffered(ssl);
}


#ifndef NO_OLD_TLS
static int SSL_hmac(CYASSL* ssl, byte* digest, const byte* in, word32 sz,
                 int content, int verify)
{
    byte   result[MAX_DIGEST_SIZE];
    word32 digestSz = ssl->specs.hash_size;            /* actual sizes */
    word32 padSz    = ssl->specs.pad_size;
    int    ret      = 0;

    Md5 md5;
    Sha sha;

    /* data */
    byte seq[SEQ_SZ];
    byte conLen[ENUM_LEN + LENGTH_SZ];     /* content & length */
    const byte* macSecret = CyaSSL_GetMacSecret(ssl, verify);
    
    XMEMSET(seq, 0, SEQ_SZ);
    conLen[0] = (byte)content;
    c16toa((word16)sz, &conLen[ENUM_LEN]);
    c32toa(GetSEQIncrement(ssl, verify), &seq[sizeof(word32)]);

    if (ssl->specs.mac_algorithm == md5_mac) {
        InitMd5(&md5);
        /* inner */
        Md5Update(&md5, macSecret, digestSz);
        Md5Update(&md5, PAD1, padSz);
        Md5Update(&md5, seq, SEQ_SZ);
        Md5Update(&md5, conLen, sizeof(conLen));
        /* in buffer */
        Md5Update(&md5, in, sz);
        Md5Final(&md5, result);
        /* outer */
        Md5Update(&md5, macSecret, digestSz);
        Md5Update(&md5, PAD2, padSz);
        Md5Update(&md5, result, digestSz);
        Md5Final(&md5, digest);        
    }
    else {
        ret = InitSha(&sha);
        if (ret != 0)
            return ret;
        /* inner */
        ShaUpdate(&sha, macSecret, digestSz);
        ShaUpdate(&sha, PAD1, padSz);
        ShaUpdate(&sha, seq, SEQ_SZ);
        ShaUpdate(&sha, conLen, sizeof(conLen));
        /* in buffer */
        ShaUpdate(&sha, in, sz);
        ShaFinal(&sha, result);
        /* outer */
        ShaUpdate(&sha, macSecret, digestSz);
        ShaUpdate(&sha, PAD2, padSz);
        ShaUpdate(&sha, result, digestSz);
        ShaFinal(&sha, digest);        
    }
    return 0;
}

#ifndef NO_CERTS
static void BuildMD5_CertVerify(CYASSL* ssl, byte* digest)
{
    byte md5_result[MD5_DIGEST_SIZE];

    /* make md5 inner */
    Md5Update(&ssl->hashMd5, ssl->arrays->masterSecret, SECRET_LEN);
    Md5Update(&ssl->hashMd5, PAD1, PAD_MD5);
    Md5Final(&ssl->hashMd5, md5_result);

    /* make md5 outer */
    Md5Update(&ssl->hashMd5, ssl->arrays->masterSecret, SECRET_LEN);
    Md5Update(&ssl->hashMd5, PAD2, PAD_MD5);
    Md5Update(&ssl->hashMd5, md5_result, MD5_DIGEST_SIZE);

    Md5Final(&ssl->hashMd5, digest);
}


static void BuildSHA_CertVerify(CYASSL* ssl, byte* digest)
{
    byte sha_result[SHA_DIGEST_SIZE];
    
    /* make sha inner */
    ShaUpdate(&ssl->hashSha, ssl->arrays->masterSecret, SECRET_LEN);
    ShaUpdate(&ssl->hashSha, PAD1, PAD_SHA);
    ShaFinal(&ssl->hashSha, sha_result);

    /* make sha outer */
    ShaUpdate(&ssl->hashSha, ssl->arrays->masterSecret, SECRET_LEN);
    ShaUpdate(&ssl->hashSha, PAD2, PAD_SHA);
    ShaUpdate(&ssl->hashSha, sha_result, SHA_DIGEST_SIZE);

    ShaFinal(&ssl->hashSha, digest);
}
#endif /* NO_CERTS */
#endif /* NO_OLD_TLS */


#ifndef NO_CERTS

static int BuildCertHashes(CYASSL* ssl, Hashes* hashes)
{
    /* store current states, building requires get_digest which resets state */
    #ifndef NO_OLD_TLS
    Md5 md5 = ssl->hashMd5;
    Sha sha = ssl->hashSha;
    #endif
    #ifndef NO_SHA256
        Sha256 sha256 = ssl->hashSha256;
    #endif
    #ifdef CYASSL_SHA384
        Sha384 sha384 = ssl->hashSha384;
    #endif
    
    if (ssl->options.tls) {
#if ! defined( NO_OLD_TLS )
        Md5Final(&ssl->hashMd5, hashes->md5);
        ShaFinal(&ssl->hashSha, hashes->sha);
#endif
        if (IsAtLeastTLSv1_2(ssl)) {
            int ret;

            #ifndef NO_SHA256
                ret = Sha256Final(&ssl->hashSha256, hashes->sha256);
                if (ret != 0)
                    return ret;
            #endif
            #ifdef CYASSL_SHA384
                ret = Sha384Final(&ssl->hashSha384, hashes->sha384);
                if (ret != 0)
                    return ret;
            #endif
        }
    }
#if ! defined( NO_OLD_TLS )
    else {
        BuildMD5_CertVerify(ssl, hashes->md5);
        BuildSHA_CertVerify(ssl, hashes->sha);
    }
    
    /* restore */
    ssl->hashMd5 = md5;
    ssl->hashSha = sha;
#endif
    if (IsAtLeastTLSv1_2(ssl)) {
        #ifndef NO_SHA256
            ssl->hashSha256 = sha256;
        #endif
        #ifdef CYASSL_SHA384
            ssl->hashSha384 = sha384;
        #endif
    }

    return 0;
}

#endif /* CYASSL_LEANPSK */

/* Build SSL Message, encrypted */
static int BuildMessage(CYASSL* ssl, byte* output, int outSz,
                        const byte* input, int inSz, int type)
{
#ifdef HAVE_TRUNCATED_HMAC
    word32 digestSz = min(ssl->specs.hash_size,
                ssl->truncated_hmac ? TRUNCATED_HMAC_SZ : ssl->specs.hash_size);
#else
    word32 digestSz = ssl->specs.hash_size;
#endif
    word32 sz = RECORD_HEADER_SZ + inSz + digestSz;                
    word32 pad  = 0, i;
    word32 idx  = RECORD_HEADER_SZ;
    word32 ivSz = 0;      /* TLSv1.1  IV */
    word32 headerSz = RECORD_HEADER_SZ;
    word16 size;
    byte               iv[AES_BLOCK_SIZE];                  /* max size */
    int ret        = 0;
    int atomicUser = 0;

#ifdef CYASSL_DTLS
    if (ssl->options.dtls) {
        sz       += DTLS_RECORD_EXTRA;
        idx      += DTLS_RECORD_EXTRA; 
        headerSz += DTLS_RECORD_EXTRA;
    }
#endif

#ifdef ATOMIC_USER
    if (ssl->ctx->MacEncryptCb)
        atomicUser = 1;
#endif

    if (ssl->specs.cipher_type == block) {
        word32 blockSz = ssl->specs.block_size;
        if (ssl->options.tls1_1) {
            ivSz = blockSz;
            sz  += ivSz;

            ret = RNG_GenerateBlock(ssl->rng, iv, ivSz);
            if (ret != 0)
                return ret;

        }
        sz += 1;       /* pad byte */
        pad = (sz - headerSz) % blockSz;
        pad = blockSz - pad;
        sz += pad;
    }

#ifdef HAVE_AEAD
    if (ssl->specs.cipher_type == aead) {
        ivSz = AEAD_EXP_IV_SZ;
        sz += (ivSz + ssl->specs.aead_mac_size - digestSz);
        XMEMCPY(iv, ssl->keys.aead_exp_IV, AEAD_EXP_IV_SZ);
    }
#endif
    if (sz > (word32)outSz) {
        CYASSL_MSG("Oops, want to write past output buffer size");
        return BUFFER_E;
    }
    size = (word16)(sz - headerSz);    /* include mac and digest */
    AddRecordHeader(output, size, (byte)type, ssl);    

    /* write to output */
    if (ivSz) {
        XMEMCPY(output + idx, iv, min(ivSz, sizeof(iv)));
        idx += ivSz;
    }
    XMEMCPY(output + idx, input, inSz);
    idx += inSz;

    if (type == handshake) {
        ret = HashOutput(ssl, output, headerSz + inSz, ivSz);
        if (ret != 0)
            return ret;
    }

    if (ssl->specs.cipher_type == block) {
        word32 tmpIdx = idx + digestSz;

        for (i = 0; i <= pad; i++)
            output[tmpIdx++] = (byte)pad; /* pad byte gets pad value too */
    }

    if (atomicUser) {   /* User Record Layer Callback handling */
#ifdef ATOMIC_USER
        if ( (ret = ssl->ctx->MacEncryptCb(ssl, output + idx,
                        output + headerSz + ivSz, inSz, type, 0,
                        output + headerSz, output + headerSz, size,
                        ssl->MacEncryptCtx)) != 0)
            return ret;
#endif
    }
    else {  
        if (ssl->specs.cipher_type != aead) {
#ifdef HAVE_TRUNCATED_HMAC
            if (ssl->truncated_hmac && ssl->specs.hash_size > digestSz) {
                byte hmac[MAX_DIGEST_SIZE];

                ret = ssl->hmac(ssl, hmac, output + headerSz + ivSz, inSz,
                                type, 0);
                XMEMCPY(output + idx, hmac, digestSz);
            } else
#endif
                ret = ssl->hmac(ssl, output+idx, output + headerSz + ivSz, inSz,
                                                                       type, 0);
        }
        if (ret != 0)
            return ret;

        if ( (ret = Encrypt(ssl, output + headerSz, output+headerSz,size)) != 0)
            return ret;
    }

    return sz;
}


int SendFinished(CYASSL* ssl)
{
    int              sendSz,
                     finishedSz = ssl->options.tls ? TLS_FINISHED_SZ :
                                                     FINISHED_SZ;
    byte             input[FINISHED_SZ + DTLS_HANDSHAKE_HEADER_SZ];  /* max */
    byte            *output;
    Hashes*          hashes;
    int              ret;
    int              headerSz = HANDSHAKE_HEADER_SZ;
    int              outputSz;

    #ifdef CYASSL_DTLS
        word32 sequence_number = ssl->keys.dtls_sequence_number;
        word16 epoch           = ssl->keys.dtls_epoch;
    #endif


    /* check for available size */
    outputSz = sizeof(input) + MAX_MSG_EXTRA;
    if ((ret = CheckAvailableSize(ssl, outputSz)) != 0)
        return ret;

    #ifdef CYASSL_DTLS
        if (ssl->options.dtls) {
            /* Send Finished message with the next epoch, but don't commit that
             * change until the other end confirms its reception. */
            headerSz += DTLS_HANDSHAKE_EXTRA;
            ssl->keys.dtls_epoch++;
            ssl->keys.dtls_sequence_number = 0;  /* reset after epoch change */
        }
    #endif

    /* get ouput buffer */
    output = ssl->buffers.outputBuffer.buffer + 
             ssl->buffers.outputBuffer.length;

    AddHandShakeHeader(input, finishedSz, finished, ssl);

    /* make finished hashes */
    hashes = (Hashes*)&input[headerSz];
    ret = BuildFinished(ssl, hashes,
                      ssl->options.side == CYASSL_CLIENT_END ? client : server);
    if (ret != 0) return ret;

    sendSz = BuildMessage(ssl, output, outputSz, input, headerSz + finishedSz,
                          handshake);
    if (sendSz < 0)
        return BUILD_MSG_ERROR;

    #ifdef CYASSL_DTLS
    if (ssl->options.dtls) {
        ssl->keys.dtls_epoch = epoch;
        ssl->keys.dtls_sequence_number = sequence_number;
    }
    #endif

    if (!ssl->options.resuming) {
#ifndef NO_SESSION_CACHE
        AddSession(ssl);    /* just try */
#endif
        if (ssl->options.side == CYASSL_CLIENT_END) {
            ret = BuildFinished(ssl, &ssl->verifyHashes, server);
            if (ret != 0) return ret;
        }
        else {
            ssl->options.handShakeState = HANDSHAKE_DONE;
            #ifdef CYASSL_DTLS
                if (ssl->options.dtls) {
                    /* Other side will soon receive our Finished, go to next
                     * epoch. */
                    ssl->keys.dtls_epoch++;
                    ssl->keys.dtls_sequence_number = 1;
                }
            #endif
        }
    }
    else {
        if (ssl->options.side == CYASSL_CLIENT_END) {
            ssl->options.handShakeState = HANDSHAKE_DONE;
            #ifdef CYASSL_DTLS
                if (ssl->options.dtls) {
                    /* Other side will soon receive our Finished, go to next
                     * epoch. */
                    ssl->keys.dtls_epoch++;
                    ssl->keys.dtls_sequence_number = 1;
                }
            #endif
        }
        else {
            ret = BuildFinished(ssl, &ssl->verifyHashes, client);
            if (ret != 0) return ret;
        }
    }
    #ifdef CYASSL_DTLS
        if (ssl->options.dtls) {
            if ((ret = DtlsPoolSave(ssl, output, sendSz)) != 0)
                return ret;
        }
    #endif

    #ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn) AddPacketName("Finished", &ssl->handShakeInfo);
        if (ssl->toInfoOn)
            AddPacketInfo("Finished", &ssl->timeoutInfo, output, sendSz,
                          ssl->heap);
    #endif

    ssl->buffers.outputBuffer.length += sendSz;

    return SendBuffered(ssl);
}

#ifndef NO_CERTS
int SendCertificate(CYASSL* ssl)
{
    int    sendSz, length, ret = 0;
    word32 i = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
    word32 certSz, listSz;
    byte*  output = 0;

    if (ssl->options.usingPSK_cipher) return 0;  /* not needed */

    if (ssl->options.sendVerify == SEND_BLANK_CERT) {
        certSz = 0;
        length = CERT_HEADER_SZ;
        listSz = 0;
    }
    else {
        certSz = ssl->buffers.certificate.length;
        /* list + cert size */
        length = certSz + 2 * CERT_HEADER_SZ;
        listSz = certSz + CERT_HEADER_SZ;

        /* may need to send rest of chain, already has leading size(s) */
        if (ssl->buffers.certChain.buffer) {
            length += ssl->buffers.certChain.length;
            listSz += ssl->buffers.certChain.length;
        }
    }
    sendSz = length + RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;

    #ifdef CYASSL_DTLS
        if (ssl->options.dtls) {
            sendSz += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
            i      += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
        }
    #endif

    /* check for available size */
    if ((ret = CheckAvailableSize(ssl, sendSz)) != 0)
        return ret;

    /* get ouput buffer */
    output = ssl->buffers.outputBuffer.buffer +
             ssl->buffers.outputBuffer.length;

    AddHeaders(output, length, certificate, ssl);

    /* list total */
    c32to24(listSz, output + i);
    i += CERT_HEADER_SZ;

    /* member */
    if (certSz) {
        c32to24(certSz, output + i);
        i += CERT_HEADER_SZ;
        XMEMCPY(output + i, ssl->buffers.certificate.buffer, certSz);
        i += certSz;

        /* send rest of chain? */
        if (ssl->buffers.certChain.buffer) {
            XMEMCPY(output + i, ssl->buffers.certChain.buffer,
                                ssl->buffers.certChain.length);
            /* if add more to output adjust i
               i += ssl->buffers.certChain.length; */
        }
    }
    #ifdef CYASSL_DTLS
        if (ssl->options.dtls) {
            if ((ret = DtlsPoolSave(ssl, output, sendSz)) != 0)
                return ret;
        }
    #endif

    ret = HashOutput(ssl, output, sendSz, 0);
    if (ret != 0)
        return ret;

    #ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn) AddPacketName("Certificate", &ssl->handShakeInfo);
        if (ssl->toInfoOn)
            AddPacketInfo("Certificate", &ssl->timeoutInfo, output, sendSz,
                           ssl->heap);
    #endif

    if (ssl->options.side == CYASSL_SERVER_END)
        ssl->options.serverState = SERVER_CERT_COMPLETE;

    ssl->buffers.outputBuffer.length += sendSz;
    if (ssl->options.groupMessages)
        return 0;
    else
        return SendBuffered(ssl);
}


int SendCertificateRequest(CYASSL* ssl)
{
    byte   *output;
    int    ret;
    int    sendSz;
    word32 i = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
    
    int  typeTotal = 1;  /* only 1 for now */
    int  reqSz = ENUM_LEN + typeTotal + REQ_HEADER_SZ;  /* add auth later */

    if (IsAtLeastTLSv1_2(ssl))
        reqSz += LENGTH_SZ + ssl->suites->hashSigAlgoSz;

    if (ssl->options.usingPSK_cipher) return 0;  /* not needed */

    sendSz = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ + reqSz;

    #ifdef CYASSL_DTLS
        if (ssl->options.dtls) {
            sendSz += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
            i      += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
        }
    #endif
    /* check for available size */
    if ((ret = CheckAvailableSize(ssl, sendSz)) != 0)
        return ret;

    /* get ouput buffer */
    output = ssl->buffers.outputBuffer.buffer +
             ssl->buffers.outputBuffer.length;

    AddHeaders(output, reqSz, certificate_request, ssl);

    /* write to output */
    output[i++] = (byte)typeTotal;  /* # of types */
#ifdef HAVE_ECC
    if (ssl->options.cipherSuite0 == ECC_BYTE &&
                     ssl->specs.sig_algo == ecc_dsa_sa_algo) {
        output[i++] = ecdsa_sign;
    } else
#endif /* HAVE_ECC */
    {
        output[i++] = rsa_sign;
    }

    /* supported hash/sig */
    if (IsAtLeastTLSv1_2(ssl)) {
        c16toa(ssl->suites->hashSigAlgoSz, &output[i]);
        i += LENGTH_SZ;

        XMEMCPY(&output[i],
                         ssl->suites->hashSigAlgo, ssl->suites->hashSigAlgoSz);
        i += ssl->suites->hashSigAlgoSz;
    }

    c16toa(0, &output[i]);  /* auth's */
    /* if add more to output, adjust i
    i += REQ_HEADER_SZ; */

    #ifdef CYASSL_DTLS
        if (ssl->options.dtls) {
            if ((ret = DtlsPoolSave(ssl, output, sendSz)) != 0)
                return ret;
        }
    #endif

    ret = HashOutput(ssl, output, sendSz, 0);
    if (ret != 0)
        return ret;

    #ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn)
            AddPacketName("CertificateRequest", &ssl->handShakeInfo);
        if (ssl->toInfoOn)
            AddPacketInfo("CertificateRequest", &ssl->timeoutInfo, output,
                          sendSz, ssl->heap);
    #endif
    ssl->buffers.outputBuffer.length += sendSz;
    if (ssl->options.groupMessages)
        return 0;
    else
        return SendBuffered(ssl);
}
#endif /* !NO_CERTS */


int SendData(CYASSL* ssl, const void* data, int sz)
{
    int sent = 0,  /* plainText size */
        sendSz,
        ret,
        dtlsExtra = 0;

    if (ssl->error == WANT_WRITE)
        ssl->error = 0;

    if (ssl->options.handShakeState != HANDSHAKE_DONE) {
        int err;
        CYASSL_MSG("handshake not complete, trying to finish");
        if ( (err = CyaSSL_negotiate(ssl)) != SSL_SUCCESS) 
            return  err;
    }

    /* last time system socket output buffer was full, try again to send */
    if (ssl->buffers.outputBuffer.length > 0) {
        CYASSL_MSG("output buffer was full, trying to send again");
        if ( (ssl->error = SendBuffered(ssl)) < 0) {
            CYASSL_ERROR(ssl->error);
            if (ssl->error == SOCKET_ERROR_E && ssl->options.connReset)
                return 0;     /* peer reset */
            return ssl->error;
        }
        else {
            /* advance sent to previous sent + plain size just sent */
            sent = ssl->buffers.prevSent + ssl->buffers.plainSz;
            CYASSL_MSG("sent write buffered data");
        }
    }

#ifdef CYASSL_DTLS
    if (ssl->options.dtls) {
        dtlsExtra = DTLS_RECORD_EXTRA;
    }
#endif

    for (;;) {
#ifdef HAVE_MAX_FRAGMENT
        int   len = min(sz - sent, min(ssl->max_fragment, OUTPUT_RECORD_SIZE));
#else
        int   len = min(sz - sent, OUTPUT_RECORD_SIZE);
#endif
        byte* out;
        byte* sendBuffer = (byte*)data + sent;  /* may switch on comp */
        int   buffSz = len;                     /* may switch on comp */
        int   outputSz;
#ifdef HAVE_LIBZ
        byte  comp[MAX_RECORD_SIZE + MAX_COMP_EXTRA];
#endif

        if (sent == sz) break;

#ifdef CYASSL_DTLS
        if (ssl->options.dtls) {
            len    = min(len, MAX_UDP_SIZE);
            buffSz = len;
        }
#endif

        /* check for available size */
        outputSz = len + COMP_EXTRA + dtlsExtra + MAX_MSG_EXTRA;
        if ((ret = CheckAvailableSize(ssl, outputSz)) != 0)
            return ssl->error = ret;

        /* get ouput buffer */
        out = ssl->buffers.outputBuffer.buffer +
              ssl->buffers.outputBuffer.length;

#ifdef HAVE_LIBZ
        if (ssl->options.usingCompression) {
            buffSz = myCompress(ssl, sendBuffer, buffSz, comp, sizeof(comp));
            if (buffSz < 0) {
                return buffSz;
            }
            sendBuffer = comp;
        }
#endif
        sendSz = BuildMessage(ssl, out, outputSz, sendBuffer, buffSz,
                              application_data);
        if (sendSz < 0)
            return BUILD_MSG_ERROR;

        ssl->buffers.outputBuffer.length += sendSz;

        if ( (ret = SendBuffered(ssl)) < 0) {
            CYASSL_ERROR(ret);
            /* store for next call if WANT_WRITE or user embedSend() that
               doesn't present like WANT_WRITE */
            ssl->buffers.plainSz  = len;
            ssl->buffers.prevSent = sent;
            if (ret == SOCKET_ERROR_E && ssl->options.connReset)
                return 0;  /* peer reset */
            return ssl->error = ret;
        }

        sent += len;

        /* only one message per attempt */
        if (ssl->options.partialWrite == 1) {
            CYASSL_MSG("Paritial Write on, only sending one record");
            break;
        }
    }
 
    return sent;
}

/* process input data */
int ReceiveData(CYASSL* ssl, byte* output, int sz, int peek)
{
    int size;

    CYASSL_ENTER("ReceiveData()");

    if (ssl->error == WANT_READ)
        ssl->error = 0;

    if (ssl->error != 0 && ssl->error != WANT_WRITE) {
        CYASSL_MSG("User calling CyaSSL_read in error state, not allowed");
        return ssl->error;
    }

    if (ssl->options.handShakeState != HANDSHAKE_DONE) {
        int err;
        CYASSL_MSG("Handshake not complete, trying to finish");
        if ( (err = CyaSSL_negotiate(ssl)) != SSL_SUCCESS)
            return  err;
    }

    while (ssl->buffers.clearOutputBuffer.length == 0)
        if ( (ssl->error = ProcessReply(ssl)) < 0) {
            CYASSL_ERROR(ssl->error);
            if (ssl->error == ZERO_RETURN) {
                CYASSL_MSG("Zero return, no more data coming");
                return 0;         /* no more data coming */
            }
            if (ssl->error == SOCKET_ERROR_E) {
                if (ssl->options.connReset || ssl->options.isClosed) {
                    CYASSL_MSG("Peer reset or closed, connection done");
                    return 0;     /* peer reset or closed */
                }
            }
            return ssl->error;
        }

    if (sz < (int)ssl->buffers.clearOutputBuffer.length)
        size = sz;
    else
        size = ssl->buffers.clearOutputBuffer.length;

    XMEMCPY(output, ssl->buffers.clearOutputBuffer.buffer, size);

    if (peek == 0) {
        ssl->buffers.clearOutputBuffer.length -= size;
        ssl->buffers.clearOutputBuffer.buffer += size;
    }
   
    if (ssl->buffers.clearOutputBuffer.length == 0 && 
                                           ssl->buffers.inputBuffer.dynamicFlag)
       ShrinkInputBuffer(ssl, NO_FORCED_FREE);

    CYASSL_LEAVE("ReceiveData()", size);
    return size;
}


/* send alert message */
int SendAlert(CYASSL* ssl, int severity, int type)
{
    byte input[ALERT_SIZE];
    byte *output;
    int  sendSz;
    int  ret;
    int  outputSz;
    int  dtlsExtra = 0;

    /* if sendalert is called again for nonbloking */
    if (ssl->options.sendAlertState != 0) {
        ret = SendBuffered(ssl);
        if (ret == 0)
            ssl->options.sendAlertState = 0;
        return ret;
    }

   #ifdef CYASSL_DTLS
        if (ssl->options.dtls)
           dtlsExtra = DTLS_RECORD_EXTRA; 
   #endif

    /* check for available size */
    outputSz = ALERT_SIZE + MAX_MSG_EXTRA + dtlsExtra;
    if ((ret = CheckAvailableSize(ssl, outputSz)) != 0)
        return ret;

    /* get ouput buffer */
    output = ssl->buffers.outputBuffer.buffer +
             ssl->buffers.outputBuffer.length;

    input[0] = (byte)severity;
    input[1] = (byte)type;
    ssl->alert_history.last_tx.code = type;
    ssl->alert_history.last_tx.level = severity;
    if (severity == alert_fatal) {
        ssl->options.isClosed = 1;  /* Don't send close_notify */
    }

    /* only send encrypted alert if handshake actually complete, otherwise
       other side may not be able to handle it */
    if (ssl->keys.encryptionOn && ssl->options.handShakeState == HANDSHAKE_DONE)
        sendSz = BuildMessage(ssl, output, outputSz, input, ALERT_SIZE, alert);
    else {

        AddRecordHeader(output, ALERT_SIZE, alert, ssl);
        output += RECORD_HEADER_SZ;
        #ifdef CYASSL_DTLS
            if (ssl->options.dtls)
                output += DTLS_RECORD_EXTRA;
        #endif
        XMEMCPY(output, input, ALERT_SIZE);

        sendSz = RECORD_HEADER_SZ + ALERT_SIZE;
        #ifdef CYASSL_DTLS
            if (ssl->options.dtls)
                sendSz += DTLS_RECORD_EXTRA;
        #endif
    }
    if (sendSz < 0)
        return BUILD_MSG_ERROR;

    #ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn)
            AddPacketName("Alert", &ssl->handShakeInfo);
        if (ssl->toInfoOn)
            AddPacketInfo("Alert", &ssl->timeoutInfo, output, sendSz,ssl->heap);
    #endif

    ssl->buffers.outputBuffer.length += sendSz;
    ssl->options.sendAlertState = 1;

    return SendBuffered(ssl);
}

const char* CyaSSL_ERR_reason_error_string(unsigned long e)
{
#ifdef NO_ERROR_STRINGS

    (void)e;
    return "no support for error strings built in";

#else

    int error = (int)e;

    /* pass to CTaoCrypt */
    if (error < MAX_CODE_E && error > MIN_CODE_E) {
        return CTaoCryptGetErrorString(error);
    }

    switch (error) {

    case UNSUPPORTED_SUITE :
        return "unsupported cipher suite";

    case INPUT_CASE_ERROR :
        return "input state error";

    case PREFIX_ERROR :
        return "bad index to key rounds";

    case MEMORY_ERROR :
        return "out of memory";

    case VERIFY_FINISHED_ERROR :
        return "verify problem on finished";

    case VERIFY_MAC_ERROR :
        return "verify mac problem";

    case PARSE_ERROR :
        return "parse error on header";

    case SIDE_ERROR :
        return "wrong client/server type";

    case NO_PEER_CERT :
        return "peer didn't send cert";

    case UNKNOWN_HANDSHAKE_TYPE :
        return "weird handshake type";

    case SOCKET_ERROR_E :
        return "error state on socket";

    case SOCKET_NODATA :
        return "expected data, not there";

    case INCOMPLETE_DATA :
        return "don't have enough data to complete task";

    case UNKNOWN_RECORD_TYPE :
        return "unknown type in record hdr";

    case DECRYPT_ERROR :
        return "error during decryption";

    case FATAL_ERROR :
        return "revcd alert fatal error";

    case ENCRYPT_ERROR :
        return "error during encryption";

    case FREAD_ERROR :
        return "fread problem";

    case NO_PEER_KEY :
        return "need peer's key";

    case NO_PRIVATE_KEY :
        return "need the private key";

    case NO_DH_PARAMS :
        return "server missing DH params";

    case RSA_PRIVATE_ERROR :
        return "error during rsa priv op";

    case MATCH_SUITE_ERROR :
        return "can't match cipher suite";

    case BUILD_MSG_ERROR :
        return "build message failure";

    case BAD_HELLO :
        return "client hello malformed";

    case DOMAIN_NAME_MISMATCH :
        return "peer subject name mismatch";

    case WANT_READ :
    case SSL_ERROR_WANT_READ :
        return "non-blocking socket wants data to be read";

    case NOT_READY_ERROR :
        return "handshake layer not ready yet, complete first";

    case PMS_VERSION_ERROR :
        return "premaster secret version mismatch error";

    case VERSION_ERROR :
        return "record layer version error";

    case WANT_WRITE :
    case SSL_ERROR_WANT_WRITE :
        return "non-blocking socket write buffer full";

    case BUFFER_ERROR :
        return "malformed buffer input error";

    case VERIFY_CERT_ERROR :
        return "verify problem on certificate";

    case VERIFY_SIGN_ERROR :
        return "verify problem based on signature";

    case CLIENT_ID_ERROR :
        return "psk client identity error";

    case SERVER_HINT_ERROR:
        return "psk server hint error";

    case PSK_KEY_ERROR:
        return "psk key callback error";

    case NTRU_KEY_ERROR:
        return "NTRU key error";

    case NTRU_DRBG_ERROR:
        return "NTRU drbg error";

    case NTRU_ENCRYPT_ERROR:
        return "NTRU encrypt error";

    case NTRU_DECRYPT_ERROR:
        return "NTRU decrypt error";

    case ZLIB_INIT_ERROR:
        return "zlib init error";

    case ZLIB_COMPRESS_ERROR:
        return "zlib compress error";

    case ZLIB_DECOMPRESS_ERROR:
        return "zlib decompress error";

    case GETTIME_ERROR:
        return "gettimeofday() error";

    case GETITIMER_ERROR:
        return "getitimer() error";

    case SIGACT_ERROR:
        return "sigaction() error";

    case SETITIMER_ERROR:
        return "setitimer() error";

    case LENGTH_ERROR:
        return "record layer length error";

    case PEER_KEY_ERROR:
        return "cant decode peer key";

    case ZERO_RETURN:
    case SSL_ERROR_ZERO_RETURN:
        return "peer sent close notify alert";

    case ECC_CURVETYPE_ERROR:
        return "Bad ECC Curve Type or unsupported";

    case ECC_CURVE_ERROR:
        return "Bad ECC Curve or unsupported";

    case ECC_PEERKEY_ERROR:
        return "Bad ECC Peer Key";

    case ECC_MAKEKEY_ERROR:
        return "ECC Make Key failure";

    case ECC_EXPORT_ERROR:
        return "ECC Export Key failure";

    case ECC_SHARED_ERROR:
        return "ECC DHE shared failure";

    case NOT_CA_ERROR:
        return "Not a CA by basic constraint error";

    case BAD_PATH_ERROR:
        return "Bad path for opendir error";

    case BAD_CERT_MANAGER_ERROR:
        return "Bad Cert Manager error";

    case OCSP_CERT_REVOKED:
        return "OCSP Cert revoked";

    case CRL_CERT_REVOKED:
        return "CRL Cert revoked";

    case CRL_MISSING:
        return "CRL missing, not loaded";

    case MONITOR_RUNNING_E:
        return "CRL monitor already running";

    case THREAD_CREATE_E:
        return "Thread creation problem";

    case OCSP_NEED_URL:
        return "OCSP need URL";

    case OCSP_CERT_UNKNOWN:
        return "OCSP Cert unknown";

    case OCSP_LOOKUP_FAIL:
        return "OCSP Responder lookup fail";

    case MAX_CHAIN_ERROR:
        return "Maximum Chain Depth Exceeded";

    case COOKIE_ERROR:
        return "DTLS Cookie Error";

    case SEQUENCE_ERROR:
        return "DTLS Sequence Error";

    case SUITES_ERROR:
        return "Suites Pointer Error";

    case SSL_NO_PEM_HEADER:
        return "No PEM Header Error";

    case OUT_OF_ORDER_E:
        return "Out of order message, fatal";

    case BAD_KEA_TYPE_E:
        return "Bad KEA type found";

    case SANITY_CIPHER_E:
        return "Sanity check on ciphertext failed";

    case RECV_OVERFLOW_E:
        return "Receive callback returned more than requested";

    case GEN_COOKIE_E:
        return "Generate Cookie Error";

    case NO_PEER_VERIFY:
        return "Need peer certificate verify Error";

    case FWRITE_ERROR:
        return "fwrite Error";

    case CACHE_MATCH_ERROR:
        return "Cache restore header match Error";

    case UNKNOWN_SNI_HOST_NAME_E:
        return "Unrecognized host name Error";

    case KEYUSE_SIGNATURE_E:
        return "Key Use digitalSignature not set Error";

    case KEYUSE_ENCIPHER_E:
        return "Key Use keyEncipherment not set Error";

    case EXTKEYUSE_AUTH_E:
        return "Ext Key Use server/client auth not set Error";

    case SEND_OOB_READ_E:
        return "Send Callback Out of Bounds Read Error";

    default :
        return "unknown error number";
    }

#endif /* NO_ERROR_STRINGS */
}

void SetErrorString(int error, char* str)
{
    XSTRNCPY(str, CyaSSL_ERR_reason_error_string(error), CYASSL_MAX_ERROR_SZ);
}


/* be sure to add to cipher_name_idx too !!!! */
static const char* const cipher_names[] = 
{
#ifdef BUILD_SSL_RSA_WITH_RC4_128_SHA
    "RC4-SHA",
#endif

#ifdef BUILD_SSL_RSA_WITH_RC4_128_MD5
    "RC4-MD5",
#endif

#ifdef BUILD_SSL_RSA_WITH_3DES_EDE_CBC_SHA
    "DES-CBC3-SHA",
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_CBC_SHA
    "AES128-SHA",
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_CBC_SHA
    "AES256-SHA",
#endif

#ifdef BUILD_TLS_RSA_WITH_NULL_SHA
    "NULL-SHA",
#endif

#ifdef BUILD_TLS_RSA_WITH_NULL_SHA256
    "NULL-SHA256",
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_128_CBC_SHA
    "DHE-RSA-AES128-SHA",
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_256_CBC_SHA
    "DHE-RSA-AES256-SHA",
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_256_GCM_SHA384
    "DHE-PSK-AES256-GCM-SHA384",
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_128_GCM_SHA256
    "DHE-PSK-AES128-GCM-SHA256",
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_GCM_SHA384
    "PSK-AES256-GCM-SHA384",
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_GCM_SHA256
    "PSK-AES128-GCM-SHA256",
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_256_CBC_SHA384
    "DHE-PSK-AES256-CBC-SHA384",
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_128_CBC_SHA256
    "DHE-PSK-AES128-CBC-SHA256",
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_CBC_SHA384
    "PSK-AES256-CBC-SHA384",
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CBC_SHA256
    "PSK-AES128-CBC-SHA256",
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CBC_SHA
    "PSK-AES128-CBC-SHA",
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_CBC_SHA
    "PSK-AES256-CBC-SHA",
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_128_CCM
    "DHE-PSK-AES128-CCM",
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_256_CCM
    "DHE-PSK-AES256-CCM",
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CCM
    "PSK-AES128-CCM",
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_CCM
    "PSK-AES256-CCM",
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CCM_8
    "PSK-AES128-CCM-8",
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_CCM_8
    "PSK-AES256-CCM-8",
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_NULL_SHA384
    "DHE-PSK-NULL-SHA384",
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_NULL_SHA256
    "DHE-PSK-NULL-SHA256",
#endif

#ifdef BUILD_TLS_PSK_WITH_NULL_SHA384
    "PSK-NULL-SHA384",
#endif

#ifdef BUILD_TLS_PSK_WITH_NULL_SHA256
    "PSK-NULL-SHA256",
#endif

#ifdef BUILD_TLS_PSK_WITH_NULL_SHA
    "PSK-NULL-SHA",
#endif

#ifdef BUILD_TLS_RSA_WITH_HC_128_MD5
    "HC128-MD5",
#endif
    
#ifdef BUILD_TLS_RSA_WITH_HC_128_SHA
    "HC128-SHA",
#endif

#ifdef BUILD_TLS_RSA_WITH_HC_128_B2B256
    "HC128-B2B256",
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_CBC_B2B256
    "AES128-B2B256",
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_CBC_B2B256
    "AES256-B2B256",
#endif

#ifdef BUILD_TLS_RSA_WITH_RABBIT_SHA
    "RABBIT-SHA",
#endif

#ifdef BUILD_TLS_NTRU_RSA_WITH_RC4_128_SHA
    "NTRU-RC4-SHA",
#endif

#ifdef BUILD_TLS_NTRU_RSA_WITH_3DES_EDE_CBC_SHA
    "NTRU-DES-CBC3-SHA",
#endif

#ifdef BUILD_TLS_NTRU_RSA_WITH_AES_128_CBC_SHA
    "NTRU-AES128-SHA",
#endif

#ifdef BUILD_TLS_NTRU_RSA_WITH_AES_256_CBC_SHA
    "NTRU-AES256-SHA",
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_CCM_8
    "AES128-CCM-8",
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_CCM_8
    "AES256-CCM-8",
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CCM_8
    "ECDHE-ECDSA-AES128-CCM-8",
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CCM_8
    "ECDHE-ECDSA-AES256-CCM-8",
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA
    "ECDHE-RSA-AES128-SHA",
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA
    "ECDHE-RSA-AES256-SHA",
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA
    "ECDHE-ECDSA-AES128-SHA",
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA
    "ECDHE-ECDSA-AES256-SHA",
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_RC4_128_SHA
    "ECDHE-RSA-RC4-SHA",
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA
    "ECDHE-RSA-DES-CBC3-SHA",
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_RC4_128_SHA
    "ECDHE-ECDSA-RC4-SHA",
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA
    "ECDHE-ECDSA-DES-CBC3-SHA",
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_CBC_SHA256
    "AES128-SHA256",
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_CBC_SHA256
    "AES256-SHA256",
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_128_CBC_SHA256
    "DHE-RSA-AES128-SHA256",
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_256_CBC_SHA256
    "DHE-RSA-AES256-SHA256",
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_128_CBC_SHA
    "ECDH-RSA-AES128-SHA",
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_256_CBC_SHA
    "ECDH-RSA-AES256-SHA",
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA
    "ECDH-ECDSA-AES128-SHA",
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA
    "ECDH-ECDSA-AES256-SHA",
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_RC4_128_SHA
    "ECDH-RSA-RC4-SHA",
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA
    "ECDH-RSA-DES-CBC3-SHA",
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_RC4_128_SHA
    "ECDH-ECDSA-RC4-SHA",
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA
    "ECDH-ECDSA-DES-CBC3-SHA",
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_GCM_SHA256
    "AES128-GCM-SHA256",
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_GCM_SHA384
    "AES256-GCM-SHA384",
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_128_GCM_SHA256
    "DHE-RSA-AES128-GCM-SHA256",
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_256_GCM_SHA384
    "DHE-RSA-AES256-GCM-SHA384",
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
    "ECDHE-RSA-AES128-GCM-SHA256",
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384
    "ECDHE-RSA-AES256-GCM-SHA384",
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256
    "ECDHE-ECDSA-AES128-GCM-SHA256",
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384
    "ECDHE-ECDSA-AES256-GCM-SHA384",
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_128_GCM_SHA256
    "ECDH-RSA-AES128-GCM-SHA256",
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_256_GCM_SHA384
    "ECDH-RSA-AES256-GCM-SHA384",
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_128_GCM_SHA256
    "ECDH-ECDSA-AES128-GCM-SHA256",
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_256_GCM_SHA384
    "ECDH-ECDSA-AES256-GCM-SHA384",
#endif

#ifdef BUILD_TLS_RSA_WITH_CAMELLIA_128_CBC_SHA
    "CAMELLIA128-SHA",
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA
    "DHE-RSA-CAMELLIA128-SHA",
#endif

#ifdef BUILD_TLS_RSA_WITH_CAMELLIA_256_CBC_SHA
    "CAMELLIA256-SHA",
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA
    "DHE-RSA-CAMELLIA256-SHA",
#endif

#ifdef BUILD_TLS_RSA_WITH_CAMELLIA_128_CBC_SHA256
    "CAMELLIA128-SHA256",
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA256
    "DHE-RSA-CAMELLIA128-SHA256",
#endif

#ifdef BUILD_TLS_RSA_WITH_CAMELLIA_256_CBC_SHA256
    "CAMELLIA256-SHA256",
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA256
    "DHE-RSA-CAMELLIA256-SHA256",
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256
    "ECDHE-RSA-AES128-SHA256",
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256
    "ECDHE-ECDSA-AES128-SHA256",
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_128_CBC_SHA256
    "ECDH-RSA-AES128-SHA256",
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA256
    "ECDH-ECDSA-AES128-SHA256",
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384
    "ECDHE-RSA-AES256-SHA384",
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA384
    "ECDHE-ECDSA-AES256-SHA384",
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_256_CBC_SHA384
    "ECDH-RSA-AES256-SHA384",
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA384
    "ECDH-ECDSA-AES256-SHA384",
#endif

};



/* cipher suite number that matches above name table */
static int cipher_name_idx[] =
{

#ifdef BUILD_SSL_RSA_WITH_RC4_128_SHA
    SSL_RSA_WITH_RC4_128_SHA,
#endif

#ifdef BUILD_SSL_RSA_WITH_RC4_128_MD5
    SSL_RSA_WITH_RC4_128_MD5,
#endif

#ifdef BUILD_SSL_RSA_WITH_3DES_EDE_CBC_SHA
    SSL_RSA_WITH_3DES_EDE_CBC_SHA,
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_CBC_SHA
    TLS_RSA_WITH_AES_128_CBC_SHA,    
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_CBC_SHA
    TLS_RSA_WITH_AES_256_CBC_SHA,
#endif

#ifdef BUILD_TLS_RSA_WITH_NULL_SHA
    TLS_RSA_WITH_NULL_SHA,
#endif

#ifdef BUILD_TLS_RSA_WITH_NULL_SHA256
    TLS_RSA_WITH_NULL_SHA256,
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_128_CBC_SHA
    TLS_DHE_RSA_WITH_AES_128_CBC_SHA,    
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_256_CBC_SHA
    TLS_DHE_RSA_WITH_AES_256_CBC_SHA,
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_256_GCM_SHA384
    TLS_DHE_PSK_WITH_AES_256_GCM_SHA384,
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_128_GCM_SHA256
    TLS_DHE_PSK_WITH_AES_128_GCM_SHA256,
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_GCM_SHA384
    TLS_PSK_WITH_AES_256_GCM_SHA384,
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_GCM_SHA256
    TLS_PSK_WITH_AES_128_GCM_SHA256,
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_256_CBC_SHA384
    TLS_DHE_PSK_WITH_AES_256_CBC_SHA384,
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_128_CBC_SHA256
    TLS_DHE_PSK_WITH_AES_128_CBC_SHA256,
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_CBC_SHA384
    TLS_PSK_WITH_AES_256_CBC_SHA384,
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CBC_SHA256
    TLS_PSK_WITH_AES_128_CBC_SHA256,    
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CBC_SHA
    TLS_PSK_WITH_AES_128_CBC_SHA,    
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_CBC_SHA
    TLS_PSK_WITH_AES_256_CBC_SHA,
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_128_CCM
    TLS_DHE_PSK_WITH_AES_128_CCM,
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_AES_256_CCM
    TLS_DHE_PSK_WITH_AES_256_CCM,
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CCM
    TLS_PSK_WITH_AES_128_CCM,
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_CCM
    TLS_PSK_WITH_AES_256_CCM,
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CCM_8
    TLS_PSK_WITH_AES_128_CCM_8,
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_CCM_8
    TLS_PSK_WITH_AES_256_CCM_8,
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_NULL_SHA384
    TLS_DHE_PSK_WITH_NULL_SHA384,
#endif

#ifdef BUILD_TLS_DHE_PSK_WITH_NULL_SHA256
    TLS_DHE_PSK_WITH_NULL_SHA256,
#endif

#ifdef BUILD_TLS_PSK_WITH_NULL_SHA384
    TLS_PSK_WITH_NULL_SHA384,
#endif

#ifdef BUILD_TLS_PSK_WITH_NULL_SHA256
    TLS_PSK_WITH_NULL_SHA256,
#endif

#ifdef BUILD_TLS_PSK_WITH_NULL_SHA
    TLS_PSK_WITH_NULL_SHA,
#endif

#ifdef BUILD_TLS_RSA_WITH_HC_128_MD5
    TLS_RSA_WITH_HC_128_MD5,    
#endif

#ifdef BUILD_TLS_RSA_WITH_HC_128_SHA
    TLS_RSA_WITH_HC_128_SHA,    
#endif

#ifdef BUILD_TLS_RSA_WITH_HC_128_B2B256
    TLS_RSA_WITH_HC_128_B2B256,
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_CBC_B2B256
    TLS_RSA_WITH_AES_128_CBC_B2B256,
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_CBC_B2B256
    TLS_RSA_WITH_AES_256_CBC_B2B256,
#endif

#ifdef BUILD_TLS_RSA_WITH_RABBIT_SHA
    TLS_RSA_WITH_RABBIT_SHA,    
#endif

#ifdef BUILD_TLS_NTRU_RSA_WITH_RC4_128_SHA
    TLS_NTRU_RSA_WITH_RC4_128_SHA,
#endif

#ifdef BUILD_TLS_NTRU_RSA_WITH_3DES_EDE_CBC_SHA
    TLS_NTRU_RSA_WITH_3DES_EDE_CBC_SHA,
#endif

#ifdef BUILD_TLS_NTRU_RSA_WITH_AES_128_CBC_SHA
    TLS_NTRU_RSA_WITH_AES_128_CBC_SHA,    
#endif

#ifdef BUILD_TLS_NTRU_RSA_WITH_AES_256_CBC_SHA
    TLS_NTRU_RSA_WITH_AES_256_CBC_SHA,    
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_CCM_8
    TLS_RSA_WITH_AES_128_CCM_8,
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_CCM_8
    TLS_RSA_WITH_AES_256_CCM_8,
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CCM_8
    TLS_ECDHE_ECDSA_WITH_AES_128_CCM_8,
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CCM_8
    TLS_ECDHE_ECDSA_WITH_AES_256_CCM_8,
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA
    TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA,    
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA
    TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA,
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA
    TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA,    
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA
    TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA,
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_RC4_128_SHA
    TLS_ECDHE_RSA_WITH_RC4_128_SHA,    
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA
    TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA,    
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_RC4_128_SHA
    TLS_ECDHE_ECDSA_WITH_RC4_128_SHA,    
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA
    TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA,    
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_CBC_SHA256
    TLS_RSA_WITH_AES_128_CBC_SHA256,    
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_CBC_SHA256
    TLS_RSA_WITH_AES_256_CBC_SHA256,
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_128_CBC_SHA256
    TLS_DHE_RSA_WITH_AES_128_CBC_SHA256,    
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_256_CBC_SHA256
    TLS_DHE_RSA_WITH_AES_256_CBC_SHA256,
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_128_CBC_SHA
    TLS_ECDH_RSA_WITH_AES_128_CBC_SHA,
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_256_CBC_SHA
    TLS_ECDH_RSA_WITH_AES_256_CBC_SHA,
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA
    TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA,
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA
    TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA,
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_RC4_128_SHA
    TLS_ECDH_RSA_WITH_RC4_128_SHA,
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA
    TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA,
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_RC4_128_SHA
    TLS_ECDH_ECDSA_WITH_RC4_128_SHA,
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA
    TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA,
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_128_GCM_SHA256
    TLS_RSA_WITH_AES_128_GCM_SHA256,
#endif

#ifdef BUILD_TLS_RSA_WITH_AES_256_GCM_SHA384
    TLS_RSA_WITH_AES_256_GCM_SHA384,
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_128_GCM_SHA256
    TLS_DHE_RSA_WITH_AES_128_GCM_SHA256,
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_256_GCM_SHA384
    TLS_DHE_RSA_WITH_AES_256_GCM_SHA384,
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
    TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256,
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384
    TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384,
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256
    TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256,
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384
    TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384,
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_128_GCM_SHA256
    TLS_ECDH_RSA_WITH_AES_128_GCM_SHA256,
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_256_GCM_SHA384
    TLS_ECDH_RSA_WITH_AES_256_GCM_SHA384,
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_128_GCM_SHA256
    TLS_ECDH_ECDSA_WITH_AES_128_GCM_SHA256,
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_256_GCM_SHA384
    TLS_ECDH_ECDSA_WITH_AES_256_GCM_SHA384,
#endif

#ifdef BUILD_TLS_RSA_WITH_CAMELLIA_128_CBC_SHA
    TLS_RSA_WITH_CAMELLIA_128_CBC_SHA,
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA
    TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA,
#endif

#ifdef BUILD_TLS_RSA_WITH_CAMELLIA_256_CBC_SHA
    TLS_RSA_WITH_CAMELLIA_256_CBC_SHA,
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA
    TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA,
#endif

#ifdef BUILD_TLS_RSA_WITH_CAMELLIA_128_CBC_SHA256
    TLS_RSA_WITH_CAMELLIA_128_CBC_SHA256,
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA256
    TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA256,
#endif

#ifdef BUILD_TLS_RSA_WITH_CAMELLIA_256_CBC_SHA256
    TLS_RSA_WITH_CAMELLIA_256_CBC_SHA256,
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA256
    TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA256,
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256
    TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256,
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256
    TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256,
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_128_CBC_SHA256
    TLS_ECDH_RSA_WITH_AES_128_CBC_SHA256,
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA256
    TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA256,
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384
    TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384,
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA384
    TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA384,
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_256_CBC_SHA384
    TLS_ECDH_RSA_WITH_AES_256_CBC_SHA384,
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA384
    TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA384
#endif
};


/* return true if set, else false */
/* only supports full name from cipher_name[] delimited by : */
int SetCipherList(Suites* s, const char* list)
{
    int  ret = 0, i;
    char name[MAX_SUITE_NAME];

    char  needle[] = ":";
    char* haystack = (char*)list;
    char* prev;

    const int suiteSz = sizeof(cipher_names) / sizeof(cipher_names[0]);
    int idx = 0;
    int haveRSA = 0, haveECDSA = 0;

    if (s == NULL) {
        CYASSL_MSG("SetCipherList suite pointer error");
        return 0;    
    }

    if (!list)
        return 0;
    
    if (*list == 0) return 1;   /* CyaSSL default */

    if (XSTRNCMP(haystack, "ALL", 3) == 0) return 1;  /* CyaSSL defualt */

    for(;;) {
        word32 len;
        prev = haystack;
        haystack = XSTRSTR(haystack, needle);

        if (!haystack)    /* last cipher */
            len = min(sizeof(name), (word32)XSTRLEN(prev));
        else
            len = min(sizeof(name), (word32)(haystack - prev));

        XSTRNCPY(name, prev, len);
        name[(len == sizeof(name)) ? len - 1 : len] = 0;

        for (i = 0; i < suiteSz; i++)
            if (XSTRNCMP(name, cipher_names[i], sizeof(name)) == 0) {
                if (XSTRSTR(name, "EC") || XSTRSTR(name, "CCM"))
                    s->suites[idx++] = ECC_BYTE;  /* ECC suite */
                else
                    s->suites[idx++] = 0x00;      /* normal */
                s->suites[idx++] = (byte)cipher_name_idx[i];

                /* The suites are either ECDSA, RSA, or PSK. The RSA suites
                 * don't necessarily have RSA in the name. */
                if ((haveECDSA == 0) && XSTRSTR(name, "ECDSA")) {
                    haveECDSA = 1;
                }
                else if ((haveRSA == 0) && (XSTRSTR(name, "PSK") == NULL)) {
                    haveRSA = 1;
                }

                if (!ret) ret = 1;   /* found at least one */
                break;
            }
        if (!haystack) break;
        haystack++;
    }

    if (ret) {
        s->setSuites = 1;
        s->suiteSz   = (word16)idx;

        idx = 0;
        
        if (haveECDSA) {
            #ifdef CYASSL_SHA384
                s->hashSigAlgo[idx++] = sha384_mac;
                s->hashSigAlgo[idx++] = ecc_dsa_sa_algo;
            #endif
            #ifndef NO_SHA256
                s->hashSigAlgo[idx++] = sha256_mac;
                s->hashSigAlgo[idx++] = ecc_dsa_sa_algo;
            #endif
            s->hashSigAlgo[idx++] = sha_mac;
            s->hashSigAlgo[idx++] = ecc_dsa_sa_algo;
        }

        if (haveRSA) {
            #ifdef CYASSL_SHA384
                s->hashSigAlgo[idx++] = sha384_mac;
                s->hashSigAlgo[idx++] = rsa_sa_algo;
            #endif
            #ifndef NO_SHA256
                s->hashSigAlgo[idx++] = sha256_mac;
                s->hashSigAlgo[idx++] = rsa_sa_algo;
            #endif
            s->hashSigAlgo[idx++] = sha_mac;
            s->hashSigAlgo[idx++] = rsa_sa_algo;
        }

        s->hashSigAlgoSz = (word16)idx;
    }

    return ret;
}


static void PickHashSigAlgo(CYASSL* ssl,
                             const byte* hashSigAlgo, word32 hashSigAlgoSz)
{
    word32 i;

    ssl->suites->sigAlgo = ssl->specs.sig_algo;
    ssl->suites->hashAlgo = sha_mac;

    for (i = 0; i < hashSigAlgoSz; i += 2) {
        if (hashSigAlgo[i+1] == ssl->specs.sig_algo) {
            if (hashSigAlgo[i] == sha_mac) {
                break;
            }
            #ifndef NO_SHA256
            else if (hashSigAlgo[i] == sha256_mac) {
                ssl->suites->hashAlgo = sha256_mac;
                break;
            }
            #endif
            #ifdef CYASSL_SHA384
            else if (hashSigAlgo[i] == sha384_mac) {
                ssl->suites->hashAlgo = sha384_mac;
                break;
            }
            #endif
        }
    }
}


#ifdef CYASSL_CALLBACKS

    /* Initialisze HandShakeInfo */
    void InitHandShakeInfo(HandShakeInfo* info)
    {
        int i;

        info->cipherName[0] = 0;
        for (i = 0; i < MAX_PACKETS_HANDSHAKE; i++)
            info->packetNames[i][0] = 0;
        info->numberPackets = 0;
        info->negotiationError = 0;
    }

    /* Set Final HandShakeInfo parameters */
    void FinishHandShakeInfo(HandShakeInfo* info, const CYASSL* ssl)
    {
        int i;
        int sz = sizeof(cipher_name_idx)/sizeof(int); 

        for (i = 0; i < sz; i++)
            if (ssl->options.cipherSuite == (byte)cipher_name_idx[i]) {
                if (ssl->options.cipherSuite0 == ECC_BYTE)
                    continue;   /* ECC suites at end */
                XSTRNCPY(info->cipherName, cipher_names[i], MAX_CIPHERNAME_SZ);
                break;
            }

        /* error max and min are negative numbers */
        if (ssl->error <= MIN_PARAM_ERR && ssl->error >= MAX_PARAM_ERR)
            info->negotiationError = ssl->error;
    }

   
    /* Add name to info packet names, increase packet name count */
    void AddPacketName(const char* name, HandShakeInfo* info)
    {
        if (info->numberPackets < MAX_PACKETS_HANDSHAKE) {
            XSTRNCPY(info->packetNames[info->numberPackets++], name,
                    MAX_PACKETNAME_SZ);
        }
    } 


    /* Initialisze TimeoutInfo */
    void InitTimeoutInfo(TimeoutInfo* info)
    {
        int i;

        info->timeoutName[0] = 0;
        info->flags          = 0;

        for (i = 0; i < MAX_PACKETS_HANDSHAKE; i++) {
            info->packets[i].packetName[0]     = 0;
            info->packets[i].timestamp.tv_sec  = 0;
            info->packets[i].timestamp.tv_usec = 0;
            info->packets[i].bufferValue       = 0;
            info->packets[i].valueSz           = 0;
        }
        info->numberPackets        = 0;
        info->timeoutValue.tv_sec  = 0;
        info->timeoutValue.tv_usec = 0;
    }


    /* Free TimeoutInfo */
    void FreeTimeoutInfo(TimeoutInfo* info, void* heap)
    {
        int i;
        (void)heap;
        for (i = 0; i < MAX_PACKETS_HANDSHAKE; i++)
            if (info->packets[i].bufferValue) {
                XFREE(info->packets[i].bufferValue, heap, DYNAMIC_TYPE_INFO);
                info->packets[i].bufferValue = 0;
            }

    }


    /* Add PacketInfo to TimeoutInfo */
    void AddPacketInfo(const char* name, TimeoutInfo* info, const byte* data,
                       int sz, void* heap)
    {
        if (info->numberPackets < (MAX_PACKETS_HANDSHAKE - 1)) {
            Timeval currTime;

            /* may add name after */
            if (name)
                XSTRNCPY(info->packets[info->numberPackets].packetName, name,
                        MAX_PACKETNAME_SZ);

            /* add data, put in buffer if bigger than static buffer */
            info->packets[info->numberPackets].valueSz = sz;
            if (sz < MAX_VALUE_SZ)
                XMEMCPY(info->packets[info->numberPackets].value, data, sz);
            else {
                info->packets[info->numberPackets].bufferValue =
                           XMALLOC(sz, heap, DYNAMIC_TYPE_INFO);
                if (!info->packets[info->numberPackets].bufferValue)
                    /* let next alloc catch, just don't fill, not fatal here  */
                    info->packets[info->numberPackets].valueSz = 0;
                else
                    XMEMCPY(info->packets[info->numberPackets].bufferValue,
                           data, sz);
            }
            gettimeofday(&currTime, 0);
            info->packets[info->numberPackets].timestamp.tv_sec  =
                                                             currTime.tv_sec;
            info->packets[info->numberPackets].timestamp.tv_usec =
                                                             currTime.tv_usec;
            info->numberPackets++;
        }
    }


    /* Add packet name to previsouly added packet info */
    void AddLateName(const char* name, TimeoutInfo* info)
    {
        /* make sure we have a valid previous one */
        if (info->numberPackets > 0 && info->numberPackets <
                                                        MAX_PACKETS_HANDSHAKE) {
            XSTRNCPY(info->packets[info->numberPackets - 1].packetName, name,
                    MAX_PACKETNAME_SZ);
        }
    }

    /* Add record header to previsouly added packet info */
    void AddLateRecordHeader(const RecordLayerHeader* rl, TimeoutInfo* info)
    {
        /* make sure we have a valid previous one */
        if (info->numberPackets > 0 && info->numberPackets <
                                                        MAX_PACKETS_HANDSHAKE) {
            if (info->packets[info->numberPackets - 1].bufferValue)
                XMEMCPY(info->packets[info->numberPackets - 1].bufferValue, rl,
                       RECORD_HEADER_SZ);
            else
                XMEMCPY(info->packets[info->numberPackets - 1].value, rl,
                       RECORD_HEADER_SZ);
        }
    }

#endif /* CYASSL_CALLBACKS */



/* client only parts */
#ifndef NO_CYASSL_CLIENT

    int SendClientHello(CYASSL* ssl)
    {
        byte              *output;
        word32             length, idx = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
        int                sendSz;
        int                idSz = ssl->options.resuming ? ID_LEN : 0;
        int                ret;

        if (ssl->suites == NULL) {
            CYASSL_MSG("Bad suites pointer in SendClientHello");
            return SUITES_ERROR;
        } 

        length = VERSION_SZ + RAN_LEN
               + idSz + ENUM_LEN                      
               + ssl->suites->suiteSz + SUITE_LEN
               + COMP_LEN + ENUM_LEN;

#ifdef HAVE_TLS_EXTENSIONS
        length += TLSX_GetRequestSize(ssl);
#else
        if (IsAtLeastTLSv1_2(ssl) && ssl->suites->hashSigAlgoSz) {
            length += ssl->suites->hashSigAlgoSz + HELLO_EXT_SZ;
        }
#endif
        sendSz = length + HANDSHAKE_HEADER_SZ + RECORD_HEADER_SZ;

#ifdef CYASSL_DTLS
        if (ssl->options.dtls) {
            length += ENUM_LEN;   /* cookie */
            if (ssl->arrays->cookieSz != 0) length += ssl->arrays->cookieSz;
            sendSz  = length + DTLS_HANDSHAKE_HEADER_SZ + DTLS_RECORD_HEADER_SZ;
            idx    += DTLS_HANDSHAKE_EXTRA + DTLS_RECORD_EXTRA;
        }
#endif

        /* check for available size */
        if ((ret = CheckAvailableSize(ssl, sendSz)) != 0)
            return ret;

        /* get ouput buffer */
        output = ssl->buffers.outputBuffer.buffer +
                 ssl->buffers.outputBuffer.length;

        AddHeaders(output, length, client_hello, ssl);

            /* client hello, first version */
        output[idx++] = ssl->version.major;
        output[idx++] = ssl->version.minor;
        ssl->chVersion = ssl->version;  /* store in case changed */

            /* then random */
        if (ssl->options.connectState == CONNECT_BEGIN) {
            ret = RNG_GenerateBlock(ssl->rng, output + idx, RAN_LEN);
            if (ret != 0)
                return ret;
            
                /* store random */
            XMEMCPY(ssl->arrays->clientRandom, output + idx, RAN_LEN);
        } else {
#ifdef CYASSL_DTLS
                /* send same random on hello again */
            XMEMCPY(output + idx, ssl->arrays->clientRandom, RAN_LEN);
#endif
        }
        idx += RAN_LEN;

            /* then session id */
        output[idx++] = (byte)idSz;
        if (idSz) {
            XMEMCPY(output + idx, ssl->session.sessionID, ID_LEN);
            idx += ID_LEN;
        }
        
            /* then DTLS cookie */
#ifdef CYASSL_DTLS
        if (ssl->options.dtls) {
            byte cookieSz = ssl->arrays->cookieSz;

            output[idx++] = cookieSz;
            if (cookieSz) {
                XMEMCPY(&output[idx], ssl->arrays->cookie, cookieSz);
                idx += cookieSz;
            }
        }
#endif
            /* then cipher suites */
        c16toa(ssl->suites->suiteSz, output + idx);
        idx += 2;
        XMEMCPY(output + idx, &ssl->suites->suites, ssl->suites->suiteSz);
        idx += ssl->suites->suiteSz;

            /* last, compression */
        output[idx++] = COMP_LEN;
        if (ssl->options.usingCompression)
            output[idx++] = ZLIB_COMPRESSION;
        else
            output[idx++] = NO_COMPRESSION;

#ifdef HAVE_TLS_EXTENSIONS
        idx += TLSX_WriteRequest(ssl, output + idx);

        (void)idx; /* suppress analyzer warning, keep idx current */
#else
        if (IsAtLeastTLSv1_2(ssl) && ssl->suites->hashSigAlgoSz)
        {
            int i;
            /* add in the extensions length */
            c16toa(HELLO_EXT_LEN + ssl->suites->hashSigAlgoSz, output + idx);
            idx += 2;

            c16toa(HELLO_EXT_SIG_ALGO, output + idx);
            idx += 2;
            c16toa(HELLO_EXT_SIGALGO_SZ+ssl->suites->hashSigAlgoSz, output+idx);
            idx += 2;
            c16toa(ssl->suites->hashSigAlgoSz, output + idx);
            idx += 2;
            for (i = 0; i < ssl->suites->hashSigAlgoSz; i++, idx++) {
                output[idx] = ssl->suites->hashSigAlgo[i];
            }
        }
#endif

        #ifdef CYASSL_DTLS
            if (ssl->options.dtls) {
                if ((ret = DtlsPoolSave(ssl, output, sendSz)) != 0)
                    return ret;
            }
        #endif

        ret = HashOutput(ssl, output, sendSz, 0);
        if (ret != 0)
            return ret;

        ssl->options.clientState = CLIENT_HELLO_COMPLETE;

#ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn) AddPacketName("ClientHello", &ssl->handShakeInfo);
        if (ssl->toInfoOn)
            AddPacketInfo("ClientHello", &ssl->timeoutInfo, output, sendSz,
                          ssl->heap);
#endif

        ssl->buffers.outputBuffer.length += sendSz;

        return SendBuffered(ssl);
    }


    static int DoHelloVerifyRequest(CYASSL* ssl, const byte* input,
                                    word32* inOutIdx, word32 size)
    {
        ProtocolVersion pv;
        byte            cookieSz;
        word32          begin = *inOutIdx;
        
#ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn) AddPacketName("HelloVerifyRequest",
                                         &ssl->handShakeInfo);
        if (ssl->toInfoOn) AddLateName("HelloVerifyRequest", &ssl->timeoutInfo);
#endif

#ifdef CYASSL_DTLS
        if (ssl->options.dtls) {
            DtlsPoolReset(ssl);
        }
#endif
        
        if ((*inOutIdx - begin) + OPAQUE16_LEN + OPAQUE8_LEN > size)
            return BUFFER_ERROR;

        XMEMCPY(&pv, input + *inOutIdx, OPAQUE16_LEN);
        *inOutIdx += OPAQUE16_LEN;

        cookieSz = input[(*inOutIdx)++];
        
        if (cookieSz) {
            if ((*inOutIdx - begin) + cookieSz > size)
                return BUFFER_ERROR;

#ifdef CYASSL_DTLS
            if (cookieSz <= MAX_COOKIE_LEN) {
                XMEMCPY(ssl->arrays->cookie, input + *inOutIdx, cookieSz);
                ssl->arrays->cookieSz = cookieSz;
            }
#endif
            *inOutIdx += cookieSz;
        }
        
        ssl->options.serverState = SERVER_HELLOVERIFYREQUEST_COMPLETE;
        return 0;
    }


    static int DoServerHello(CYASSL* ssl, const byte* input, word32* inOutIdx,
                             word32 helloSz)
    {
        byte            b;
        ProtocolVersion pv;
        byte            compression;
        word32          i = *inOutIdx;
        word32          begin = i;

#ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn) AddPacketName("ServerHello", &ssl->handShakeInfo);
        if (ssl->toInfoOn) AddLateName("ServerHello", &ssl->timeoutInfo);
#endif

        /* protocol version, random and session id length check */
        if ((i - begin) + OPAQUE16_LEN + RAN_LEN + OPAQUE8_LEN > helloSz)
            return BUFFER_ERROR;

        /* protocol version */
        XMEMCPY(&pv, input + i, OPAQUE16_LEN);
        i += OPAQUE16_LEN;

        if (pv.minor > ssl->version.minor) {
            CYASSL_MSG("Server using higher version, fatal error");
            return VERSION_ERROR;
        }
        else if (pv.minor < ssl->version.minor) {
            CYASSL_MSG("server using lower version");

            if (!ssl->options.downgrade) {
                CYASSL_MSG("    no downgrade allowed, fatal error");
                return VERSION_ERROR;
            }

            if (pv.minor == SSLv3_MINOR) {
                /* turn off tls */
                CYASSL_MSG("    downgrading to SSLv3");
                ssl->options.tls    = 0;
                ssl->options.tls1_1 = 0;
                ssl->version.minor  = SSLv3_MINOR;
            }
            else if (pv.minor == TLSv1_MINOR) {
                /* turn off tls 1.1+ */
                CYASSL_MSG("    downgrading to TLSv1");
                ssl->options.tls1_1 = 0;
                ssl->version.minor  = TLSv1_MINOR;
            }
            else if (pv.minor == TLSv1_1_MINOR) {
                CYASSL_MSG("    downgrading to TLSv1.1");
                ssl->version.minor  = TLSv1_1_MINOR;
            }
        }

        /* random */
        XMEMCPY(ssl->arrays->serverRandom, input + i, RAN_LEN);
        i += RAN_LEN;

        /* session id */
        b = input[i++];

        if (b == ID_LEN) {
            if ((i - begin) + ID_LEN > helloSz)
                return BUFFER_ERROR;

            XMEMCPY(ssl->arrays->sessionID, input + i, min(b, ID_LEN));
            i += ID_LEN;
            ssl->options.haveSessionId = 1;
        }
        else if (b) {
            CYASSL_MSG("Invalid session ID size");
            return BUFFER_ERROR; /* session ID nor 0 neither 32 bytes long */
        }

        /* suite and compression */
        if ((i - begin) + OPAQUE16_LEN + OPAQUE8_LEN > helloSz)
            return BUFFER_ERROR;

        ssl->options.cipherSuite0 = input[i++];
        ssl->options.cipherSuite  = input[i++];  
        compression = input[i++];

        if (compression != ZLIB_COMPRESSION && ssl->options.usingCompression) {
            CYASSL_MSG("Server refused compression, turning off"); 
            ssl->options.usingCompression = 0;  /* turn off if server refused */
        }

        *inOutIdx = i;

        /* tls extensions */
        if ( (i - begin) < helloSz) {
#ifdef HAVE_TLS_EXTENSIONS
            if (TLSX_SupportExtensions(ssl)) {
                int    ret = 0;
                word16 totalExtSz;
                Suites clSuites; /* just for compatibility right now */

                if ((i - begin) + OPAQUE16_LEN > helloSz)
                    return BUFFER_ERROR;

                ato16(&input[i], &totalExtSz);
                i += OPAQUE16_LEN;

                if ((i - begin) + totalExtSz > helloSz)
                    return BUFFER_ERROR;

                if ((ret = TLSX_Parse(ssl, (byte *) input + i,
                                                     totalExtSz, 0, &clSuites)))
                    return ret;

                i += totalExtSz;
                *inOutIdx = i;
            }
            else
#endif
                *inOutIdx = begin + helloSz; /* skip extensions */
        }

        ssl->options.serverState = SERVER_HELLO_COMPLETE;

        if (ssl->options.resuming) {
            if (ssl->options.haveSessionId && XMEMCMP(ssl->arrays->sessionID,
                                         ssl->session.sessionID, ID_LEN) == 0) {
                if (SetCipherSpecs(ssl) == 0) {
                    int ret = -1;

                    XMEMCPY(ssl->arrays->masterSecret,
                            ssl->session.masterSecret, SECRET_LEN);
                    #ifdef NO_OLD_TLS
                        ret = DeriveTlsKeys(ssl);
                    #else
                        #ifndef NO_TLS
                            if (ssl->options.tls)
                                ret = DeriveTlsKeys(ssl);
                        #endif
                            if (!ssl->options.tls)
                                ret = DeriveKeys(ssl);
                    #endif
                    ssl->options.serverState = SERVER_HELLODONE_COMPLETE;

                    return ret;
                }
                else {
                    CYASSL_MSG("Unsupported cipher suite, DoServerHello");
                    return UNSUPPORTED_SUITE;
                }
            }
            else {
                CYASSL_MSG("Server denied resumption attempt"); 
                ssl->options.resuming = 0; /* server denied resumption try */
            }
        }
        #ifdef CYASSL_DTLS
            if (ssl->options.dtls) {
                DtlsPoolReset(ssl);
            }
        #endif

        return SetCipherSpecs(ssl);
    }


    /* Make sure client setup is valid for this suite, true on success */
    int VerifyClientSuite(CYASSL* ssl)
    {
        int  havePSK = 0;
        byte first   = ssl->options.cipherSuite0;
        byte second  = ssl->options.cipherSuite;

        CYASSL_ENTER("VerifyClientSuite");

        #ifndef NO_PSK
            havePSK = ssl->options.havePSK;
        #endif

        if (CipherRequires(first, second, REQUIRES_PSK)) {
            CYASSL_MSG("Requires PSK");
            if (havePSK == 0) {
                CYASSL_MSG("Don't have PSK");
                return 0;
            }
        }

        return 1;  /* success */
    }


#ifndef NO_CERTS
    /* just read in and ignore for now TODO: */
    static int DoCertificateRequest(CYASSL* ssl, const byte* input, word32*
                                    inOutIdx, word32 size)
    {
        word16 len;
        word32 begin = *inOutIdx;
       
        #ifdef CYASSL_CALLBACKS
            if (ssl->hsInfoOn)
                AddPacketName("CertificateRequest", &ssl->handShakeInfo);
            if (ssl->toInfoOn)
                AddLateName("CertificateRequest", &ssl->timeoutInfo);
        #endif

        if ((*inOutIdx - begin) + OPAQUE8_LEN > size)
            return BUFFER_ERROR;

        len = input[(*inOutIdx)++];

        if ((*inOutIdx - begin) + len > size)
            return BUFFER_ERROR;

        /* types, read in here */
        *inOutIdx += len;

        /* signature and hash signature algorithm */
        if (IsAtLeastTLSv1_2(ssl)) {
            if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
                return BUFFER_ERROR;

            ato16(input + *inOutIdx, &len);
            *inOutIdx += OPAQUE16_LEN;

            if ((*inOutIdx - begin) + len > size)
                return BUFFER_ERROR;

            PickHashSigAlgo(ssl, input + *inOutIdx, len);
            *inOutIdx += len;
        }

        /* authorities */
        if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
            return BUFFER_ERROR;

        ato16(input + *inOutIdx, &len);
        *inOutIdx += OPAQUE16_LEN;

        if ((*inOutIdx - begin) + len > size)
            return BUFFER_ERROR;

        while (len) {
            word16 dnSz;

            if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
                return BUFFER_ERROR;

            ato16(input + *inOutIdx, &dnSz);
            *inOutIdx += OPAQUE16_LEN;

            if ((*inOutIdx - begin) + dnSz > size)
                return BUFFER_ERROR;

            *inOutIdx += dnSz;
            len -= OPAQUE16_LEN + dnSz;
        }

        /* don't send client cert or cert verify if user hasn't provided
           cert and private key */
        if (ssl->buffers.certificate.buffer && ssl->buffers.key.buffer)
            ssl->options.sendVerify = SEND_CERT;
        else if (IsTLS(ssl))
            ssl->options.sendVerify = SEND_BLANK_CERT;

        return 0;
    }
#endif /* !NO_CERTS */


    static int DoServerKeyExchange(CYASSL* ssl, const byte* input,
                                   word32* inOutIdx, word32 size)
    {
        word16 length = 0;
        word32 begin  = *inOutIdx;
        int    ret    = 0;

        (void)length; /* shut up compiler warnings */
        (void)begin;
        (void)ssl;
        (void)input;
        (void)size;
        (void)ret;

    #ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn)
            AddPacketName("ServerKeyExchange", &ssl->handShakeInfo);
        if (ssl->toInfoOn)
            AddLateName("ServerKeyExchange", &ssl->timeoutInfo);
    #endif

    #ifndef NO_PSK
        if (ssl->specs.kea == psk_kea) {

            if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
                return BUFFER_ERROR;

            ato16(input + *inOutIdx, &length);
            *inOutIdx += OPAQUE16_LEN;

            if ((*inOutIdx - begin) + length > size)
                return BUFFER_ERROR;

            XMEMCPY(ssl->arrays->server_hint, input + *inOutIdx,
                   min(length, MAX_PSK_ID_LEN));

            ssl->arrays->server_hint[min(length, MAX_PSK_ID_LEN - 1)] = 0;
            *inOutIdx += length;

            return 0;
        }
    #endif
    #ifndef NO_DH
        if (ssl->specs.kea == diffie_hellman_kea)
        {
        /* p */
        if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
            return BUFFER_ERROR;

        ato16(input + *inOutIdx, &length);
        *inOutIdx += OPAQUE16_LEN;

        if ((*inOutIdx - begin) + length > size)
            return BUFFER_ERROR;

        ssl->buffers.serverDH_P.buffer = (byte*) XMALLOC(length, ssl->heap,
                                                         DYNAMIC_TYPE_DH);

        if (ssl->buffers.serverDH_P.buffer)
            ssl->buffers.serverDH_P.length = length;
        else
            return MEMORY_ERROR;

        XMEMCPY(ssl->buffers.serverDH_P.buffer, input + *inOutIdx, length);
        *inOutIdx += length;

        /* g */
        if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
            return BUFFER_ERROR;

        ato16(input + *inOutIdx, &length);
        *inOutIdx += OPAQUE16_LEN;

        if ((*inOutIdx - begin) + length > size)
            return BUFFER_ERROR;

        ssl->buffers.serverDH_G.buffer = (byte*) XMALLOC(length, ssl->heap,
                                                         DYNAMIC_TYPE_DH);

        if (ssl->buffers.serverDH_G.buffer)
            ssl->buffers.serverDH_G.length = length;
        else
            return MEMORY_ERROR;

        XMEMCPY(ssl->buffers.serverDH_G.buffer, input + *inOutIdx, length);
        *inOutIdx += length;

        /* pub */
        if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
            return BUFFER_ERROR;

        ato16(input + *inOutIdx, &length);
        *inOutIdx += OPAQUE16_LEN;

        if ((*inOutIdx - begin) + length > size)
            return BUFFER_ERROR;

        ssl->buffers.serverDH_Pub.buffer = (byte*) XMALLOC(length, ssl->heap,
                                                           DYNAMIC_TYPE_DH);

        if (ssl->buffers.serverDH_Pub.buffer)
            ssl->buffers.serverDH_Pub.length = length;
        else
            return MEMORY_ERROR;

        XMEMCPY(ssl->buffers.serverDH_Pub.buffer, input + *inOutIdx, length);
        *inOutIdx += length;
        }  /* dh_kea */
    #endif /* NO_DH */

    #ifdef HAVE_ECC
        if (ssl->specs.kea == ecc_diffie_hellman_kea)
        {
        byte b;

        if ((*inOutIdx - begin) + ENUM_LEN + OPAQUE16_LEN + OPAQUE8_LEN > size)
            return BUFFER_ERROR;

        b = input[(*inOutIdx)++];

        if (b != named_curve)
            return ECC_CURVETYPE_ERROR;

        *inOutIdx += 1;   /* curve type, eat leading 0 */
        b = input[(*inOutIdx)++];

        if (b != secp256r1 && b != secp384r1 && b != secp521r1 && b !=
                 secp160r1 && b != secp192r1 && b != secp224r1)
            return ECC_CURVE_ERROR;

        length = input[(*inOutIdx)++];

        if ((*inOutIdx - begin) + length > size)
            return BUFFER_ERROR;

        if (ecc_import_x963(input + *inOutIdx, length, ssl->peerEccKey) != 0)
            return ECC_PEERKEY_ERROR;

        *inOutIdx += length;
        ssl->peerEccKeyPresent = 1;
        }
    #endif /* HAVE_ECC */

    #if !defined(NO_DH) && !defined(NO_PSK)
    if (ssl->specs.kea == dhe_psk_kea) {
        if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
            return BUFFER_ERROR;

        ato16(input + *inOutIdx, &length);
        *inOutIdx += OPAQUE16_LEN;

        if ((*inOutIdx - begin) + length > size)
            return BUFFER_ERROR;

        XMEMCPY(ssl->arrays->server_hint, input + *inOutIdx,
               min(length, MAX_PSK_ID_LEN));

        ssl->arrays->server_hint[min(length, MAX_PSK_ID_LEN - 1)] = 0;
        *inOutIdx += length;

        /* p */
        if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
            return BUFFER_ERROR;

        ato16(input + *inOutIdx, &length);
        *inOutIdx += OPAQUE16_LEN;

        if ((*inOutIdx - begin) + length > size)
            return BUFFER_ERROR;

        ssl->buffers.serverDH_P.buffer = (byte*) XMALLOC(length, ssl->heap,
                                                         DYNAMIC_TYPE_DH);

        if (ssl->buffers.serverDH_P.buffer)
            ssl->buffers.serverDH_P.length = length;
        else
            return MEMORY_ERROR;

        XMEMCPY(ssl->buffers.serverDH_P.buffer, input + *inOutIdx, length);
        *inOutIdx += length;

        /* g */
        if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
            return BUFFER_ERROR;

        ato16(input + *inOutIdx, &length);
        *inOutIdx += OPAQUE16_LEN;

        if ((*inOutIdx - begin) + length > size)
            return BUFFER_ERROR;

        ssl->buffers.serverDH_G.buffer = (byte*) XMALLOC(length, ssl->heap,
                                                         DYNAMIC_TYPE_DH);

        if (ssl->buffers.serverDH_G.buffer)
            ssl->buffers.serverDH_G.length = length;
        else
            return MEMORY_ERROR;

        XMEMCPY(ssl->buffers.serverDH_G.buffer, input + *inOutIdx, length);
        *inOutIdx += length;

        /* pub */
        if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
            return BUFFER_ERROR;

        ato16(input + *inOutIdx, &length);
        *inOutIdx += OPAQUE16_LEN;

        if ((*inOutIdx - begin) + length > size)
            return BUFFER_ERROR;

        ssl->buffers.serverDH_Pub.buffer = (byte*) XMALLOC(length, ssl->heap,
                                                           DYNAMIC_TYPE_DH);

        if (ssl->buffers.serverDH_Pub.buffer)
            ssl->buffers.serverDH_Pub.length = length;
        else
            return MEMORY_ERROR;

        XMEMCPY(ssl->buffers.serverDH_Pub.buffer, input + *inOutIdx, length);
        *inOutIdx += length;
    }
    #endif /* !NO_DH || !NO_PSK */

    #if !defined(NO_DH) || defined(HAVE_ECC)
    if (ssl->specs.kea == ecc_diffie_hellman_kea ||
        ssl->specs.kea == diffie_hellman_kea)
    {
#ifndef NO_OLD_TLS
        Md5    md5;
        Sha    sha;
#endif
#ifndef NO_SHA256
        Sha256 sha256;
        byte hash256[SHA256_DIGEST_SIZE];
#endif
#ifdef CYASSL_SHA384
        Sha384 sha384;
        byte hash384[SHA384_DIGEST_SIZE];
#endif
        byte   hash[FINISHED_SZ];
        byte   messageVerify[MAX_DH_SZ];
        byte   hashAlgo = sha_mac;
        byte   sigAlgo  = ssl->specs.sig_algo;
        word16 verifySz = (word16) (*inOutIdx - begin);

        /* save message for hash verify */
        if (verifySz > sizeof(messageVerify))
            return BUFFER_ERROR;

        XMEMCPY(messageVerify, input + begin, verifySz);

        if (IsAtLeastTLSv1_2(ssl)) {
            if ((*inOutIdx - begin) + ENUM_LEN + ENUM_LEN > size)
                return BUFFER_ERROR;

            hashAlgo = input[(*inOutIdx)++];
            sigAlgo  = input[(*inOutIdx)++];
        }

        /* signature */
        if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
            return BUFFER_ERROR;

        ato16(input + *inOutIdx, &length);
        *inOutIdx += OPAQUE16_LEN;

        if ((*inOutIdx - begin) + length > size)
            return BUFFER_ERROR;

        /* inOutIdx updated at the end of the function */

        /* verify signature */
#ifndef NO_OLD_TLS
        /* md5 */
        InitMd5(&md5);
        Md5Update(&md5, ssl->arrays->clientRandom, RAN_LEN);
        Md5Update(&md5, ssl->arrays->serverRandom, RAN_LEN);
        Md5Update(&md5, messageVerify, verifySz);
        Md5Final(&md5, hash);

        /* sha */
        ret = InitSha(&sha);
        if (ret != 0)
            return ret;
        ShaUpdate(&sha, ssl->arrays->clientRandom, RAN_LEN);
        ShaUpdate(&sha, ssl->arrays->serverRandom, RAN_LEN);
        ShaUpdate(&sha, messageVerify, verifySz);
        ShaFinal(&sha, hash + MD5_DIGEST_SIZE);
#endif

#ifndef NO_SHA256
        ret = InitSha256(&sha256);
        if (ret != 0)
            return ret;
        ret = Sha256Update(&sha256, ssl->arrays->clientRandom, RAN_LEN);
        if (ret != 0)
            return ret;
        ret = Sha256Update(&sha256, ssl->arrays->serverRandom, RAN_LEN);
        if (ret != 0)
            return ret;
        ret = Sha256Update(&sha256, messageVerify, verifySz);
        if (ret != 0)
            return ret;
        ret = Sha256Final(&sha256, hash256);
        if (ret != 0)
            return ret;
#endif

#ifdef CYASSL_SHA384
        ret = InitSha384(&sha384);
        if (ret != 0)
            return ret;
        ret = Sha384Update(&sha384, ssl->arrays->clientRandom, RAN_LEN);
        if (ret != 0)
            return ret;
        ret = Sha384Update(&sha384, ssl->arrays->serverRandom, RAN_LEN);
        if (ret != 0)
            return ret;
        ret = Sha384Update(&sha384, messageVerify, verifySz);
        if (ret != 0)
            return ret;
        ret = Sha384Final(&sha384, hash384);
        if (ret != 0)
            return ret;
#endif

#ifndef NO_RSA
        /* rsa */
        if (sigAlgo == rsa_sa_algo)
        {
            byte* out       = NULL;
            byte  doUserRsa = 0;

            #ifdef HAVE_PK_CALLBACKS
                if (ssl->ctx->RsaVerifyCb)
                    doUserRsa = 1;
            #endif /*HAVE_PK_CALLBACKS */

            if (!ssl->peerRsaKeyPresent)
                return NO_PEER_KEY;

            if (doUserRsa) {
            #ifdef HAVE_PK_CALLBACKS
                ret = ssl->ctx->RsaVerifyCb(ssl, (byte *) input + *inOutIdx,
                                            length, &out, 
                                            ssl->buffers.peerRsaKey.buffer,
                                            ssl->buffers.peerRsaKey.length,
                                            ssl->RsaVerifyCtx);
            #endif /*HAVE_PK_CALLBACKS */
            }
            else {
                ret = RsaSSL_VerifyInline((byte *) input + *inOutIdx, length,
                                          &out, ssl->peerRsaKey);
            }

            if (IsAtLeastTLSv1_2(ssl)) {
                byte   encodedSig[MAX_ENCODED_SIG_SZ];
                word32 encSigSz;
#ifndef NO_OLD_TLS
                byte*  digest = &hash[MD5_DIGEST_SIZE];
                int    typeH = SHAh;
                int    digestSz = SHA_DIGEST_SIZE;
#else
                byte*  digest = hash256;
                int    typeH =  SHA256h;
                int    digestSz = SHA256_DIGEST_SIZE;
#endif

                if (hashAlgo == sha_mac) {
                    #ifndef NO_SHA
                        digest   = &hash[MD5_DIGEST_SIZE];
                        typeH    = SHAh;
                        digestSz = SHA_DIGEST_SIZE;
                    #endif
                }
                else if (hashAlgo == sha256_mac) {
                    #ifndef NO_SHA256
                        digest   = hash256;
                        typeH    = SHA256h;
                        digestSz = SHA256_DIGEST_SIZE;
                    #endif
                }
                else if (hashAlgo == sha384_mac) {
                    #ifdef CYASSL_SHA384
                        digest   = hash384;
                        typeH    = SHA384h;
                        digestSz = SHA384_DIGEST_SIZE;
                    #endif
                }

                encSigSz = EncodeSignature(encodedSig, digest, digestSz, typeH);

                if (encSigSz != (word32)ret || !out || XMEMCMP(out, encodedSig,
                                        min(encSigSz, MAX_ENCODED_SIG_SZ)) != 0)
                    return VERIFY_SIGN_ERROR;
            }
            else { 
                if (ret != sizeof(hash) || !out || XMEMCMP(out,
                                                       hash, sizeof(hash)) != 0)
                    return VERIFY_SIGN_ERROR;
            }
        } else
#endif
#ifdef HAVE_ECC
        /* ecdsa */
        if (sigAlgo == ecc_dsa_sa_algo) {
            int verify = 0;
#ifndef NO_OLD_TLS
            byte* digest = &hash[MD5_DIGEST_SIZE];
            word32 digestSz = SHA_DIGEST_SIZE;
#else
            byte* digest = hash256;
            word32 digestSz = SHA256_DIGEST_SIZE;
#endif
            byte doUserEcc = 0;

            #ifdef HAVE_PK_CALLBACKS
                if (ssl->ctx->EccVerifyCb)
                    doUserEcc = 1;
            #endif

            if (!ssl->peerEccDsaKeyPresent)
                return NO_PEER_KEY;

            if (IsAtLeastTLSv1_2(ssl)) {
                if (hashAlgo == sha_mac) {
                    #ifndef NO_SHA
                        digest   = &hash[MD5_DIGEST_SIZE];
                        digestSz = SHA_DIGEST_SIZE;
                    #endif
                }
                else if (hashAlgo == sha256_mac) {
                    #ifndef NO_SHA256
                        digest   = hash256;
                        digestSz = SHA256_DIGEST_SIZE;
                    #endif
                }
                else if (hashAlgo == sha384_mac) {
                    #ifdef CYASSL_SHA384
                        digest   = hash384;
                        digestSz = SHA384_DIGEST_SIZE;
                    #endif
                }
            }
            if (doUserEcc) {
            #ifdef HAVE_PK_CALLBACKS
                ret = ssl->ctx->EccVerifyCb(ssl, input + *inOutIdx, length,
                                            digest, digestSz,
                                            ssl->buffers.peerEccDsaKey.buffer,
                                            ssl->buffers.peerEccDsaKey.length,
                                            &verify, ssl->EccVerifyCtx);
            #endif
            }
            else {
                ret = ecc_verify_hash(input + *inOutIdx, length,
                                 digest, digestSz, &verify, ssl->peerEccDsaKey);
            }
            if (ret != 0 || verify == 0)
                return VERIFY_SIGN_ERROR;
        }
        else
#endif /* HAVE_ECC */
            return ALGO_ID_E;

        /* signature length */
        *inOutIdx += length;

        ssl->options.serverState = SERVER_KEYEXCHANGE_COMPLETE;
    }
    return 0;
#else  /* !NO_DH or HAVE_ECC */
        return NOT_COMPILED_IN;  /* not supported by build */
#endif /* !NO_DH or HAVE_ECC */
    }


    int SendClientKeyExchange(CYASSL* ssl)
    {
        byte   encSecret[MAX_ENCRYPT_SZ];
        word32 encSz = 0;
        word32 idx = 0;
        int    ret = 0;
        byte   doUserRsa = 0;

        (void)doUserRsa;

        #ifdef HAVE_PK_CALLBACKS
            #ifndef NO_RSA
                if (ssl->ctx->RsaEncCb)
                    doUserRsa = 1;
            #endif /* NO_RSA */
        #endif /*HAVE_PK_CALLBACKS */

        switch (ssl->specs.kea) {
        #ifndef NO_RSA
            case rsa_kea:
                ret = RNG_GenerateBlock(ssl->rng, ssl->arrays->preMasterSecret,
                                                                    SECRET_LEN);
                if (ret != 0)
                    return ret;

                ssl->arrays->preMasterSecret[0] = ssl->chVersion.major;
                ssl->arrays->preMasterSecret[1] = ssl->chVersion.minor;
                ssl->arrays->preMasterSz = SECRET_LEN;

                if (ssl->peerRsaKeyPresent == 0)
                    return NO_PEER_KEY;

                if (doUserRsa) {
                #ifdef HAVE_PK_CALLBACKS
                    #ifndef NO_RSA
                        encSz = sizeof(encSecret);
                        ret = ssl->ctx->RsaEncCb(ssl,
                                            ssl->arrays->preMasterSecret,
                                            SECRET_LEN,
                                            encSecret, &encSz,
                                            ssl->buffers.peerRsaKey.buffer,
                                            ssl->buffers.peerRsaKey.length,
                                            ssl->RsaEncCtx);
                    #endif /* NO_RSA */
                #endif /*HAVE_PK_CALLBACKS */
                }
                else {
                    ret = RsaPublicEncrypt(ssl->arrays->preMasterSecret,
                                 SECRET_LEN, encSecret, sizeof(encSecret),
                                 ssl->peerRsaKey, ssl->rng);
                    if (ret > 0) {
                        encSz = ret;
                        ret = 0;   /* set success to 0 */
                    }
                }
                break;
        #endif
        #ifndef NO_DH
            case diffie_hellman_kea:
                {
                    buffer  serverP   = ssl->buffers.serverDH_P;
                    buffer  serverG   = ssl->buffers.serverDH_G;
                    buffer  serverPub = ssl->buffers.serverDH_Pub;
                    byte    priv[ENCRYPT_LEN];
                    word32  privSz = 0;
                    DhKey   key;

                    if (serverP.buffer == 0 || serverG.buffer == 0 ||
                                               serverPub.buffer == 0)
                        return NO_PEER_KEY;

                    InitDhKey(&key);
                    ret = DhSetKey(&key, serverP.buffer, serverP.length,
                                   serverG.buffer, serverG.length);
                    if (ret == 0)
                        /* for DH, encSecret is Yc, agree is pre-master */
                        ret = DhGenerateKeyPair(&key, ssl->rng, priv, &privSz,
                                                encSecret, &encSz);
                    if (ret == 0)
                        ret = DhAgree(&key, ssl->arrays->preMasterSecret,
                                      &ssl->arrays->preMasterSz, priv, privSz,
                                      serverPub.buffer, serverPub.length);
                    FreeDhKey(&key);
                }
                break;
        #endif /* NO_DH */
        #ifndef NO_PSK
            case psk_kea:
                {
                    byte* pms = ssl->arrays->preMasterSecret;

                    ssl->arrays->psk_keySz = ssl->options.client_psk_cb(ssl,
                        ssl->arrays->server_hint, ssl->arrays->client_identity,
                        MAX_PSK_ID_LEN, ssl->arrays->psk_key, MAX_PSK_KEY_LEN);
                    if (ssl->arrays->psk_keySz == 0 || 
                        ssl->arrays->psk_keySz > MAX_PSK_KEY_LEN)
                        return PSK_KEY_ERROR;
                    encSz = (word32)XSTRLEN(ssl->arrays->client_identity);
                    if (encSz > MAX_PSK_ID_LEN) return CLIENT_ID_ERROR;
                    XMEMCPY(encSecret, ssl->arrays->client_identity, encSz);

                    /* make psk pre master secret */
                    /* length of key + length 0s + length of key + key */
                    c16toa((word16)ssl->arrays->psk_keySz, pms);
                    pms += 2;
                    XMEMSET(pms, 0, ssl->arrays->psk_keySz);
                    pms += ssl->arrays->psk_keySz;
                    c16toa((word16)ssl->arrays->psk_keySz, pms);
                    pms += 2;
                    XMEMCPY(pms, ssl->arrays->psk_key, ssl->arrays->psk_keySz);
                    ssl->arrays->preMasterSz = ssl->arrays->psk_keySz * 2 + 4;
                    XMEMSET(ssl->arrays->psk_key, 0, ssl->arrays->psk_keySz);
                    ssl->arrays->psk_keySz = 0; /* No further need */
                }
                break;
        #endif /* NO_PSK */
        #if !defined(NO_DH) && !defined(NO_PSK)
            case dhe_psk_kea:
                {
                    byte* pms = ssl->arrays->preMasterSecret;
                    byte* es  = encSecret;
                    buffer  serverP   = ssl->buffers.serverDH_P;
                    buffer  serverG   = ssl->buffers.serverDH_G;
                    buffer  serverPub = ssl->buffers.serverDH_Pub;
                    byte    priv[ENCRYPT_LEN];
                    word32  privSz = 0;
                    word32  pubSz = 0;
                    word32  esSz = 0;
                    DhKey   key;

                    if (serverP.buffer == 0 || serverG.buffer == 0 ||
                                               serverPub.buffer == 0)
                        return NO_PEER_KEY;

                    ssl->arrays->psk_keySz = ssl->options.client_psk_cb(ssl,
                         ssl->arrays->server_hint, ssl->arrays->client_identity,
                         MAX_PSK_ID_LEN, ssl->arrays->psk_key, MAX_PSK_KEY_LEN);
                    if (ssl->arrays->psk_keySz == 0 ||
                                       ssl->arrays->psk_keySz > MAX_PSK_KEY_LEN)
                        return PSK_KEY_ERROR;
                    esSz = (word32)XSTRLEN(ssl->arrays->client_identity);

                    if (esSz > MAX_PSK_ID_LEN)
                        return CLIENT_ID_ERROR;
                    c16toa((word16)esSz, es);
                    es += OPAQUE16_LEN;
                    XMEMCPY(es, ssl->arrays->client_identity, esSz);
                    es += esSz;
                    encSz = esSz + OPAQUE16_LEN;

                    InitDhKey(&key);
                    ret = DhSetKey(&key, serverP.buffer, serverP.length,
                                   serverG.buffer, serverG.length);
                    if (ret == 0)
                        /* for DH, encSecret is Yc, agree is pre-master */
                        ret = DhGenerateKeyPair(&key, ssl->rng, priv, &privSz,
                                                es + OPAQUE16_LEN, &pubSz);
                    if (ret == 0)
                        ret = DhAgree(&key, pms + OPAQUE16_LEN,
                                      &ssl->arrays->preMasterSz, priv, privSz,
                                      serverPub.buffer, serverPub.length);
                    FreeDhKey(&key);
                    if (ret != 0)
                        return ret;

                    c16toa((word16)pubSz, es);
                    encSz += pubSz + OPAQUE16_LEN;
                    c16toa((word16)ssl->arrays->preMasterSz, pms);
                    ssl->arrays->preMasterSz += OPAQUE16_LEN;
                    pms += ssl->arrays->preMasterSz;

                    /* make psk pre master secret */
                    /* length of key + length 0s + length of key + key */
                    c16toa((word16)ssl->arrays->psk_keySz, pms);
                    pms += OPAQUE16_LEN;
                    XMEMCPY(pms, ssl->arrays->psk_key, ssl->arrays->psk_keySz);
                    ssl->arrays->preMasterSz +=
                                          ssl->arrays->psk_keySz + OPAQUE16_LEN;
                    XMEMSET(ssl->arrays->psk_key, 0, ssl->arrays->psk_keySz);
                    ssl->arrays->psk_keySz = 0; /* No further need */
                }
                break;
        #endif /* !NO_DH && !NO_PSK */
        #ifdef HAVE_NTRU
            case ntru_kea:
                {
                    word32 rc;
                    word16 cipherLen = sizeof(encSecret);
                    DRBG_HANDLE drbg;
                    static uint8_t const cyasslStr[] = {
                        'C', 'y', 'a', 'S', 'S', 'L', ' ', 'N', 'T', 'R', 'U'
                    };

                    ret = RNG_GenerateBlock(ssl->rng,
                                      ssl->arrays->preMasterSecret, SECRET_LEN);
                    if (ret != 0)
                        return ret;

                    ssl->arrays->preMasterSz = SECRET_LEN;

                    if (ssl->peerNtruKeyPresent == 0)
                        return NO_PEER_KEY;

                    rc = ntru_crypto_drbg_instantiate(MAX_NTRU_BITS, cyasslStr,
                                                 sizeof(cyasslStr), GetEntropy,
                                                 &drbg);
                    if (rc != DRBG_OK)
                        return NTRU_DRBG_ERROR; 

                    rc = ntru_crypto_ntru_encrypt(drbg, ssl->peerNtruKeyLen,
                                                  ssl->peerNtruKey,
                                                  ssl->arrays->preMasterSz,
                                                  ssl->arrays->preMasterSecret,
                                                  &cipherLen, encSecret);
                    ntru_crypto_drbg_uninstantiate(drbg);
                    if (rc != NTRU_OK)
                        return NTRU_ENCRYPT_ERROR;

                    encSz = cipherLen;
                    ret = 0;
                }
                break;
        #endif /* HAVE_NTRU */
        #ifdef HAVE_ECC
            case ecc_diffie_hellman_kea:
                {
                    ecc_key  myKey;
                    ecc_key* peerKey = NULL;
                    word32   size = sizeof(encSecret);

                    if (ssl->specs.static_ecdh) {
                        /* TODO: EccDsa is really fixed Ecc change naming */
                        if (!ssl->peerEccDsaKeyPresent || !ssl->peerEccDsaKey->dp)
                            return NO_PEER_KEY;
                        peerKey = ssl->peerEccDsaKey;
                    }
                    else {
                        if (!ssl->peerEccKeyPresent || !ssl->peerEccKey->dp)
                            return NO_PEER_KEY;
                        peerKey = ssl->peerEccKey;
                    }

                    if (peerKey == NULL)
                        return NO_PEER_KEY;

                    ecc_init(&myKey);
                    ret = ecc_make_key(ssl->rng, peerKey->dp->size, &myKey);
                    if (ret != 0)
                        return ECC_MAKEKEY_ERROR;

                    /* precede export with 1 byte length */
                    ret = ecc_export_x963(&myKey, encSecret + 1, &size);
                    encSecret[0] = (byte)size;
                    encSz = size + 1;

                    if (ret != 0)
                        ret = ECC_EXPORT_ERROR;
                    else {
                        size = sizeof(ssl->arrays->preMasterSecret);
                        ret  = ecc_shared_secret(&myKey, peerKey,
                                                 ssl->arrays->preMasterSecret, &size);
                        if (ret != 0)
                            ret = ECC_SHARED_ERROR;
                    }

                    ssl->arrays->preMasterSz = size;
                    ecc_free(&myKey);
                }
                break;
        #endif /* HAVE_ECC */
            default:
                return ALGO_ID_E; /* unsupported kea */
        }

        if (ret == 0) {
            byte              *output;
            int                sendSz;
            word32             tlsSz = 0;
            
            if (ssl->options.tls || ssl->specs.kea == diffie_hellman_kea)
                tlsSz = 2;

            if (ssl->specs.kea == ecc_diffie_hellman_kea ||
                ssl->specs.kea == dhe_psk_kea)  /* always off */
                tlsSz = 0;

            sendSz = encSz + tlsSz + HANDSHAKE_HEADER_SZ + RECORD_HEADER_SZ;
            idx    = HANDSHAKE_HEADER_SZ + RECORD_HEADER_SZ;

            #ifdef CYASSL_DTLS
                if (ssl->options.dtls) {
                    sendSz += DTLS_HANDSHAKE_EXTRA + DTLS_RECORD_EXTRA;
                    idx    += DTLS_HANDSHAKE_EXTRA + DTLS_RECORD_EXTRA;
                }
            #endif

            /* check for available size */
            if ((ret = CheckAvailableSize(ssl, sendSz)) != 0)
                return ret;

            /* get ouput buffer */
            output = ssl->buffers.outputBuffer.buffer + 
                     ssl->buffers.outputBuffer.length;

            AddHeaders(output, encSz + tlsSz, client_key_exchange, ssl);

            if (tlsSz) {
                c16toa((word16)encSz, &output[idx]);
                idx += 2;
            }
            XMEMCPY(output + idx, encSecret, encSz);
            /* if add more to output, adjust idx
            idx += encSz; */
            #ifdef CYASSL_DTLS
                if (ssl->options.dtls) {
                    if ((ret = DtlsPoolSave(ssl, output, sendSz)) != 0)
                        return ret;
                }
            #endif

            ret = HashOutput(ssl, output, sendSz, 0);
            if (ret != 0)
                return ret;

            #ifdef CYASSL_CALLBACKS
                if (ssl->hsInfoOn)
                    AddPacketName("ClientKeyExchange", &ssl->handShakeInfo);
                if (ssl->toInfoOn)
                    AddPacketInfo("ClientKeyExchange", &ssl->timeoutInfo,
                                  output, sendSz, ssl->heap);
            #endif

            ssl->buffers.outputBuffer.length += sendSz;

            if (ssl->options.groupMessages)
                ret = 0;
            else
                ret = SendBuffered(ssl);
        }
    
        if (ret == 0 || ret == WANT_WRITE) {
            int tmpRet = MakeMasterSecret(ssl);
            if (tmpRet != 0)
                ret = tmpRet;   /* save WANT_WRITE unless more serious */
            ssl->options.clientState = CLIENT_KEYEXCHANGE_COMPLETE;
        }
        /* No further need for PMS */
        XMEMSET(ssl->arrays->preMasterSecret, 0, ssl->arrays->preMasterSz);
        ssl->arrays->preMasterSz = 0;

        return ret;
    }

#ifndef NO_CERTS
    int SendCertificateVerify(CYASSL* ssl)
    {
        byte              *output;
        int                sendSz = 0, length, ret;
        word32             idx = 0;
        word32             sigOutSz = 0;
#ifndef NO_RSA
        RsaKey             key;
        int                initRsaKey = 0;
#endif
        int                usingEcc = 0;
#ifdef HAVE_ECC
        ecc_key            eccKey;
#endif

        (void)idx;

        if (ssl->options.sendVerify == SEND_BLANK_CERT)
            return 0;  /* sent blank cert, can't verify */

        /* check for available size */
        if ((ret = CheckAvailableSize(ssl, MAX_CERT_VERIFY_SZ)) != 0)
            return ret;

        /* get ouput buffer */
        output = ssl->buffers.outputBuffer.buffer +
                 ssl->buffers.outputBuffer.length;

        ret = BuildCertHashes(ssl, &ssl->certHashes);
        if (ret != 0)
            return ret;

#ifdef HAVE_ECC
        ecc_init(&eccKey);
#endif
#ifndef NO_RSA
        ret = InitRsaKey(&key, ssl->heap);
        if (ret == 0) initRsaKey = 1;
        if (ret == 0)
            ret = RsaPrivateKeyDecode(ssl->buffers.key.buffer, &idx, &key,
                                      ssl->buffers.key.length);
        if (ret == 0)
            sigOutSz = RsaEncryptSize(&key);
        else 
#endif
        {
    #ifdef HAVE_ECC
            CYASSL_MSG("Trying ECC client cert, RSA didn't work");
           
            idx = 0; 
            ret = EccPrivateKeyDecode(ssl->buffers.key.buffer, &idx, &eccKey,
                                      ssl->buffers.key.length);
            if (ret == 0) {
                CYASSL_MSG("Using ECC client cert");
                usingEcc = 1;
                sigOutSz = MAX_ENCODED_SIG_SZ; 
            }
            else {
                CYASSL_MSG("Bad client cert type");
            }
    #endif
        }
        if (ret == 0) {
            byte*  verify = (byte*)&output[RECORD_HEADER_SZ +
                                           HANDSHAKE_HEADER_SZ];
#ifndef NO_OLD_TLS
            byte*  signBuffer = ssl->certHashes.md5;
#else
            byte*  signBuffer = NULL;
#endif
            word32 signSz = FINISHED_SZ;
            byte   encodedSig[MAX_ENCODED_SIG_SZ];
            word32 extraSz = 0;  /* tls 1.2 hash/sig */

            (void)encodedSig;
            (void)signSz;
            (void)signBuffer;

            #ifdef CYASSL_DTLS
                if (ssl->options.dtls)
                    verify += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
            #endif
            length = sigOutSz;
            if (IsAtLeastTLSv1_2(ssl)) {
                verify[0] = ssl->suites->hashAlgo;
                verify[1] = usingEcc ? ecc_dsa_sa_algo : rsa_sa_algo;
                extraSz = HASH_SIG_SIZE;
            }

            if (usingEcc) {
#ifdef HAVE_ECC
                word32 localSz = MAX_ENCODED_SIG_SZ;
                word32 digestSz;
                byte*  digest;
                byte   doUserEcc = 0;
#ifndef NO_OLD_TLS
                /* old tls default */
                digestSz = SHA_DIGEST_SIZE;
                digest   = ssl->certHashes.sha;
#else
                /* new tls default */
                digestSz = SHA256_DIGEST_SIZE;
                digest   = ssl->certHashes.sha256;
#endif

                #ifdef HAVE_PK_CALLBACKS
                    #ifdef HAVE_ECC
                        if (ssl->ctx->EccSignCb)
                            doUserEcc = 1;
                    #endif /* HAVE_ECC */
                #endif /*HAVE_PK_CALLBACKS */

                if (IsAtLeastTLSv1_2(ssl)) {
                    if (ssl->suites->hashAlgo == sha_mac) {
                        #ifndef NO_SHA
                            digest = ssl->certHashes.sha;
                            digestSz = SHA_DIGEST_SIZE;
                        #endif
                    }
                    else if (ssl->suites->hashAlgo == sha256_mac) {
                        #ifndef NO_SHA256
                            digest = ssl->certHashes.sha256;
                            digestSz = SHA256_DIGEST_SIZE;
                        #endif
                    }
                    else if (ssl->suites->hashAlgo == sha384_mac) {
                        #ifdef CYASSL_SHA384
                            digest = ssl->certHashes.sha384;
                            digestSz = SHA384_DIGEST_SIZE;
                        #endif
                    }
                }

                if (doUserEcc) {
                #ifdef HAVE_PK_CALLBACKS
                    #ifdef HAVE_ECC
                        ret = ssl->ctx->EccSignCb(ssl, digest, digestSz,
                                        encodedSig, &localSz,
                                        ssl->buffers.key.buffer,
                                        ssl->buffers.key.length,
                                        ssl->EccSignCtx);
                    #endif /* HAVE_ECC */
                #endif /*HAVE_PK_CALLBACKS */
                }
                else {
                    ret = ecc_sign_hash(digest, digestSz, encodedSig,
                                        &localSz, ssl->rng, &eccKey);
                }
                if (ret == 0) {
                    length = localSz;
                    c16toa((word16)length, verify + extraSz); /* prepend hdr */
                    XMEMCPY(verify + extraSz + VERIFY_HEADER,encodedSig,length);
                }
#endif
            }
#ifndef NO_RSA
            else {
                byte doUserRsa = 0;

                #ifdef HAVE_PK_CALLBACKS
                    if (ssl->ctx->RsaSignCb)
                        doUserRsa = 1;
                #endif /*HAVE_PK_CALLBACKS */

                if (IsAtLeastTLSv1_2(ssl)) {
#ifndef NO_OLD_TLS
                    byte* digest = ssl->certHashes.sha;
                    int   digestSz = SHA_DIGEST_SIZE;
                    int   typeH = SHAh;
#else
                    byte* digest = ssl->certHashes.sha256;
                    int   digestSz = SHA256_DIGEST_SIZE;
                    int   typeH = SHA256h;
#endif

                    if (ssl->suites->hashAlgo == sha_mac) {
                        #ifndef NO_SHA
                            digest = ssl->certHashes.sha;
                            typeH    = SHAh;
                            digestSz = SHA_DIGEST_SIZE;
                        #endif
                    }
                    else if (ssl->suites->hashAlgo == sha256_mac) {
                        #ifndef NO_SHA256
                            digest = ssl->certHashes.sha256;
                            typeH    = SHA256h;
                            digestSz = SHA256_DIGEST_SIZE;
                        #endif
                    }
                    else if (ssl->suites->hashAlgo == sha384_mac) {
                        #ifdef CYASSL_SHA384
                            digest = ssl->certHashes.sha384;
                            typeH    = SHA384h;
                            digestSz = SHA384_DIGEST_SIZE;
                        #endif
                    }

                    signSz = EncodeSignature(encodedSig, digest,digestSz,typeH);
                    signBuffer = encodedSig;
                }

                c16toa((word16)length, verify + extraSz); /* prepend hdr */
                if (doUserRsa) {
                #ifdef HAVE_PK_CALLBACKS
                    #ifndef NO_RSA
                        word32 ioLen = ENCRYPT_LEN;
                        ret = ssl->ctx->RsaSignCb(ssl, signBuffer, signSz,
                                            verify + extraSz + VERIFY_HEADER,
                                            &ioLen,
                                            ssl->buffers.key.buffer,
                                            ssl->buffers.key.length,
                                            ssl->RsaSignCtx);
                    #endif /* NO_RSA */
                #endif /*HAVE_PK_CALLBACKS */
                }
                else {
                    ret = RsaSSL_Sign(signBuffer, signSz, verify + extraSz +
                                  VERIFY_HEADER, ENCRYPT_LEN, &key, ssl->rng);
                }

                if (ret > 0)
                    ret = 0;  /* RSA reset */
            }
#endif
            if (ret == 0) {
                AddHeaders(output, length + extraSz + VERIFY_HEADER,
                           certificate_verify, ssl);

                sendSz = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ + length +
                         extraSz + VERIFY_HEADER;
                #ifdef CYASSL_DTLS
                    if (ssl->options.dtls) {
                        sendSz += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
                        if ((ret = DtlsPoolSave(ssl, output, sendSz)) != 0)
                            return ret;
                    }
                #endif

                ret = HashOutput(ssl, output, sendSz, 0);
            }
        }
#ifndef NO_RSA
        if (initRsaKey)
            FreeRsaKey(&key);
#endif
#ifdef HAVE_ECC
        ecc_free(&eccKey);
#endif

        if (ret == 0) {
            #ifdef CYASSL_CALLBACKS
                if (ssl->hsInfoOn)
                    AddPacketName("CertificateVerify", &ssl->handShakeInfo);
                if (ssl->toInfoOn)
                    AddPacketInfo("CertificateVerify", &ssl->timeoutInfo,
                                  output, sendSz, ssl->heap);
            #endif
            ssl->buffers.outputBuffer.length += sendSz;
            if (ssl->options.groupMessages)
                return 0;
            else
                return SendBuffered(ssl);
        }
        else
            return ret;
    }
#endif /* NO_CERTS */


#endif /* NO_CYASSL_CLIENT */


#ifndef NO_CYASSL_SERVER

    int SendServerHello(CYASSL* ssl)
    {
        byte              *output;
        word32             length, idx = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
        int                sendSz;
        int                ret;

        length = VERSION_SZ + RAN_LEN
               + ID_LEN + ENUM_LEN                 
               + SUITE_LEN 
               + ENUM_LEN;

#ifdef HAVE_TLS_EXTENSIONS
        length += TLSX_GetResponseSize(ssl);
#endif

        /* check for avalaible size */
        if ((ret = CheckAvailableSize(ssl, MAX_HELLO_SZ)) != 0)
            return ret;

        /* get ouput buffer */
        output = ssl->buffers.outputBuffer.buffer + 
                 ssl->buffers.outputBuffer.length;

        sendSz = length + HANDSHAKE_HEADER_SZ + RECORD_HEADER_SZ;
        AddHeaders(output, length, server_hello, ssl);

        #ifdef CYASSL_DTLS
            if (ssl->options.dtls) {
                idx    += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
                sendSz += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
            }
        #endif
        /* now write to output */
            /* first version */
        output[idx++] = ssl->version.major;
        output[idx++] = ssl->version.minor;

            /* then random */
        if (!ssl->options.resuming) {
            ret = RNG_GenerateBlock(ssl->rng, ssl->arrays->serverRandom,
                                                                       RAN_LEN);
            if (ret != 0)
                return ret;
        }

        XMEMCPY(output + idx, ssl->arrays->serverRandom, RAN_LEN);
        idx += RAN_LEN;

#ifdef SHOW_SECRETS
        {
            int j;
            printf("server random: ");
            for (j = 0; j < RAN_LEN; j++)
                printf("%02x", ssl->arrays->serverRandom[j]);
            printf("\n");
        }
#endif
            /* then session id */
        output[idx++] = ID_LEN;

        if (!ssl->options.resuming) {
            ret = RNG_GenerateBlock(ssl->rng, ssl->arrays->sessionID, ID_LEN);
            if (ret != 0)
                return ret;
        }

        XMEMCPY(output + idx, ssl->arrays->sessionID, ID_LEN);
        idx += ID_LEN;

            /* then cipher suite */
        output[idx++] = ssl->options.cipherSuite0; 
        output[idx++] = ssl->options.cipherSuite;

            /* then compression */
        if (ssl->options.usingCompression)
            output[idx++] = ZLIB_COMPRESSION;
        else
            output[idx++] = NO_COMPRESSION;

            /* last, extensions */
#ifdef HAVE_TLS_EXTENSIONS
        TLSX_WriteResponse(ssl, output + idx);
#endif
            
        ssl->buffers.outputBuffer.length += sendSz;
        #ifdef CYASSL_DTLS
            if (ssl->options.dtls) {
                if ((ret = DtlsPoolSave(ssl, output, sendSz)) != 0)
                    return ret;
            }
        #endif

        ret = HashOutput(ssl, output, sendSz, 0);
        if (ret != 0)
            return ret;

        #ifdef CYASSL_CALLBACKS
            if (ssl->hsInfoOn)
                AddPacketName("ServerHello", &ssl->handShakeInfo);
            if (ssl->toInfoOn)
                AddPacketInfo("ServerHello", &ssl->timeoutInfo, output, sendSz,
                              ssl->heap);
        #endif

        ssl->options.serverState = SERVER_HELLO_COMPLETE;

        if (ssl->options.groupMessages)
            return 0;
        else
            return SendBuffered(ssl);
    }


#ifdef HAVE_ECC

    static byte SetCurveId(int size)
    {
        switch(size) {
            case 20:
                return secp160r1;
            case 24:
                return secp192r1;
            case 28:
                return secp224r1;
            case 32:
                return secp256r1;
            case 48:
                return secp384r1;
            case 66:
                return secp521r1;
            default:
                return 0;
        }        
    }

#endif /* HAVE_ECC */


    int SendServerKeyExchange(CYASSL* ssl)
    {
        int ret = 0;
        (void)ssl;

        #ifndef NO_PSK
        if (ssl->specs.kea == psk_kea)
        {
            byte    *output;
            word32   length, idx = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
            int      sendSz;
            if (ssl->arrays->server_hint[0] == 0) return 0; /* don't send */

            /* include size part */
            length = (word32)XSTRLEN(ssl->arrays->server_hint);
            if (length > MAX_PSK_ID_LEN) return SERVER_HINT_ERROR;
            length += HINT_LEN_SZ;
            sendSz = length + HANDSHAKE_HEADER_SZ + RECORD_HEADER_SZ;

            #ifdef CYASSL_DTLS 
                if (ssl->options.dtls) {
                    sendSz += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
                    idx    += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
                }
            #endif
            /* check for available size */
            if ((ret = CheckAvailableSize(ssl, sendSz)) != 0)
               return ret;

            /* get ouput buffer */
            output = ssl->buffers.outputBuffer.buffer + 
                     ssl->buffers.outputBuffer.length;

            AddHeaders(output, length, server_key_exchange, ssl);

            /* key data */
            c16toa((word16)(length - HINT_LEN_SZ), output + idx);
            idx += HINT_LEN_SZ;
            XMEMCPY(output + idx, ssl->arrays->server_hint,length -HINT_LEN_SZ);

            ret = HashOutput(ssl, output, sendSz, 0);
            if (ret != 0)
                return ret;

            #ifdef CYASSL_CALLBACKS
                if (ssl->hsInfoOn)
                    AddPacketName("ServerKeyExchange", &ssl->handShakeInfo);
                if (ssl->toInfoOn)
                    AddPacketInfo("ServerKeyExchange", &ssl->timeoutInfo,
                                  output, sendSz, ssl->heap);
            #endif

            ssl->buffers.outputBuffer.length += sendSz;
            if (ssl->options.groupMessages)
                ret = 0;
            else
                ret = SendBuffered(ssl);
            ssl->options.serverState = SERVER_KEYEXCHANGE_COMPLETE;
        }
        #endif /*NO_PSK */

        #if !defined(NO_DH) && !defined(NO_PSK)
        if (ssl->specs.kea == dhe_psk_kea) {
            byte    *output;
            word32   length, idx = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
            word32   hintLen;
            int      sendSz;
            DhKey    dhKey;

            if (ssl->buffers.serverDH_P.buffer == NULL ||
                ssl->buffers.serverDH_G.buffer == NULL)
                return NO_DH_PARAMS;

            if (ssl->buffers.serverDH_Pub.buffer == NULL) {
                ssl->buffers.serverDH_Pub.buffer = (byte*)XMALLOC(
                        ssl->buffers.serverDH_P.length + 2, ssl->ctx->heap,
                        DYNAMIC_TYPE_DH);
                if (ssl->buffers.serverDH_Pub.buffer == NULL)
                    return MEMORY_E;
            }

            if (ssl->buffers.serverDH_Priv.buffer == NULL) {
                ssl->buffers.serverDH_Priv.buffer = (byte*)XMALLOC(
                        ssl->buffers.serverDH_P.length + 2, ssl->ctx->heap,
                        DYNAMIC_TYPE_DH);
                if (ssl->buffers.serverDH_Priv.buffer == NULL)
                    return MEMORY_E;
            }

            InitDhKey(&dhKey);
            ret = DhSetKey(&dhKey, ssl->buffers.serverDH_P.buffer,
                                   ssl->buffers.serverDH_P.length,
                                   ssl->buffers.serverDH_G.buffer,
                                   ssl->buffers.serverDH_G.length);
            if (ret == 0)
                ret = DhGenerateKeyPair(&dhKey, ssl->rng,
                                         ssl->buffers.serverDH_Priv.buffer,
                                        &ssl->buffers.serverDH_Priv.length,
                                         ssl->buffers.serverDH_Pub.buffer,
                                        &ssl->buffers.serverDH_Pub.length);
            FreeDhKey(&dhKey);
            if (ret != 0)
                return ret;

            length = LENGTH_SZ * 3 + /* p, g, pub */
                     ssl->buffers.serverDH_P.length +
                     ssl->buffers.serverDH_G.length +
                     ssl->buffers.serverDH_Pub.length;

            /* include size part */
            hintLen = (word32)XSTRLEN(ssl->arrays->server_hint);
            if (hintLen > MAX_PSK_ID_LEN)
                return SERVER_HINT_ERROR;
            length += hintLen + HINT_LEN_SZ;
            sendSz = length + HANDSHAKE_HEADER_SZ + RECORD_HEADER_SZ;

            #ifdef CYASSL_DTLS
                if (ssl->options.dtls) {
                    sendSz += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
                    idx    += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
                }
            #endif
            /* check for available size */
            if ((ret = CheckAvailableSize(ssl, sendSz)) != 0)
               return ret;

            /* get ouput buffer */
            output = ssl->buffers.outputBuffer.buffer +
                     ssl->buffers.outputBuffer.length;

            AddHeaders(output, length, server_key_exchange, ssl);

            /* key data */
            c16toa((word16)hintLen, output + idx);
            idx += HINT_LEN_SZ;
            XMEMCPY(output + idx, ssl->arrays->server_hint, hintLen);
            idx += hintLen;

            /* add p, g, pub */
            c16toa((word16)ssl->buffers.serverDH_P.length, output + idx);
            idx += LENGTH_SZ;
            XMEMCPY(output + idx, ssl->buffers.serverDH_P.buffer,
                                  ssl->buffers.serverDH_P.length);
            idx += ssl->buffers.serverDH_P.length;

            /*  g */
            c16toa((word16)ssl->buffers.serverDH_G.length, output + idx);
            idx += LENGTH_SZ;
            XMEMCPY(output + idx, ssl->buffers.serverDH_G.buffer,
                                  ssl->buffers.serverDH_G.length);
            idx += ssl->buffers.serverDH_G.length;

            /*  pub */
            c16toa((word16)ssl->buffers.serverDH_Pub.length, output + idx);
            idx += LENGTH_SZ;
            XMEMCPY(output + idx, ssl->buffers.serverDH_Pub.buffer,
                                  ssl->buffers.serverDH_Pub.length);
            idx += ssl->buffers.serverDH_Pub.length;

            ret = HashOutput(ssl, output, sendSz, 0);

            if (ret != 0)
                return ret;

            #ifdef CYASSL_CALLBACKS
                if (ssl->hsInfoOn)
                    AddPacketName("ServerKeyExchange", &ssl->handShakeInfo);
                if (ssl->toInfoOn)
                    AddPacketInfo("ServerKeyExchange", &ssl->timeoutInfo,
                                  output, sendSz, ssl->heap);
            #endif

            ssl->buffers.outputBuffer.length += sendSz;
            if (ssl->options.groupMessages)
                ret = 0;
            else
                ret = SendBuffered(ssl);
            ssl->options.serverState = SERVER_KEYEXCHANGE_COMPLETE;
        }
        #endif /* !NO_DH && !NO_PSK */

        #ifdef HAVE_ECC
        if (ssl->specs.kea == ecc_diffie_hellman_kea)
        {
            byte    *output;
            word32   length, idx = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
            int      sendSz;
            byte     exportBuf[MAX_EXPORT_ECC_SZ];
            word32   expSz = sizeof(exportBuf);
            word32   sigSz;
            word32   preSigSz, preSigIdx;
#ifndef NO_RSA
            RsaKey   rsaKey;
#endif
            ecc_key  dsaKey;

            if (ssl->specs.static_ecdh) {
                CYASSL_MSG("Using Static ECDH, not sending ServerKeyExchagne");
                return 0;
            }

            /* curve type, named curve, length(1) */
            length = ENUM_LEN + CURVE_LEN + ENUM_LEN;
            /* pub key size */
            CYASSL_MSG("Using ephemeral ECDH");
            if (ecc_export_x963(ssl->eccTempKey, exportBuf, &expSz) != 0)
                return ECC_EXPORT_ERROR;
            length += expSz;

            preSigSz  = length;
            preSigIdx = idx;

#ifndef NO_RSA
            ret = InitRsaKey(&rsaKey, ssl->heap);
            if (ret != 0) return ret;
#endif
            ecc_init(&dsaKey);

            /* sig length */
            length += LENGTH_SZ;

            if (!ssl->buffers.key.buffer) {
#ifndef NO_RSA
                FreeRsaKey(&rsaKey);
#endif
                ecc_free(&dsaKey);
                return NO_PRIVATE_KEY;
            }

#ifndef NO_RSA
            if (ssl->specs.sig_algo == rsa_sa_algo) {
                /* rsa sig size */
                word32 i = 0;
                ret = RsaPrivateKeyDecode(ssl->buffers.key.buffer, &i,
                                          &rsaKey, ssl->buffers.key.length);
                if (ret != 0) return ret;
                sigSz = RsaEncryptSize(&rsaKey); 
            } else 
#endif
            if (ssl->specs.sig_algo == ecc_dsa_sa_algo) {
                /* ecdsa sig size */
                word32 i = 0;
                ret = EccPrivateKeyDecode(ssl->buffers.key.buffer, &i,
                                          &dsaKey, ssl->buffers.key.length);
                if (ret != 0) return ret;
                sigSz = ecc_sig_size(&dsaKey);  /* worst case estimate */
            }
            else {
#ifndef NO_RSA
                FreeRsaKey(&rsaKey);
#endif
                ecc_free(&dsaKey);
                return ALGO_ID_E;  /* unsupported type */
            }
            length += sigSz;

            if (IsAtLeastTLSv1_2(ssl))
                length += HASH_SIG_SIZE;

            sendSz = length + HANDSHAKE_HEADER_SZ + RECORD_HEADER_SZ;

            #ifdef CYASSL_DTLS 
                if (ssl->options.dtls) {
                    sendSz += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
                    idx    += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
                    preSigIdx = idx;
                }
            #endif
            /* check for available size */
            if ((ret = CheckAvailableSize(ssl, sendSz)) != 0) {
#ifndef NO_RSA
                FreeRsaKey(&rsaKey);
#endif
                ecc_free(&dsaKey); 
                return ret;
            } 

            /* get ouput buffer */
            output = ssl->buffers.outputBuffer.buffer + 
                     ssl->buffers.outputBuffer.length;

            /* record and message headers will be added below, when we're sure
               of the sig length */

            /* key exchange data */
            output[idx++] = named_curve;
            output[idx++] = 0x00;          /* leading zero */
            output[idx++] = SetCurveId(ecc_size(ssl->eccTempKey)); 
            output[idx++] = (byte)expSz;
            XMEMCPY(output + idx, exportBuf, expSz);
            idx += expSz;
            if (IsAtLeastTLSv1_2(ssl)) {
                output[idx++] = ssl->suites->hashAlgo;
                output[idx++] = ssl->suites->sigAlgo;
            }

            /* Signtaure length will be written later, when we're sure what it
               is */

            /* do signature */
            {
#ifndef NO_OLD_TLS
                Md5    md5;
                Sha    sha;
#endif
                byte   hash[FINISHED_SZ];
                #ifndef NO_SHA256
                    Sha256 sha256;
                    byte hash256[SHA256_DIGEST_SIZE];
                #endif
                #ifdef CYASSL_SHA384
                    Sha384 sha384;
                    byte hash384[SHA384_DIGEST_SIZE];
                #endif

#ifndef NO_OLD_TLS
                /* md5 */
                InitMd5(&md5);
                Md5Update(&md5, ssl->arrays->clientRandom, RAN_LEN);
                Md5Update(&md5, ssl->arrays->serverRandom, RAN_LEN);
                Md5Update(&md5, output + preSigIdx, preSigSz);
                Md5Final(&md5, hash);

                /* sha */
                ret = InitSha(&sha);
                if (ret != 0)
                    return ret;
                ShaUpdate(&sha, ssl->arrays->clientRandom, RAN_LEN);
                ShaUpdate(&sha, ssl->arrays->serverRandom, RAN_LEN);
                ShaUpdate(&sha, output + preSigIdx, preSigSz);
                ShaFinal(&sha, &hash[MD5_DIGEST_SIZE]);
#endif

                #ifndef NO_SHA256
                    ret = InitSha256(&sha256);
                    if (ret != 0)
                        return ret;
                    ret = Sha256Update(&sha256, ssl->arrays->clientRandom, RAN_LEN);
                    if (ret != 0)
                        return ret;
                    ret = Sha256Update(&sha256, ssl->arrays->serverRandom, RAN_LEN);
                    if (ret != 0)
                        return ret;
                    ret = Sha256Update(&sha256, output + preSigIdx, preSigSz);
                    if (ret != 0)
                        return ret;
                    ret = Sha256Final(&sha256, hash256);
                    if (ret != 0)
                        return ret;
                #endif

                #ifdef CYASSL_SHA384
                    ret = InitSha384(&sha384);
                    if (ret != 0)
                        return ret;
                    ret = Sha384Update(&sha384, ssl->arrays->clientRandom, RAN_LEN);
                    if (ret != 0)
                        return ret;
                    ret = Sha384Update(&sha384, ssl->arrays->serverRandom, RAN_LEN);
                    if (ret != 0)
                        return ret;
                    ret = Sha384Update(&sha384, output + preSigIdx, preSigSz);
                    if (ret != 0)
                        return ret;
                    ret = Sha384Final(&sha384, hash384);
                    if (ret != 0)
                        return ret;
                #endif
#ifndef NO_RSA
                if (ssl->suites->sigAlgo == rsa_sa_algo) {
                    byte*  signBuffer = hash;
                    word32 signSz    = sizeof(hash);
                    byte   encodedSig[MAX_ENCODED_SIG_SZ];
                    byte   doUserRsa = 0;

                    #ifdef HAVE_PK_CALLBACKS
                        if (ssl->ctx->RsaSignCb)
                            doUserRsa = 1;
                    #endif /*HAVE_PK_CALLBACKS */

                    if (IsAtLeastTLSv1_2(ssl)) {
                        byte* digest   = &hash[MD5_DIGEST_SIZE];
                        int   typeH    = SHAh;
                        int   digestSz = SHA_DIGEST_SIZE;

                        if (ssl->suites->hashAlgo == sha256_mac) {
                            #ifndef NO_SHA256
                                digest   = hash256;
                                typeH    = SHA256h;
                                digestSz = SHA256_DIGEST_SIZE;
                            #endif
                        }
                        else if (ssl->suites->hashAlgo == sha384_mac) {
                            #ifdef CYASSL_SHA384
                                digest   = hash384;
                                typeH    = SHA384h;
                                digestSz = SHA384_DIGEST_SIZE;
                            #endif
                        }

                        signSz = EncodeSignature(encodedSig, digest, digestSz,
                                                 typeH);
                        signBuffer = encodedSig;
                    }
                    /* write sig size here */
                    c16toa((word16)sigSz, output + idx);
                    idx += LENGTH_SZ;

                    if (doUserRsa) {
                        #ifdef HAVE_PK_CALLBACKS
                            word32 ioLen = sigSz;
                            ret = ssl->ctx->RsaSignCb(ssl, signBuffer, signSz,
                                                output + idx,
                                                &ioLen,
                                                ssl->buffers.key.buffer,
                                                ssl->buffers.key.length,
                                                ssl->RsaSignCtx);
                        #endif /*HAVE_PK_CALLBACKS */
                    }
                    else {
                        ret = RsaSSL_Sign(signBuffer, signSz, output + idx,
                                          sigSz, &rsaKey, ssl->rng);
                        if (ret > 0)
                            ret = 0; /* reset on success */
                    }
                    FreeRsaKey(&rsaKey);
                    ecc_free(&dsaKey);
                    if (ret < 0)
                        return ret;
                } else 
#endif
                if (ssl->suites->sigAlgo == ecc_dsa_sa_algo) {
#ifndef NO_OLD_TLS
                    byte* digest = &hash[MD5_DIGEST_SIZE];
                    word32 digestSz = SHA_DIGEST_SIZE;
#else
                    byte* digest = hash256;
                    word32 digestSz = SHA256_DIGEST_SIZE;
#endif
                    word32 sz = sigSz;
                    byte   doUserEcc = 0;

                    #ifdef HAVE_PK_CALLBACKS
                        #ifdef HAVE_ECC
                            if (ssl->ctx->EccSignCb)
                                doUserEcc = 1;
                        #endif /* HAVE_ECC */
                    #endif /*HAVE_PK_CALLBACKS */

                    if (IsAtLeastTLSv1_2(ssl)) {
                        if (ssl->suites->hashAlgo == sha_mac) {
                            #ifndef NO_SHA
                                digest   = &hash[MD5_DIGEST_SIZE];
                                digestSz = SHA_DIGEST_SIZE;
                            #endif
                        }
                        else if (ssl->suites->hashAlgo == sha256_mac) {
                            #ifndef NO_SHA256
                                digest   = hash256;
                                digestSz = SHA256_DIGEST_SIZE;
                            #endif
                        }
                        else if (ssl->suites->hashAlgo == sha384_mac) {
                            #ifdef CYASSL_SHA384
                                digest   = hash384;
                                digestSz = SHA384_DIGEST_SIZE;
                            #endif
                        }
                    }

                    if (doUserEcc) {
                    #ifdef HAVE_PK_CALLBACKS
                        #ifdef HAVE_ECC
                            ret = ssl->ctx->EccSignCb(ssl, digest, digestSz,
                                            output + LENGTH_SZ + idx, &sz,
                                            ssl->buffers.key.buffer,
                                            ssl->buffers.key.length,
                                            ssl->EccSignCtx);
                        #endif /* HAVE_ECC */
                    #endif /*HAVE_PK_CALLBACKS */
                    }
                    else {
                        ret = ecc_sign_hash(digest, digestSz,
                              output + LENGTH_SZ + idx, &sz, ssl->rng, &dsaKey);
                    }
#ifndef NO_RSA
                    FreeRsaKey(&rsaKey);
#endif
                    ecc_free(&dsaKey);
                    if (ret < 0) return ret;

                    /* Now that we know the real sig size, write it. */
                    c16toa((word16)sz, output + idx);

                    /* And adjust length and sendSz from estimates */
                    length += sz - sigSz;
                    sendSz += sz - sigSz;
                }
            }

            AddHeaders(output, length, server_key_exchange, ssl);

            ret = HashOutput(ssl, output, sendSz, 0);
            if (ret != 0)
                return ret;

            #ifdef CYASSL_CALLBACKS
                if (ssl->hsInfoOn)
                    AddPacketName("ServerKeyExchange", &ssl->handShakeInfo);
                if (ssl->toInfoOn)
                    AddPacketInfo("ServerKeyExchange", &ssl->timeoutInfo,
                                  output, sendSz, ssl->heap);
            #endif

            ssl->buffers.outputBuffer.length += sendSz;
            if (ssl->options.groupMessages)
                ret = 0;
            else
                ret = SendBuffered(ssl);
            ssl->options.serverState = SERVER_KEYEXCHANGE_COMPLETE;
        }
        #endif /* HAVE_ECC */

        #if !defined(NO_DH) && !defined(NO_RSA)
        if (ssl->specs.kea == diffie_hellman_kea) {
            byte    *output;
            word32   length = 0, idx = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
            int      sendSz;
            word32   sigSz = 0, i = 0;
            word32   preSigSz = 0, preSigIdx = 0;
            RsaKey   rsaKey;
            DhKey    dhKey;
            
            if (ssl->buffers.serverDH_P.buffer == NULL ||
                ssl->buffers.serverDH_G.buffer == NULL)
                return NO_DH_PARAMS;

            if (ssl->buffers.serverDH_Pub.buffer == NULL) {
                ssl->buffers.serverDH_Pub.buffer = (byte*)XMALLOC(
                        ssl->buffers.serverDH_P.length + 2, ssl->ctx->heap,
                        DYNAMIC_TYPE_DH);
                if (ssl->buffers.serverDH_Pub.buffer == NULL)
                    return MEMORY_E;
            } 

            if (ssl->buffers.serverDH_Priv.buffer == NULL) {
                ssl->buffers.serverDH_Priv.buffer = (byte*)XMALLOC(
                        ssl->buffers.serverDH_P.length + 2, ssl->ctx->heap,
                        DYNAMIC_TYPE_DH);
                if (ssl->buffers.serverDH_Priv.buffer == NULL)
                    return MEMORY_E;
            } 

            InitDhKey(&dhKey);
            ret = DhSetKey(&dhKey, ssl->buffers.serverDH_P.buffer,
                                   ssl->buffers.serverDH_P.length,
                                   ssl->buffers.serverDH_G.buffer,
                                   ssl->buffers.serverDH_G.length);
            if (ret == 0)
                ret = DhGenerateKeyPair(&dhKey, ssl->rng,
                                         ssl->buffers.serverDH_Priv.buffer,
                                        &ssl->buffers.serverDH_Priv.length,
                                         ssl->buffers.serverDH_Pub.buffer,
                                        &ssl->buffers.serverDH_Pub.length);
            FreeDhKey(&dhKey);

            if (ret == 0) {
                ret = InitRsaKey(&rsaKey, ssl->heap);
                if (ret != 0) return ret;
            }
            if (ret == 0) {
                length = LENGTH_SZ * 3;  /* p, g, pub */
                length += ssl->buffers.serverDH_P.length +
                          ssl->buffers.serverDH_G.length + 
                          ssl->buffers.serverDH_Pub.length;

                preSigIdx = idx;
                preSigSz  = length;

                /* sig length */
                length += LENGTH_SZ;

                if (!ssl->buffers.key.buffer)
                    return NO_PRIVATE_KEY;

                ret = RsaPrivateKeyDecode(ssl->buffers.key.buffer, &i, &rsaKey,
                                          ssl->buffers.key.length);
                if (ret == 0) {
                    sigSz = RsaEncryptSize(&rsaKey);
                    length += sigSz;
                }
            }
            if (ret != 0) {
                FreeRsaKey(&rsaKey);
                return ret;
            }
                                         
            if (IsAtLeastTLSv1_2(ssl))
                length += HASH_SIG_SIZE;

            sendSz = length + HANDSHAKE_HEADER_SZ + RECORD_HEADER_SZ;

            #ifdef CYASSL_DTLS 
                if (ssl->options.dtls) {
                    sendSz += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
                    idx    += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
                    preSigIdx = idx;
                }
            #endif
            /* check for available size */
            if ((ret = CheckAvailableSize(ssl, sendSz)) != 0) {
                FreeRsaKey(&rsaKey);
                return ret;
            } 

            /* get ouput buffer */
            output = ssl->buffers.outputBuffer.buffer + 
                     ssl->buffers.outputBuffer.length;

            AddHeaders(output, length, server_key_exchange, ssl);

            /* add p, g, pub */
            c16toa((word16)ssl->buffers.serverDH_P.length, output + idx);
            idx += LENGTH_SZ;
            XMEMCPY(output + idx, ssl->buffers.serverDH_P.buffer,
                                  ssl->buffers.serverDH_P.length);
            idx += ssl->buffers.serverDH_P.length;

            /*  g */
            c16toa((word16)ssl->buffers.serverDH_G.length, output + idx);
            idx += LENGTH_SZ;
            XMEMCPY(output + idx, ssl->buffers.serverDH_G.buffer,
                                  ssl->buffers.serverDH_G.length);
            idx += ssl->buffers.serverDH_G.length;

            /*  pub */
            c16toa((word16)ssl->buffers.serverDH_Pub.length, output + idx);
            idx += LENGTH_SZ;
            XMEMCPY(output + idx, ssl->buffers.serverDH_Pub.buffer,
                                  ssl->buffers.serverDH_Pub.length);
            idx += ssl->buffers.serverDH_Pub.length;

            /* Add signature */
            if (IsAtLeastTLSv1_2(ssl)) {
                output[idx++] = ssl->suites->hashAlgo;
                output[idx++] = ssl->suites->sigAlgo; 
            }
            /*    size */
            c16toa((word16)sigSz, output + idx);
            idx += LENGTH_SZ;

            /* do signature */
            {
#ifndef NO_OLD_TLS
                Md5    md5;
                Sha    sha;
#endif
                byte   hash[FINISHED_SZ];
                #ifndef NO_SHA256
                    Sha256 sha256;
                    byte hash256[SHA256_DIGEST_SIZE];
                #endif
                #ifdef CYASSL_SHA384
                    Sha384 sha384;
                    byte hash384[SHA384_DIGEST_SIZE];
                #endif

#ifndef NO_OLD_TLS
                /* md5 */
                InitMd5(&md5);
                Md5Update(&md5, ssl->arrays->clientRandom, RAN_LEN);
                Md5Update(&md5, ssl->arrays->serverRandom, RAN_LEN);
                Md5Update(&md5, output + preSigIdx, preSigSz);
                Md5Final(&md5, hash);

                /* sha */
                ret = InitSha(&sha);
                if (ret != 0)
                    return ret;
                ShaUpdate(&sha, ssl->arrays->clientRandom, RAN_LEN);
                ShaUpdate(&sha, ssl->arrays->serverRandom, RAN_LEN);
                ShaUpdate(&sha, output + preSigIdx, preSigSz);
                ShaFinal(&sha, &hash[MD5_DIGEST_SIZE]);
#endif

                #ifndef NO_SHA256
                    ret = InitSha256(&sha256);
                    if (ret != 0)
                        return ret;
                    ret = Sha256Update(&sha256, ssl->arrays->clientRandom, RAN_LEN);
                    if (ret != 0)
                        return ret;
                    ret = Sha256Update(&sha256, ssl->arrays->serverRandom, RAN_LEN);
                    if (ret != 0)
                        return ret;
                    ret = Sha256Update(&sha256, output + preSigIdx, preSigSz);
                    if (ret != 0)
                        return ret;
                    ret = Sha256Final(&sha256, hash256);
                    if (ret != 0)
                        return ret;
                #endif

                #ifdef CYASSL_SHA384
                    ret = InitSha384(&sha384);
                    if (ret != 0)
                        return ret;
                    ret = Sha384Update(&sha384, ssl->arrays->clientRandom, RAN_LEN);
                    if (ret != 0)
                        return ret;
                    ret = Sha384Update(&sha384, ssl->arrays->serverRandom, RAN_LEN);
                    if (ret != 0)
                        return ret;
                    ret = Sha384Update(&sha384, output + preSigIdx, preSigSz);
                    if (ret != 0)
                        return ret;
                    ret = Sha384Final(&sha384, hash384);
                    if (ret != 0)
                        return ret;
                #endif
#ifndef NO_RSA
                if (ssl->suites->sigAlgo == rsa_sa_algo) {
                    byte*  signBuffer = hash;
                    word32 signSz    = sizeof(hash);
                    byte   encodedSig[MAX_ENCODED_SIG_SZ];
                    byte   doUserRsa = 0;

                    #ifdef HAVE_PK_CALLBACKS
                        if (ssl->ctx->RsaSignCb)
                            doUserRsa = 1;
                    #endif /*HAVE_PK_CALLBACKS */

                    if (IsAtLeastTLSv1_2(ssl)) {
                        byte* digest   = &hash[MD5_DIGEST_SIZE];
                        int   typeH    = SHAh;
                        int   digestSz = SHA_DIGEST_SIZE;

                        if (ssl->suites->hashAlgo == sha256_mac) {
                            #ifndef NO_SHA256
                                digest   = hash256;
                                typeH    = SHA256h;
                                digestSz = SHA256_DIGEST_SIZE;
                            #endif
                        }
                        else if (ssl->suites->hashAlgo == sha384_mac) {
                            #ifdef CYASSL_SHA384
                                digest   = hash384;
                                typeH    = SHA384h;
                                digestSz = SHA384_DIGEST_SIZE;
                            #endif
                        }

                        signSz = EncodeSignature(encodedSig, digest, digestSz,
                                                 typeH);
                        signBuffer = encodedSig;
                    }
                    if (doUserRsa) {
                        #ifdef HAVE_PK_CALLBACKS
                            word32 ioLen = sigSz;
                            ret = ssl->ctx->RsaSignCb(ssl, signBuffer, signSz,
                                                output + idx,
                                                &ioLen,
                                                ssl->buffers.key.buffer,
                                                ssl->buffers.key.length,
                                                ssl->RsaSignCtx);
                        #endif /*HAVE_PK_CALLBACKS */
                    }
                    else {
                        ret = RsaSSL_Sign(signBuffer, signSz, output + idx,
                                          sigSz, &rsaKey, ssl->rng);
                    }
                    FreeRsaKey(&rsaKey);
                    if (ret < 0)
                        return ret;
                }
#endif
            }

            #ifdef CYASSL_DTLS
                if (ssl->options.dtls) {
                    if ((ret = DtlsPoolSave(ssl, output, sendSz)) != 0)
                        return ret;
                }
            #endif

            ret = HashOutput(ssl, output, sendSz, 0);
            if (ret != 0)
                return ret;

            #ifdef CYASSL_CALLBACKS
                if (ssl->hsInfoOn)
                    AddPacketName("ServerKeyExchange", &ssl->handShakeInfo);
                if (ssl->toInfoOn)
                    AddPacketInfo("ServerKeyExchange", &ssl->timeoutInfo,
                                  output, sendSz, ssl->heap);
            #endif

            ssl->buffers.outputBuffer.length += sendSz;
            if (ssl->options.groupMessages)
                ret = 0;
            else
                ret = SendBuffered(ssl);
            ssl->options.serverState = SERVER_KEYEXCHANGE_COMPLETE;
        }
        #endif /* NO_DH */

        return ret;
    }


    /* Make sure server cert/key are valid for this suite, true on success */
    static int VerifyServerSuite(CYASSL* ssl, word16 idx)
    {
        int  haveRSA = !ssl->options.haveStaticECC;
        int  havePSK = 0;
        byte first;
        byte second;

        CYASSL_ENTER("VerifyServerSuite");

        if (ssl->suites == NULL) {
            CYASSL_MSG("Suites pointer error");
            return 0;
        }

        first   = ssl->suites->suites[idx];
        second  = ssl->suites->suites[idx+1];

        #ifndef NO_PSK
            havePSK = ssl->options.havePSK;
        #endif

        if (ssl->options.haveNTRU)
            haveRSA = 0;

        if (CipherRequires(first, second, REQUIRES_RSA)) {
            CYASSL_MSG("Requires RSA");
            if (haveRSA == 0) {
                CYASSL_MSG("Don't have RSA");
                return 0;
            }
        }

        if (CipherRequires(first, second, REQUIRES_DHE)) {
            CYASSL_MSG("Requires DHE");
            if (ssl->options.haveDH == 0) {
                CYASSL_MSG("Don't have DHE");
                return 0;
            }
        }

        if (CipherRequires(first, second, REQUIRES_ECC_DSA)) {
            CYASSL_MSG("Requires ECCDSA");
            if (ssl->options.haveECDSAsig == 0) {
                CYASSL_MSG("Don't have ECCDSA");
                return 0;
            }
        }

        if (CipherRequires(first, second, REQUIRES_ECC_STATIC)) {
            CYASSL_MSG("Requires static ECC");
            if (ssl->options.haveStaticECC == 0) {
                CYASSL_MSG("Don't have static ECC");
                return 0;
            }
        }

        if (CipherRequires(first, second, REQUIRES_PSK)) {
            CYASSL_MSG("Requires PSK");
            if (havePSK == 0) {
                CYASSL_MSG("Don't have PSK");
                return 0;
            }
        }

        if (CipherRequires(first, second, REQUIRES_NTRU)) {
            CYASSL_MSG("Requires NTRU");
            if (ssl->options.haveNTRU == 0) {
                CYASSL_MSG("Don't have NTRU");
                return 0;
            }
        }

        if (CipherRequires(first, second, REQUIRES_RSA_SIG)) {
            CYASSL_MSG("Requires RSA Signature");
            if (ssl->options.side == CYASSL_SERVER_END &&
                                           ssl->options.haveECDSAsig == 1) {
                CYASSL_MSG("Don't have RSA Signature");
                return 0;
            }
        }

#ifdef HAVE_SUPPORTED_CURVES
        if (!TLSX_ValidateEllipticCurves(ssl, first, second)) {
            CYASSL_MSG("Don't have matching curves");
                return 0;
        }
#endif

        /* ECCDHE is always supported if ECC on */

        return 1;
    }


    static int MatchSuite(CYASSL* ssl, Suites* peerSuites)
    {
        word16 i, j;

        CYASSL_ENTER("MatchSuite");

        /* & 0x1 equivalent % 2 */
        if (peerSuites->suiteSz == 0 || peerSuites->suiteSz & 0x1)
            return MATCH_SUITE_ERROR;

        if (ssl->suites == NULL)
            return SUITES_ERROR;
        /* start with best, if a match we are good */
        for (i = 0; i < ssl->suites->suiteSz; i += 2)
            for (j = 0; j < peerSuites->suiteSz; j += 2)
                if (ssl->suites->suites[i]   == peerSuites->suites[j] &&
                    ssl->suites->suites[i+1] == peerSuites->suites[j+1] ) {

                    if (VerifyServerSuite(ssl, i)) {
                        int result;
                        CYASSL_MSG("Verified suite validity");
                        ssl->options.cipherSuite0 = ssl->suites->suites[i];
                        ssl->options.cipherSuite  = ssl->suites->suites[i+1];
                        result = SetCipherSpecs(ssl);
                        if (result == 0)
                            PickHashSigAlgo(ssl, peerSuites->hashSigAlgo,
                                                 peerSuites->hashSigAlgoSz);
                        return result;
                    }
                    else {
                        CYASSL_MSG("Could not verify suite validity, continue");
                    }
                }

        return MATCH_SUITE_ERROR;
    }


    /* process old style client hello, deprecate? */
    int ProcessOldClientHello(CYASSL* ssl, const byte* input, word32* inOutIdx,
                              word32 inSz, word16 sz)
    {
        word32          idx = *inOutIdx;
        word16          sessionSz;
        word16          randomSz;
        word16          i, j;
        ProtocolVersion pv;
        Suites          clSuites;

        (void)inSz;
        CYASSL_MSG("Got old format client hello");
#ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn)
            AddPacketName("ClientHello", &ssl->handShakeInfo);
        if (ssl->toInfoOn)
            AddLateName("ClientHello", &ssl->timeoutInfo);
#endif

        /* manually hash input since different format */
#ifndef NO_OLD_TLS
#ifndef NO_MD5
        Md5Update(&ssl->hashMd5, input + idx, sz);
#endif
#ifndef NO_SHA
        ShaUpdate(&ssl->hashSha, input + idx, sz);
#endif
#endif
#ifndef NO_SHA256
        if (IsAtLeastTLSv1_2(ssl)) {
            int shaRet = Sha256Update(&ssl->hashSha256, input + idx, sz);

            if (shaRet != 0)
                return shaRet;
        }
#endif

        /* does this value mean client_hello? */
        idx++;

        /* version */
        pv.major = input[idx++];
        pv.minor = input[idx++];
        ssl->chVersion = pv;  /* store */

        if (ssl->version.minor > pv.minor) {
            byte haveRSA = 0;
            byte havePSK = 0;
            if (!ssl->options.downgrade) {
                CYASSL_MSG("Client trying to connect with lesser version"); 
                return VERSION_ERROR;
            }
            if (pv.minor == SSLv3_MINOR) {
                /* turn off tls */
                CYASSL_MSG("    downgrading to SSLv3");
                ssl->options.tls    = 0;
                ssl->options.tls1_1 = 0;
                ssl->version.minor  = SSLv3_MINOR;
            }
            else if (pv.minor == TLSv1_MINOR) {
                CYASSL_MSG("    downgrading to TLSv1");
                /* turn off tls 1.1+ */
                ssl->options.tls1_1 = 0;
                ssl->version.minor  = TLSv1_MINOR;
            }
            else if (pv.minor == TLSv1_1_MINOR) {
                CYASSL_MSG("    downgrading to TLSv1.1");
                ssl->version.minor  = TLSv1_1_MINOR;
            }
#ifndef NO_RSA
            haveRSA = 1;
#endif
#ifndef NO_PSK
            havePSK = ssl->options.havePSK;
#endif

            InitSuites(ssl->suites, ssl->version, haveRSA, havePSK,
                       ssl->options.haveDH, ssl->options.haveNTRU,
                       ssl->options.haveECDSAsig, ssl->options.haveStaticECC,
                       ssl->options.side);
        }

        /* suite size */
        ato16(&input[idx], &clSuites.suiteSz);
        idx += 2;

        if (clSuites.suiteSz > MAX_SUITE_SZ)
            return BUFFER_ERROR;
        clSuites.hashSigAlgoSz = 0;

        /* session size */
        ato16(&input[idx], &sessionSz);
        idx += 2;

        if (sessionSz > ID_LEN)
            return BUFFER_ERROR;
    
        /* random size */
        ato16(&input[idx], &randomSz);
        idx += 2;

        if (randomSz > RAN_LEN)
            return BUFFER_ERROR;

        /* suites */
        for (i = 0, j = 0; i < clSuites.suiteSz; i += 3) {    
            byte first = input[idx++];
            if (!first) { /* implicit: skip sslv2 type */
                XMEMCPY(&clSuites.suites[j], &input[idx], 2);
                j += 2;
            }
            idx += 2;
        }
        clSuites.suiteSz = j;

        /* session id */
        if (sessionSz) {
            XMEMCPY(ssl->arrays->sessionID, input + idx, sessionSz);
            idx += sessionSz;
            ssl->options.resuming = 1;
        }

        /* random */
        if (randomSz < RAN_LEN)
            XMEMSET(ssl->arrays->clientRandom, 0, RAN_LEN - randomSz);
        XMEMCPY(&ssl->arrays->clientRandom[RAN_LEN - randomSz], input + idx,
               randomSz);
        idx += randomSz;

        if (ssl->options.usingCompression)
            ssl->options.usingCompression = 0;  /* turn off */

        ssl->options.clientState = CLIENT_HELLO_COMPLETE;
        *inOutIdx = idx;

        ssl->options.haveSessionId = 1;
        /* DoClientHello uses same resume code */
        if (ssl->options.resuming) {  /* let's try */
            int ret = -1; 
            CYASSL_SESSION* session = GetSession(ssl,ssl->arrays->masterSecret);
            if (!session) {
                CYASSL_MSG("Session lookup for resume failed");
                ssl->options.resuming = 0;
            } else {
                if (MatchSuite(ssl, &clSuites) < 0) {
                    CYASSL_MSG("Unsupported cipher suite, OldClientHello");
                    return UNSUPPORTED_SUITE;
                }
                #ifdef SESSION_CERTS
                    ssl->session = *session; /* restore session certs. */
                #endif

                ret = RNG_GenerateBlock(ssl->rng, ssl->arrays->serverRandom,
                                                                       RAN_LEN);
                if (ret != 0)
                    return ret;

                #ifdef NO_OLD_TLS
                    ret = DeriveTlsKeys(ssl);
                #else
                    #ifndef NO_TLS
                        if (ssl->options.tls)
                            ret = DeriveTlsKeys(ssl);
                    #endif
                        if (!ssl->options.tls)
                            ret = DeriveKeys(ssl);
                #endif
                ssl->options.clientState = CLIENT_KEYEXCHANGE_COMPLETE;

                return ret;
            }
        }

        return MatchSuite(ssl, &clSuites);
    }


    static int DoClientHello(CYASSL* ssl, const byte* input, word32* inOutIdx,
                             word32 helloSz)
    {
        byte            b;
        ProtocolVersion pv;
        Suites          clSuites;
        word32          i = *inOutIdx;
        word32          begin = i;

#ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn) AddPacketName("ClientHello", &ssl->handShakeInfo);
        if (ssl->toInfoOn) AddLateName("ClientHello", &ssl->timeoutInfo);
#endif

        /* protocol version, random and session id length check */
        if ((i - begin) + OPAQUE16_LEN + RAN_LEN + OPAQUE8_LEN > helloSz)
            return BUFFER_ERROR;

        /* protocol version */
        XMEMCPY(&pv, input + i, OPAQUE16_LEN);
        ssl->chVersion = pv;   /* store */
        i += OPAQUE16_LEN;

        if (ssl->version.minor > pv.minor) {
            byte haveRSA = 0;
            byte havePSK = 0;

            if (!ssl->options.downgrade) {
                CYASSL_MSG("Client trying to connect with lesser version"); 
                return VERSION_ERROR;
            }

            if (pv.minor == SSLv3_MINOR) {
                /* turn off tls */
                CYASSL_MSG("    downgrading to SSLv3");
                ssl->options.tls    = 0;
                ssl->options.tls1_1 = 0;
                ssl->version.minor  = SSLv3_MINOR;
            }
            else if (pv.minor == TLSv1_MINOR) {
                /* turn off tls 1.1+ */
                CYASSL_MSG("    downgrading to TLSv1");
                ssl->options.tls1_1 = 0;
                ssl->version.minor  = TLSv1_MINOR;
            }
            else if (pv.minor == TLSv1_1_MINOR) {
                CYASSL_MSG("    downgrading to TLSv1.1");
                ssl->version.minor  = TLSv1_1_MINOR;
            }
#ifndef NO_RSA
            haveRSA = 1;
#endif
#ifndef NO_PSK
            havePSK = ssl->options.havePSK;
#endif
            InitSuites(ssl->suites, ssl->version, haveRSA, havePSK,
                       ssl->options.haveDH, ssl->options.haveNTRU,
                       ssl->options.haveECDSAsig, ssl->options.haveStaticECC,
                       ssl->options.side);
        }

        /* random */
        XMEMCPY(ssl->arrays->clientRandom, input + i, RAN_LEN);
        i += RAN_LEN;

#ifdef SHOW_SECRETS
        {
            int j;
            printf("client random: ");
            for (j = 0; j < RAN_LEN; j++)
                printf("%02x", ssl->arrays->clientRandom[j]);
            printf("\n");
        }
#endif

        /* session id */
        b = input[i++];

        if (b == ID_LEN) {
            if ((i - begin) + ID_LEN > helloSz)
                return BUFFER_ERROR;

            XMEMCPY(ssl->arrays->sessionID, input + i, ID_LEN);
            i += ID_LEN;
            ssl->options.resuming = 1; /* client wants to resume */
            CYASSL_MSG("Client wants to resume session");
        }
        else if (b) {
            CYASSL_MSG("Invalid session ID size");
            return BUFFER_ERROR; /* session ID nor 0 neither 32 bytes long */
        }
        
        #ifdef CYASSL_DTLS
            /* cookie */
            if (ssl->options.dtls) {

                if ((i - begin) + OPAQUE8_LEN > helloSz)
                    return BUFFER_ERROR;

                b = input[i++];

                if (b) {
                    byte cookie[MAX_COOKIE_LEN];

                    if (b > MAX_COOKIE_LEN)
                        return BUFFER_ERROR;

                    if ((i - begin) + b > helloSz)
                        return BUFFER_ERROR;

                    if (ssl->ctx->CBIOCookie == NULL) {
                        CYASSL_MSG("Your Cookie callback is null, please set");
                        return COOKIE_ERROR;
                    }

                    if ((ssl->ctx->CBIOCookie(ssl, cookie, COOKIE_SZ,
                                              ssl->IOCB_CookieCtx) != COOKIE_SZ)
                            || (b != COOKIE_SZ)
                            || (XMEMCMP(cookie, input + i, b) != 0)) {
                        return COOKIE_ERROR;
                    }

                    i += b;
                }
            }
        #endif

        /* suites */
        if ((i - begin) + OPAQUE16_LEN > helloSz)
            return BUFFER_ERROR;

        ato16(&input[i], &clSuites.suiteSz);
        i += OPAQUE16_LEN;

        /* suites and compression length check */
        if ((i - begin) + clSuites.suiteSz + OPAQUE8_LEN > helloSz)
            return BUFFER_ERROR;

        if (clSuites.suiteSz > MAX_SUITE_SZ)
            return BUFFER_ERROR;

        XMEMCPY(clSuites.suites, input + i, clSuites.suiteSz);
        i += clSuites.suiteSz;
        clSuites.hashSigAlgoSz = 0;

        /* compression length */
        b = input[i++];

        if ((i - begin) + b > helloSz)
            return BUFFER_ERROR;

        if (ssl->options.usingCompression) {
            int match = 0;

            while (b--) {
                byte comp = input[i++];

                if (comp == ZLIB_COMPRESSION)
                    match = 1;
            }

            if (!match) {
                CYASSL_MSG("Not matching compression, turning off"); 
                ssl->options.usingCompression = 0;  /* turn off */
            }
        }
        else
            i += b; /* ignore, since we're not on */

        *inOutIdx = i;

        /* tls extensions */
        if ((i - begin) < helloSz) {
#ifdef HAVE_TLS_EXTENSIONS
            if (TLSX_SupportExtensions(ssl)) {
                int ret = 0;
#else
            if (IsAtLeastTLSv1_2(ssl)) {
#endif
                /* Process the hello extension. Skip unsupported. */
                word16 totalExtSz;

                if ((i - begin) + OPAQUE16_LEN > helloSz)
                    return BUFFER_ERROR;

                ato16(&input[i], &totalExtSz);
                i += OPAQUE16_LEN;

                if ((i - begin) + totalExtSz > helloSz)
                    return BUFFER_ERROR;

#ifdef HAVE_TLS_EXTENSIONS
                if ((ret = TLSX_Parse(ssl, (byte *) input + i,
                                                     totalExtSz, 1, &clSuites)))
                    return ret;

                i += totalExtSz;
#else
                while (totalExtSz) {
                    word16 extId, extSz;

                    if (OPAQUE16_LEN + OPAQUE16_LEN > totalExtSz)
                        return BUFFER_ERROR;
                   
                    ato16(&input[i], &extId);
                    i += OPAQUE16_LEN;
                    ato16(&input[i], &extSz);
                    i += OPAQUE16_LEN;

                    if (OPAQUE16_LEN + OPAQUE16_LEN + extSz > totalExtSz)
                        return BUFFER_ERROR;

                    if (extId == HELLO_EXT_SIG_ALGO) {
                        ato16(&input[i], &clSuites.hashSigAlgoSz);
                        i += OPAQUE16_LEN;

                        if (OPAQUE16_LEN + clSuites.hashSigAlgoSz > extSz)
                            return BUFFER_ERROR;

                        XMEMCPY(clSuites.hashSigAlgo, &input[i],
                            min(clSuites.hashSigAlgoSz, HELLO_EXT_SIGALGO_MAX));
                        i += clSuites.hashSigAlgoSz;
                    }
                    else
                        i += extSz;

                    totalExtSz -= OPAQUE16_LEN + OPAQUE16_LEN + extSz;
                }
#endif
                *inOutIdx = i;
            }
            else
                *inOutIdx = begin + helloSz; /* skip extensions */
        }

        ssl->options.clientState   = CLIENT_HELLO_COMPLETE;
        ssl->options.haveSessionId = 1;
        
        /* ProcessOld uses same resume code */
        if (ssl->options.resuming && (!ssl->options.dtls ||
               ssl->options.acceptState == HELLO_VERIFY_SENT)) { /* let's try */
            int ret = -1;            
            CYASSL_SESSION* session = GetSession(ssl,ssl->arrays->masterSecret);

            if (!session) {
                CYASSL_MSG("Session lookup for resume failed");
                ssl->options.resuming = 0;
            }
            else {
                if (MatchSuite(ssl, &clSuites) < 0) {
                    CYASSL_MSG("Unsupported cipher suite, ClientHello");
                    return UNSUPPORTED_SUITE;
                }
                #ifdef SESSION_CERTS
                    ssl->session = *session; /* restore session certs. */
                #endif

                ret = RNG_GenerateBlock(ssl->rng, ssl->arrays->serverRandom,
                                                                       RAN_LEN);
                if (ret != 0)
                    return ret;

                #ifdef NO_OLD_TLS
                    ret = DeriveTlsKeys(ssl);
                #else
                    #ifndef NO_TLS
                        if (ssl->options.tls)
                            ret = DeriveTlsKeys(ssl);
                    #endif
                        if (!ssl->options.tls)
                            ret = DeriveKeys(ssl);
                #endif
                ssl->options.clientState = CLIENT_KEYEXCHANGE_COMPLETE;

                return ret;
            }
        }
        return MatchSuite(ssl, &clSuites);
    }

#if !defined(NO_RSA) || defined(HAVE_ECC)
    static int DoCertificateVerify(CYASSL* ssl, byte* input, word32* inOutIdx,
                                   word32 size)
    {
        word16      sz = 0;
        int         ret = VERIFY_CERT_ERROR;   /* start in error state */
        byte        hashAlgo = sha_mac;
        byte        sigAlgo = anonymous_sa_algo;
        word32      begin = *inOutIdx;

        #ifdef CYASSL_CALLBACKS
            if (ssl->hsInfoOn)
                AddPacketName("CertificateVerify", &ssl->handShakeInfo);
            if (ssl->toInfoOn)
                AddLateName("CertificateVerify", &ssl->timeoutInfo);
        #endif


        if (IsAtLeastTLSv1_2(ssl)) {
            if ((*inOutIdx - begin) + ENUM_LEN + ENUM_LEN > size)
                return BUFFER_ERROR;

            hashAlgo = input[(*inOutIdx)++];
            sigAlgo  = input[(*inOutIdx)++];
        }

        if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
            return BUFFER_ERROR;

        ato16(input + *inOutIdx, &sz);
        *inOutIdx += OPAQUE16_LEN;

        if ((*inOutIdx - begin) + sz > size || sz > ENCRYPT_LEN)
            return BUFFER_ERROR;

        /* RSA */
#ifndef NO_RSA
        if (ssl->peerRsaKeyPresent != 0) {
            byte* out       = NULL;
            int   outLen    = 0;
            byte  doUserRsa = 0;

            #ifdef HAVE_PK_CALLBACKS
                if (ssl->ctx->RsaVerifyCb)
                    doUserRsa = 1;
            #endif /*HAVE_PK_CALLBACKS */

            CYASSL_MSG("Doing RSA peer cert verify");

            if (doUserRsa) {
            #ifdef HAVE_PK_CALLBACKS
                outLen = ssl->ctx->RsaVerifyCb(ssl, input + *inOutIdx, sz,
                                            &out, 
                                            ssl->buffers.peerRsaKey.buffer,
                                            ssl->buffers.peerRsaKey.length,
                                            ssl->RsaVerifyCtx);
            #endif /*HAVE_PK_CALLBACKS */
            }
            else {
                outLen = RsaSSL_VerifyInline(input + *inOutIdx, sz, &out,
                                                               ssl->peerRsaKey);
            }

            if (IsAtLeastTLSv1_2(ssl)) {
                byte   encodedSig[MAX_ENCODED_SIG_SZ];
                word32 sigSz;
                byte*  digest = ssl->certHashes.sha;
                int    typeH = SHAh;
                int    digestSz = SHA_DIGEST_SIZE;

                if (sigAlgo != rsa_sa_algo) {
                    CYASSL_MSG("Oops, peer sent RSA key but not in verify");
                }

                if (hashAlgo == sha256_mac) {
                    #ifndef NO_SHA256
                        digest = ssl->certHashes.sha256;
                        typeH    = SHA256h;
                        digestSz = SHA256_DIGEST_SIZE;
                    #endif
                }
                else if (hashAlgo == sha384_mac) {
                    #ifdef CYASSL_SHA384
                        digest = ssl->certHashes.sha384;
                        typeH    = SHA384h;
                        digestSz = SHA384_DIGEST_SIZE;
                    #endif
                }

                sigSz = EncodeSignature(encodedSig, digest, digestSz, typeH);

                if (outLen == (int)sigSz && out && XMEMCMP(out, encodedSig,
                                           min(sigSz, MAX_ENCODED_SIG_SZ)) == 0)
                    ret = 0; /* verified */
            }
            else {
                if (outLen == FINISHED_SZ && out && XMEMCMP(out,
                                            &ssl->certHashes, FINISHED_SZ) == 0)
                    ret = 0; /* verified */
            }
        }
#endif
#ifdef HAVE_ECC
        if (ssl->peerEccDsaKeyPresent) {
            int verify =  0;
            int err    = -1;
            byte* digest = ssl->certHashes.sha;
            word32 digestSz = SHA_DIGEST_SIZE;
            byte doUserEcc = 0;

            #ifdef HAVE_PK_CALLBACKS
                if (ssl->ctx->EccVerifyCb)
                    doUserEcc = 1;
            #endif

            CYASSL_MSG("Doing ECC peer cert verify");

            if (IsAtLeastTLSv1_2(ssl)) {
                if (sigAlgo != ecc_dsa_sa_algo) {
                    CYASSL_MSG("Oops, peer sent ECC key but not in verify");
                }

                if (hashAlgo == sha256_mac) {
                    #ifndef NO_SHA256
                        digest = ssl->certHashes.sha256;
                        digestSz = SHA256_DIGEST_SIZE;
                    #endif
                }
                else if (hashAlgo == sha384_mac) {
                    #ifdef CYASSL_SHA384
                        digest = ssl->certHashes.sha384;
                        digestSz = SHA384_DIGEST_SIZE;
                    #endif
                }
            }

            if (doUserEcc) {
            #ifdef HAVE_PK_CALLBACKS
                ret = ssl->ctx->EccVerifyCb(ssl, input + *inOutIdx, sz, digest,
                                            digestSz,
                                            ssl->buffers.peerEccDsaKey.buffer,
                                            ssl->buffers.peerEccDsaKey.length,
                                            &verify, ssl->EccVerifyCtx);
            #endif
            }
            else {
                err = ecc_verify_hash(input + *inOutIdx, sz, digest, digestSz,
                                                   &verify, ssl->peerEccDsaKey);
            }

            if (err == 0 && verify == 1)
               ret = 0; /* verified */
        }
#endif
        *inOutIdx += sz;

        if (ret == 0)
            ssl->options.havePeerVerify = 1;
          
        return ret;
    }
#endif /* !NO_RSA || HAVE_ECC */

    int SendServerHelloDone(CYASSL* ssl)
    {
        byte              *output;
        int                sendSz = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
        int                ret;

        #ifdef CYASSL_DTLS
            if (ssl->options.dtls)
                sendSz += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
        #endif
        /* check for available size */
        if ((ret = CheckAvailableSize(ssl, sendSz)) != 0)
            return ret;

        /* get ouput buffer */
        output = ssl->buffers.outputBuffer.buffer +
                 ssl->buffers.outputBuffer.length;

        AddHeaders(output, 0, server_hello_done, ssl);

        #ifdef CYASSL_DTLS
            if (ssl->options.dtls) {
                if ((ret = DtlsPoolSave(ssl, output, sendSz)) != 0)
                    return 0;
            }
        #endif

        ret = HashOutput(ssl, output, sendSz, 0);
            if (ret != 0)
                return ret;

#ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn)
            AddPacketName("ServerHelloDone", &ssl->handShakeInfo);
        if (ssl->toInfoOn)
            AddPacketInfo("ServerHelloDone", &ssl->timeoutInfo, output, sendSz,
                          ssl->heap);
#endif
        ssl->options.serverState = SERVER_HELLODONE_COMPLETE;

        ssl->buffers.outputBuffer.length += sendSz;

        return SendBuffered(ssl);
    }

#ifdef CYASSL_DTLS
    int SendHelloVerifyRequest(CYASSL* ssl)
    {
        byte* output;
        byte  cookieSz = COOKIE_SZ;
        int   length = VERSION_SZ + ENUM_LEN + cookieSz;
        int   idx    = DTLS_RECORD_HEADER_SZ + DTLS_HANDSHAKE_HEADER_SZ;
        int   sendSz = length + idx;
        int   ret;

        /* check for available size */
        if ((ret = CheckAvailableSize(ssl, sendSz)) != 0)
            return ret;

        /* get ouput buffer */
        output = ssl->buffers.outputBuffer.buffer +
                 ssl->buffers.outputBuffer.length;

        AddHeaders(output, length, hello_verify_request, ssl);

        output[idx++] =  ssl->chVersion.major;
        output[idx++] =  ssl->chVersion.minor;

        output[idx++] = cookieSz;
        if (ssl->ctx->CBIOCookie == NULL) {
            CYASSL_MSG("Your Cookie callback is null, please set");
            return COOKIE_ERROR;
        }
        if ((ret = ssl->ctx->CBIOCookie(ssl, output + idx, cookieSz,
                                        ssl->IOCB_CookieCtx)) < 0)
            return ret;

        ret = HashOutput(ssl, output, sendSz, 0);
        if (ret != 0)
            return ret;

#ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn)
            AddPacketName("HelloVerifyRequest", &ssl->handShakeInfo);
        if (ssl->toInfoOn)
            AddPacketInfo("HelloVerifyRequest", &ssl->timeoutInfo, output,
                          sendSz, ssl->heap);
#endif
        ssl->options.serverState = SERVER_HELLOVERIFYREQUEST_COMPLETE;

        ssl->buffers.outputBuffer.length += sendSz;

        return SendBuffered(ssl);
    }
#endif

    static int DoClientKeyExchange(CYASSL* ssl, byte* input, word32* inOutIdx,
                                                                    word32 size)
    {
        int    ret = 0;
        word32 length = 0;
        byte*  out = NULL;
        word32 begin = *inOutIdx;

        (void)length; /* shut up compiler warnings */
        (void)out;
        (void)input;
        (void)size;
        (void)begin;

        if (ssl->options.side != CYASSL_SERVER_END) {
            CYASSL_MSG("Client received client keyexchange, attack?");
            CYASSL_ERROR(ssl->error = SIDE_ERROR);
            return SSL_FATAL_ERROR;
        }

        if (ssl->options.clientState < CLIENT_HELLO_COMPLETE) {
            CYASSL_MSG("Client sending keyexchange at wrong time");
            SendAlert(ssl, alert_fatal, unexpected_message);
            return OUT_OF_ORDER_E;
        }

        #ifndef NO_CERTS
            if (ssl->options.verifyPeer && ssl->options.failNoCert)
                if (!ssl->options.havePeerCert) {
                    CYASSL_MSG("client didn't present peer cert");
                    return NO_PEER_CERT;
                }
        #endif

        #ifdef CYASSL_CALLBACKS
            if (ssl->hsInfoOn)
                AddPacketName("ClientKeyExchange", &ssl->handShakeInfo);
            if (ssl->toInfoOn)
                AddLateName("ClientKeyExchange", &ssl->timeoutInfo);
        #endif

        switch (ssl->specs.kea) {
        #ifndef NO_RSA
            case rsa_kea: 
            {
                word32 idx = 0;
                RsaKey key;
                byte   doUserRsa = 0;

                #ifdef HAVE_PK_CALLBACKS
                    if (ssl->ctx->RsaDecCb)
                        doUserRsa = 1;
                #endif

                ret = InitRsaKey(&key, ssl->heap);
                if (ret != 0) return ret;

                if (ssl->buffers.key.buffer)
                    ret = RsaPrivateKeyDecode(ssl->buffers.key.buffer, &idx,
                                             &key, ssl->buffers.key.length);
                else
                    return NO_PRIVATE_KEY;

                if (ret == 0) {
                    length = RsaEncryptSize(&key);
                    ssl->arrays->preMasterSz = SECRET_LEN;

                    if (ssl->options.tls) {
                        word16 check;

                        if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
                            return BUFFER_ERROR;

                        ato16(input + *inOutIdx, &check);
                        *inOutIdx += OPAQUE16_LEN;

                        if ((word32) check != length) {
                            CYASSL_MSG("RSA explicit size doesn't match");
                            FreeRsaKey(&key);
                            return RSA_PRIVATE_ERROR;
                        }
                    }

                    if ((*inOutIdx - begin) + length > size) {
                        CYASSL_MSG("RSA message too big");
                        FreeRsaKey(&key);
                        return BUFFER_ERROR;
                    }

                    if (doUserRsa) {
                        #ifdef HAVE_PK_CALLBACKS
                            ret = ssl->ctx->RsaDecCb(ssl,
                                        input + *inOutIdx, length, &out,
                                        ssl->buffers.key.buffer,
                                        ssl->buffers.key.length,
                                        ssl->RsaDecCtx);
                        #endif
                    }
                    else {
                        ret = RsaPrivateDecryptInline(input + *inOutIdx, length,
                                                                    &out, &key);
                    }

                    *inOutIdx += length;

                    if (ret == SECRET_LEN) {
                        XMEMCPY(ssl->arrays->preMasterSecret, out, SECRET_LEN);
                        if (ssl->arrays->preMasterSecret[0] !=
                                                           ssl->chVersion.major
                            || ssl->arrays->preMasterSecret[1] != 
                                                           ssl->chVersion.minor)
                            ret = PMS_VERSION_ERROR;
                        else
                            ret = MakeMasterSecret(ssl);
                    }
                    else {
                        ret = RSA_PRIVATE_ERROR;
                    }
                }

                FreeRsaKey(&key);
            }
            break;
        #endif
        #ifndef NO_PSK
            case psk_kea:
            {
                byte* pms = ssl->arrays->preMasterSecret;
                word16 ci_sz;

                if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
                    return BUFFER_ERROR;

                ato16(input + *inOutIdx, &ci_sz);
                *inOutIdx += OPAQUE16_LEN;

                if (ci_sz > MAX_PSK_ID_LEN)
                    return CLIENT_ID_ERROR;

                if ((*inOutIdx - begin) + ci_sz > size)
                    return BUFFER_ERROR;

                XMEMCPY(ssl->arrays->client_identity, input + *inOutIdx, ci_sz);
                *inOutIdx += ci_sz;

                ssl->arrays->client_identity[min(ci_sz, MAX_PSK_ID_LEN-1)] = 0;
                ssl->arrays->psk_keySz = ssl->options.server_psk_cb(ssl,
                    ssl->arrays->client_identity, ssl->arrays->psk_key,
                    MAX_PSK_KEY_LEN);

                if (ssl->arrays->psk_keySz == 0 || 
                                       ssl->arrays->psk_keySz > MAX_PSK_KEY_LEN)
                    return PSK_KEY_ERROR;
                
                /* make psk pre master secret */
                /* length of key + length 0s + length of key + key */
                c16toa((word16) ssl->arrays->psk_keySz, pms);
                pms += OPAQUE16_LEN;

                XMEMSET(pms, 0, ssl->arrays->psk_keySz);
                pms += ssl->arrays->psk_keySz;

                c16toa((word16) ssl->arrays->psk_keySz, pms);
                pms += OPAQUE16_LEN;

                XMEMCPY(pms, ssl->arrays->psk_key, ssl->arrays->psk_keySz);
                ssl->arrays->preMasterSz = ssl->arrays->psk_keySz * 2 + 4;

                ret = MakeMasterSecret(ssl);

                /* No further need for PSK */
                XMEMSET(ssl->arrays->psk_key, 0, ssl->arrays->psk_keySz);
                ssl->arrays->psk_keySz = 0;
            }
            break;
        #endif /* NO_PSK */
        #ifdef HAVE_NTRU
            case ntru_kea:
            {
                word16 cipherLen;
                word16 plainLen = sizeof(ssl->arrays->preMasterSecret);

                if (!ssl->buffers.key.buffer)
                    return NO_PRIVATE_KEY;

                if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
                    return BUFFER_ERROR;

                ato16(input + *inOutIdx, &cipherLen);
                *inOutIdx += OPAQUE16_LEN;

                if (cipherLen > MAX_NTRU_ENCRYPT_SZ)
                    return NTRU_KEY_ERROR;

                if ((*inOutIdx - begin) + cipherLen > size)
                    return BUFFER_ERROR;

                if (NTRU_OK != ntru_crypto_ntru_decrypt(
                            (word16) ssl->buffers.key.length,
                            ssl->buffers.key.buffer, cipherLen,
                            input + *inOutIdx, &plainLen,
                            ssl->arrays->preMasterSecret))
                    return NTRU_DECRYPT_ERROR;

                if (plainLen != SECRET_LEN)
                    return NTRU_DECRYPT_ERROR;

                *inOutIdx += cipherLen;

                ssl->arrays->preMasterSz = plainLen;
                ret = MakeMasterSecret(ssl);
            }
            break;
        #endif /* HAVE_NTRU */
        #ifdef HAVE_ECC
            case ecc_diffie_hellman_kea:
            {
                if ((*inOutIdx - begin) + OPAQUE8_LEN > size)
                    return BUFFER_ERROR;

                length = input[(*inOutIdx)++];

                if ((*inOutIdx - begin) + length > size)
                    return BUFFER_ERROR;

                if (ecc_import_x963(input + *inOutIdx, length, ssl->peerEccKey))
                    return ECC_PEERKEY_ERROR;

                *inOutIdx += length;
                ssl->peerEccKeyPresent = 1;

                length = sizeof(ssl->arrays->preMasterSecret);

                if (ssl->specs.static_ecdh) {
                    ecc_key staticKey;
                    word32 i = 0;

                    ecc_init(&staticKey);
                    ret = EccPrivateKeyDecode(ssl->buffers.key.buffer, &i,
                                           &staticKey, ssl->buffers.key.length);

                    if (ret == 0)
                        ret = ecc_shared_secret(&staticKey, ssl->peerEccKey,
                                         ssl->arrays->preMasterSecret, &length);

                    ecc_free(&staticKey);
                }
                else
                    ret = ecc_shared_secret(ssl->eccTempKey, ssl->peerEccKey,
                                         ssl->arrays->preMasterSecret, &length);

                if (ret != 0)
                    return ECC_SHARED_ERROR;

                ssl->arrays->preMasterSz = length;
                ret = MakeMasterSecret(ssl);
            }
            break;
        #endif /* HAVE_ECC */
        #ifndef NO_DH
            case diffie_hellman_kea:
            {
                word16 clientPubSz;
                DhKey  dhKey;

                if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
                    return BUFFER_ERROR;

                ato16(input + *inOutIdx, &clientPubSz);
                *inOutIdx += OPAQUE16_LEN;

                if ((*inOutIdx - begin) + clientPubSz > size)
                    return BUFFER_ERROR;

                InitDhKey(&dhKey);
                ret = DhSetKey(&dhKey, ssl->buffers.serverDH_P.buffer,
                                       ssl->buffers.serverDH_P.length,
                                       ssl->buffers.serverDH_G.buffer,
                                       ssl->buffers.serverDH_G.length);
                if (ret == 0)
                    ret = DhAgree(&dhKey, ssl->arrays->preMasterSecret,
                                         &ssl->arrays->preMasterSz,
                                          ssl->buffers.serverDH_Priv.buffer,
                                          ssl->buffers.serverDH_Priv.length,
                                          input + *inOutIdx, clientPubSz);
                FreeDhKey(&dhKey);

                *inOutIdx += clientPubSz;

                if (ret == 0)
                    ret = MakeMasterSecret(ssl);
            }
            break;
        #endif /* NO_DH */
        #if !defined(NO_DH) && !defined(NO_PSK)
            case dhe_psk_kea:
            {
                byte* pms = ssl->arrays->preMasterSecret;
                word16 clientSz;
                DhKey  dhKey;

                /* Read in the PSK hint */
                if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
                    return BUFFER_ERROR;

                ato16(input + *inOutIdx, &clientSz);
                *inOutIdx += OPAQUE16_LEN;
                if (clientSz > MAX_PSK_ID_LEN)
                    return CLIENT_ID_ERROR;

                if ((*inOutIdx - begin) + clientSz > size)
                    return BUFFER_ERROR;

                XMEMCPY(ssl->arrays->client_identity,
                                                   input + *inOutIdx, clientSz);
                *inOutIdx += clientSz;
                ssl->arrays->client_identity[min(clientSz, MAX_PSK_ID_LEN-1)] =
                                                                              0;

                /* Read in the DHE business */
                if ((*inOutIdx - begin) + OPAQUE16_LEN > size)
                    return BUFFER_ERROR;

                ato16(input + *inOutIdx, &clientSz);
                *inOutIdx += OPAQUE16_LEN;

                if ((*inOutIdx - begin) + clientSz > size)
                    return BUFFER_ERROR;

                InitDhKey(&dhKey);
                ret = DhSetKey(&dhKey, ssl->buffers.serverDH_P.buffer,
                                       ssl->buffers.serverDH_P.length,
                                       ssl->buffers.serverDH_G.buffer,
                                       ssl->buffers.serverDH_G.length);
                if (ret == 0)
                    ret = DhAgree(&dhKey, pms + OPAQUE16_LEN,
                                          &ssl->arrays->preMasterSz,
                                          ssl->buffers.serverDH_Priv.buffer,
                                          ssl->buffers.serverDH_Priv.length,
                                          input + *inOutIdx, clientSz);
                FreeDhKey(&dhKey);

                *inOutIdx += clientSz;
                c16toa((word16)ssl->arrays->preMasterSz, pms);
                ssl->arrays->preMasterSz += OPAQUE16_LEN;
                pms += ssl->arrays->preMasterSz;

                /* Use the PSK hint to look up the PSK and add it to the
                 * preMasterSecret here. */
                ssl->arrays->psk_keySz = ssl->options.server_psk_cb(ssl,
                    ssl->arrays->client_identity, ssl->arrays->psk_key,
                    MAX_PSK_KEY_LEN);

                if (ssl->arrays->psk_keySz == 0 ||
                                       ssl->arrays->psk_keySz > MAX_PSK_KEY_LEN)
                    return PSK_KEY_ERROR;

                c16toa((word16) ssl->arrays->psk_keySz, pms);
                pms += OPAQUE16_LEN;

                XMEMCPY(pms, ssl->arrays->psk_key, ssl->arrays->psk_keySz);
                ssl->arrays->preMasterSz +=
                                          ssl->arrays->psk_keySz + OPAQUE16_LEN;
                if (ret == 0)
                    ret = MakeMasterSecret(ssl);

                /* No further need for PSK */
                XMEMSET(ssl->arrays->psk_key, 0, ssl->arrays->psk_keySz);
                ssl->arrays->psk_keySz = 0;
            }
            break;
        #endif /* !NO_DH && !NO_PSK */
            default:
            {
                CYASSL_MSG("Bad kea type");
                ret = BAD_KEA_TYPE_E; 
            }
            break;
        }

        /* No further need for PMS */
        XMEMSET(ssl->arrays->preMasterSecret, 0, ssl->arrays->preMasterSz);
        ssl->arrays->preMasterSz = 0;

        if (ret == 0) {
            ssl->options.clientState = CLIENT_KEYEXCHANGE_COMPLETE;
            #ifndef NO_CERTS
                if (ssl->options.verifyPeer)
                    ret = BuildCertHashes(ssl, &ssl->certHashes);
            #endif
        }

        return ret;
    }

#endif /* NO_CYASSL_SERVER */
