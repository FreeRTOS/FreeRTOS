/* internal.c
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

#include <cyassl/internal.h>
#include <cyassl/error.h>
#include <cyassl/ctaocrypt/asn.h>

#ifdef HAVE_LIBZ
    #include "zlib.h"
#endif

#ifdef HAVE_NTRU
    #include "crypto_ntru.h"
#endif

#if defined(DEBUG_CYASSL) || defined(SHOW_SECRETS)
    #include <stdio.h>
#endif

#ifdef __sun
    #include <sys/filio.h>
#endif

#define TRUE  1
#define FALSE 0


#if defined(OPENSSL_EXTRA) && defined(NO_DH)
    #error OPENSSL_EXTRA needs DH, please remove NO_DH
#endif


#ifndef NO_CYASSL_CLIENT
    static int DoHelloVerifyRequest(CYASSL* ssl, const byte* input, word32*);
    static int DoServerHello(CYASSL* ssl, const byte* input, word32*);
    static int DoCertificateRequest(CYASSL* ssl, const byte* input, word32*);
    static int DoServerKeyExchange(CYASSL* ssl, const byte* input, word32*);
#endif


#ifndef NO_CYASSL_SERVER
    static int DoClientHello(CYASSL* ssl, const byte* input, word32*, word32,
                             word32);
    static int DoCertificateVerify(CYASSL* ssl, byte*, word32*, word32);
    static int DoClientKeyExchange(CYASSL* ssl, byte* input, word32*);
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

static void Hmac(CYASSL* ssl, byte* digest, const byte* buffer, word32 sz,
                 int content, int verify);

static void BuildCertHashes(CYASSL* ssl, Hashes* hashes);


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

    return 0;
}


#ifdef HAVE_NTRU

static byte GetEntropy(ENTROPY_CMD cmd, byte* out)
{
    /* TODO: add locking? */
    static RNG rng;

    if (cmd == INIT) {
        int ret = InitRng(&rng);
        if (ret == 0)
            return 1;
        else
            return 0;
    }

    if (out == NULL)
        return 0;

    if (cmd == GET_BYTE_OF_ENTROPY) {
        RNG_GenerateBlock(&rng, out, 1);
        return 1;
    }

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
    *u32 = 0;
    *u32 = (u24[0] << 16) | (u24[1] << 8) | u24[2];
}


/* convert opaque to 16 bit integer */
static INLINE void ato16(const byte* c, word16* u16)
{
    *u16 = 0;
    *u16 = (c[0] << 8) | (c[1]);
}


#ifdef CYASSL_DTLS

/* convert opaque to 32 bit integer */
static INLINE void ato32(const byte* c, word32* u32)
{
    *u32 = 0;
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

        if (deflateInit(&ssl->c_stream, 8) != Z_OK) return ZLIB_INIT_ERROR;

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
    static int Compress(CYASSL* ssl, byte* in, int inSz, byte* out, int outSz)
    {
        int    err;
        int    currTotal = ssl->c_stream.total_out;

        /* put size in front of compression */
        c16toa((word16)inSz, out);
        out   += 2;
        outSz -= 2;

        ssl->c_stream.next_in   = in;
        ssl->c_stream.avail_in  = inSz;
        ssl->c_stream.next_out  = out;
        ssl->c_stream.avail_out = outSz;

        err = deflate(&ssl->c_stream, Z_SYNC_FLUSH);
        if (err != Z_OK && err != Z_STREAM_END) return ZLIB_COMPRESS_ERROR;

        return ssl->c_stream.total_out - currTotal + sizeof(word16);
    }
        

    /* decompress in to out, returnn out size or error */
    static int DeCompress(CYASSL* ssl, byte* in, int inSz, byte* out, int outSz)
    {
        int    err;
        int    currTotal = ssl->d_stream.total_out;
        word16 len;

        /* find size in front of compression */
        ato16(in, &len);
        in   += 2;
        inSz -= 2;

        ssl->d_stream.next_in   = in;
        ssl->d_stream.avail_in  = inSz;
        ssl->d_stream.next_out  = out;
        ssl->d_stream.avail_out = outSz;

        err = inflate(&ssl->d_stream, Z_SYNC_FLUSH);
        if (err != Z_OK && err != Z_STREAM_END) return ZLIB_DECOMPRESS_ERROR;

        return ssl->d_stream.total_out - currTotal;
    }
        
#endif /* HAVE_LIBZ */


void InitSSL_Method(CYASSL_METHOD* method, ProtocolVersion pv)
{
    method->version    = pv;
    method->side       = CLIENT_END;
    method->verifyPeer = 0;
    method->verifyNone = 0;
    method->failNoCert = 0;
    method->downgrade  = 0;
}


/* Initialze SSL context, return 0 on success */
int InitSSL_Ctx(CYASSL_CTX* ctx, CYASSL_METHOD* method)
{
    ctx->method = method;
    ctx->refCount = 1;          /* so either CTX_free or SSL_free can release */
    ctx->certificate.buffer = 0;
    ctx->certChain.buffer   = 0;
    ctx->privateKey.buffer  = 0;
    ctx->serverDH_P.buffer  = 0;
    ctx->serverDH_G.buffer  = 0;
    ctx->haveDH             = 0;
    ctx->haveNTRU           = 0;    /* start off */
    ctx->haveECDSA          = 0;    /* start off */
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

#ifdef OPENSSL_EXTRA
    ctx->passwd_cb   = 0;
    ctx->userdata    = 0;
#endif /* OPENSSL_EXTRA */

    ctx->timeout = DEFAULT_TIMEOUT;

#ifndef CYASSL_USER_IO
    ctx->CBIORecv = EmbedReceive;
    ctx->CBIOSend = EmbedSend;
#else
    /* user will set */
    ctx->CBIORecv = NULL;
    ctx->CBIOSend = NULL;
#endif
    ctx->partialWrite   = 0;
    ctx->verifyCallback = 0;

    ctx->cm = CyaSSL_CertManagerNew();
#ifdef HAVE_NTRU
    if (method->side == CLIENT_END)
        ctx->haveNTRU = 1;           /* always on cliet side */
                                     /* server can turn on by loading key */
#endif
#ifdef HAVE_ECC
    if (method->side == CLIENT_END) {
        ctx->haveECDSA     = 1;        /* always on cliet side */
        ctx->haveStaticECC = 1;        /* server can turn on by loading key */
    }
#endif
    ctx->suites.setSuites = 0;  /* user hasn't set yet */
    /* remove DH later if server didn't set, add psk later */
    InitSuites(&ctx->suites, method->version, TRUE, FALSE, ctx->haveNTRU,
               ctx->haveECDSA, ctx->haveStaticECC, method->side);  
    ctx->verifyPeer = 0;
    ctx->verifyNone = 0;
    ctx->failNoCert = 0;
    ctx->sessionCacheOff      = 0;  /* initially on */
    ctx->sessionCacheFlushOff = 0;  /* initially on */
    ctx->sendVerify = 0;
    ctx->quietShutdown = 0;
    ctx->groupMessages = 0;
#ifdef HAVE_OCSP
    CyaSSL_OCSP_Init(&ctx->ocsp);
#endif

    if (InitMutex(&ctx->countMutex) < 0) {
        CYASSL_MSG("Mutex error on CTX init");
        return BAD_MUTEX_ERROR;
    } 
    if (ctx->cm == NULL) {
        CYASSL_MSG("Bad Cert Manager New");
        return BAD_CERT_MANAGER_ERROR;
    }
    return 0;
}


/* In case contexts are held in array and don't want to free actual ctx */
void SSL_CtxResourceFree(CYASSL_CTX* ctx)
{
    XFREE(ctx->serverDH_G.buffer, ctx->heap, DYNAMIC_TYPE_DH);
    XFREE(ctx->serverDH_P.buffer, ctx->heap, DYNAMIC_TYPE_DH);
    XFREE(ctx->privateKey.buffer, ctx->heap, DYNAMIC_TYPE_KEY);
    XFREE(ctx->certificate.buffer, ctx->heap, DYNAMIC_TYPE_CERT);
    XFREE(ctx->certChain.buffer, ctx->heap, DYNAMIC_TYPE_CERT);
    XFREE(ctx->method, ctx->heap, DYNAMIC_TYPE_METHOD);

    CyaSSL_CertManagerFree(ctx->cm);

#ifdef HAVE_OCSP
    CyaSSL_OCSP_Cleanup(&ctx->ocsp);
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
        XFREE(ctx, ctx->heap, DYNAMIC_TYPE_CTX);
    }
    else {
        (void)ctx;
        CYASSL_MSG("CTX ref count not 0 yet, no free");
    }
}

    
void InitSuites(Suites* suites, ProtocolVersion pv, byte haveDH, byte havePSK,
                byte haveNTRU, byte haveStaticECC, byte haveECDSA, int side)
{
    word16 idx = 0;
    int    tls    = pv.major == SSLv3_MAJOR && pv.minor >= TLSv1_MINOR;
    int    tls1_2 = pv.major == SSLv3_MAJOR && pv.minor >= TLSv1_2_MINOR;
    int    haveRSA = 1;

    (void)tls;  /* shut up compiler */
    (void)haveDH;
    (void)havePSK;
    (void)haveNTRU;
    (void)haveStaticECC;

    if (suites->setSuites)
        return;      /* trust user settings, don't override */

    if (side == SERVER_END && haveECDSA)
        haveRSA = 0;   /* can't do RSA with ECDSA cert */

#ifdef CYASSL_DTLS
    if (pv.major == DTLS_MAJOR && pv.minor == DTLS_MINOR)
        tls = 1;
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

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA
    if (tls && haveECDSA) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA
    if (tls && haveECDSA && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA
    if (tls && haveECDSA) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA
    if (tls && haveECDSA && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_RC4_128_SHA
    if (tls && haveECDSA) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDHE_ECDSA_WITH_RC4_128_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_RC4_128_SHA
    if (tls && haveECDSA && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDH_ECDSA_WITH_RC4_128_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA
    if (tls && haveECDSA) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA
    if (tls && haveECDSA && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA
    if (tls && haveRSA) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_256_CBC_SHA
    if (tls && haveRSA && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDH_RSA_WITH_AES_256_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA
    if (tls && haveRSA) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_ECDH_RSA_WITH_AES_128_CBC_SHA
    if (tls && haveRSA && haveStaticECC) {
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
    if (tls && haveRSA && haveStaticECC) {
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
    if (tls && haveRSA && haveStaticECC) {
        suites->suites[idx++] = ECC_BYTE; 
        suites->suites[idx++] = TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_256_CBC_SHA256
    if (tls1_2 && haveDH && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_DHE_RSA_WITH_AES_256_CBC_SHA256;
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

#ifdef BUILD_TLS_RSA_WITH_AES_256_CBC_SHA256
    if (tls1_2 && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_AES_256_CBC_SHA256;
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

#ifdef BUILD_TLS_PSK_WITH_AES_256_CBC_SHA
    if (tls && havePSK) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_PSK_WITH_AES_256_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CBC_SHA
    if (tls && havePSK) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_PSK_WITH_AES_128_CBC_SHA;
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

#ifdef BUILD_TLS_RSA_WITH_HC_128_CBC_MD5
    if (tls && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_HC_128_CBC_MD5;
    }
#endif
    
#ifdef BUILD_TLS_RSA_WITH_HC_128_CBC_SHA
    if (tls && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_HC_128_CBC_SHA;
    }
#endif

#ifdef BUILD_TLS_RSA_WITH_RABBIT_CBC_SHA
    if (tls && haveRSA) {
        suites->suites[idx++] = 0; 
        suites->suites[idx++] = TLS_RSA_WITH_RABBIT_CBC_SHA;
    }
#endif

    suites->suiteSz = idx;
}


int InitSSL(CYASSL* ssl, CYASSL_CTX* ctx)
{
    int  ret;
    byte havePSK = 0;

    ssl->ctx     = ctx; /* only for passing to calls, options could change */
    ssl->version = ctx->method->version;
    ssl->suites  = ctx->suites;

#ifdef HAVE_LIBZ
    ssl->didStreamInit = 0;
#endif
   
    ssl->buffers.certificate.buffer   = 0;
    ssl->buffers.key.buffer           = 0;
    ssl->buffers.certChain.buffer     = 0;
    ssl->buffers.inputBuffer.length   = 0;
    ssl->buffers.inputBuffer.idx      = 0;
    ssl->buffers.inputBuffer.buffer = ssl->buffers.inputBuffer.staticBuffer;
    ssl->buffers.inputBuffer.bufferSize  = STATIC_BUFFER_LEN;
    ssl->buffers.inputBuffer.dynamicFlag = 0;
    ssl->buffers.outputBuffer.length  = 0;
    ssl->buffers.outputBuffer.idx     = 0;
    ssl->buffers.outputBuffer.buffer = ssl->buffers.outputBuffer.staticBuffer;
    ssl->buffers.outputBuffer.bufferSize  = STATIC_BUFFER_LEN;
    ssl->buffers.outputBuffer.dynamicFlag = 0;
    ssl->buffers.domainName.buffer    = 0;
    ssl->buffers.serverDH_P.buffer    = 0;
    ssl->buffers.serverDH_G.buffer    = 0;
    ssl->buffers.serverDH_Pub.buffer  = 0;
    ssl->buffers.serverDH_Priv.buffer = 0;
    ssl->buffers.clearOutputBuffer.buffer  = 0;
    ssl->buffers.clearOutputBuffer.length  = 0;
    ssl->buffers.prevSent                  = 0;
    ssl->buffers.plainSz                   = 0;

#ifdef OPENSSL_EXTRA
    ssl->peerCert.derCert.buffer = 0;
#endif

#ifdef HAVE_ECC
    ssl->eccTempKeySz = ctx->eccTempKeySz;
    ssl->peerEccKeyPresent = 0;
    ssl->peerEccDsaKeyPresent = 0;
    ssl->eccDsaKeyPresent = 0;
    ssl->eccTempKeyPresent = 0;
    ecc_init(&ssl->peerEccKey);
    ecc_init(&ssl->peerEccDsaKey);
    ecc_init(&ssl->eccDsaKey);
    ecc_init(&ssl->eccTempKey);
#endif

    ssl->timeout = ctx->timeout;
    ssl->rfd = -1;   /* set to invalid descriptor */
    ssl->wfd = -1;
    ssl->biord = 0;
    ssl->biowr = 0;

    ssl->IOCB_ReadCtx  = &ssl->rfd;   /* prevent invalid pointer acess if not */
    ssl->IOCB_WriteCtx = &ssl->wfd;   /* correctly set */

    /* increment CTX reference count */
    if (LockMutex(&ctx->countMutex) != 0) {
        CYASSL_MSG("Couldn't lock CTX count mutex");
        return BAD_MUTEX_ERROR;
    }
    ctx->refCount++;
    UnLockMutex(&ctx->countMutex);

    if ( (ret = InitRng(&ssl->rng)) != 0)
        return ret;

    InitMd5(&ssl->hashMd5);
    InitSha(&ssl->hashSha);
#ifndef NO_SHA256
    InitSha256(&ssl->hashSha256);
#endif
    InitRsaKey(&ssl->peerRsaKey, ctx->heap);

    ssl->verifyCallback    = ctx->verifyCallback;
    ssl->peerRsaKeyPresent = 0;
    ssl->options.side      = ctx->method->side;
    ssl->options.downgrade = ctx->method->downgrade;
    ssl->error = 0;
    ssl->options.connReset = 0;
    ssl->options.isClosed  = 0;
    ssl->options.closeNotify  = 0;
    ssl->options.sentNotify   = 0;
    ssl->options.usingCompression = 0;
    if (ssl->options.side == SERVER_END)
        ssl->options.haveDH = ctx->haveDH;
    else
        ssl->options.haveDH = 0;
    ssl->options.haveNTRU  = ctx->haveNTRU;
    ssl->options.haveECDSA = ctx->haveECDSA;
    ssl->options.haveStaticECC = ctx->haveStaticECC;
    ssl->options.havePeerCert  = 0; 
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
    ssl->keys.dtls_sequence_number       = 0;
    ssl->keys.dtls_peer_sequence_number  = 0;
    ssl->keys.dtls_handshake_number      = 0;
    ssl->keys.dtls_epoch      = 0;
    ssl->keys.dtls_peer_epoch = 0;
#endif
    ssl->keys.encryptionOn = 0;     /* initially off */
    ssl->options.sessionCacheOff      = ctx->sessionCacheOff;
    ssl->options.sessionCacheFlushOff = ctx->sessionCacheFlushOff;

    ssl->options.verifyPeer = ctx->verifyPeer;
    ssl->options.verifyNone = ctx->verifyNone;
    ssl->options.failNoCert = ctx->failNoCert;
    ssl->options.sendVerify = ctx->sendVerify;
    
    ssl->options.resuming = 0;
    ssl->options.haveSessionId = 0;
    ssl->hmac = Hmac;         /* default to SSLv3 */
    ssl->heap = ctx->heap;    /* defaults to self */
    ssl->options.tls    = 0;
    ssl->options.tls1_1 = 0;
    ssl->options.dtls   = 0;
    ssl->options.partialWrite  = ctx->partialWrite;
    ssl->options.quietShutdown = ctx->quietShutdown;
    ssl->options.certOnly = 0;
    ssl->options.groupMessages = ctx->groupMessages;

    /* ctx still owns certificate, certChain, key, dh, and cm */
    ssl->buffers.certificate = ctx->certificate;
    ssl->buffers.certChain = ctx->certChain;
    ssl->buffers.key = ctx->privateKey;
    if (ssl->options.side == SERVER_END) {
        ssl->buffers.serverDH_P = ctx->serverDH_P;
        ssl->buffers.serverDH_G = ctx->serverDH_G;
    }
    ssl->buffers.weOwnCert = 0;
    ssl->buffers.weOwnKey  = 0;
    ssl->buffers.weOwnDH   = 0;

#ifdef OPENSSL_EXTRA
    ssl->peerCert.issuer.sz    = 0;
    ssl->peerCert.subject.sz   = 0;
#endif
   
    /* make sure server has cert and key unless using PSK */
    if (ssl->options.side == SERVER_END && !havePSK)
        if (!ssl->buffers.certificate.buffer || !ssl->buffers.key.buffer) {
            CYASSL_MSG("Server missing certificate and/or private key"); 
            return NO_PRIVATE_KEY;
        }

#ifndef NO_PSK
    ssl->arrays.client_identity[0] = 0;
    if (ctx->server_hint[0]) {   /* set in CTX */
        XSTRNCPY(ssl->arrays.server_hint, ctx->server_hint, MAX_PSK_ID_LEN);
        ssl->arrays.server_hint[MAX_PSK_ID_LEN - 1] = '\0';
    }
    else
        ssl->arrays.server_hint[0] = 0;
#endif /* NO_PSK */

#ifdef CYASSL_CALLBACKS
    ssl->hsInfoOn = 0;
    ssl->toInfoOn = 0;
#endif

    /* make sure server has DH parms, and add PSK if there, add NTRU too */
    if (ssl->options.side == SERVER_END) 
        InitSuites(&ssl->suites, ssl->version,ssl->options.haveDH, havePSK,
                   ssl->options.haveNTRU, ssl->options.haveECDSA,
                   ssl->options.haveStaticECC, ssl->ctx->method->side);
    else 
        InitSuites(&ssl->suites, ssl->version, TRUE, havePSK,
                   ssl->options.haveNTRU, ssl->options.haveECDSA,
                   ssl->options.haveStaticECC, ssl->ctx->method->side);


#ifdef SESSION_CERTS
    ssl->session.chain.count = 0;
#endif

    ssl->cipher.ssl = ssl;

#ifdef FORTRESS
    ssl->ex_data[0] = 0;
    ssl->ex_data[1] = 0;
    ssl->ex_data[2] = 0;
#endif

    return 0;
}


/* In case holding SSL object in array and don't want to free actual ssl */
void SSL_ResourceFree(CYASSL* ssl)
{
    XFREE(ssl->buffers.serverDH_Priv.buffer, ssl->heap, DYNAMIC_TYPE_DH);
    XFREE(ssl->buffers.serverDH_Pub.buffer, ssl->heap, DYNAMIC_TYPE_DH);
    /* parameters (p,g) may be owned by ctx */
    if (ssl->buffers.weOwnDH) {
        XFREE(ssl->buffers.serverDH_G.buffer, ssl->heap, DYNAMIC_TYPE_DH);
        XFREE(ssl->buffers.serverDH_P.buffer, ssl->heap, DYNAMIC_TYPE_DH);
    }
    XFREE(ssl->buffers.domainName.buffer, ssl->heap, DYNAMIC_TYPE_DOMAIN);

    /* CYASSL_CTX always owns certChain */
    if (ssl->buffers.weOwnCert)
        XFREE(ssl->buffers.certificate.buffer, ssl->heap, DYNAMIC_TYPE_CERT);
    if (ssl->buffers.weOwnKey)
        XFREE(ssl->buffers.key.buffer, ssl->heap, DYNAMIC_TYPE_KEY);

    FreeRsaKey(&ssl->peerRsaKey);
    if (ssl->buffers.inputBuffer.dynamicFlag)
        ShrinkInputBuffer(ssl, FORCED_FREE);
    if (ssl->buffers.outputBuffer.dynamicFlag)
        ShrinkOutputBuffer(ssl);
#if defined(OPENSSL_EXTRA) || defined(GOAHEAD_WS)
    XFREE(ssl->peerCert.derCert.buffer, ssl->heap, DYNAMIC_TYPE_CERT);
    CyaSSL_BIO_free(ssl->biord);
    if (ssl->biord != ssl->biowr)        /* in case same as write */
        CyaSSL_BIO_free(ssl->biowr);
#endif
#ifdef HAVE_LIBZ
    FreeStreams(ssl);
#endif
#ifdef HAVE_ECC
    ecc_free(&ssl->peerEccKey);
    ecc_free(&ssl->peerEccDsaKey);
    ecc_free(&ssl->eccTempKey);
    ecc_free(&ssl->eccDsaKey);
#endif
}


void FreeSSL(CYASSL* ssl)
{
    FreeSSL_Ctx(ssl->ctx);  /* will decrement and free underyling CTX if 0 */
    SSL_ResourceFree(ssl);
    XFREE(ssl, ssl->heap, DYNAMIC_TYPE_SSL);
}


ProtocolVersion MakeSSLv3(void)
{
    ProtocolVersion pv;
    pv.major = SSLv3_MAJOR;
    pv.minor = SSLv3_MINOR;

    return pv;
}


#ifdef CYASSL_DTLS

ProtocolVersion MakeDTLSv1(void)
{
    ProtocolVersion pv;
    pv.major = DTLS_MAJOR;
    pv.minor = DTLS_MINOR;

    return pv;
}

#endif /* CYASSL_DTLS */




#ifdef USE_WINDOWS_API 

    timer_d Timer(void)
    {
        static int           init = 0;
        static LARGE_INTEGER freq;
        LARGE_INTEGER        count;
    
        if (!init) {
            QueryPerformanceFrequency(&freq);
            init = 1;
        }

        QueryPerformanceCounter(&count);

        return (double)count.QuadPart / freq.QuadPart;
    }


    word32 LowResTimer(void)
    {
        return (word32)Timer();
    }


#elif defined(THREADX)

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

#elif defined(USER_TICKS)

    word32 LowResTimer(void)
    {
        /*
        write your own clock tick function if don't want time(0)
        needs second accuracy but doesn't have to correlated to EPOCH
        */
    }

#else /* !USE_WINDOWS_API && !THREADX && !MICRIUM && !USER_TICKS */

    #include <time.h>

    word32 LowResTimer(void)
    {
        return time(0); 
    }


#endif /* USE_WINDOWS_API */


/* add output to md5 and sha handshake hashes, exclude record header */
static void HashOutput(CYASSL* ssl, const byte* output, int sz, int ivSz)
{
    const byte* adj = output + RECORD_HEADER_SZ + ivSz;
    sz -= RECORD_HEADER_SZ;
    
#ifdef CYASSL_DTLS
    if (ssl->options.dtls) {
        adj += DTLS_RECORD_EXTRA;
        sz  -= DTLS_RECORD_EXTRA;
    }
#endif

    Md5Update(&ssl->hashMd5, adj, sz);
    ShaUpdate(&ssl->hashSha, adj, sz);
#ifndef NO_SHA256
    if (IsAtLeastTLSv1_2(ssl))
        Sha256Update(&ssl->hashSha256, adj, sz);
#endif
}


/* add input to md5 and sha handshake hashes, include handshake header */
static void HashInput(CYASSL* ssl, const byte* input, int sz)
{
    const byte* adj = input - HANDSHAKE_HEADER_SZ;
    sz += HANDSHAKE_HEADER_SZ;
    
#ifdef CYASSL_DTLS
    if (ssl->options.dtls) {
        adj -= DTLS_HANDSHAKE_EXTRA;
        sz  += DTLS_HANDSHAKE_EXTRA;
    }
#endif

    Md5Update(&ssl->hashMd5, adj, sz);
    ShaUpdate(&ssl->hashSha, adj, sz);
#ifndef NO_SHA256
    if (IsAtLeastTLSv1_2(ssl))
        Sha256Update(&ssl->hashSha256, adj, sz);
#endif
}


/* add record layer header for message */
static void AddRecordHeader(byte* output, word32 length, byte type, CYASSL* ssl)
{
    RecordLayerHeader* rl;
  
    /* record layer header */
    rl = (RecordLayerHeader*)output;
    rl->type    = type;
    rl->version = ssl->version;           /* type and version same in each */

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

retry:
    recvd = ssl->ctx->CBIORecv((char *)buf, (int)sz, ssl->IOCB_ReadCtx);
    if (recvd < 0)
        switch (recvd) {
            case IO_ERR_GENERAL:        /* general/unknown error */
                return -1;

            case IO_ERR_WANT_READ:      /* want read, would block */
                return WANT_READ;

            case IO_ERR_CONN_RST:       /* connection reset */
                ssl->options.connReset = 1;
                return -1;

            case IO_ERR_ISR:            /* interrupt */
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

            case IO_ERR_CONN_CLOSE:     /* peer closed connection */
                ssl->options.isClosed = 1;
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
    XFREE(ssl->buffers.outputBuffer.buffer, ssl->heap, DYNAMIC_TYPE_OUT_BUFFER);
    ssl->buffers.outputBuffer.buffer = ssl->buffers.outputBuffer.staticBuffer;
    ssl->buffers.outputBuffer.bufferSize  = STATIC_BUFFER_LEN;
    ssl->buffers.outputBuffer.dynamicFlag = 0;
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

    XFREE(ssl->buffers.inputBuffer.buffer, ssl->heap, DYNAMIC_TYPE_IN_BUFFER);
    ssl->buffers.inputBuffer.buffer = ssl->buffers.inputBuffer.staticBuffer;
    ssl->buffers.inputBuffer.bufferSize  = STATIC_BUFFER_LEN;
    ssl->buffers.inputBuffer.dynamicFlag = 0;
    ssl->buffers.inputBuffer.idx = 0;
    ssl->buffers.inputBuffer.length = usedLength;
}


int SendBuffered(CYASSL* ssl)
{
    while (ssl->buffers.outputBuffer.length > 0) {
        int sent = ssl->ctx->CBIOSend((char*)ssl->buffers.outputBuffer.buffer +
                                      ssl->buffers.outputBuffer.idx,
                                      (int)ssl->buffers.outputBuffer.length,
                                      ssl->IOCB_WriteCtx);
        if (sent < 0) {
            switch (sent) {

                case IO_ERR_WANT_WRITE:        /* would block */
                    return WANT_WRITE;

                case IO_ERR_CONN_RST:          /* connection reset */
                    ssl->options.connReset = 1;
                    break;

                case IO_ERR_ISR:               /* interrupt */
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

                case IO_ERR_CONN_CLOSE: /* epipe / conn closed, same as reset */
                    ssl->options.connReset = 1;
                    break;

                default:
                    return SOCKET_ERROR_E;
            }

            return SOCKET_ERROR_E;
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
    byte* tmp = (byte*) XMALLOC(size + ssl->buffers.outputBuffer.length,
                                ssl->heap, DYNAMIC_TYPE_OUT_BUFFER);
    CYASSL_MSG("growing output buffer\n");
   
    if (!tmp) return MEMORY_E;

    if (ssl->buffers.outputBuffer.length)
        XMEMCPY(tmp, ssl->buffers.outputBuffer.buffer,
               ssl->buffers.outputBuffer.length);

    if (ssl->buffers.outputBuffer.dynamicFlag)
        XFREE(ssl->buffers.outputBuffer.buffer, ssl->heap,
              DYNAMIC_TYPE_OUT_BUFFER);
    ssl->buffers.outputBuffer.dynamicFlag = 1;
    ssl->buffers.outputBuffer.buffer = tmp;
    ssl->buffers.outputBuffer.bufferSize = size +
                                           ssl->buffers.outputBuffer.length; 
    return 0;
}


/* Grow the input buffer, should only be to read cert or big app data */
static INLINE int GrowInputBuffer(CYASSL* ssl, int size, int usedLength)
{
    byte* tmp = (byte*) XMALLOC(size + usedLength, ssl->heap,
                                DYNAMIC_TYPE_IN_BUFFER);
    CYASSL_MSG("growing input buffer\n");
   
    if (!tmp) return MEMORY_E;

    if (usedLength)
        XMEMCPY(tmp, ssl->buffers.inputBuffer.buffer +
                    ssl->buffers.inputBuffer.idx, usedLength);

    if (ssl->buffers.inputBuffer.dynamicFlag)
        XFREE(ssl->buffers.inputBuffer.buffer,ssl->heap,DYNAMIC_TYPE_IN_BUFFER);

    ssl->buffers.inputBuffer.dynamicFlag = 1;
    ssl->buffers.inputBuffer.buffer = tmp;
    ssl->buffers.inputBuffer.bufferSize = size + usedLength;
    ssl->buffers.inputBuffer.idx    = 0;
    ssl->buffers.inputBuffer.length = usedLength;

    return 0;
}


/* check avalaible size into output buffer, make room if needed */
static INLINE int CheckAvalaibleSize(CYASSL *ssl, int size)
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
        *inOutIdx += 4;  /* skip epoch and first 2 seq bytes for now */
        ato32(input + *inOutIdx, &ssl->keys.dtls_peer_sequence_number);
        *inOutIdx += 4;  /* advance past rest of seq */
        ato16(input + *inOutIdx, size);
        *inOutIdx += LENGTH_SZ;
#endif
    }

    /* catch version mismatch */
    if (rh->version.major != ssl->version.major || 
        rh->version.minor != ssl->version.minor) {
        
        if (ssl->options.side == SERVER_END &&
            ssl->options.acceptState == ACCEPT_BEGIN)
            CYASSL_MSG("Client attempting to connect with different version"); 
        else if (ssl->options.side == CLIENT_END && ssl->options.downgrade &&
                 ssl->options.connectState < FIRST_REPLY_DONE)
            CYASSL_MSG("Server attempting to accept with different version"); 
        else {
            CYASSL_MSG("SSL version error"); 
            return VERSION_ERROR;              /* only use requested version */
        }
    }

    /* record layer length check */
    if (*size > (MAX_RECORD_SIZE + MAX_COMP_EXTRA + MAX_MSG_EXTRA))
        return LENGTH_ERROR;

    /* verify record type here as well */
    switch ((enum ContentType)rh->type) {
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

    return 0;
}


static int GetHandShakeHeader(CYASSL* ssl, const byte* input, word32* inOutIdx,
                              byte *type, word32 *size)
{
    const byte *ptr = input + *inOutIdx;
    (void)ssl;
    *inOutIdx += HANDSHAKE_HEADER_SZ;
    
#ifdef CYASSL_DTLS
    if (ssl->options.dtls)
        *inOutIdx += DTLS_HANDSHAKE_EXTRA;
#endif

    *type = ptr[0];
    c24to32(&ptr[1], size);

    return 0;
}


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
    Md5Update(&ssl->hashMd5, ssl->arrays.masterSecret, SECRET_LEN);
    Md5Update(&ssl->hashMd5, PAD1, PAD_MD5);
    Md5Final(&ssl->hashMd5, md5_result);

    /* make md5 outer */
    Md5Update(&ssl->hashMd5, ssl->arrays.masterSecret, SECRET_LEN);
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
    ShaUpdate(&ssl->hashSha, ssl->arrays.masterSecret, SECRET_LEN);
    ShaUpdate(&ssl->hashSha, PAD1, PAD_SHA);
    ShaFinal(&ssl->hashSha, sha_result);

    /* make sha outer */
    ShaUpdate(&ssl->hashSha, ssl->arrays.masterSecret, SECRET_LEN);
    ShaUpdate(&ssl->hashSha, PAD2, PAD_SHA);
    ShaUpdate(&ssl->hashSha, sha_result, SHA_DIGEST_SIZE);

    ShaFinal(&ssl->hashSha, hashes->sha);
}


static void BuildFinished(CYASSL* ssl, Hashes* hashes, const byte* sender)
{
    /* store current states, building requires get_digest which resets state */
    Md5 md5 = ssl->hashMd5;
    Sha sha = ssl->hashSha;
#ifndef NO_SHA256
    Sha256 sha256;
    InitSha256(&sha256);
    if (IsAtLeastTLSv1_2(ssl))
        sha256 = ssl->hashSha256;
#endif

    if (ssl->options.tls)
        BuildTlsFinished(ssl, hashes, sender);
    else {
        BuildMD5(ssl, hashes, sender);
        BuildSHA(ssl, hashes, sender);
    }
    
    /* restore */
    ssl->hashMd5 = md5;
    ssl->hashSha = sha;
#ifndef NO_SHA256
    if (IsAtLeastTLSv1_2(ssl))
        ssl->hashSha256 = sha256;
#endif
}


static int DoCertificate(CYASSL* ssl, byte* input, word32* inOutIdx)
{
    word32 listSz, i = *inOutIdx;
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
    c24to32(&input[i], &listSz);
    i += CERT_HEADER_SZ;

    CYASSL_MSG("Loading peer's cert chain");
    /* first put cert chain into buffer so can verify top down
       we're sent bottom up */
    while (listSz) {
        /* cert size */
        word32 certSz;

        if (totalCerts >= MAX_CHAIN_DEPTH)
            return BUFFER_E;

        c24to32(&input[i], &certSz);
        i += CERT_HEADER_SZ;
       
        if (listSz > MAX_RECORD_SIZE || certSz > MAX_RECORD_SIZE)
            return BUFFER_E;

        certs[totalCerts].length = certSz;
        certs[totalCerts].buffer = input + i;

#ifdef SESSION_CERTS
        if (ssl->session.chain.count < MAX_CHAIN_DEPTH &&
                                       certSz < MAX_X509_SIZE) {
            ssl->session.chain.certs[ssl->session.chain.count].length = certSz;
            XMEMCPY(ssl->session.chain.certs[ssl->session.chain.count].buffer,
                    input + i, certSz);
            ssl->session.chain.count++;
        } else {
            CYASSL_MSG("Couldn't store chain cert for session");
        }
#endif

        i += certSz;
        listSz -= certSz + CERT_HEADER_SZ;

        totalCerts++;
        CYASSL_MSG("    Put another cert into chain");
    }

    count = totalCerts;

    /* verify up to peer's first */
    while (count > 1) {
        buffer myCert = certs[count - 1];
        DecodedCert dCert;

        InitDecodedCert(&dCert, myCert.buffer, myCert.length, ssl->heap);
        ret = ParseCertRelative(&dCert, CERT_TYPE, !ssl->options.verifyNone,
                                ssl->ctx->cm);
        if (ret == 0 && dCert.isCA == 0) {
            CYASSL_MSG("Chain cert is not a CA, not adding as one");
            (void)ret;
        }
        else if (ret == 0 && ssl->options.verifyNone) {
            CYASSL_MSG("Chain cert not verified by option, not adding as CA");
            (void)ret;
        }
        else if (ret == 0 && !AlreadySigner(ssl->ctx->cm, dCert.subjectHash)) {
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
            (void)ret;
        }
        else {
            CYASSL_MSG("Verified CA from chain and already had it");
            (void)ret;
        }

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

        CYASSL_MSG("Veriying Peer's cert");

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
                CYASSL_MSG("\tCallback override availalbe, will continue");
                fatal = 0;
            }
            else {
                CYASSL_MSG("\tNo callback override availalbe, fatal");
                fatal = 1;
            }
        }

#ifdef HAVE_OCSP
        if (CyaSSL_OCSP_Lookup_Cert(&ssl->ctx->ocsp, &dCert) == CERT_REVOKED) {
            CYASSL_MSG("\tOCSP Lookup returned revoked");
            ret = OCSP_CERT_REVOKED;
            fatal = 0;
        }
#endif

#ifdef HAVE_CRL
        if (ssl->ctx->cm->crlEnabled) {
            ret = CheckCertCRL(ssl->ctx->cm->crl, &dCert);

            if (ret != 0) {
                CYASSL_MSG("\tCRL check not ok");
                fatal = 0;
            }
        }
#endif /* HAVE_CRL */

#ifdef OPENSSL_EXTRA
        /* set X509 format for peer cert even if fatal */
        XSTRNCPY(ssl->peerCert.issuer.name, dCert.issuer, ASN_NAME_MAX);
        ssl->peerCert.issuer.name[ASN_NAME_MAX - 1] = '\0';
        ssl->peerCert.issuer.sz = (int)XSTRLEN(ssl->peerCert.issuer.name) + 1;

        XSTRNCPY(ssl->peerCert.subject.name, dCert.subject, ASN_NAME_MAX);
        ssl->peerCert.subject.name[ASN_NAME_MAX - 1] = '\0';
        ssl->peerCert.subject.sz = (int)XSTRLEN(ssl->peerCert.subject.name) + 1;

        XMEMCPY(ssl->peerCert.serial, dCert.serial, EXTERNAL_SERIAL_SIZE);
        ssl->peerCert.serialSz = dCert.serialSz;
        if (dCert.subjectCNLen < ASN_NAME_MAX) {
            XMEMCPY(ssl->peerCert.subjectCN,dCert.subjectCN,dCert.subjectCNLen);
            ssl->peerCert.subjectCN[dCert.subjectCNLen] = '\0';
        }
        else
            ssl->peerCert.subjectCN[0] = '\0';

        /* store cert for potential retrieval */
        ssl->peerCert.derCert.buffer = (byte*)XMALLOC(myCert.length, ssl->heap,
                                                      DYNAMIC_TYPE_CERT);
        if (ssl->peerCert.derCert.buffer == NULL)
            return MEMORY_E;
        XMEMCPY(ssl->peerCert.derCert.buffer, myCert.buffer, myCert.length);
        ssl->peerCert.derCert.length = myCert.length;
#endif    

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

        if (!ssl->options.verifyNone && ssl->buffers.domainName.buffer)
            if (XSTRNCMP((char*)ssl->buffers.domainName.buffer,
                        dCert.subjectCN,
                        ssl->buffers.domainName.length - 1)) {
                ret = DOMAIN_NAME_MISMATCH;   /* try to get peer key still */
            }

        /* decode peer key */
        if (dCert.keyOID == RSAk) {
            word32 idx = 0;
            if (RsaPublicKeyDecode(dCert.publicKey, &idx,
                               &ssl->peerRsaKey, dCert.pubKeySize) != 0) {
                ret = PEER_KEY_ERROR;
            }
            else
                ssl->peerRsaKeyPresent = 1;
        }
#ifdef HAVE_NTRU
        else if (dCert.keyOID == NTRUk) {
            if (dCert.pubKeySize > sizeof(ssl->peerNtruKey)) {
                ret = PEER_KEY_ERROR;
            }
            else {
                XMEMCPY(ssl->peerNtruKey, dCert.publicKey, dCert.pubKeySize);
                ssl->peerNtruKeyLen = (word16)dCert.pubKeySize;
                ssl->peerNtruKeyPresent = 1;
            }
        }
#endif /* HAVE_NTRU */
#ifdef HAVE_ECC
        else if (dCert.keyOID == ECDSAk) {
            if (ecc_import_x963(dCert.publicKey, dCert.pubKeySize,
                                &ssl->peerEccDsaKey) != 0) {
                ret = PEER_KEY_ERROR;
            }
            else
                ssl->peerEccDsaKeyPresent = 1;
        }
#endif /* HAVE_ECC */

        FreeDecodedCert(&dCert);
    }
    
    if (anyError != 0 && ret == 0)
        ret = anyError;

    if (ret == 0 && ssl->options.side == CLIENT_END)
        ssl->options.serverState = SERVER_CERT_COMPLETE;

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
                store.domain = domain;
#ifdef OPENSSL_EXTRA
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
            }
            if (ret != 0) {
                SendAlert(ssl, alert_fatal, why);   /* try to send */
                ssl->options.isClosed = 1;
            }
        }
        ssl->error = ret;
    }
#ifdef FORTRESS
    else {
        if (ssl->verifyCallback) {
            int ok;
            CYASSL_X509_STORE_CTX store;

            store.error = ret;
            store.error_depth = totalCerts;
            store.domain = domain;
            store.current_cert = &ssl->peerCert;
            store.ex_data = ssl;

            ok = ssl->verifyCallback(1, &store);
            if (!ok) {
                CYASSL_MSG("Verify callback overriding valid certificate!");
                ret = -1;
                SendAlert(ssl, alert_fatal, bad_certificate);
                ssl->options.isClosed = 1;
            }
        }
    }
#endif

    *inOutIdx = i;
    return ret;
}


static int DoHelloRequest(CYASSL* ssl, const byte* input, word32* inOutIdx)
{
    if (ssl->keys.encryptionOn) {
        const byte* mac;
        int         padSz = ssl->keys.encryptSz - HANDSHAKE_HEADER_SZ - 
                            ssl->specs.hash_size;
        byte        verify[SHA256_DIGEST_SIZE];
       
        ssl->hmac(ssl, verify, input + *inOutIdx - HANDSHAKE_HEADER_SZ,
                  HANDSHAKE_HEADER_SZ, handshake, 1);
        /* read mac and fill */
        mac = input + *inOutIdx;
        *inOutIdx += ssl->specs.hash_size;

        if (ssl->options.tls1_1 && ssl->specs.cipher_type == block)
            padSz -= ssl->specs.block_size;

        *inOutIdx += padSz;

        /* verify */
        if (XMEMCMP(mac, verify, ssl->specs.hash_size)) {
            CYASSL_MSG("    hello_request verify mac error");
            return VERIFY_MAC_ERROR;
        }
    }

    return SendAlert(ssl, alert_warning, no_renegotiation);
}


int DoFinished(CYASSL* ssl, const byte* input, word32* inOutIdx, int sniff)
{
    byte   verifyMAC[SHA256_DIGEST_SIZE];
    int    finishedSz = ssl->options.tls ? TLS_FINISHED_SZ : FINISHED_SZ;
    int    headerSz = HANDSHAKE_HEADER_SZ;
    word32 macSz = finishedSz + HANDSHAKE_HEADER_SZ,
           idx = *inOutIdx,
           padSz = ssl->keys.encryptSz - HANDSHAKE_HEADER_SZ - finishedSz -
                   ssl->specs.hash_size;
    const byte* mac;

    #ifdef CYASSL_DTLS
        if (ssl->options.dtls) {
            headerSz += DTLS_HANDSHAKE_EXTRA;
            macSz    += DTLS_HANDSHAKE_EXTRA;
            padSz    -= DTLS_HANDSHAKE_EXTRA;
        }
    #endif

    #ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn) AddPacketName("Finished", &ssl->handShakeInfo);
        if (ssl->toInfoOn) AddLateName("Finished", &ssl->timeoutInfo);
    #endif
    if (sniff == NO_SNIFF) {
        if (XMEMCMP(input + idx, &ssl->verifyHashes, finishedSz)) {
            CYASSL_MSG("Verify finished error on hashes");
            return VERIFY_FINISHED_ERROR;
        }
    }

    ssl->hmac(ssl, verifyMAC, input + idx - headerSz, macSz,
         handshake, 1);
    idx += finishedSz;

    /* read mac and fill */
    mac = input + idx;
    idx += ssl->specs.hash_size;

    if (ssl->options.tls1_1 && ssl->specs.cipher_type == block)
        padSz -= ssl->specs.block_size;

    idx += padSz;

    /* verify mac */
    if (XMEMCMP(mac, verifyMAC, ssl->specs.hash_size)) {
        CYASSL_MSG("Verify finished error on mac");
        return VERIFY_MAC_ERROR;
    }

    if (ssl->options.side == CLIENT_END) {
        ssl->options.serverState = SERVER_FINISHED_COMPLETE;
        if (!ssl->options.resuming)
            ssl->options.handShakeState = HANDSHAKE_DONE;
    }
    else {
        ssl->options.clientState = CLIENT_FINISHED_COMPLETE;
        if (ssl->options.resuming)
            ssl->options.handShakeState = HANDSHAKE_DONE;
    }

    *inOutIdx = idx;
    return 0;
}


static int DoHandShakeMsg(CYASSL* ssl, byte* input, word32* inOutIdx,
                          word32 totalSz)
{
    byte type;
    word32 size;
    int ret = 0;

    CYASSL_ENTER("DoHandShakeMsg()");

    if (GetHandShakeHeader(ssl, input, inOutIdx, &type, &size) != 0)
        return PARSE_ERROR;

    if (*inOutIdx + size > totalSz)
        return INCOMPLETE_DATA;
    
    HashInput(ssl, input + *inOutIdx, size);
#ifdef CYASSL_CALLBACKS
    /* add name later, add on record and handshake header part back on */
    if (ssl->toInfoOn) {
        int add = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
        AddPacketInfo(0, &ssl->timeoutInfo, input + *inOutIdx - add,
                      size + add, ssl->heap);
        AddLateRecordHeader(&ssl->curRL, &ssl->timeoutInfo);
    }
#endif

    switch (type) {

    case hello_request:
        CYASSL_MSG("processing hello request");
        ret = DoHelloRequest(ssl, input, inOutIdx);
        break;

#ifndef NO_CYASSL_CLIENT
    case hello_verify_request:
        CYASSL_MSG("processing hello verify request");
        ret = DoHelloVerifyRequest(ssl, input,inOutIdx);
        break;
            
    case server_hello:
        CYASSL_MSG("processing server hello");
        ret = DoServerHello(ssl, input, inOutIdx);
        break;

    case certificate_request:
        CYASSL_MSG("processing certificate request");
        ret = DoCertificateRequest(ssl, input, inOutIdx);
        break;

    case server_key_exchange:
        CYASSL_MSG("processing server key exchange");
        ret = DoServerKeyExchange(ssl, input, inOutIdx);
        break;
#endif

    case certificate:
        CYASSL_MSG("processing certificate");
        ret =  DoCertificate(ssl, input, inOutIdx);
        break;

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
        ret = DoFinished(ssl, input, inOutIdx, NO_SNIFF);
        break;

#ifndef NO_CYASSL_SERVER
    case client_hello:
        CYASSL_MSG("processing client hello");
        ret = DoClientHello(ssl, input, inOutIdx, totalSz, size);
        break;

    case client_key_exchange:
        CYASSL_MSG("processing client key exchange");
        ret = DoClientKeyExchange(ssl, input, inOutIdx);
        break;

    case certificate_verify:
        CYASSL_MSG("processing certificate verify");
        ret = DoCertificateVerify(ssl, input, inOutIdx, totalSz);
        break;

#endif

    default:
        CYASSL_MSG("Unknown handshake message type");
        ret = UNKNOWN_HANDSHAKE_TYPE;
    }

    CYASSL_LEAVE("DoHandShakeMsg()", ret);
    return ret;
}


static INLINE void Encrypt(CYASSL* ssl, byte* out, const byte* input, word32 sz)
{
    switch (ssl->specs.bulk_cipher_algorithm) {
        #ifdef BUILD_ARC4
            case rc4:
                Arc4Process(&ssl->encrypt.arc4, out, input, sz);
                break;
        #endif

        #ifdef BUILD_DES3
            case triple_des:
                Des3_CbcEncrypt(&ssl->encrypt.des3, out, input, sz);
                break;
        #endif

        #ifdef BUILD_AES
            case aes:
            #ifdef CYASSL_AESNI
                if ((word)input % 16) {
                    byte buffer[MAX_RECORD_SIZE + MAX_COMP_EXTRA+MAX_MSG_EXTRA];
                    XMEMCPY(buffer, input, sz);
                    AesCbcEncrypt(&ssl->encrypt.aes, buffer, buffer, sz);
                    XMEMCPY(out, buffer, sz);
                    break;
                }
            #endif
                AesCbcEncrypt(&ssl->encrypt.aes, out, input, sz);
                break;
        #endif

        #ifdef HAVE_HC128
            case hc128:
                Hc128_Process(&ssl->encrypt.hc128, out, input, sz);
                break;
        #endif

        #ifdef BUILD_RABBIT
            case rabbit:
                RabbitProcess(&ssl->encrypt.rabbit, out, input, sz);
                break;
        #endif

            default:
                CYASSL_MSG("CyaSSL Encrypt programming error");
    }
}


static INLINE void Decrypt(CYASSL* ssl, byte* plain, const byte* input,
                           word32 sz)
{
    switch (ssl->specs.bulk_cipher_algorithm) {
        #ifdef BUILD_ARC4
            case rc4:
                Arc4Process(&ssl->decrypt.arc4, plain, input, sz);
                break;
        #endif

        #ifdef BUILD_DES3
            case triple_des:
                Des3_CbcDecrypt(&ssl->decrypt.des3, plain, input, sz);
                break;
        #endif

        #ifdef BUILD_AES
            case aes:
                AesCbcDecrypt(&ssl->decrypt.aes, plain, input, sz);
                break;
        #endif

        #ifdef HAVE_HC128
            case hc128:
                Hc128_Process(&ssl->decrypt.hc128, plain, input, sz);
                break;
        #endif

        #ifdef BUILD_RABBIT
            case rabbit:
                RabbitProcess(&ssl->decrypt.rabbit, plain, input, sz);
                break;
        #endif

            default:
                CYASSL_MSG("CyaSSL Decrypt programming error");
    }
}


/* decrypt input message in place */
static int DecryptMessage(CYASSL* ssl, byte* input, word32 sz, word32* idx)
{
    Decrypt(ssl, input, input, sz);
    ssl->keys.encryptSz = sz;
    if (ssl->options.tls1_1 && ssl->specs.cipher_type == block)
        *idx += ssl->specs.block_size;  /* go past TLSv1.1 IV */

    return 0;
}


static INLINE word32 GetSEQIncrement(CYASSL* ssl, int verify)
{
    if (verify)
        return ssl->keys.peer_sequence_number++; 
    else
        return ssl->keys.sequence_number++; 
}


int DoApplicationData(CYASSL* ssl, byte* input, word32* inOutIdx)
{
    word32 msgSz   = ssl->keys.encryptSz;
    word32 pad     = 0, 
           padByte = 0,
           idx     = *inOutIdx,
           digestSz = ssl->specs.hash_size;
    int    dataSz;
    int    ivExtra = 0;
    byte*  rawData = input + idx;  /* keep current  for hmac */
#ifdef HAVE_LIBZ
    byte   decomp[MAX_RECORD_SIZE + MAX_COMP_EXTRA];
#endif

    byte        verify[SHA256_DIGEST_SIZE];
    const byte* mac;

    if (ssl->specs.cipher_type == block) {
        if (ssl->options.tls1_1)
            ivExtra = ssl->specs.block_size;
        pad = *(input + idx + msgSz - ivExtra - 1);
        padByte = 1;
    }

    dataSz = msgSz - ivExtra - digestSz - pad - padByte;
    if (dataSz < 0) {
        CYASSL_MSG("App data buffer error, malicious input?"); 
        return BUFFER_ERROR;
    }

    /* read data */
    if (dataSz) {
        int    rawSz   = dataSz;       /* keep raw size for hmac */

        ssl->hmac(ssl, verify, rawData, rawSz, application_data, 1);

#ifdef HAVE_LIBZ
        if (ssl->options.usingCompression) {
            dataSz = DeCompress(ssl, rawData, dataSz, decomp, sizeof(decomp));
            if (dataSz < 0) return dataSz;
        }
#endif

        if (ssl->options.usingCompression)
            idx += rawSz;
        else
            idx += dataSz;

        ssl->buffers.clearOutputBuffer.buffer = rawData;
        ssl->buffers.clearOutputBuffer.length = dataSz;
    }

    /* read mac and fill */
    mac = input + idx;
    idx += digestSz;
   
    idx += pad;
    if (padByte)
        idx++;

#ifdef HAVE_LIBZ
    if (ssl->options.usingCompression)
        XMEMMOVE(rawData, decomp, dataSz);
#endif

    /* verify */
    if (dataSz) {
        if (XMEMCMP(mac, verify, digestSz)) {
            CYASSL_MSG("App data verify mac error"); 
            return VERIFY_MAC_ERROR;
        }
    }
    else 
        GetSEQIncrement(ssl, 1);  /* even though no data, increment verify */

    *inOutIdx = idx;
    return 0;
}


/* process alert, return level */
static int DoAlert(CYASSL* ssl, byte* input, word32* inOutIdx, int* type)
{
    byte level;

    #ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn)
            AddPacketName("Alert", &ssl->handShakeInfo);
        if (ssl->toInfoOn)
            /* add record header back on to info + 2 byte level, data */
            AddPacketInfo("Alert", &ssl->timeoutInfo, input + *inOutIdx -
                          RECORD_HEADER_SZ, 2 + RECORD_HEADER_SZ, ssl->heap);
    #endif
    level = input[(*inOutIdx)++];
    *type  = (int)input[(*inOutIdx)++];

    CYASSL_MSG("Got alert");
    if (*type == close_notify) {
        CYASSL_MSG("    close notify");
        ssl->options.closeNotify = 1;
    }
    CYASSL_ERROR(*type);

    if (ssl->keys.encryptionOn) {
        int         aSz = ALERT_SIZE;
        const byte* mac;
        byte        verify[SHA256_DIGEST_SIZE];
        int         padSz = ssl->keys.encryptSz - aSz - ssl->specs.hash_size;
        
        ssl->hmac(ssl, verify, input + *inOutIdx - aSz, aSz, alert, 1);

        /* read mac and fill */
        mac = input + *inOutIdx;
        *inOutIdx += (ssl->specs.hash_size + padSz);

        /* verify */
        if (XMEMCMP(mac, verify, ssl->specs.hash_size)) {
            CYASSL_MSG("    alert verify mac error");
            return VERIFY_MAC_ERROR;
        }
    }

    return level;
}

static int GetInputData(CYASSL *ssl, word32 size)
{
    int in;
    int inSz;
    int maxLength;
    int usedLength;

    
    /* check max input length */
    usedLength = ssl->buffers.inputBuffer.length - ssl->buffers.inputBuffer.idx;
    maxLength  = ssl->buffers.inputBuffer.bufferSize - usedLength;
    inSz       = (int)(size - usedLength);      /* from last partial read */

#ifdef CYASSL_DTLS
    if (ssl->options.dtls)
        inSz = MAX_MTU;       /* read ahead up to MTU */
#endif
    
    if (inSz > maxLength) {
        if (GrowInputBuffer(ssl, size, usedLength) < 0)
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
        
        ssl->buffers.inputBuffer.length += in;
        inSz -= in;

    } while (ssl->buffers.inputBuffer.length < size);

    return 0;
}

/* process input requests, return 0 is done, 1 is call again to complete, and
   negative number is error */
int ProcessReply(CYASSL* ssl)
{
    int    ret, type, readSz;
    word32 startIdx = 0;
#ifndef NO_CYASSL_SERVER
    byte   b0, b1;
#endif
#ifdef CYASSL_DTLS
    int    used;
#endif

    for (;;) {
        switch ((processReply)ssl->options.processReply) {

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
            if ( ssl->options.side == SERVER_END &&
                 ssl->options.clientState == NULL_STATE &&
                 ssl->buffers.inputBuffer.buffer[ssl->buffers.inputBuffer.idx]
                         != handshake) {
                ssl->options.processReply = runProcessOldClientHello;

                /* how many bytes need ProcessOldClientHello */
                b0 =
                ssl->buffers.inputBuffer.buffer[ssl->buffers.inputBuffer.idx++];
                b1 =
                ssl->buffers.inputBuffer.buffer[ssl->buffers.inputBuffer.idx++];
                ssl->curSize = ((b0 & 0x7f) << 8) | b1;
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

            if (ssl->keys.encryptionOn)
                if (DecryptMessage(ssl, ssl->buffers.inputBuffer.buffer + 
                                        ssl->buffers.inputBuffer.idx,
                                        ssl->curSize,
                                        &ssl->buffers.inputBuffer.idx) < 0)
                    return DECRYPT_ERROR;

            CYASSL_MSG("received record layer msg");

            switch (ssl->curRL.type) {
                case handshake :
                    /* debugging in DoHandShakeMsg */
                    if ((ret = DoHandShakeMsg(ssl, 
                                              ssl->buffers.inputBuffer.buffer,
                                              &ssl->buffers.inputBuffer.idx,
                                              ssl->buffers.inputBuffer.length))
                                                                           != 0)
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
                    ssl->buffers.inputBuffer.idx++;
                    ssl->keys.encryptionOn = 1;

                    #ifdef CYASSL_DTLS
                        if (ssl->options.dtls)
                            ssl->keys.dtls_peer_epoch++;
                    #endif

                    #ifdef HAVE_LIBZ
                        if (ssl->options.usingCompression)
                            if ( (ret = InitStreams(ssl)) != 0)
                                return ret;
                    #endif
                    if (ssl->options.resuming && ssl->options.side ==
                                                                    CLIENT_END)
                        BuildFinished(ssl, &ssl->verifyHashes, server);
                    else if (!ssl->options.resuming && ssl->options.side ==
                                                                    SERVER_END)
                        BuildFinished(ssl, &ssl->verifyHashes, client);
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
                    if (DoAlert(ssl, ssl->buffers.inputBuffer.buffer,
                           &ssl->buffers.inputBuffer.idx, &type) == alert_fatal)
                        return FATAL_ERROR;

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
    if ((ret = CheckAvalaibleSize(ssl, sendSz)) != 0)
        return ret;

    /* get ouput buffer */
    output = ssl->buffers.outputBuffer.buffer + 
             ssl->buffers.outputBuffer.length;

    AddRecordHeader(output, 1, change_cipher_spec, ssl);

    output[idx] = 1;             /* turn it on */

    #ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn) AddPacketName("ChangeCipher", &ssl->handShakeInfo);
        if (ssl->toInfoOn)
            AddPacketInfo("ChangeCipher", &ssl->timeoutInfo, output, sendSz,
                           ssl->heap);
    #endif
    ssl->buffers.outputBuffer.length += sendSz;

    if (ssl->options.groupMessages)
        return 0;
    else
        return SendBuffered(ssl);
}


static INLINE const byte* GetMacSecret(CYASSL* ssl, int verify)
{
    if ( (ssl->options.side == CLIENT_END && !verify) ||
         (ssl->options.side == SERVER_END &&  verify) )
        return ssl->keys.client_write_MAC_secret;
    else
        return ssl->keys.server_write_MAC_secret;
}


static void Hmac(CYASSL* ssl, byte* digest, const byte* in, word32 sz,
                 int content, int verify)
{
    byte   result[SHA256_DIGEST_SIZE];                 /* max possible sizes */
    word32 digestSz = ssl->specs.hash_size;            /* actual sizes */
    word32 padSz    = ssl->specs.pad_size;

    Md5 md5;
    Sha sha;

    /* data */
    byte seq[SEQ_SZ] = { 0x00, 0x00, 0x00, 0x00 };
    byte conLen[ENUM_LEN + LENGTH_SZ];     /* content & length */
    const byte* macSecret = GetMacSecret(ssl, verify);
    
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
        InitSha(&sha);
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
}


static void BuildMD5_CertVerify(CYASSL* ssl, byte* digest)
{
    byte md5_result[MD5_DIGEST_SIZE];

    /* make md5 inner */
    Md5Update(&ssl->hashMd5, ssl->arrays.masterSecret, SECRET_LEN);
    Md5Update(&ssl->hashMd5, PAD1, PAD_MD5);
    Md5Final(&ssl->hashMd5, md5_result);

    /* make md5 outer */
    Md5Update(&ssl->hashMd5, ssl->arrays.masterSecret, SECRET_LEN);
    Md5Update(&ssl->hashMd5, PAD2, PAD_MD5);
    Md5Update(&ssl->hashMd5, md5_result, MD5_DIGEST_SIZE);

    Md5Final(&ssl->hashMd5, digest);
}


static void BuildSHA_CertVerify(CYASSL* ssl, byte* digest)
{
    byte sha_result[SHA_DIGEST_SIZE];
    
    /* make sha inner */
    ShaUpdate(&ssl->hashSha, ssl->arrays.masterSecret, SECRET_LEN);
    ShaUpdate(&ssl->hashSha, PAD1, PAD_SHA);
    ShaFinal(&ssl->hashSha, sha_result);

    /* make sha outer */
    ShaUpdate(&ssl->hashSha, ssl->arrays.masterSecret, SECRET_LEN);
    ShaUpdate(&ssl->hashSha, PAD2, PAD_SHA);
    ShaUpdate(&ssl->hashSha, sha_result, SHA_DIGEST_SIZE);

    ShaFinal(&ssl->hashSha, digest);
}


static void BuildCertHashes(CYASSL* ssl, Hashes* hashes)
{
    /* store current states, building requires get_digest which resets state */
    Md5 md5 = ssl->hashMd5;
    Sha sha = ssl->hashSha;
#ifndef NO_SHA256     /* for possible future changes */
    Sha256 sha256;
    InitSha256(&sha256);
    if (IsAtLeastTLSv1_2(ssl))
        sha256 = ssl->hashSha256;
#endif

    if (ssl->options.tls) {
        Md5Final(&ssl->hashMd5, hashes->md5);
        ShaFinal(&ssl->hashSha, hashes->sha);
    }
    else {
        BuildMD5_CertVerify(ssl, hashes->md5);
        BuildSHA_CertVerify(ssl, hashes->sha);
    }
    
    /* restore */
    ssl->hashMd5 = md5;
    ssl->hashSha = sha;
#ifndef NO_SHA256
    if (IsAtLeastTLSv1_2(ssl))
        ssl->hashSha256 = sha256;
#endif
}


/* Build SSL Message, encrypted */
static int BuildMessage(CYASSL* ssl, byte* output, const byte* input, int inSz,
                        int type)
{
    word32 digestSz = ssl->specs.hash_size;
    word32 sz = RECORD_HEADER_SZ + inSz + digestSz;                
    word32 pad  = 0, i;
    word32 idx  = RECORD_HEADER_SZ;
    word32 ivSz = 0;      /* TLSv1.1  IV */
    word32 headerSz = RECORD_HEADER_SZ;
    word16 size;
    byte               iv[AES_BLOCK_SIZE];                  /* max size */

#ifdef CYASSL_DTLS
    if (ssl->options.dtls) {
        sz       += DTLS_RECORD_EXTRA;
        idx      += DTLS_RECORD_EXTRA; 
        headerSz += DTLS_RECORD_EXTRA;
    }
#endif

    if (ssl->specs.cipher_type == block) {
        word32 blockSz = ssl->specs.block_size;
        if (ssl->options.tls1_1) {
            ivSz = blockSz;
            sz  += ivSz;
            RNG_GenerateBlock(&ssl->rng, iv, ivSz);
        }
        sz += 1;       /* pad byte */
        pad = (sz - headerSz) % blockSz;
        pad = blockSz - pad;
        sz += pad;
    }

    size = (word16)(sz - headerSz);    /* include mac and digest */
    AddRecordHeader(output, size, (byte)type, ssl);    

    /* write to output */
    if (ivSz) {
        XMEMCPY(output + idx, iv, ivSz);
        idx += ivSz;
    }
    XMEMCPY(output + idx, input, inSz);
    idx += inSz;

    if (type == handshake)
        HashOutput(ssl, output, headerSz + inSz, ivSz);
    ssl->hmac(ssl, output+idx, output + headerSz + ivSz, inSz, type, 0);
    idx += digestSz;

    if (ssl->specs.cipher_type == block)
        for (i = 0; i <= pad; i++)
            output[idx++] = (byte)pad; /* pad byte gets pad value too */

    Encrypt(ssl, output + headerSz, output + headerSz, size);

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


    #ifdef CYASSL_DTLS
        if (ssl->options.dtls) {
            headerSz += DTLS_HANDSHAKE_EXTRA;
            ssl->keys.dtls_epoch++;
            ssl->keys.dtls_sequence_number = 0;  /* reset after epoch change */
        }
    #endif
    
    /* check for avalaible size */
    if ((ret = CheckAvalaibleSize(ssl, sizeof(input) + MAX_MSG_EXTRA)) != 0)
        return ret;

    /* get ouput buffer */
    output = ssl->buffers.outputBuffer.buffer + 
             ssl->buffers.outputBuffer.length;

    AddHandShakeHeader(input, finishedSz, finished, ssl);

    /* make finished hashes */
    hashes = (Hashes*)&input[headerSz];
    BuildFinished(ssl, hashes, ssl->options.side == CLIENT_END ? client :
                  server);

    if ( (sendSz = BuildMessage(ssl, output, input, headerSz +
                                finishedSz, handshake)) < 0)
        return BUILD_MSG_ERROR;

    if (!ssl->options.resuming) {
#ifndef NO_SESSION_CACHE
        AddSession(ssl);    /* just try */
#endif
        if (ssl->options.side == CLIENT_END)
            BuildFinished(ssl, &ssl->verifyHashes, server);
        else
            ssl->options.handShakeState = HANDSHAKE_DONE;
    }
    else {
        if (ssl->options.side == CLIENT_END)
            ssl->options.handShakeState = HANDSHAKE_DONE;
        else
            BuildFinished(ssl, &ssl->verifyHashes, client);
    }

    #ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn) AddPacketName("Finished", &ssl->handShakeInfo);
        if (ssl->toInfoOn)
            AddPacketInfo("Finished", &ssl->timeoutInfo, output, sendSz,
                          ssl->heap);
    #endif

    ssl->buffers.outputBuffer.length += sendSz;

    return SendBuffered(ssl);
}


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

    /* check for avalaible size */
    if ((ret = CheckAvalaibleSize(ssl, sendSz)) != 0)
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
            i += ssl->buffers.certChain.length;
        }
    }
    HashOutput(ssl, output, sendSz, 0);
    #ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn) AddPacketName("Certificate", &ssl->handShakeInfo);
        if (ssl->toInfoOn)
            AddPacketInfo("Certificate", &ssl->timeoutInfo, output, sendSz,
                           ssl->heap);
    #endif

    if (ssl->options.side == SERVER_END)
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
    
    int  typeTotal = 1;  /* only rsa for now */
    int  reqSz = ENUM_LEN + typeTotal + REQ_HEADER_SZ;  /* add auth later */

    if (IsAtLeastTLSv1_2(ssl))
        reqSz += LENGTH_SZ + HASH_SIG_SIZE;

    if (ssl->options.usingPSK_cipher) return 0;  /* not needed */

    sendSz = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ + reqSz;

    #ifdef CYASSL_DTLS
        if (ssl->options.dtls) {
            sendSz += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
            i      += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
        }
    #endif
    /* check for avalaible size */
    if ((ret = CheckAvalaibleSize(ssl, sendSz)) != 0)
        return ret;

    /* get ouput buffer */
    output = ssl->buffers.outputBuffer.buffer +
             ssl->buffers.outputBuffer.length;

    AddHeaders(output, reqSz, certificate_request, ssl);

    /* write to output */
    output[i++] = (byte)typeTotal;  /* # of types */
    output[i++] = rsa_sign;

    /* supported hash/sig */
    if (IsAtLeastTLSv1_2(ssl)) {
        c16toa(HASH_SIG_SIZE, &output[i]);
        i += LENGTH_SZ;

        output[i++] = sha_mac;      /* hash */
        output[i++] = rsa_sa_algo;  /* sig  */
    }

    c16toa(0, &output[i]);  /* auth's */
    i += REQ_HEADER_SZ;

    HashOutput(ssl, output, sendSz, 0);

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


int SendData(CYASSL* ssl, const void* data, int sz)
{
    int sent = 0,  /* plainText size */
        sendSz,
        ret;

    if (ssl->error == WANT_WRITE)
        ssl->error = 0;

    if (ssl->options.handShakeState != HANDSHAKE_DONE) {
        int err;
        CYASSL_MSG("handshake not complete, trying to finish");
        if ( (err = CyaSSL_negotiate(ssl)) != 0) 
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

    for (;;) {
        int   len = min(sz - sent, OUTPUT_RECORD_SIZE);
        byte* out;
        byte* sendBuffer = (byte*)data + sent;  /* may switch on comp */
        int   buffSz = len;                       /* may switch on comp */
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

        /* check for avalaible size */
        if ((ret = CheckAvalaibleSize(ssl, len + COMP_EXTRA +
                                      MAX_MSG_EXTRA)) != 0)
            return ret;

        /* get ouput buffer */
        out = ssl->buffers.outputBuffer.buffer +
              ssl->buffers.outputBuffer.length;

#ifdef HAVE_LIBZ
        if (ssl->options.usingCompression) {
            buffSz = Compress(ssl, sendBuffer, buffSz, comp, sizeof(comp));
            if (buffSz < 0) {
                return buffSz;
            }
            sendBuffer = comp;
        }
#endif
        sendSz = BuildMessage(ssl, out, sendBuffer, buffSz,
                              application_data);

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
int ReceiveData(CYASSL* ssl, byte* output, int sz)
{
    int size;

    CYASSL_ENTER("ReceiveData()");

    if (ssl->error == WANT_READ)
        ssl->error = 0;

    if (ssl->options.handShakeState != HANDSHAKE_DONE) {
        int err;
        CYASSL_MSG("Handshake not complete, trying to finish");
        if ( (err = CyaSSL_negotiate(ssl)) != 0)
            return  err;
    }

    while (ssl->buffers.clearOutputBuffer.length == 0)
        if ( (ssl->error = ProcessReply(ssl)) < 0) {
            CYASSL_ERROR(ssl->error);
            if (ssl->error == ZERO_RETURN) {
                CYASSL_MSG("Zero return, no more data coming");
                ssl->options.isClosed = 1;
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
    ssl->buffers.clearOutputBuffer.length -= size;
    ssl->buffers.clearOutputBuffer.buffer += size;
   
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

    /* if sendalert is called again for nonbloking */
    if (ssl->options.sendAlertState != 0) {
        ret = SendBuffered(ssl);
        if (ret == 0)
            ssl->options.sendAlertState = 0;
        return ret;
    }

    /* check for avalaible size */
    if ((ret = CheckAvalaibleSize(ssl, ALERT_SIZE + MAX_MSG_EXTRA)) != 0)
        return ret;

    /* get ouput buffer */
    output = ssl->buffers.outputBuffer.buffer +
             ssl->buffers.outputBuffer.length;

    input[0] = (byte)severity;
    input[1] = (byte)type;

    if (ssl->keys.encryptionOn)
        sendSz = BuildMessage(ssl, output, input, ALERT_SIZE, alert);
    else {
        RecordLayerHeader *const rl = (RecordLayerHeader*)output;
        rl->type    = alert;
        rl->version = ssl->version;
        c16toa(ALERT_SIZE, rl->length);      

        XMEMCPY(output + RECORD_HEADER_SZ, input, ALERT_SIZE);
        sendSz = RECORD_HEADER_SZ + ALERT_SIZE;
    }

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



void SetErrorString(int error, char* str)
{
    const int max = MAX_ERROR_SZ;  /* shorthand */

#ifdef NO_ERROR_STRINGS

    XSTRNCPY(str, "no support for error strings built in", max);

#else

    /* pass to CTaoCrypt */
    if (error < MAX_CODE_E && error > MIN_CODE_E) {
        CTaoCryptErrorString(error, str);
        return;
    }

    switch (error) {

    case UNSUPPORTED_SUITE :
        XSTRNCPY(str, "unsupported cipher suite", max);
        break;

    case INPUT_CASE_ERROR :
        XSTRNCPY(str, "input state error", max);
        break;

    case PREFIX_ERROR :
        XSTRNCPY(str, "bad index to key rounds", max);
        break;

    case MEMORY_ERROR :
        XSTRNCPY(str, "out of memory", max);
        break;

    case VERIFY_FINISHED_ERROR :
        XSTRNCPY(str, "verify problem on finished", max);
        break;

    case VERIFY_MAC_ERROR :
        XSTRNCPY(str, "verify mac problem", max);
        break;

    case PARSE_ERROR :
        XSTRNCPY(str, "parse error on header", max);
        break;

    case SIDE_ERROR :
        XSTRNCPY(str, "wrong client/server type", max);
        break;

    case NO_PEER_CERT :
        XSTRNCPY(str, "peer didn't send cert", max);
        break;

    case UNKNOWN_HANDSHAKE_TYPE :
        XSTRNCPY(str, "weird handshake type", max);
        break;

    case SOCKET_ERROR_E :
        XSTRNCPY(str, "error state on socket", max);
        break;

    case SOCKET_NODATA :
        XSTRNCPY(str, "expected data, not there", max);
        break;

    case INCOMPLETE_DATA :
        XSTRNCPY(str, "don't have enough data to complete task", max);
        break;

    case UNKNOWN_RECORD_TYPE :
        XSTRNCPY(str, "unknown type in record hdr", max);
        break;

    case DECRYPT_ERROR :
        XSTRNCPY(str, "error during decryption", max);
        break;

    case FATAL_ERROR :
        XSTRNCPY(str, "revcd alert fatal error", max);
        break;

    case ENCRYPT_ERROR :
        XSTRNCPY(str, "error during encryption", max);
        break;

    case FREAD_ERROR :
        XSTRNCPY(str, "fread problem", max);
        break;

    case NO_PEER_KEY :
        XSTRNCPY(str, "need peer's key", max);
        break;

    case NO_PRIVATE_KEY :
        XSTRNCPY(str, "need the private key", max);
        break;

    case NO_DH_PARAMS :
        XSTRNCPY(str, "server missing DH params", max);
        break;

    case RSA_PRIVATE_ERROR :
        XSTRNCPY(str, "error during rsa priv op", max);
        break;

    case MATCH_SUITE_ERROR :
        XSTRNCPY(str, "can't match cipher suite", max);
        break;

    case BUILD_MSG_ERROR :
        XSTRNCPY(str, "build message failure", max);
        break;

    case BAD_HELLO :
        XSTRNCPY(str, "client hello malformed", max);
        break;

    case DOMAIN_NAME_MISMATCH :
        XSTRNCPY(str, "peer subject name mismatch", max);
        break;

    case WANT_READ :
        XSTRNCPY(str, "non-blocking socket wants data to be read", max);
        break;

    case NOT_READY_ERROR :
        XSTRNCPY(str, "handshake layer not ready yet, complete first", max);
        break;

    case PMS_VERSION_ERROR :
        XSTRNCPY(str, "premaster secret version mismatch error", max);
        break;

    case VERSION_ERROR :
        XSTRNCPY(str, "record layer version error", max);
        break;

    case WANT_WRITE :
        XSTRNCPY(str, "non-blocking socket write buffer full", max);
        break;

    case BUFFER_ERROR :
        XSTRNCPY(str, "malformed buffer input error", max);
        break;

    case VERIFY_CERT_ERROR :
        XSTRNCPY(str, "verify problem on certificate", max);
        break;

    case VERIFY_SIGN_ERROR :
        XSTRNCPY(str, "verify problem based on signature", max);
        break;

    case CLIENT_ID_ERROR :
        XSTRNCPY(str, "psk client identity error", max);
        break;

    case SERVER_HINT_ERROR:
        XSTRNCPY(str, "psk server hint error", max);
        break;

    case PSK_KEY_ERROR:
        XSTRNCPY(str, "psk key callback error", max);
        break;

    case NTRU_KEY_ERROR:
        XSTRNCPY(str, "NTRU key error", max);
        break;

    case NTRU_DRBG_ERROR:
        XSTRNCPY(str, "NTRU drbg error", max);
        break;

    case NTRU_ENCRYPT_ERROR:
        XSTRNCPY(str, "NTRU encrypt error", max);
        break;

    case NTRU_DECRYPT_ERROR:
        XSTRNCPY(str, "NTRU decrypt error", max);
        break;

    case ZLIB_INIT_ERROR:
        XSTRNCPY(str, "zlib init error", max);
        break;

    case ZLIB_COMPRESS_ERROR:
        XSTRNCPY(str, "zlib compress error", max);
        break;

    case ZLIB_DECOMPRESS_ERROR:
        XSTRNCPY(str, "zlib decompress error", max);
        break;

    case GETTIME_ERROR:
        XSTRNCPY(str, "gettimeofday() error", max);
        break;

    case GETITIMER_ERROR:
        XSTRNCPY(str, "getitimer() error", max);
        break;

    case SIGACT_ERROR:
        XSTRNCPY(str, "sigaction() error", max);
        break;

    case SETITIMER_ERROR:
        XSTRNCPY(str, "setitimer() error", max);
        break;

    case LENGTH_ERROR:
        XSTRNCPY(str, "record layer length error", max);
        break;

    case PEER_KEY_ERROR:
        XSTRNCPY(str, "cant decode peer key", max);
        break;

    case ZERO_RETURN:
        XSTRNCPY(str, "peer sent close notify alert", max);
        break;

    case ECC_CURVETYPE_ERROR:
        XSTRNCPY(str, "Bad ECC Curve Type or unsupported", max);
        break;

    case ECC_CURVE_ERROR:
        XSTRNCPY(str, "Bad ECC Curve or unsupported", max);
        break;

    case ECC_PEERKEY_ERROR:
        XSTRNCPY(str, "Bad ECC Peer Key", max);
        break;

    case ECC_MAKEKEY_ERROR:
        XSTRNCPY(str, "ECC Make Key failure", max);
        break;

    case ECC_EXPORT_ERROR:
        XSTRNCPY(str, "ECC Export Key failure", max);
        break;

    case ECC_SHARED_ERROR:
        XSTRNCPY(str, "ECC DHE shared failure", max);
        break;

    case BAD_MUTEX_ERROR:
        XSTRNCPY(str, "Bad mutex, operation failed", max);
        break;

    case NOT_CA_ERROR:
        XSTRNCPY(str, "Not a CA by basic constraint error", max);
        break;

    case BAD_PATH_ERROR:
        XSTRNCPY(str, "Bad path for opendir error", max);
        break;

    case BAD_CERT_MANAGER_ERROR:
        XSTRNCPY(str, "Bad Cert Manager error", max);
        break;

    case OCSP_CERT_REVOKED:
        XSTRNCPY(str, "OCSP Cert revoked", max);
        break;

    case CRL_CERT_REVOKED:
        XSTRNCPY(str, "CRL Cert revoked", max);
        break;

    case CRL_MISSING:
        XSTRNCPY(str, "CRL missing, not loaded", max);
        break;

    default :
        XSTRNCPY(str, "unknown error number", max);
    }

#endif /* NO_ERROR_STRINGS */
}



/* be sure to add to cipher_name_idx too !!!! */
const char* const cipher_names[] = 
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

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_128_CBC_SHA
    "DHE-RSA-AES128-SHA",
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_256_CBC_SHA
    "DHE-RSA-AES256-SHA",
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CBC_SHA
    "PSK-AES128-CBC-SHA",
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_CBC_SHA
    "PSK-AES256-CBC-SHA",
#endif

#ifdef BUILD_TLS_RSA_WITH_HC_128_CBC_MD5
    "HC128-MD5",
#endif
    
#ifdef BUILD_TLS_RSA_WITH_HC_128_CBC_SHA
    "HC128-SHA",
#endif

#ifdef BUILD_TLS_RSA_WITH_RABBIT_CBC_SHA
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
    "ECDH-ECDSA-DES-CBC3-SHA"
#endif

};



/* cipher suite number that matches above name table */
int cipher_name_idx[] =
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

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_128_CBC_SHA
    TLS_DHE_RSA_WITH_AES_128_CBC_SHA,    
#endif

#ifdef BUILD_TLS_DHE_RSA_WITH_AES_256_CBC_SHA
    TLS_DHE_RSA_WITH_AES_256_CBC_SHA,
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_128_CBC_SHA
    TLS_PSK_WITH_AES_128_CBC_SHA,    
#endif

#ifdef BUILD_TLS_PSK_WITH_AES_256_CBC_SHA
    TLS_PSK_WITH_AES_256_CBC_SHA,
#endif

#ifdef BUILD_TLS_RSA_WITH_HC_128_CBC_MD5
    TLS_RSA_WITH_HC_128_CBC_MD5,    
#endif

#ifdef BUILD_TLS_RSA_WITH_HC_128_CBC_SHA
    TLS_RSA_WITH_HC_128_CBC_SHA,    
#endif

#ifdef BUILD_TLS_RSA_WITH_RABBIT_CBC_SHA
    TLS_RSA_WITH_RABBIT_CBC_SHA,    
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
    TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA
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

    if (!list)
        return 0;
    
    if (*list == 0) return 1;   /* CyaSSL default */

    if (XSTRNCMP(haystack, "ALL", 3) == 0) return 1;  /* CyaSSL defualt */

    for(;;) {
        word32 len;
        prev = haystack;
        haystack = XSTRSTR(haystack, needle);

        if (!haystack)    /* last cipher */
            len = min(sizeof(name), XSTRLEN(prev));
        else
            len = min(sizeof(name), (word32)(haystack - prev));

        XSTRNCPY(name, prev, len);
        name[(len == sizeof(name)) ? len - 1 : len] = 0;

        for (i = 0; i < suiteSz; i++)
            if (XSTRNCMP(name, cipher_names[i], sizeof(name)) == 0) {
                if (XSTRSTR(name, "EC"))
                    s->suites[idx++] = ECC_BYTE;  /* ECC suite */
                else
                    s->suites[idx++] = 0x00;      /* normal */
                s->suites[idx++] = (byte)cipher_name_idx[i];

                if (!ret) ret = 1;   /* found at least one */
                break;
            }
        if (!haystack) break;
        haystack++;
    }

    if (ret) {
        s->setSuites = 1;
        s->suiteSz   = (word16)idx;
    }

    return ret;
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

        length = sizeof(ProtocolVersion) + RAN_LEN
               + idSz + ENUM_LEN                      
               + ssl->suites.suiteSz + SUITE_LEN
               + COMP_LEN  + ENUM_LEN;

        sendSz = length + HANDSHAKE_HEADER_SZ + RECORD_HEADER_SZ;

#ifdef CYASSL_DTLS
        if (ssl->options.dtls) {
            length += ENUM_LEN;   /* cookie */
            sendSz  = length + DTLS_HANDSHAKE_HEADER_SZ + DTLS_RECORD_HEADER_SZ;
            idx    += DTLS_HANDSHAKE_EXTRA + DTLS_RECORD_EXTRA;
        }
#endif

        /* check for avalaible size */
        if ((ret = CheckAvalaibleSize(ssl, sendSz)) != 0)
            return ret;

        /* get ouput buffer */
        output = ssl->buffers.outputBuffer.buffer +
                 ssl->buffers.outputBuffer.length;

        AddHeaders(output, length, client_hello, ssl);

            /* client hello, first version */
        XMEMCPY(output + idx, &ssl->version, sizeof(ProtocolVersion));
        idx += sizeof(ProtocolVersion);
        ssl->chVersion = ssl->version;  /* store in case changed */

            /* then random */
        if (ssl->options.connectState == CONNECT_BEGIN) {
            RNG_GenerateBlock(&ssl->rng, output + idx, RAN_LEN);
            
                /* store random */
            XMEMCPY(ssl->arrays.clientRandom, output + idx, RAN_LEN);
        } else {
#ifdef CYASSL_DTLS
                /* send same random on hello again */
            XMEMCPY(output + idx, ssl->arrays.clientRandom, RAN_LEN);
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
            output[idx++] = 0;
        }
#endif
            /* then cipher suites */
        c16toa(ssl->suites.suiteSz, output + idx);
        idx += 2;
        XMEMCPY(output + idx, &ssl->suites.suites, ssl->suites.suiteSz);
        idx += ssl->suites.suiteSz;

            /* last, compression */
        output[idx++] = COMP_LEN;
        if (ssl->options.usingCompression)
            output[idx++] = ZLIB_COMPRESSION;
        else
            output[idx++] = NO_COMPRESSION;
            
        HashOutput(ssl, output, sendSz, 0);

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
                                    word32* inOutIdx)
    {
        ProtocolVersion pv;
        byte            cookieSz;
        
#ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn) AddPacketName("HelloVerifyRequest",
                                         &ssl->handShakeInfo);
        if (ssl->toInfoOn) AddLateName("HelloVerifyRequest", &ssl->timeoutInfo);
#endif
        XMEMCPY(&pv, input + *inOutIdx, sizeof(pv));
        *inOutIdx += sizeof(pv);
        
        cookieSz = input[(*inOutIdx)++];
        
        if (cookieSz)
            *inOutIdx += cookieSz;   /* skip for now */
        
        ssl->options.serverState = SERVER_HELLOVERIFYREQUEST_COMPLETE;
        return 0;
    }


    static int DoServerHello(CYASSL* ssl, const byte* input, word32* inOutIdx)
    {
        byte b;
        byte compression;
        ProtocolVersion pv;
        word32 i = *inOutIdx;

#ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn) AddPacketName("ServerHello", &ssl->handShakeInfo);
        if (ssl->toInfoOn) AddLateName("ServerHello", &ssl->timeoutInfo);
#endif
        XMEMCPY(&pv, input + i, sizeof(pv));
        i += sizeof(pv);
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
            else if (pv.minor == SSLv3_MINOR) {
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
        XMEMCPY(ssl->arrays.serverRandom, input + i, RAN_LEN);
        i += RAN_LEN;
        b = input[i++];
        if (b) {
            XMEMCPY(ssl->arrays.sessionID, input + i, b);
            i += b;
            ssl->options.haveSessionId = 1;
        }
        ssl->options.cipherSuite0 = input[i++];
        ssl->options.cipherSuite  = input[i++];  
        compression = input[i++];

        if (compression != ZLIB_COMPRESSION && ssl->options.usingCompression) {
            CYASSL_MSG("Server refused compression, turning off"); 
            ssl->options.usingCompression = 0;  /* turn off if server refused */
        }
        
        ssl->options.serverState = SERVER_HELLO_COMPLETE;

        *inOutIdx = i;

        if (ssl->options.resuming) {
            if (ssl->options.haveSessionId && XMEMCMP(ssl->arrays.sessionID,
                                         ssl->session.sessionID, ID_LEN) == 0) {
                if (SetCipherSpecs(ssl) == 0) {
                    int ret; 
                    XMEMCPY(ssl->arrays.masterSecret, ssl->session.masterSecret,
                           SECRET_LEN);
                    if (ssl->options.tls)
                        ret = DeriveTlsKeys(ssl);
                    else
                        ret = DeriveKeys(ssl);
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

        return SetCipherSpecs(ssl);
    }


    /* just read in and ignore for now TODO: */
    static int DoCertificateRequest(CYASSL* ssl, const byte* input, word32*
                                    inOutIdx)
    {
        word16 len;
       
        #ifdef CYASSL_CALLBACKS
            if (ssl->hsInfoOn)
                AddPacketName("CertificateRequest", &ssl->handShakeInfo);
            if (ssl->toInfoOn)
                AddLateName("CertificateRequest", &ssl->timeoutInfo);
        #endif
        len = input[(*inOutIdx)++];

        /* types, read in here */
        *inOutIdx += len;
        ato16(&input[*inOutIdx], &len);
        *inOutIdx += LENGTH_SZ;

        if (IsAtLeastTLSv1_2(ssl)) {
            /* hash sig format */
            *inOutIdx += len;
            ato16(&input[*inOutIdx], &len);
            *inOutIdx += LENGTH_SZ;
        }

        /* authorities */
        while (len) {
            word16 dnSz;
       
            ato16(&input[*inOutIdx], &dnSz);
            *inOutIdx += (REQUEST_HEADER + dnSz);
            len -= dnSz + REQUEST_HEADER;
        }

        /* don't send client cert or cert verify if user hasn't provided
           cert and private key */
        if (ssl->buffers.certificate.buffer && ssl->buffers.key.buffer)
            ssl->options.sendVerify = SEND_CERT;
        else if (IsAtLeastTLSv1_2(ssl))
            ssl->options.sendVerify = SEND_BLANK_CERT;

        return 0;
    }


    static int DoServerKeyExchange(CYASSL* ssl, const byte* input,
                                   word32* inOutIdx)
    {
    #if defined(OPENSSL_EXTRA) || defined(HAVE_ECC)
        word16 length    = 0;
        word16 sigLen    = 0;
        word16 verifySz  = (word16)*inOutIdx;  /* keep start idx */
        byte*  signature = 0;
    #endif 

        (void)ssl;
        (void)input;
        (void)inOutIdx;

    #ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn)
            AddPacketName("ServerKeyExchange", &ssl->handShakeInfo);
        if (ssl->toInfoOn)
            AddLateName("ServerKeyExchange", &ssl->timeoutInfo);
    #endif

    #ifndef NO_PSK
        if (ssl->specs.kea == psk_kea) {
            word16 pskLen = 0;
            ato16(&input[*inOutIdx], &pskLen);
            *inOutIdx += LENGTH_SZ;
            XMEMCPY(ssl->arrays.server_hint, &input[*inOutIdx],
                   min(pskLen, MAX_PSK_ID_LEN));
            if (pskLen < MAX_PSK_ID_LEN)
                ssl->arrays.server_hint[pskLen] = 0;
            else
                ssl->arrays.server_hint[MAX_PSK_ID_LEN - 1] = 0;
            *inOutIdx += pskLen;

            return 0;
        }
    #endif
    #ifdef OPENSSL_EXTRA
        if (ssl->specs.kea == diffie_hellman_kea)
        {
        /* p */
        ato16(&input[*inOutIdx], &length);
        *inOutIdx += LENGTH_SZ;

        ssl->buffers.serverDH_P.buffer = (byte*) XMALLOC(length, ssl->heap,
                                                         DYNAMIC_TYPE_DH);
        if (ssl->buffers.serverDH_P.buffer)
            ssl->buffers.serverDH_P.length = length;
        else
            return MEMORY_ERROR;
        XMEMCPY(ssl->buffers.serverDH_P.buffer, &input[*inOutIdx], length);
        *inOutIdx += length;

        /* g */
        ato16(&input[*inOutIdx], &length);
        *inOutIdx += LENGTH_SZ;

        ssl->buffers.serverDH_G.buffer = (byte*) XMALLOC(length, ssl->heap,
                                                         DYNAMIC_TYPE_DH);
        if (ssl->buffers.serverDH_G.buffer)
            ssl->buffers.serverDH_G.length = length;
        else
            return MEMORY_ERROR;
        XMEMCPY(ssl->buffers.serverDH_G.buffer, &input[*inOutIdx], length);
        *inOutIdx += length;

        /* pub */
        ato16(&input[*inOutIdx], &length);
        *inOutIdx += LENGTH_SZ;

        ssl->buffers.serverDH_Pub.buffer = (byte*) XMALLOC(length, ssl->heap,
                                                           DYNAMIC_TYPE_DH);
        if (ssl->buffers.serverDH_Pub.buffer)
            ssl->buffers.serverDH_Pub.length = length;
        else
            return MEMORY_ERROR;
        XMEMCPY(ssl->buffers.serverDH_Pub.buffer, &input[*inOutIdx], length);
        *inOutIdx += length;
        }  /* dh_kea */
    #endif /* OPENSSL_EXTRA */

    #ifdef HAVE_ECC
        if (ssl->specs.kea == ecc_diffie_hellman_kea)
        {
        byte b = input[*inOutIdx];
        *inOutIdx += 1;

        if (b != named_curve)
            return ECC_CURVETYPE_ERROR;

        *inOutIdx += 1;   /* curve type, eat leading 0 */
        b = input[*inOutIdx];
        *inOutIdx += 1;

        if (b != secp256r1 && b != secp384r1 && b != secp521r1 && b !=
                 secp160r1 && b != secp192r1 && b != secp224r1)
            return ECC_CURVE_ERROR;

        length = input[*inOutIdx];
        *inOutIdx += 1;

        if (ecc_import_x963(&input[*inOutIdx], length, &ssl->peerEccKey) != 0)
            return ECC_PEERKEY_ERROR;

        *inOutIdx += length;
        ssl->peerEccKeyPresent = 1;
        }
    #endif /* HAVE_ECC */

    #if defined(OPENSSL_EXTRA) || defined(HAVE_ECC)
    {
        Md5    md5;
        Sha    sha;
        byte   hash[FINISHED_SZ];
        byte   messageVerify[MAX_DH_SZ];

        /* adjust from start idx */
        verifySz = (word16)(*inOutIdx - verifySz);

        /* save message for hash verify */
        if (verifySz > sizeof(messageVerify))
            return BUFFER_ERROR;
        XMEMCPY(messageVerify, &input[*inOutIdx - verifySz], verifySz);

        if (IsAtLeastTLSv1_2(ssl)) {
            /* just advance for now TODO: validate hash algo params */
            *inOutIdx += LENGTH_SZ;
        }

        /* signature */
        ato16(&input[*inOutIdx], &length);
        *inOutIdx += LENGTH_SZ;

        signature = (byte*)&input[*inOutIdx];
        *inOutIdx += length;
        sigLen = length;

        /* verify signature */

        /* md5 */
        InitMd5(&md5);
        Md5Update(&md5, ssl->arrays.clientRandom, RAN_LEN);
        Md5Update(&md5, ssl->arrays.serverRandom, RAN_LEN);
        Md5Update(&md5, messageVerify, verifySz);
        Md5Final(&md5, hash);

        /* sha */
        InitSha(&sha);
        ShaUpdate(&sha, ssl->arrays.clientRandom, RAN_LEN);
        ShaUpdate(&sha, ssl->arrays.serverRandom, RAN_LEN);
        ShaUpdate(&sha, messageVerify, verifySz);
        ShaFinal(&sha, &hash[MD5_DIGEST_SIZE]);

        /* rsa */
        if (ssl->specs.sig_algo == rsa_sa_algo)
        {
            int   ret;
            byte* out;

            if (!ssl->peerRsaKeyPresent)
                return NO_PEER_KEY;

            ret = RsaSSL_VerifyInline(signature, sigLen,&out, &ssl->peerRsaKey);

            if (IsAtLeastTLSv1_2(ssl)) {
                byte   encodedSig[MAX_ENCODED_SIG_SZ];
                word32 encSigSz;
                byte*  digest;
                int    typeH;
                int    digestSz;

                /* sha1 for now */
                digest   = &hash[MD5_DIGEST_SIZE];
                typeH    = SHAh;
                digestSz = SHA_DIGEST_SIZE;

                encSigSz = EncodeSignature(encodedSig, digest, digestSz, typeH);

                if (encSigSz != (word32)ret || XMEMCMP(out, encodedSig,
                                                       encSigSz) != 0)
                    return VERIFY_SIGN_ERROR;
            }
            else { 
                if (ret != sizeof(hash) || XMEMCMP(out, hash, sizeof(hash)))
                    return VERIFY_SIGN_ERROR;
            }
        }
#ifdef HAVE_ECC
        /* ecdsa */
        else if (ssl->specs.sig_algo == ecc_dsa_sa_algo) {
            int verify = 0, ret;
            if (!ssl->peerEccDsaKeyPresent)
                return NO_PEER_KEY;

            ret = ecc_verify_hash(signature, sigLen, &hash[MD5_DIGEST_SIZE],
                                 SHA_DIGEST_SIZE, &verify, &ssl->peerEccDsaKey);
            if (ret != 0 || verify == 0)
                return VERIFY_SIGN_ERROR;
        }
#endif /* HAVE_ECC */
        else
            return ALGO_ID_E;

        ssl->options.serverState = SERVER_KEYEXCHANGE_COMPLETE;

        return 0;

    }
#else  /* HAVE_OPENSSL or HAVE_ECC */
        return NOT_COMPILED_IN;  /* not supported by build */
#endif /* HAVE_OPENSSL or HAVE_ECC */
    }


    int SendClientKeyExchange(CYASSL* ssl)
    {
        byte   encSecret[MAX_NTRU_ENCRYPT_SZ];
        word32 encSz = 0;
        word32 idx = 0;
        int    ret = 0;

        if (ssl->specs.kea == rsa_kea) {
            RNG_GenerateBlock(&ssl->rng, ssl->arrays.preMasterSecret,
                              SECRET_LEN);
            ssl->arrays.preMasterSecret[0] = ssl->chVersion.major;
            ssl->arrays.preMasterSecret[1] = ssl->chVersion.minor;
            ssl->arrays.preMasterSz = SECRET_LEN;

            if (ssl->peerRsaKeyPresent == 0)
                return NO_PEER_KEY;

            ret = RsaPublicEncrypt(ssl->arrays.preMasterSecret, SECRET_LEN,
                             encSecret, sizeof(encSecret), &ssl->peerRsaKey,
                             &ssl->rng);
            if (ret > 0) {
                encSz = ret;
                ret = 0;   /* set success to 0 */
            }
        #ifdef OPENSSL_EXTRA
        } else if (ssl->specs.kea == diffie_hellman_kea) {
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
                ret = DhGenerateKeyPair(&key, &ssl->rng, priv, &privSz,
                                        encSecret, &encSz);
            if (ret == 0)
                ret = DhAgree(&key, ssl->arrays.preMasterSecret,
                              &ssl->arrays.preMasterSz, priv, privSz,
                              serverPub.buffer, serverPub.length);
            FreeDhKey(&key);
        #endif /* OPENSSL_EXTRA */
        #ifndef NO_PSK
        } else if (ssl->specs.kea == psk_kea) {
            byte* pms = ssl->arrays.preMasterSecret;

            ssl->arrays.psk_keySz = ssl->options.client_psk_cb(ssl,
                ssl->arrays.server_hint, ssl->arrays.client_identity,
                MAX_PSK_ID_LEN, ssl->arrays.psk_key, MAX_PSK_KEY_LEN);
            if (ssl->arrays.psk_keySz == 0 || 
                ssl->arrays.psk_keySz > MAX_PSK_KEY_LEN)
                return PSK_KEY_ERROR;
            encSz = (word32)XSTRLEN(ssl->arrays.client_identity);
            if (encSz > MAX_PSK_ID_LEN) return CLIENT_ID_ERROR;
            XMEMCPY(encSecret, ssl->arrays.client_identity, encSz);

            /* make psk pre master secret */
            /* length of key + length 0s + length of key + key */
            c16toa((word16)ssl->arrays.psk_keySz, pms);
            pms += 2;
            XMEMSET(pms, 0, ssl->arrays.psk_keySz);
            pms += ssl->arrays.psk_keySz;
            c16toa((word16)ssl->arrays.psk_keySz, pms);
            pms += 2;
            XMEMCPY(pms, ssl->arrays.psk_key, ssl->arrays.psk_keySz);
            ssl->arrays.preMasterSz = ssl->arrays.psk_keySz * 2 + 4;
        #endif /* NO_PSK */
        #ifdef HAVE_NTRU
        } else if (ssl->specs.kea == ntru_kea) {
            word32 rc;
            word16 cipherLen = sizeof(encSecret);
            DRBG_HANDLE drbg;
            static uint8_t const cyasslStr[] = {
                'C', 'y', 'a', 'S', 'S', 'L', ' ', 'N', 'T', 'R', 'U'
            };

            RNG_GenerateBlock(&ssl->rng, ssl->arrays.preMasterSecret,
                              SECRET_LEN);
            ssl->arrays.preMasterSz = SECRET_LEN;

            if (ssl->peerNtruKeyPresent == 0)
                return NO_PEER_KEY;

            rc = crypto_drbg_instantiate(MAX_NTRU_BITS, cyasslStr,
                                          sizeof(cyasslStr), GetEntropy, &drbg);
            if (rc != DRBG_OK)
                return NTRU_DRBG_ERROR; 

            rc = crypto_ntru_encrypt(drbg, ssl->peerNtruKeyLen,ssl->peerNtruKey,
                                     ssl->arrays.preMasterSz,
                                     ssl->arrays.preMasterSecret,
                                     &cipherLen, encSecret);
            crypto_drbg_uninstantiate(drbg);
            if (rc != NTRU_OK)
                return NTRU_ENCRYPT_ERROR;

            encSz = cipherLen;
            ret = 0;
        #endif /* HAVE_NTRU */
        #ifdef HAVE_ECC
        } else if (ssl->specs.kea == ecc_diffie_hellman_kea) {
            ecc_key  myKey;
            ecc_key* peerKey = &myKey;
            word32   size = sizeof(encSecret);

            if (ssl->specs.static_ecdh) {
                /* TODO: EccDsa is really fixed Ecc change naming */
                if (!ssl->peerEccDsaKeyPresent || !ssl->peerEccDsaKey.dp)
                    return NO_PEER_KEY;
                peerKey = &ssl->peerEccDsaKey;
            }
            else {
                if (!ssl->peerEccKeyPresent || !ssl->peerEccKey.dp)
                    return NO_PEER_KEY;
                peerKey = &ssl->peerEccKey;
            }

            ecc_init(&myKey);
            ret = ecc_make_key(&ssl->rng, peerKey->dp->size, &myKey);
            if (ret != 0)
                return ECC_MAKEKEY_ERROR;

            /* precede export with 1 byte length */
            ret = ecc_export_x963(&myKey, encSecret + 1, &size);
            encSecret[0] = size;
            encSz = size + 1;

            if (ret != 0)
                ret = ECC_EXPORT_ERROR;
            else {
                size = sizeof(ssl->arrays.preMasterSecret);
                ret  = ecc_shared_secret(&myKey, peerKey,
                                         ssl->arrays.preMasterSecret, &size);
                if (ret != 0)
                    ret = ECC_SHARED_ERROR;
            }

            ssl->arrays.preMasterSz = size;
            ecc_free(&myKey);
        #endif /* HAVE_ECC */
        } else
            return ALGO_ID_E; /* unsupported kea */

        if (ret == 0) {
            byte              *output;
            int                sendSz;
            word32             tlsSz = 0;
            
            if (ssl->options.tls || ssl->specs.kea == diffie_hellman_kea)
                tlsSz = 2;

            if (ssl->specs.kea == ecc_diffie_hellman_kea)  /* always off */
                tlsSz = 0;

            sendSz = encSz + tlsSz + HANDSHAKE_HEADER_SZ + RECORD_HEADER_SZ;
            idx    = HANDSHAKE_HEADER_SZ + RECORD_HEADER_SZ;

            #ifdef CYASSL_DTLS
                if (ssl->options.dtls) {
                    sendSz += DTLS_HANDSHAKE_EXTRA + DTLS_RECORD_EXTRA;
                    idx    += DTLS_HANDSHAKE_EXTRA + DTLS_RECORD_EXTRA;
                }
            #endif

            /* check for avalaible size */
            if ((ret = CheckAvalaibleSize(ssl, sendSz)) != 0)
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
            idx += encSz;

            HashOutput(ssl, output, sendSz, 0);

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

        return ret;
    }

    int SendCertificateVerify(CYASSL* ssl)
    {
        byte              *output;
        int                sendSz = 0, length, ret;
        word32             idx = 0;
        word32             sigOutSz = 0;
        RsaKey             key;
        int                usingEcc = 0;
#ifdef HAVE_ECC
        ecc_key            eccKey;
#endif

        if (ssl->options.sendVerify == SEND_BLANK_CERT)
            return 0;  /* sent blank cert, can't verify */

        /* check for avalaible size */
        if ((ret = CheckAvalaibleSize(ssl, MAX_CERT_VERIFY_SZ)) != 0)
            return ret;

        /* get ouput buffer */
        output = ssl->buffers.outputBuffer.buffer +
                 ssl->buffers.outputBuffer.length;

        BuildCertHashes(ssl, &ssl->certHashes);

#ifdef HAVE_ECC
        ecc_init(&eccKey);
#endif
        InitRsaKey(&key, ssl->heap);
        ret = RsaPrivateKeyDecode(ssl->buffers.key.buffer, &idx, &key,
                                  ssl->buffers.key.length);
        if (ret == 0)
            sigOutSz = RsaEncryptSize(&key);
        else {
    #ifdef HAVE_ECC
            CYASSL_MSG("Trying ECC client cert, RSA didn't work");
           
            idx = 0; 
            ret = EccPrivateKeyDecode(ssl->buffers.key.buffer, &idx, &eccKey,
                                      ssl->buffers.key.length);
            if (ret == 0) {
                CYASSL_MSG("Using ECC client cert");
                usingEcc = 1;
                sigOutSz = ecc_sig_size(&eccKey);
            }
            else {
                CYASSL_MSG("Bad client cert type");
            }
    #endif
        }
        if (ret == 0) {
            byte*  verify = (byte*)&output[RECORD_HEADER_SZ +
                                           HANDSHAKE_HEADER_SZ];
            byte*  signBuffer = ssl->certHashes.md5;
            word32 signSz = sizeof(Hashes);
            byte   encodedSig[MAX_ENCODED_SIG_SZ];
            word32 extraSz = 0;  /* tls 1.2 hash/sig */

            #ifdef CYASSL_DTLS
                if (ssl->options.dtls)
                    verify += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
            #endif
            length = sigOutSz;
            if (IsAtLeastTLSv1_2(ssl)) {
                verify[0] = sha_mac;
                verify[1] = usingEcc ? ecc_dsa_sa_algo : rsa_sa_algo;
                extraSz = HASH_SIG_SIZE;
            }
            c16toa((word16)length, verify + extraSz); /* prepend verify header*/

            if (usingEcc) {
#ifdef HAVE_ECC
                word32 localSz = sigOutSz;
                ret = ecc_sign_hash(signBuffer + MD5_DIGEST_SIZE,
                              SHA_DIGEST_SIZE, verify + extraSz + VERIFY_HEADER,
                              &localSz, &ssl->rng, &eccKey);
#endif
            }
            else {
                if (IsAtLeastTLSv1_2(ssl)) {
                    byte* digest;
                    int   typeH;
                    int   digestSz;

                    /* sha1 for now */
                    digest   = ssl->certHashes.sha;
                    typeH    = SHAh;
                    digestSz = SHA_DIGEST_SIZE;

                    signSz = EncodeSignature(encodedSig, digest,digestSz,typeH);
                    signBuffer = encodedSig;
                }

                ret = RsaSSL_Sign(signBuffer, signSz, verify + extraSz +
                                  VERIFY_HEADER, ENCRYPT_LEN, &key, &ssl->rng);

                if (ret > 0)
                    ret = 0;  /* RSA reset */
            }
            
            if (ret == 0) {
                AddHeaders(output, length + extraSz + VERIFY_HEADER,
                           certificate_verify, ssl);

                sendSz = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ + length +
                         extraSz + VERIFY_HEADER;
                #ifdef CYASSL_DTLS
                    if (ssl->options.dtls)
                        sendSz += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
                #endif
                HashOutput(ssl, output, sendSz, 0);
            }
        }

        FreeRsaKey(&key);
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



#endif /* NO_CYASSL_CLIENT */


#ifndef NO_CYASSL_SERVER

    int SendServerHello(CYASSL* ssl)
    {
        byte              *output;
        word32             length, idx = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
        int                sendSz;
        int                ret;

        length = sizeof(ProtocolVersion) + RAN_LEN
               + ID_LEN + ENUM_LEN                 
               + SUITE_LEN 
               + ENUM_LEN;

        /* check for avalaible size */
        if ((ret = CheckAvalaibleSize(ssl, MAX_HELLO_SZ)) != 0)
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
        XMEMCPY(output + idx, &ssl->version, sizeof(ProtocolVersion));
        idx += sizeof(ProtocolVersion);

            /* then random */
        if (!ssl->options.resuming)         
            RNG_GenerateBlock(&ssl->rng, ssl->arrays.serverRandom, RAN_LEN);
        XMEMCPY(output + idx, ssl->arrays.serverRandom, RAN_LEN);
        idx += RAN_LEN;

#ifdef SHOW_SECRETS
        {
            int j;
            printf("server random: ");
            for (j = 0; j < RAN_LEN; j++)
                printf("%02x", ssl->arrays.serverRandom[j]);
            printf("\n");
        }
#endif
            /* then session id */
        output[idx++] = ID_LEN;
        if (!ssl->options.resuming)
            RNG_GenerateBlock(&ssl->rng, ssl->arrays.sessionID, ID_LEN);
        XMEMCPY(output + idx, ssl->arrays.sessionID, ID_LEN);
        idx += ID_LEN;

            /* then cipher suite */
        output[idx++] = ssl->options.cipherSuite0; 
        output[idx++] = ssl->options.cipherSuite;

            /* last, compression */
        if (ssl->options.usingCompression)
            output[idx++] = ZLIB_COMPRESSION;
        else
            output[idx++] = NO_COMPRESSION;
            
        ssl->buffers.outputBuffer.length += sendSz;
        HashOutput(ssl, output, sendSz, 0);

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
                break;
            case 24:
                return secp192r1;
                break;
            case 28:
                return secp224r1;
                break;
            case 32:
                return secp256r1;
                break;
            case 48:
                return secp384r1;
                break;
            case 66:
                return secp521r1;
                break;
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
            if (ssl->arrays.server_hint[0] == 0) return 0; /* don't send */

            /* include size part */
            length = (word32)XSTRLEN(ssl->arrays.server_hint);
            if (length > MAX_PSK_ID_LEN) return SERVER_HINT_ERROR;
            length += HINT_LEN_SZ;
            sendSz = length + HANDSHAKE_HEADER_SZ + RECORD_HEADER_SZ;

            #ifdef CYASSL_DTLS 
                if (ssl->options.dtls) {
                    sendSz += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
                    idx    += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
                }
            #endif
            /* check for avalaible size */
            if ((ret = CheckAvalaibleSize(ssl, sendSz)) != 0)
               return ret;

            /* get ouput buffer */
            output = ssl->buffers.outputBuffer.buffer + 
                     ssl->buffers.outputBuffer.length;

            AddHeaders(output, length, server_key_exchange, ssl);

            /* key data */
            c16toa((word16)(length - HINT_LEN_SZ), output + idx);
            idx += HINT_LEN_SZ;
            XMEMCPY(output + idx, ssl->arrays.server_hint, length -HINT_LEN_SZ);

            HashOutput(ssl, output, sendSz, 0);

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
            RsaKey   rsaKey;
            ecc_key  dsaKey;

            if (ssl->specs.static_ecdh) {
                CYASSL_MSG("Using Static ECDH, not sending ServerKeyExchagne");
                return 0;
            }

            /* curve type, named curve, length(1) */
            length = ENUM_LEN + CURVE_LEN + ENUM_LEN;
            /* pub key size */
            CYASSL_MSG("Using ephemeral ECDH");
            if (ecc_export_x963(&ssl->eccTempKey, exportBuf, &expSz) != 0)
                return ECC_EXPORT_ERROR;
            length += expSz;

            preSigSz  = length;
            preSigIdx = idx;

            InitRsaKey(&rsaKey, ssl->heap);
            ecc_init(&dsaKey);

            /* sig length */
            length += LENGTH_SZ;

            if (!ssl->buffers.key.buffer) {
                FreeRsaKey(&rsaKey);
                ecc_free(&dsaKey);
                return NO_PRIVATE_KEY;
            }

            if (ssl->specs.sig_algo == rsa_sa_algo) {
                /* rsa sig size */
                word32 i = 0;
                ret = RsaPrivateKeyDecode(ssl->buffers.key.buffer, &i,
                                          &rsaKey, ssl->buffers.key.length);
                if (ret != 0) return ret;
                sigSz = RsaEncryptSize(&rsaKey); 
            }
            else if (ssl->specs.sig_algo == ecc_dsa_sa_algo) {
                /* ecdsa sig size */
                word32 i = 0;
                ret = EccPrivateKeyDecode(ssl->buffers.key.buffer, &i,
                                          &dsaKey, ssl->buffers.key.length);
                if (ret != 0) return ret;
                sigSz = ecc_sig_size(&dsaKey);
            }
            else {
                FreeRsaKey(&rsaKey);
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
            /* check for avalaible size */
            if ((ret = CheckAvalaibleSize(ssl, sendSz)) != 0) {
                FreeRsaKey(&rsaKey);
                ecc_free(&dsaKey); 
                return ret;
            } 

            /* get ouput buffer */
            output = ssl->buffers.outputBuffer.buffer + 
                     ssl->buffers.outputBuffer.length;

            AddHeaders(output, length, server_key_exchange, ssl);

            /* key exchange data */
            output[idx++] = named_curve;
            output[idx++] = 0x00;          /* leading zero */
            output[idx++] = SetCurveId(ecc_size(&ssl->eccTempKey)); 
            output[idx++] = (byte)expSz;
            XMEMCPY(output + idx, exportBuf, expSz);
            idx += expSz;
            if (IsAtLeastTLSv1_2(ssl)) {
                output[idx++] = sha_mac;
                output[idx++] = ssl->specs.sig_algo;
            }
            c16toa((word16)sigSz, output + idx);
            idx += LENGTH_SZ;

            /* do signature */
            {
                Md5    md5;
                Sha    sha;
                byte   hash[FINISHED_SZ];
                byte*  signBuffer = hash;
                word32 signSz    = sizeof(hash);

                /* md5 */
                InitMd5(&md5);
                Md5Update(&md5, ssl->arrays.clientRandom, RAN_LEN);
                Md5Update(&md5, ssl->arrays.serverRandom, RAN_LEN);
                Md5Update(&md5, output + preSigIdx, preSigSz);
                Md5Final(&md5, hash);

                /* sha */
                InitSha(&sha);
                ShaUpdate(&sha, ssl->arrays.clientRandom, RAN_LEN);
                ShaUpdate(&sha, ssl->arrays.serverRandom, RAN_LEN);
                ShaUpdate(&sha, output + preSigIdx, preSigSz);
                ShaFinal(&sha, &hash[MD5_DIGEST_SIZE]);

                if (ssl->specs.sig_algo == rsa_sa_algo) {
                    byte encodedSig[MAX_ENCODED_SIG_SZ];
                    if (IsAtLeastTLSv1_2(ssl)) {
                        byte* digest;
                        int   hType;
                        int   digestSz;

                        /* sha1 for now */
                        digest   = &hash[MD5_DIGEST_SIZE];
                        hType    = SHAh;
                        digestSz = SHA_DIGEST_SIZE;

                        signSz = EncodeSignature(encodedSig, digest, digestSz,
                                                 hType);
                        signBuffer = encodedSig;
                    }
                    ret = RsaSSL_Sign(signBuffer, signSz, output + idx, sigSz,
                                      &rsaKey, &ssl->rng);
                    FreeRsaKey(&rsaKey);
                    ecc_free(&dsaKey);
                    if (ret > 0)
                        ret = 0;  /* reset on success */
                    else
                        return ret;
                }
                else if (ssl->specs.sig_algo == ecc_dsa_sa_algo) {
                    word32 sz = sigSz;

                    ret = ecc_sign_hash(&hash[MD5_DIGEST_SIZE], SHA_DIGEST_SIZE,
                            output + idx, &sz, &ssl->rng, &dsaKey);
                    FreeRsaKey(&rsaKey);
                    ecc_free(&dsaKey);
                    if (ret < 0) return ret;
                }
            }

            HashOutput(ssl, output, sendSz, 0);

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

        #ifdef OPENSSL_EXTRA 
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
                ret = DhGenerateKeyPair(&dhKey, &ssl->rng,
                                         ssl->buffers.serverDH_Priv.buffer,
                                        &ssl->buffers.serverDH_Priv.length,
                                         ssl->buffers.serverDH_Pub.buffer,
                                        &ssl->buffers.serverDH_Pub.length);
            FreeDhKey(&dhKey);

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

                InitRsaKey(&rsaKey, ssl->heap);
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
            /* check for avalaible size */
            if ((ret = CheckAvalaibleSize(ssl, sendSz)) != 0) {
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
                output[idx++] = sha_mac;
                output[idx++] = ssl->specs.sig_algo; 
            }
            /*    size */
            c16toa((word16)sigSz, output + idx);
            idx += LENGTH_SZ;

            /* do signature */
            {
                Md5    md5;
                Sha    sha;
                byte   hash[FINISHED_SZ];
                byte*  signBuffer = hash;
                word32 signSz    = sizeof(hash);

                /* md5 */
                InitMd5(&md5);
                Md5Update(&md5, ssl->arrays.clientRandom, RAN_LEN);
                Md5Update(&md5, ssl->arrays.serverRandom, RAN_LEN);
                Md5Update(&md5, output + preSigIdx, preSigSz);
                Md5Final(&md5, hash);

                /* sha */
                InitSha(&sha);
                ShaUpdate(&sha, ssl->arrays.clientRandom, RAN_LEN);
                ShaUpdate(&sha, ssl->arrays.serverRandom, RAN_LEN);
                ShaUpdate(&sha, output + preSigIdx, preSigSz);
                ShaFinal(&sha, &hash[MD5_DIGEST_SIZE]);

                if (ssl->specs.sig_algo == rsa_sa_algo) {
                    byte encodedSig[MAX_ENCODED_SIG_SZ];
                    if (IsAtLeastTLSv1_2(ssl)) {
                        byte* digest;
                        int   typeH;
                        int   digestSz;

                        /* sha1 for now */
                        digest   = &hash[MD5_DIGEST_SIZE];
                        typeH    = SHAh;
                        digestSz = SHA_DIGEST_SIZE;

                        signSz = EncodeSignature(encodedSig, digest, digestSz,
                                                 typeH);
                        signBuffer = encodedSig;
                    }
                    ret = RsaSSL_Sign(signBuffer, signSz, output + idx, sigSz,
                                      &rsaKey, &ssl->rng);
                    FreeRsaKey(&rsaKey);
                    if (ret > 0)
                        ret = 0;  /* reset on success */
                    else
                        return ret;
                }
            }

            HashOutput(ssl, output, sendSz, 0);

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
        #endif /* OPENSSL_EXTRA */

        return ret;
    }


    static int MatchSuite(CYASSL* ssl, Suites* peerSuites)
    {
        word16 i, j;

        /* & 0x1 equivalent % 2 */
        if (peerSuites->suiteSz == 0 || peerSuites->suiteSz & 0x1)
            return MATCH_SUITE_ERROR;

        /* start with best, if a match we are good */
        for (i = 0; i < ssl->suites.suiteSz; i += 2)
            for (j = 0; j < peerSuites->suiteSz; j += 2)
                if (ssl->suites.suites[i]   == peerSuites->suites[j] &&
                    ssl->suites.suites[i+1] == peerSuites->suites[j+1] ) {

                    ssl->options.cipherSuite0 = ssl->suites.suites[i];
                    ssl->options.cipherSuite  = ssl->suites.suites[i+1];
                    return SetCipherSpecs(ssl);
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
        Md5Update(&ssl->hashMd5, input + idx, sz);
        ShaUpdate(&ssl->hashSha, input + idx, sz);
#ifndef NO_SHA256
    if (IsAtLeastTLSv1_2(ssl))
        Sha256Update(&ssl->hashSha256, input + idx, sz);
#endif

        /* does this value mean client_hello? */
        idx++;

        /* version */
        pv.major = input[idx++];
        pv.minor = input[idx++];
        ssl->chVersion = pv;  /* store */

        if (ssl->version.minor > pv.minor) {
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
#ifndef NO_PSK
            havePSK = ssl->options.havePSK;
#endif

            InitSuites(&ssl->suites, ssl->version, ssl->options.haveDH, havePSK,
                       ssl->options.haveNTRU, ssl->options.haveECDSA,
                       ssl->options.haveStaticECC, ssl->ctx->method->side);
        }

        /* suite size */
        ato16(&input[idx], &clSuites.suiteSz);
        idx += 2;

        if (clSuites.suiteSz > MAX_SUITE_SZ)
            return BUFFER_ERROR;

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
            XMEMCPY(ssl->arrays.sessionID, input + idx, sessionSz);
            idx += sessionSz;
            ssl->options.resuming = 1;
        }

        /* random */
        if (randomSz < RAN_LEN)
            XMEMSET(ssl->arrays.clientRandom, 0, RAN_LEN - randomSz);
        XMEMCPY(&ssl->arrays.clientRandom[RAN_LEN - randomSz], input + idx,
               randomSz);
        idx += randomSz;

        if (ssl->options.usingCompression)
            ssl->options.usingCompression = 0;  /* turn off */

        ssl->options.clientState = CLIENT_HELLO_COMPLETE;
        *inOutIdx = idx;

        ssl->options.haveSessionId = 1;
        /* DoClientHello uses same resume code */
        while (ssl->options.resuming) {  /* let's try */
            int ret; 
            CYASSL_SESSION* session = GetSession(ssl, ssl->arrays.masterSecret);
            if (!session) {
                ssl->options.resuming = 0;
                break;   /* session lookup failed */
            }
            if (MatchSuite(ssl, &clSuites) < 0) {
                CYASSL_MSG("Unsupported cipher suite, OldClientHello");
                return UNSUPPORTED_SUITE;
            }

            RNG_GenerateBlock(&ssl->rng, ssl->arrays.serverRandom, RAN_LEN);
            if (ssl->options.tls)
                ret = DeriveTlsKeys(ssl);
            else
                ret = DeriveKeys(ssl);
            ssl->options.clientState = CLIENT_KEYEXCHANGE_COMPLETE;

            return ret;
        }

        return MatchSuite(ssl, &clSuites);
    }


    static int DoClientHello(CYASSL* ssl, const byte* input, word32* inOutIdx,
                             word32 totalSz, word32 helloSz)
    {
        byte b;
        ProtocolVersion pv;
        Suites          clSuites;
        word32 i = *inOutIdx;
        word32 begin = i;

#ifdef CYASSL_CALLBACKS
        if (ssl->hsInfoOn) AddPacketName("ClientHello", &ssl->handShakeInfo);
        if (ssl->toInfoOn) AddLateName("ClientHello", &ssl->timeoutInfo);
#endif
        /* make sure can read up to session */
        if (i + sizeof(pv) + RAN_LEN + ENUM_LEN > totalSz)
            return INCOMPLETE_DATA;

        XMEMCPY(&pv, input + i, sizeof(pv));
        ssl->chVersion = pv;   /* store */
        i += sizeof(pv);
        if (ssl->version.minor > pv.minor) {
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
#ifndef NO_PSK
            havePSK = ssl->options.havePSK;
#endif
            InitSuites(&ssl->suites, ssl->version, ssl->options.haveDH, havePSK,
                       ssl->options.haveNTRU, ssl->options.haveECDSA,
                       ssl->options.haveStaticECC, ssl->ctx->method->side);
        }
        /* random */
        XMEMCPY(ssl->arrays.clientRandom, input + i, RAN_LEN);
        i += RAN_LEN;

#ifdef SHOW_SECRETS
        {
            int j;
            printf("client random: ");
            for (j = 0; j < RAN_LEN; j++)
                printf("%02x", ssl->arrays.clientRandom[j]);
            printf("\n");
        }
#endif
        /* session id */
        b = input[i++];
        if (b) {
            if (i + ID_LEN > totalSz)
                return INCOMPLETE_DATA;
            XMEMCPY(ssl->arrays.sessionID, input + i, ID_LEN);
            i += b;
            ssl->options.resuming= 1; /* client wants to resume */
            CYASSL_MSG("Client wants to resume session");
        }
        
        #ifdef CYASSL_DTLS
            /* cookie */
            if (ssl->options.dtls) {
                b = input[i++];
                if (b) {
                    if (b > MAX_COOKIE_LEN)
                        return BUFFER_ERROR;
                    if (i + b > totalSz)
                        return INCOMPLETE_DATA;
                    XMEMCPY(ssl->arrays.cookie, input + i, b);
                    i += b;
                }
            }
        #endif

        if (i + LENGTH_SZ > totalSz)
            return INCOMPLETE_DATA;
        /* suites */
        ato16(&input[i], &clSuites.suiteSz);
        i += 2;

        /* suites and comp len */
        if (i + clSuites.suiteSz + ENUM_LEN > totalSz)
            return INCOMPLETE_DATA;
        if (clSuites.suiteSz > MAX_SUITE_SZ)
            return BUFFER_ERROR;
        XMEMCPY(clSuites.suites, input + i, clSuites.suiteSz);
        i += clSuites.suiteSz;

        b = input[i++];  /* comp len */
        if (i + b > totalSz)
            return INCOMPLETE_DATA;

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
            i += b;  /* ignore, since we're not on */

        ssl->options.clientState = CLIENT_HELLO_COMPLETE;

        *inOutIdx = i;
        if ( (i - begin) < helloSz)
            *inOutIdx = begin + helloSz;  /* skip extensions */
        
        ssl->options.haveSessionId = 1;
        /* ProcessOld uses same resume code */
        while (ssl->options.resuming) {  /* let's try */
            int ret;            
            CYASSL_SESSION* session = GetSession(ssl, ssl->arrays.masterSecret);
            if (!session) {
                ssl->options.resuming = 0;
                CYASSL_MSG("Session lookup for resume failed");
                break;   /* session lookup failed */
            }
            if (MatchSuite(ssl, &clSuites) < 0) {
                CYASSL_MSG("Unsupported cipher suite, ClientHello");
                return UNSUPPORTED_SUITE;
            }

            RNG_GenerateBlock(&ssl->rng, ssl->arrays.serverRandom, RAN_LEN);
            if (ssl->options.tls)
                ret = DeriveTlsKeys(ssl);
            else
                ret = DeriveKeys(ssl);
            ssl->options.clientState = CLIENT_KEYEXCHANGE_COMPLETE;

            return ret;
        }
        return MatchSuite(ssl, &clSuites);
    }


    static int DoCertificateVerify(CYASSL* ssl, byte* input, word32* inOutsz,
                                   word32 totalSz)
    {
        word16      sz = 0;
        word32      i = *inOutsz;
        int         ret = VERIFY_CERT_ERROR;   /* start in error state */
        byte*       sig;
        byte*       out;
        int         outLen;

        #ifdef CYASSL_CALLBACKS
            if (ssl->hsInfoOn)
                AddPacketName("CertificateVerify", &ssl->handShakeInfo);
            if (ssl->toInfoOn)
                AddLateName("CertificateVerify", &ssl->timeoutInfo);
        #endif
        if ( (i + VERIFY_HEADER) > totalSz)
            return INCOMPLETE_DATA;

        if (IsAtLeastTLSv1_2(ssl))
           i += HASH_SIG_SIZE; 
        ato16(&input[i], &sz);
        i += VERIFY_HEADER;

        if ( (i + sz) > totalSz)
            return INCOMPLETE_DATA;

        if (sz > ENCRYPT_LEN)
            return BUFFER_ERROR;

        sig = &input[i];
        *inOutsz = i + sz;

        /* RSA */
        if (ssl->peerRsaKeyPresent != 0) {
            CYASSL_MSG("Doing RSA peer cert verify");

            outLen = RsaSSL_VerifyInline(sig, sz, &out, &ssl->peerRsaKey);

            if (IsAtLeastTLSv1_2(ssl)) {
                byte   encodedSig[MAX_ENCODED_SIG_SZ];
                word32 sigSz;
                byte*  digest;
                int    typeH;
                int    digestSz;

                /* sha1 for now */
                digest   = ssl->certHashes.sha;
                typeH    = SHAh;
                digestSz = SHA_DIGEST_SIZE;

                sigSz = EncodeSignature(encodedSig, digest, digestSz, typeH);

                if (outLen == (int)sigSz && XMEMCMP(out, encodedSig,sigSz) == 0)
                    ret = 0;  /* verified */
            }
            else {
                if (outLen == sizeof(ssl->certHashes) && XMEMCMP(out,
                             ssl->certHashes.md5, sizeof(ssl->certHashes)) == 0)
                    ret = 0;  /* verified */
            }
        }
#ifdef HAVE_ECC
        else if (ssl->peerEccDsaKeyPresent) {
            int verify =  0;
            int err    = -1;

            CYASSL_MSG("Doing ECC peer cert verify");

            err = ecc_verify_hash(sig, sz, ssl->certHashes.sha, SHA_DIGEST_SIZE,
                                  &verify, &ssl->peerEccDsaKey);

            if (err == 0 && verify == 1)
               ret = 0;   /* verified */ 
        }
#endif
        return ret;
    }


    int SendServerHelloDone(CYASSL* ssl)
    {
        byte              *output;
        int                sendSz = RECORD_HEADER_SZ + HANDSHAKE_HEADER_SZ;
        int                ret;

        #ifdef CYASSL_DTLS
            if (ssl->options.dtls)
                sendSz += DTLS_RECORD_EXTRA + DTLS_HANDSHAKE_EXTRA;
        #endif
        /* check for avalaible size */
        if ((ret = CheckAvalaibleSize(ssl, sendSz)) != 0)
            return ret;

        /* get ouput buffer */
        output = ssl->buffers.outputBuffer.buffer +
                 ssl->buffers.outputBuffer.length;

        AddHeaders(output, 0, server_hello_done, ssl);

        HashOutput(ssl, output, sendSz, 0);
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


    int SendHelloVerifyRequest(CYASSL* ssl)
    {
        byte* output;
        int   length = VERSION_SZ + ENUM_LEN;
        int   idx    = DTLS_RECORD_HEADER_SZ + DTLS_HANDSHAKE_HEADER_SZ;
        int   sendSz = length + idx;
        int   ret;

        /* check for avalaible size */
        if ((ret = CheckAvalaibleSize(ssl, sendSz)) != 0)
            return ret;

        /* get ouput buffer */
        output = ssl->buffers.outputBuffer.buffer +
                 ssl->buffers.outputBuffer.length;

        AddHeaders(output, length, hello_verify_request, ssl);

        XMEMCPY(output + idx, &ssl->chVersion, VERSION_SZ);
        idx += VERSION_SZ;
        output[idx++] = 0;     /* no cookie for now */

        HashOutput(ssl, output, sendSz, 0);
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


    static int DoClientKeyExchange(CYASSL* ssl, byte* input,
                                   word32* inOutIdx)
    {
        int    ret = 0;
        word32 length = 0;
        byte*  out;

        if (ssl->options.verifyPeer && ssl->options.failNoCert)
            if (!ssl->options.havePeerCert) {
                CYASSL_MSG("client didn't present peer cert");
                return NO_PEER_CERT;
            }

        #ifdef CYASSL_CALLBACKS
            if (ssl->hsInfoOn)
                AddPacketName("ClientKeyExchange", &ssl->handShakeInfo);
            if (ssl->toInfoOn)
                AddLateName("ClientKeyExchange", &ssl->timeoutInfo);
        #endif
        if (ssl->specs.kea == rsa_kea) {
            word32 idx = 0;
            RsaKey key;
            byte*  tmp = 0;

            InitRsaKey(&key, ssl->heap);

            if (ssl->buffers.key.buffer)
                ret = RsaPrivateKeyDecode(ssl->buffers.key.buffer, &idx, &key,
                                          ssl->buffers.key.length);
            else
                return NO_PRIVATE_KEY;

            if (ret == 0) {
                length = RsaEncryptSize(&key);
                ssl->arrays.preMasterSz = SECRET_LEN;

                if (ssl->options.tls)
                    (*inOutIdx) += 2;
                tmp = input + *inOutIdx;
                *inOutIdx += length;

                if (RsaPrivateDecryptInline(tmp, length, &out, &key) ==
                                                             SECRET_LEN) {
                    XMEMCPY(ssl->arrays.preMasterSecret, out, SECRET_LEN);
                    if (ssl->arrays.preMasterSecret[0] != ssl->chVersion.major
                     ||
                        ssl->arrays.preMasterSecret[1] != ssl->chVersion.minor)

                        ret = PMS_VERSION_ERROR;
                    else
                        ret = MakeMasterSecret(ssl);
                }
                else
                    ret = RSA_PRIVATE_ERROR;
            }

            FreeRsaKey(&key);
#ifndef NO_PSK
        } else if (ssl->specs.kea == psk_kea) {
            byte* pms = ssl->arrays.preMasterSecret;
            word16 ci_sz;

            ato16(&input[*inOutIdx], &ci_sz);
            *inOutIdx += LENGTH_SZ;
            if (ci_sz > MAX_PSK_ID_LEN) return CLIENT_ID_ERROR;

            XMEMCPY(ssl->arrays.client_identity, &input[*inOutIdx], ci_sz);
            *inOutIdx += ci_sz;
            ssl->arrays.client_identity[ci_sz] = 0;

            ssl->arrays.psk_keySz = ssl->options.server_psk_cb(ssl,
                ssl->arrays.client_identity, ssl->arrays.psk_key,
                MAX_PSK_KEY_LEN);
            if (ssl->arrays.psk_keySz == 0 || 
                ssl->arrays.psk_keySz > MAX_PSK_KEY_LEN) return PSK_KEY_ERROR;
            
            /* make psk pre master secret */
            /* length of key + length 0s + length of key + key */
            c16toa((word16)ssl->arrays.psk_keySz, pms);
            pms += 2;
            XMEMSET(pms, 0, ssl->arrays.psk_keySz);
            pms += ssl->arrays.psk_keySz;
            c16toa((word16)ssl->arrays.psk_keySz, pms);
            pms += 2;
            XMEMCPY(pms, ssl->arrays.psk_key, ssl->arrays.psk_keySz);
            ssl->arrays.preMasterSz = ssl->arrays.psk_keySz * 2 + 4;

            ret = MakeMasterSecret(ssl);
#endif /* NO_PSK */
#ifdef HAVE_NTRU
        } else if (ssl->specs.kea == ntru_kea) {
            word32 rc;
            word16 cipherLen;
            word16 plainLen = sizeof(ssl->arrays.preMasterSecret);
            byte*  tmp;

            if (!ssl->buffers.key.buffer)
                return NO_PRIVATE_KEY;

            ato16(&input[*inOutIdx], &cipherLen);
            *inOutIdx += LENGTH_SZ;
            if (cipherLen > MAX_NTRU_ENCRYPT_SZ)
                return NTRU_KEY_ERROR;

            tmp = input + *inOutIdx;
            rc = crypto_ntru_decrypt((word16)ssl->buffers.key.length,
                        ssl->buffers.key.buffer, cipherLen, tmp, &plainLen,
                        ssl->arrays.preMasterSecret);

            if (rc != NTRU_OK || plainLen != SECRET_LEN)
                return NTRU_DECRYPT_ERROR;
            *inOutIdx += cipherLen;

            ssl->arrays.preMasterSz = plainLen;
            ret = MakeMasterSecret(ssl);
#endif /* HAVE_NTRU */
#ifdef HAVE_ECC
        } else if (ssl->specs.kea == ecc_diffie_hellman_kea) {
            word32 size;
            word32 bLength = input[*inOutIdx];  /* one byte length */
            *inOutIdx += 1;

            ret = ecc_import_x963(&input[*inOutIdx], bLength, &ssl->peerEccKey);
            if (ret != 0)
                return ECC_PEERKEY_ERROR;
            *inOutIdx += bLength;
            ssl->peerEccKeyPresent = 1;

            size = sizeof(ssl->arrays.preMasterSecret);
            if (ssl->specs.static_ecdh) {
                ecc_key staticKey;
                word32 i = 0;

                ecc_init(&staticKey);
                ret = EccPrivateKeyDecode(ssl->buffers.key.buffer, &i,
                                          &staticKey, ssl->buffers.key.length);
                if (ret == 0)
                    ret = ecc_shared_secret(&staticKey, &ssl->peerEccKey,
                                            ssl->arrays.preMasterSecret, &size);
                ecc_free(&staticKey);
            }
            else 
                ret = ecc_shared_secret(&ssl->eccTempKey, &ssl->peerEccKey,
                                    ssl->arrays.preMasterSecret, &size);
            if (ret != 0)
                return ECC_SHARED_ERROR;
            ssl->arrays.preMasterSz = size;
            ret = MakeMasterSecret(ssl);
#endif /* HAVE_ECC */
#ifdef OPENSSL_EXTRA 
        } else if (ssl->specs.kea == diffie_hellman_kea) {
            byte*  clientPub;
            word16 clientPubSz;
            DhKey  dhKey;

            ato16(&input[*inOutIdx], &clientPubSz);
            *inOutIdx += LENGTH_SZ;

            clientPub = &input[*inOutIdx];
            *inOutIdx += clientPubSz;

            InitDhKey(&dhKey);
            ret = DhSetKey(&dhKey, ssl->buffers.serverDH_P.buffer,
                                   ssl->buffers.serverDH_P.length,
                                   ssl->buffers.serverDH_G.buffer,
                                   ssl->buffers.serverDH_G.length);
            if (ret == 0)
                ret = DhAgree(&dhKey, ssl->arrays.preMasterSecret,
                                     &ssl->arrays.preMasterSz,
                                      ssl->buffers.serverDH_Priv.buffer,
                                      ssl->buffers.serverDH_Priv.length,
                                      clientPub, clientPubSz);
            FreeDhKey(&dhKey);
            if (ret == 0)
                ret = MakeMasterSecret(ssl);
#endif /* OPENSSL_EXTRA */
        }

        if (ret == 0) {
            ssl->options.clientState = CLIENT_KEYEXCHANGE_COMPLETE;
            if (ssl->options.verifyPeer)
                BuildCertHashes(ssl, &ssl->certHashes);
        }

        return ret;
    }

#endif /* NO_CYASSL_SERVER */


#ifdef SINGLE_THREADED

int InitMutex(CyaSSL_Mutex* m)
{
    return 0;
}


int FreeMutex(CyaSSL_Mutex* m)
{
    return 0;
}


int LockMutex(CyaSSL_Mutex* m)
{
    return 0;
}


int UnLockMutex(CyaSSL_Mutex* m)
{
    return 0;
}

#else /* MULTI_THREAD */
    
    #if defined(FREERTOS)

        int InitMutex(CyaSSL_Mutex* m)
        {
            int iReturn;
            
            *m = ( CyaSSL_Mutex ) xSemaphoreCreateMutex();
            if( *m != NULL )
                iReturn = 0;
            else
                iReturn = BAD_MUTEX_ERROR;
            
            return iReturn;
        }

        int FreeMutex(CyaSSL_Mutex* m)
        {
            vSemaphoreDelete( *m );
            return 0;
        }

        
        int LockMutex(CyaSSL_Mutex* m)
        {
            /* Assume an infinite block, or should there be zero block? */
            xSemaphoreTake( *m, portMAX_DELAY );
            return 0;
        }


        int UnLockMutex(CyaSSL_Mutex* m)
        {
            xSemaphoreGive( *m );
            return 0;
        }

    #elif defined(USE_WINDOWS_API)

        int InitMutex(CyaSSL_Mutex* m)
        {
            InitializeCriticalSection(m);
            return 0;
        }


        int FreeMutex(CyaSSL_Mutex* m)
        {
            DeleteCriticalSection(m);
            return 0;
        }


        int LockMutex(CyaSSL_Mutex* m)
        {
            EnterCriticalSection(m);
            return 0;
        }


        int UnLockMutex(CyaSSL_Mutex* m)
        {
            LeaveCriticalSection(m);
            return 0;
        }

    #elif defined(CYASSL_PTHREADS)

        int InitMutex(CyaSSL_Mutex* m)
        {
            if (pthread_mutex_init(m, 0) == 0)
                return 0;
            else
                return BAD_MUTEX_ERROR;
        }


        int FreeMutex(CyaSSL_Mutex* m)
        {
            if (pthread_mutex_destroy(m) == 0)
                return 0;
            else
                return BAD_MUTEX_ERROR;
        }


        int LockMutex(CyaSSL_Mutex* m)
        {
            if (pthread_mutex_lock(m) == 0)
                return 0;
            else
                return BAD_MUTEX_ERROR;
        }


        int UnLockMutex(CyaSSL_Mutex* m)
        {
            if (pthread_mutex_unlock(m) == 0)
                return 0;
            else
                return BAD_MUTEX_ERROR;
        }

    #elif defined(THREADX)

        int InitMutex(CyaSSL_Mutex* m)
        {
            if (tx_mutex_create(m, "CyaSSL Mutex", TX_NO_INHERIT) == 0)
                return 0;
            else
                return BAD_MUTEX_ERROR;
        }


        int FreeMutex(CyaSSL_Mutex* m)
        {
            if (tx_mutex_delete(m) == 0)
                return 0;
            else
                return BAD_MUTEX_ERROR;
        }


        int LockMutex(CyaSSL_Mutex* m)
        {
            if (tx_mutex_get(m, TX_WAIT_FOREVER) == 0)
                return 0;
            else
                return BAD_MUTEX_ERROR;
        }


        int UnLockMutex(CyaSSL_Mutex* m)
        {
            if (tx_mutex_put(m) == 0)
                return 0;
            else
                return BAD_MUTEX_ERROR;
        }

    #elif defined(MICRIUM)

        int InitMutex(CyaSSL_Mutex* m)
        {
            #if (NET_SECURE_MGR_CFG_EN == DEF_ENABLED)
                if (NetSecure_OS_MutexCreate(m) == 0)
                    return 0;
                else
                    return BAD_MUTEX_ERROR;
            #else
                return 0;
            #endif
        }


        int FreeMutex(CyaSSL_Mutex* m)
        {
            #if (NET_SECURE_MGR_CFG_EN == DEF_ENABLED)
                if (NetSecure_OS_FreeMutex(m) == 0)
                    return 0;
                else
                    return BAD_MUTEX_ERROR;
            #else
                return 0;
            #endif
        }


        int LockMutex(CyaSSL_Mutex* m)
        {
            #if (NET_SECURE_MGR_CFG_EN == DEF_ENABLED)
                if (NetSecure_OS_LockMutex(m) == 0)
                    return 0;
                else
                    return BAD_MUTEX_ERROR;
            #else
                return 0;
            #endif
        }


        int UnLockMutex(CyaSSL_Mutex* m)
        {
            #if (NET_SECURE_MGR_CFG_EN == DEF_ENABLED)
                if (NetSecure_OS_UnLockMutex(m) == 0)
                    return 0;
                else
                    return BAD_MUTEX_ERROR;
            #else
                return 0;
            #endif

        }

    #endif /* USE_WINDOWS_API */
#endif /* SINGLE_THREADED */
