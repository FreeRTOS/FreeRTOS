/* ssl.c
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

#ifdef HAVE_ERRNO_H
    #include <errno.h>
#endif


#include <cyassl/ssl.h>
#include <cyassl/internal.h>
#include <cyassl/error-ssl.h>
#include <cyassl/ctaocrypt/coding.h>

#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
    #include <cyassl/openssl/evp.h>
#endif

#ifdef OPENSSL_EXTRA
    /* openssl headers begin */
    #include <cyassl/openssl/hmac.h>
    #include <cyassl/openssl/crypto.h>
    #include <cyassl/openssl/des.h>
    #include <cyassl/openssl/bn.h>
    #include <cyassl/openssl/dh.h>
    #include <cyassl/openssl/rsa.h>
    #include <cyassl/openssl/pem.h>
    /* openssl headers end, cyassl internal headers next */
    #include <cyassl/ctaocrypt/hmac.h>
    #include <cyassl/ctaocrypt/random.h>
    #include <cyassl/ctaocrypt/des3.h>
    #include <cyassl/ctaocrypt/md4.h>
    #include <cyassl/ctaocrypt/md5.h>
    #include <cyassl/ctaocrypt/arc4.h>
    #ifdef CYASSL_SHA512
        #include <cyassl/ctaocrypt/sha512.h>
    #endif
#endif

#ifndef NO_FILESYSTEM
    #if !defined(USE_WINDOWS_API) && !defined(NO_CYASSL_DIR) \
            && !defined(EBSNET)
        #include <dirent.h>
        #include <sys/stat.h>
    #endif
    #ifdef EBSNET
        #include "vfapi.h"
        #include "vfile.h"
    #endif
#endif /* NO_FILESYSTEM */

#ifndef TRUE
    #define TRUE  1
#endif
#ifndef FALSE
    #define FALSE 0
#endif

#ifndef min

    static INLINE word32 min(word32 a, word32 b)
    {
        return a > b ? b : a;
    }

#endif /* min */

#ifndef max
#ifdef CYASSL_DTLS
    static INLINE word32 max(word32 a, word32 b)
    {
        return a > b ? a : b;
    }
#endif
#endif /* min */


#ifndef CYASSL_LEANPSK
char* mystrnstr(const char* s1, const char* s2, unsigned int n)
{
    unsigned int s2_len = (unsigned int)XSTRLEN(s2);

    if (s2_len == 0)
        return (char*)s1;

    while (n >= s2_len && s1[0]) {
        if (s1[0] == s2[0])
            if (XMEMCMP(s1, s2, s2_len) == 0)
                return (char*)s1;
        s1++;
        n--;
    }

    return NULL;
}
#endif


/* prevent multiple mutex initializations */
static volatile int initRefCount = 0;
static CyaSSL_Mutex count_mutex;   /* init ref count mutex */


CYASSL_CTX* CyaSSL_CTX_new(CYASSL_METHOD* method)
{
    CYASSL_CTX* ctx = NULL;

    CYASSL_ENTER("CYASSL_CTX_new");

    if (initRefCount == 0)
        CyaSSL_Init(); /* user no longer forced to call Init themselves */

    if (method == NULL)
        return ctx;

    ctx = (CYASSL_CTX*) XMALLOC(sizeof(CYASSL_CTX), 0, DYNAMIC_TYPE_CTX);
    if (ctx) {
        if (InitSSL_Ctx(ctx, method) < 0) {
            CYASSL_MSG("Init CTX failed");
            CyaSSL_CTX_free(ctx);
            ctx = NULL;
        }
    }
    else {
        CYASSL_MSG("Alloc CTX failed, method freed");
        XFREE(method, NULL, DYNAMIC_TYPE_METHOD);
    }

    CYASSL_LEAVE("CYASSL_CTX_new", 0);
    return ctx;
}


void CyaSSL_CTX_free(CYASSL_CTX* ctx)
{
    CYASSL_ENTER("SSL_CTX_free");
    if (ctx)
        FreeSSL_Ctx(ctx);
    CYASSL_LEAVE("SSL_CTX_free", 0);
}


CYASSL* CyaSSL_new(CYASSL_CTX* ctx)
{
    CYASSL* ssl = NULL;
    int ret = 0;

    (void)ret;
    CYASSL_ENTER("SSL_new");

    if (ctx == NULL)
        return ssl;

    ssl = (CYASSL*) XMALLOC(sizeof(CYASSL), ctx->heap,DYNAMIC_TYPE_SSL);
    if (ssl)
        if ( (ret = InitSSL(ssl, ctx)) < 0) {
            FreeSSL(ssl);
            ssl = 0;
        }

    CYASSL_LEAVE("SSL_new", ret);
    return ssl;
}


void CyaSSL_free(CYASSL* ssl)
{
    CYASSL_ENTER("SSL_free");
    if (ssl)
        FreeSSL(ssl);
    CYASSL_LEAVE("SSL_free", 0);
}


int CyaSSL_set_fd(CYASSL* ssl, int fd)
{
    CYASSL_ENTER("SSL_set_fd");
    ssl->rfd = fd;      /* not used directly to allow IO callbacks */
    ssl->wfd = fd;

    ssl->IOCB_ReadCtx  = &ssl->rfd;
    ssl->IOCB_WriteCtx = &ssl->wfd;

    #ifdef CYASSL_DTLS
        if (ssl->options.dtls) {
            ssl->IOCB_ReadCtx = &ssl->buffers.dtlsCtx;
            ssl->IOCB_WriteCtx = &ssl->buffers.dtlsCtx;
            ssl->buffers.dtlsCtx.fd = fd;
        }
    #endif

    CYASSL_LEAVE("SSL_set_fd", SSL_SUCCESS);
    return SSL_SUCCESS;
}


int CyaSSL_get_fd(const CYASSL* ssl)
{
    CYASSL_ENTER("SSL_get_fd");
    CYASSL_LEAVE("SSL_get_fd", ssl->rfd);
    return ssl->rfd;
}


int CyaSSL_get_using_nonblock(CYASSL* ssl)
{
    CYASSL_ENTER("CyaSSL_get_using_nonblock");
    CYASSL_LEAVE("CyaSSL_get_using_nonblock", ssl->options.usingNonblock);
    return ssl->options.usingNonblock;
}


int CyaSSL_dtls(CYASSL* ssl)
{
    return ssl->options.dtls;
}


#ifndef CYASSL_LEANPSK
void CyaSSL_set_using_nonblock(CYASSL* ssl, int nonblock)
{
    CYASSL_ENTER("CyaSSL_set_using_nonblock");
    ssl->options.usingNonblock = (nonblock != 0);
}


int CyaSSL_dtls_set_peer(CYASSL* ssl, void* peer, unsigned int peerSz)
{
#ifdef CYASSL_DTLS
    void* sa = (void*)XMALLOC(peerSz, ssl->heap, DYNAMIC_TYPE_SOCKADDR);
    if (sa != NULL) {
        XMEMCPY(sa, peer, peerSz);
        ssl->buffers.dtlsCtx.peer.sa = sa;
        ssl->buffers.dtlsCtx.peer.sz = peerSz;
        return SSL_SUCCESS;
    }
    return SSL_FAILURE;
#else
    (void)ssl;
    (void)peer;
    (void)peerSz;
    return SSL_NOT_IMPLEMENTED;
#endif
}

int CyaSSL_dtls_get_peer(CYASSL* ssl, void* peer, unsigned int* peerSz)
{
#ifdef CYASSL_DTLS
    if (peer != NULL && peerSz != NULL
            && *peerSz >= ssl->buffers.dtlsCtx.peer.sz) {
        *peerSz = ssl->buffers.dtlsCtx.peer.sz;
        XMEMCPY(peer, ssl->buffers.dtlsCtx.peer.sa, *peerSz);
        return SSL_SUCCESS;
    }
    return SSL_FAILURE;
#else
    (void)ssl;
    (void)peer;
    (void)peerSz;
    return SSL_NOT_IMPLEMENTED;
#endif
}
#endif /* CYASSL_LEANPSK */


/* return underlyig connect or accept, SSL_SUCCESS on ok */
int CyaSSL_negotiate(CYASSL* ssl)
{
    int err = SSL_FATAL_ERROR;

    CYASSL_ENTER("CyaSSL_negotiate");
#ifndef NO_CYASSL_SERVER
    if (ssl->options.side == CYASSL_SERVER_END)
        err = CyaSSL_accept(ssl);
#endif

#ifndef NO_CYASSL_CLIENT
    if (ssl->options.side == CYASSL_CLIENT_END)
        err = CyaSSL_connect(ssl);
#endif

    CYASSL_LEAVE("CyaSSL_negotiate", err);

    return err;
}


#ifndef CYASSL_LEANPSK
/* object size based on build */
int CyaSSL_GetObjectSize(void)
{
#ifdef SHOW_SIZES
    printf("sizeof suites           = %lu\n", sizeof(Suites));
    printf("sizeof ciphers(2)       = %lu\n", sizeof(Ciphers));
#ifndef NO_RC4
    printf("    sizeof arc4         = %lu\n", sizeof(Arc4));
#endif
    printf("    sizeof aes          = %lu\n", sizeof(Aes));
#ifndef NO_DES3
    printf("    sizeof des3         = %lu\n", sizeof(Des3));
#endif
#ifndef NO_RABBIT
    printf("    sizeof rabbit       = %lu\n", sizeof(Rabbit));
#endif
    printf("sizeof cipher specs     = %lu\n", sizeof(CipherSpecs));
    printf("sizeof keys             = %lu\n", sizeof(Keys));
    printf("sizeof Hashes(2)        = %lu\n", sizeof(Hashes));
#ifndef NO_MD5
    printf("    sizeof MD5          = %lu\n", sizeof(Md5));
#endif
#ifndef NO_SHA
    printf("    sizeof SHA          = %lu\n", sizeof(Sha));
#endif
#ifndef NO_SHA256
    printf("    sizeof SHA256       = %lu\n", sizeof(Sha256));
#endif
#ifdef CYASSL_SHA384
    printf("    sizeof SHA384       = %lu\n", sizeof(Sha384));
#endif
#ifdef CYASSL_SHA384
    printf("    sizeof SHA512       = %lu\n", sizeof(Sha512));
#endif
    printf("sizeof Buffers          = %lu\n", sizeof(Buffers));
    printf("sizeof Options          = %lu\n", sizeof(Options));
    printf("sizeof Arrays           = %lu\n", sizeof(Arrays));
#ifndef NO_RSA
    printf("sizeof RsaKey           = %lu\n", sizeof(RsaKey));
#endif
#ifdef HAVE_ECC
    printf("sizeof ecc_key          = %lu\n", sizeof(ecc_key));
#endif
    printf("sizeof CYASSL_CIPHER    = %lu\n", sizeof(CYASSL_CIPHER));
    printf("sizeof CYASSL_SESSION   = %lu\n", sizeof(CYASSL_SESSION));
    printf("sizeof CYASSL           = %lu\n", sizeof(CYASSL));
    printf("sizeof CYASSL_CTX       = %lu\n", sizeof(CYASSL_CTX));
#endif

    return sizeof(CYASSL);
}
#endif


#ifndef NO_DH
/* server Diffie-Hellman parameters, SSL_SUCCESS on ok */
int CyaSSL_SetTmpDH(CYASSL* ssl, const unsigned char* p, int pSz,
                    const unsigned char* g, int gSz)
{
    byte havePSK = 0;
    byte haveRSA = 1;

    CYASSL_ENTER("CyaSSL_SetTmpDH");
    if (ssl == NULL || p == NULL || g == NULL) return BAD_FUNC_ARG;

    if (ssl->options.side != CYASSL_SERVER_END)
        return SIDE_ERROR;

    if (ssl->buffers.serverDH_P.buffer && ssl->buffers.weOwnDH)
        XFREE(ssl->buffers.serverDH_P.buffer, ssl->ctx->heap, DYNAMIC_TYPE_DH);
    if (ssl->buffers.serverDH_G.buffer && ssl->buffers.weOwnDH)
        XFREE(ssl->buffers.serverDH_G.buffer, ssl->ctx->heap, DYNAMIC_TYPE_DH);

    ssl->buffers.weOwnDH = 1;  /* SSL owns now */
    ssl->buffers.serverDH_P.buffer = (byte*)XMALLOC(pSz, ssl->ctx->heap,
                                                    DYNAMIC_TYPE_DH);
    if (ssl->buffers.serverDH_P.buffer == NULL)
        return MEMORY_E;

    ssl->buffers.serverDH_G.buffer = (byte*)XMALLOC(gSz, ssl->ctx->heap,
                                                    DYNAMIC_TYPE_DH);
    if (ssl->buffers.serverDH_G.buffer == NULL) {
        XFREE(ssl->buffers.serverDH_P.buffer, ssl->ctx->heap, DYNAMIC_TYPE_DH);
        return MEMORY_E;
    }

    ssl->buffers.serverDH_P.length = pSz;
    ssl->buffers.serverDH_G.length = gSz;

    XMEMCPY(ssl->buffers.serverDH_P.buffer, p, pSz);
    XMEMCPY(ssl->buffers.serverDH_G.buffer, g, gSz);

    ssl->options.haveDH = 1;
    #ifndef NO_PSK
        havePSK = ssl->options.havePSK;
    #endif
    #ifdef NO_RSA
        haveRSA = 0;
    #endif
    InitSuites(ssl->suites, ssl->version, haveRSA, havePSK, ssl->options.haveDH,
               ssl->options.haveNTRU, ssl->options.haveECDSAsig,
               ssl->options.haveStaticECC, ssl->options.side);

    CYASSL_LEAVE("CyaSSL_SetTmpDH", 0);
    return SSL_SUCCESS;
}
#endif /* !NO_DH */


int CyaSSL_write(CYASSL* ssl, const void* data, int sz)
{
    int ret;

    CYASSL_ENTER("SSL_write()");

    if (ssl == NULL || data == NULL || sz < 0)
        return BAD_FUNC_ARG;

#ifdef HAVE_ERRNO_H
    errno = 0;
#endif

    ret = SendData(ssl, data, sz);

    CYASSL_LEAVE("SSL_write()", ret);

    if (ret < 0)
        return SSL_FATAL_ERROR;
    else
        return ret;
}


static int CyaSSL_read_internal(CYASSL* ssl, void* data, int sz, int peek)
{
    int ret;

    CYASSL_ENTER("CyaSSL_read_internal()");

    if (ssl == NULL || data == NULL || sz < 0)
        return BAD_FUNC_ARG;

#ifdef HAVE_ERRNO_H
        errno = 0;
#endif
#ifdef CYASSL_DTLS
    if (ssl->options.dtls)
        ssl->dtls_expected_rx = max(sz + 100, MAX_MTU);
#endif

#ifdef HAVE_MAX_FRAGMENT
    ret = ReceiveData(ssl, (byte*)data,
                     min(sz, min(ssl->max_fragment, OUTPUT_RECORD_SIZE)), peek);
#else
    ret = ReceiveData(ssl, (byte*)data, min(sz, OUTPUT_RECORD_SIZE), peek);
#endif

    CYASSL_LEAVE("CyaSSL_read_internal()", ret);

    if (ret < 0)
        return SSL_FATAL_ERROR;
    else
        return ret;
}


int CyaSSL_peek(CYASSL* ssl, void* data, int sz)
{
    CYASSL_ENTER("CyaSSL_peek()");

    return CyaSSL_read_internal(ssl, data, sz, TRUE);
}


int CyaSSL_read(CYASSL* ssl, void* data, int sz)
{
    CYASSL_ENTER("CyaSSL_read()");

    return CyaSSL_read_internal(ssl, data, sz, FALSE);
}


#ifdef HAVE_CAVIUM

/* let's use cavium, SSL_SUCCESS on ok */
int CyaSSL_UseCavium(CYASSL* ssl, int devId)
{
    if (ssl == NULL)
        return BAD_FUNC_ARG;

    ssl->devId = devId;

    return SSL_SUCCESS;
}


/* let's use cavium, SSL_SUCCESS on ok */
int CyaSSL_CTX_UseCavium(CYASSL_CTX* ctx, int devId)
{
    if (ctx == NULL)
        return BAD_FUNC_ARG;

    ctx->devId = devId;

    return SSL_SUCCESS;
}


#endif /* HAVE_CAVIUM */

#ifdef HAVE_SNI

int CyaSSL_UseSNI(CYASSL* ssl, byte type, const void* data, word16 size)
{
	if (ssl == NULL)
		return BAD_FUNC_ARG;

    return TLSX_UseSNI(&ssl->extensions, type, data, size);
}

int CyaSSL_CTX_UseSNI(CYASSL_CTX* ctx, byte type, const void* data, word16 size)
{
    if (ctx == NULL)
        return BAD_FUNC_ARG;

    return TLSX_UseSNI(&ctx->extensions, type, data, size);
}

#ifndef NO_CYASSL_SERVER

void CyaSSL_SNI_SetOptions(CYASSL* ssl, byte type, byte options)
{
    if (ssl && ssl->extensions)
        TLSX_SNI_SetOptions(ssl->extensions, type, options);
}

void CyaSSL_CTX_SNI_SetOptions(CYASSL_CTX* ctx, byte type, byte options)
{
    if (ctx && ctx->extensions)
        TLSX_SNI_SetOptions(ctx->extensions, type, options);
}

byte CyaSSL_SNI_Status(CYASSL* ssl, byte type)
{
    return TLSX_SNI_Status(ssl ? ssl->extensions : NULL, type);
}

word16 CyaSSL_SNI_GetRequest(CYASSL* ssl, byte type, void** data)
{
    if (data)
        *data = NULL;

    if (ssl && ssl->extensions)
        return TLSX_SNI_GetRequest(ssl->extensions, type, data);

    return 0;
}

int CyaSSL_SNI_GetFromBuffer(const byte* clientHello, word32 helloSz, byte type,
                                                     byte* sni, word32* inOutSz)
{
    if (clientHello && helloSz > 0 && sni && inOutSz && *inOutSz > 0)
        return TLSX_SNI_GetFromBuffer(clientHello, helloSz, type, sni, inOutSz);

    return BAD_FUNC_ARG;
}

#endif /* NO_CYASSL_SERVER */

#endif /* HAVE_SNI */


#ifdef HAVE_MAX_FRAGMENT
#ifndef NO_CYASSL_CLIENT
int CyaSSL_UseMaxFragment(CYASSL* ssl, byte mfl)
{
    if (ssl == NULL)
        return BAD_FUNC_ARG;

    return TLSX_UseMaxFragment(&ssl->extensions, mfl);
}

int CyaSSL_CTX_UseMaxFragment(CYASSL_CTX* ctx, byte mfl)
{
    if (ctx == NULL)
        return BAD_FUNC_ARG;

    return TLSX_UseMaxFragment(&ctx->extensions, mfl);
}
#endif /* NO_CYASSL_CLIENT */
#endif /* HAVE_MAX_FRAGMENT */

#ifdef HAVE_TRUNCATED_HMAC
#ifndef NO_CYASSL_CLIENT
int CyaSSL_UseTruncatedHMAC(CYASSL* ssl)
{
    if (ssl == NULL)
        return BAD_FUNC_ARG;

    return TLSX_UseTruncatedHMAC(&ssl->extensions);
}

int CyaSSL_CTX_UseTruncatedHMAC(CYASSL_CTX* ctx)
{
    if (ctx == NULL)
        return BAD_FUNC_ARG;

    return TLSX_UseTruncatedHMAC(&ctx->extensions);
}
#endif /* NO_CYASSL_CLIENT */
#endif /* HAVE_TRUNCATED_HMAC */

/* Elliptic Curves */
#ifdef HAVE_SUPPORTED_CURVES
#ifndef NO_CYASSL_CLIENT

int CyaSSL_UseSupportedCurve(CYASSL* ssl, word16 name)
{
    if (ssl == NULL)
        return BAD_FUNC_ARG;

    switch (name) {
        case CYASSL_ECC_SECP160R1:
        case CYASSL_ECC_SECP192R1:
        case CYASSL_ECC_SECP224R1:
        case CYASSL_ECC_SECP256R1:
        case CYASSL_ECC_SECP384R1:
        case CYASSL_ECC_SECP521R1:
            break;

        default:
            return BAD_FUNC_ARG;
    }

    return TLSX_UseSupportedCurve(&ssl->extensions, name);
}

int CyaSSL_CTX_UseSupportedCurve(CYASSL_CTX* ctx, word16 name)
{
    if (ctx == NULL)
        return BAD_FUNC_ARG;

    switch (name) {
        case CYASSL_ECC_SECP160R1:
        case CYASSL_ECC_SECP192R1:
        case CYASSL_ECC_SECP224R1:
        case CYASSL_ECC_SECP256R1:
        case CYASSL_ECC_SECP384R1:
        case CYASSL_ECC_SECP521R1:
            break;

        default:
            return BAD_FUNC_ARG;
    }

    return TLSX_UseSupportedCurve(&ctx->extensions, name);
}

#endif /* NO_CYASSL_CLIENT */
#endif /* HAVE_SUPPORTED_CURVES */


#ifndef CYASSL_LEANPSK
int CyaSSL_send(CYASSL* ssl, const void* data, int sz, int flags)
{
    int ret;
    int oldFlags;

    CYASSL_ENTER("CyaSSL_send()");

    if (ssl == NULL || data == NULL || sz < 0)
        return BAD_FUNC_ARG;

    oldFlags = ssl->wflags;

    ssl->wflags = flags;
    ret = CyaSSL_write(ssl, data, sz);
    ssl->wflags = oldFlags;

    CYASSL_LEAVE("CyaSSL_send()", ret);

    return ret;
}


int CyaSSL_recv(CYASSL* ssl, void* data, int sz, int flags)
{
    int ret;
    int oldFlags;

    CYASSL_ENTER("CyaSSL_recv()");

    if (ssl == NULL || data == NULL || sz < 0)
        return BAD_FUNC_ARG;

    oldFlags = ssl->rflags;

    ssl->rflags = flags;
    ret = CyaSSL_read(ssl, data, sz);
    ssl->rflags = oldFlags;

    CYASSL_LEAVE("CyaSSL_recv()", ret);

    return ret;
}
#endif


/* SSL_SUCCESS on ok */
int CyaSSL_shutdown(CYASSL* ssl)
{
    CYASSL_ENTER("SSL_shutdown()");

    if (ssl == NULL)
        return SSL_FATAL_ERROR;

    if (ssl->options.quietShutdown) {
        CYASSL_MSG("quiet shutdown, no close notify sent");
        return SSL_SUCCESS;
    }

    /* try to send close notify, not an error if can't */
    if (!ssl->options.isClosed && !ssl->options.connReset &&
                                  !ssl->options.sentNotify) {
        ssl->error = SendAlert(ssl, alert_warning, close_notify);
        if (ssl->error < 0) {
            CYASSL_ERROR(ssl->error);
            return SSL_FATAL_ERROR;
        }
        ssl->options.sentNotify = 1;  /* don't send close_notify twice */
    }

    CYASSL_LEAVE("SSL_shutdown()", ssl->error);

    ssl->error = SSL_ERROR_SYSCALL;   /* simulate OpenSSL behavior */

    return SSL_SUCCESS;
}


int CyaSSL_get_error(CYASSL* ssl, int ret)
{
    CYASSL_ENTER("SSL_get_error");

    if (ret > 0)
        return SSL_ERROR_NONE;
    if (ssl == NULL)
        return BAD_FUNC_ARG;

    CYASSL_LEAVE("SSL_get_error", ssl->error);

    /* make sure converted types are handled in SetErrorString() too */
    if (ssl->error == WANT_READ)
        return SSL_ERROR_WANT_READ;         /* convert to OpenSSL type */
    else if (ssl->error == WANT_WRITE)
        return SSL_ERROR_WANT_WRITE;        /* convert to OpenSSL type */
    else if (ssl->error == ZERO_RETURN)
        return SSL_ERROR_ZERO_RETURN;       /* convert to OpenSSL type */
    return ssl->error;
}


/* retrive alert history, SSL_SUCCESS on ok */
int CyaSSL_get_alert_history(CYASSL* ssl, CYASSL_ALERT_HISTORY *h)
{
    if (ssl && h) {
        *h = ssl->alert_history;
    }
    return SSL_SUCCESS;
}


/* return TRUE if current error is want read */
int CyaSSL_want_read(CYASSL* ssl)
{
    CYASSL_ENTER("SSL_want_read");
    if (ssl->error == WANT_READ)
        return 1;

    return 0;
}


/* return TRUE if current error is want write */
int CyaSSL_want_write(CYASSL* ssl)
{
    CYASSL_ENTER("SSL_want_write");
    if (ssl->error == WANT_WRITE)
        return 1;

    return 0;
}


char* CyaSSL_ERR_error_string(unsigned long errNumber, char* data)
{
    static const char* msg = "Please supply a buffer for error string";

    CYASSL_ENTER("ERR_error_string");
    if (data) {
        SetErrorString((int)errNumber, data);
        return data;
    }

    return (char*)msg;
}


void CyaSSL_ERR_error_string_n(unsigned long e, char* buf, unsigned long len)
{
    CYASSL_ENTER("CyaSSL_ERR_error_string_n");
    if (len >= CYASSL_MAX_ERROR_SZ)
        CyaSSL_ERR_error_string(e, buf);
    else {
        char tmp[CYASSL_MAX_ERROR_SZ];

        CYASSL_MSG("Error buffer too short, truncating");
        if (len) {
            CyaSSL_ERR_error_string(e, tmp);
            XMEMCPY(buf, tmp, len-1);
            buf[len-1] = '\0';
        }
    }
}


/* don't free temporary arrays at end of handshake */
void CyaSSL_KeepArrays(CYASSL* ssl)
{
    if (ssl)
        ssl->options.saveArrays = 1;
}


/* user doesn't need temporary arrays anymore, Free */
void CyaSSL_FreeArrays(CYASSL* ssl)
{
    if (ssl && ssl->options.handShakeState == HANDSHAKE_DONE) {
        ssl->options.saveArrays = 0;
        FreeArrays(ssl, 1);
    }
}


const byte* CyaSSL_GetMacSecret(CYASSL* ssl, int verify)
{
    if (ssl == NULL)
        return NULL;

    if ( (ssl->options.side == CYASSL_CLIENT_END && !verify) ||
         (ssl->options.side == CYASSL_SERVER_END &&  verify) )
        return ssl->keys.client_write_MAC_secret;
    else
        return ssl->keys.server_write_MAC_secret;
}


#ifdef ATOMIC_USER

void  CyaSSL_CTX_SetMacEncryptCb(CYASSL_CTX* ctx, CallbackMacEncrypt cb)
{
    if (ctx)
        ctx->MacEncryptCb = cb;
}


void  CyaSSL_SetMacEncryptCtx(CYASSL* ssl, void *ctx)
{
    if (ssl)
        ssl->MacEncryptCtx = ctx;
}


void* CyaSSL_GetMacEncryptCtx(CYASSL* ssl)
{
    if (ssl)
        return ssl->MacEncryptCtx;

    return NULL;
}


void  CyaSSL_CTX_SetDecryptVerifyCb(CYASSL_CTX* ctx, CallbackDecryptVerify cb)
{
    if (ctx)
        ctx->DecryptVerifyCb = cb;
}


void  CyaSSL_SetDecryptVerifyCtx(CYASSL* ssl, void *ctx)
{
    if (ssl)
        ssl->DecryptVerifyCtx = ctx;
}


void* CyaSSL_GetDecryptVerifyCtx(CYASSL* ssl)
{
    if (ssl)
        return ssl->DecryptVerifyCtx;

    return NULL;
}


const byte* CyaSSL_GetClientWriteKey(CYASSL* ssl)
{
    if (ssl)
        return ssl->keys.client_write_key;

    return NULL;
}


const byte* CyaSSL_GetClientWriteIV(CYASSL* ssl)
{
    if (ssl)
        return ssl->keys.client_write_IV;

    return NULL;
}


const byte* CyaSSL_GetServerWriteKey(CYASSL* ssl)
{
    if (ssl)
        return ssl->keys.server_write_key;

    return NULL;
}


const byte* CyaSSL_GetServerWriteIV(CYASSL* ssl)
{
    if (ssl)
        return ssl->keys.server_write_IV;

    return NULL;
}


int CyaSSL_GetKeySize(CYASSL* ssl)
{
    if (ssl)
        return ssl->specs.key_size;

    return BAD_FUNC_ARG;
}


int CyaSSL_GetIVSize(CYASSL* ssl)
{
    if (ssl)
        return ssl->specs.iv_size;

    return BAD_FUNC_ARG;
}


int CyaSSL_GetBulkCipher(CYASSL* ssl)
{
    if (ssl)
        return ssl->specs.bulk_cipher_algorithm;

    return BAD_FUNC_ARG;
}


int CyaSSL_GetCipherType(CYASSL* ssl)
{
    if (ssl == NULL)
        return BAD_FUNC_ARG;

    if (ssl->specs.cipher_type == block)
        return CYASSL_BLOCK_TYPE;
    if (ssl->specs.cipher_type == stream)
        return CYASSL_STREAM_TYPE;
    if (ssl->specs.cipher_type == aead)
        return CYASSL_AEAD_TYPE;

    return -1;
}


int CyaSSL_GetCipherBlockSize(CYASSL* ssl)
{
    if (ssl == NULL)
        return BAD_FUNC_ARG;

    return ssl->specs.block_size;
}


int CyaSSL_GetAeadMacSize(CYASSL* ssl)
{
    if (ssl == NULL)
        return BAD_FUNC_ARG;

    return ssl->specs.aead_mac_size;
}


int CyaSSL_IsTLSv1_1(CYASSL* ssl)
{
    if (ssl == NULL)
        return BAD_FUNC_ARG;

    if (ssl->options.tls1_1)
        return 1;

    return 0;
}


int CyaSSL_GetSide(CYASSL* ssl)
{
    if (ssl)
        return ssl->options.side;

    return BAD_FUNC_ARG;
}


int CyaSSL_GetHmacSize(CYASSL* ssl)
{
    /* AEAD ciphers don't have HMAC keys */
    if (ssl)
        return (ssl->specs.cipher_type != aead) ? ssl->specs.hash_size : 0;

    return BAD_FUNC_ARG;
}

#endif /* ATOMIC_USER */

#ifndef NO_CERTS

CYASSL_CERT_MANAGER* CyaSSL_CertManagerNew(void)
{
    CYASSL_CERT_MANAGER* cm = NULL;

    CYASSL_ENTER("CyaSSL_CertManagerNew");

    cm = (CYASSL_CERT_MANAGER*) XMALLOC(sizeof(CYASSL_CERT_MANAGER), 0,
                                        DYNAMIC_TYPE_CERT_MANAGER);
    if (cm) {
        XMEMSET(cm, 0, sizeof(CYASSL_CERT_MANAGER));

        if (InitMutex(&cm->caLock) != 0) {
            CYASSL_MSG("Bad mutex init");
            CyaSSL_CertManagerFree(cm);
            return NULL;
        }
    }

    return cm;
}


void CyaSSL_CertManagerFree(CYASSL_CERT_MANAGER* cm)
{
    CYASSL_ENTER("CyaSSL_CertManagerFree");

    if (cm) {
        #ifdef HAVE_CRL
            if (cm->crl)
                FreeCRL(cm->crl, 1);
        #endif
        #ifdef HAVE_OCSP
            if (cm->ocsp)
                FreeOCSP(cm->ocsp, 1);
        #endif
        FreeSignerTable(cm->caTable, CA_TABLE_SIZE, NULL);
        FreeMutex(&cm->caLock);
        XFREE(cm, NULL, DYNAMIC_TYPE_CERT_MANAGER);
    }

}


/* Unload the CA signer list */
int CyaSSL_CertManagerUnloadCAs(CYASSL_CERT_MANAGER* cm)
{
    CYASSL_ENTER("CyaSSL_CertManagerUnloadCAs");

    if (cm == NULL)
        return BAD_FUNC_ARG;

    if (LockMutex(&cm->caLock) != 0)
        return BAD_MUTEX_E;

    FreeSignerTable(cm->caTable, CA_TABLE_SIZE, NULL);

    UnLockMutex(&cm->caLock);


    return SSL_SUCCESS;
}


/* Return bytes written to buff or < 0 for error */
int CyaSSL_CertPemToDer(const unsigned char* pem, int pemSz,
                        unsigned char* buff, int buffSz,
                        int type)
{
    EncryptedInfo info;
    int           eccKey = 0;
    int           ret;
    buffer        der;

    CYASSL_ENTER("CyaSSL_CertPemToDer");

    if (pem == NULL || buff == NULL || buffSz <= 0) {
        CYASSL_MSG("Bad pem der args");
        return BAD_FUNC_ARG;
    }

    if (type != CERT_TYPE && type != CA_TYPE && type != CERTREQ_TYPE) {
        CYASSL_MSG("Bad cert type");
        return BAD_FUNC_ARG;
    }

    info.set       = 0;
    info.ctx      = NULL;
    info.consumed = 0;
    der.buffer    = NULL;

    ret = PemToDer(pem, pemSz, type, &der, NULL, &info, &eccKey);
    if (ret < 0) {
        CYASSL_MSG("Bad Pem To Der");
    }
    else {
        if (der.length <= (word32)buffSz) {
            XMEMCPY(buff, der.buffer, der.length);
            ret = der.length;
        }
        else {
            CYASSL_MSG("Bad der length");
            ret = BAD_FUNC_ARG;
        }
    }

    XFREE(der.buffer, NULL, DYNAMIC_TYPE_KEY);

    return ret;
}


#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)

/* our KeyPemToDer password callback, password in userData */
static INLINE int OurPasswordCb(char* passwd, int sz, int rw, void* userdata)
{
    (void)rw;

    if (userdata == NULL)
        return 0;

    XSTRNCPY(passwd, (char*)userdata, sz);
    return min((word32)sz, (word32)XSTRLEN((char*)userdata));
}

#endif /* OPENSSL_EXTRA || HAVE_WEBSERVER */


/* Return bytes written to buff or < 0 for error */
int CyaSSL_KeyPemToDer(const unsigned char* pem, int pemSz, unsigned char* buff,
                       int buffSz, const char* pass)
{
    EncryptedInfo info;
    int           eccKey = 0;
    int           ret;
    buffer        der;

    (void)pass;

    CYASSL_ENTER("CyaSSL_KeyPemToDer");

    if (pem == NULL || buff == NULL || buffSz <= 0) {
        CYASSL_MSG("Bad pem der args");
        return BAD_FUNC_ARG;
    }

    info.set       = 0;
    info.ctx      = NULL;
    info.consumed = 0;
    der.buffer    = NULL;

#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
    if (pass) {
        info.ctx = CyaSSL_CTX_new(CyaSSLv23_client_method());
        if (info.ctx == NULL)
            return MEMORY_E;
        CyaSSL_CTX_set_default_passwd_cb(info.ctx, OurPasswordCb);
        CyaSSL_CTX_set_default_passwd_cb_userdata(info.ctx, (void*)pass);
    }
#endif

    ret = PemToDer(pem, pemSz, PRIVATEKEY_TYPE, &der, NULL, &info, &eccKey);
    if (ret < 0) {
        CYASSL_MSG("Bad Pem To Der");
    }
    else {
        if (der.length <= (word32)buffSz) {
            XMEMCPY(buff, der.buffer, der.length);
            ret = der.length;
        }
        else {
            CYASSL_MSG("Bad der length");
            ret = BAD_FUNC_ARG;
        }
    }

    XFREE(der.buffer, NULL, DYNAMIC_TYPE_KEY);

    if (info.ctx)
        CyaSSL_CTX_free(info.ctx);

    return ret;
}


#endif /* !NO_CERTS */



#if !defined(NO_FILESYSTEM) && !defined(NO_STDIO_FILESYSTEM)

void CyaSSL_ERR_print_errors_fp(FILE* fp, int err)
{
    char data[CYASSL_MAX_ERROR_SZ + 1];

    CYASSL_ENTER("CyaSSL_ERR_print_errors_fp");
    SetErrorString(err, data);
    fprintf(fp, "%s", data);
}

#endif


int CyaSSL_pending(CYASSL* ssl)
{
    CYASSL_ENTER("SSL_pending");
    return ssl->buffers.clearOutputBuffer.length;
}


#ifndef CYASSL_LEANPSK
/* trun on handshake group messages for context */
int CyaSSL_CTX_set_group_messages(CYASSL_CTX* ctx)
{
    if (ctx == NULL)
       return BAD_FUNC_ARG;

    ctx->groupMessages = 1;

    return SSL_SUCCESS;
}
#endif


#ifndef NO_CYASSL_CLIENT
/* connect enough to get peer cert chain */
int CyaSSL_connect_cert(CYASSL* ssl)
{
    int  ret;

    if (ssl == NULL)
        return SSL_FAILURE;

    ssl->options.certOnly = 1;
    ret = CyaSSL_connect(ssl);
    ssl->options.certOnly   = 0;

    return ret;
}
#endif


#ifndef CYASSL_LEANPSK
/* trun on handshake group messages for ssl object */
int CyaSSL_set_group_messages(CYASSL* ssl)
{
    if (ssl == NULL)
       return BAD_FUNC_ARG;

    ssl->options.groupMessages = 1;

    return SSL_SUCCESS;
}


int CyaSSL_SetVersion(CYASSL* ssl, int version)
{
    byte haveRSA = 1;
    byte havePSK = 0;

    CYASSL_ENTER("CyaSSL_SetVersion");

    if (ssl == NULL) {
        CYASSL_MSG("Bad function argument");
        return BAD_FUNC_ARG;
    }

    switch (version) {
#ifndef NO_OLD_TLS
        case CYASSL_SSLV3:
            ssl->version = MakeSSLv3();
            break;
#endif

#ifndef NO_TLS
    #ifndef NO_OLD_TLS
        case CYASSL_TLSV1:
            ssl->version = MakeTLSv1();
            break;

        case CYASSL_TLSV1_1:
            ssl->version = MakeTLSv1_1();
            break;
    #endif
        case CYASSL_TLSV1_2:
            ssl->version = MakeTLSv1_2();
            break;
#endif

        default:
            CYASSL_MSG("Bad function argument");
            return BAD_FUNC_ARG;
    }

    #ifdef NO_RSA
        haveRSA = 0;
    #endif
    #ifndef NO_PSK
        havePSK = ssl->options.havePSK;
    #endif

    InitSuites(ssl->suites, ssl->version, haveRSA, havePSK, ssl->options.haveDH,
                ssl->options.haveNTRU, ssl->options.haveECDSAsig,
                ssl->options.haveStaticECC, ssl->options.side);

    return SSL_SUCCESS;
}
#endif /* !leanpsk */


#if !defined(NO_CERTS) || !defined(NO_SESSION_CACHE)

/* Make a work from the front of random hash */
static INLINE word32 MakeWordFromHash(const byte* hashID)
{
    return (hashID[0] << 24) | (hashID[1] << 16) | (hashID[2] <<  8) |
            hashID[3];
}

#endif /* !NO_CERTS || !NO_SESSION_CACHE */


#ifndef NO_CERTS

/* hash is the SHA digest of name, just use first 32 bits as hash */
static INLINE word32 HashSigner(const byte* hash)
{
    return MakeWordFromHash(hash) % CA_TABLE_SIZE;
}


/* does CA already exist on signer list */
int AlreadySigner(CYASSL_CERT_MANAGER* cm, byte* hash)
{
    Signer* signers;
    int     ret = 0;
    word32  row = HashSigner(hash);

    if (LockMutex(&cm->caLock) != 0)
        return  ret;
    signers = cm->caTable[row];
    while (signers) {
        byte* subjectHash;
        #ifndef NO_SKID
            subjectHash = signers->subjectKeyIdHash;
        #else
            subjectHash = signers->subjectNameHash;
        #endif
        if (XMEMCMP(hash, subjectHash, SHA_DIGEST_SIZE) == 0) {
            ret = 1;
            break;
        }
        signers = signers->next;
    }
    UnLockMutex(&cm->caLock);

    return ret;
}


/* return CA if found, otherwise NULL */
Signer* GetCA(void* vp, byte* hash)
{
    CYASSL_CERT_MANAGER* cm = (CYASSL_CERT_MANAGER*)vp;
    Signer* ret = NULL;
    Signer* signers;
    word32  row = HashSigner(hash);

    if (cm == NULL)
        return NULL;

    if (LockMutex(&cm->caLock) != 0)
        return ret;

    signers = cm->caTable[row];
    while (signers) {
        byte* subjectHash;
        #ifndef NO_SKID
            subjectHash = signers->subjectKeyIdHash;
        #else
            subjectHash = signers->subjectNameHash;
        #endif
        if (XMEMCMP(hash, subjectHash, SHA_DIGEST_SIZE) == 0) {
            ret = signers;
            break;
        }
        signers = signers->next;
    }
    UnLockMutex(&cm->caLock);

    return ret;
}


#ifndef NO_SKID
/* return CA if found, otherwise NULL. Walk through hash table. */
Signer* GetCAByName(void* vp, byte* hash)
{
    CYASSL_CERT_MANAGER* cm = (CYASSL_CERT_MANAGER*)vp;
    Signer* ret = NULL;
    Signer* signers;
    word32  row;

    if (cm == NULL)
        return NULL;

    if (LockMutex(&cm->caLock) != 0)
        return ret;

    for (row = 0; row < CA_TABLE_SIZE && ret == NULL; row++) {
        signers = cm->caTable[row];
        while (signers && ret == NULL) {
            if (XMEMCMP(hash, signers->subjectNameHash, SHA_DIGEST_SIZE) == 0) {
                ret = signers;
            }
            signers = signers->next;
        }
    }
    UnLockMutex(&cm->caLock);

    return ret;
}
#endif


/* owns der, internal now uses too */
/* type flag ids from user or from chain received during verify
   don't allow chain ones to be added w/o isCA extension */
int AddCA(CYASSL_CERT_MANAGER* cm, buffer der, int type, int verify)
{
    int         ret;
    DecodedCert cert;
    Signer*     signer = 0;
    word32      row;
    byte*       subjectHash;

    CYASSL_MSG("Adding a CA");
    InitDecodedCert(&cert, der.buffer, der.length, cm->heap);
    ret = ParseCert(&cert, CA_TYPE, verify, cm);
    CYASSL_MSG("    Parsed new CA");

    #ifndef NO_SKID
        subjectHash = cert.extSubjKeyId;
    #else
        subjectHash = cert.subjectHash;
    #endif

    if (ret == 0 && cert.isCA == 0 && type != CYASSL_USER_CA) {
        CYASSL_MSG("    Can't add as CA if not actually one");
        ret = NOT_CA_ERROR;
    }
    #ifndef ALLOW_INVALID_CERTSIGN
        else if (ret == 0 && cert.isCA == 1 && type != CYASSL_USER_CA &&
                               (cert.extKeyUsage & KEYUSE_KEY_CERT_SIGN) == 0) {
            /* Intermediate CA certs are required to have the keyCertSign
            * extension set. User loaded root certs are not. */
            CYASSL_MSG("    Doesn't have key usage certificate signing");
            ret = NOT_CA_ERROR;
        }
    #endif
    else if (ret == 0 && AlreadySigner(cm, subjectHash)) {
        CYASSL_MSG("    Already have this CA, not adding again");
        (void)ret;
    }
    else if (ret == 0) {
        /* take over signer parts */
        signer = MakeSigner(cm->heap);
        if (!signer)
            ret = MEMORY_ERROR;
        else {
            signer->keyOID     = cert.keyOID;
            signer->publicKey  = cert.publicKey;
            signer->pubKeySize = cert.pubKeySize;
            signer->nameLen    = cert.subjectCNLen;
            signer->name       = cert.subjectCN;
            #ifndef IGNORE_NAME_CONSTRAINTS
                signer->permittedNames = cert.permittedNames;
                signer->excludedNames = cert.excludedNames;
            #endif
            #ifndef NO_SKID
                XMEMCPY(signer->subjectKeyIdHash,
                                            cert.extSubjKeyId, SHA_DIGEST_SIZE);
            #endif
            XMEMCPY(signer->subjectNameHash, cert.subjectHash, SHA_DIGEST_SIZE);
            signer->keyUsage = cert.extKeyUsageSet ? cert.extKeyUsage : 0xFFFF;
                                   /* If Key Usage not set, all uses valid. */
            signer->next = NULL;   /* in case lock fails */

            cert.publicKey = 0;  /* don't free here */
            cert.subjectCN = 0;
            #ifndef IGNORE_NAME_CONSTRAINTS
                cert.permittedNames = NULL;
                cert.excludedNames = NULL;
            #endif

            #ifndef NO_SKID
                row = HashSigner(signer->subjectKeyIdHash);
            #else
                row = HashSigner(signer->subjectNameHash);
            #endif

            if (LockMutex(&cm->caLock) == 0) {
                signer->next = cm->caTable[row];
                cm->caTable[row] = signer;   /* takes ownership */
                UnLockMutex(&cm->caLock);
                if (cm->caCacheCallback)
                    cm->caCacheCallback(der.buffer, (int)der.length, type);
            }
            else {
                CYASSL_MSG("    CA Mutex Lock failed");
                ret = BAD_MUTEX_E;
                FreeSigner(signer, cm->heap);
            }
        }
    }

    CYASSL_MSG("    Freeing Parsed CA");
    FreeDecodedCert(&cert);
    CYASSL_MSG("    Freeing der CA");
    XFREE(der.buffer, cm->heap, DYNAMIC_TYPE_CA);
    CYASSL_MSG("        OK Freeing der CA");

    CYASSL_LEAVE("AddCA", ret);
    if (ret == 0) return SSL_SUCCESS;
    return ret;
}

#endif /* !NO_CERTS */


#ifndef NO_SESSION_CACHE

    /* basic config gives a cache with 33 sessions, adequate for clients and
       embedded servers

       MEDIUM_SESSION_CACHE allows 1055 sessions, adequate for servers that
       aren't under heavy load, basically allows 200 new sessions per minute

       BIG_SESSION_CACHE yields 20,027 sessions

       HUGE_SESSION_CACHE yields 65,791 sessions, for servers under heavy load,
       allows over 13,000 new sessions per minute or over 200 new sessions per
       second

       SMALL_SESSION_CACHE only stores 6 sessions, good for embedded clients
       or systems where the default of nearly 3kB is too much RAM, this define
       uses less than 500 bytes RAM

       default SESSION_CACHE stores 33 sessions (no XXX_SESSION_CACHE defined)
    */
    #ifdef HUGE_SESSION_CACHE
        #define SESSIONS_PER_ROW 11
        #define SESSION_ROWS 5981
    #elif defined(BIG_SESSION_CACHE)
        #define SESSIONS_PER_ROW 7
        #define SESSION_ROWS 2861
    #elif defined(MEDIUM_SESSION_CACHE)
        #define SESSIONS_PER_ROW 5
        #define SESSION_ROWS 211
    #elif defined(SMALL_SESSION_CACHE)
        #define SESSIONS_PER_ROW 2
        #define SESSION_ROWS 3
    #else
        #define SESSIONS_PER_ROW 3
        #define SESSION_ROWS 11
    #endif

    typedef struct SessionRow {
        int nextIdx;                           /* where to place next one   */
        int totalCount;                        /* sessions ever on this row */
        CYASSL_SESSION Sessions[SESSIONS_PER_ROW];
    } SessionRow;

    static SessionRow SessionCache[SESSION_ROWS];

    static CyaSSL_Mutex session_mutex;   /* SessionCache mutex */

    #ifndef NO_CLIENT_CACHE

        typedef struct ClientSession {
            word16 serverRow;            /* SessionCache Row id */
            word16 serverIdx;            /* SessionCache Idx (column) */
        } ClientSession;

        typedef struct ClientRow {
            int nextIdx;                /* where to place next one   */
            int totalCount;             /* sessions ever on this row */
            ClientSession Clients[SESSIONS_PER_ROW];
        } ClientRow;

        static ClientRow ClientCache[SESSION_ROWS];  /* Client Cache */
                                                     /* uses session mutex */
    #endif  /* NO_CLIENT_CACHE */

#endif /* NO_SESSION_CACHE */


int CyaSSL_Init(void)
{
    int ret = SSL_SUCCESS;

    CYASSL_ENTER("CyaSSL_Init");

    if (initRefCount == 0) {
#ifndef NO_SESSION_CACHE
        if (InitMutex(&session_mutex) != 0)
            ret = BAD_MUTEX_E;
#endif
        if (InitMutex(&count_mutex) != 0)
            ret = BAD_MUTEX_E;
    }
    if (ret == SSL_SUCCESS) {
        if (LockMutex(&count_mutex) != 0) {
            CYASSL_MSG("Bad Lock Mutex count");
            return BAD_MUTEX_E;
        }
        initRefCount++;
        UnLockMutex(&count_mutex);
    }

    return ret;
}


#ifndef NO_CERTS

    /* Remove PEM header/footer, convert to ASN1, store any encrypted data
       info->consumed tracks of PEM bytes consumed in case multiple parts */
    int PemToDer(const unsigned char* buff, long longSz, int type,
                      buffer* der, void* heap, EncryptedInfo* info, int* eccKey)
    {
        char  header[PEM_LINE_LEN];
        char  footer[PEM_LINE_LEN];
        char* headerEnd;
        char* footerEnd;
        char* consumedEnd;
        char* bufferEnd = (char*)(buff + longSz);
        long  neededSz;
        int   ret      = 0;
        int   pkcs8    = 0;
        int   pkcs8Enc = 0;
        int   dynamicType = 0;
        int   sz = (int)longSz;

        (void)heap;
        (void)dynamicType;

        if (type == CERT_TYPE || type == CA_TYPE)  {
            XSTRNCPY(header, "-----BEGIN CERTIFICATE-----", sizeof(header));
            XSTRNCPY(footer, "-----END CERTIFICATE-----", sizeof(footer));
            dynamicType = (type == CA_TYPE) ? DYNAMIC_TYPE_CA :
                                              DYNAMIC_TYPE_CERT;
        } else if (type == CERTREQ_TYPE) {
            XSTRNCPY(header, "-----BEGIN CERTIFICATE REQUEST-----",
                     sizeof(header));
            XSTRNCPY(footer, "-----END CERTIFICATE REQUEST-----",
                     sizeof(footer));
            dynamicType = DYNAMIC_TYPE_KEY;
        } else if (type == DH_PARAM_TYPE) {
            XSTRNCPY(header, "-----BEGIN DH PARAMETERS-----", sizeof(header));
            XSTRNCPY(footer, "-----END DH PARAMETERS-----", sizeof(footer));
            dynamicType = DYNAMIC_TYPE_KEY;
        } else if (type == CRL_TYPE) {
            XSTRNCPY(header, "-----BEGIN X509 CRL-----", sizeof(header));
            XSTRNCPY(footer, "-----END X509 CRL-----", sizeof(footer));
            dynamicType = DYNAMIC_TYPE_CRL;
        } else {
            XSTRNCPY(header, "-----BEGIN RSA PRIVATE KEY-----", sizeof(header));
            XSTRNCPY(footer, "-----END RSA PRIVATE KEY-----", sizeof(footer));
            dynamicType = DYNAMIC_TYPE_KEY;
        }

        /* find header */
        headerEnd = XSTRNSTR((char*)buff, header, sz);
        if (!headerEnd && type == PRIVATEKEY_TYPE) {  /* may be pkcs8 */
            XSTRNCPY(header, "-----BEGIN PRIVATE KEY-----", sizeof(header));
            XSTRNCPY(footer, "-----END PRIVATE KEY-----", sizeof(footer));

            headerEnd = XSTRNSTR((char*)buff, header, sz);
            if (headerEnd)
                pkcs8 = 1;
            else {
                XSTRNCPY(header, "-----BEGIN ENCRYPTED PRIVATE KEY-----",
                        sizeof(header));
                XSTRNCPY(footer, "-----END ENCRYPTED PRIVATE KEY-----",
                        sizeof(footer));

                headerEnd = XSTRNSTR((char*)buff, header, sz);
                if (headerEnd) {
                    pkcs8Enc = 1;
                    (void)pkcs8Enc;  /* only opensslextra will read */
                }
            }
        }
        if (!headerEnd && type == PRIVATEKEY_TYPE) {  /* may be ecc */
            XSTRNCPY(header, "-----BEGIN EC PRIVATE KEY-----", sizeof(header));
            XSTRNCPY(footer, "-----END EC PRIVATE KEY-----", sizeof(footer));

            headerEnd = XSTRNSTR((char*)buff, header, sz);
            if (headerEnd)
                *eccKey = 1;
        }
        if (!headerEnd && type == PRIVATEKEY_TYPE) {  /* may be dsa */
            XSTRNCPY(header, "-----BEGIN DSA PRIVATE KEY-----", sizeof(header));
            XSTRNCPY(footer, "-----END DSA PRIVATE KEY-----", sizeof(footer));

            headerEnd = XSTRNSTR((char*)buff, header, sz);
        }
        if (!headerEnd) {
            CYASSL_MSG("Couldn't find PEM header");
            return SSL_NO_PEM_HEADER;
        }
        headerEnd += XSTRLEN(header);

        /* eat end of line */
        if (headerEnd[0] == '\n')
            headerEnd++;
        else if (headerEnd[1] == '\n')
            headerEnd += 2;
        else
            return SSL_BAD_FILE;

#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
    {
        /* remove encrypted header if there */
        char encHeader[] = "Proc-Type";
        char* line = XSTRNSTR(headerEnd, encHeader, PEM_LINE_LEN);
        if (line) {
            char* newline;
            char* finish;
            char* start  = XSTRNSTR(line, "DES", PEM_LINE_LEN);

            if (!start)
                start = XSTRNSTR(line, "AES", PEM_LINE_LEN);

            if (!start) return SSL_BAD_FILE;
            if (!info)  return SSL_BAD_FILE;

            finish = XSTRNSTR(start, ",", PEM_LINE_LEN);

            if (start && finish && (start < finish)) {
                newline = XSTRNSTR(finish, "\r", PEM_LINE_LEN);

                XMEMCPY(info->name, start, finish - start);
                info->name[finish - start] = 0;
                XMEMCPY(info->iv, finish + 1, sizeof(info->iv));

                if (!newline) newline = XSTRNSTR(finish, "\n", PEM_LINE_LEN);
                if (newline && (newline > finish)) {
                    info->ivSz = (word32)(newline - (finish + 1));
                    info->set = 1;
                }
                else
                    return SSL_BAD_FILE;
            }
            else
                return SSL_BAD_FILE;

            /* eat blank line */
            while (*newline == '\r' || *newline == '\n')
                newline++;
            headerEnd = newline;
        }
    }
#endif /* OPENSSL_EXTRA || HAVE_WEBSERVER */

        /* find footer */
        footerEnd = XSTRNSTR((char*)buff, footer, sz);
        if (!footerEnd) return SSL_BAD_FILE;

        consumedEnd = footerEnd + XSTRLEN(footer);

        if (consumedEnd < bufferEnd) {  /* handle no end of line on last line */
            /* eat end of line */
            if (consumedEnd[0] == '\n')
                consumedEnd++;
            else if (consumedEnd[1] == '\n')
                consumedEnd += 2;
            else
                return SSL_BAD_FILE;
        }

        if (info)
            info->consumed = (long)(consumedEnd - (char*)buff);

        /* set up der buffer */
        neededSz = (long)(footerEnd - headerEnd);
        if (neededSz > sz || neededSz < 0) return SSL_BAD_FILE;
        der->buffer = (byte*) XMALLOC(neededSz, heap, dynamicType);
        if (!der->buffer) return MEMORY_ERROR;
        der->length = (word32)neededSz;

        if (Base64_Decode((byte*)headerEnd, (word32)neededSz, der->buffer,
                          &der->length) < 0)
            return SSL_BAD_FILE;

        if (pkcs8) {
            /* convert and adjust length */
            if ( (ret = ToTraditional(der->buffer, der->length)) < 0 ) {
                return ret;
            } else {
                der->length = ret;
                return 0;
            }
        }

#if (defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)) && !defined(NO_PWDBASED)
         if (pkcs8Enc) {
            int  passwordSz;
            char password[80];

            if (!info || !info->ctx || !info->ctx->passwd_cb)
                return SSL_BAD_FILE;  /* no callback error */
            passwordSz = info->ctx->passwd_cb(password, sizeof(password), 0,
                                              info->ctx->userdata);
            /* convert and adjust length */
            if ( (ret = ToTraditionalEnc(der->buffer, der->length, password,
                                         passwordSz)) < 0 ) {
                return ret;
            } else {
                der->length = ret;
                return 0;
            }
         }
#endif

        return 0;
    }


    /* process the buffer buff, legnth sz, into ctx of format and type
       used tracks bytes consumed, userChain specifies a user cert chain
       to pass during the handshake */
    static int ProcessBuffer(CYASSL_CTX* ctx, const unsigned char* buff,
                             long sz, int format, int type, CYASSL* ssl,
                             long* used, int userChain)
    {
        EncryptedInfo info;
        buffer        der;        /* holds DER or RAW (for NTRU) */
        int           ret;
        int           dynamicType = 0;
        int           eccKey = 0;
        int           rsaKey = 0;
        void*         heap = ctx ? ctx->heap : NULL;

        info.set      = 0;
        info.ctx      = ctx;
        info.consumed = 0;
        der.buffer    = 0;

        (void)dynamicType;
        (void)rsaKey;

        if (used)
            *used = sz;     /* used bytes default to sz, PEM chain may shorten*/

        if (format != SSL_FILETYPE_ASN1 && format != SSL_FILETYPE_PEM
                                        && format != SSL_FILETYPE_RAW)
            return SSL_BAD_FILETYPE;

        if (ctx == NULL && ssl == NULL)
            return BAD_FUNC_ARG;

        if (type == CA_TYPE)
            dynamicType = DYNAMIC_TYPE_CA;
        else if (type == CERT_TYPE)
            dynamicType = DYNAMIC_TYPE_CERT;
        else
            dynamicType = DYNAMIC_TYPE_KEY;

        if (format == SSL_FILETYPE_PEM) {
            ret = PemToDer(buff, sz, type, &der, heap, &info, &eccKey);
            if (ret < 0) {
                XFREE(der.buffer, heap, dynamicType);
                return ret;
            }
            if (used)
                *used = info.consumed;
            /* we may have a user cert chain, try to consume */
            if (userChain && type == CERT_TYPE && info.consumed < sz) {
                byte   staticBuffer[FILE_BUFFER_SIZE];  /* tmp chain buffer */
                byte*  chainBuffer = staticBuffer;
                byte*  shrinked    = NULL;   /* shrinked to size chainBuffer
                                              * or staticBuffer */
                int    dynamicBuffer = 0;
                word32 bufferSz = sizeof(staticBuffer);
                long   consumed = info.consumed;
                word32 idx = 0;
                int    gotOne = 0;

                if ( (sz - consumed) > (int)bufferSz) {
                    CYASSL_MSG("Growing Tmp Chain Buffer");
                    bufferSz = (word32)(sz - consumed);
                               /* will shrink to actual size */
                    chainBuffer = (byte*)XMALLOC(bufferSz, heap,
                                                 DYNAMIC_TYPE_FILE);
                    if (chainBuffer == NULL) {
                        XFREE(der.buffer, heap, dynamicType);
                        return MEMORY_E;
                    }
                    dynamicBuffer = 1;
                }

                CYASSL_MSG("Processing Cert Chain");
                while (consumed < sz) {
                    buffer part;
                    info.consumed = 0;
                    part.buffer = 0;

                    ret = PemToDer(buff + consumed, sz - consumed, type, &part,
                                   heap, &info, &eccKey);
                    if (ret == 0) {
                        gotOne = 1;
                        if ( (idx + part.length) > bufferSz) {
                            CYASSL_MSG("   Cert Chain bigger than buffer");
                            ret = BUFFER_E;
                        }
                        else {
                            c32to24(part.length, &chainBuffer[idx]);
                            idx += CERT_HEADER_SZ;
                            XMEMCPY(&chainBuffer[idx], part.buffer,part.length);
                            idx += part.length;
                            consumed  += info.consumed;
                            if (used)
                                *used += info.consumed;
                        }
                    }

                    XFREE(part.buffer, heap, dynamicType);

                    if (ret == SSL_NO_PEM_HEADER && gotOne) {
                        CYASSL_MSG("We got one good PEM so stuff at end ok");
                        break;
                    }

                    if (ret < 0) {
                        CYASSL_MSG("   Error in Cert in Chain");
                        if (dynamicBuffer)
                            XFREE(chainBuffer, heap, DYNAMIC_TYPE_FILE);
                        XFREE(der.buffer, heap, dynamicType);
                        return ret;
                    }
                    CYASSL_MSG("   Consumed another Cert in Chain");
                }
                CYASSL_MSG("Finished Processing Cert Chain");

                /* only retain actual size used */
                shrinked = (byte*)XMALLOC(idx, heap, dynamicType);
                if (shrinked) {
                    if (ssl) {
                        if (ssl->buffers.certChain.buffer &&
                                         ssl->buffers.weOwnCertChain) {
                            XFREE(ssl->buffers.certChain.buffer, heap,
                                  dynamicType);
                        }
                        ssl->buffers.certChain.buffer = shrinked;
                        ssl->buffers.certChain.length = idx;
                        XMEMCPY(ssl->buffers.certChain.buffer, chainBuffer,idx);
                        ssl->buffers.weOwnCertChain = 1;
                    } else if (ctx) {
                        if (ctx->certChain.buffer)
                            XFREE(ctx->certChain.buffer, heap, dynamicType);
                        ctx->certChain.buffer = shrinked;
                        ctx->certChain.length = idx;
                        XMEMCPY(ctx->certChain.buffer, chainBuffer, idx);
                    }
                }
                if (dynamicBuffer)
                    XFREE(chainBuffer, heap, DYNAMIC_TYPE_FILE);
                if (shrinked == NULL) {
                    XFREE(der.buffer, heap, dynamicType);
                    return MEMORY_E;
                }
            }
        }
        else {  /* ASN1 (DER) or RAW (NTRU) */
            der.buffer = (byte*) XMALLOC(sz, heap, dynamicType);
            if (!der.buffer) return MEMORY_ERROR;
            XMEMCPY(der.buffer, buff, sz);
            der.length = (word32)sz;
        }

#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
        if (info.set) {
            /* decrypt */
            char password[80];
            int  passwordSz;

            byte key[AES_256_KEY_SIZE];
            byte  iv[AES_IV_SIZE];

            if (!ctx || !ctx->passwd_cb) {
                XFREE(der.buffer, heap, dynamicType);
                return NO_PASSWORD;
            }

            /* use file's salt for key derivation, hex decode first */
            if (Base16_Decode(info.iv, info.ivSz, info.iv, &info.ivSz) != 0) {
                XFREE(der.buffer, heap, dynamicType);
                return ASN_INPUT_E;
            }

            passwordSz = ctx->passwd_cb(password, sizeof(password), 0,
                                    ctx->userdata);
            if ( (ret = EVP_BytesToKey(info.name, "MD5", info.iv,
                            (byte*)password, passwordSz, 1, key, iv)) <= 0) {
                XFREE(der.buffer, heap, dynamicType);
                return ret;
            }

            if (XSTRNCMP(info.name, "DES-CBC", 7) == 0) {
                Des enc;

                ret = Des_SetKey(&enc, key, info.iv, DES_DECRYPTION);
                if (ret != 0)
                    return ret;

                Des_CbcDecrypt(&enc, der.buffer, der.buffer, der.length);
            }
            else if (XSTRNCMP(info.name, "DES-EDE3-CBC", 13) == 0) {
                Des3 enc;

                ret = Des3_SetKey(&enc, key, info.iv, DES_DECRYPTION);
                if (ret != 0)
                    return ret;

                ret = Des3_CbcDecrypt(&enc, der.buffer, der.buffer, der.length);
                if (ret != 0)
                    return ret;
            }
            else if (XSTRNCMP(info.name, "AES-128-CBC", 13) == 0) {
                Aes enc;
                ret = AesSetKey(&enc, key, AES_128_KEY_SIZE, info.iv,
                                AES_DECRYPTION);
                if (ret == 0)
                    ret = AesCbcDecrypt(&enc, der.buffer,der.buffer,der.length);
            }
            else if (XSTRNCMP(info.name, "AES-192-CBC", 13) == 0) {
                Aes enc;
                ret = AesSetKey(&enc, key, AES_192_KEY_SIZE, info.iv,
                                AES_DECRYPTION);
                if (ret == 0)
                    ret = AesCbcDecrypt(&enc, der.buffer,der.buffer,der.length);
            }
            else if (XSTRNCMP(info.name, "AES-256-CBC", 13) == 0) {
                Aes enc;
                ret = AesSetKey(&enc, key, AES_256_KEY_SIZE, info.iv,
                                AES_DECRYPTION);
                if (ret == 0)
                    ret = AesCbcDecrypt(&enc, der.buffer,der.buffer,der.length);
            }
            else {
                XFREE(der.buffer, heap, dynamicType);
                return SSL_BAD_FILE;
            }

            if (ret != 0) {
                XFREE(der.buffer, heap, dynamicType);
                return ret;
            }
        }
#endif /* OPENSSL_EXTRA || HAVE_WEBSERVER */

        if (type == CA_TYPE) {
            if (ctx == NULL) {
                CYASSL_MSG("Need context for CA load");
                XFREE(der.buffer, heap, dynamicType);
                return BAD_FUNC_ARG;
            }
            return AddCA(ctx->cm, der, CYASSL_USER_CA, ctx->verifyPeer);
                                                          /* takes der over */
        }
        else if (type == CERT_TYPE) {
            if (ssl) {
                if (ssl->buffers.weOwnCert && ssl->buffers.certificate.buffer)
                    XFREE(ssl->buffers.certificate.buffer, heap,
                          dynamicType);
                ssl->buffers.certificate = der;
                ssl->buffers.weOwnCert = 1;
            }
            else if (ctx) {
                if (ctx->certificate.buffer)
                    XFREE(ctx->certificate.buffer, heap, dynamicType);
                ctx->certificate = der;     /* takes der over */
            }
        }
        else if (type == PRIVATEKEY_TYPE) {
            if (ssl) {
                if (ssl->buffers.weOwnKey && ssl->buffers.key.buffer)
                    XFREE(ssl->buffers.key.buffer, heap, dynamicType);
                ssl->buffers.key = der;
                ssl->buffers.weOwnKey = 1;
            }
            else if (ctx) {
                if (ctx->privateKey.buffer)
                    XFREE(ctx->privateKey.buffer, heap, dynamicType);
                ctx->privateKey = der;      /* takes der over */
            }
        }
        else {
            XFREE(der.buffer, heap, dynamicType);
            return SSL_BAD_CERTTYPE;
        }

        if (type == PRIVATEKEY_TYPE && format != SSL_FILETYPE_RAW) {
#ifndef NO_RSA
            if (!eccKey) {
                /* make sure RSA key can be used */
                RsaKey key;
                word32 idx = 0;

                ret = InitRsaKey(&key, 0);
                if (ret != 0) return ret;
                if (RsaPrivateKeyDecode(der.buffer,&idx,&key,der.length) != 0) {
#ifdef HAVE_ECC
                    /* could have DER ECC (or pkcs8 ecc), no easy way to tell */
                    eccKey = 1;  /* so try it out */
#endif
                    if (!eccKey) {
                        FreeRsaKey(&key);
                        return SSL_BAD_FILE;
                    }
                } else {
                    rsaKey = 1;
                    (void)rsaKey;  /* for no ecc builds */
                }
                FreeRsaKey(&key);
            }
#endif
#ifdef HAVE_ECC
            if (!rsaKey) {
                /* make sure ECC key can be used */
                word32  idx = 0;
                ecc_key key;

                ecc_init(&key);
                if (EccPrivateKeyDecode(der.buffer,&idx,&key,der.length) != 0) {
                    ecc_free(&key);
                    return SSL_BAD_FILE;
                }
                ecc_free(&key);
                eccKey = 1;
                if (ctx)
                    ctx->haveStaticECC = 1;
                if (ssl)
                    ssl->options.haveStaticECC = 1;
            }
#endif /* HAVE_ECC */
        }
        else if (type == CERT_TYPE) {
            DecodedCert cert;

            CYASSL_MSG("Checking cert signature type");
            InitDecodedCert(&cert, der.buffer, der.length, heap);

            if (DecodeToKey(&cert, 0) < 0) {
                CYASSL_MSG("Decode to key failed");
                return SSL_BAD_FILE;
            }
            switch (cert.signatureOID) {
                case CTC_SHAwECDSA:
                case CTC_SHA256wECDSA:
                case CTC_SHA384wECDSA:
                case CTC_SHA512wECDSA:
                    CYASSL_MSG("ECDSA cert signature");
                    if (ctx)
                        ctx->haveECDSAsig = 1;
                    if (ssl)
                        ssl->options.haveECDSAsig = 1;
                    break;
                default:
                    CYASSL_MSG("Not ECDSA cert signature");
                    break;
            }

#ifdef HAVE_ECC
            if (ctx)
                ctx->pkCurveOID = cert.pkCurveOID;
            if (ssl)
                ssl->pkCurveOID = cert.pkCurveOID;
#endif

            FreeDecodedCert(&cert);
        }

        return SSL_SUCCESS;
    }




/* CA PEM file for verification, may have multiple/chain certs to process */
static int ProcessChainBuffer(CYASSL_CTX* ctx, const unsigned char* buff,
                            long sz, int format, int type, CYASSL* ssl)
{
    long used   = 0;
    int  ret    = 0;
    int  gotOne = 0;

    CYASSL_MSG("Processing CA PEM file");
    while (used < sz) {
        long consumed = 0;

        ret = ProcessBuffer(ctx, buff + used, sz - used, format, type, ssl,
                            &consumed, 0);

        if (ret == SSL_NO_PEM_HEADER && gotOne) {
            CYASSL_MSG("We got one good PEM file so stuff at end ok");
            ret = SSL_SUCCESS;
            break;
        }

        if (ret < 0)
            break;

        CYASSL_MSG("   Processed a CA");
        gotOne = 1;
        used += consumed;
    }

    return ret;
}


/* Verify the ceritficate, SSL_SUCCESS for ok, < 0 for error */
int CyaSSL_CertManagerVerifyBuffer(CYASSL_CERT_MANAGER* cm, const byte* buff,
                                   long sz, int format)
{
    int ret = 0;
    int eccKey = 0;  /* not used */

    DecodedCert cert;
    buffer      der;

    CYASSL_ENTER("CyaSSL_CertManagerVerifyBuffer");

    der.buffer = NULL;
    der.length = 0;

    if (format == SSL_FILETYPE_PEM) {
        EncryptedInfo info;

        info.set      = 0;
        info.ctx      = NULL;
        info.consumed = 0;
        ret = PemToDer(buff, sz, CERT_TYPE, &der, cm->heap, &info, &eccKey);
        InitDecodedCert(&cert, der.buffer, der.length, cm->heap);
    }
    else
        InitDecodedCert(&cert, (byte*)buff, (word32)sz, cm->heap);

    if (ret == 0)
        ret = ParseCertRelative(&cert, CERT_TYPE, 1, cm);
#ifdef HAVE_CRL
    if (ret == 0 && cm->crlEnabled)
        ret = CheckCertCRL(cm->crl, &cert);
#endif

    FreeDecodedCert(&cert);
    XFREE(der.buffer, cm->heap, DYNAMIC_TYPE_CERT);

    if (ret == 0)
        return SSL_SUCCESS;
    return ret;
}


/* turn on OCSP if off and compiled in, set options */
int CyaSSL_CertManagerEnableOCSP(CYASSL_CERT_MANAGER* cm, int options)
{
    int ret = SSL_SUCCESS;

    (void)options;

    CYASSL_ENTER("CyaSSL_CertManagerEnableOCSP");
    if (cm == NULL)
        return BAD_FUNC_ARG;

    #ifdef HAVE_OCSP
        if (cm->ocsp == NULL) {
            cm->ocsp = (CYASSL_OCSP*)XMALLOC(sizeof(CYASSL_OCSP), cm->heap,
                                                             DYNAMIC_TYPE_OCSP);
            if (cm->ocsp == NULL)
                return MEMORY_E;

            if (InitOCSP(cm->ocsp, cm) != 0) {
                CYASSL_MSG("Init OCSP failed");
                FreeOCSP(cm->ocsp, 1);
                cm->ocsp = NULL;
                return SSL_FAILURE;
            }
        }
        cm->ocspEnabled = 1;
        if (options & CYASSL_OCSP_URL_OVERRIDE)
            cm->ocspUseOverrideURL = 1;
        if (options & CYASSL_OCSP_NO_NONCE)
            cm->ocspSendNonce = 0;
        else
            cm->ocspSendNonce = 1;
        #ifndef CYASSL_USER_IO
            cm->ocspIOCb = EmbedOcspLookup;
            cm->ocspRespFreeCb = EmbedOcspRespFree;
        #endif /* CYASSL_USER_IO */
    #else
        ret = NOT_COMPILED_IN;
    #endif

    return ret;
}


int CyaSSL_CertManagerDisableOCSP(CYASSL_CERT_MANAGER* cm)
{
    CYASSL_ENTER("CyaSSL_CertManagerDisableOCSP");
    if (cm == NULL)
        return BAD_FUNC_ARG;

    cm->ocspEnabled = 0;

    return SSL_SUCCESS;
}


#ifdef HAVE_OCSP


/* check CRL if enabled, SSL_SUCCESS  */
int CyaSSL_CertManagerCheckOCSP(CYASSL_CERT_MANAGER* cm, byte* der, int sz)
{
    int         ret;
    DecodedCert cert;

    CYASSL_ENTER("CyaSSL_CertManagerCheckOCSP");

    if (cm == NULL)
        return BAD_FUNC_ARG;

    if (cm->ocspEnabled == 0)
        return SSL_SUCCESS;

    InitDecodedCert(&cert, der, sz, NULL);

    ret = ParseCertRelative(&cert, CERT_TYPE, NO_VERIFY, cm);
    if (ret != 0) {
        CYASSL_MSG("ParseCert failed");
        return ret;
    }
    else {
        ret = CheckCertOCSP(cm->ocsp, &cert);
        if (ret != 0) {
            CYASSL_MSG("CheckCertOCSP failed");
        }
    }

    FreeDecodedCert(&cert);

    if (ret == 0)
        return SSL_SUCCESS;  /* convert */

    return ret;
}


int CyaSSL_CertManagerSetOCSPOverrideURL(CYASSL_CERT_MANAGER* cm,
                                                                const char* url)
{
    CYASSL_ENTER("CyaSSL_CertManagerSetOCSPOverrideURL");
    if (cm == NULL)
        return BAD_FUNC_ARG;

    XFREE(cm->ocspOverrideURL, cm->heap, 0);
    if (url != NULL) {
        int urlSz = (int)XSTRLEN(url) + 1;
        cm->ocspOverrideURL = (char*)XMALLOC(urlSz, cm->heap, 0);
        if (cm->ocspOverrideURL != NULL) {
            XMEMCPY(cm->ocspOverrideURL, url, urlSz);
        }
        else
            return MEMORY_E;
    }
    else
        cm->ocspOverrideURL = NULL;

    return SSL_SUCCESS;
}


int CyaSSL_CertManagerSetOCSP_Cb(CYASSL_CERT_MANAGER* cm,
                        CbOCSPIO ioCb, CbOCSPRespFree respFreeCb, void* ioCbCtx)
{
    CYASSL_ENTER("CyaSSL_CertManagerSetOCSP_Cb");
    if (cm == NULL)
        return BAD_FUNC_ARG;

    cm->ocspIOCb = ioCb;
    cm->ocspRespFreeCb = respFreeCb;
    cm->ocspIOCtx = ioCbCtx;

    return SSL_SUCCESS;
}


int CyaSSL_EnableOCSP(CYASSL* ssl, int options)
{
    CYASSL_ENTER("CyaSSL_EnableOCSP");
    if (ssl)
        return CyaSSL_CertManagerEnableOCSP(ssl->ctx->cm, options);
    else
        return BAD_FUNC_ARG;
}


int CyaSSL_DisableOCSP(CYASSL* ssl)
{
    CYASSL_ENTER("CyaSSL_DisableOCSP");
    if (ssl)
        return CyaSSL_CertManagerDisableOCSP(ssl->ctx->cm);
    else
        return BAD_FUNC_ARG;
}


int CyaSSL_SetOCSP_OverrideURL(CYASSL* ssl, const char* url)
{
    CYASSL_ENTER("CyaSSL_SetOCSP_OverrideURL");
    if (ssl)
        return CyaSSL_CertManagerSetOCSPOverrideURL(ssl->ctx->cm, url);
    else
        return BAD_FUNC_ARG;
}


int CyaSSL_SetOCSP_Cb(CYASSL* ssl,
                        CbOCSPIO ioCb, CbOCSPRespFree respFreeCb, void* ioCbCtx)
{
    CYASSL_ENTER("CyaSSL_SetOCSP_Cb");
    if (ssl)
        return CyaSSL_CertManagerSetOCSP_Cb(ssl->ctx->cm,
                                                     ioCb, respFreeCb, ioCbCtx);
    else
        return BAD_FUNC_ARG;
}


int CyaSSL_CTX_EnableOCSP(CYASSL_CTX* ctx, int options)
{
    CYASSL_ENTER("CyaSSL_CTX_EnableOCSP");
    if (ctx)
        return CyaSSL_CertManagerEnableOCSP(ctx->cm, options);
    else
        return BAD_FUNC_ARG;
}


int CyaSSL_CTX_DisableOCSP(CYASSL_CTX* ctx)
{
    CYASSL_ENTER("CyaSSL_CTX_DisableOCSP");
    if (ctx)
        return CyaSSL_CertManagerDisableOCSP(ctx->cm);
    else
        return BAD_FUNC_ARG;
}


int CyaSSL_CTX_SetOCSP_OverrideURL(CYASSL_CTX* ctx, const char* url)
{
    CYASSL_ENTER("CyaSSL_SetOCSP_OverrideURL");
    if (ctx)
        return CyaSSL_CertManagerSetOCSPOverrideURL(ctx->cm, url);
    else
        return BAD_FUNC_ARG;
}


int CyaSSL_CTX_SetOCSP_Cb(CYASSL_CTX* ctx,
                        CbOCSPIO ioCb, CbOCSPRespFree respFreeCb, void* ioCbCtx)
{
    CYASSL_ENTER("CyaSSL_CTX_SetOCSP_Cb");
    if (ctx)
        return CyaSSL_CertManagerSetOCSP_Cb(ctx->cm, ioCb, respFreeCb, ioCbCtx);
    else
        return BAD_FUNC_ARG;
}


#endif /* HAVE_OCSP */


#ifndef NO_FILESYSTEM

    #if defined(CYASSL_MDK_ARM)
        extern FILE * CyaSSL_fopen(const char *name, const char *mode) ;
        #define XFOPEN     CyaSSL_fopen
    #else
        #define XFOPEN     fopen
    #endif

/* process a file with name fname into ctx of format and type
   userChain specifies a user certificate chain to pass during handshake */
int ProcessFile(CYASSL_CTX* ctx, const char* fname, int format, int type,
                CYASSL* ssl, int userChain, CYASSL_CRL* crl)
{
    byte   staticBuffer[FILE_BUFFER_SIZE];
    byte*  myBuffer = staticBuffer;
    int    dynamic = 0;
    int    ret;
    long   sz = 0;
    XFILE  file;
    void*  heapHint = ctx ? ctx->heap : NULL;

    (void)crl;
    (void)heapHint;

    if (fname == NULL) return SSL_BAD_FILE;

    file = XFOPEN(fname, "rb");
    if (file == XBADFILE) return SSL_BAD_FILE;
    XFSEEK(file, 0, XSEEK_END);
    sz = XFTELL(file);
    XREWIND(file);

    if (sz > (long)sizeof(staticBuffer)) {
        CYASSL_MSG("Getting dynamic buffer");
        myBuffer = (byte*)XMALLOC(sz, heapHint, DYNAMIC_TYPE_FILE);
        if (myBuffer == NULL) {
            XFCLOSE(file);
            return SSL_BAD_FILE;
        }
        dynamic = 1;
    }
    else if (sz < 0) {
        XFCLOSE(file);
        return SSL_BAD_FILE;
    }

    if ( (ret = (int)XFREAD(myBuffer, sz, 1, file)) < 0)
        ret = SSL_BAD_FILE;
    else {
        if (type == CA_TYPE && format == SSL_FILETYPE_PEM)
            ret = ProcessChainBuffer(ctx, myBuffer, sz, format, type, ssl);
#ifdef HAVE_CRL
        else if (type == CRL_TYPE)
            ret = BufferLoadCRL(crl, myBuffer, sz, format);
#endif
        else
            ret = ProcessBuffer(ctx, myBuffer, sz, format, type, ssl, NULL,
                                userChain);
    }

    XFCLOSE(file);
    if (dynamic) XFREE(myBuffer, heapHint, DYNAMIC_TYPE_FILE);

    return ret;
}


/* loads file then loads each file in path, no c_rehash */
int CyaSSL_CTX_load_verify_locations(CYASSL_CTX* ctx, const char* file,
                                     const char* path)
{
    int ret = SSL_SUCCESS;

    CYASSL_ENTER("CyaSSL_CTX_load_verify_locations");
    (void)path;

    if (ctx == NULL || (file == NULL && path == NULL) )
        return SSL_FAILURE;

    if (file)
        ret = ProcessFile(ctx, file, SSL_FILETYPE_PEM, CA_TYPE, NULL, 0, NULL);

    if (ret == SSL_SUCCESS && path) {
        /* try to load each regular file in path */
    #ifdef USE_WINDOWS_API
        WIN32_FIND_DATAA FindFileData;
        HANDLE hFind;
        char   name[MAX_FILENAME_SZ];

        XMEMSET(name, 0, sizeof(name));
        XSTRNCPY(name, path, MAX_FILENAME_SZ - 4);
        XSTRNCAT(name, "\\*", 3);

        hFind = FindFirstFileA(name, &FindFileData);
        if (hFind == INVALID_HANDLE_VALUE) {
            CYASSL_MSG("FindFirstFile for path verify locations failed");
            return BAD_PATH_ERROR;
        }

        do {
            if (FindFileData.dwFileAttributes != FILE_ATTRIBUTE_DIRECTORY) {
                XSTRNCPY(name, path, MAX_FILENAME_SZ/2 - 3);
                XSTRNCAT(name, "\\", 2);
                XSTRNCAT(name, FindFileData.cFileName, MAX_FILENAME_SZ/2);

                ret = ProcessFile(ctx, name, SSL_FILETYPE_PEM, CA_TYPE, NULL,0,
                                  NULL);
            }
        } while (ret == SSL_SUCCESS && FindNextFileA(hFind, &FindFileData));

        FindClose(hFind);
    #elif !defined(NO_CYASSL_DIR)
        struct dirent* entry;
        DIR*   dir = opendir(path);

        if (dir == NULL) {
            CYASSL_MSG("opendir path verify locations failed");
            return BAD_PATH_ERROR;
        }
        while ( ret == SSL_SUCCESS && (entry = readdir(dir)) != NULL) {
            char name[MAX_FILENAME_SZ];
            struct stat s;

            XMEMSET(name, 0, sizeof(name));
            XSTRNCPY(name, path, MAX_FILENAME_SZ/2 - 2);
            XSTRNCAT(name, "/", 1);
            XSTRNCAT(name, entry->d_name, MAX_FILENAME_SZ/2);

            if (stat(name, &s) != 0) {
                CYASSL_MSG("stat on name failed");
                closedir(dir);
                return BAD_PATH_ERROR;
            }
            if (s.st_mode & S_IFREG) {
                ret = ProcessFile(ctx, name, SSL_FILETYPE_PEM, CA_TYPE, NULL,0,
                                  NULL);
            }
        }
        closedir(dir);
    #endif
    }

    return ret;
}


/* Verify the ceritficate, SSL_SUCCESS for ok, < 0 for error */
int CyaSSL_CertManagerVerify(CYASSL_CERT_MANAGER* cm, const char* fname,
                             int format)
{
    int    ret = SSL_FATAL_ERROR;
    byte   staticBuffer[FILE_BUFFER_SIZE];
    byte*  myBuffer = staticBuffer;
    int    dynamic = 0;
    long   sz = 0;
    XFILE  file = XFOPEN(fname, "rb");

    CYASSL_ENTER("CyaSSL_CertManagerVerify");

    if (file == XBADFILE) return SSL_BAD_FILE;
    XFSEEK(file, 0, XSEEK_END);
    sz = XFTELL(file);
    XREWIND(file);

    if (sz > MAX_CYASSL_FILE_SIZE || sz < 0) {
        CYASSL_MSG("CertManagerVerify file bad size");
        XFCLOSE(file);
        return SSL_BAD_FILE;
    }

    if (sz > (long)sizeof(staticBuffer)) {
        CYASSL_MSG("Getting dynamic buffer");
        myBuffer = (byte*) XMALLOC(sz, cm->heap, DYNAMIC_TYPE_FILE);
        if (myBuffer == NULL) {
            XFCLOSE(file);
            return SSL_BAD_FILE;
        }
        dynamic = 1;
    }

    if ( (ret = (int)XFREAD(myBuffer, sz, 1, file)) < 0)
        ret = SSL_BAD_FILE;
    else
        ret = CyaSSL_CertManagerVerifyBuffer(cm, myBuffer, sz, format);

    XFCLOSE(file);
    if (dynamic) XFREE(myBuffer, cm->heap, DYNAMIC_TYPE_FILE);

    return ret;
}


static INLINE CYASSL_METHOD* cm_pick_method(void)
{
    #ifndef NO_CYASSL_CLIENT
        #ifdef NO_OLD_TLS
            return CyaTLSv1_2_client_method();
        #else
            return CyaSSLv3_client_method();
        #endif
    #elif !defined(NO_CYASSL_SERVER)
        #ifdef NO_OLD_TLS
            return CyaTLSv1_2_server_method();
        #else
            return CyaSSLv3_server_method();
        #endif
    #else
        return NULL;
    #endif
}


/* like load verify locations, 1 for success, < 0 for error */
int CyaSSL_CertManagerLoadCA(CYASSL_CERT_MANAGER* cm, const char* file,
                             const char* path)
{
    int ret = SSL_FATAL_ERROR;
    CYASSL_CTX* tmp;

    CYASSL_ENTER("CyaSSL_CertManagerLoadCA");

    if (cm == NULL) {
        CYASSL_MSG("No CertManager error");
        return ret;
    }
    tmp = CyaSSL_CTX_new(cm_pick_method());

    if (tmp == NULL) {
        CYASSL_MSG("CTX new failed");
        return ret;
    }

    /* for tmp use */
    CyaSSL_CertManagerFree(tmp->cm);
    tmp->cm = cm;

    ret = CyaSSL_CTX_load_verify_locations(tmp, file, path);

    /* don't loose our good one */
    tmp->cm = NULL;
    CyaSSL_CTX_free(tmp);

    return ret;
}



/* turn on CRL if off and compiled in, set options */
int CyaSSL_CertManagerEnableCRL(CYASSL_CERT_MANAGER* cm, int options)
{
    int ret = SSL_SUCCESS;

    (void)options;

    CYASSL_ENTER("CyaSSL_CertManagerEnableCRL");
    if (cm == NULL)
        return BAD_FUNC_ARG;

    #ifdef HAVE_CRL
        if (cm->crl == NULL) {
            cm->crl = (CYASSL_CRL*)XMALLOC(sizeof(CYASSL_CRL), cm->heap,
                                           DYNAMIC_TYPE_CRL);
            if (cm->crl == NULL)
                return MEMORY_E;

            if (InitCRL(cm->crl, cm) != 0) {
                CYASSL_MSG("Init CRL failed");
                FreeCRL(cm->crl, 1);
                cm->crl = NULL;
                return SSL_FAILURE;
            }
        }
        cm->crlEnabled = 1;
        if (options & CYASSL_CRL_CHECKALL)
            cm->crlCheckAll = 1;
    #else
        ret = NOT_COMPILED_IN;
    #endif

    return ret;
}


int CyaSSL_CertManagerDisableCRL(CYASSL_CERT_MANAGER* cm)
{
    CYASSL_ENTER("CyaSSL_CertManagerDisableCRL");
    if (cm == NULL)
        return BAD_FUNC_ARG;

    cm->crlEnabled = 0;

    return SSL_SUCCESS;
}


int CyaSSL_CTX_check_private_key(CYASSL_CTX* ctx)
{
    /* TODO: check private against public for RSA match */
    (void)ctx;
    CYASSL_ENTER("SSL_CTX_check_private_key");
    return SSL_SUCCESS;
}


#ifdef HAVE_CRL


/* check CRL if enabled, SSL_SUCCESS  */
int CyaSSL_CertManagerCheckCRL(CYASSL_CERT_MANAGER* cm, byte* der, int sz)
{
    int         ret;
    DecodedCert cert;

    CYASSL_ENTER("CyaSSL_CertManagerCheckCRL");

    if (cm == NULL)
        return BAD_FUNC_ARG;

    if (cm->crlEnabled == 0)
        return SSL_SUCCESS;

    InitDecodedCert(&cert, der, sz, NULL);

    ret = ParseCertRelative(&cert, CERT_TYPE, NO_VERIFY, cm);
    if (ret != 0) {
        CYASSL_MSG("ParseCert failed");
        return ret;
    }
    else {
        ret = CheckCertCRL(cm->crl, &cert);
        if (ret != 0) {
            CYASSL_MSG("CheckCertCRL failed");
        }
    }

    FreeDecodedCert(&cert);

    if (ret == 0)
        return SSL_SUCCESS;  /* convert */

    return ret;
}


int CyaSSL_CertManagerSetCRL_Cb(CYASSL_CERT_MANAGER* cm, CbMissingCRL cb)
{
    CYASSL_ENTER("CyaSSL_CertManagerSetCRL_Cb");
    if (cm == NULL)
        return BAD_FUNC_ARG;

    cm->cbMissingCRL = cb;

    return SSL_SUCCESS;
}


int CyaSSL_CertManagerLoadCRL(CYASSL_CERT_MANAGER* cm, const char* path,
                              int type, int monitor)
{
    CYASSL_ENTER("CyaSSL_CertManagerLoadCRL");
    if (cm == NULL)
        return BAD_FUNC_ARG;

    if (cm->crl == NULL) {
        if (CyaSSL_CertManagerEnableCRL(cm, 0) != SSL_SUCCESS) {
            CYASSL_MSG("Enable CRL failed");
            return SSL_FATAL_ERROR;
        }
    }

    return LoadCRL(cm->crl, path, type, monitor);
}


int CyaSSL_EnableCRL(CYASSL* ssl, int options)
{
    CYASSL_ENTER("CyaSSL_EnableCRL");
    if (ssl)
        return CyaSSL_CertManagerEnableCRL(ssl->ctx->cm, options);
    else
        return BAD_FUNC_ARG;
}


int CyaSSL_DisableCRL(CYASSL* ssl)
{
    CYASSL_ENTER("CyaSSL_DisableCRL");
    if (ssl)
        return CyaSSL_CertManagerDisableCRL(ssl->ctx->cm);
    else
        return BAD_FUNC_ARG;
}


int CyaSSL_LoadCRL(CYASSL* ssl, const char* path, int type, int monitor)
{
    CYASSL_ENTER("CyaSSL_LoadCRL");
    if (ssl)
        return CyaSSL_CertManagerLoadCRL(ssl->ctx->cm, path, type, monitor);
    else
        return BAD_FUNC_ARG;
}


int CyaSSL_SetCRL_Cb(CYASSL* ssl, CbMissingCRL cb)
{
    CYASSL_ENTER("CyaSSL_SetCRL_Cb");
    if (ssl)
        return CyaSSL_CertManagerSetCRL_Cb(ssl->ctx->cm, cb);
    else
        return BAD_FUNC_ARG;
}


int CyaSSL_CTX_EnableCRL(CYASSL_CTX* ctx, int options)
{
    CYASSL_ENTER("CyaSSL_CTX_EnableCRL");
    if (ctx)
        return CyaSSL_CertManagerEnableCRL(ctx->cm, options);
    else
        return BAD_FUNC_ARG;
}


int CyaSSL_CTX_DisableCRL(CYASSL_CTX* ctx)
{
    CYASSL_ENTER("CyaSSL_CTX_DisableCRL");
    if (ctx)
        return CyaSSL_CertManagerDisableCRL(ctx->cm);
    else
        return BAD_FUNC_ARG;
}


int CyaSSL_CTX_LoadCRL(CYASSL_CTX* ctx, const char* path, int type, int monitor)
{
    CYASSL_ENTER("CyaSSL_CTX_LoadCRL");
    if (ctx)
        return CyaSSL_CertManagerLoadCRL(ctx->cm, path, type, monitor);
    else
        return BAD_FUNC_ARG;
}


int CyaSSL_CTX_SetCRL_Cb(CYASSL_CTX* ctx, CbMissingCRL cb)
{
    CYASSL_ENTER("CyaSSL_CTX_SetCRL_Cb");
    if (ctx)
        return CyaSSL_CertManagerSetCRL_Cb(ctx->cm, cb);
    else
        return BAD_FUNC_ARG;
}


#endif /* HAVE_CRL */


#ifdef CYASSL_DER_LOAD

/* Add format parameter to allow DER load of CA files */
int CyaSSL_CTX_der_load_verify_locations(CYASSL_CTX* ctx, const char* file,
                                         int format)
{
    CYASSL_ENTER("CyaSSL_CTX_der_load_verify_locations");
    if (ctx == NULL || file == NULL)
        return SSL_FAILURE;

    if (ProcessFile(ctx, file, format, CA_TYPE, NULL, 0, NULL) == SSL_SUCCESS)
        return SSL_SUCCESS;

    return SSL_FAILURE;
}

#endif /* CYASSL_DER_LOAD */


#ifdef CYASSL_CERT_GEN

/* load pem cert from file into der buffer, return der size or error */
int CyaSSL_PemCertToDer(const char* fileName, unsigned char* derBuf, int derSz)
{
    byte   staticBuffer[FILE_BUFFER_SIZE];
    byte*  fileBuf = staticBuffer;
    int    dynamic = 0;
    int    ret;
    int    ecc = 0;
    long   sz = 0;
    XFILE  file = XFOPEN(fileName, "rb");
    EncryptedInfo info;
    buffer        converted;

    CYASSL_ENTER("CyaSSL_PemCertToDer");
    converted.buffer = 0;

    if (file == XBADFILE) return SSL_BAD_FILE;
    XFSEEK(file, 0, XSEEK_END);
    sz = XFTELL(file);
    XREWIND(file);

    if (sz > (long)sizeof(staticBuffer)) {
        fileBuf = (byte*) XMALLOC(sz, 0, DYNAMIC_TYPE_FILE);
        if (fileBuf == NULL) {
            XFCLOSE(file);
            return SSL_BAD_FILE;
        }
        dynamic = 1;
    }
    else if (sz < 0) {
        XFCLOSE(file);
        return SSL_BAD_FILE;
    }

    if ( (ret = (int)XFREAD(fileBuf, sz, 1, file)) < 0)
        ret = SSL_BAD_FILE;
    else
        ret = PemToDer(fileBuf, sz, CA_TYPE, &converted, 0, &info, &ecc);

    if (ret == 0) {
        if (converted.length < (word32)derSz) {
            XMEMCPY(derBuf, converted.buffer, converted.length);
            ret = converted.length;
        }
        else
            ret = BUFFER_E;
    }

    XFREE(converted.buffer, 0, DYNAMIC_TYPE_CA);
    if (dynamic)
        XFREE(fileBuf, 0, DYNAMIC_TYPE_FILE);
    XFCLOSE(file);

    return ret;
}

#endif /* CYASSL_CERT_GEN */


int CyaSSL_CTX_use_certificate_file(CYASSL_CTX* ctx, const char* file,
                                    int format)
{
    CYASSL_ENTER("CyaSSL_CTX_use_certificate_file");
    if (ProcessFile(ctx, file, format, CERT_TYPE, NULL, 0, NULL) == SSL_SUCCESS)
        return SSL_SUCCESS;

    return SSL_FAILURE;
}


int CyaSSL_CTX_use_PrivateKey_file(CYASSL_CTX* ctx, const char* file,int format)
{
    CYASSL_ENTER("CyaSSL_CTX_use_PrivateKey_file");
    if (ProcessFile(ctx, file, format, PRIVATEKEY_TYPE, NULL, 0, NULL)
                    == SSL_SUCCESS)
        return SSL_SUCCESS;

    return SSL_FAILURE;
}


int CyaSSL_CTX_use_certificate_chain_file(CYASSL_CTX* ctx, const char* file)
{
   /* procces up to MAX_CHAIN_DEPTH plus subject cert */
   CYASSL_ENTER("CyaSSL_CTX_use_certificate_chain_file");
   if (ProcessFile(ctx, file, SSL_FILETYPE_PEM,CERT_TYPE,NULL,1, NULL)
                   == SSL_SUCCESS)
       return SSL_SUCCESS;

   return SSL_FAILURE;
}


#ifndef NO_DH

/* server wrapper for ctx or ssl Diffie-Hellman parameters */
static int CyaSSL_SetTmpDH_buffer_wrapper(CYASSL_CTX* ctx, CYASSL* ssl,
                                  const unsigned char* buf, long sz, int format)
{
    buffer der;
    int    ret;
    int    weOwnDer = 0;
    byte   p[MAX_DH_SIZE];
    byte   g[MAX_DH_SIZE];
    word32 pSz = sizeof(p);
    word32 gSz = sizeof(g);

    der.buffer = (byte*)buf;
    der.length = (word32)sz;

    if (format != SSL_FILETYPE_ASN1 && format != SSL_FILETYPE_PEM)
        return SSL_BAD_FILETYPE;

    if (format == SSL_FILETYPE_PEM) {
        der.buffer = NULL;
        ret = PemToDer(buf, sz, DH_PARAM_TYPE, &der, ctx->heap, NULL,NULL);
        if (ret < 0) {
            XFREE(der.buffer, ctx->heap, DYNAMIC_TYPE_KEY);
            return ret;
        }
        weOwnDer = 1;
    }

    if (DhParamsLoad(der.buffer, der.length, p, &pSz, g, &gSz) < 0)
        ret = SSL_BAD_FILETYPE;
    else {
        if (ssl)
            ret = CyaSSL_SetTmpDH(ssl, p, pSz, g, gSz);
        else
            ret = CyaSSL_CTX_SetTmpDH(ctx, p, pSz, g, gSz);
    }

    if (weOwnDer)
        XFREE(der.buffer, ctx->heap, DYNAMIC_TYPE_KEY);

    return ret;
}


/* server Diffie-Hellman parameters, SSL_SUCCESS on ok */
int CyaSSL_SetTmpDH_buffer(CYASSL* ssl, const unsigned char* buf, long sz,
                           int format)
{
    return CyaSSL_SetTmpDH_buffer_wrapper(ssl->ctx, ssl, buf, sz, format);
}


/* server ctx Diffie-Hellman parameters, SSL_SUCCESS on ok */
int CyaSSL_CTX_SetTmpDH_buffer(CYASSL_CTX* ctx, const unsigned char* buf,
                               long sz, int format)
{
    return CyaSSL_SetTmpDH_buffer_wrapper(ctx, NULL, buf, sz, format);
}


/* server Diffie-Hellman parameters */
static int CyaSSL_SetTmpDH_file_wrapper(CYASSL_CTX* ctx, CYASSL* ssl,
                                        const char* fname, int format)
{
    byte   staticBuffer[FILE_BUFFER_SIZE];
    byte*  myBuffer = staticBuffer;
    int    dynamic = 0;
    int    ret;
    long   sz = 0;
    XFILE  file = XFOPEN(fname, "rb");

    if (file == XBADFILE) return SSL_BAD_FILE;
    XFSEEK(file, 0, XSEEK_END);
    sz = XFTELL(file);
    XREWIND(file);

    if (sz > (long)sizeof(staticBuffer)) {
        CYASSL_MSG("Getting dynamic buffer");
        myBuffer = (byte*) XMALLOC(sz, ctx->heap, DYNAMIC_TYPE_FILE);
        if (myBuffer == NULL) {
            XFCLOSE(file);
            return SSL_BAD_FILE;
        }
        dynamic = 1;
    }
    else if (sz < 0) {
        XFCLOSE(file);
        return SSL_BAD_FILE;
    }

    if ( (ret = (int)XFREAD(myBuffer, sz, 1, file)) < 0)
        ret = SSL_BAD_FILE;
    else {
        if (ssl)
            ret = CyaSSL_SetTmpDH_buffer(ssl, myBuffer, sz, format);
        else
            ret = CyaSSL_CTX_SetTmpDH_buffer(ctx, myBuffer, sz, format);
    }

    XFCLOSE(file);
    if (dynamic) XFREE(myBuffer, ctx->heap, DYNAMIC_TYPE_FILE);

    return ret;
}

/* server Diffie-Hellman parameters */
int CyaSSL_SetTmpDH_file(CYASSL* ssl, const char* fname, int format)
{
    return CyaSSL_SetTmpDH_file_wrapper(ssl->ctx, ssl, fname, format);
}


/* server Diffie-Hellman parameters */
int CyaSSL_CTX_SetTmpDH_file(CYASSL_CTX* ctx, const char* fname, int format)
{
    return CyaSSL_SetTmpDH_file_wrapper(ctx, NULL, fname, format);
}


    /* server ctx Diffie-Hellman parameters, SSL_SUCCESS on ok */
    int CyaSSL_CTX_SetTmpDH(CYASSL_CTX* ctx, const unsigned char* p, int pSz,
                            const unsigned char* g, int gSz)
    {
        CYASSL_ENTER("CyaSSL_CTX_SetTmpDH");
        if (ctx == NULL || p == NULL || g == NULL) return BAD_FUNC_ARG;

        XFREE(ctx->serverDH_P.buffer, ctx->heap, DYNAMIC_TYPE_DH);
        XFREE(ctx->serverDH_G.buffer, ctx->heap, DYNAMIC_TYPE_DH);

        ctx->serverDH_P.buffer = (byte*)XMALLOC(pSz, ctx->heap,DYNAMIC_TYPE_DH);
        if (ctx->serverDH_P.buffer == NULL)
            return MEMORY_E;

        ctx->serverDH_G.buffer = (byte*)XMALLOC(gSz, ctx->heap,DYNAMIC_TYPE_DH);
        if (ctx->serverDH_G.buffer == NULL) {
            XFREE(ctx->serverDH_P.buffer, ctx->heap, DYNAMIC_TYPE_DH);
            return MEMORY_E;
        }

        ctx->serverDH_P.length = pSz;
        ctx->serverDH_G.length = gSz;

        XMEMCPY(ctx->serverDH_P.buffer, p, pSz);
        XMEMCPY(ctx->serverDH_G.buffer, g, gSz);

        ctx->haveDH = 1;

        CYASSL_LEAVE("CyaSSL_CTX_SetTmpDH", 0);
        return SSL_SUCCESS;
    }
#endif /* NO_DH */


#ifdef OPENSSL_EXTRA
/* put SSL type in extra for now, not very common */

int CyaSSL_use_certificate_file(CYASSL* ssl, const char* file, int format)
{
    CYASSL_ENTER("CyaSSL_use_certificate_file");
    if (ProcessFile(ssl->ctx, file, format, CERT_TYPE, ssl, 0, NULL)
                    == SSL_SUCCESS)
        return SSL_SUCCESS;

    return SSL_FAILURE;
}


int CyaSSL_use_PrivateKey_file(CYASSL* ssl, const char* file, int format)
{
    CYASSL_ENTER("CyaSSL_use_PrivateKey_file");
    if (ProcessFile(ssl->ctx, file, format, PRIVATEKEY_TYPE, ssl, 0, NULL)
                                                                 == SSL_SUCCESS)
        return SSL_SUCCESS;

    return SSL_FAILURE;
}


int CyaSSL_use_certificate_chain_file(CYASSL* ssl, const char* file)
{
   /* procces up to MAX_CHAIN_DEPTH plus subject cert */
   CYASSL_ENTER("CyaSSL_use_certificate_chain_file");
   if (ProcessFile(ssl->ctx, file, SSL_FILETYPE_PEM, CERT_TYPE, ssl, 1, NULL)
                                                                 == SSL_SUCCESS)
       return SSL_SUCCESS;

   return SSL_FAILURE;
}



#ifdef HAVE_ECC

/* Set Temp CTX EC-DHE size in octets, should be 20 - 66 for 160 - 521 bit */
int CyaSSL_CTX_SetTmpEC_DHE_Sz(CYASSL_CTX* ctx, word16 sz)
{
    if (ctx == NULL || sz < ECC_MINSIZE || sz > ECC_MAXSIZE)
        return BAD_FUNC_ARG;

    ctx->eccTempKeySz = sz;

    return SSL_SUCCESS;
}


/* Set Temp SSL EC-DHE size in octets, should be 20 - 66 for 160 - 521 bit */
int CyaSSL_SetTmpEC_DHE_Sz(CYASSL* ssl, word16 sz)
{
    if (ssl == NULL || sz < ECC_MINSIZE || sz > ECC_MAXSIZE)
        return BAD_FUNC_ARG;

    ssl->eccTempKeySz = sz;

    return SSL_SUCCESS;
}

#endif /* HAVE_ECC */




int CyaSSL_CTX_use_RSAPrivateKey_file(CYASSL_CTX* ctx,const char* file,
                                   int format)
{
    CYASSL_ENTER("SSL_CTX_use_RSAPrivateKey_file");

    return CyaSSL_CTX_use_PrivateKey_file(ctx, file, format);
}


int CyaSSL_use_RSAPrivateKey_file(CYASSL* ssl, const char* file, int format)
{
    CYASSL_ENTER("CyaSSL_use_RSAPrivateKey_file");

    return CyaSSL_use_PrivateKey_file(ssl, file, format);
}

#endif /* OPENSSL_EXTRA */

#ifdef HAVE_NTRU

int CyaSSL_CTX_use_NTRUPrivateKey_file(CYASSL_CTX* ctx, const char* file)
{
    CYASSL_ENTER("CyaSSL_CTX_use_NTRUPrivateKey_file");
    if (ctx == NULL)
        return SSL_FAILURE;

    if (ProcessFile(ctx, file, SSL_FILETYPE_RAW, PRIVATEKEY_TYPE, NULL, 0, NULL)
                         == SSL_SUCCESS) {
        ctx->haveNTRU = 1;
        return SSL_SUCCESS;
    }

    return SSL_FAILURE;
}

#endif /* HAVE_NTRU */


#endif /* NO_FILESYSTEM */


void CyaSSL_CTX_set_verify(CYASSL_CTX* ctx, int mode, VerifyCallback vc)
{
    CYASSL_ENTER("CyaSSL_CTX_set_verify");
    if (mode & SSL_VERIFY_PEER) {
        ctx->verifyPeer = 1;
        ctx->verifyNone = 0;  /* in case perviously set */
    }

    if (mode == SSL_VERIFY_NONE) {
        ctx->verifyNone = 1;
        ctx->verifyPeer = 0;  /* in case previously set */
    }

    if (mode & SSL_VERIFY_FAIL_IF_NO_PEER_CERT)
        ctx->failNoCert = 1;

    ctx->verifyCallback = vc;
}


void CyaSSL_set_verify(CYASSL* ssl, int mode, VerifyCallback vc)
{
    CYASSL_ENTER("CyaSSL_set_verify");
    if (mode & SSL_VERIFY_PEER) {
        ssl->options.verifyPeer = 1;
        ssl->options.verifyNone = 0;  /* in case perviously set */
    }

    if (mode == SSL_VERIFY_NONE) {
        ssl->options.verifyNone = 1;
        ssl->options.verifyPeer = 0;  /* in case previously set */
    }

    if (mode & SSL_VERIFY_FAIL_IF_NO_PEER_CERT)
        ssl->options.failNoCert = 1;

    ssl->verifyCallback = vc;
}


/* store user ctx for verify callback */
void CyaSSL_SetCertCbCtx(CYASSL* ssl, void* ctx)
{
    CYASSL_ENTER("CyaSSL_SetCertCbCtx");
    if (ssl)
        ssl->verifyCbCtx = ctx;
}


/* store context CA Cache addition callback */
void CyaSSL_CTX_SetCACb(CYASSL_CTX* ctx, CallbackCACache cb)
{
    if (ctx && ctx->cm)
        ctx->cm->caCacheCallback = cb;
}


#if defined(PERSIST_CERT_CACHE)

#if !defined(NO_FILESYSTEM)

/* Persist cert cache to file */
int CyaSSL_CTX_save_cert_cache(CYASSL_CTX* ctx, const char* fname)
{
    CYASSL_ENTER("CyaSSL_CTX_save_cert_cache");

    if (ctx == NULL || fname == NULL)
        return BAD_FUNC_ARG;

    return CM_SaveCertCache(ctx->cm, fname);
}


/* Persist cert cache from file */
int CyaSSL_CTX_restore_cert_cache(CYASSL_CTX* ctx, const char* fname)
{
    CYASSL_ENTER("CyaSSL_CTX_restore_cert_cache");

    if (ctx == NULL || fname == NULL)
        return BAD_FUNC_ARG;

    return CM_RestoreCertCache(ctx->cm, fname);
}

#endif /* NO_FILESYSTEM */

/* Persist cert cache to memory */
int CyaSSL_CTX_memsave_cert_cache(CYASSL_CTX* ctx, void* mem, int sz, int* used)
{
    CYASSL_ENTER("CyaSSL_CTX_memsave_cert_cache");

    if (ctx == NULL || mem == NULL || used == NULL || sz <= 0)
        return BAD_FUNC_ARG;

    return CM_MemSaveCertCache(ctx->cm, mem, sz, used);
}


/* Restore cert cache from memory */
int CyaSSL_CTX_memrestore_cert_cache(CYASSL_CTX* ctx, const void* mem, int sz)
{
    CYASSL_ENTER("CyaSSL_CTX_memrestore_cert_cache");

    if (ctx == NULL || mem == NULL || sz <= 0)
        return BAD_FUNC_ARG;

    return CM_MemRestoreCertCache(ctx->cm, mem, sz);
}


/* get how big the the cert cache save buffer needs to be */
int CyaSSL_CTX_get_cert_cache_memsize(CYASSL_CTX* ctx)
{
    CYASSL_ENTER("CyaSSL_CTX_get_cert_cache_memsize");

    if (ctx == NULL)
        return BAD_FUNC_ARG;

    return CM_GetCertCacheMemSize(ctx->cm);
}

#endif /* PERSISTE_CERT_CACHE */
#endif /* !NO_CERTS */


#ifndef NO_SESSION_CACHE

CYASSL_SESSION* CyaSSL_get_session(CYASSL* ssl)
{
    CYASSL_ENTER("SSL_get_session");
    if (ssl)
        return GetSession(ssl, 0);

    return NULL;
}


int CyaSSL_set_session(CYASSL* ssl, CYASSL_SESSION* session)
{
    CYASSL_ENTER("SSL_set_session");
    if (session)
        return SetSession(ssl, session);

    return SSL_FAILURE;
}


#ifndef NO_CLIENT_CACHE

/* Associate client session with serverID, find existing or store for saving
   if newSession flag on, don't reuse existing session
   SSL_SUCCESS on ok */
int CyaSSL_SetServerID(CYASSL* ssl, const byte* id, int len, int newSession)
{
    CYASSL_SESSION* session = NULL;

    CYASSL_ENTER("CyaSSL_SetServerID");

    if (ssl == NULL || id == NULL || len <= 0)
        return BAD_FUNC_ARG;

    if (newSession == 0) {
        session = GetSessionClient(ssl, id, len);
        if (session) {
            if (SetSession(ssl, session) != SSL_SUCCESS) {
                CYASSL_MSG("SetSession failed");
                session = NULL;
            }
        }
    }

    if (session == NULL) {
        CYASSL_MSG("Valid ServerID not cached already");

        ssl->session.idLen = (word16)min(SERVER_ID_LEN, (word32)len);
        XMEMCPY(ssl->session.serverID, id, ssl->session.idLen);
    }

    return SSL_SUCCESS;
}

#endif /* NO_CLIENT_CACHE */

#if defined(PERSIST_SESSION_CACHE)

/* for persistance, if changes to layout need to increment and modify
   save_session_cache() and restore_session_cache and memory versions too */
#define CYASSL_CACHE_VERSION 2

/* Session Cache Header information */
typedef struct {
    int version;     /* cache layout version id */
    int rows;        /* session rows */
    int columns;     /* session columns */
    int sessionSz;   /* sizeof CYASSL_SESSION */
} cache_header_t;

/* current persistence layout is:

   1) cache_header_t
   2) SessionCache
   3) ClientCache

   update CYASSL_CACHE_VERSION if change layout for the following
   PERSISTENT_SESSION_CACHE functions
*/


/* get how big the the session cache save buffer needs to be */
int CyaSSL_get_session_cache_memsize(void)
{
    int sz  = (int)(sizeof(SessionCache) + sizeof(cache_header_t));

    #ifndef NO_CLIENT_CACHE
        sz += (int)(sizeof(ClientCache));
    #endif

    return sz;
}


/* Persist session cache to memory */
int CyaSSL_memsave_session_cache(void* mem, int sz)
{
    int i;
    cache_header_t cache_header;
    SessionRow*    row  = (SessionRow*)((byte*)mem + sizeof(cache_header));
#ifndef NO_CLIENT_CACHE
    ClientRow*     clRow;
#endif

    CYASSL_ENTER("CyaSSL_memsave_session_cache");

    if (sz < CyaSSL_get_session_cache_memsize()) {
        CYASSL_MSG("Memory buffer too small");
        return BUFFER_E;
    }

    cache_header.version   = CYASSL_CACHE_VERSION;
    cache_header.rows      = SESSION_ROWS;
    cache_header.columns   = SESSIONS_PER_ROW;
    cache_header.sessionSz = (int)sizeof(CYASSL_SESSION);
    XMEMCPY(mem, &cache_header, sizeof(cache_header));

    if (LockMutex(&session_mutex) != 0) {
        CYASSL_MSG("Session cache mutex lock failed");
        return BAD_MUTEX_E;
    }

    for (i = 0; i < cache_header.rows; ++i)
        XMEMCPY(row++, SessionCache + i, sizeof(SessionRow));

#ifndef NO_CLIENT_CACHE
    clRow = (ClientRow*)row;
    for (i = 0; i < cache_header.rows; ++i)
        XMEMCPY(clRow++, ClientCache + i, sizeof(ClientRow));
#endif

    UnLockMutex(&session_mutex);

    CYASSL_LEAVE("CyaSSL_memsave_session_cache", SSL_SUCCESS);

    return SSL_SUCCESS;
}


/* Restore the persistant session cache from memory */
int CyaSSL_memrestore_session_cache(const void* mem, int sz)
{
    int    i;
    cache_header_t cache_header;
    SessionRow*    row  = (SessionRow*)((byte*)mem + sizeof(cache_header));
#ifndef NO_CLIENT_CACHE
    ClientRow*     clRow;
#endif

    CYASSL_ENTER("CyaSSL_memrestore_session_cache");

    if (sz < CyaSSL_get_session_cache_memsize()) {
        CYASSL_MSG("Memory buffer too small");
        return BUFFER_E;
    }

    XMEMCPY(&cache_header, mem, sizeof(cache_header));
    if (cache_header.version   != CYASSL_CACHE_VERSION ||
        cache_header.rows      != SESSION_ROWS ||
        cache_header.columns   != SESSIONS_PER_ROW ||
        cache_header.sessionSz != (int)sizeof(CYASSL_SESSION)) {

        CYASSL_MSG("Session cache header match failed");
        return CACHE_MATCH_ERROR;
    }

    if (LockMutex(&session_mutex) != 0) {
        CYASSL_MSG("Session cache mutex lock failed");
        return BAD_MUTEX_E;
    }

    for (i = 0; i < cache_header.rows; ++i)
        XMEMCPY(SessionCache + i, row++, sizeof(SessionRow));

#ifndef NO_CLIENT_CACHE
    clRow = (ClientRow*)row;
    for (i = 0; i < cache_header.rows; ++i)
        XMEMCPY(ClientCache + i, clRow++, sizeof(ClientRow));
#endif

    UnLockMutex(&session_mutex);

    CYASSL_LEAVE("CyaSSL_memrestore_session_cache", SSL_SUCCESS);

    return SSL_SUCCESS;
}

#if !defined(NO_FILESYSTEM)

/* Persist session cache to file */
/* doesn't use memsave because of additional memory use */
int CyaSSL_save_session_cache(const char *fname)
{
    XFILE  file;
    int    ret;
    int    rc = SSL_SUCCESS;
    int    i;
    cache_header_t cache_header;

    CYASSL_ENTER("CyaSSL_save_session_cache");

    file = XFOPEN(fname, "w+b");
    if (file == XBADFILE) {
        CYASSL_MSG("Couldn't open session cache save file");
        return SSL_BAD_FILE;
    }
    cache_header.version   = CYASSL_CACHE_VERSION;
    cache_header.rows      = SESSION_ROWS;
    cache_header.columns   = SESSIONS_PER_ROW;
    cache_header.sessionSz = (int)sizeof(CYASSL_SESSION);

    /* cache header */
    ret = (int)XFWRITE(&cache_header, sizeof cache_header, 1, file);
    if (ret != 1) {
        CYASSL_MSG("Session cache header file write failed");
        XFCLOSE(file);
        return FWRITE_ERROR;
    }

    if (LockMutex(&session_mutex) != 0) {
        CYASSL_MSG("Session cache mutex lock failed");
        XFCLOSE(file);
        return BAD_MUTEX_E;
    }

    /* session cache */
    for (i = 0; i < cache_header.rows; ++i) {
        ret = (int)XFWRITE(SessionCache + i, sizeof(SessionRow), 1, file);
        if (ret != 1) {
            CYASSL_MSG("Session cache member file write failed");
            rc = FWRITE_ERROR;
            break;
        }
    }

#ifndef NO_CLIENT_CACHE
    /* client cache */
    for (i = 0; i < cache_header.rows; ++i) {
        ret = (int)XFWRITE(ClientCache + i, sizeof(ClientRow), 1, file);
        if (ret != 1) {
            CYASSL_MSG("Client cache member file write failed");
            rc = FWRITE_ERROR;
            break;
        }
    }
#endif /* NO_CLIENT_CACHE */

    UnLockMutex(&session_mutex);

    XFCLOSE(file);
    CYASSL_LEAVE("CyaSSL_save_session_cache", rc);

    return rc;
}


/* Restore the persistant session cache from file */
/* doesn't use memstore because of additional memory use */
int CyaSSL_restore_session_cache(const char *fname)
{
    XFILE  file;
    int    rc = SSL_SUCCESS;
    int    ret;
    int    i;
    cache_header_t cache_header;

    CYASSL_ENTER("CyaSSL_restore_session_cache");

    file = XFOPEN(fname, "rb");
    if (file == XBADFILE) {
        CYASSL_MSG("Couldn't open session cache save file");
        return SSL_BAD_FILE;
    }
    /* cache header */
    ret = (int)XFREAD(&cache_header, sizeof cache_header, 1, file);
    if (ret != 1) {
        CYASSL_MSG("Session cache header file read failed");
        XFCLOSE(file);
        return FREAD_ERROR;
    }
    if (cache_header.version   != CYASSL_CACHE_VERSION ||
        cache_header.rows      != SESSION_ROWS ||
        cache_header.columns   != SESSIONS_PER_ROW ||
        cache_header.sessionSz != (int)sizeof(CYASSL_SESSION)) {

        CYASSL_MSG("Session cache header match failed");
        XFCLOSE(file);
        return CACHE_MATCH_ERROR;
    }

    if (LockMutex(&session_mutex) != 0) {
        CYASSL_MSG("Session cache mutex lock failed");
        XFCLOSE(file);
        return BAD_MUTEX_E;
    }

    /* session cache */
    for (i = 0; i < cache_header.rows; ++i) {
        ret = (int)XFREAD(SessionCache + i, sizeof(SessionRow), 1, file);
        if (ret != 1) {
            CYASSL_MSG("Session cache member file read failed");
            XMEMSET(SessionCache, 0, sizeof SessionCache);
            rc = FREAD_ERROR;
            break;
        }
    }

#ifndef NO_CLIENT_CACHE
    /* client cache */
    for (i = 0; i < cache_header.rows; ++i) {
        ret = (int)XFREAD(ClientCache + i, sizeof(ClientRow), 1, file);
        if (ret != 1) {
            CYASSL_MSG("Client cache member file read failed");
            XMEMSET(ClientCache, 0, sizeof ClientCache);
            rc = FREAD_ERROR;
            break;
        }
    }

#endif /* NO_CLIENT_CACHE */

    UnLockMutex(&session_mutex);

    XFCLOSE(file);
    CYASSL_LEAVE("CyaSSL_restore_session_cache", rc);

    return rc;
}

#endif /* !NO_FILESYSTEM */
#endif /* PERSIST_SESSION_CACHE */
#endif /* NO_SESSION_CACHE */


void CyaSSL_load_error_strings(void)   /* compatibility only */
{}


int CyaSSL_library_init(void)
{
    CYASSL_ENTER("SSL_library_init");
    if (CyaSSL_Init() == SSL_SUCCESS)
        return SSL_SUCCESS;
    else
        return SSL_FATAL_ERROR;
}


#ifndef NO_SESSION_CACHE

/* on by default if built in but allow user to turn off */
long CyaSSL_CTX_set_session_cache_mode(CYASSL_CTX* ctx, long mode)
{
    CYASSL_ENTER("SSL_CTX_set_session_cache_mode");
    if (mode == SSL_SESS_CACHE_OFF)
        ctx->sessionCacheOff = 1;

    if (mode == SSL_SESS_CACHE_NO_AUTO_CLEAR)
        ctx->sessionCacheFlushOff = 1;

    return SSL_SUCCESS;
}

#endif /* NO_SESSION_CACHE */


#if !defined(NO_CERTS)
#if defined(PERSIST_CERT_CACHE)


#define CYASSL_CACHE_CERT_VERSION 1

typedef struct {
    int version;                 /* cache cert layout version id */
    int rows;                    /* hash table rows, CA_TABLE_SIZE */
    int columns[CA_TABLE_SIZE];  /* columns per row on list */
    int signerSz;                /* sizeof Signer object */
} CertCacheHeader;

/* current cert persistance layout is:

   1) CertCacheHeader
   2) caTable

   update CYASSL_CERT_CACHE_VERSION if change layout for the following
   PERSIST_CERT_CACHE functions
*/


/* Return memory needed to persist this signer, have lock */
static INLINE int GetSignerMemory(Signer* signer)
{
    int sz = sizeof(signer->pubKeySize) + sizeof(signer->keyOID)
           + sizeof(signer->nameLen)    + sizeof(signer->subjectNameHash);

#if !defined(NO_SKID)
        sz += (int)sizeof(signer->subjectKeyIdHash);
#endif

    /* add dynamic bytes needed */
    sz += signer->pubKeySize;
    sz += signer->nameLen;

    return sz;
}


/* Return memory needed to persist this row, have lock */
static INLINE int GetCertCacheRowMemory(Signer* row)
{
    int sz = 0;

    while (row) {
        sz += GetSignerMemory(row);
        row = row->next;
    }

    return sz;
}


/* get the size of persist cert cache, have lock */
static INLINE int GetCertCacheMemSize(CYASSL_CERT_MANAGER* cm)
{
    int sz;
    int i;

    sz = sizeof(CertCacheHeader);

    for (i = 0; i < CA_TABLE_SIZE; i++)
        sz += GetCertCacheRowMemory(cm->caTable[i]);

    return sz;
}


/* Store cert cache header columns with number of items per list, have lock */
static INLINE void SetCertHeaderColumns(CYASSL_CERT_MANAGER* cm, int* columns)
{
    int     i;
    Signer* row;

    for (i = 0; i < CA_TABLE_SIZE; i++) {
        int count = 0;
        row = cm->caTable[i];

        while (row) {
            ++count;
            row = row->next;
        }
        columns[i] = count;
    }
}


/* Restore whole cert row from memory, have lock, return bytes consumed,
   < 0 on error, have lock */
static INLINE int RestoreCertRow(CYASSL_CERT_MANAGER* cm, byte* current,
                                 int row, int listSz, const byte* end)
{
    int idx = 0;

    if (listSz < 0) {
        CYASSL_MSG("Row header corrupted, negative value");
        return PARSE_ERROR;
    }

    while (listSz) {
        Signer* signer;
        byte*   start = current + idx;  /* for end checks on this signer */
        int     minSz = sizeof(signer->pubKeySize) + sizeof(signer->keyOID) +
                      sizeof(signer->nameLen) + sizeof(signer->subjectNameHash);
        #ifndef NO_SKID
                minSz += (int)sizeof(signer->subjectKeyIdHash);
        #endif

        if (start + minSz > end) {
            CYASSL_MSG("Would overread restore buffer");
            return BUFFER_E;
        }
        signer = MakeSigner(cm->heap);
        if (signer == NULL)
            return MEMORY_E;

        /* pubKeySize */
        XMEMCPY(&signer->pubKeySize, current + idx, sizeof(signer->pubKeySize));
        idx += (int)sizeof(signer->pubKeySize);

        /* keyOID */
        XMEMCPY(&signer->keyOID, current + idx, sizeof(signer->keyOID));
        idx += (int)sizeof(signer->keyOID);

        /* pulicKey */
        if (start + minSz + signer->pubKeySize > end) {
            CYASSL_MSG("Would overread restore buffer");
            FreeSigner(signer, cm->heap);
            return BUFFER_E;
        }
        signer->publicKey = (byte*)XMALLOC(signer->pubKeySize, cm->heap,
                                           DYNAMIC_TYPE_KEY);
        if (signer->publicKey == NULL) {
            FreeSigner(signer, cm->heap);
            return MEMORY_E;
        }

        XMEMCPY(signer->publicKey, current + idx, signer->pubKeySize);
        idx += signer->pubKeySize;

        /* nameLen */
        XMEMCPY(&signer->nameLen, current + idx, sizeof(signer->nameLen));
        idx += (int)sizeof(signer->nameLen);

        /* name */
        if (start + minSz + signer->pubKeySize + signer->nameLen > end) {
            CYASSL_MSG("Would overread restore buffer");
            FreeSigner(signer, cm->heap);
            return BUFFER_E;
        }
        signer->name = (char*)XMALLOC(signer->nameLen, cm->heap,
                                      DYNAMIC_TYPE_SUBJECT_CN);
        if (signer->name == NULL) {
            FreeSigner(signer, cm->heap);
            return MEMORY_E;
        }

        XMEMCPY(signer->name, current + idx, signer->nameLen);
        idx += signer->nameLen;

        /* subjectNameHash */
        XMEMCPY(signer->subjectNameHash, current + idx, SIGNER_DIGEST_SIZE);
        idx += SIGNER_DIGEST_SIZE;

        #ifndef NO_SKID
            /* subjectKeyIdHash */
            XMEMCPY(signer->subjectKeyIdHash, current + idx,SIGNER_DIGEST_SIZE);
            idx += SIGNER_DIGEST_SIZE;
        #endif

        signer->next = cm->caTable[row];
        cm->caTable[row] = signer;

        --listSz;
    }

    return idx;
}


/* Store whole cert row into memory, have lock, return bytes added */
static INLINE int StoreCertRow(CYASSL_CERT_MANAGER* cm, byte* current, int row)
{
    int     added  = 0;
    Signer* list   = cm->caTable[row];

    while (list) {
        XMEMCPY(current + added, &list->pubKeySize, sizeof(list->pubKeySize));
        added += (int)sizeof(list->pubKeySize);

        XMEMCPY(current + added, &list->keyOID,     sizeof(list->keyOID));
        added += (int)sizeof(list->keyOID);

        XMEMCPY(current + added, list->publicKey, list->pubKeySize);
        added += list->pubKeySize;

        XMEMCPY(current + added, &list->nameLen, sizeof(list->nameLen));
        added += (int)sizeof(list->nameLen);

        XMEMCPY(current + added, list->name, list->nameLen);
        added += list->nameLen;

        XMEMCPY(current + added, list->subjectNameHash, SIGNER_DIGEST_SIZE);
        added += SIGNER_DIGEST_SIZE;

        #ifndef NO_SKID
            XMEMCPY(current + added, list->subjectKeyIdHash,SIGNER_DIGEST_SIZE);
            added += SIGNER_DIGEST_SIZE;
        #endif

        list = list->next;
    }

    return added;
}


/* Persist cert cache to memory, have lock */
static INLINE int DoMemSaveCertCache(CYASSL_CERT_MANAGER* cm, void* mem, int sz)
{
    int realSz;
    int ret = SSL_SUCCESS;
    int i;

    CYASSL_ENTER("DoMemSaveCertCache");

    realSz = GetCertCacheMemSize(cm);
    if (realSz > sz) {
        CYASSL_MSG("Mem output buffer too small");
        ret = BUFFER_E;
    }
    else {
        byte*           current;
        CertCacheHeader hdr;

        hdr.version  = CYASSL_CACHE_CERT_VERSION;
        hdr.rows     = CA_TABLE_SIZE;
        SetCertHeaderColumns(cm, hdr.columns);
        hdr.signerSz = (int)sizeof(Signer);

        XMEMCPY(mem, &hdr, sizeof(CertCacheHeader));
        current = (byte*)mem + sizeof(CertCacheHeader);

        for (i = 0; i < CA_TABLE_SIZE; ++i)
            current += StoreCertRow(cm, current, i);
    }

    return ret;
}


#if !defined(NO_FILESYSTEM)

/* Persist cert cache to file */
int CM_SaveCertCache(CYASSL_CERT_MANAGER* cm, const char* fname)
{
    XFILE file;
    int   rc = SSL_SUCCESS;
    int   memSz;
    byte* mem;

    CYASSL_ENTER("CM_SaveCertCache");

    file = XFOPEN(fname, "w+b");
    if (file == XBADFILE) {
       CYASSL_MSG("Couldn't open cert cache save file");
       return SSL_BAD_FILE;
    }

    if (LockMutex(&cm->caLock) != 0) {
        CYASSL_MSG("LockMutex on caLock failed");
        XFCLOSE(file);
        return BAD_MUTEX_E;
    }

    memSz = GetCertCacheMemSize(cm);
    mem   = (byte*)XMALLOC(memSz, cm->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (mem == NULL) {
        CYASSL_MSG("Alloc for tmp buffer failed");
        rc = MEMORY_E;
    } else {
        rc = DoMemSaveCertCache(cm, mem, memSz);
        if (rc == SSL_SUCCESS) {
            int ret = (int)XFWRITE(mem, memSz, 1, file);
            if (ret != 1) {
                CYASSL_MSG("Cert cache file write failed");
                rc = FWRITE_ERROR;
            }
        }
        XFREE(mem, cm->heap, DYNAMIC_TYPE_TMP_BUFFER);
    }

    UnLockMutex(&cm->caLock);
    XFCLOSE(file);

    return rc;
}


/* Restore cert cache from file */
int CM_RestoreCertCache(CYASSL_CERT_MANAGER* cm, const char* fname)
{
    XFILE file;
    int   rc = SSL_SUCCESS;
    int   ret;
    int   memSz;
    byte* mem;

    CYASSL_ENTER("CM_RestoreCertCache");

    file = XFOPEN(fname, "rb");
    if (file == XBADFILE) {
       CYASSL_MSG("Couldn't open cert cache save file");
       return SSL_BAD_FILE;
    }

    XFSEEK(file, 0, XSEEK_END);
    memSz = (int)XFTELL(file);
    XREWIND(file);

    if (memSz <= 0) {
        CYASSL_MSG("Bad file size");
        XFCLOSE(file);
        return SSL_BAD_FILE;
    }

    mem = (byte*)XMALLOC(memSz, cm->heap, DYNAMIC_TYPE_TMP_BUFFER);
    if (mem == NULL) {
        CYASSL_MSG("Alloc for tmp buffer failed");
        XFCLOSE(file);
        return MEMORY_E;
    }

    ret = (int)XFREAD(mem, memSz, 1, file);
    if (ret != 1) {
        CYASSL_MSG("Cert file read error");
        rc = FREAD_ERROR;
    } else {
        rc = CM_MemRestoreCertCache(cm, mem, memSz);
        if (rc != SSL_SUCCESS) {
            CYASSL_MSG("Mem restore cert cache failed");
        }
    }

    XFREE(mem, cm->heap, DYNAMIC_TYPE_TMP_BUFFER);
    XFCLOSE(file);

    return rc;
}

#endif /* NO_FILESYSTEM */


/* Persist cert cache to memory */
int CM_MemSaveCertCache(CYASSL_CERT_MANAGER* cm, void* mem, int sz, int* used)
{
    int ret = SSL_SUCCESS;

    CYASSL_ENTER("CM_MemSaveCertCache");

    if (LockMutex(&cm->caLock) != 0) {
        CYASSL_MSG("LockMutex on caLock failed");
        return BAD_MUTEX_E;
    }

    ret = DoMemSaveCertCache(cm, mem, sz);
    if (ret == SSL_SUCCESS)
        *used  = GetCertCacheMemSize(cm);

    UnLockMutex(&cm->caLock);

    return ret;
}


/* Restore cert cache from memory */
int CM_MemRestoreCertCache(CYASSL_CERT_MANAGER* cm, const void* mem, int sz)
{
    int ret = SSL_SUCCESS;
    int i;
    CertCacheHeader* hdr = (CertCacheHeader*)mem;
    byte*            current = (byte*)mem + sizeof(CertCacheHeader);
    byte*            end     = (byte*)mem + sz;  /* don't go over */

    CYASSL_ENTER("CM_MemRestoreCertCache");

    if (current > end) {
        CYASSL_MSG("Cert Cache Memory buffer too small");
        return BUFFER_E;
    }

    if (hdr->version  != CYASSL_CACHE_CERT_VERSION ||
        hdr->rows     != CA_TABLE_SIZE ||
        hdr->signerSz != (int)sizeof(Signer)) {

        CYASSL_MSG("Cert Cache Memory header mismatch");
        return CACHE_MATCH_ERROR;
    }

    if (LockMutex(&cm->caLock) != 0) {
        CYASSL_MSG("LockMutex on caLock failed");
        return BAD_MUTEX_E;
    }

    FreeSignerTable(cm->caTable, CA_TABLE_SIZE, cm->heap);

    for (i = 0; i < CA_TABLE_SIZE; ++i) {
        int added = RestoreCertRow(cm, current, i, hdr->columns[i], end);
        if (added < 0) {
            CYASSL_MSG("RestoreCertRow error");
            ret = added;
            break;
        }
        current += added;
    }

    UnLockMutex(&cm->caLock);

    return ret;
}


/* get how big the the cert cache save buffer needs to be */
int CM_GetCertCacheMemSize(CYASSL_CERT_MANAGER* cm)
{
    int sz;

    CYASSL_ENTER("CM_GetCertCacheMemSize");

    if (LockMutex(&cm->caLock) != 0) {
        CYASSL_MSG("LockMutex on caLock failed");
        return BAD_MUTEX_E;
    }

    sz = GetCertCacheMemSize(cm);

    UnLockMutex(&cm->caLock);

    return sz;
}

#endif /* PERSIST_CERT_CACHE */
#endif /* NO_CERTS */


int CyaSSL_CTX_set_cipher_list(CYASSL_CTX* ctx, const char* list)
{
    CYASSL_ENTER("CyaSSL_CTX_set_cipher_list");
    if (SetCipherList(&ctx->suites, list))
        return SSL_SUCCESS;
    else
        return SSL_FAILURE;
}


int CyaSSL_set_cipher_list(CYASSL* ssl, const char* list)
{
    CYASSL_ENTER("CyaSSL_set_cipher_list");
    if (SetCipherList(ssl->suites, list)) {
        byte haveRSA = 1;
        byte havePSK = 0;

        #ifdef NO_RSA
            haveRSA = 0;
        #endif
        #ifndef NO_PSK
            havePSK = ssl->options.havePSK;
        #endif

        InitSuites(ssl->suites, ssl->version, haveRSA, havePSK,
                   ssl->options.haveDH, ssl->options.haveNTRU,
                   ssl->options.haveECDSAsig, ssl->options.haveStaticECC,
                   ssl->options.side);

        return SSL_SUCCESS;
    }
    else
        return SSL_FAILURE;
}


#ifndef CYASSL_LEANPSK
#ifdef CYASSL_DTLS

int CyaSSL_dtls_get_current_timeout(CYASSL* ssl)
{
    (void)ssl;

    return ssl->dtls_timeout;
}


/* user may need to alter init dtls recv timeout, SSL_SUCCESS on ok */
int CyaSSL_dtls_set_timeout_init(CYASSL* ssl, int timeout)
{
    if (ssl == NULL || timeout < 0)
        return BAD_FUNC_ARG;

    if (timeout > ssl->dtls_timeout_max) {
        CYASSL_MSG("Can't set dtls timeout init greater than dtls timeout max");
        return BAD_FUNC_ARG;
    }

    ssl->dtls_timeout_init = timeout;
    ssl->dtls_timeout = timeout;

    return SSL_SUCCESS;
}


/* user may need to alter max dtls recv timeout, SSL_SUCCESS on ok */
int CyaSSL_dtls_set_timeout_max(CYASSL* ssl, int timeout)
{
    if (ssl == NULL || timeout < 0)
        return BAD_FUNC_ARG;

    if (timeout < ssl->dtls_timeout_init) {
        CYASSL_MSG("Can't set dtls timeout max less than dtls timeout init");
        return BAD_FUNC_ARG;
    }

    ssl->dtls_timeout_max = timeout;

    return SSL_SUCCESS;
}


int CyaSSL_dtls_got_timeout(CYASSL* ssl)
{
    int result = SSL_SUCCESS;

    DtlsMsgListDelete(ssl->dtls_msg_list, ssl->heap);
    ssl->dtls_msg_list = NULL;
    if (DtlsPoolTimeout(ssl) < 0 || DtlsPoolSend(ssl) < 0) {
        result = SSL_FATAL_ERROR;
    }
    return result;
}

#endif /* DTLS */
#endif /* LEANPSK */


/* client only parts */
#ifndef NO_CYASSL_CLIENT

    #ifndef NO_OLD_TLS
    CYASSL_METHOD* CyaSSLv3_client_method(void)
    {
        CYASSL_METHOD* method =
                              (CYASSL_METHOD*) XMALLOC(sizeof(CYASSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
        CYASSL_ENTER("SSLv3_client_method");
        if (method)
            InitSSL_Method(method, MakeSSLv3());
        return method;
    }
    #endif

    #ifdef CYASSL_DTLS
        CYASSL_METHOD* CyaDTLSv1_client_method(void)
        {
            CYASSL_METHOD* method =
                              (CYASSL_METHOD*) XMALLOC(sizeof(CYASSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
            CYASSL_ENTER("DTLSv1_client_method");
            if (method)
                InitSSL_Method(method, MakeDTLSv1());
            return method;
        }

        CYASSL_METHOD* CyaDTLSv1_2_client_method(void)
        {
            CYASSL_METHOD* method =
                              (CYASSL_METHOD*) XMALLOC(sizeof(CYASSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
            CYASSL_ENTER("DTLSv1_2_client_method");
            if (method)
                InitSSL_Method(method, MakeDTLSv1_2());
            return method;
        }
    #endif


    /* please see note at top of README if you get an error from connect */
    int CyaSSL_connect(CYASSL* ssl)
    {
        int neededState;

        CYASSL_ENTER("SSL_connect()");

        #ifdef HAVE_ERRNO_H
            errno = 0;
        #endif

        if (ssl->options.side != CYASSL_CLIENT_END) {
            CYASSL_ERROR(ssl->error = SIDE_ERROR);
            return SSL_FATAL_ERROR;
        }

        #ifdef CYASSL_DTLS
            if (ssl->version.major == DTLS_MAJOR) {
                ssl->options.dtls   = 1;
                ssl->options.tls    = 1;
                ssl->options.tls1_1 = 1;

                if (DtlsPoolInit(ssl) != 0) {
                    ssl->error = MEMORY_ERROR;
                    CYASSL_ERROR(ssl->error);
                    return SSL_FATAL_ERROR;
                }
            }
        #endif

        if (ssl->buffers.outputBuffer.length > 0) {
            if ( (ssl->error = SendBuffered(ssl)) == 0) {
                ssl->options.connectState++;
                CYASSL_MSG("connect state: Advanced from buffered send");
            }
            else {
                CYASSL_ERROR(ssl->error);
                return SSL_FATAL_ERROR;
            }
        }

        switch (ssl->options.connectState) {

        case CONNECT_BEGIN :
            /* always send client hello first */
            if ( (ssl->error = SendClientHello(ssl)) != 0) {
                CYASSL_ERROR(ssl->error);
                return SSL_FATAL_ERROR;
            }
            ssl->options.connectState = CLIENT_HELLO_SENT;
            CYASSL_MSG("connect state: CLIENT_HELLO_SENT");

        case CLIENT_HELLO_SENT :
            neededState = ssl->options.resuming ? SERVER_FINISHED_COMPLETE :
                                          SERVER_HELLODONE_COMPLETE;
            #ifdef CYASSL_DTLS
                /* In DTLS, when resuming, we can go straight to FINISHED,
                 * or do a cookie exchange and then skip to FINISHED, assume
                 * we need the cookie exchange first. */
                if (ssl->options.dtls)
                    neededState = SERVER_HELLOVERIFYREQUEST_COMPLETE;
            #endif
            /* get response */
            while (ssl->options.serverState < neededState) {
                if ( (ssl->error = ProcessReply(ssl)) < 0) {
                    CYASSL_ERROR(ssl->error);
                    return SSL_FATAL_ERROR;
                }
                /* if resumption failed, reset needed state */
                else if (neededState == SERVER_FINISHED_COMPLETE)
                    if (!ssl->options.resuming) {
                        if (!ssl->options.dtls)
                            neededState = SERVER_HELLODONE_COMPLETE;
                        else
                            neededState = SERVER_HELLOVERIFYREQUEST_COMPLETE;
                    }
            }

            ssl->options.connectState = HELLO_AGAIN;
            CYASSL_MSG("connect state: HELLO_AGAIN");

        case HELLO_AGAIN :
            if (ssl->options.certOnly)
                return SSL_SUCCESS;

            #ifdef CYASSL_DTLS
                if (ssl->options.dtls) {
                    /* re-init hashes, exclude first hello and verify request */
#ifndef NO_OLD_TLS
                    InitMd5(&ssl->hashMd5);
                    if ( (ssl->error = InitSha(&ssl->hashSha)) != 0) {
                        CYASSL_ERROR(ssl->error);
                        return SSL_FATAL_ERROR;
                    }
#endif
                    if (IsAtLeastTLSv1_2(ssl)) {
                        #ifndef NO_SHA256
                            if ( (ssl->error =
                                           InitSha256(&ssl->hashSha256)) != 0) {
                                CYASSL_ERROR(ssl->error);
                                return SSL_FATAL_ERROR;
                            }
                        #endif
                        #ifdef CYASSL_SHA384
                            if ( (ssl->error =
                                           InitSha384(&ssl->hashSha384)) != 0) {
                                CYASSL_ERROR(ssl->error);
                                return SSL_FATAL_ERROR;
                            }
                        #endif
                    }
                    if ( (ssl->error = SendClientHello(ssl)) != 0) {
                        CYASSL_ERROR(ssl->error);
                        return SSL_FATAL_ERROR;
                    }
                }
            #endif

            ssl->options.connectState = HELLO_AGAIN_REPLY;
            CYASSL_MSG("connect state: HELLO_AGAIN_REPLY");

        case HELLO_AGAIN_REPLY :
            #ifdef CYASSL_DTLS
                if (ssl->options.dtls) {
                    neededState = ssl->options.resuming ?
                           SERVER_FINISHED_COMPLETE : SERVER_HELLODONE_COMPLETE;

                    /* get response */
                    while (ssl->options.serverState < neededState) {
                        if ( (ssl->error = ProcessReply(ssl)) < 0) {
                                CYASSL_ERROR(ssl->error);
                                return SSL_FATAL_ERROR;
                        }
                        /* if resumption failed, reset needed state */
                        else if (neededState == SERVER_FINISHED_COMPLETE)
                            if (!ssl->options.resuming)
                                neededState = SERVER_HELLODONE_COMPLETE;
                    }
                }
            #endif

            ssl->options.connectState = FIRST_REPLY_DONE;
            CYASSL_MSG("connect state: FIRST_REPLY_DONE");

        case FIRST_REPLY_DONE :
            #ifndef NO_CERTS
                if (ssl->options.sendVerify) {
                    if ( (ssl->error = SendCertificate(ssl)) != 0) {
                        CYASSL_ERROR(ssl->error);
                        return SSL_FATAL_ERROR;
                    }
                    CYASSL_MSG("sent: certificate");
                }

            #endif
            ssl->options.connectState = FIRST_REPLY_FIRST;
            CYASSL_MSG("connect state: FIRST_REPLY_FIRST");

        case FIRST_REPLY_FIRST :
            if (!ssl->options.resuming) {
                if ( (ssl->error = SendClientKeyExchange(ssl)) != 0) {
                    CYASSL_ERROR(ssl->error);
                    return SSL_FATAL_ERROR;
                }
                CYASSL_MSG("sent: client key exchange");
            }

            ssl->options.connectState = FIRST_REPLY_SECOND;
            CYASSL_MSG("connect state: FIRST_REPLY_SECOND");

        case FIRST_REPLY_SECOND :
            #ifndef NO_CERTS
                if (ssl->options.sendVerify) {
                    if ( (ssl->error = SendCertificateVerify(ssl)) != 0) {
                        CYASSL_ERROR(ssl->error);
                        return SSL_FATAL_ERROR;
                    }
                    CYASSL_MSG("sent: certificate verify");
                }
            #endif
            ssl->options.connectState = FIRST_REPLY_THIRD;
            CYASSL_MSG("connect state: FIRST_REPLY_THIRD");

        case FIRST_REPLY_THIRD :
            if ( (ssl->error = SendChangeCipher(ssl)) != 0) {
                CYASSL_ERROR(ssl->error);
                return SSL_FATAL_ERROR;
            }
            CYASSL_MSG("sent: change cipher spec");
            ssl->options.connectState = FIRST_REPLY_FOURTH;
            CYASSL_MSG("connect state: FIRST_REPLY_FOURTH");

        case FIRST_REPLY_FOURTH :
            if ( (ssl->error = SendFinished(ssl)) != 0) {
                CYASSL_ERROR(ssl->error);
                return SSL_FATAL_ERROR;
            }
            CYASSL_MSG("sent: finished");
            ssl->options.connectState = FINISHED_DONE;
            CYASSL_MSG("connect state: FINISHED_DONE");

        case FINISHED_DONE :
            /* get response */
            while (ssl->options.serverState < SERVER_FINISHED_COMPLETE)
                if ( (ssl->error = ProcessReply(ssl)) < 0) {
                    CYASSL_ERROR(ssl->error);
                    return SSL_FATAL_ERROR;
                }

            ssl->options.connectState = SECOND_REPLY_DONE;
            CYASSL_MSG("connect state: SECOND_REPLY_DONE");

        case SECOND_REPLY_DONE:
            FreeHandshakeResources(ssl);
            CYASSL_LEAVE("SSL_connect()", SSL_SUCCESS);
            return SSL_SUCCESS;

        default:
            CYASSL_MSG("Unknown connect state ERROR");
            return SSL_FATAL_ERROR; /* unknown connect state */
        }
    }

#endif /* NO_CYASSL_CLIENT */


/* server only parts */
#ifndef NO_CYASSL_SERVER

    #ifndef NO_OLD_TLS
    CYASSL_METHOD* CyaSSLv3_server_method(void)
    {
        CYASSL_METHOD* method =
                              (CYASSL_METHOD*) XMALLOC(sizeof(CYASSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
        CYASSL_ENTER("SSLv3_server_method");
        if (method) {
            InitSSL_Method(method, MakeSSLv3());
            method->side = CYASSL_SERVER_END;
        }
        return method;
    }
    #endif


    #ifdef CYASSL_DTLS
        CYASSL_METHOD* CyaDTLSv1_server_method(void)
        {
            CYASSL_METHOD* method =
                              (CYASSL_METHOD*) XMALLOC(sizeof(CYASSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
            CYASSL_ENTER("DTLSv1_server_method");
            if (method) {
                InitSSL_Method(method, MakeDTLSv1());
                method->side = CYASSL_SERVER_END;
            }
            return method;
        }

        CYASSL_METHOD* CyaDTLSv1_2_server_method(void)
        {
            CYASSL_METHOD* method =
                              (CYASSL_METHOD*) XMALLOC(sizeof(CYASSL_METHOD), 0,
                                                       DYNAMIC_TYPE_METHOD);
            CYASSL_ENTER("DTLSv1_2_server_method");
            if (method) {
                InitSSL_Method(method, MakeDTLSv1_2());
                method->side = CYASSL_SERVER_END;
            }
            return method;
        }
    #endif


    int CyaSSL_accept(CYASSL* ssl)
    {
        byte havePSK = 0;
        CYASSL_ENTER("SSL_accept()");

        #ifdef HAVE_ERRNO_H
            errno = 0;
        #endif

        #ifndef NO_PSK
            havePSK = ssl->options.havePSK;
        #endif
        (void)havePSK;

        if (ssl->options.side != CYASSL_SERVER_END) {
            CYASSL_ERROR(ssl->error = SIDE_ERROR);
            return SSL_FATAL_ERROR;
        }

        #ifndef NO_CERTS
            /* in case used set_accept_state after init */
            if (!havePSK && (ssl->buffers.certificate.buffer == NULL ||
                             ssl->buffers.key.buffer == NULL)) {
                CYASSL_MSG("accept error: don't have server cert and key");
                ssl->error = NO_PRIVATE_KEY;
                CYASSL_ERROR(ssl->error);
                return SSL_FATAL_ERROR;
            }
        #endif

        #ifdef HAVE_ECC
            /* in case used set_accept_state after init */
            if (ssl->eccTempKeyPresent == 0) {
                if (ecc_make_key(ssl->rng, ssl->eccTempKeySz,
                                 ssl->eccTempKey) != 0) {
                    ssl->error = ECC_MAKEKEY_ERROR;
                    CYASSL_ERROR(ssl->error);
                    return SSL_FATAL_ERROR;
                }
                ssl->eccTempKeyPresent = 1;
            }
        #endif

        #ifdef CYASSL_DTLS
            if (ssl->version.major == DTLS_MAJOR) {
                ssl->options.dtls   = 1;
                ssl->options.tls    = 1;
                ssl->options.tls1_1 = 1;

                if (DtlsPoolInit(ssl) != 0) {
                    ssl->error = MEMORY_ERROR;
                    CYASSL_ERROR(ssl->error);
                    return SSL_FATAL_ERROR;
                }
            }
        #endif

        if (ssl->buffers.outputBuffer.length > 0) {
            if ( (ssl->error = SendBuffered(ssl)) == 0) {
                ssl->options.acceptState++;
                CYASSL_MSG("accept state: Advanced from buffered send");
            }
            else {
                CYASSL_ERROR(ssl->error);
                return SSL_FATAL_ERROR;
            }
        }

        switch (ssl->options.acceptState) {

        case ACCEPT_BEGIN :
            /* get response */
            while (ssl->options.clientState < CLIENT_HELLO_COMPLETE)
                if ( (ssl->error = ProcessReply(ssl)) < 0) {
                    CYASSL_ERROR(ssl->error);
                    return SSL_FATAL_ERROR;
                }
            ssl->options.acceptState = ACCEPT_CLIENT_HELLO_DONE;
            CYASSL_MSG("accept state ACCEPT_CLIENT_HELLO_DONE");

        case ACCEPT_CLIENT_HELLO_DONE :
            #ifdef CYASSL_DTLS
                if (ssl->options.dtls)
                    if ( (ssl->error = SendHelloVerifyRequest(ssl)) != 0) {
                        CYASSL_ERROR(ssl->error);
                        return SSL_FATAL_ERROR;
                    }
            #endif
            ssl->options.acceptState = HELLO_VERIFY_SENT;
            CYASSL_MSG("accept state HELLO_VERIFY_SENT");

        case HELLO_VERIFY_SENT:
            #ifdef CYASSL_DTLS
                if (ssl->options.dtls) {
                    ssl->options.clientState = NULL_STATE;  /* get again */
                    /* re-init hashes, exclude first hello and verify request */
#ifndef NO_OLD_TLS
                    InitMd5(&ssl->hashMd5);
                    if ( (ssl->error = InitSha(&ssl->hashSha)) != 0) {
                        CYASSL_ERROR(ssl->error);
                        return SSL_FATAL_ERROR;
                    }
#endif
                    if (IsAtLeastTLSv1_2(ssl)) {
                        #ifndef NO_SHA256
                            if ( (ssl->error =
                                           InitSha256(&ssl->hashSha256)) != 0) {
                               CYASSL_ERROR(ssl->error);
                               return SSL_FATAL_ERROR;
                            }
                        #endif
                        #ifdef CYASSL_SHA384
                            if ( (ssl->error =
                                           InitSha384(&ssl->hashSha384)) != 0) {
                               CYASSL_ERROR(ssl->error);
                               return SSL_FATAL_ERROR;
                            }
                        #endif
                    }

                    while (ssl->options.clientState < CLIENT_HELLO_COMPLETE)
                        if ( (ssl->error = ProcessReply(ssl)) < 0) {
                            CYASSL_ERROR(ssl->error);
                            return SSL_FATAL_ERROR;
                        }
                }
            #endif
            ssl->options.acceptState = ACCEPT_FIRST_REPLY_DONE;
            CYASSL_MSG("accept state ACCEPT_FIRST_REPLY_DONE");

        case ACCEPT_FIRST_REPLY_DONE :
            if ( (ssl->error = SendServerHello(ssl)) != 0) {
                CYASSL_ERROR(ssl->error);
                return SSL_FATAL_ERROR;
            }
            ssl->options.acceptState = SERVER_HELLO_SENT;
            CYASSL_MSG("accept state SERVER_HELLO_SENT");

        case SERVER_HELLO_SENT :
            #ifndef NO_CERTS
                if (!ssl->options.resuming)
                    if ( (ssl->error = SendCertificate(ssl)) != 0) {
                        CYASSL_ERROR(ssl->error);
                        return SSL_FATAL_ERROR;
                    }
            #endif
            ssl->options.acceptState = CERT_SENT;
            CYASSL_MSG("accept state CERT_SENT");

        case CERT_SENT :
            if (!ssl->options.resuming)
                if ( (ssl->error = SendServerKeyExchange(ssl)) != 0) {
                    CYASSL_ERROR(ssl->error);
                    return SSL_FATAL_ERROR;
                }
            ssl->options.acceptState = KEY_EXCHANGE_SENT;
            CYASSL_MSG("accept state KEY_EXCHANGE_SENT");

        case KEY_EXCHANGE_SENT :
            #ifndef NO_CERTS
                if (!ssl->options.resuming)
                    if (ssl->options.verifyPeer)
                        if ( (ssl->error = SendCertificateRequest(ssl)) != 0) {
                            CYASSL_ERROR(ssl->error);
                            return SSL_FATAL_ERROR;
                        }
            #endif
            ssl->options.acceptState = CERT_REQ_SENT;
            CYASSL_MSG("accept state CERT_REQ_SENT");

        case CERT_REQ_SENT :
            if (!ssl->options.resuming)
                if ( (ssl->error = SendServerHelloDone(ssl)) != 0) {
                    CYASSL_ERROR(ssl->error);
                    return SSL_FATAL_ERROR;
                }
            ssl->options.acceptState = SERVER_HELLO_DONE;
            CYASSL_MSG("accept state SERVER_HELLO_DONE");

        case SERVER_HELLO_DONE :
            if (!ssl->options.resuming) {
                while (ssl->options.clientState < CLIENT_FINISHED_COMPLETE)
                    if ( (ssl->error = ProcessReply(ssl)) < 0) {
                        CYASSL_ERROR(ssl->error);
                        return SSL_FATAL_ERROR;
                    }
            }
            ssl->options.acceptState = ACCEPT_SECOND_REPLY_DONE;
            CYASSL_MSG("accept state  ACCEPT_SECOND_REPLY_DONE");

        case ACCEPT_SECOND_REPLY_DONE :
            if ( (ssl->error = SendChangeCipher(ssl)) != 0) {
                CYASSL_ERROR(ssl->error);
                return SSL_FATAL_ERROR;
            }
            ssl->options.acceptState = CHANGE_CIPHER_SENT;
            CYASSL_MSG("accept state  CHANGE_CIPHER_SENT");

        case CHANGE_CIPHER_SENT :
            if ( (ssl->error = SendFinished(ssl)) != 0) {
                CYASSL_ERROR(ssl->error);
                return SSL_FATAL_ERROR;
            }

            ssl->options.acceptState = ACCEPT_FINISHED_DONE;
            CYASSL_MSG("accept state ACCEPT_FINISHED_DONE");

        case ACCEPT_FINISHED_DONE :
            if (ssl->options.resuming)
                while (ssl->options.clientState < CLIENT_FINISHED_COMPLETE)
                    if ( (ssl->error = ProcessReply(ssl)) < 0) {
                        CYASSL_ERROR(ssl->error);
                        return SSL_FATAL_ERROR;
                    }

            ssl->options.acceptState = ACCEPT_THIRD_REPLY_DONE;
            CYASSL_MSG("accept state ACCEPT_THIRD_REPLY_DONE");

        case ACCEPT_THIRD_REPLY_DONE :
            FreeHandshakeResources(ssl);
            CYASSL_LEAVE("SSL_accept()", SSL_SUCCESS);
            return SSL_SUCCESS;

        default :
            CYASSL_MSG("Unknown accept state ERROR");
            return SSL_FATAL_ERROR;
        }
    }

#endif /* NO_CYASSL_SERVER */


int CyaSSL_Cleanup(void)
{
    int ret = SSL_SUCCESS;
    int release = 0;

    CYASSL_ENTER("CyaSSL_Cleanup");

    if (initRefCount == 0)
        return ret;  /* possibly no init yet, but not failure either way */

    if (LockMutex(&count_mutex) != 0) {
        CYASSL_MSG("Bad Lock Mutex count");
        return BAD_MUTEX_E;
    }

    release = initRefCount-- == 1;
    if (initRefCount < 0)
        initRefCount = 0;

    UnLockMutex(&count_mutex);

    if (!release)
        return ret;

#ifndef NO_SESSION_CACHE
    if (FreeMutex(&session_mutex) != 0)
        ret = BAD_MUTEX_E;
#endif
    if (FreeMutex(&count_mutex) != 0)
        ret = BAD_MUTEX_E;

#if defined(HAVE_ECC) && defined(FP_ECC)
    ecc_fp_free();
#endif

    return ret;
}


#ifndef NO_SESSION_CACHE

#ifndef NO_MD5

/* some session IDs aren't random afterall, let's make them random */

static INLINE word32 HashSession(const byte* sessionID, word32 len, int* error)
{
    byte digest[MD5_DIGEST_SIZE];
    Md5  md5;

    (void)error;

    InitMd5(&md5);
    Md5Update(&md5, sessionID, len);
    Md5Final(&md5, digest);

    return MakeWordFromHash(digest);
}

#elif !defined(NO_SHA)

/* 0 on failure */
static INLINE word32 HashSession(const byte* sessionID, word32 len, int* error)
{
    byte digest[SHA_DIGEST_SIZE];
    Sha  sha;
    int  ret = 0;

    ret = InitSha(&sha);
    if (ret != 0) {
        *error = ret;
        return 0;
    }
    ShaUpdate(&sha, sessionID, len);
    ShaFinal(&sha, digest);

    return MakeWordFromHash(digest);
}

#elif !defined(NO_SHA256)

static INLINE word32 HashSession(const byte* sessionID, word32 len, int* error)
{
    byte    digest[SHA256_DIGEST_SIZE];
    Sha256  sha256;
    int     ret;

    ret = InitSha256(&sha256);
    if (ret != 0) {
        *error = ret;
        return 0;
    }

    ret = Sha256Update(&sha256, sessionID, len);
    if (ret != 0) {
        *error = ret;
        return 0;
    }

    ret = Sha256Final(&sha256, digest);
    if (ret != 0) {
        *error = ret;
        return 0;
    }

    return MakeWordFromHash(digest);
}

#else

#error "We need a digest to hash the session IDs"

#endif /* NO_MD5 */


void CyaSSL_flush_sessions(CYASSL_CTX* ctx, long tm)
{
    /* static table now, no flusing needed */
    (void)ctx;
    (void)tm;
}


/* set ssl session timeout in seconds */
int CyaSSL_set_timeout(CYASSL* ssl, unsigned int to)
{
    if (ssl == NULL)
        return BAD_FUNC_ARG;

    ssl->timeout = to;

    return SSL_SUCCESS;
}


/* set ctx session timeout in seconds */
int CyaSSL_CTX_set_timeout(CYASSL_CTX* ctx, unsigned int to)
{
    if (ctx == NULL)
        return BAD_FUNC_ARG;

    ctx->timeout = to;

    return SSL_SUCCESS;
}


#ifndef NO_CLIENT_CACHE

/* Get Session from Client cache based on id/len, return NULL on failure */
CYASSL_SESSION* GetSessionClient(CYASSL* ssl, const byte* id, int len)
{
    CYASSL_SESSION* ret = NULL;
    word32          row;
    int             idx;
    int             count;
    int             error = 0;

    CYASSL_ENTER("GetSessionClient");

    if (ssl->options.side == CYASSL_SERVER_END)
        return NULL;

    len = min(SERVER_ID_LEN, (word32)len);
    row = HashSession(id, len, &error) % SESSION_ROWS;
    if (error != 0) {
        CYASSL_MSG("Hash session failed");
        return NULL;
    }

    if (LockMutex(&session_mutex) != 0) {
        CYASSL_MSG("Lock session mutex failed");
        return NULL;
    }

    /* start from most recently used */
    count = min((word32)ClientCache[row].totalCount, SESSIONS_PER_ROW);
    idx = ClientCache[row].nextIdx - 1;
    if (idx < 0)
        idx = SESSIONS_PER_ROW - 1; /* if back to front, the previous was end */

    for (; count > 0; --count, idx = idx ? idx - 1 : SESSIONS_PER_ROW - 1) {
        CYASSL_SESSION* current;
        ClientSession   clSess;

        if (idx >= SESSIONS_PER_ROW || idx < 0) { /* sanity check */
            CYASSL_MSG("Bad idx");
            break;
        }

        clSess = ClientCache[row].Clients[idx];

        current = &SessionCache[clSess.serverRow].Sessions[clSess.serverIdx];
        if (XMEMCMP(current->serverID, id, len) == 0) {
            CYASSL_MSG("Found a serverid match for client");
            if (LowResTimer() < (current->bornOn + current->timeout)) {
                CYASSL_MSG("Session valid");
                ret = current;
                break;
            } else {
                CYASSL_MSG("Session timed out");  /* could have more for id */
            }
        } else {
            CYASSL_MSG("ServerID not a match from client table");
        }
    }

    UnLockMutex(&session_mutex);

    return ret;
}

#endif /* NO_CLIENT_CACHE */


CYASSL_SESSION* GetSession(CYASSL* ssl, byte* masterSecret)
{
    CYASSL_SESSION* ret = 0;
    const byte*  id = NULL;
    word32       row;
    int          idx;
    int          count;
    int          error = 0;

    if (ssl->options.sessionCacheOff)
        return NULL;

    if (ssl->options.haveSessionId == 0)
        return NULL;

    if (ssl->arrays)
        id = ssl->arrays->sessionID;
    else
        id = ssl->session.sessionID;

    row = HashSession(id, ID_LEN, &error) % SESSION_ROWS;
    if (error != 0) {
        CYASSL_MSG("Hash session failed");
        return NULL;
    }

    if (LockMutex(&session_mutex) != 0)
        return 0;

    /* start from most recently used */
    count = min((word32)SessionCache[row].totalCount, SESSIONS_PER_ROW);
    idx = SessionCache[row].nextIdx - 1;
    if (idx < 0)
        idx = SESSIONS_PER_ROW - 1; /* if back to front, the previous was end */

    for (; count > 0; --count, idx = idx ? idx - 1 : SESSIONS_PER_ROW - 1) {
        CYASSL_SESSION* current;

        if (idx >= SESSIONS_PER_ROW || idx < 0) { /* sanity check */
            CYASSL_MSG("Bad idx");
            break;
        }

        current = &SessionCache[row].Sessions[idx];
        if (XMEMCMP(current->sessionID, id, ID_LEN) == 0) {
            CYASSL_MSG("Found a session match");
            if (LowResTimer() < (current->bornOn + current->timeout)) {
                CYASSL_MSG("Session valid");
                ret = current;
                if (masterSecret)
                    XMEMCPY(masterSecret, current->masterSecret, SECRET_LEN);
            } else {
                CYASSL_MSG("Session timed out");
            }
            break;  /* no more sessionIDs whether valid or not that match */
        } else {
            CYASSL_MSG("SessionID not a match at this idx");
        }
    }

    UnLockMutex(&session_mutex);

    return ret;
}


int SetSession(CYASSL* ssl, CYASSL_SESSION* session)
{
    if (ssl->options.sessionCacheOff)
        return SSL_FAILURE;

    if (LowResTimer() < (session->bornOn + session->timeout)) {
        ssl->session  = *session;
        ssl->options.resuming = 1;

#ifdef SESSION_CERTS
        ssl->version              = session->version;
        ssl->options.cipherSuite0 = session->cipherSuite0;
        ssl->options.cipherSuite  = session->cipherSuite;
#endif

        return SSL_SUCCESS;
    }
    return SSL_FAILURE;  /* session timed out */
}


int AddSession(CYASSL* ssl)
{
    word32 row, idx;
    int    error = 0;

    if (ssl->options.sessionCacheOff)
        return 0;

    if (ssl->options.haveSessionId == 0)
        return 0;

    row = HashSession(ssl->arrays->sessionID, ID_LEN, &error) % SESSION_ROWS;
    if (error != 0) {
        CYASSL_MSG("Hash session failed");
        return error;
    }

    if (LockMutex(&session_mutex) != 0)
        return BAD_MUTEX_E;

    idx = SessionCache[row].nextIdx++;
#ifdef SESSION_INDEX
    ssl->sessionIndex = (row << SESSIDX_ROW_SHIFT) | idx;
#endif

    XMEMCPY(SessionCache[row].Sessions[idx].masterSecret,
           ssl->arrays->masterSecret, SECRET_LEN);
    XMEMCPY(SessionCache[row].Sessions[idx].sessionID, ssl->arrays->sessionID,
           ID_LEN);

    SessionCache[row].Sessions[idx].timeout = ssl->timeout;
    SessionCache[row].Sessions[idx].bornOn  = LowResTimer();

#ifdef SESSION_CERTS
    SessionCache[row].Sessions[idx].chain.count = ssl->session.chain.count;
    XMEMCPY(SessionCache[row].Sessions[idx].chain.certs,
           ssl->session.chain.certs, sizeof(x509_buffer) * MAX_CHAIN_DEPTH);

    SessionCache[row].Sessions[idx].version      = ssl->version;
    SessionCache[row].Sessions[idx].cipherSuite0 = ssl->options.cipherSuite0;
    SessionCache[row].Sessions[idx].cipherSuite  = ssl->options.cipherSuite;
#endif /* SESSION_CERTS */

    SessionCache[row].totalCount++;
    if (SessionCache[row].nextIdx == SESSIONS_PER_ROW)
        SessionCache[row].nextIdx = 0;

#ifndef NO_CLIENT_CACHE
    if (ssl->options.side == CYASSL_CLIENT_END && ssl->session.idLen) {
        word32 clientRow, clientIdx;

        CYASSL_MSG("Adding client cache entry");

        SessionCache[row].Sessions[idx].idLen = ssl->session.idLen;
        XMEMCPY(SessionCache[row].Sessions[idx].serverID, ssl->session.serverID,
                ssl->session.idLen);

        clientRow = HashSession(ssl->session.serverID, ssl->session.idLen,
                                &error) % SESSION_ROWS;
        if (error != 0) {
            CYASSL_MSG("Hash session failed");
            return error;
        }
        clientIdx = ClientCache[clientRow].nextIdx++;

        ClientCache[clientRow].Clients[clientIdx].serverRow = (word16)row;
        ClientCache[clientRow].Clients[clientIdx].serverIdx = (word16)idx;

        ClientCache[clientRow].totalCount++;
        if (ClientCache[clientRow].nextIdx == SESSIONS_PER_ROW)
            ClientCache[clientRow].nextIdx = 0;
    }
    else
        SessionCache[row].Sessions[idx].idLen = 0;
#endif /* NO_CLIENT_CACHE */

    if (UnLockMutex(&session_mutex) != 0)
        return BAD_MUTEX_E;

    return 0;
}


#ifdef SESSION_INDEX

int CyaSSL_GetSessionIndex(CYASSL* ssl)
{
    CYASSL_ENTER("CyaSSL_GetSessionIndex");
    CYASSL_LEAVE("CyaSSL_GetSessionIndex", ssl->sessionIndex);
    return ssl->sessionIndex;
}


int CyaSSL_GetSessionAtIndex(int idx, CYASSL_SESSION* session)
{
    int row, col, result = SSL_FAILURE;

    CYASSL_ENTER("CyaSSL_GetSessionAtIndex");

    row = idx >> SESSIDX_ROW_SHIFT;
    col = idx & SESSIDX_IDX_MASK;

    if (LockMutex(&session_mutex) != 0) {
        return BAD_MUTEX_E;
    }

    if (row < SESSION_ROWS &&
        col < (int)min(SessionCache[row].totalCount, SESSIONS_PER_ROW)) {
        XMEMCPY(session,
                 &SessionCache[row].Sessions[col], sizeof(CYASSL_SESSION));
        result = SSL_SUCCESS;
    }

    if (UnLockMutex(&session_mutex) != 0)
        result = BAD_MUTEX_E;

    CYASSL_LEAVE("CyaSSL_GetSessionAtIndex", result);
    return result;
}

#endif /* SESSION_INDEX */

#if defined(SESSION_INDEX) && defined(SESSION_CERTS)

CYASSL_X509_CHAIN* CyaSSL_SESSION_get_peer_chain(CYASSL_SESSION* session)
{
    CYASSL_X509_CHAIN* chain = NULL;

    CYASSL_ENTER("CyaSSL_SESSION_get_peer_chain");
    if (session)
        chain = &session->chain;

    CYASSL_LEAVE("CyaSSL_SESSION_get_peer_chain", chain ? 1 : 0);
    return chain;
}

#endif /* SESSION_INDEX && SESSION_CERTS */


    #ifdef SESSION_STATS

    CYASSL_API
    void PrintSessionStats(void)
    {
        word32 totalSessionsSeen = 0;
        word32 totalSessionsNow = 0;
        word32 rowNow;
        int    i;
        double E;               /* expected freq */
        double chiSquare = 0;

        for (i = 0; i < SESSION_ROWS; i++) {
            totalSessionsSeen += SessionCache[i].totalCount;

            if (SessionCache[i].totalCount >= SESSIONS_PER_ROW)
                rowNow = SESSIONS_PER_ROW;
            else if (SessionCache[i].nextIdx == 0)
                rowNow = 0;
            else
                rowNow = SessionCache[i].nextIdx;

            totalSessionsNow += rowNow;
        }

        printf("Total Sessions Seen = %d\n", totalSessionsSeen);
        printf("Total Sessions Now  = %d\n", totalSessionsNow);

        E = (double)totalSessionsSeen / SESSION_ROWS;

        for (i = 0; i < SESSION_ROWS; i++) {
            double diff = SessionCache[i].totalCount - E;
            diff *= diff;                /* square    */
            diff /= E;                   /* normalize */

            chiSquare += diff;
        }
        printf("  chi-square = %5.1f, d.f. = %d\n", chiSquare,
                                                     SESSION_ROWS - 1);
        if (SESSION_ROWS == 11)
            printf(" .05 p value =  18.3, chi-square should be less\n");
        else if (SESSION_ROWS == 211)
            printf(".05 p value  = 244.8, chi-square should be less\n");
        else if (SESSION_ROWS == 5981)
            printf(".05 p value  = 6161.0, chi-square should be less\n");
        else if (SESSION_ROWS == 3)
            printf(".05 p value  =   6.0, chi-square should be less\n");
        else if (SESSION_ROWS == 2861)
            printf(".05 p value  = 2985.5, chi-square should be less\n");
        printf("\n");
    }

    #endif /* SESSION_STATS */

#else  /* NO_SESSION_CACHE */

/* No session cache version */
CYASSL_SESSION* GetSession(CYASSL* ssl, byte* masterSecret)
{
    (void)ssl;
    (void)masterSecret;

    return NULL;
}

#endif /* NO_SESSION_CACHE */


/* call before SSL_connect, if verifying will add name check to
   date check and signature check */
int CyaSSL_check_domain_name(CYASSL* ssl, const char* dn)
{
    CYASSL_ENTER("CyaSSL_check_domain_name");
    if (ssl->buffers.domainName.buffer)
        XFREE(ssl->buffers.domainName.buffer, ssl->heap, DYNAMIC_TYPE_DOMAIN);

    ssl->buffers.domainName.length = (word32)XSTRLEN(dn) + 1;
    ssl->buffers.domainName.buffer = (byte*) XMALLOC(
                ssl->buffers.domainName.length, ssl->heap, DYNAMIC_TYPE_DOMAIN);

    if (ssl->buffers.domainName.buffer) {
        XSTRNCPY((char*)ssl->buffers.domainName.buffer, dn,
                ssl->buffers.domainName.length);
        return SSL_SUCCESS;
    }
    else {
        ssl->error = MEMORY_ERROR;
        return SSL_FAILURE;
    }
}


/* turn on CyaSSL zlib compression
   returns SSL_SUCCESS for success, else error (not built in)
*/
int CyaSSL_set_compression(CYASSL* ssl)
{
    CYASSL_ENTER("CyaSSL_set_compression");
    (void)ssl;
#ifdef HAVE_LIBZ
    ssl->options.usingCompression = 1;
    return SSL_SUCCESS;
#else
    return NOT_COMPILED_IN;
#endif
}


#ifndef USE_WINDOWS_API
    #ifndef NO_WRITEV

        /* simulate writev semantics, doesn't actually do block at a time though
           because of SSL_write behavior and because front adds may be small */
        int CyaSSL_writev(CYASSL* ssl, const struct iovec* iov, int iovcnt)
        {
            byte  tmp[FILE_BUFFER_SIZE];
            byte* myBuffer    = tmp;
            int   sending   = 0;
            int   newBuffer = 0;
            int   idx       = 0;
            int   i;
            int   ret;

            CYASSL_ENTER("CyaSSL_writev");

            for (i = 0; i < iovcnt; i++)
                sending += (int)iov[i].iov_len;

            if (sending > (int)sizeof(tmp)) {
                byte* tmp2 = (byte*) XMALLOC(sending, ssl->heap,
                                             DYNAMIC_TYPE_WRITEV);
                if (!tmp2)
                    return MEMORY_ERROR;
                myBuffer = tmp2;
                newBuffer = 1;
            }

            for (i = 0; i < iovcnt; i++) {
                XMEMCPY(&myBuffer[idx], iov[i].iov_base, iov[i].iov_len);
                idx += (int)iov[i].iov_len;
            }

            ret = CyaSSL_write(ssl, myBuffer, sending);

            if (newBuffer) XFREE(myBuffer, ssl->heap, DYNAMIC_TYPE_WRITEV);

            return ret;
        }
    #endif
#endif


#ifdef CYASSL_CALLBACKS

    typedef struct itimerval Itimerval;

    /* don't keep calling simple functions while setting up timer and singals
       if no inlining these are the next best */

    #define AddTimes(a, b, c)                       \
        do {                                        \
            c.tv_sec  = a.tv_sec  + b.tv_sec;       \
            c.tv_usec = a.tv_usec + b.tv_usec;      \
            if (c.tv_usec >=  1000000) {            \
                c.tv_sec++;                         \
                c.tv_usec -= 1000000;               \
            }                                       \
        } while (0)


    #define SubtractTimes(a, b, c)                  \
        do {                                        \
            c.tv_sec  = a.tv_sec  - b.tv_sec;       \
            c.tv_usec = a.tv_usec - b.tv_usec;      \
            if (c.tv_usec < 0) {                    \
                c.tv_sec--;                         \
                c.tv_usec += 1000000;               \
            }                                       \
        } while (0)

    #define CmpTimes(a, b, cmp)                     \
        ((a.tv_sec  ==  b.tv_sec) ?                 \
            (a.tv_usec cmp b.tv_usec) :             \
            (a.tv_sec  cmp b.tv_sec))               \


    /* do nothing handler */
    static void myHandler(int signo)
    {
        (void)signo;
        return;
    }


    static int CyaSSL_ex_wrapper(CYASSL* ssl, HandShakeCallBack hsCb,
                                 TimeoutCallBack toCb, Timeval timeout)
    {
        int       ret        = SSL_FATAL_ERROR;
        int       oldTimerOn = 0;   /* was timer already on */
        Timeval   startTime;
        Timeval   endTime;
        Timeval   totalTime;
        Itimerval myTimeout;
        Itimerval oldTimeout; /* if old timer adjust from total time to reset */
        struct sigaction act, oact;

        #define ERR_OUT(x) { ssl->hsInfoOn = 0; ssl->toInfoOn = 0; return x; }

        if (hsCb) {
            ssl->hsInfoOn = 1;
            InitHandShakeInfo(&ssl->handShakeInfo);
        }
        if (toCb) {
            ssl->toInfoOn = 1;
            InitTimeoutInfo(&ssl->timeoutInfo);

            if (gettimeofday(&startTime, 0) < 0)
                ERR_OUT(GETTIME_ERROR);

            /* use setitimer to simulate getitimer, init 0 myTimeout */
            myTimeout.it_interval.tv_sec  = 0;
            myTimeout.it_interval.tv_usec = 0;
            myTimeout.it_value.tv_sec     = 0;
            myTimeout.it_value.tv_usec    = 0;
            if (setitimer(ITIMER_REAL, &myTimeout, &oldTimeout) < 0)
                ERR_OUT(SETITIMER_ERROR);

            if (oldTimeout.it_value.tv_sec || oldTimeout.it_value.tv_usec) {
                oldTimerOn = 1;

                /* is old timer going to expire before ours */
                if (CmpTimes(oldTimeout.it_value, timeout, <)) {
                    timeout.tv_sec  = oldTimeout.it_value.tv_sec;
                    timeout.tv_usec = oldTimeout.it_value.tv_usec;
                }
            }
            myTimeout.it_value.tv_sec  = timeout.tv_sec;
            myTimeout.it_value.tv_usec = timeout.tv_usec;

            /* set up signal handler, don't restart socket send/recv */
            act.sa_handler = myHandler;
            sigemptyset(&act.sa_mask);
            act.sa_flags = 0;
#ifdef SA_INTERRUPT
            act.sa_flags |= SA_INTERRUPT;
#endif
            if (sigaction(SIGALRM, &act, &oact) < 0)
                ERR_OUT(SIGACT_ERROR);

            if (setitimer(ITIMER_REAL, &myTimeout, 0) < 0)
                ERR_OUT(SETITIMER_ERROR);
        }

        /* do main work */
#ifndef NO_CYASSL_CLIENT
        if (ssl->options.side == CYASSL_CLIENT_END)
            ret = CyaSSL_connect(ssl);
#endif
#ifndef NO_CYASSL_SERVER
        if (ssl->options.side == CYASSL_SERVER_END)
            ret = CyaSSL_accept(ssl);
#endif

        /* do callbacks */
        if (toCb) {
            if (oldTimerOn) {
                gettimeofday(&endTime, 0);
                SubtractTimes(endTime, startTime, totalTime);
                /* adjust old timer for elapsed time */
                if (CmpTimes(totalTime, oldTimeout.it_value, <))
                    SubtractTimes(oldTimeout.it_value, totalTime,
                                  oldTimeout.it_value);
                else {
                    /* reset value to interval, may be off */
                    oldTimeout.it_value.tv_sec = oldTimeout.it_interval.tv_sec;
                    oldTimeout.it_value.tv_usec =oldTimeout.it_interval.tv_usec;
                }
                /* keep iter the same whether there or not */
            }
            /* restore old handler */
            if (sigaction(SIGALRM, &oact, 0) < 0)
                ret = SIGACT_ERROR;    /* more pressing error, stomp */
            else
                /* use old settings which may turn off (expired or not there) */
                if (setitimer(ITIMER_REAL, &oldTimeout, 0) < 0)
                    ret = SETITIMER_ERROR;

            /* if we had a timeout call callback */
            if (ssl->timeoutInfo.timeoutName[0]) {
                ssl->timeoutInfo.timeoutValue.tv_sec  = timeout.tv_sec;
                ssl->timeoutInfo.timeoutValue.tv_usec = timeout.tv_usec;
                (toCb)(&ssl->timeoutInfo);
            }
            /* clean up */
            FreeTimeoutInfo(&ssl->timeoutInfo, ssl->heap);
            ssl->toInfoOn = 0;
        }
        if (hsCb) {
            FinishHandShakeInfo(&ssl->handShakeInfo, ssl);
            (hsCb)(&ssl->handShakeInfo);
            ssl->hsInfoOn = 0;
        }
        return ret;
    }


#ifndef NO_CYASSL_CLIENT

    int CyaSSL_connect_ex(CYASSL* ssl, HandShakeCallBack hsCb,
                          TimeoutCallBack toCb, Timeval timeout)
    {
        CYASSL_ENTER("CyaSSL_connect_ex");
        return CyaSSL_ex_wrapper(ssl, hsCb, toCb, timeout);
    }

#endif


#ifndef NO_CYASSL_SERVER

    int CyaSSL_accept_ex(CYASSL* ssl, HandShakeCallBack hsCb,
                         TimeoutCallBack toCb,Timeval timeout)
    {
        CYASSL_ENTER("CyaSSL_accept_ex");
        return CyaSSL_ex_wrapper(ssl, hsCb, toCb, timeout);
    }

#endif

#endif /* CYASSL_CALLBACKS */


#ifndef NO_PSK

    void CyaSSL_CTX_set_psk_client_callback(CYASSL_CTX* ctx,
                                         psk_client_callback cb)
    {
        CYASSL_ENTER("SSL_CTX_set_psk_client_callback");
        ctx->havePSK = 1;
        ctx->client_psk_cb = cb;
    }


    void CyaSSL_set_psk_client_callback(CYASSL* ssl, psk_client_callback cb)
    {
        byte haveRSA = 1;

        CYASSL_ENTER("SSL_set_psk_client_callback");
        ssl->options.havePSK = 1;
        ssl->options.client_psk_cb = cb;

        #ifdef NO_RSA
            haveRSA = 0;
        #endif
        InitSuites(ssl->suites, ssl->version, haveRSA, TRUE,
                   ssl->options.haveDH, ssl->options.haveNTRU,
                   ssl->options.haveECDSAsig, ssl->options.haveStaticECC,
                   ssl->options.side);
    }


    void CyaSSL_CTX_set_psk_server_callback(CYASSL_CTX* ctx,
                                         psk_server_callback cb)
    {
        CYASSL_ENTER("SSL_CTX_set_psk_server_callback");
        ctx->havePSK = 1;
        ctx->server_psk_cb = cb;
    }


    void CyaSSL_set_psk_server_callback(CYASSL* ssl, psk_server_callback cb)
    {
        byte haveRSA = 1;

        CYASSL_ENTER("SSL_set_psk_server_callback");
        ssl->options.havePSK = 1;
        ssl->options.server_psk_cb = cb;

        #ifdef NO_RSA
            haveRSA = 0;
        #endif
        InitSuites(ssl->suites, ssl->version, haveRSA, TRUE,
                   ssl->options.haveDH, ssl->options.haveNTRU,
                   ssl->options.haveECDSAsig, ssl->options.haveStaticECC,
                   ssl->options.side);
    }


    const char* CyaSSL_get_psk_identity_hint(const CYASSL* ssl)
    {
        CYASSL_ENTER("SSL_get_psk_identity_hint");

        if (ssl == NULL || ssl->arrays == NULL)
            return NULL;

        return ssl->arrays->server_hint;
    }


    const char* CyaSSL_get_psk_identity(const CYASSL* ssl)
    {
        CYASSL_ENTER("SSL_get_psk_identity");

        if (ssl == NULL || ssl->arrays == NULL)
            return NULL;

        return ssl->arrays->client_identity;
    }


    int CyaSSL_CTX_use_psk_identity_hint(CYASSL_CTX* ctx, const char* hint)
    {
        CYASSL_ENTER("SSL_CTX_use_psk_identity_hint");
        if (hint == 0)
            ctx->server_hint[0] = 0;
        else {
            XSTRNCPY(ctx->server_hint, hint, MAX_PSK_ID_LEN);
            ctx->server_hint[MAX_PSK_ID_LEN - 1] = '\0';
        }
        return SSL_SUCCESS;
    }


    int CyaSSL_use_psk_identity_hint(CYASSL* ssl, const char* hint)
    {
        CYASSL_ENTER("SSL_use_psk_identity_hint");

        if (ssl == NULL || ssl->arrays == NULL)
            return SSL_FAILURE;

        if (hint == 0)
            ssl->arrays->server_hint[0] = 0;
        else {
            XSTRNCPY(ssl->arrays->server_hint, hint, MAX_PSK_ID_LEN);
            ssl->arrays->server_hint[MAX_PSK_ID_LEN - 1] = '\0';
        }
        return SSL_SUCCESS;
    }

#endif /* NO_PSK */


#ifndef NO_CERTS
/* used to be defined on NO_FILESYSTEM only, but are generally useful */

    /* CyaSSL extension allows DER files to be loaded from buffers as well */
    int CyaSSL_CTX_load_verify_buffer(CYASSL_CTX* ctx, const unsigned char* in,
                                      long sz, int format)
    {
        CYASSL_ENTER("CyaSSL_CTX_load_verify_buffer");
        if (format == SSL_FILETYPE_PEM)
            return ProcessChainBuffer(ctx, in, sz, format, CA_TYPE, NULL);
        else
            return ProcessBuffer(ctx, in, sz, format, CA_TYPE, NULL,NULL,0);
    }


    int CyaSSL_CTX_use_certificate_buffer(CYASSL_CTX* ctx,
                                 const unsigned char* in, long sz, int format)
    {
        CYASSL_ENTER("CyaSSL_CTX_use_certificate_buffer");
        return ProcessBuffer(ctx, in, sz, format, CERT_TYPE, NULL, NULL, 0);
    }


    int CyaSSL_CTX_use_PrivateKey_buffer(CYASSL_CTX* ctx,
                                 const unsigned char* in, long sz, int format)
    {
        CYASSL_ENTER("CyaSSL_CTX_use_PrivateKey_buffer");
        return ProcessBuffer(ctx, in, sz, format, PRIVATEKEY_TYPE, NULL,NULL,0);
    }


    int CyaSSL_CTX_use_certificate_chain_buffer(CYASSL_CTX* ctx,
                                 const unsigned char* in, long sz)
    {
        CYASSL_ENTER("CyaSSL_CTX_use_certificate_chain_buffer");
        return ProcessBuffer(ctx, in, sz, SSL_FILETYPE_PEM, CERT_TYPE, NULL,
                             NULL, 1);
    }

    int CyaSSL_use_certificate_buffer(CYASSL* ssl,
                                 const unsigned char* in, long sz, int format)
    {
        CYASSL_ENTER("CyaSSL_use_certificate_buffer");
        return ProcessBuffer(ssl->ctx, in, sz, format,CERT_TYPE,ssl,NULL,0);
    }


    int CyaSSL_use_PrivateKey_buffer(CYASSL* ssl,
                                 const unsigned char* in, long sz, int format)
    {
        CYASSL_ENTER("CyaSSL_use_PrivateKey_buffer");
        return ProcessBuffer(ssl->ctx, in, sz, format, PRIVATEKEY_TYPE,
                             ssl, NULL, 0);
    }


    int CyaSSL_use_certificate_chain_buffer(CYASSL* ssl,
                                 const unsigned char* in, long sz)
    {
        CYASSL_ENTER("CyaSSL_use_certificate_chain_buffer");
        return ProcessBuffer(ssl->ctx, in, sz, SSL_FILETYPE_PEM, CERT_TYPE,
                             ssl, NULL, 1);
    }


    /* unload any certs or keys that SSL owns, leave CTX as is
       SSL_SUCCESS on ok */
    int CyaSSL_UnloadCertsKeys(CYASSL* ssl)
    {
        if (ssl == NULL) {
            CYASSL_MSG("Null function arg");
            return BAD_FUNC_ARG;
        }

        if (ssl->buffers.weOwnCert) {
            CYASSL_MSG("Unloading cert");
            XFREE(ssl->buffers.certificate.buffer, ssl->heap,DYNAMIC_TYPE_CERT);
            ssl->buffers.weOwnCert = 0;
            ssl->buffers.certificate.length = 0;
            ssl->buffers.certificate.buffer = NULL;
        }

        if (ssl->buffers.weOwnCertChain) {
            CYASSL_MSG("Unloading cert chain");
            XFREE(ssl->buffers.certChain.buffer, ssl->heap,DYNAMIC_TYPE_CERT);
            ssl->buffers.weOwnCertChain = 0;
            ssl->buffers.certChain.length = 0;
            ssl->buffers.certChain.buffer = NULL;
        }

        if (ssl->buffers.weOwnKey) {
            CYASSL_MSG("Unloading key");
            XFREE(ssl->buffers.key.buffer, ssl->heap, DYNAMIC_TYPE_KEY);
            ssl->buffers.weOwnKey = 0;
            ssl->buffers.key.length = 0;
            ssl->buffers.key.buffer = NULL;
        }

        return SSL_SUCCESS;
    }


    int CyaSSL_CTX_UnloadCAs(CYASSL_CTX* ctx)
    {
        CYASSL_ENTER("CyaSSL_CTX_UnloadCAs");

        if (ctx == NULL)
            return BAD_FUNC_ARG;

        return CyaSSL_CertManagerUnloadCAs(ctx->cm);
    }

/* old NO_FILESYSTEM end */
#endif /* !NO_CERTS */


#if defined(OPENSSL_EXTRA) || defined(GOAHEAD_WS)


    int CyaSSL_add_all_algorithms(void)
    {
        CYASSL_ENTER("CyaSSL_add_all_algorithms");
        CyaSSL_Init();
        return SSL_SUCCESS;
    }


    long CyaSSL_CTX_sess_set_cache_size(CYASSL_CTX* ctx, long sz)
    {
        /* cache size fixed at compile time in CyaSSL */
        (void)ctx;
        (void)sz;
        return 0;
    }


    void CyaSSL_CTX_set_quiet_shutdown(CYASSL_CTX* ctx, int mode)
    {
        CYASSL_ENTER("CyaSSL_CTX_set_quiet_shutdown");
        if (mode)
            ctx->quietShutdown = 1;
    }


    void CyaSSL_set_quiet_shutdown(CYASSL* ssl, int mode)
    {
        CYASSL_ENTER("CyaSSL_CTX_set_quiet_shutdown");
        if (mode)
            ssl->options.quietShutdown = 1;
    }


    void CyaSSL_set_bio(CYASSL* ssl, CYASSL_BIO* rd, CYASSL_BIO* wr)
    {
        CYASSL_ENTER("SSL_set_bio");
        CyaSSL_set_rfd(ssl, rd->fd);
        CyaSSL_set_wfd(ssl, wr->fd);

        ssl->biord = rd;
        ssl->biowr = wr;
    }


    void CyaSSL_CTX_set_client_CA_list(CYASSL_CTX* ctx,
                                       STACK_OF(CYASSL_X509_NAME)* names)
    {
        (void)ctx;
        (void)names;
    }


    STACK_OF(CYASSL_X509_NAME)* CyaSSL_load_client_CA_file(const char* fname)
    {
        (void)fname;
        return 0;
    }


    int CyaSSL_CTX_set_default_verify_paths(CYASSL_CTX* ctx)
    {
        /* TODO:, not needed in goahead */
        (void)ctx;
        return SSL_NOT_IMPLEMENTED;
    }


    /* keyblock size in bytes or -1 */
    int CyaSSL_get_keyblock_size(CYASSL* ssl)
    {
        if (ssl == NULL)
            return SSL_FATAL_ERROR;

        return 2 * (ssl->specs.key_size + ssl->specs.iv_size +
                    ssl->specs.hash_size);
    }


    /* store keys returns SSL_SUCCESS or -1 on error */
    int CyaSSL_get_keys(CYASSL* ssl, unsigned char** ms, unsigned int* msLen,
                                     unsigned char** sr, unsigned int* srLen,
                                     unsigned char** cr, unsigned int* crLen)
    {
        if (ssl == NULL || ssl->arrays == NULL)
            return SSL_FATAL_ERROR;

        *ms = ssl->arrays->masterSecret;
        *sr = ssl->arrays->serverRandom;
        *cr = ssl->arrays->clientRandom;

        *msLen = SECRET_LEN;
        *srLen = RAN_LEN;
        *crLen = RAN_LEN;

        return SSL_SUCCESS;
    }


    void CyaSSL_set_accept_state(CYASSL* ssl)
    {
        byte haveRSA = 1;
        byte havePSK = 0;

        CYASSL_ENTER("SSL_set_accept_state");
        ssl->options.side = CYASSL_SERVER_END;
        /* reset suites in case user switched */

        #ifdef NO_RSA
            haveRSA = 0;
        #endif
        #ifndef NO_PSK
            havePSK = ssl->options.havePSK;
        #endif
        InitSuites(ssl->suites, ssl->version, haveRSA, havePSK,
                   ssl->options.haveDH, ssl->options.haveNTRU,
                   ssl->options.haveECDSAsig, ssl->options.haveStaticECC,
                   ssl->options.side);
    }
#endif

    /* return true if connection established */
    int CyaSSL_is_init_finished(CYASSL* ssl)
    {
        if (ssl == NULL)
            return 0;

        if (ssl->options.handShakeState == HANDSHAKE_DONE)
            return 1;

        return 0;
    }

#if defined(OPENSSL_EXTRA) || defined(GOAHEAD_WS)
    void CyaSSL_CTX_set_tmp_rsa_callback(CYASSL_CTX* ctx,
                                      CYASSL_RSA*(*f)(CYASSL*, int, int))
    {
        /* CyaSSL verifies all these internally */
        (void)ctx;
        (void)f;
    }


    void CyaSSL_set_shutdown(CYASSL* ssl, int opt)
    {
        (void)ssl;
        (void)opt;
    }


    long CyaSSL_CTX_set_options(CYASSL_CTX* ctx, long opt)
    {
        /* goahead calls with 0, do nothing */
        CYASSL_ENTER("SSL_CTX_set_options");
        (void)ctx;
        return opt;
    }


    int CyaSSL_set_rfd(CYASSL* ssl, int rfd)
    {
        CYASSL_ENTER("SSL_set_rfd");
        ssl->rfd = rfd;      /* not used directly to allow IO callbacks */

        ssl->IOCB_ReadCtx  = &ssl->rfd;

        return SSL_SUCCESS;
    }


    int CyaSSL_set_wfd(CYASSL* ssl, int wfd)
    {
        CYASSL_ENTER("SSL_set_wfd");
        ssl->wfd = wfd;      /* not used directly to allow IO callbacks */

        ssl->IOCB_WriteCtx  = &ssl->wfd;

        return SSL_SUCCESS;
    }


    CYASSL_RSA* CyaSSL_RSA_generate_key(int len, unsigned long bits,
                                          void(*f)(int, int, void*), void* data)
    {
        /* no tmp key needed, actual generation not supported */
        CYASSL_ENTER("RSA_generate_key");
        (void)len;
        (void)bits;
        (void)f;
        (void)data;
        return NULL;
    }



    CYASSL_X509* CyaSSL_X509_STORE_CTX_get_current_cert(
                                                     CYASSL_X509_STORE_CTX* ctx)
    {
        (void)ctx;
        return 0;
    }


    int CyaSSL_X509_STORE_CTX_get_error(CYASSL_X509_STORE_CTX* ctx)
    {
        if (ctx != NULL)
            return ctx->error;
        return 0;
    }


    int CyaSSL_X509_STORE_CTX_get_error_depth(CYASSL_X509_STORE_CTX* ctx)
    {
        (void)ctx;
        return 0;
    }


    CYASSL_BIO_METHOD* CyaSSL_BIO_f_buffer(void)
    {
        static CYASSL_BIO_METHOD meth;

        CYASSL_ENTER("BIO_f_buffer");
        meth.type = BIO_BUFFER;

        return &meth;
    }


    long CyaSSL_BIO_set_write_buffer_size(CYASSL_BIO* bio, long size)
    {
        /* CyaSSL has internal buffer, compatibility only */
        CYASSL_ENTER("BIO_set_write_buffer_size");
        (void)bio;
        return size;
    }


    CYASSL_BIO_METHOD* CyaSSL_BIO_f_ssl(void)
    {
        static CYASSL_BIO_METHOD meth;

        CYASSL_ENTER("BIO_f_ssl");
        meth.type = BIO_SSL;

        return &meth;
    }


    CYASSL_BIO* CyaSSL_BIO_new_socket(int sfd, int closeF)
    {
        CYASSL_BIO* bio = (CYASSL_BIO*) XMALLOC(sizeof(CYASSL_BIO), 0,
                                                DYNAMIC_TYPE_OPENSSL);

        CYASSL_ENTER("BIO_new_socket");
        if (bio) {
            bio->type  = BIO_SOCKET;
            bio->close = (byte)closeF;
            bio->eof   = 0;
            bio->ssl   = 0;
            bio->fd    = sfd;
            bio->prev  = 0;
            bio->next  = 0;
            bio->mem   = NULL;
            bio->memLen = 0;
        }
        return bio;
    }


    int CyaSSL_BIO_eof(CYASSL_BIO* b)
    {
        CYASSL_ENTER("BIO_eof");
        if (b->eof)
            return 1;

        return 0;
    }


    long CyaSSL_BIO_set_ssl(CYASSL_BIO* b, CYASSL* ssl, int closeF)
    {
        CYASSL_ENTER("BIO_set_ssl");
        b->ssl   = ssl;
        b->close = (byte)closeF;
    /* add to ssl for bio free if SSL_free called before/instead of free_all? */

        return 0;
    }


    CYASSL_BIO* CyaSSL_BIO_new(CYASSL_BIO_METHOD* method)
    {
        CYASSL_BIO* bio = (CYASSL_BIO*) XMALLOC(sizeof(CYASSL_BIO), 0,
                                                DYNAMIC_TYPE_OPENSSL);
        CYASSL_ENTER("BIO_new");
        if (bio) {
            bio->type   = method->type;
            bio->close  = 0;
            bio->eof    = 0;
            bio->ssl    = NULL;
            bio->mem    = NULL;
            bio->memLen = 0;
            bio->fd     = 0;
            bio->prev   = NULL;
            bio->next   = NULL;
        }
        return bio;
    }


    int CyaSSL_BIO_get_mem_data(CYASSL_BIO* bio, const byte** p)
    {
        if (bio == NULL || p == NULL)
            return SSL_FATAL_ERROR;

        *p = bio->mem;

        return bio->memLen;
    }


    CYASSL_BIO* CyaSSL_BIO_new_mem_buf(void* buf, int len)
    {
        CYASSL_BIO* bio = NULL;
        if (buf == NULL)
            return bio;

        bio = CyaSSL_BIO_new(CyaSSL_BIO_s_mem());
        if (bio == NULL)
            return bio;

        bio->memLen = len;
        bio->mem    = (byte*)XMALLOC(len, 0, DYNAMIC_TYPE_OPENSSL);
        if (bio->mem == NULL) {
            XFREE(bio, 0, DYNAMIC_TYPE_OPENSSL);
            return NULL;
        }

        XMEMCPY(bio->mem, buf, len);

        return bio;
    }


#ifdef USE_WINDOWS_API
    #define CloseSocket(s) closesocket(s)
#elif defined(CYASSL_MDK_ARM)
    #define CloseSocket(s) closesocket(s)
    extern int closesocket(int) ;
#else
    #define CloseSocket(s) close(s)
#endif

    int CyaSSL_BIO_free(CYASSL_BIO* bio)
    {
        /* unchain?, doesn't matter in goahead since from free all */
        CYASSL_ENTER("BIO_free");
        if (bio) {
            if (bio->close) {
                if (bio->ssl)
                    CyaSSL_free(bio->ssl);
                if (bio->fd)
                    CloseSocket(bio->fd);
            }
            if (bio->mem)
                XFREE(bio->mem, 0, DYNAMIC_TYPE_OPENSSL);
            XFREE(bio, 0, DYNAMIC_TYPE_OPENSSL);
        }
        return 0;
    }


    int CyaSSL_BIO_free_all(CYASSL_BIO* bio)
    {
        CYASSL_ENTER("BIO_free_all");
        while (bio) {
            CYASSL_BIO* next = bio->next;
            CyaSSL_BIO_free(bio);
            bio = next;
        }
        return 0;
    }


    int CyaSSL_BIO_read(CYASSL_BIO* bio, void* buf, int len)
    {
        int  ret;
        CYASSL* ssl = 0;
        CYASSL_BIO* front = bio;

        CYASSL_ENTER("BIO_read");
        /* already got eof, again is error */
        if (front->eof)
            return SSL_FATAL_ERROR;

        while(bio && ((ssl = bio->ssl) == 0) )
            bio = bio->next;

        if (ssl == 0) return BAD_FUNC_ARG;

        ret = CyaSSL_read(ssl, buf, len);
        if (ret == 0)
            front->eof = 1;
        else if (ret < 0) {
            int err = CyaSSL_get_error(ssl, 0);
            if ( !(err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE) )
                front->eof = 1;
        }
        return ret;
    }


    int CyaSSL_BIO_write(CYASSL_BIO* bio, const void* data, int len)
    {
        int  ret;
        CYASSL* ssl = 0;
        CYASSL_BIO* front = bio;

        CYASSL_ENTER("BIO_write");
        /* already got eof, again is error */
        if (front->eof)
            return SSL_FATAL_ERROR;

        while(bio && ((ssl = bio->ssl) == 0) )
            bio = bio->next;

        if (ssl == 0) return BAD_FUNC_ARG;

        ret = CyaSSL_write(ssl, data, len);
        if (ret == 0)
            front->eof = 1;
        else if (ret < 0) {
            int err = CyaSSL_get_error(ssl, 0);
            if ( !(err == SSL_ERROR_WANT_READ || err == SSL_ERROR_WANT_WRITE) )
                front->eof = 1;
        }

        return ret;
    }


    CYASSL_BIO* CyaSSL_BIO_push(CYASSL_BIO* top, CYASSL_BIO* append)
    {
        CYASSL_ENTER("BIO_push");
        top->next    = append;
        append->prev = top;

        return top;
    }


    int CyaSSL_BIO_flush(CYASSL_BIO* bio)
    {
        /* for CyaSSL no flushing needed */
        CYASSL_ENTER("BIO_flush");
        (void)bio;
        return 1;
    }


#endif /* OPENSSL_EXTRA || GOAHEAD_WS */


#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)

    void CyaSSL_CTX_set_default_passwd_cb_userdata(CYASSL_CTX* ctx,
                                                   void* userdata)
    {
        CYASSL_ENTER("SSL_CTX_set_default_passwd_cb_userdata");
        ctx->userdata = userdata;
    }


    void CyaSSL_CTX_set_default_passwd_cb(CYASSL_CTX* ctx, pem_password_cb cb)
    {
        CYASSL_ENTER("SSL_CTX_set_default_passwd_cb");
        ctx->passwd_cb = cb;
    }

    int CyaSSL_num_locks(void)
    {
        return 0;
    }

    void CyaSSL_set_locking_callback(void (*f)(int, int, const char*, int))
    {
        (void)f;
    }

    void CyaSSL_set_id_callback(unsigned long (*f)(void))
    {
        (void)f;
    }

    unsigned long CyaSSL_ERR_get_error(void)
    {
        /* TODO: */
        return 0;
    }

    int CyaSSL_EVP_BytesToKey(const CYASSL_EVP_CIPHER* type,
                       const CYASSL_EVP_MD* md, const byte* salt,
                       const byte* data, int sz, int count, byte* key, byte* iv)
    {
        int keyLen = 0;
        int ivLen  = 0;

        Md5    myMD;
        byte   digest[MD5_DIGEST_SIZE];

        int j;
        int keyLeft;
        int ivLeft;
        int keyOutput = 0;

        CYASSL_ENTER("EVP_BytesToKey");
        InitMd5(&myMD);

        /* only support MD5 for now */
        if (XSTRNCMP(md, "MD5", 3) != 0) return 0;

        /* only support CBC DES and AES for now */
        if (XSTRNCMP(type, "DES-CBC", 7) == 0) {
            keyLen = DES_KEY_SIZE;
            ivLen  = DES_IV_SIZE;
        }
        else if (XSTRNCMP(type, "DES-EDE3-CBC", 12) == 0) {
            keyLen = DES3_KEY_SIZE;
            ivLen  = DES_IV_SIZE;
        }
        else if (XSTRNCMP(type, "AES-128-CBC", 11) == 0) {
            keyLen = AES_128_KEY_SIZE;
            ivLen  = AES_IV_SIZE;
        }
        else if (XSTRNCMP(type, "AES-192-CBC", 11) == 0) {
            keyLen = AES_192_KEY_SIZE;
            ivLen  = AES_IV_SIZE;
        }
        else if (XSTRNCMP(type, "AES-256-CBC", 11) == 0) {
            keyLen = AES_256_KEY_SIZE;
            ivLen  = AES_IV_SIZE;
        }
        else
            return 0;

        keyLeft   = keyLen;
        ivLeft    = ivLen;

        while (keyOutput < (keyLen + ivLen)) {
            int digestLeft = MD5_DIGEST_SIZE;
            /* D_(i - 1) */
            if (keyOutput)                      /* first time D_0 is empty */
                Md5Update(&myMD, digest, MD5_DIGEST_SIZE);
            /* data */
            Md5Update(&myMD, data, sz);
            /* salt */
            if (salt)
                Md5Update(&myMD, salt, EVP_SALT_SIZE);
            Md5Final(&myMD, digest);
            /* count */
            for (j = 1; j < count; j++) {
                Md5Update(&myMD, digest, MD5_DIGEST_SIZE);
                Md5Final(&myMD, digest);
            }

            if (keyLeft) {
                int store = min(keyLeft, MD5_DIGEST_SIZE);
                XMEMCPY(&key[keyLen - keyLeft], digest, store);

                keyOutput  += store;
                keyLeft    -= store;
                digestLeft -= store;
            }

            if (ivLeft && digestLeft) {
                int store = min(ivLeft, digestLeft);
                XMEMCPY(&iv[ivLen - ivLeft], &digest[MD5_DIGEST_SIZE -
                                                    digestLeft], store);
                keyOutput += store;
                ivLeft    -= store;
            }
        }
        if (keyOutput != (keyLen + ivLen))
            return 0;
        return keyOutput;
    }

#endif /* OPENSSL_EXTRA || HAVE_WEBSERVER */


#ifdef OPENSSL_EXTRA

    unsigned long CyaSSLeay(void)
    {
        return SSLEAY_VERSION_NUMBER;
    }


    const char* CyaSSLeay_version(int type)
    {
        static const char* version = "SSLeay CyaSSL compatibility";
        (void)type;
        return version;
    }


    void CyaSSL_MD5_Init(CYASSL_MD5_CTX* md5)
    {
        typedef char md5_test[sizeof(MD5_CTX) >= sizeof(Md5) ? 1 : -1];
        (void)sizeof(md5_test);

        CYASSL_ENTER("MD5_Init");
        InitMd5((Md5*)md5);
    }


    void CyaSSL_MD5_Update(CYASSL_MD5_CTX* md5, const void* input,
                           unsigned long sz)
    {
        CYASSL_ENTER("CyaSSL_MD5_Update");
        Md5Update((Md5*)md5, (const byte*)input, (word32)sz);
    }


    void CyaSSL_MD5_Final(byte* input, CYASSL_MD5_CTX* md5)
    {
        CYASSL_ENTER("MD5_Final");
        Md5Final((Md5*)md5, input);
    }


    void CyaSSL_SHA_Init(CYASSL_SHA_CTX* sha)
    {
        typedef char sha_test[sizeof(SHA_CTX) >= sizeof(Sha) ? 1 : -1];
        (void)sizeof(sha_test);

        CYASSL_ENTER("SHA_Init");
        InitSha((Sha*)sha);  /* OpenSSL compat, no ret */
    }


    void CyaSSL_SHA_Update(CYASSL_SHA_CTX* sha, const void* input,
                           unsigned long sz)
    {
        CYASSL_ENTER("SHA_Update");
        ShaUpdate((Sha*)sha, (const byte*)input, (word32)sz);
    }


    void CyaSSL_SHA_Final(byte* input, CYASSL_SHA_CTX* sha)
    {
        CYASSL_ENTER("SHA_Final");
        ShaFinal((Sha*)sha, input);
    }


    void CyaSSL_SHA1_Init(CYASSL_SHA_CTX* sha)
    {
        CYASSL_ENTER("SHA1_Init");
        SHA_Init(sha);
    }


    void CyaSSL_SHA1_Update(CYASSL_SHA_CTX* sha, const void* input,
                            unsigned long sz)
    {
        CYASSL_ENTER("SHA1_Update");
        SHA_Update(sha, input, sz);
    }


    void CyaSSL_SHA1_Final(byte* input, CYASSL_SHA_CTX* sha)
    {
        CYASSL_ENTER("SHA1_Final");
        SHA_Final(input, sha);
    }


    void CyaSSL_SHA256_Init(CYASSL_SHA256_CTX* sha256)
    {
        typedef char sha_test[sizeof(SHA256_CTX) >= sizeof(Sha256) ? 1 : -1];
        (void)sizeof(sha_test);

        CYASSL_ENTER("SHA256_Init");
        InitSha256((Sha256*)sha256);  /* OpenSSL compat, no error */
    }


    void CyaSSL_SHA256_Update(CYASSL_SHA256_CTX* sha, const void* input,
                              unsigned long sz)
    {
        CYASSL_ENTER("SHA256_Update");
        Sha256Update((Sha256*)sha, (const byte*)input, (word32)sz);
        /* OpenSSL compat, no error */
    }


    void CyaSSL_SHA256_Final(byte* input, CYASSL_SHA256_CTX* sha)
    {
        CYASSL_ENTER("SHA256_Final");
        Sha256Final((Sha256*)sha, input);
        /* OpenSSL compat, no error */
    }


    #ifdef CYASSL_SHA384

    void CyaSSL_SHA384_Init(CYASSL_SHA384_CTX* sha)
    {
        typedef char sha_test[sizeof(SHA384_CTX) >= sizeof(Sha384) ? 1 : -1];
        (void)sizeof(sha_test);

        CYASSL_ENTER("SHA384_Init");
        InitSha384((Sha384*)sha);   /* OpenSSL compat, no error */
    }


    void CyaSSL_SHA384_Update(CYASSL_SHA384_CTX* sha, const void* input,
                           unsigned long sz)
    {
        CYASSL_ENTER("SHA384_Update");
        Sha384Update((Sha384*)sha, (const byte*)input, (word32)sz);
        /* OpenSSL compat, no error */
    }


    void CyaSSL_SHA384_Final(byte* input, CYASSL_SHA384_CTX* sha)
    {
        CYASSL_ENTER("SHA384_Final");
        Sha384Final((Sha384*)sha, input);
        /* OpenSSL compat, no error */
    }

    #endif /* CYASSL_SHA384 */


   #ifdef CYASSL_SHA512

    void CyaSSL_SHA512_Init(CYASSL_SHA512_CTX* sha)
    {
        typedef char sha_test[sizeof(SHA512_CTX) >= sizeof(Sha512) ? 1 : -1];
        (void)sizeof(sha_test);

        CYASSL_ENTER("SHA512_Init");
        InitSha512((Sha512*)sha);  /* OpenSSL compat, no error */
    }


    void CyaSSL_SHA512_Update(CYASSL_SHA512_CTX* sha, const void* input,
                           unsigned long sz)
    {
        CYASSL_ENTER("SHA512_Update");
        Sha512Update((Sha512*)sha, (const byte*)input, (word32)sz);
        /* OpenSSL compat, no error */
    }


    void CyaSSL_SHA512_Final(byte* input, CYASSL_SHA512_CTX* sha)
    {
        CYASSL_ENTER("SHA512_Final");
        Sha512Final((Sha512*)sha, input);
        /* OpenSSL compat, no error */
    }

    #endif /* CYASSL_SHA512 */


    const CYASSL_EVP_MD* CyaSSL_EVP_md5(void)
    {
        static const char* type = "MD5";
        CYASSL_ENTER("EVP_md5");
        return type;
    }


    const CYASSL_EVP_MD* CyaSSL_EVP_sha1(void)
    {
        static const char* type = "SHA";
        CYASSL_ENTER("EVP_sha1");
        return type;
    }


    const CYASSL_EVP_MD* CyaSSL_EVP_sha256(void)
    {
        static const char* type = "SHA256";
        CYASSL_ENTER("EVP_sha256");
        return type;
    }

    #ifdef CYASSL_SHA384

    const CYASSL_EVP_MD* CyaSSL_EVP_sha384(void)
    {
        static const char* type = "SHA384";
        CYASSL_ENTER("EVP_sha384");
        return type;
    }

    #endif /* CYASSL_SHA384 */

    #ifdef CYASSL_SHA512

    const CYASSL_EVP_MD* CyaSSL_EVP_sha512(void)
    {
        static const char* type = "SHA512";
        CYASSL_ENTER("EVP_sha512");
        return type;
    }

    #endif /* CYASSL_SHA512 */


    void CyaSSL_EVP_MD_CTX_init(CYASSL_EVP_MD_CTX* ctx)
    {
        CYASSL_ENTER("EVP_CIPHER_MD_CTX_init");
        (void)ctx;
        /* do nothing */
    }


    const CYASSL_EVP_CIPHER* CyaSSL_EVP_aes_128_cbc(void)
    {
        static const char* type = "AES128-CBC";
        CYASSL_ENTER("CyaSSL_EVP_aes_128_cbc");
        return type;
    }


    const CYASSL_EVP_CIPHER* CyaSSL_EVP_aes_192_cbc(void)
    {
        static const char* type = "AES192-CBC";
        CYASSL_ENTER("CyaSSL_EVP_aes_192_cbc");
        return type;
    }


    const CYASSL_EVP_CIPHER* CyaSSL_EVP_aes_256_cbc(void)
    {
        static const char* type = "AES256-CBC";
        CYASSL_ENTER("CyaSSL_EVP_aes_256_cbc");
        return type;
    }


    const CYASSL_EVP_CIPHER* CyaSSL_EVP_aes_128_ctr(void)
    {
        static const char* type = "AES128-CTR";
        CYASSL_ENTER("CyaSSL_EVP_aes_128_ctr");
        return type;
    }


    const CYASSL_EVP_CIPHER* CyaSSL_EVP_aes_192_ctr(void)
    {
        static const char* type = "AES192-CTR";
        CYASSL_ENTER("CyaSSL_EVP_aes_192_ctr");
        return type;
    }


    const CYASSL_EVP_CIPHER* CyaSSL_EVP_aes_256_ctr(void)
    {
        static const char* type = "AES256-CTR";
        CYASSL_ENTER("CyaSSL_EVP_aes_256_ctr");
        return type;
    }


    const CYASSL_EVP_CIPHER* CyaSSL_EVP_des_cbc(void)
    {
        static const char* type = "DES-CBC";
        CYASSL_ENTER("CyaSSL_EVP_des_cbc");
        return type;
    }


    const CYASSL_EVP_CIPHER* CyaSSL_EVP_des_ede3_cbc(void)
    {
        static const char* type = "DES-EDE3-CBC";
        CYASSL_ENTER("CyaSSL_EVP_des_ede3_cbc");
        return type;
    }


    const CYASSL_EVP_CIPHER* CyaSSL_EVP_rc4(void)
    {
        static const char* type = "ARC4";
        CYASSL_ENTER("CyaSSL_EVP_rc4");
        return type;
    }


    const CYASSL_EVP_CIPHER* CyaSSL_EVP_enc_null(void)
    {
        static const char* type = "NULL";
        CYASSL_ENTER("CyaSSL_EVP_enc_null");
        return type;
    }


    int CyaSSL_EVP_MD_CTX_cleanup(CYASSL_EVP_MD_CTX* ctx)
    {
        CYASSL_ENTER("EVP_MD_CTX_cleanup");
        (void)ctx;
        return 0;
    }



    void CyaSSL_EVP_CIPHER_CTX_init(CYASSL_EVP_CIPHER_CTX* ctx)
    {
        CYASSL_ENTER("EVP_CIPHER_CTX_init");
        if (ctx) {
            ctx->cipherType = 0xff;   /* no init */
            ctx->keyLen     = 0;
            ctx->enc        = 1;      /* start in encrypt mode */
        }
    }


    /* SSL_SUCCESS on ok */
    int CyaSSL_EVP_CIPHER_CTX_cleanup(CYASSL_EVP_CIPHER_CTX* ctx)
    {
        CYASSL_ENTER("EVP_CIPHER_CTX_cleanup");
        if (ctx) {
            ctx->cipherType = 0xff;  /* no more init */
            ctx->keyLen     = 0;
        }

        return SSL_SUCCESS;
    }


    /* SSL_SUCCESS on ok */
    int  CyaSSL_EVP_CipherInit(CYASSL_EVP_CIPHER_CTX* ctx,
                               const CYASSL_EVP_CIPHER* type, byte* key,
                               byte* iv, int enc)
    {
        int ret = 0;

        CYASSL_ENTER("CyaSSL_EVP_CipherInit");
        if (ctx == NULL) {
            CYASSL_MSG("no ctx");
            return 0;   /* failure */
        }

        if (type == NULL && ctx->cipherType == 0xff) {
            CYASSL_MSG("no type set");
            return 0;   /* failure */
        }

        if (ctx->cipherType == AES_128_CBC_TYPE || (type &&
                                       XSTRNCMP(type, "AES128-CBC", 10) == 0)) {
            CYASSL_MSG("AES-128-CBC");
            ctx->cipherType = AES_128_CBC_TYPE;
            ctx->keyLen     = 16;
            if (enc == 0 || enc == 1)
                ctx->enc = enc ? 1 : 0;
            if (key) {
                ret = AesSetKey(&ctx->cipher.aes, key, ctx->keyLen, iv,
                                ctx->enc ? AES_ENCRYPTION : AES_DECRYPTION);
                if (ret != 0)
                    return ret;
            }
            if (iv && key == NULL) {
                ret = AesSetIV(&ctx->cipher.aes, iv);
                if (ret != 0)
                    return ret;
            }
        }
        else if (ctx->cipherType == AES_192_CBC_TYPE || (type &&
                                       XSTRNCMP(type, "AES192-CBC", 10) == 0)) {
            CYASSL_MSG("AES-192-CBC");
            ctx->cipherType = AES_192_CBC_TYPE;
            ctx->keyLen     = 24;
            if (enc == 0 || enc == 1)
                ctx->enc = enc ? 1 : 0;
            if (key) {
                ret = AesSetKey(&ctx->cipher.aes, key, ctx->keyLen, iv,
                                ctx->enc ? AES_ENCRYPTION : AES_DECRYPTION);
                if (ret != 0)
                    return ret;
            }
            if (iv && key == NULL) {
                ret = AesSetIV(&ctx->cipher.aes, iv);
                if (ret != 0)
                    return ret;
            }
        }
        else if (ctx->cipherType == AES_256_CBC_TYPE || (type &&
                                       XSTRNCMP(type, "AES256-CBC", 10) == 0)) {
            CYASSL_MSG("AES-256-CBC");
            ctx->cipherType = AES_256_CBC_TYPE;
            ctx->keyLen     = 32;
            if (enc == 0 || enc == 1)
                ctx->enc = enc ? 1 : 0;
            if (key) {
                ret = AesSetKey(&ctx->cipher.aes, key, ctx->keyLen, iv,
                                ctx->enc ? AES_ENCRYPTION : AES_DECRYPTION);
                if (ret != 0)
                    return ret;
            }
            if (iv && key == NULL) {
                ret = AesSetIV(&ctx->cipher.aes, iv);
                if (ret != 0)
                    return ret;
            }
        }
#ifdef CYASSL_AES_COUNTER
        else if (ctx->cipherType == AES_128_CTR_TYPE || (type &&
                                       XSTRNCMP(type, "AES128-CTR", 10) == 0)) {
            CYASSL_MSG("AES-128-CTR");
            ctx->cipherType = AES_128_CTR_TYPE;
            ctx->keyLen     = 16;
            if (enc == 0 || enc == 1)
                ctx->enc = enc ? 1 : 0;
            if (key) {
                ret = AesSetKey(&ctx->cipher.aes, key, ctx->keyLen, iv,
                                AES_ENCRYPTION);
                if (ret != 0)
                    return ret;
            }
            if (iv && key == NULL) {
                ret = AesSetIV(&ctx->cipher.aes, iv);
                if (ret != 0)
                    return ret;
            }
        }
        else if (ctx->cipherType == AES_192_CTR_TYPE || (type &&
                                       XSTRNCMP(type, "AES192-CTR", 10) == 0)) {
            CYASSL_MSG("AES-192-CTR");
            ctx->cipherType = AES_192_CTR_TYPE;
            ctx->keyLen     = 24;
            if (enc == 0 || enc == 1)
                ctx->enc = enc ? 1 : 0;
            if (key) {
                ret = AesSetKey(&ctx->cipher.aes, key, ctx->keyLen, iv,
                                AES_ENCRYPTION);
                if (ret != 0)
                    return ret;
            }
            if (iv && key == NULL) {
                ret = AesSetIV(&ctx->cipher.aes, iv);
                if (ret != 0)
                    return ret;
            }
        }
        else if (ctx->cipherType == AES_256_CTR_TYPE || (type &&
                                       XSTRNCMP(type, "AES256-CTR", 10) == 0)) {
            CYASSL_MSG("AES-256-CTR");
            ctx->cipherType = AES_256_CTR_TYPE;
            ctx->keyLen     = 32;
            if (enc == 0 || enc == 1)
                ctx->enc = enc ? 1 : 0;
            if (key) {
                ret = AesSetKey(&ctx->cipher.aes, key, ctx->keyLen, iv,
                                AES_ENCRYPTION);
                if (ret != 0)
                    return ret;
            }
            if (iv && key == NULL) {
                ret = AesSetIV(&ctx->cipher.aes, iv);
                if (ret != 0)
                    return ret;
            }
        }
#endif /* CYASSL_AES_CTR */
        else if (ctx->cipherType == DES_CBC_TYPE || (type &&
                                       XSTRNCMP(type, "DES-CBC", 7) == 0)) {
            CYASSL_MSG("DES-CBC");
            ctx->cipherType = DES_CBC_TYPE;
            ctx->keyLen     = 8;
            if (enc == 0 || enc == 1)
                ctx->enc = enc ? 1 : 0;
            if (key) {
                ret = Des_SetKey(&ctx->cipher.des, key, iv,
                          ctx->enc ? DES_ENCRYPTION : DES_DECRYPTION);
                if (ret != 0)
                    return ret;
            }

            if (iv && key == NULL)
                Des_SetIV(&ctx->cipher.des, iv);
        }
        else if (ctx->cipherType == DES_EDE3_CBC_TYPE || (type &&
                                     XSTRNCMP(type, "DES-EDE3-CBC", 11) == 0)) {
            CYASSL_MSG("DES-EDE3-CBC");
            ctx->cipherType = DES_EDE3_CBC_TYPE;
            ctx->keyLen     = 24;
            if (enc == 0 || enc == 1)
                ctx->enc = enc ? 1 : 0;
            if (key) {
                ret = Des3_SetKey(&ctx->cipher.des3, key, iv,
                          ctx->enc ? DES_ENCRYPTION : DES_DECRYPTION);
                if (ret != 0)
                    return ret;
            }

            if (iv && key == NULL) {
                ret = Des3_SetIV(&ctx->cipher.des3, iv);
                if (ret != 0)
                    return ret;
            }
        }
        else if (ctx->cipherType == ARC4_TYPE || (type &&
                                     XSTRNCMP(type, "ARC4", 4) == 0)) {
            CYASSL_MSG("ARC4");
            ctx->cipherType = ARC4_TYPE;
            if (ctx->keyLen == 0)  /* user may have already set */
                ctx->keyLen = 16;  /* default to 128 */
            if (key)
                Arc4SetKey(&ctx->cipher.arc4, key, ctx->keyLen);
        }
        else if (ctx->cipherType == NULL_CIPHER_TYPE || (type &&
                                     XSTRNCMP(type, "NULL", 4) == 0)) {
            CYASSL_MSG("NULL cipher");
            ctx->cipherType = NULL_CIPHER_TYPE;
            ctx->keyLen = 0;
        }
        else
            return 0;   /* failure */


        return SSL_SUCCESS;
    }


    /* SSL_SUCCESS on ok */
    int CyaSSL_EVP_CIPHER_CTX_key_length(CYASSL_EVP_CIPHER_CTX* ctx)
    {
        CYASSL_ENTER("CyaSSL_EVP_CIPHER_CTX_key_length");
        if (ctx)
            return ctx->keyLen;

        return 0;   /* failure */
    }


    /* SSL_SUCCESS on ok */
    int CyaSSL_EVP_CIPHER_CTX_set_key_length(CYASSL_EVP_CIPHER_CTX* ctx,
                                             int keylen)
    {
        CYASSL_ENTER("CyaSSL_EVP_CIPHER_CTX_set_key_length");
        if (ctx)
            ctx->keyLen = keylen;
        else
            return 0;  /* failure */

        return SSL_SUCCESS;
    }


    /* SSL_SUCCESS on ok */
    int CyaSSL_EVP_Cipher(CYASSL_EVP_CIPHER_CTX* ctx, byte* dst, byte* src,
                          word32 len)
    {
        int ret = 0;
        CYASSL_ENTER("CyaSSL_EVP_Cipher");

        if (ctx == NULL || dst == NULL || src == NULL) {
            CYASSL_MSG("Bad function argument");
            return 0;  /* failure */
        }

        if (ctx->cipherType == 0xff) {
            CYASSL_MSG("no init");
            return 0;  /* failure */
        }

        switch (ctx->cipherType) {

            case AES_128_CBC_TYPE :
            case AES_192_CBC_TYPE :
            case AES_256_CBC_TYPE :
                CYASSL_MSG("AES CBC");
                if (ctx->enc)
                    ret = AesCbcEncrypt(&ctx->cipher.aes, dst, src, len);
                else
                    ret = AesCbcDecrypt(&ctx->cipher.aes, dst, src, len);
                break;

#ifdef CYASSL_AES_COUNTER
            case AES_128_CTR_TYPE :
            case AES_192_CTR_TYPE :
            case AES_256_CTR_TYPE :
                    CYASSL_MSG("AES CTR");
                    AesCtrEncrypt(&ctx->cipher.aes, dst, src, len);
                break;
#endif

            case DES_CBC_TYPE :
                if (ctx->enc)
                    Des_CbcEncrypt(&ctx->cipher.des, dst, src, len);
                else
                    Des_CbcDecrypt(&ctx->cipher.des, dst, src, len);
                break;

            case DES_EDE3_CBC_TYPE :
                if (ctx->enc)
                    ret = Des3_CbcEncrypt(&ctx->cipher.des3, dst, src, len);
                else
                    ret = Des3_CbcDecrypt(&ctx->cipher.des3, dst, src, len);
                break;

            case ARC4_TYPE :
                Arc4Process(&ctx->cipher.arc4, dst, src, len);
                break;

            case NULL_CIPHER_TYPE :
                XMEMCPY(dst, src, len);
                break;

            default: {
                CYASSL_MSG("bad type");
                return 0;  /* failure */
            }
        }

        if (ret != 0) {
            CYASSL_MSG("CyaSSL_EVP_Cipher failure");
            return 0;  /* failuer */
        }

        CYASSL_MSG("CyaSSL_EVP_Cipher success");
        return SSL_SUCCESS;  /* success */
    }


    /* store for external read of iv, SSL_SUCCESS on success */
    int  CyaSSL_StoreExternalIV(CYASSL_EVP_CIPHER_CTX* ctx)
    {
        CYASSL_ENTER("CyaSSL_StoreExternalIV");

        if (ctx == NULL) {
            CYASSL_MSG("Bad function argument");
            return SSL_FATAL_ERROR;
        }

        switch (ctx->cipherType) {

            case AES_128_CBC_TYPE :
            case AES_192_CBC_TYPE :
            case AES_256_CBC_TYPE :
                CYASSL_MSG("AES CBC");
                memcpy(ctx->iv, &ctx->cipher.aes.reg, AES_BLOCK_SIZE);
                break;

#ifdef CYASSL_AES_COUNTER
            case AES_128_CTR_TYPE :
            case AES_192_CTR_TYPE :
            case AES_256_CTR_TYPE :
                CYASSL_MSG("AES CTR");
                memcpy(ctx->iv, &ctx->cipher.aes.reg, AES_BLOCK_SIZE);
                break;
#endif

            case DES_CBC_TYPE :
                CYASSL_MSG("DES CBC");
                memcpy(ctx->iv, &ctx->cipher.des.reg, DES_BLOCK_SIZE);
                break;

            case DES_EDE3_CBC_TYPE :
                CYASSL_MSG("DES EDE3 CBC");
                memcpy(ctx->iv, &ctx->cipher.des.reg, DES_BLOCK_SIZE);
                break;

            case ARC4_TYPE :
                CYASSL_MSG("ARC4");
                break;

            case NULL_CIPHER_TYPE :
                CYASSL_MSG("NULL");
                break;

            default: {
                CYASSL_MSG("bad type");
                return SSL_FATAL_ERROR;
            }
        }
        return SSL_SUCCESS;
    }


    /* set internal IV from external, SSL_SUCCESS on success */
    int  CyaSSL_SetInternalIV(CYASSL_EVP_CIPHER_CTX* ctx)
    {

        CYASSL_ENTER("CyaSSL_SetInternalIV");

        if (ctx == NULL) {
            CYASSL_MSG("Bad function argument");
            return SSL_FATAL_ERROR;
        }

        switch (ctx->cipherType) {

            case AES_128_CBC_TYPE :
            case AES_192_CBC_TYPE :
            case AES_256_CBC_TYPE :
                CYASSL_MSG("AES CBC");
                memcpy(&ctx->cipher.aes.reg, ctx->iv, AES_BLOCK_SIZE);
                break;

#ifdef CYASSL_AES_COUNTER
            case AES_128_CTR_TYPE :
            case AES_192_CTR_TYPE :
            case AES_256_CTR_TYPE :
                CYASSL_MSG("AES CTR");
                memcpy(&ctx->cipher.aes.reg, ctx->iv, AES_BLOCK_SIZE);
                break;
#endif

            case DES_CBC_TYPE :
                CYASSL_MSG("DES CBC");
                memcpy(&ctx->cipher.des.reg, ctx->iv, DES_BLOCK_SIZE);
                break;

            case DES_EDE3_CBC_TYPE :
                CYASSL_MSG("DES EDE3 CBC");
                memcpy(&ctx->cipher.des.reg, ctx->iv, DES_BLOCK_SIZE);
                break;

            case ARC4_TYPE :
                CYASSL_MSG("ARC4");
                break;

            case NULL_CIPHER_TYPE :
                CYASSL_MSG("NULL");
                break;

            default: {
                CYASSL_MSG("bad type");
                return SSL_FATAL_ERROR;
            }
        }
        return SSL_SUCCESS;
    }


    /* SSL_SUCCESS on ok */
    int CyaSSL_EVP_DigestInit(CYASSL_EVP_MD_CTX* ctx, const CYASSL_EVP_MD* type)
    {
        CYASSL_ENTER("EVP_DigestInit");
        if (XSTRNCMP(type, "MD5", 3) == 0) {
             ctx->macType = MD5;
             CyaSSL_MD5_Init((MD5_CTX*)&ctx->hash);
        }
        else if (XSTRNCMP(type, "SHA256", 6) == 0) {
             ctx->macType = SHA256;
             CyaSSL_SHA256_Init((SHA256_CTX*)&ctx->hash);
        }
    #ifdef CYASSL_SHA384
        else if (XSTRNCMP(type, "SHA384", 6) == 0) {
             ctx->macType = SHA384;
             CyaSSL_SHA384_Init((SHA384_CTX*)&ctx->hash);
        }
    #endif
    #ifdef CYASSL_SHA512
        else if (XSTRNCMP(type, "SHA512", 6) == 0) {
             ctx->macType = SHA512;
             CyaSSL_SHA512_Init((SHA512_CTX*)&ctx->hash);
        }
    #endif
        /* has to be last since would pick or 256, 384, or 512 too */
        else if (XSTRNCMP(type, "SHA", 3) == 0) {
             ctx->macType = SHA;
             CyaSSL_SHA_Init((SHA_CTX*)&ctx->hash);
        }
        else
             return BAD_FUNC_ARG;

        return SSL_SUCCESS;
    }


    /* SSL_SUCCESS on ok */
    int CyaSSL_EVP_DigestUpdate(CYASSL_EVP_MD_CTX* ctx, const void* data,
                                unsigned long sz)
    {
        CYASSL_ENTER("EVP_DigestUpdate");
        if (ctx->macType == MD5)
            CyaSSL_MD5_Update((MD5_CTX*)&ctx->hash, data, (unsigned long)sz);
        else if (ctx->macType == SHA)
            CyaSSL_SHA_Update((SHA_CTX*)&ctx->hash, data, (unsigned long)sz);
        else if (ctx->macType == SHA256)
            CyaSSL_SHA256_Update((SHA256_CTX*)&ctx->hash, data,
                                 (unsigned long)sz);
    #ifdef CYASSL_SHA384
        else if (ctx->macType == SHA384)
            CyaSSL_SHA384_Update((SHA384_CTX*)&ctx->hash, data,
                                 (unsigned long)sz);
    #endif
    #ifdef CYASSL_SHA512
        else if (ctx->macType == SHA512)
            CyaSSL_SHA512_Update((SHA512_CTX*)&ctx->hash, data,
                                 (unsigned long)sz);
    #endif
        else
            return BAD_FUNC_ARG;

        return SSL_SUCCESS;
    }


    /* SSL_SUCCESS on ok */
    int CyaSSL_EVP_DigestFinal(CYASSL_EVP_MD_CTX* ctx, unsigned char* md,
                               unsigned int* s)
    {
        CYASSL_ENTER("EVP_DigestFinal");
        if (ctx->macType == MD5) {
            CyaSSL_MD5_Final(md, (MD5_CTX*)&ctx->hash);
            if (s) *s = MD5_DIGEST_SIZE;
        }
        else if (ctx->macType == SHA) {
            CyaSSL_SHA_Final(md, (SHA_CTX*)&ctx->hash);
            if (s) *s = SHA_DIGEST_SIZE;
        }
        else if (ctx->macType == SHA256) {
            CyaSSL_SHA256_Final(md, (SHA256_CTX*)&ctx->hash);
            if (s) *s = SHA256_DIGEST_SIZE;
        }
    #ifdef CYASSL_SHA384
        else if (ctx->macType == SHA384) {
            CyaSSL_SHA384_Final(md, (SHA384_CTX*)&ctx->hash);
            if (s) *s = SHA384_DIGEST_SIZE;
        }
    #endif
    #ifdef CYASSL_SHA512
        else if (ctx->macType == SHA512) {
            CyaSSL_SHA512_Final(md, (SHA512_CTX*)&ctx->hash);
            if (s) *s = SHA512_DIGEST_SIZE;
        }
    #endif
        else
            return BAD_FUNC_ARG;

        return SSL_SUCCESS;
    }


    /* SSL_SUCCESS on ok */
    int CyaSSL_EVP_DigestFinal_ex(CYASSL_EVP_MD_CTX* ctx, unsigned char* md,
                                  unsigned int* s)
    {
        CYASSL_ENTER("EVP_DigestFinal_ex");
        return EVP_DigestFinal(ctx, md, s);
    }


    unsigned char* CyaSSL_HMAC(const CYASSL_EVP_MD* evp_md, const void* key,
                               int key_len, const unsigned char* d, int n,
                               unsigned char* md, unsigned int* md_len)
    {
        Hmac hmac;

        CYASSL_ENTER("HMAC");
        if (!md) return NULL;  /* no static buffer support */

        if (XSTRNCMP(evp_md, "MD5", 3) == 0) {
            if (HmacSetKey(&hmac, MD5, (const byte*)key, key_len) != 0)
                return NULL;

            if (md_len) *md_len = MD5_DIGEST_SIZE;
        }
        else if (XSTRNCMP(evp_md, "SHA", 3) == 0) {
            if (HmacSetKey(&hmac, SHA, (const byte*)key, key_len) != 0)
                return NULL;

            if (md_len) *md_len = SHA_DIGEST_SIZE;
        }
        else
            return NULL;

        if (HmacUpdate(&hmac, d, n) != 0)
            return NULL;

        if (HmacFinal(&hmac, md) != 0)
            return NULL;
    
        return md;
    }

    void CyaSSL_ERR_clear_error(void)
    {
        /* TODO: */
    }


    int CyaSSL_RAND_status(void)
    {
        return SSL_SUCCESS;  /* CTaoCrypt provides enough seed internally */
    }



    void CyaSSL_RAND_add(const void* add, int len, double entropy)
    {
        (void)add;
        (void)len;
        (void)entropy;

        /* CyaSSL seeds/adds internally, use explicit RNG if you want
           to take control */
    }


    /* SSL_SUCCESS on ok */
    int CyaSSL_DES_key_sched(CYASSL_const_DES_cblock* key,
                             CYASSL_DES_key_schedule* schedule)
    {
        CYASSL_ENTER("DES_key_sched");
        XMEMCPY(schedule, key, sizeof(const_DES_cblock));
        return SSL_SUCCESS;
    }


    void CyaSSL_DES_cbc_encrypt(const unsigned char* input,
                     unsigned char* output, long length,
                     CYASSL_DES_key_schedule* schedule, CYASSL_DES_cblock* ivec,
                     int enc)
    {
        Des myDes;

        CYASSL_ENTER("DES_cbc_encrypt");

        /* OpenSSL compat, no ret */
        Des_SetKey(&myDes, (const byte*)schedule, (const byte*)ivec, !enc);

        if (enc)
            Des_CbcEncrypt(&myDes, output, input, (word32)length);
        else
            Des_CbcDecrypt(&myDes, output, input, (word32)length);
    }


    /* correctly sets ivec for next call */
    void CyaSSL_DES_ncbc_encrypt(const unsigned char* input,
                     unsigned char* output, long length,
                     CYASSL_DES_key_schedule* schedule, CYASSL_DES_cblock* ivec,
                     int enc)
    {
        Des myDes;

        CYASSL_ENTER("DES_ncbc_encrypt");

        /* OpenSSL compat, no ret */
        Des_SetKey(&myDes, (const byte*)schedule, (const byte*)ivec, !enc);

        if (enc)
            Des_CbcEncrypt(&myDes, output, input, (word32)length);
        else
            Des_CbcDecrypt(&myDes, output, input, (word32)length);

        XMEMCPY(ivec, output + length - sizeof(DES_cblock), sizeof(DES_cblock));
    }


    void CyaSSL_ERR_free_strings(void)
    {
        /* handled internally */
    }


    void CyaSSL_ERR_remove_state(unsigned long state)
    {
        /* TODO: GetErrors().Remove(); */
        (void)state;
    }


    void CyaSSL_EVP_cleanup(void)
    {
        /* nothing to do here */
    }


    void CyaSSL_cleanup_all_ex_data(void)
    {
        /* nothing to do here */
    }


    long CyaSSL_CTX_set_mode(CYASSL_CTX* ctx, long mode)
    {
        /* SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER is CyaSSL default mode */

        CYASSL_ENTER("SSL_CTX_set_mode");
        if (mode == SSL_MODE_ENABLE_PARTIAL_WRITE)
            ctx->partialWrite = 1;

        return mode;
    }


    long CyaSSL_CTX_get_mode(CYASSL_CTX* ctx)
    {
        /* TODO: */
        (void)ctx;
        return 0;
    }


    void CyaSSL_CTX_set_default_read_ahead(CYASSL_CTX* ctx, int m)
    {
        /* TODO: maybe? */
        (void)ctx;
        (void)m;
    }


    int CyaSSL_CTX_set_session_id_context(CYASSL_CTX* ctx,
                                       const unsigned char* sid_ctx,
                                       unsigned int sid_ctx_len)
    {
        /* No application specific context needed for cyaSSL */
        (void)ctx;
        (void)sid_ctx;
        (void)sid_ctx_len;
        return SSL_SUCCESS;
    }


    long CyaSSL_CTX_sess_get_cache_size(CYASSL_CTX* ctx)
    {
        /* TODO: maybe? */
        (void)ctx;
        return (~0);
    }

    unsigned long CyaSSL_ERR_get_error_line_data(const char** file, int* line,
                                          const char** data, int *flags)
    {
        /* Not implemented */
        (void)file;
        (void)line;
        (void)data;
        (void)flags;
        return 0;
    }

#endif /* OPENSSL_EXTRA */


#if defined(KEEP_PEER_CERT)

    CYASSL_X509* CyaSSL_get_peer_certificate(CYASSL* ssl)
    {
        CYASSL_ENTER("SSL_get_peer_certificate");
        if (ssl->peerCert.issuer.sz)
            return &ssl->peerCert;
        else
            return 0;
    }

#endif /* KEEP_PEER_CERT */


#if defined(KEEP_PEER_CERT) || defined(SESSION_CERTS)

    void CyaSSL_FreeX509(CYASSL_X509* x509)
    {
        CYASSL_ENTER("CyaSSL_FreeX509");
        FreeX509(x509);
    }


    /* return the next, if any, altname from the peer cert */
    char* CyaSSL_X509_get_next_altname(CYASSL_X509* cert)
    {
        char* ret = NULL;
        CYASSL_ENTER("CyaSSL_X509_get_next_altname");

        /* don't have any to work with */
        if (cert == NULL || cert->altNames == NULL)
            return NULL;

        /* already went through them */
        if (cert->altNamesNext == NULL)
            return NULL;

        ret = cert->altNamesNext->name;
        cert->altNamesNext = cert->altNamesNext->next;

        return ret;
    }


    CYASSL_X509_NAME* CyaSSL_X509_get_issuer_name(CYASSL_X509* cert)
    {
        CYASSL_ENTER("X509_get_issuer_name");
        return &cert->issuer;
    }


    CYASSL_X509_NAME* CyaSSL_X509_get_subject_name(CYASSL_X509* cert)
    {
        CYASSL_ENTER("X509_get_subject_name");
        return &cert->subject;
    }


    int CyaSSL_X509_get_isCA(CYASSL_X509* x509)
    {
        int isCA = 0;

        CYASSL_ENTER("CyaSSL_X509_get_isCA");

        if (x509 != NULL)
            isCA = x509->isCa;

        CYASSL_LEAVE("CyaSSL_X509_get_isCA", isCA);

        return isCA;
    }


#ifdef OPENSSL_EXTRA
    int CyaSSL_X509_ext_isSet_by_NID(CYASSL_X509* x509, int nid)
    {
        int isSet = 0;

        CYASSL_ENTER("CyaSSL_X509_ext_isSet_by_NID");

        if (x509 != NULL) {
            switch (nid) {
                case BASIC_CA_OID: isSet = x509->basicConstSet; break;
                case ALT_NAMES_OID: isSet = x509->subjAltNameSet; break;
                case AUTH_KEY_OID: isSet = x509->authKeyIdSet; break;
                case SUBJ_KEY_OID: isSet = x509->subjKeyIdSet; break;
                case KEY_USAGE_OID: isSet = x509->keyUsageSet; break;
                #ifdef CYASSL_SEP
                    case CERT_POLICY_OID: isSet = x509->certPolicySet; break;
                #endif /* CYASSL_SEP */
            }
        }

        CYASSL_LEAVE("CyaSSL_X509_ext_isSet_by_NID", isSet);

        return isSet;
    }


    int CyaSSL_X509_ext_get_critical_by_NID(CYASSL_X509* x509, int nid)
    {
        int crit = 0;

        CYASSL_ENTER("CyaSSL_X509_ext_get_critical_by_NID");

        if (x509 != NULL) {
            switch (nid) {
                case BASIC_CA_OID: crit = x509->basicConstCrit; break;
                case ALT_NAMES_OID: crit = x509->subjAltNameCrit; break;
                case AUTH_KEY_OID: crit = x509->authKeyIdCrit; break;
                case SUBJ_KEY_OID: crit = x509->subjKeyIdCrit; break;
                case KEY_USAGE_OID: crit = x509->keyUsageCrit; break;
                #ifdef CYASSL_SEP
                    case CERT_POLICY_OID: crit = x509->certPolicyCrit; break;
                #endif /* CYASSL_SEP */
            }
        }

        CYASSL_LEAVE("CyaSSL_X509_ext_get_critical_by_NID", crit);

        return crit;
    }


    int CyaSSL_X509_get_isSet_pathLength(CYASSL_X509* x509)
    {
        int isSet = 0;

        CYASSL_ENTER("CyaSSL_X509_get_isSet_pathLength");

        if (x509 != NULL)
            isSet = x509->basicConstPlSet;

        CYASSL_LEAVE("CyaSSL_X509_get_isSet_pathLength", isSet);

        return isSet;
    }


    word32 CyaSSL_X509_get_pathLength(CYASSL_X509* x509)
    {
        word32 pathLength = 0;

        CYASSL_ENTER("CyaSSL_X509_get_pathLength");

        if (x509 != NULL)
            pathLength = x509->pathLength;

        CYASSL_LEAVE("CyaSSL_X509_get_pathLength", pathLength);

        return pathLength;
    }


    unsigned int CyaSSL_X509_get_keyUsage(CYASSL_X509* x509)
    {
        word16 usage = 0;

        CYASSL_ENTER("CyaSSL_X509_get_keyUsage");

        if (x509 != NULL)
            usage = x509->keyUsage;

        CYASSL_LEAVE("CyaSSL_X509_get_keyUsage", usage);

        return usage;
    }


    byte* CyaSSL_X509_get_authorityKeyID(
                                      CYASSL_X509* x509, byte* dst, int* dstLen)
    {
        byte *id = NULL;
        int copySz = 0;

        CYASSL_ENTER("CyaSSL_X509_get_authorityKeyID");

        if (x509 != NULL) {
            if (x509->authKeyIdSet) {
                copySz = min(dstLen != NULL ? *dstLen : 0,
                                                        (int)x509->authKeyIdSz);
                id = x509->authKeyId;
            }

            if (dst != NULL && dstLen != NULL && id != NULL && copySz > 0) {
                XMEMCPY(dst, id, copySz);
                id = dst;
                *dstLen = copySz;
            }
        }

        CYASSL_LEAVE("CyaSSL_X509_get_authorityKeyID", copySz);

        return id;
    }


    byte* CyaSSL_X509_get_subjectKeyID(
                                      CYASSL_X509* x509, byte* dst, int* dstLen)
    {
        byte *id = NULL;
        int copySz = 0;

        CYASSL_ENTER("CyaSSL_X509_get_subjectKeyID");

        if (x509 != NULL) {
            if (x509->subjKeyIdSet) {
                copySz = min(dstLen != NULL ? *dstLen : 0,
                                                        (int)x509->subjKeyIdSz);
                id = x509->subjKeyId;
            }

            if (dst != NULL && dstLen != NULL && id != NULL && copySz > 0) {
                XMEMCPY(dst, id, copySz);
                id = dst;
                *dstLen = copySz;
            }
        }

        CYASSL_LEAVE("CyaSSL_X509_get_subjectKeyID", copySz);

        return id;
    }


    int CyaSSL_X509_NAME_entry_count(CYASSL_X509_NAME* name)
    {
        int count = 0;

        CYASSL_ENTER("CyaSSL_X509_NAME_entry_count");

        if (name != NULL)
            count = name->fullName.entryCount;

        CYASSL_LEAVE("CyaSSL_X509_NAME_entry_count", count);
        return count;
    }


    int CyaSSL_X509_NAME_get_text_by_NID(CYASSL_X509_NAME* name,
                                                    int nid, char* buf, int len)
    {
        char *text = NULL;
        int textSz = 0;

        CYASSL_ENTER("CyaSSL_X509_NAME_get_text_by_NID");

        switch (nid) {
            case ASN_COMMON_NAME:
                text = name->fullName.fullName + name->fullName.cnIdx;
                textSz = name->fullName.cnLen;
                break;
            case ASN_SUR_NAME:
                text = name->fullName.fullName + name->fullName.snIdx;
                textSz = name->fullName.snLen;
                break;
            case ASN_SERIAL_NUMBER:
                text = name->fullName.fullName + name->fullName.serialIdx;
                textSz = name->fullName.serialLen;
                break;
            case ASN_COUNTRY_NAME:
                text = name->fullName.fullName + name->fullName.cIdx;
                textSz = name->fullName.cLen;
                break;
            case ASN_LOCALITY_NAME:
                text = name->fullName.fullName + name->fullName.lIdx;
                textSz = name->fullName.lLen;
                break;
            case ASN_STATE_NAME:
                text = name->fullName.fullName + name->fullName.stIdx;
                textSz = name->fullName.stLen;
                break;
            case ASN_ORG_NAME:
                text = name->fullName.fullName + name->fullName.oIdx;
                textSz = name->fullName.oLen;
                break;
            case ASN_ORGUNIT_NAME:
                text = name->fullName.fullName + name->fullName.ouIdx;
                textSz = name->fullName.ouLen;
                break;
            default:
                break;
        }

        if (buf != NULL && text != NULL) {
            textSz = min(textSz, len);
            XMEMCPY(buf, text, textSz);
            buf[textSz] = '\0';
        }

        CYASSL_LEAVE("CyaSSL_X509_NAME_get_text_by_NID", textSz);
        return textSz;
    }
#endif


    /* copy name into in buffer, at most sz bytes, if buffer is null will
       malloc buffer, call responsible for freeing                     */
    char* CyaSSL_X509_NAME_oneline(CYASSL_X509_NAME* name, char* in, int sz)
    {
        int copySz = min(sz, name->sz);

        CYASSL_ENTER("CyaSSL_X509_NAME_oneline");
        if (!name->sz) return in;

        if (!in) {
            in = (char*)XMALLOC(name->sz, 0, DYNAMIC_TYPE_OPENSSL);
            if (!in ) return in;
            copySz = name->sz;
        }

        if (copySz == 0)
            return in;

        XMEMCPY(in, name->name, copySz - 1);
        in[copySz - 1] = 0;

        return in;
    }


    int CyaSSL_X509_get_signature_type(CYASSL_X509* x509)
    {
        int type = 0;

        CYASSL_ENTER("CyaSSL_X509_get_signature_type");

        if (x509 != NULL)
            type = x509->sigOID;

        return type;
    }


    int CyaSSL_X509_get_signature(CYASSL_X509* x509,
                                                 unsigned char* buf, int* bufSz)
    {
        CYASSL_ENTER("CyaSSL_X509_get_signature");
        if (x509 == NULL || bufSz == NULL || *bufSz < (int)x509->sig.length)
            return SSL_FATAL_ERROR;

        if (buf != NULL)
            XMEMCPY(buf, x509->sig.buffer, x509->sig.length);
        *bufSz = x509->sig.length;

        return SSL_SUCCESS;
    }


    /* write X509 serial number in unsigned binary to buffer
       buffer needs to be at least EXTERNAL_SERIAL_SIZE (32) for all cases
       return SSL_SUCCESS on success */
    int CyaSSL_X509_get_serial_number(CYASSL_X509* x509, byte* in, int* inOutSz)
    {
        CYASSL_ENTER("CyaSSL_X509_get_serial_number");
        if (x509 == NULL || in == NULL ||
                                   inOutSz == NULL || *inOutSz < x509->serialSz)
            return BAD_FUNC_ARG;

        XMEMCPY(in, x509->serial, x509->serialSz);
        *inOutSz = x509->serialSz;

        return SSL_SUCCESS;
    }


    const byte* CyaSSL_X509_get_der(CYASSL_X509* x509, int* outSz)
    {
        CYASSL_ENTER("CyaSSL_X509_get_der");

        if (x509 == NULL || outSz == NULL)
            return NULL;

        *outSz = (int)x509->derCert.length;
        return x509->derCert.buffer;
    }


    int CyaSSL_X509_version(CYASSL_X509* x509)
    {
        CYASSL_ENTER("CyaSSL_X509_version");

        if (x509 == NULL)
            return 0;

        return x509->version;
    }


    const byte* CyaSSL_X509_notBefore(CYASSL_X509* x509)
    {
        CYASSL_ENTER("CyaSSL_X509_notBefore");

        if (x509 == NULL)
            return NULL;

        return x509->notBefore;
    }


    const byte* CyaSSL_X509_notAfter(CYASSL_X509* x509)
    {
        CYASSL_ENTER("CyaSSL_X509_notAfter");

        if (x509 == NULL)
            return NULL;

        return x509->notAfter;
    }


#ifdef CYASSL_SEP

/* copy oid into in buffer, at most *inOutSz bytes, if buffer is null will
   malloc buffer, call responsible for freeing. Actual size returned in
   *inOutSz. Requires inOutSz be non-null */
byte* CyaSSL_X509_get_device_type(CYASSL_X509* x509, byte* in, int *inOutSz)
{
    int copySz;

    CYASSL_ENTER("CyaSSL_X509_get_dev_type");
    if (inOutSz == NULL) return NULL;
    if (!x509->deviceTypeSz) return in;

    copySz = min(*inOutSz, x509->deviceTypeSz);

    if (!in) {
        in = (byte*)XMALLOC(x509->deviceTypeSz, 0, DYNAMIC_TYPE_OPENSSL);
        if (!in) return in;
        copySz = x509->deviceTypeSz;
    }

    XMEMCPY(in, x509->deviceType, copySz);
    *inOutSz = copySz;

    return in;
}


byte* CyaSSL_X509_get_hw_type(CYASSL_X509* x509, byte* in, int* inOutSz)
{
    int copySz;

    CYASSL_ENTER("CyaSSL_X509_get_hw_type");
    if (inOutSz == NULL) return NULL;
    if (!x509->hwTypeSz) return in;

    copySz = min(*inOutSz, x509->hwTypeSz);

    if (!in) {
        in = (byte*)XMALLOC(x509->hwTypeSz, 0, DYNAMIC_TYPE_OPENSSL);
        if (!in) return in;
        copySz = x509->hwTypeSz;
    }

    XMEMCPY(in, x509->hwType, copySz);
    *inOutSz = copySz;

    return in;
}


byte* CyaSSL_X509_get_hw_serial_number(CYASSL_X509* x509,byte* in,int* inOutSz)
{
    int copySz;

    CYASSL_ENTER("CyaSSL_X509_get_hw_serial_number");
    if (inOutSz == NULL) return NULL;
    if (!x509->hwTypeSz) return in;

    copySz = min(*inOutSz, x509->hwSerialNumSz);

    if (!in) {
        in = (byte*)XMALLOC(x509->hwSerialNumSz, 0, DYNAMIC_TYPE_OPENSSL);
        if (!in) return in;
        copySz = x509->hwSerialNumSz;
    }

    XMEMCPY(in, x509->hwSerialNum, copySz);
    *inOutSz = copySz;

    return in;
}

#endif /* CYASSL_SEP */


CYASSL_X509* CyaSSL_X509_d2i(CYASSL_X509** x509, const byte* in, int len)
{
    CYASSL_X509 *newX509 = NULL;

    CYASSL_ENTER("CyaSSL_X509_d2i");

    if (in != NULL && len != 0) {
        DecodedCert cert;

        InitDecodedCert(&cert, (byte*)in, len, NULL);
        if (ParseCertRelative(&cert, CERT_TYPE, 0, NULL) == 0) {
            newX509 = (CYASSL_X509*)XMALLOC(sizeof(CYASSL_X509),
                                                       NULL, DYNAMIC_TYPE_X509);
            if (newX509 != NULL) {
                InitX509(newX509, 1);
                if (CopyDecodedToX509(newX509, &cert) != 0) {
                    XFREE(newX509, NULL, DYNAMIC_TYPE_X509);
                    newX509 = NULL;
                }
            }
        }
        FreeDecodedCert(&cert);
    }

    if (x509 != NULL)
        *x509 = newX509;

    return newX509;
}


#ifndef NO_FILESYSTEM

#ifndef NO_STDIO_FILESYSTEM

CYASSL_X509* CyaSSL_X509_d2i_fp(CYASSL_X509** x509, XFILE file)
{
    CYASSL_X509* newX509 = NULL;

    CYASSL_ENTER("CyaSSL_X509_d2i_fp");

    if (file != XBADFILE) {
        byte* fileBuffer = NULL;
        long sz = 0;

        XFSEEK(file, 0, XSEEK_END);
        sz = XFTELL(file);
        XREWIND(file);

        fileBuffer = (byte*)XMALLOC(sz, NULL, DYNAMIC_TYPE_FILE);
        if (fileBuffer != NULL) {
            if ((int)XFREAD(fileBuffer, sz, 1, file) > 0) {
                newX509 = CyaSSL_X509_d2i(NULL, fileBuffer, (int)sz);
            }
            XFREE(fileBuffer, NULL, DYNAMIC_TYPE_FILE);
        }
    }

    if (x509 != NULL)
        *x509 = newX509;

    return newX509;
}

#endif /* NO_STDIO_FILESYSTEM */

CYASSL_X509* CyaSSL_X509_load_certificate_file(const char* fname, int format)
{
    byte staticBuffer[FILE_BUFFER_SIZE];
    byte* fileBuffer = staticBuffer;
    int dynamic = 0;
    long sz = 0;
    XFILE file;
    CYASSL_X509* x509 = NULL;
    buffer der;

    CYASSL_ENTER("CyaSSL_X509_load_certificate");

    /* Check the inputs */
    if ((fname == NULL) ||
        (format != SSL_FILETYPE_ASN1 && format != SSL_FILETYPE_PEM))
        return NULL;

    file = XFOPEN(fname, "rb");
    if (file == XBADFILE) return NULL;
    XFSEEK(file, 0, XSEEK_END);
    sz = XFTELL(file);
    XREWIND(file);

    if (sz > (long)sizeof(staticBuffer)) {
        fileBuffer = (byte*)XMALLOC(sz, NULL, DYNAMIC_TYPE_FILE);
        if (fileBuffer == NULL) {
            XFCLOSE(file);
            return NULL;
        }
        dynamic = 1;
    }
    if ((int)XFREAD(fileBuffer, sz, 1, file) < 0) {
        XFCLOSE(file);
        if (dynamic) XFREE(fileBuffer, NULL, DYNAMIC_TYPE_FILE);
        return NULL;
    }
    XFCLOSE(file);

    der.buffer = NULL;
    der.length = 0;

    if (format == SSL_FILETYPE_PEM) {
        EncryptedInfo info;
        int ecc = 0;

        info.set = 0;
        info.ctx = NULL;
        info.consumed = 0;

        if (PemToDer(fileBuffer, sz, CERT_TYPE, &der, NULL, &info, &ecc) != 0)
        {
            /* Only time this should fail, and leave `der` with a buffer
               is when the Base64 Decode fails. Release `der.buffer` in
               that case. */
            if (der.buffer != NULL) {
                XFREE(der.buffer, NULL, DYNAMIC_TYPE_CERT);
                der.buffer = NULL;
            }
        }
    }
    else {
        der.buffer = (byte*)XMALLOC(sz, NULL, DYNAMIC_TYPE_CERT);
        if (der.buffer != NULL) {
            XMEMCPY(der.buffer, fileBuffer, sz);
            der.length = (word32)sz;
        }
    }
    if (dynamic) XFREE(fileBuffer, NULL, DYNAMIC_TYPE_FILE);

    /* At this point we want `der` to have the certificate in DER format */
    /* ready to be decoded. */
    if (der.buffer != NULL) {
        DecodedCert cert;

        InitDecodedCert(&cert, der.buffer, der.length, NULL);
        if (ParseCertRelative(&cert, CERT_TYPE, 0, NULL) == 0) {
            x509 = (CYASSL_X509*)XMALLOC(sizeof(CYASSL_X509),
                                                       NULL, DYNAMIC_TYPE_X509);
            if (x509 != NULL) {
                InitX509(x509, 1);
                if (CopyDecodedToX509(x509, &cert) != 0) {
                    XFREE(x509, NULL, DYNAMIC_TYPE_X509);
                    x509 = NULL;
                }
            }
        }
        FreeDecodedCert(&cert);

        XFREE(der.buffer, NULL, DYNAMIC_TYPE_CERT);
    }

    return x509;
}

#endif /* NO_FILESYSTEM */

#endif /* KEEP_PEER_CERT || SESSION_CERTS */


#ifdef OPENSSL_EXTRA
    int CyaSSL_set_ex_data(CYASSL* ssl, int idx, void* data)
    {
#ifdef FORTRESS
        if (ssl != NULL && idx < MAX_EX_DATA)
        {
            ssl->ex_data[idx] = data;
            return SSL_SUCCESS;
        }
#else
        (void)ssl;
        (void)idx;
        (void)data;
#endif
        return SSL_FAILURE;
    }


    int CyaSSL_set_session_id_context(CYASSL* ssl, const unsigned char* id,
                                   unsigned int len)
    {
        (void)ssl;
        (void)id;
        (void)len;
        return 0;
    }


    void CyaSSL_set_connect_state(CYASSL* ssl)
    {
        (void)ssl;
        /* client by default */
    }
#endif

    int CyaSSL_get_shutdown(const CYASSL* ssl)
    {
        return (ssl->options.isClosed  ||
                ssl->options.connReset ||
                ssl->options.sentNotify);
    }


    int CyaSSL_session_reused(CYASSL* ssl)
    {
        return ssl->options.resuming;
    }

#ifdef OPENSSL_EXTRA
    void CyaSSL_SESSION_free(CYASSL_SESSION* session)
    {
        (void)session;
    }
#endif

    const char* CyaSSL_get_version(CYASSL* ssl)
    {
        CYASSL_ENTER("SSL_get_version");
        if (ssl->version.major == SSLv3_MAJOR) {
            switch (ssl->version.minor) {
                case SSLv3_MINOR :
                    return "SSLv3";
                case TLSv1_MINOR :
                    return "TLSv1";
                case TLSv1_1_MINOR :
                    return "TLSv1.1";
                case TLSv1_2_MINOR :
                    return "TLSv1.2";
                default:
                    return "unknown";
            }
        }
        else if (ssl->version.major == DTLS_MAJOR) {
            switch (ssl->version.minor) {
                case DTLS_MINOR :
                    return "DTLS";
                case DTLSv1_2_MINOR :
                    return "DTLSv1.2";
                default:
                    return "unknown";
            }
        }
        return "unknown";
    }

    int CyaSSL_get_current_cipher_suite(CYASSL* ssl)
    {
        CYASSL_ENTER("SSL_get_current_cipher_suite");
        if (ssl)
            return (ssl->options.cipherSuite0 << 8) | ssl->options.cipherSuite;
        return 0;
    }

    CYASSL_CIPHER* CyaSSL_get_current_cipher(CYASSL* ssl)
    {
        CYASSL_ENTER("SSL_get_current_cipher");
        if (ssl)
            return &ssl->cipher;
        else
            return NULL;
    }


    const char* CyaSSL_CIPHER_get_name(const CYASSL_CIPHER* cipher)
    {
        (void)cipher;

        CYASSL_ENTER("SSL_CIPHER_get_name");
#ifndef NO_ERROR_STRINGS
        if (cipher) {
#if defined(HAVE_ECC) || defined(HAVE_AESCCM)
            /* Awkwardly, the ECC cipher suites use the ECC_BYTE as expected,
             * but the AES-CCM cipher suites also use it, even the ones that
             * aren't ECC. */
            if (cipher->ssl->options.cipherSuite0 == ECC_BYTE) {
            /* ECC suites */
            switch (cipher->ssl->options.cipherSuite) {
#ifdef HAVE_ECC
#ifndef NO_RSA
                case TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256 :
                    return "TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256";
#endif
                case TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256 :
                    return "TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256";
#ifndef NO_RSA
                case TLS_ECDH_RSA_WITH_AES_128_CBC_SHA256 :
                    return "TLS_ECDH_RSA_WITH_AES_128_CBC_SHA256";
#endif
                case TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA256 :
                    return "TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA256";
#ifndef NO_RSA
                case TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384 :
                    return "TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384";
#endif
                case TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA384 :
                    return "TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA384";
#ifndef NO_RSA
                case TLS_ECDH_RSA_WITH_AES_256_CBC_SHA384 :
                    return "TLS_ECDH_RSA_WITH_AES_256_CBC_SHA384";
#endif
                case TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA384 :
                    return "TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA384";
#ifndef NO_SHA
    #ifndef NO_RSA
                case TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA :
                    return "TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA";
                case TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA :
                    return "TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA";
    #endif
                case TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA :
                    return "TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA";
                case TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA :
                    return "TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA";
    #ifndef NO_RC4
        #ifndef NO_RSA
                case TLS_ECDHE_RSA_WITH_RC4_128_SHA :
                    return "TLS_ECDHE_RSA_WITH_RC4_128_SHA";
        #endif
                case TLS_ECDHE_ECDSA_WITH_RC4_128_SHA :
                    return "TLS_ECDHE_ECDSA_WITH_RC4_128_SHA";
    #endif
    #ifndef NO_DES3
        #ifndef NO_RSA
                case TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA :
                    return "TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA";
        #endif
                case TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA :
                    return "TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA";
    #endif

    #ifndef NO_RSA
                case TLS_ECDH_RSA_WITH_AES_128_CBC_SHA :
                    return "TLS_ECDH_RSA_WITH_AES_128_CBC_SHA";
                case TLS_ECDH_RSA_WITH_AES_256_CBC_SHA :
                    return "TLS_ECDH_RSA_WITH_AES_256_CBC_SHA";
    #endif
                case TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA :
                    return "TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA";
                case TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA :
                    return "TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA";
    #ifndef NO_RC4
        #ifndef NO_RSA
                case TLS_ECDH_RSA_WITH_RC4_128_SHA :
                    return "TLS_ECDH_RSA_WITH_RC4_128_SHA";
        #endif
                case TLS_ECDH_ECDSA_WITH_RC4_128_SHA :
                    return "TLS_ECDH_ECDSA_WITH_RC4_128_SHA";
    #endif
    #ifndef NO_DES3
        #ifndef NO_RSA
                case TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA :
                    return "TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA";
        #endif
                case TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA :
                    return "TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA";
    #endif
#endif /* NO_SHA */

#ifdef HAVE_AESGCM
    #ifndef NO_RSA
                case TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256 :
                    return "TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256";
                case TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384 :
                    return "TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384";
    #endif
                case TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256 :
                    return "TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256";
                case TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384 :
                    return "TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384";
    #ifndef NO_RSA
                case TLS_ECDH_RSA_WITH_AES_128_GCM_SHA256 :
                    return "TLS_ECDH_RSA_WITH_AES_128_GCM_SHA256";
                case TLS_ECDH_RSA_WITH_AES_256_GCM_SHA384 :
                    return "TLS_ECDH_RSA_WITH_AES_256_GCM_SHA384";
    #endif
                case TLS_ECDH_ECDSA_WITH_AES_128_GCM_SHA256 :
                    return "TLS_ECDH_ECDSA_WITH_AES_128_GCM_SHA256";
                case TLS_ECDH_ECDSA_WITH_AES_256_GCM_SHA384 :
                    return "TLS_ECDH_ECDSA_WITH_AES_256_GCM_SHA384";
#endif
#endif /* HAVE_ECC */

#ifdef HAVE_AESCCM
    #ifndef NO_RSA
                case TLS_RSA_WITH_AES_128_CCM_8 :
                    return "TLS_RSA_WITH_AES_128_CCM_8";
                case TLS_RSA_WITH_AES_256_CCM_8 :
                    return "TLS_RSA_WITH_AES_256_CCM_8";
    #endif
    #ifndef NO_PSK
                case TLS_PSK_WITH_AES_128_CCM_8 :
                    return "TLS_PSK_WITH_AES_128_CCM_8";
                case TLS_PSK_WITH_AES_256_CCM_8 :
                    return "TLS_PSK_WITH_AES_256_CCM_8";
                case TLS_PSK_WITH_AES_128_CCM :
                    return "TLS_PSK_WITH_AES_128_CCM";
                case TLS_PSK_WITH_AES_256_CCM :
                    return "TLS_PSK_WITH_AES_256_CCM";
                case TLS_DHE_PSK_WITH_AES_128_CCM :
                    return "TLS_DHE_PSK_WITH_AES_128_CCM";
                case TLS_DHE_PSK_WITH_AES_256_CCM :
                    return "TLS_DHE_PSK_WITH_AES_256_CCM";
    #endif
    #ifdef HAVE_ECC
                case TLS_ECDHE_ECDSA_WITH_AES_128_CCM_8:
                    return "TLS_ECDHE_ECDSA_WITH_AES_128_CCM_8";
                case TLS_ECDHE_ECDSA_WITH_AES_256_CCM_8 :
                    return "TLS_ECDHE_ECDSA_WITH_AES_256_CCM_8";
    #endif
#endif

                default:
                    return "NONE";
            }
            }
#endif  /* ECC */
            if (cipher->ssl->options.cipherSuite0 != ECC_BYTE) {
            /* normal suites */
            switch (cipher->ssl->options.cipherSuite) {
#ifndef NO_RSA
    #ifndef NO_RC4
        #ifndef NO_SHA
                case SSL_RSA_WITH_RC4_128_SHA :
                    return "SSL_RSA_WITH_RC4_128_SHA";
        #endif
        #ifndef NO_MD5
                case SSL_RSA_WITH_RC4_128_MD5 :
                    return "SSL_RSA_WITH_RC4_128_MD5";
        #endif
    #endif
    #ifndef NO_SHA
        #ifndef NO_DES3
                case SSL_RSA_WITH_3DES_EDE_CBC_SHA :
                    return "SSL_RSA_WITH_3DES_EDE_CBC_SHA";
        #endif
                case TLS_RSA_WITH_AES_128_CBC_SHA :
                    return "TLS_RSA_WITH_AES_128_CBC_SHA";
                case TLS_RSA_WITH_AES_256_CBC_SHA :
                    return "TLS_RSA_WITH_AES_256_CBC_SHA";
    #endif
                case TLS_RSA_WITH_AES_128_CBC_SHA256 :
                    return "TLS_RSA_WITH_AES_128_CBC_SHA256";
                case TLS_RSA_WITH_AES_256_CBC_SHA256 :
                    return "TLS_RSA_WITH_AES_256_CBC_SHA256";
        #ifdef HAVE_BLAKE2
                case TLS_RSA_WITH_AES_128_CBC_B2B256:
                    return "TLS_RSA_WITH_AES_128_CBC_B2B256";
                case TLS_RSA_WITH_AES_256_CBC_B2B256:
                    return "TLS_RSA_WITH_AES_256_CBC_B2B256";
        #endif
    #ifndef NO_SHA
                case TLS_RSA_WITH_NULL_SHA :
                    return "TLS_RSA_WITH_NULL_SHA";
    #endif
                case TLS_RSA_WITH_NULL_SHA256 :
                    return "TLS_RSA_WITH_NULL_SHA256";
#endif /* NO_RSA */
#ifndef NO_PSK
    #ifndef NO_SHA
                case TLS_PSK_WITH_AES_128_CBC_SHA :
                    return "TLS_PSK_WITH_AES_128_CBC_SHA";
                case TLS_PSK_WITH_AES_256_CBC_SHA :
                    return "TLS_PSK_WITH_AES_256_CBC_SHA";
    #endif
    #ifndef NO_SHA256
                case TLS_PSK_WITH_AES_128_CBC_SHA256 :
                    return "TLS_PSK_WITH_AES_128_CBC_SHA256";
                case TLS_PSK_WITH_NULL_SHA256 :
                    return "TLS_PSK_WITH_NULL_SHA256";
                case TLS_DHE_PSK_WITH_AES_128_CBC_SHA256 :
                    return "TLS_DHE_PSK_WITH_AES_128_CBC_SHA256";
                case TLS_DHE_PSK_WITH_NULL_SHA256 :
                    return "TLS_DHE_PSK_WITH_NULL_SHA256";
        #ifdef HAVE_AESGCM
                case TLS_PSK_WITH_AES_128_GCM_SHA256 :
                    return "TLS_PSK_WITH_AES_128_GCM_SHA256";
                case TLS_DHE_PSK_WITH_AES_128_GCM_SHA256 :
                    return "TLS_DHE_PSK_WITH_AES_128_GCM_SHA256";
        #endif
    #endif
    #ifdef CYASSL_SHA384
                case TLS_PSK_WITH_AES_256_CBC_SHA384 :
                    return "TLS_PSK_WITH_AES_256_CBC_SHA384";
                case TLS_PSK_WITH_NULL_SHA384 :
                    return "TLS_PSK_WITH_NULL_SHA384";
                case TLS_DHE_PSK_WITH_AES_256_CBC_SHA384 :
                    return "TLS_DHE_PSK_WITH_AES_256_CBC_SHA384";
                case TLS_DHE_PSK_WITH_NULL_SHA384 :
                    return "TLS_DHE_PSK_WITH_NULL_SHA384";
        #ifdef HAVE_AESGCM
                case TLS_PSK_WITH_AES_256_GCM_SHA384 :
                    return "TLS_PSK_WITH_AES_256_GCM_SHA384";
                case TLS_DHE_PSK_WITH_AES_256_GCM_SHA384 :
                    return "TLS_DHE_PSK_WITH_AES_256_GCM_SHA384";
        #endif
    #endif
    #ifndef NO_SHA
                case TLS_PSK_WITH_NULL_SHA :
                    return "TLS_PSK_WITH_NULL_SHA";
    #endif
#endif /* NO_PSK */
#ifndef NO_RSA
                case TLS_DHE_RSA_WITH_AES_128_CBC_SHA256 :
                    return "TLS_DHE_RSA_WITH_AES_128_CBC_SHA256";
                case TLS_DHE_RSA_WITH_AES_256_CBC_SHA256 :
                    return "TLS_DHE_RSA_WITH_AES_256_CBC_SHA256";
    #ifndef NO_SHA
                case TLS_DHE_RSA_WITH_AES_128_CBC_SHA :
                    return "TLS_DHE_RSA_WITH_AES_128_CBC_SHA";
                case TLS_DHE_RSA_WITH_AES_256_CBC_SHA :
                    return "TLS_DHE_RSA_WITH_AES_256_CBC_SHA";
    #endif
    #ifndef NO_HC128
        #ifndef NO_MD5
                case TLS_RSA_WITH_HC_128_MD5 :
                    return "TLS_RSA_WITH_HC_128_MD5";
        #endif
        #ifndef NO_SHA
                case TLS_RSA_WITH_HC_128_SHA :
                    return "TLS_RSA_WITH_HC_128_SHA";
        #endif
        #ifdef HAVE_BLAKE2
                case TLS_RSA_WITH_HC_128_B2B256:
                    return "TLS_RSA_WITH_HC_128_B2B256";
        #endif
    #endif /* NO_HC128 */
    #ifndef NO_SHA
        #ifndef NO_RABBIT
                case TLS_RSA_WITH_RABBIT_SHA :
                    return "TLS_RSA_WITH_RABBIT_SHA";
        #endif
        #ifdef HAVE_NTRU
            #ifndef NO_RC4
                case TLS_NTRU_RSA_WITH_RC4_128_SHA :
                    return "TLS_NTRU_RSA_WITH_RC4_128_SHA";
            #endif
            #ifndef NO_DES3
                case TLS_NTRU_RSA_WITH_3DES_EDE_CBC_SHA :
                    return "TLS_NTRU_RSA_WITH_3DES_EDE_CBC_SHA";
            #endif
                case TLS_NTRU_RSA_WITH_AES_128_CBC_SHA :
                    return "TLS_NTRU_RSA_WITH_AES_128_CBC_SHA";
                case TLS_NTRU_RSA_WITH_AES_256_CBC_SHA :
                    return "TLS_NTRU_RSA_WITH_AES_256_CBC_SHA";
        #endif /* HAVE_NTRU */
    #endif /* NO_SHA */
                case TLS_RSA_WITH_AES_128_GCM_SHA256 :
                    return "TLS_RSA_WITH_AES_128_GCM_SHA256";
                case TLS_RSA_WITH_AES_256_GCM_SHA384 :
                    return "TLS_RSA_WITH_AES_256_GCM_SHA384";
                case TLS_DHE_RSA_WITH_AES_128_GCM_SHA256 :
                    return "TLS_DHE_RSA_WITH_AES_128_GCM_SHA256";
                case TLS_DHE_RSA_WITH_AES_256_GCM_SHA384 :
                    return "TLS_DHE_RSA_WITH_AES_256_GCM_SHA384";
    #ifndef NO_SHA
                case TLS_RSA_WITH_CAMELLIA_128_CBC_SHA :
                    return "TLS_RSA_WITH_CAMELLIA_128_CBC_SHA";
                case TLS_RSA_WITH_CAMELLIA_256_CBC_SHA :
                    return "TLS_RSA_WITH_CAMELLIA_256_CBC_SHA";
    #endif
                case TLS_RSA_WITH_CAMELLIA_128_CBC_SHA256 :
                    return "TLS_RSA_WITH_CAMELLIA_128_CBC_SHA256";
                case TLS_RSA_WITH_CAMELLIA_256_CBC_SHA256 :
                    return "TLS_RSA_WITH_CAMELLIA_256_CBC_SHA256";
    #ifndef NO_SHA
                case TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA :
                    return "TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA";
                case TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA :
                    return "TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA";
    #endif
                case TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA256 :
                    return "TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA256";
                case TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA256 :
                    return "TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA256";
#endif /* NO_RSA */
                default:
                    return "NONE";
            }  /* switch */
            }  /* normal / ECC */
        }
#endif /* NO_ERROR_STRINGS */
        return "NONE";
    }


    const char* CyaSSL_get_cipher(CYASSL* ssl)
    {
        CYASSL_ENTER("CyaSSL_get_cipher");
        return CyaSSL_CIPHER_get_name(CyaSSL_get_current_cipher(ssl));
    }

#ifdef OPENSSL_EXTRA



    char* CyaSSL_CIPHER_description(CYASSL_CIPHER* cipher, char* in, int len)
    {
        (void)cipher;
        (void)in;
        (void)len;
        return 0;
    }


    CYASSL_SESSION* CyaSSL_get1_session(CYASSL* ssl)  /* what's ref count */
    {
        (void)ssl;
        return 0;
    }


    void CyaSSL_X509_free(CYASSL_X509* buf)
    {
        (void)buf;
    }


    /* was do nothing */
    /*
    void OPENSSL_free(void* buf)
    {
        (void)buf;
    }
    */


    int CyaSSL_OCSP_parse_url(char* url, char** host, char** port, char** path,
                       int* ssl)
    {
        (void)url;
        (void)host;
        (void)port;
        (void)path;
        (void)ssl;
        return 0;
    }


    CYASSL_METHOD* CyaSSLv2_client_method(void)
    {
        return 0;
    }


    CYASSL_METHOD* CyaSSLv2_server_method(void)
    {
        return 0;
    }


#ifndef NO_MD4

    void CyaSSL_MD4_Init(CYASSL_MD4_CTX* md4)
    {
        /* make sure we have a big enough buffer */
        typedef char ok[sizeof(md4->buffer) >= sizeof(Md4) ? 1 : -1];
        (void) sizeof(ok);

        CYASSL_ENTER("MD4_Init");
        InitMd4((Md4*)md4);
    }


    void CyaSSL_MD4_Update(CYASSL_MD4_CTX* md4, const void* data,
                           unsigned long len)
    {
        CYASSL_ENTER("MD4_Update");
        Md4Update((Md4*)md4, (const byte*)data, (word32)len);
    }


    void CyaSSL_MD4_Final(unsigned char* digest, CYASSL_MD4_CTX* md4)
    {
        CYASSL_ENTER("MD4_Final");
        Md4Final((Md4*)md4, digest);
    }

#endif /* NO_MD4 */


    CYASSL_BIO* CyaSSL_BIO_pop(CYASSL_BIO* top)
    {
        (void)top;
        return 0;
    }


    int CyaSSL_BIO_pending(CYASSL_BIO* bio)
    {
        (void)bio;
        return 0;
    }



    CYASSL_BIO_METHOD* CyaSSL_BIO_s_mem(void)
    {
        static CYASSL_BIO_METHOD meth;

        CYASSL_ENTER("BIO_s_mem");
        meth.type = BIO_MEMORY;

        return &meth;
    }


    CYASSL_BIO_METHOD* CyaSSL_BIO_f_base64(void)
    {
        return 0;
    }


    void CyaSSL_BIO_set_flags(CYASSL_BIO* bio, int flags)
    {
        (void)bio;
        (void)flags;
    }



    void CyaSSL_RAND_screen(void)
    {

    }


    const char* CyaSSL_RAND_file_name(char* fname, unsigned long len)
    {
        (void)fname;
        (void)len;
        return 0;
    }


    int CyaSSL_RAND_write_file(const char* fname)
    {
        (void)fname;
        return 0;
    }


    int CyaSSL_RAND_load_file(const char* fname, long len)
    {
        (void)fname;
        /* CTaoCrypt provides enough entropy internally or will report error */
        if (len == -1)
            return 1024;
        else
            return (int)len;
    }


    int CyaSSL_RAND_egd(const char* path)
    {
        (void)path;
        return 0;
    }



    CYASSL_COMP_METHOD* CyaSSL_COMP_zlib(void)
    {
        return 0;
    }


    CYASSL_COMP_METHOD* CyaSSL_COMP_rle(void)
    {
        return 0;
    }


    int CyaSSL_COMP_add_compression_method(int method, void* data)
    {
        (void)method;
        (void)data;
        return 0;
    }



    int CyaSSL_get_ex_new_index(long idx, void* data, void* cb1, void* cb2,
                             void* cb3)
    {
        (void)idx;
        (void)data;
        (void)cb1;
        (void)cb2;
        (void)cb3;
        return 0;
    }


    void CyaSSL_set_dynlock_create_callback(CYASSL_dynlock_value* (*f)(
                                                              const char*, int))
    {
        (void)f;
    }


    void CyaSSL_set_dynlock_lock_callback(
                 void (*f)(int, CYASSL_dynlock_value*, const char*, int))
    {
        (void)f;
    }


    void CyaSSL_set_dynlock_destroy_callback(
                      void (*f)(CYASSL_dynlock_value*, const char*, int))
    {
        (void)f;
    }



    const char* CyaSSL_X509_verify_cert_error_string(long err)
    {
        (void)err;
        return 0;
    }



    int CyaSSL_X509_LOOKUP_add_dir(CYASSL_X509_LOOKUP* lookup, const char* dir,
                                   long len)
    {
        (void)lookup;
        (void)dir;
        (void)len;
        return 0;
    }


    int CyaSSL_X509_LOOKUP_load_file(CYASSL_X509_LOOKUP* lookup,
                                     const char* file, long len)
    {
        (void)lookup;
        (void)file;
        (void)len;
        return 0;
    }


    CYASSL_X509_LOOKUP_METHOD* CyaSSL_X509_LOOKUP_hash_dir(void)
    {
        return 0;
    }


    CYASSL_X509_LOOKUP_METHOD* CyaSSL_X509_LOOKUP_file(void)
    {
        return 0;
    }



    CYASSL_X509_LOOKUP* CyaSSL_X509_STORE_add_lookup(CYASSL_X509_STORE* store,
                                                   CYASSL_X509_LOOKUP_METHOD* m)
    {
        (void)store;
        (void)m;
        return 0;
    }


    int CyaSSL_X509_STORE_add_cert(CYASSL_X509_STORE* store, CYASSL_X509* x509)
    {
        int result = SSL_FATAL_ERROR;

        CYASSL_ENTER("CyaSSL_X509_STORE_add_cert");
        if (store != NULL && store->cm != NULL && x509 != NULL) {
            buffer derCert;
            derCert.buffer = (byte*)XMALLOC(x509->derCert.length,
                                                       NULL, DYNAMIC_TYPE_CERT);
            if (derCert.buffer != NULL) {
                derCert.length = x509->derCert.length;
                    /* AddCA() frees the buffer. */
                XMEMCPY(derCert.buffer,
                                    x509->derCert.buffer, x509->derCert.length);
                result = AddCA(store->cm, derCert, CYASSL_USER_CA, 1);
                if (result != SSL_SUCCESS) result = SSL_FATAL_ERROR;
            }
        }

        CYASSL_LEAVE("CyaSSL_X509_STORE_add_cert", result);
        return result;
    }


    CYASSL_X509_STORE* CyaSSL_X509_STORE_new(void)
    {
        CYASSL_X509_STORE* store = NULL;

        store = (CYASSL_X509_STORE*)XMALLOC(sizeof(CYASSL_X509_STORE), NULL, 0);
        if (store != NULL) {
            store->cm = CyaSSL_CertManagerNew();
            if (store->cm == NULL) {
                XFREE(store, NULL, 0);
                store = NULL;
            }
        }

        return store;
    }


    void CyaSSL_X509_STORE_free(CYASSL_X509_STORE* store)
    {
        if (store != NULL) {
            if (store->cm != NULL)
            CyaSSL_CertManagerFree(store->cm);
            XFREE(store, NULL, 0);
        }
    }


    int CyaSSL_X509_STORE_set_default_paths(CYASSL_X509_STORE* store)
    {
        (void)store;
        return SSL_SUCCESS;
    }


    int CyaSSL_X509_STORE_get_by_subject(CYASSL_X509_STORE_CTX* ctx, int idx,
                                CYASSL_X509_NAME* name, CYASSL_X509_OBJECT* obj)
    {
        (void)ctx;
        (void)idx;
        (void)name;
        (void)obj;
        return 0;
    }


    CYASSL_X509_STORE_CTX* CyaSSL_X509_STORE_CTX_new(void)
    {
        CYASSL_X509_STORE_CTX* ctx = (CYASSL_X509_STORE_CTX*)XMALLOC(
                                        sizeof(CYASSL_X509_STORE_CTX), NULL, 0);

        if (ctx != NULL)
            CyaSSL_X509_STORE_CTX_init(ctx, NULL, NULL, NULL);

        return ctx;
    }


    int CyaSSL_X509_STORE_CTX_init(CYASSL_X509_STORE_CTX* ctx,
         CYASSL_X509_STORE* store, CYASSL_X509* x509, STACK_OF(CYASSL_X509)* sk)
    {
        (void)sk;
        if (ctx != NULL) {
            ctx->store = store;
            ctx->current_cert = x509;
            ctx->domain = NULL;
            ctx->ex_data = NULL;
            ctx->userCtx = NULL;
            ctx->error = 0;
            ctx->error_depth = 0;
            ctx->discardSessionCerts = 0;
            return SSL_SUCCESS;
        }
        return SSL_FATAL_ERROR;
    }


    void CyaSSL_X509_STORE_CTX_free(CYASSL_X509_STORE_CTX* ctx)
    {
        if (ctx != NULL) {
            if (ctx->store != NULL)
                CyaSSL_X509_STORE_free(ctx->store);
            if (ctx->current_cert != NULL)
                CyaSSL_FreeX509(ctx->current_cert);
            XFREE(ctx, NULL, 0);
        }
    }


    void CyaSSL_X509_STORE_CTX_cleanup(CYASSL_X509_STORE_CTX* ctx)
    {
        (void)ctx;
    }


    int CyaSSL_X509_verify_cert(CYASSL_X509_STORE_CTX* ctx)
    {
        if (ctx != NULL && ctx->store != NULL && ctx->store->cm != NULL
                                                 && ctx->current_cert != NULL) {
            return CyaSSL_CertManagerVerifyBuffer(ctx->store->cm,
                        ctx->current_cert->derCert.buffer,
                        ctx->current_cert->derCert.length,
                        SSL_FILETYPE_ASN1);
        }
        return SSL_FATAL_ERROR;
    }


    CYASSL_ASN1_TIME* CyaSSL_X509_CRL_get_lastUpdate(CYASSL_X509_CRL* crl)
    {
        (void)crl;
        return 0;
    }


    CYASSL_ASN1_TIME* CyaSSL_X509_CRL_get_nextUpdate(CYASSL_X509_CRL* crl)
    {
        (void)crl;
        return 0;
    }



    CYASSL_EVP_PKEY* CyaSSL_X509_get_pubkey(CYASSL_X509* x509)
    {
        CYASSL_EVP_PKEY* key = NULL;
        if (x509 != NULL) {
            key = (CYASSL_EVP_PKEY*)XMALLOC(
                        sizeof(CYASSL_EVP_PKEY), NULL, DYNAMIC_TYPE_PUBLIC_KEY);
            if (key != NULL) {
                key->type = x509->pubKeyOID;
                key->save_type = 0;
                key->pkey.ptr = (char*)XMALLOC(
                            x509->pubKey.length, NULL, DYNAMIC_TYPE_PUBLIC_KEY);
                if (key->pkey.ptr == NULL) {
                    XFREE(key, NULL, DYNAMIC_TYPE_PUBLIC_KEY);
                    return NULL;
                }
                XMEMCPY(key->pkey.ptr,
                                      x509->pubKey.buffer, x509->pubKey.length);
                key->pkey_sz = x509->pubKey.length;
                #ifdef HAVE_ECC
                    key->pkey_curve = (int)x509->pkCurveOID;
                #endif /* HAVE_ECC */
            }
        }
        return key;
    }


    int CyaSSL_X509_CRL_verify(CYASSL_X509_CRL* crl, CYASSL_EVP_PKEY* key)
    {
        (void)crl;
        (void)key;
        return 0;
    }


    void CyaSSL_X509_STORE_CTX_set_error(CYASSL_X509_STORE_CTX* ctx, int err)
    {
        (void)ctx;
        (void)err;
    }


    void CyaSSL_X509_OBJECT_free_contents(CYASSL_X509_OBJECT* obj)
    {
        (void)obj;
    }


    void CyaSSL_EVP_PKEY_free(CYASSL_EVP_PKEY* key)
    {
        if (key != NULL) {
            if (key->pkey.ptr != NULL)
                XFREE(key->pkey.ptr, NULL, 0);
            XFREE(key, NULL, 0);
        }
    }


    int CyaSSL_X509_cmp_current_time(const CYASSL_ASN1_TIME* asnTime)
    {
        (void)asnTime;
        return 0;
    }


    int CyaSSL_sk_X509_REVOKED_num(CYASSL_X509_REVOKED* revoked)
    {
        (void)revoked;
        return 0;
    }



    CYASSL_X509_REVOKED* CyaSSL_X509_CRL_get_REVOKED(CYASSL_X509_CRL* crl)
    {
        (void)crl;
        return 0;
    }


    CYASSL_X509_REVOKED* CyaSSL_sk_X509_REVOKED_value(
                                        CYASSL_X509_REVOKED* revoked, int value)
    {
        (void)revoked;
        (void)value;
        return 0;
    }



    CYASSL_ASN1_INTEGER* CyaSSL_X509_get_serialNumber(CYASSL_X509* x509)
    {
        (void)x509;
        return 0;
    }


    int CyaSSL_ASN1_TIME_print(CYASSL_BIO* bio, const CYASSL_ASN1_TIME* asnTime)
    {
        (void)bio;
        (void)asnTime;
        return 0;
    }



    int CyaSSL_ASN1_INTEGER_cmp(const CYASSL_ASN1_INTEGER* a,
                                const CYASSL_ASN1_INTEGER* b)
    {
        (void)a;
        (void)b;
        return 0;
    }


    long CyaSSL_ASN1_INTEGER_get(const CYASSL_ASN1_INTEGER* i)
    {
        (void)i;
        return 0;
    }



    void* CyaSSL_X509_STORE_CTX_get_ex_data(CYASSL_X509_STORE_CTX* ctx, int idx)
    {
#ifdef FORTRESS
        if (ctx != NULL && idx == 0)
            return ctx->ex_data;
#else
        (void)ctx;
        (void)idx;
#endif
        return 0;
    }


    int CyaSSL_get_ex_data_X509_STORE_CTX_idx(void)
    {
        return 0;
    }


    void* CyaSSL_get_ex_data(const CYASSL* ssl, int idx)
    {
#ifdef FORTRESS
        if (ssl != NULL && idx < MAX_EX_DATA)
            return ssl->ex_data[idx];
#else
        (void)ssl;
        (void)idx;
#endif
        return 0;
    }


    void CyaSSL_CTX_set_info_callback(CYASSL_CTX* ctx, void (*f)(void))
    {
        (void)ctx;
        (void)f;
    }


    unsigned long CyaSSL_ERR_peek_error(void)
    {
        return 0;
    }


    int CyaSSL_ERR_GET_REASON(int err)
    {
        (void)err;
        return 0;
    }


    char* CyaSSL_alert_type_string_long(int alertID)
    {
        (void)alertID;
        return 0;
    }


    char* CyaSSL_alert_desc_string_long(int alertID)
    {
        (void)alertID;
        return 0;
    }


    char* CyaSSL_state_string_long(CYASSL* ssl)
    {
        (void)ssl;
        return 0;
    }


    int CyaSSL_PEM_def_callback(char* name, int num, int w, void* key)
    {
        (void)name;
        (void)num;
        (void)w;
        (void)key;
        return 0;
    }


    long CyaSSL_CTX_sess_accept(CYASSL_CTX* ctx)
    {
        (void)ctx;
        return 0;
    }


    long CyaSSL_CTX_sess_connect(CYASSL_CTX* ctx)
    {
        (void)ctx;
        return 0;
    }


    long CyaSSL_CTX_sess_accept_good(CYASSL_CTX* ctx)
    {
        (void)ctx;
        return 0;
    }


    long CyaSSL_CTX_sess_connect_good(CYASSL_CTX* ctx)
    {
        (void)ctx;
        return 0;
    }


    long CyaSSL_CTX_sess_accept_renegotiate(CYASSL_CTX* ctx)
    {
        (void)ctx;
        return 0;
    }


    long CyaSSL_CTX_sess_connect_renegotiate(CYASSL_CTX* ctx)
    {
        (void)ctx;
        return 0;
    }


    long CyaSSL_CTX_sess_hits(CYASSL_CTX* ctx)
    {
        (void)ctx;
        return 0;
    }


    long CyaSSL_CTX_sess_cb_hits(CYASSL_CTX* ctx)
    {
        (void)ctx;
        return 0;
    }


    long CyaSSL_CTX_sess_cache_full(CYASSL_CTX* ctx)
    {
        (void)ctx;
        return 0;
    }


    long CyaSSL_CTX_sess_misses(CYASSL_CTX* ctx)
    {
        (void)ctx;
        return 0;
    }


    long CyaSSL_CTX_sess_timeouts(CYASSL_CTX* ctx)
    {
        (void)ctx;
        return 0;
    }


    long CyaSSL_CTX_sess_number(CYASSL_CTX* ctx)
    {
        (void)ctx;
        return 0;
    }


    void CyaSSL_DES_set_key_unchecked(CYASSL_const_DES_cblock* myDes,
                                                   CYASSL_DES_key_schedule* key)
    {
        (void)myDes;
        (void)key;
    }


    void CyaSSL_DES_set_odd_parity(CYASSL_DES_cblock* myDes)
    {
        (void)myDes;
    }


    void CyaSSL_DES_ecb_encrypt(CYASSL_DES_cblock* desa,
                 CYASSL_DES_cblock* desb, CYASSL_DES_key_schedule* key, int len)
    {
        (void)desa;
        (void)desb;
        (void)key;
        (void)len;
    }

    int CyaSSL_BIO_printf(CYASSL_BIO* bio, const char* format, ...)
    {
        (void)bio;
        (void)format;
        return 0;
    }


    int CyaSSL_ASN1_UTCTIME_print(CYASSL_BIO* bio, const CYASSL_ASN1_UTCTIME* a)
    {
        (void)bio;
        (void)a;
        return 0;
    }


    int  CyaSSL_sk_num(CYASSL_X509_REVOKED* rev)
    {
        (void)rev;
        return 0;
    }


    void* CyaSSL_sk_value(CYASSL_X509_REVOKED* rev, int i)
    {
        (void)rev;
        (void)i;
        return 0;
    }


    /* stunnel 4.28 needs */
    void* CyaSSL_CTX_get_ex_data(const CYASSL_CTX* ctx, int d)
    {
        (void)ctx;
        (void)d;
        return 0;
    }


    int CyaSSL_CTX_set_ex_data(CYASSL_CTX* ctx, int d, void* p)
    {
        (void)ctx;
        (void)d;
        (void)p;
        return SSL_SUCCESS;
    }


    void CyaSSL_CTX_sess_set_get_cb(CYASSL_CTX* ctx,
                        CYASSL_SESSION*(*f)(CYASSL*, unsigned char*, int, int*))
    {
        (void)ctx;
        (void)f;
    }


    void CyaSSL_CTX_sess_set_new_cb(CYASSL_CTX* ctx,
                                 int (*f)(CYASSL*, CYASSL_SESSION*))
    {
        (void)ctx;
        (void)f;
    }


    void CyaSSL_CTX_sess_set_remove_cb(CYASSL_CTX* ctx, void (*f)(CYASSL_CTX*,
                                                            CYASSL_SESSION*))
    {
        (void)ctx;
        (void)f;
    }


    int CyaSSL_i2d_SSL_SESSION(CYASSL_SESSION* sess, unsigned char** p)
    {
        (void)sess;
        (void)p;
        return sizeof(CYASSL_SESSION);
    }


    CYASSL_SESSION* CyaSSL_d2i_SSL_SESSION(CYASSL_SESSION** sess,
                                    const unsigned char** p, long i)
    {
        (void)p;
        (void)i;
        if (sess)
            return *sess;
        return NULL;
    }


    long CyaSSL_SESSION_get_timeout(const CYASSL_SESSION* sess)
    {
        CYASSL_ENTER("CyaSSL_SESSION_get_timeout");
        return sess->timeout;
    }


    long CyaSSL_SESSION_get_time(const CYASSL_SESSION* sess)
    {
        CYASSL_ENTER("CyaSSL_SESSION_get_time");
        return sess->bornOn;
    }


    int CyaSSL_CTX_get_ex_new_index(long idx, void* arg, void* a, void* b,
                                    void* c)
    {
        (void)idx;
        (void)arg;
        (void)a;
        (void)b;
        (void)c;
        return 0;
    }

#endif /* OPENSSL_EXTRA */


#ifdef KEEP_PEER_CERT
    char*  CyaSSL_X509_get_subjectCN(CYASSL_X509* x509)
    {
        if (x509 == NULL)
            return NULL;

        return x509->subjectCN;
    }
#endif /* KEEP_PEER_CERT */

#ifdef OPENSSL_EXTRA

#ifdef FORTRESS
    int CyaSSL_cmp_peer_cert_to_file(CYASSL* ssl, const char *fname)
    {
        int ret = SSL_FATAL_ERROR;

        CYASSL_ENTER("CyaSSL_cmp_peer_cert_to_file");
        if (ssl != NULL && fname != NULL)
        {
            XFILE         file = XBADFILE;
            long          sz = 0;
            byte          staticBuffer[FILE_BUFFER_SIZE];
            byte*         myBuffer = staticBuffer;
            CYASSL_CTX*   ctx = ssl->ctx;
            EncryptedInfo info;
            buffer        fileDer;
            int           eccKey = 0;
            CYASSL_X509*  peer_cert = &ssl->peerCert;

            info.set = 0;
            info.ctx = ctx;
            info.consumed = 0;
            fileDer.buffer = 0;

            file = XFOPEN(fname, "rb");
            if (file == XBADFILE) return SSL_BAD_FILE;
            XFSEEK(file, 0, XSEEK_END);
            sz = XFTELL(file);
            XREWIND(file);
            if (sz > (long)sizeof(staticBuffer)) {
                CYASSL_MSG("Getting dynamic buffer");
                myBuffer = (byte*) XMALLOC(sz, ctx->heap, DYNAMIC_TYPE_FILE);
            }

            if ((myBuffer != NULL) &&
                (sz > 0) &&
                (XFREAD(myBuffer, sz, 1, file) > 0) &&
                (PemToDer(myBuffer, sz, CERT_TYPE,
                                &fileDer, ctx->heap, &info, &eccKey) == 0) &&
                (fileDer.length != 0) &&
                (fileDer.length == peer_cert->derCert.length) &&
                (XMEMCMP(peer_cert->derCert.buffer, fileDer.buffer,
                                                    fileDer.length) == 0))
            {
                ret = 0;
            }

            XFCLOSE(file);
            if (fileDer.buffer)
                XFREE(fileDer.buffer, ctx->heap, DYNAMIC_TYPE_CERT);
            if (myBuffer && (myBuffer != staticBuffer))
                XFREE(myBuffer, ctx->heap, DYNAMIC_TYPE_FILE);
        }

        return ret;
    }
#endif


static RNG globalRNG;
static int initGlobalRNG = 0;

    /* SSL_SUCCESS on ok */
    int CyaSSL_RAND_seed(const void* seed, int len)
    {

        CYASSL_MSG("CyaSSL_RAND_seed");

        (void)seed;
        (void)len;

        if (initGlobalRNG == 0) {
            if (InitRng(&globalRNG) < 0) {
                CYASSL_MSG("CyaSSL Init Global RNG failed");
                return 0;
            }
            initGlobalRNG = 1;
        }

        return SSL_SUCCESS;
    }


    /* SSL_SUCCESS on ok */
    int CyaSSL_RAND_bytes(unsigned char* buf, int num)
    {
        RNG    tmpRNG;
        RNG*   rng = &tmpRNG;

        CYASSL_ENTER("RAND_bytes");
        if (InitRng(&tmpRNG) != 0) {
            CYASSL_MSG("Bad RNG Init, trying global");
            if (initGlobalRNG == 0) {
                CYASSL_MSG("Global RNG no Init");
                return 0;
            }
            rng = &globalRNG;
        }

        if (RNG_GenerateBlock(rng, buf, num) != 0) {
            CYASSL_MSG("Bad RNG_GenerateBlock");
            return 0;
        }

        return SSL_SUCCESS;
    }

    CYASSL_BN_CTX* CyaSSL_BN_CTX_new(void)
    {
        static int ctx;  /* ctaocrypt doesn't now need ctx */

        CYASSL_MSG("CyaSSL_BN_CTX_new");

        return (CYASSL_BN_CTX*)&ctx;
    }

    void CyaSSL_BN_CTX_init(CYASSL_BN_CTX* ctx)
    {
        (void)ctx;
        CYASSL_MSG("CyaSSL_BN_CTX_init");
    }


    void CyaSSL_BN_CTX_free(CYASSL_BN_CTX* ctx)
    {
        (void)ctx;
        CYASSL_MSG("CyaSSL_BN_CTX_free");

        /* do free since static ctx that does nothing */
    }


    static void InitCyaSSL_BigNum(CYASSL_BIGNUM* bn)
    {
        CYASSL_MSG("InitCyaSSL_BigNum");
        if (bn) {
            bn->neg      = 0;
            bn->internal = NULL;
        }
    }


    CYASSL_BIGNUM* CyaSSL_BN_new(void)
    {
        CYASSL_BIGNUM* external;
        mp_int*        mpi;

        CYASSL_MSG("CyaSSL_BN_new");

        mpi = (mp_int*) XMALLOC(sizeof(mp_int), NULL, DYNAMIC_TYPE_BIGINT);
        if (mpi == NULL) {
            CYASSL_MSG("CyaSSL_BN_new malloc mpi failure");
            return NULL;
        }

        external = (CYASSL_BIGNUM*) XMALLOC(sizeof(CYASSL_BIGNUM), NULL,
                                            DYNAMIC_TYPE_BIGINT);
        if (external == NULL) {
            CYASSL_MSG("CyaSSL_BN_new malloc CYASSL_BIGNUM failure");
            XFREE(mpi, NULL, DYNAMIC_TYPE_BIGINT);
            return NULL;
        }

        InitCyaSSL_BigNum(external);
        external->internal = mpi;
        if (mp_init(mpi) != MP_OKAY) {
            CyaSSL_BN_free(external);
            return NULL;
        }

        return external;
    }


    void CyaSSL_BN_free(CYASSL_BIGNUM* bn)
    {
        CYASSL_MSG("CyaSSL_BN_free");
        if (bn) {
            if (bn->internal) {
                mp_clear((mp_int*)bn->internal);
                XFREE(bn->internal, NULL, DYNAMIC_TYPE_BIGINT);
                bn->internal = NULL;
            }
            XFREE(bn, NULL, DYNAMIC_TYPE_BIGINT);
        }
    }


    void CyaSSL_BN_clear_free(CYASSL_BIGNUM* bn)
    {
        CYASSL_MSG("CyaSSL_BN_clear_free");

        CyaSSL_BN_free(bn);
    }


    /* SSL_SUCCESS on ok */
    int CyaSSL_BN_sub(CYASSL_BIGNUM* r, const CYASSL_BIGNUM* a,
                      const CYASSL_BIGNUM* b)
    {
        CYASSL_MSG("CyaSSL_BN_sub");

        if (r == NULL || a == NULL || b == NULL)
            return 0;

        if (mp_sub((mp_int*)a->internal,(mp_int*)b->internal,
                   (mp_int*)r->internal) == MP_OKAY)
            return SSL_SUCCESS;

        CYASSL_MSG("CyaSSL_BN_sub mp_sub failed");
        return 0;
    }


    /* SSL_SUCCESS on ok */
    int CyaSSL_BN_mod(CYASSL_BIGNUM* r, const CYASSL_BIGNUM* a,
	                  const CYASSL_BIGNUM* b, const CYASSL_BN_CTX* c)
    {
        (void)c;
        CYASSL_MSG("CyaSSL_BN_mod");

        if (r == NULL || a == NULL || b == NULL)
            return 0;

        if (mp_mod((mp_int*)a->internal,(mp_int*)b->internal,
                   (mp_int*)r->internal) == MP_OKAY)
            return SSL_SUCCESS;

        CYASSL_MSG("CyaSSL_BN_mod mp_mod failed");
        return 0;
    }


    const CYASSL_BIGNUM* CyaSSL_BN_value_one(void)
    {
        static CYASSL_BIGNUM* bn_one = NULL;

        CYASSL_MSG("CyaSSL_BN_value_one");

        if (bn_one == NULL) {
            bn_one = CyaSSL_BN_new();
            if (bn_one)
                mp_set_int((mp_int*)bn_one->internal, 1);
        }

        return bn_one;
    }


    int CyaSSL_BN_num_bytes(const CYASSL_BIGNUM* bn)
    {
        CYASSL_MSG("CyaSSL_BN_num_bytes");

        if (bn == NULL || bn->internal == NULL)
            return 0;

        return mp_unsigned_bin_size((mp_int*)bn->internal);
    }


    int CyaSSL_BN_num_bits(const CYASSL_BIGNUM* bn)
    {
        CYASSL_MSG("CyaSSL_BN_num_bits");

        if (bn == NULL || bn->internal == NULL)
            return 0;

        return mp_count_bits((mp_int*)bn->internal);
    }


    int CyaSSL_BN_is_zero(const CYASSL_BIGNUM* bn)
    {
        CYASSL_MSG("CyaSSL_BN_is_zero");

        if (bn == NULL || bn->internal == NULL)
            return 0;

        return mp_iszero((mp_int*)bn->internal);
    }


    int CyaSSL_BN_is_one(const CYASSL_BIGNUM* bn)
    {
        CYASSL_MSG("CyaSSL_BN_is_one");

        if (bn == NULL || bn->internal == NULL)
            return 0;

        if (mp_cmp_d((mp_int*)bn->internal, 1) == 0)
            return 1;

        return 0;
    }


    int CyaSSL_BN_is_odd(const CYASSL_BIGNUM* bn)
    {
        CYASSL_MSG("CyaSSL_BN_is_odd");

        if (bn == NULL || bn->internal == NULL)
            return 0;

        return mp_isodd((mp_int*)bn->internal);
    }


    int CyaSSL_BN_cmp(const CYASSL_BIGNUM* a, const CYASSL_BIGNUM* b)
    {
        CYASSL_MSG("CyaSSL_BN_cmp");

        if (a == NULL || a->internal == NULL || b == NULL || b->internal ==NULL)
            return 0;

        return mp_cmp((mp_int*)a->internal, (mp_int*)b->internal);
    }


    int CyaSSL_BN_bn2bin(const CYASSL_BIGNUM* bn, unsigned char* r)
    {
        CYASSL_MSG("CyaSSL_BN_bn2bin");

        if (bn == NULL || bn->internal == NULL) {
            CYASSL_MSG("NULL bn error");
            return SSL_FATAL_ERROR;
        }

        if (r == NULL)
            return mp_unsigned_bin_size((mp_int*)bn->internal);

        if (mp_to_unsigned_bin((mp_int*)bn->internal, r) != MP_OKAY) {
            CYASSL_MSG("mp_to_unsigned_bin error");
            return SSL_FATAL_ERROR;
        }

        return mp_unsigned_bin_size((mp_int*)bn->internal);
    }


    CYASSL_BIGNUM* CyaSSL_BN_bin2bn(const unsigned char* str, int len,
	                            CYASSL_BIGNUM* ret)
    {
        CYASSL_MSG("CyaSSL_BN_bin2bn");

        if (ret && ret->internal) {
            if (mp_read_unsigned_bin((mp_int*)ret->internal, str, len) != 0) {
                CYASSL_MSG("mp_read_unsigned_bin failure");
                return NULL;
            }
        }
        else {
            CYASSL_MSG("CyaSSL_BN_bin2bn wants return bignum");
        }

        return ret;
    }


    int CyaSSL_mask_bits(CYASSL_BIGNUM* bn, int n)
    {
        (void)bn;
        (void)n;
        CYASSL_MSG("CyaSSL_BN_mask_bits");

        return SSL_FATAL_ERROR;
    }


    /* SSL_SUCCESS on ok */
    int CyaSSL_BN_rand(CYASSL_BIGNUM* bn, int bits, int top, int bottom)
    {
        byte          buff[1024];
        RNG           tmpRNG;
        RNG*          rng = &tmpRNG;
        int           len = bits/8;

        (void)top;
        (void)bottom;
        CYASSL_MSG("CyaSSL_BN_rand");

        if (bn == NULL || bn->internal == NULL) {
            CYASSL_MSG("Bad function arguments");
            return 0;
        }

        if (bits % 8)
            len++;

        if ( (InitRng(&tmpRNG)) != 0) {
            CYASSL_MSG("Bad RNG Init, trying global");
            if (initGlobalRNG == 0) {
                CYASSL_MSG("Global RNG no Init");
                return 0;
            }
            rng = &globalRNG;
        }

        if (RNG_GenerateBlock(rng, buff, len) != 0) {
            CYASSL_MSG("Bad RNG_GenerateBlock");
            return 0;
        }

        buff[0]     |= 0x80 | 0x40;
        buff[len-1] |= 0x01;

        if (mp_read_unsigned_bin((mp_int*)bn->internal,buff,len) != MP_OKAY) {
            CYASSL_MSG("mp read bin failed");
            return 0;
        }

        return SSL_SUCCESS;
    }


    int CyaSSL_BN_is_bit_set(const CYASSL_BIGNUM* bn, int n)
    {
        (void)bn;
        (void)n;

        CYASSL_MSG("CyaSSL_BN_is_bit_set");

        return 0;
    }


    /* SSL_SUCCESS on ok */
    int CyaSSL_BN_hex2bn(CYASSL_BIGNUM** bn, const char* str)
    {
        byte    decoded[1024];
        word32  decSz = sizeof(decoded);

        CYASSL_MSG("CyaSSL_BN_hex2bn");

        if (str == NULL) {
            CYASSL_MSG("Bad function argument");
            return 0;
        }

        if (Base16_Decode((byte*)str, (int)XSTRLEN(str), decoded, &decSz) < 0) {
            CYASSL_MSG("Bad Base16_Decode error");
            return 0;
        }

        if (bn == NULL)
            return decSz;

        if (*bn == NULL) {
            *bn = CyaSSL_BN_new();
            if (*bn == NULL) {
                CYASSL_MSG("BN new failed");
                return 0;
            }
        }

        if (CyaSSL_BN_bin2bn(decoded, decSz, *bn) == NULL) {
            CYASSL_MSG("Bad bin2bn error");
            return 0;
        }

        return SSL_SUCCESS;
    }


    CYASSL_BIGNUM* CyaSSL_BN_dup(const CYASSL_BIGNUM* bn)
    {
        CYASSL_BIGNUM* ret;

        CYASSL_MSG("CyaSSL_BN_dup");

        if (bn == NULL || bn->internal == NULL) {
            CYASSL_MSG("bn NULL error");
            return NULL;
        }

        ret = CyaSSL_BN_new();
        if (ret == NULL) {
            CYASSL_MSG("bn new error");
            return NULL;
        }

        if (mp_copy((mp_int*)bn->internal, (mp_int*)ret->internal) != MP_OKAY) {
            CYASSL_MSG("mp_copy error");
            CyaSSL_BN_free(ret);
            return NULL;
        }

        return ret;
    }


    CYASSL_BIGNUM* CyaSSL_BN_copy(CYASSL_BIGNUM* r, const CYASSL_BIGNUM* bn)
    {
        (void)r;
        (void)bn;

        CYASSL_MSG("CyaSSL_BN_copy");

        return NULL;
    }


    int CyaSSL_BN_set_word(CYASSL_BIGNUM* bn, unsigned long w)
    {
        (void)bn;
        (void)w;

        CYASSL_MSG("CyaSSL_BN_set_word");

        return SSL_FATAL_ERROR;
    }


    int CyaSSL_BN_dec2bn(CYASSL_BIGNUM** bn, const char* str)
    {
        (void)bn;
        (void)str;

        CYASSL_MSG("CyaSSL_BN_dec2bn");

        return SSL_FATAL_ERROR;
    }


    char* CyaSSL_BN_bn2dec(const CYASSL_BIGNUM* bn)
    {
        (void)bn;

        CYASSL_MSG("CyaSSL_BN_bn2dec");

        return NULL;
    }


    #ifndef NO_DH

    static void InitCyaSSL_DH(CYASSL_DH* dh)
    {
        if (dh) {
            dh->p        = NULL;
            dh->g        = NULL;
            dh->pub_key  = NULL;
            dh->priv_key = NULL;
            dh->internal = NULL;
            dh->inSet    = 0;
            dh->exSet    = 0;
        }
    }


    CYASSL_DH* CyaSSL_DH_new(void)
    {
        CYASSL_DH* external;
        DhKey*     key;

        CYASSL_MSG("CyaSSL_DH_new");

        key = (DhKey*) XMALLOC(sizeof(DhKey), NULL, DYNAMIC_TYPE_DH);
        if (key == NULL) {
            CYASSL_MSG("CyaSSL_DH_new malloc DhKey failure");
            return NULL;
        }

        external = (CYASSL_DH*) XMALLOC(sizeof(CYASSL_DH), NULL,
                                        DYNAMIC_TYPE_DH);
        if (external == NULL) {
            CYASSL_MSG("CyaSSL_DH_new malloc CYASSL_DH failure");
            XFREE(key, NULL, DYNAMIC_TYPE_DH);
            return NULL;
        }

        InitCyaSSL_DH(external);
        InitDhKey(key);
        external->internal = key;

        return external;
    }


    void CyaSSL_DH_free(CYASSL_DH* dh)
    {
        CYASSL_MSG("CyaSSL_DH_free");

        if (dh) {
            if (dh->internal) {
                FreeDhKey((DhKey*)dh->internal);
                XFREE(dh->internal, NULL, DYNAMIC_TYPE_DH);
                dh->internal = NULL;
            }
            CyaSSL_BN_free(dh->priv_key);
            CyaSSL_BN_free(dh->pub_key);
            CyaSSL_BN_free(dh->g);
            CyaSSL_BN_free(dh->p);
            InitCyaSSL_DH(dh);  /* set back to NULLs for safety */

            XFREE(dh, NULL, DYNAMIC_TYPE_DH);
        }
    }


    static int SetDhInternal(CYASSL_DH* dh)
    {
        unsigned char p[1024];
        unsigned char g[1024];
        int           pSz = sizeof(p);
        int           gSz = sizeof(g);

        CYASSL_ENTER("SetDhInternal");

        if (dh == NULL || dh->p == NULL || dh->g == NULL) {
            CYASSL_MSG("Bad function arguments");
            return SSL_FATAL_ERROR;
        }

        if (CyaSSL_BN_bn2bin(dh->p, NULL) > pSz) {
            CYASSL_MSG("Bad p internal size");
            return SSL_FATAL_ERROR;
        }

        if (CyaSSL_BN_bn2bin(dh->g, NULL) > gSz) {
            CYASSL_MSG("Bad g internal size");
            return SSL_FATAL_ERROR;
        }

        pSz = CyaSSL_BN_bn2bin(dh->p, p);
        gSz = CyaSSL_BN_bn2bin(dh->g, g);

        if (pSz <= 0 || gSz <= 0) {
            CYASSL_MSG("Bad BN2bin set");
            return SSL_FATAL_ERROR;
        }

        if (DhSetKey((DhKey*)dh->internal, p, pSz, g, gSz) < 0) {
            CYASSL_MSG("Bad DH SetKey");
            return SSL_FATAL_ERROR;
        }

        dh->inSet = 1;

        return 0;
    }


    int CyaSSL_DH_size(CYASSL_DH* dh)
    {
        CYASSL_MSG("CyaSSL_DH_size");

        if (dh == NULL)
            return 0;

        return CyaSSL_BN_num_bytes(dh->p);
    }


    /* return SSL_SUCCESS on ok, else 0 */
    int CyaSSL_DH_generate_key(CYASSL_DH* dh)
    {
        unsigned char pub [768];
        unsigned char priv[768];
        word32        pubSz  = sizeof(pub);
        word32        privSz = sizeof(priv);
        RNG           tmpRNG;
        RNG*          rng = &tmpRNG;

        CYASSL_MSG("CyaSSL_DH_generate_key");

        if (dh == NULL || dh->p == NULL || dh->g == NULL) {
            CYASSL_MSG("Bad function arguments");
            return 0;
        }

        if (dh->inSet == 0) {
            if (SetDhInternal(dh) < 0) {
                CYASSL_MSG("Bad DH set internal");
                return 0;
            }
        }

        if ( (InitRng(&tmpRNG)) != 0) {
            CYASSL_MSG("Bad RNG Init, trying global");
            if (initGlobalRNG == 0) {
                CYASSL_MSG("Global RNG no Init");
                return 0;
            }
            rng = &globalRNG;
        }

        if (DhGenerateKeyPair((DhKey*)dh->internal, rng, priv, &privSz,
                                pub, &pubSz) < 0) {
            CYASSL_MSG("Bad DhGenerateKeyPair");
            return 0;
        }

        if (dh->pub_key)
            CyaSSL_BN_free(dh->pub_key);
        dh->pub_key = CyaSSL_BN_new();
        if (dh->pub_key == NULL) {
            CYASSL_MSG("Bad DH new pub");
            return 0;
        }

        if (dh->priv_key)
            CyaSSL_BN_free(dh->priv_key);
        dh->priv_key = CyaSSL_BN_new();
        if (dh->priv_key == NULL) {
            CYASSL_MSG("Bad DH new priv");
            return 0;
        }

        if (CyaSSL_BN_bin2bn(pub, pubSz, dh->pub_key) == NULL) {
            CYASSL_MSG("Bad DH bn2bin error pub");
            return 0;
        }

        if (CyaSSL_BN_bin2bn(priv, privSz, dh->priv_key) == NULL) {
            CYASSL_MSG("Bad DH bn2bin error priv");
            return 0;
        }

        CYASSL_MSG("CyaSSL_generate_key success");
        return SSL_SUCCESS;
    }


    /* return key size on ok, 0 otherwise */
    int CyaSSL_DH_compute_key(unsigned char* key, CYASSL_BIGNUM* otherPub,
                              CYASSL_DH* dh)
    {
        unsigned char pub [1024];
        unsigned char priv[1024];
        word32        pubSz  = sizeof(pub);
        word32        privSz = sizeof(priv);
        word32        keySz;

        CYASSL_MSG("CyaSSL_DH_compute_key");

        if (dh == NULL || dh->priv_key == NULL || otherPub == NULL) {
            CYASSL_MSG("Bad function arguments");
            return 0;
        }

        keySz = (word32)DH_size(dh);
        if (keySz == 0) {
            CYASSL_MSG("Bad DH_size");
            return 0;
        }

        if (CyaSSL_BN_bn2bin(dh->priv_key, NULL) > (int)privSz) {
            CYASSL_MSG("Bad priv internal size");
            return 0;
        }

        if (CyaSSL_BN_bn2bin(otherPub, NULL) > (int)pubSz) {
            CYASSL_MSG("Bad otherPub size");
            return 0;
        }

        privSz = CyaSSL_BN_bn2bin(dh->priv_key, priv);
        pubSz  = CyaSSL_BN_bn2bin(otherPub, pub);

        if (privSz <= 0 || pubSz <= 0) {
            CYASSL_MSG("Bad BN2bin set");
            return 0;
        }

        if (DhAgree((DhKey*)dh->internal, key, &keySz, priv, privSz, pub,
                    pubSz) < 0) {
            CYASSL_MSG("DhAgree failed");
            return 0;
        }

        CYASSL_MSG("CyaSSL_compute_key success");
        return (int)keySz;
    }
    #endif /* NO_DH */


#ifndef NO_DSA
    static void InitCyaSSL_DSA(CYASSL_DSA* dsa)
    {
        if (dsa) {
            dsa->p        = NULL;
            dsa->q        = NULL;
            dsa->g        = NULL;
            dsa->pub_key  = NULL;
            dsa->priv_key = NULL;
            dsa->internal = NULL;
            dsa->inSet    = 0;
            dsa->exSet    = 0;
        }
    }


    CYASSL_DSA* CyaSSL_DSA_new(void)
    {
        CYASSL_DSA* external;
        DsaKey*     key;

        CYASSL_MSG("CyaSSL_DSA_new");

        key = (DsaKey*) XMALLOC(sizeof(DsaKey), NULL, DYNAMIC_TYPE_DSA);
        if (key == NULL) {
            CYASSL_MSG("CyaSSL_DSA_new malloc DsaKey failure");
            return NULL;
        }

        external = (CYASSL_DSA*) XMALLOC(sizeof(CYASSL_DSA), NULL,
                                        DYNAMIC_TYPE_DSA);
        if (external == NULL) {
            CYASSL_MSG("CyaSSL_DSA_new malloc CYASSL_DSA failure");
            XFREE(key, NULL, DYNAMIC_TYPE_DSA);
            return NULL;
        }

        InitCyaSSL_DSA(external);
        InitDsaKey(key);
        external->internal = key;

        return external;
    }


    void CyaSSL_DSA_free(CYASSL_DSA* dsa)
    {
        CYASSL_MSG("CyaSSL_DSA_free");

        if (dsa) {
            if (dsa->internal) {
                FreeDsaKey((DsaKey*)dsa->internal);
                XFREE(dsa->internal, NULL, DYNAMIC_TYPE_DSA);
                dsa->internal = NULL;
            }
            CyaSSL_BN_free(dsa->priv_key);
            CyaSSL_BN_free(dsa->pub_key);
            CyaSSL_BN_free(dsa->g);
            CyaSSL_BN_free(dsa->q);
            CyaSSL_BN_free(dsa->p);
            InitCyaSSL_DSA(dsa);  /* set back to NULLs for safety */

            XFREE(dsa, NULL, DYNAMIC_TYPE_DSA);
        }
    }


    int CyaSSL_DSA_generate_key(CYASSL_DSA* dsa)
    {
        (void)dsa;

        CYASSL_MSG("CyaSSL_DSA_generate_key");

        return 0;  /* key gen not needed by server */
    }


    int CyaSSL_DSA_generate_parameters_ex(CYASSL_DSA* dsa, int bits,
                   unsigned char* seed, int seedLen, int* counterRet,
                   unsigned long* hRet, void* cb)
    {
        (void)dsa;
        (void)bits;
        (void)seed;
        (void)seedLen;
        (void)counterRet;
        (void)hRet;
        (void)cb;

        CYASSL_MSG("CyaSSL_DSA_generate_parameters_ex");

        return 0;  /* key gen not needed by server */
    }
#endif /* NO_DSA */

#ifndef NO_RSA
    static void InitCyaSSL_Rsa(CYASSL_RSA* rsa)
    {
        if (rsa) {
            rsa->n        = NULL;
            rsa->e        = NULL;
            rsa->d        = NULL;
            rsa->p        = NULL;
            rsa->q        = NULL;
	        rsa->dmp1     = NULL;
	        rsa->dmq1     = NULL;
	        rsa->iqmp     = NULL;
            rsa->internal = NULL;
            rsa->inSet    = 0;
            rsa->exSet    = 0;
        }
    }


    CYASSL_RSA* CyaSSL_RSA_new(void)
    {
        CYASSL_RSA* external;
        RsaKey*     key;

        CYASSL_MSG("CyaSSL_RSA_new");

        key = (RsaKey*) XMALLOC(sizeof(RsaKey), NULL, DYNAMIC_TYPE_RSA);
        if (key == NULL) {
            CYASSL_MSG("CyaSSL_RSA_new malloc RsaKey failure");
            return NULL;
        }

        external = (CYASSL_RSA*) XMALLOC(sizeof(CYASSL_RSA), NULL,
                                         DYNAMIC_TYPE_RSA);
        if (external == NULL) {
            CYASSL_MSG("CyaSSL_RSA_new malloc CYASSL_RSA failure");
            XFREE(key, NULL, DYNAMIC_TYPE_RSA);
            return NULL;
        }

        InitCyaSSL_Rsa(external);
        if (InitRsaKey(key, NULL) != 0) {
            CYASSL_MSG("InitRsaKey CYASSL_RSA failure");
            XFREE(external, NULL, DYNAMIC_TYPE_RSA);
            XFREE(key, NULL, DYNAMIC_TYPE_RSA);
            return NULL;
        }
        external->internal = key;

        return external;
    }


    void CyaSSL_RSA_free(CYASSL_RSA* rsa)
    {
        CYASSL_MSG("CyaSSL_RSA_free");

        if (rsa) {
            if (rsa->internal) {
                FreeRsaKey((RsaKey*)rsa->internal);
                XFREE(rsa->internal, NULL, DYNAMIC_TYPE_RSA);
                rsa->internal = NULL;
            }
            CyaSSL_BN_free(rsa->iqmp);
            CyaSSL_BN_free(rsa->dmq1);
            CyaSSL_BN_free(rsa->dmp1);
            CyaSSL_BN_free(rsa->q);
            CyaSSL_BN_free(rsa->p);
            CyaSSL_BN_free(rsa->d);
            CyaSSL_BN_free(rsa->e);
            CyaSSL_BN_free(rsa->n);
            InitCyaSSL_Rsa(rsa);  /* set back to NULLs for safety */

            XFREE(rsa, NULL, DYNAMIC_TYPE_RSA);
        }
    }
#endif /* NO_RSA */


#if !defined(NO_RSA) || !defined(NO_DSA)
    static int SetIndividualExternal(CYASSL_BIGNUM** bn, mp_int* mpi)
    {
        CYASSL_MSG("Entering SetIndividualExternal");

        if (mpi == NULL) {
            CYASSL_MSG("mpi NULL error");
            return SSL_FATAL_ERROR;
        }

        if (*bn == NULL) {
            *bn = CyaSSL_BN_new();
            if (*bn == NULL) {
                CYASSL_MSG("SetIndividualExternal alloc failed");
                return SSL_FATAL_ERROR;
            }
        }

        if (mp_copy(mpi, (mp_int*)((*bn)->internal)) != MP_OKAY) {
            CYASSL_MSG("mp_copy error");
            return SSL_FATAL_ERROR;
        }

        return 0;
    }
#endif /* !NO_RSA && !NO_DSA */


#ifndef NO_DSA
    static int SetDsaExternal(CYASSL_DSA* dsa)
    {
        DsaKey* key;
        CYASSL_MSG("Entering SetDsaExternal");

        if (dsa == NULL || dsa->internal == NULL) {
            CYASSL_MSG("dsa key NULL error");
            return SSL_FATAL_ERROR;
        }

        key = (DsaKey*)dsa->internal;

        if (SetIndividualExternal(&dsa->p, &key->p) < 0) {
            CYASSL_MSG("dsa p key error");
            return SSL_FATAL_ERROR;
        }

        if (SetIndividualExternal(&dsa->q, &key->q) < 0) {
            CYASSL_MSG("dsa q key error");
            return SSL_FATAL_ERROR;
        }

        if (SetIndividualExternal(&dsa->g, &key->g) < 0) {
            CYASSL_MSG("dsa g key error");
            return SSL_FATAL_ERROR;
        }

        if (SetIndividualExternal(&dsa->pub_key, &key->y) < 0) {
            CYASSL_MSG("dsa y key error");
            return SSL_FATAL_ERROR;
        }

        if (SetIndividualExternal(&dsa->priv_key, &key->x) < 0) {
            CYASSL_MSG("dsa x key error");
            return SSL_FATAL_ERROR;
        }

        dsa->exSet = 1;

        return 0;
    }
#endif /* NO_DSA */


#ifndef NO_RSA
    static int SetRsaExternal(CYASSL_RSA* rsa)
    {
        RsaKey* key;
        CYASSL_MSG("Entering SetRsaExternal");

        if (rsa == NULL || rsa->internal == NULL) {
            CYASSL_MSG("rsa key NULL error");
            return SSL_FATAL_ERROR;
        }

        key = (RsaKey*)rsa->internal;

        if (SetIndividualExternal(&rsa->n, &key->n) < 0) {
            CYASSL_MSG("rsa n key error");
            return SSL_FATAL_ERROR;
        }

        if (SetIndividualExternal(&rsa->e, &key->e) < 0) {
            CYASSL_MSG("rsa e key error");
            return SSL_FATAL_ERROR;
        }

        if (SetIndividualExternal(&rsa->d, &key->d) < 0) {
            CYASSL_MSG("rsa d key error");
            return SSL_FATAL_ERROR;
        }

        if (SetIndividualExternal(&rsa->p, &key->p) < 0) {
            CYASSL_MSG("rsa p key error");
            return SSL_FATAL_ERROR;
        }

        if (SetIndividualExternal(&rsa->q, &key->q) < 0) {
            CYASSL_MSG("rsa q key error");
            return SSL_FATAL_ERROR;
        }

        if (SetIndividualExternal(&rsa->dmp1, &key->dP) < 0) {
            CYASSL_MSG("rsa dP key error");
            return SSL_FATAL_ERROR;
        }

        if (SetIndividualExternal(&rsa->dmq1, &key->dQ) < 0) {
            CYASSL_MSG("rsa dQ key error");
            return SSL_FATAL_ERROR;
        }

        if (SetIndividualExternal(&rsa->iqmp, &key->u) < 0) {
            CYASSL_MSG("rsa u key error");
            return SSL_FATAL_ERROR;
        }

        rsa->exSet = 1;

        return 0;
    }


    /* SSL_SUCCESS on ok */
    int CyaSSL_RSA_generate_key_ex(CYASSL_RSA* rsa, int bits, CYASSL_BIGNUM* bn,
                                   void* cb)
    {
        RNG rng;

        CYASSL_MSG("CyaSSL_RSA_generate_key_ex");

        (void)rsa;
        (void)bits;
        (void)cb;
        (void)bn;

        if (InitRng(&rng) < 0) {
            CYASSL_MSG("RNG init failed");
            return SSL_FATAL_ERROR;
        }

#ifdef CYASSL_KEY_GEN
        if (MakeRsaKey((RsaKey*)rsa->internal, bits, 65537, &rng) < 0) {
            CYASSL_MSG("MakeRsaKey failed");
            return SSL_FATAL_ERROR;
        }

        if (SetRsaExternal(rsa) < 0) {
            CYASSL_MSG("SetRsaExternal failed");
            return SSL_FATAL_ERROR;
        }

        rsa->inSet = 1;

        return SSL_SUCCESS;
#else
        CYASSL_MSG("No Key Gen built in");
        return SSL_FATAL_ERROR;
#endif

    }


    /* SSL_SUCCESS on ok */
    int CyaSSL_RSA_blinding_on(CYASSL_RSA* rsa, CYASSL_BN_CTX* bn)
    {
        (void)rsa;
        (void)bn;

        CYASSL_MSG("CyaSSL_RSA_blinding_on");

        return SSL_SUCCESS;  /* on by default */
    }


    int CyaSSL_RSA_public_encrypt(int len, unsigned char* fr,
	                            unsigned char* to, CYASSL_RSA* rsa, int padding)
    {
        (void)len;
        (void)fr;
        (void)to;
        (void)rsa;
        (void)padding;

        CYASSL_MSG("CyaSSL_RSA_public_encrypt");

        return SSL_FATAL_ERROR;
    }


    int CyaSSL_RSA_private_decrypt(int len, unsigned char* fr,
	                            unsigned char* to, CYASSL_RSA* rsa, int padding)
    {
        (void)len;
        (void)fr;
        (void)to;
        (void)rsa;
        (void)padding;

        CYASSL_MSG("CyaSSL_RSA_private_decrypt");

        return SSL_FATAL_ERROR;
    }


    int CyaSSL_RSA_size(const CYASSL_RSA* rsa)
    {
        CYASSL_MSG("CyaSSL_RSA_size");

        if (rsa == NULL)
            return 0;

        return CyaSSL_BN_num_bytes(rsa->n);
    }
#endif /* NO_RSA */


#ifndef NO_DSA
    /* return SSL_SUCCESS on success, < 0 otherwise */
    int CyaSSL_DSA_do_sign(const unsigned char* d, unsigned char* sigRet,
                           CYASSL_DSA* dsa)
    {
        RNG    tmpRNG;
        RNG*   rng = &tmpRNG;

        CYASSL_MSG("CyaSSL_DSA_do_sign");

        if (d == NULL || sigRet == NULL || dsa == NULL) {
            CYASSL_MSG("Bad function arguments");
            return SSL_FATAL_ERROR;
        }

        if (dsa->inSet == 0) {
            CYASSL_MSG("No DSA internal set");
            return SSL_FATAL_ERROR;
        }

        if (InitRng(&tmpRNG) != 0) {
            CYASSL_MSG("Bad RNG Init, trying global");
            if (initGlobalRNG == 0) {
                CYASSL_MSG("Global RNG no Init");
                return SSL_FATAL_ERROR;
            }
            rng = &globalRNG;
        }

        if (DsaSign(d, sigRet, (DsaKey*)dsa->internal, rng) < 0) {
            CYASSL_MSG("DsaSign failed");
            return SSL_FATAL_ERROR;
        }

        return SSL_SUCCESS;
    }
#endif /* NO_DSA */


#ifndef NO_RSA
    /* return SSL_SUCCES on ok, 0 otherwise */
    int CyaSSL_RSA_sign(int type, const unsigned char* m,
                               unsigned int mLen, unsigned char* sigRet,
                               unsigned int* sigLen, CYASSL_RSA* rsa)
    {
        byte   encodedSig[MAX_ENCODED_SIG_SZ];
        word32 outLen;
        word32 signSz;
        RNG    tmpRNG;
        RNG*   rng = &tmpRNG;

        CYASSL_MSG("CyaSSL_RSA_sign");

        if (m == NULL || sigRet == NULL || sigLen == NULL || rsa == NULL) {
            CYASSL_MSG("Bad function arguments");
            return 0;
        }

        if (rsa->inSet == 0) {
            CYASSL_MSG("No RSA internal set");
            return 0;
        }

        outLen = (word32)CyaSSL_BN_num_bytes(rsa->n);
        if (outLen == 0) {
            CYASSL_MSG("Bad RSA size");
            return 0;
        }

        if (InitRng(&tmpRNG) != 0) {
            CYASSL_MSG("Bad RNG Init, trying global");
            if (initGlobalRNG == 0) {
                CYASSL_MSG("Global RNG no Init");
                return 0;
            }
            rng = &globalRNG;
        }

        switch (type) {
            case NID_md5:
                type = MD5h;
                break;

            case NID_sha1:
                type = SHAh;
                break;

            default:
                CYASSL_MSG("Bad md type");
                return 0;
        }

        signSz = EncodeSignature(encodedSig, m, mLen, type);
        if (signSz == 0) {
            CYASSL_MSG("Bad Encode Signature");
            return 0;
        }

        *sigLen = RsaSSL_Sign(encodedSig, signSz, sigRet, outLen,
                              (RsaKey*)rsa->internal, rng);
        if (*sigLen <= 0) {
            CYASSL_MSG("Bad Rsa Sign");
            return 0;
        }

        CYASSL_MSG("CyaSSL_RSA_sign success");
        return SSL_SUCCESS;
    }


    int CyaSSL_RSA_public_decrypt(int flen, unsigned char* from,
                              unsigned char* to, CYASSL_RSA* rsa, int padding)
    {
        (void)flen;
        (void)from;
        (void)to;
        (void)rsa;
        (void)padding;

        CYASSL_MSG("CyaSSL_RSA_public_decrypt");

        return SSL_FATAL_ERROR;
    }


    /* generate p-1 and q-1, SSL_SUCCESS on ok */
    int CyaSSL_RSA_GenAdd(CYASSL_RSA* rsa)
    {
        int    err;
        mp_int tmp;

        CYASSL_MSG("CyaSSL_RsaGenAdd");

        if (rsa == NULL || rsa->p == NULL || rsa->q == NULL || rsa->d == NULL ||
                           rsa->dmp1 == NULL || rsa->dmq1 == NULL) {
            CYASSL_MSG("rsa no init error");
            return SSL_FATAL_ERROR;
        }

        if (mp_init(&tmp) != MP_OKAY) {
            CYASSL_MSG("mp_init error");
            return SSL_FATAL_ERROR;
        }

        err = mp_sub_d((mp_int*)rsa->p->internal, 1, &tmp);
        if (err != MP_OKAY) {
            CYASSL_MSG("mp_sub_d error");
        }
        else
            err = mp_mod((mp_int*)rsa->d->internal, &tmp,
                         (mp_int*)rsa->dmp1->internal);

        if (err != MP_OKAY) {
            CYASSL_MSG("mp_mod error");
        }
        else
            err = mp_sub_d((mp_int*)rsa->q->internal, 1, &tmp);
        if (err != MP_OKAY) {
            CYASSL_MSG("mp_sub_d error");
        }
        else
            err = mp_mod((mp_int*)rsa->d->internal, &tmp,
                         (mp_int*)rsa->dmq1->internal);

        mp_clear(&tmp);

        if (err == MP_OKAY)
            return SSL_SUCCESS;
        else
            return SSL_FATAL_ERROR;
    }
#endif /* NO_RSA */


    void CyaSSL_HMAC_Init(CYASSL_HMAC_CTX* ctx, const void* key, int keylen,
                      const EVP_MD* type)
    {
        CYASSL_MSG("CyaSSL_HMAC_Init");

        if (ctx == NULL) {
            CYASSL_MSG("no ctx on init");
            return;
        }

        if (type) {
            CYASSL_MSG("init has type");

            if (XSTRNCMP(type, "MD5", 3) == 0) {
                CYASSL_MSG("md5 hmac");
                ctx->type = MD5;
            }
            else if (XSTRNCMP(type, "SHA256", 6) == 0) {
                CYASSL_MSG("sha256 hmac");
                ctx->type = SHA256;
            }

            /* has to be last since would pick or 256, 384, or 512 too */
            else if (XSTRNCMP(type, "SHA", 3) == 0) {
                CYASSL_MSG("sha hmac");
                ctx->type = SHA;
            }
            else {
                CYASSL_MSG("bad init type");
            }
        }

        if (key && keylen) {
            CYASSL_MSG("keying hmac");
            HmacSetKey(&ctx->hmac, ctx->type, (const byte*)key, (word32)keylen);
            /* OpenSSL compat, no error */
        }
    }


    void CyaSSL_HMAC_Update(CYASSL_HMAC_CTX* ctx, const unsigned char* data,
                        int len)
    {
        CYASSL_MSG("CyaSSL_HMAC_Update");

        if (ctx && data) {
            CYASSL_MSG("updating hmac");
            HmacUpdate(&ctx->hmac, data, (word32)len);
            /* OpenSSL compat, no error */
        }
    }


    void CyaSSL_HMAC_Final(CYASSL_HMAC_CTX* ctx, unsigned char* hash,
                       unsigned int* len)
    {
        CYASSL_MSG("CyaSSL_HMAC_Final");

        if (ctx && hash) {
            CYASSL_MSG("final hmac");
            HmacFinal(&ctx->hmac, hash);
            /* OpenSSL compat, no error */

            if (len) {
                CYASSL_MSG("setting output len");
                switch (ctx->type) {
                    case MD5:
                        *len = MD5_DIGEST_SIZE;
                        break;

                    case SHA:
                        *len = SHA_DIGEST_SIZE;
                        break;

                    case SHA256:
                        *len = SHA256_DIGEST_SIZE;
                        break;

                    default:
                        CYASSL_MSG("bad hmac type");
                }
            }
        }
    }


    void CyaSSL_HMAC_cleanup(CYASSL_HMAC_CTX* ctx)
    {
        (void)ctx;

        CYASSL_MSG("CyaSSL_HMAC_cleanup");
    }


    const CYASSL_EVP_MD* CyaSSL_EVP_get_digestbynid(int id)
    {
        CYASSL_MSG("CyaSSL_get_digestbynid");

        switch(id) {
            case NID_md5:
                return CyaSSL_EVP_md5();

            case NID_sha1:
                return CyaSSL_EVP_sha1();

            default:
                CYASSL_MSG("Bad digest id value");
        }

        return NULL;
    }


    CYASSL_RSA* CyaSSL_EVP_PKEY_get1_RSA(CYASSL_EVP_PKEY* key)
    {
        (void)key;
        CYASSL_MSG("CyaSSL_EVP_PKEY_get1_RSA");

        return NULL;
    }


    CYASSL_DSA* CyaSSL_EVP_PKEY_get1_DSA(CYASSL_EVP_PKEY* key)
    {
        (void)key;
        CYASSL_MSG("CyaSSL_EVP_PKEY_get1_DSA");

        return NULL;
    }


    void* CyaSSL_EVP_X_STATE(const CYASSL_EVP_CIPHER_CTX* ctx)
    {
        CYASSL_MSG("CyaSSL_EVP_X_STATE");

        if (ctx) {
            switch (ctx->cipherType) {
                case ARC4_TYPE:
                    CYASSL_MSG("returning arc4 state");
                    return (void*)&ctx->cipher.arc4.x;

                default:
                    CYASSL_MSG("bad x state type");
                    return 0;
            }
        }

        return NULL;
    }


    int CyaSSL_EVP_X_STATE_LEN(const CYASSL_EVP_CIPHER_CTX* ctx)
    {
        CYASSL_MSG("CyaSSL_EVP_X_STATE_LEN");

        if (ctx) {
            switch (ctx->cipherType) {
                case ARC4_TYPE:
                    CYASSL_MSG("returning arc4 state size");
                    return sizeof(Arc4);

                default:
                    CYASSL_MSG("bad x state type");
                    return 0;
            }
        }

        return 0;
    }


    void CyaSSL_3des_iv(CYASSL_EVP_CIPHER_CTX* ctx, int doset,
                                unsigned char* iv, int len)
    {
        (void)len;

        CYASSL_MSG("CyaSSL_3des_iv");

        if (ctx == NULL || iv == NULL) {
            CYASSL_MSG("Bad function argument");
            return;
        }

        if (doset)
            Des3_SetIV(&ctx->cipher.des3, iv);  /* OpenSSL compat, no ret */
        else
            memcpy(iv, &ctx->cipher.des3.reg, DES_BLOCK_SIZE);
    }


    void CyaSSL_aes_ctr_iv(CYASSL_EVP_CIPHER_CTX* ctx, int doset,
                          unsigned char* iv, int len)
    {
        (void)len;

        CYASSL_MSG("CyaSSL_aes_ctr_iv");

        if (ctx == NULL || iv == NULL) {
            CYASSL_MSG("Bad function argument");
            return;
        }

        if (doset)
            AesSetIV(&ctx->cipher.aes, iv);  /* OpenSSL compat, no ret */
        else
            memcpy(iv, &ctx->cipher.aes.reg, AES_BLOCK_SIZE);
    }


    const CYASSL_EVP_MD* CyaSSL_EVP_ripemd160(void)
    {
        CYASSL_MSG("CyaSSL_ripemd160");

        return NULL;
    }


    int CyaSSL_EVP_MD_size(const CYASSL_EVP_MD* type)
    {
        CYASSL_MSG("CyaSSL_EVP_MD_size");

        if (type == NULL) {
            CYASSL_MSG("No md type arg");
            return BAD_FUNC_ARG;
        }

        if (XSTRNCMP(type, "MD5", 3) == 0) {
            return MD5_DIGEST_SIZE;
        }
        else if (XSTRNCMP(type, "SHA256", 6) == 0) {
            return SHA256_DIGEST_SIZE;
        }
    #ifdef CYASSL_SHA384
        else if (XSTRNCMP(type, "SHA384", 6) == 0) {
            return SHA384_DIGEST_SIZE;
        }
    #endif
    #ifdef CYASSL_SHA512
        else if (XSTRNCMP(type, "SHA512", 6) == 0) {
            return SHA512_DIGEST_SIZE;
        }
    #endif
        /* has to be last since would pick or 256, 384, or 512 too */
        else if (XSTRNCMP(type, "SHA", 3) == 0) {
            return SHA_DIGEST_SIZE;
        }

        return BAD_FUNC_ARG;
    }


    int CyaSSL_EVP_CIPHER_CTX_iv_length(const CYASSL_EVP_CIPHER_CTX* ctx)
    {
        CYASSL_MSG("CyaSSL_EVP_CIPHER_CTX_iv_length");

        switch (ctx->cipherType) {

            case AES_128_CBC_TYPE :
            case AES_192_CBC_TYPE :
            case AES_256_CBC_TYPE :
                CYASSL_MSG("AES CBC");
                return AES_BLOCK_SIZE;

#ifdef CYASSL_AES_COUNTER
            case AES_128_CTR_TYPE :
            case AES_192_CTR_TYPE :
            case AES_256_CTR_TYPE :
                CYASSL_MSG("AES CTR");
                return AES_BLOCK_SIZE;
#endif

            case DES_CBC_TYPE :
                CYASSL_MSG("DES CBC");
                return DES_BLOCK_SIZE;

            case DES_EDE3_CBC_TYPE :
                CYASSL_MSG("DES EDE3 CBC");
                return DES_BLOCK_SIZE;

            case ARC4_TYPE :
                CYASSL_MSG("ARC4");
                return 0;

            case NULL_CIPHER_TYPE :
                CYASSL_MSG("NULL");
                return 0;

            default: {
                CYASSL_MSG("bad type");
            }
        }
        return 0;
    }


    void CyaSSL_OPENSSL_free(void* p)
    {
        CYASSL_MSG("CyaSSL_OPENSSL_free");

        XFREE(p, NULL, 0);
    }


    int CyaSSL_PEM_write_bio_RSAPrivateKey(CYASSL_BIO* bio, RSA* rsa,
	                                  const EVP_CIPHER* cipher,
	                                  unsigned char* passwd, int len,
	                                  pem_password_cb cb, void* arg)
    {
        (void)bio;
        (void)rsa;
        (void)cipher;
        (void)passwd;
        (void)len;
        (void)cb;
        (void)arg;

        CYASSL_MSG("CyaSSL_PEM_write_bio_RSAPrivateKey");

        return SSL_FATAL_ERROR;
    }



    int CyaSSL_PEM_write_bio_DSAPrivateKey(CYASSL_BIO* bio, DSA* rsa,
	                                  const EVP_CIPHER* cipher,
	                                  unsigned char* passwd, int len,
	                                  pem_password_cb cb, void* arg)
    {
        (void)bio;
        (void)rsa;
        (void)cipher;
        (void)passwd;
        (void)len;
        (void)cb;
        (void)arg;

        CYASSL_MSG("CyaSSL_PEM_write_bio_DSAPrivateKey");

        return SSL_FATAL_ERROR;
    }



    CYASSL_EVP_PKEY* CyaSSL_PEM_read_bio_PrivateKey(CYASSL_BIO* bio,
                        CYASSL_EVP_PKEY** key, pem_password_cb cb, void* arg)
    {
        (void)bio;
        (void)key;
        (void)cb;
        (void)arg;

        CYASSL_MSG("CyaSSL_PEM_read_bio_PrivateKey");

        return NULL;
    }



#ifndef NO_RSA
/* Load RSA from Der, SSL_SUCCESS on success < 0 on error */
int CyaSSL_RSA_LoadDer(CYASSL_RSA* rsa, const unsigned char* der,  int derSz)
{
    word32 idx = 0;
    int    ret;

    CYASSL_ENTER("CyaSSL_RSA_LoadDer");

    if (rsa == NULL || rsa->internal == NULL || der == NULL || derSz <= 0) {
        CYASSL_MSG("Bad function arguments");
        return BAD_FUNC_ARG;
    }

    ret = RsaPrivateKeyDecode(der, &idx, (RsaKey*)rsa->internal, derSz);
    if (ret < 0) {
        CYASSL_MSG("RsaPrivateKeyDecode failed");
        return ret;
    }

    if (SetRsaExternal(rsa) < 0) {
        CYASSL_MSG("SetRsaExternal failed");
        return SSL_FATAL_ERROR;
    }

    rsa->inSet = 1;

    return SSL_SUCCESS;
}
#endif /* NO_RSA */


#ifndef NO_DSA
/* Load DSA from Der, SSL_SUCCESS on success < 0 on error */
int CyaSSL_DSA_LoadDer(CYASSL_DSA* dsa, const unsigned char* der,  int derSz)
{
    word32 idx = 0;
    int    ret;

    CYASSL_ENTER("CyaSSL_DSA_LoadDer");

    if (dsa == NULL || dsa->internal == NULL || der == NULL || derSz <= 0) {
        CYASSL_MSG("Bad function arguments");
        return BAD_FUNC_ARG;
    }

    ret = DsaPrivateKeyDecode(der, &idx, (DsaKey*)dsa->internal, derSz);
    if (ret < 0) {
        CYASSL_MSG("DsaPrivateKeyDecode failed");
        return ret;
    }

    if (SetDsaExternal(dsa) < 0) {
        CYASSL_MSG("SetDsaExternal failed");
        return SSL_FATAL_ERROR;
    }

    dsa->inSet = 1;

    return SSL_SUCCESS;
}
#endif /* NO_DSA */




#endif /* OPENSSL_EXTRA */


#ifdef SESSION_CERTS


/* Get peer's certificate chain */
CYASSL_X509_CHAIN* CyaSSL_get_peer_chain(CYASSL* ssl)
{
    CYASSL_ENTER("CyaSSL_get_peer_chain");
    if (ssl)
        return &ssl->session.chain;

    return 0;
}


/* Get peer's certificate chain total count */
int CyaSSL_get_chain_count(CYASSL_X509_CHAIN* chain)
{
    CYASSL_ENTER("CyaSSL_get_chain_count");
    if (chain)
        return chain->count;

    return 0;
}


/* Get peer's ASN.1 DER ceritifcate at index (idx) length in bytes */
int CyaSSL_get_chain_length(CYASSL_X509_CHAIN* chain, int idx)
{
    CYASSL_ENTER("CyaSSL_get_chain_length");
    if (chain)
        return chain->certs[idx].length;

    return 0;
}


/* Get peer's ASN.1 DER ceritifcate at index (idx) */
byte* CyaSSL_get_chain_cert(CYASSL_X509_CHAIN* chain, int idx)
{
    CYASSL_ENTER("CyaSSL_get_chain_cert");
    if (chain)
        return chain->certs[idx].buffer;

    return 0;
}


/* Get peer's CyaSSL X509 ceritifcate at index (idx) */
CYASSL_X509* CyaSSL_get_chain_X509(CYASSL_X509_CHAIN* chain, int idx)
{
    int          ret;
    CYASSL_X509* x509;
    DecodedCert  dCert;

    CYASSL_ENTER("CyaSSL_get_chain_X509");
    if (chain == NULL)
        return NULL;

    InitDecodedCert(&dCert, chain->certs[idx].buffer, chain->certs[idx].length,
                    NULL);
    ret = ParseCertRelative(&dCert, CERT_TYPE, 0, NULL);
    if (ret != 0) {
        CYASSL_MSG("Failed to parse cert");
        FreeDecodedCert(&dCert);
        return NULL;
    }

    x509 = (CYASSL_X509*)XMALLOC(sizeof(CYASSL_X509), NULL, DYNAMIC_TYPE_X509);
    if (x509 == NULL) {
        CYASSL_MSG("Failed alloc X509");
        FreeDecodedCert(&dCert);
        return NULL;
    }
    InitX509(x509, 1);

    ret = CopyDecodedToX509(x509, &dCert);
    if (ret != 0) {
        CYASSL_MSG("Failed to copy decoded");
        XFREE(x509, NULL, DYNAMIC_TYPE_X509);
        x509 = NULL;
    }
    FreeDecodedCert(&dCert);

    return x509;
}


/* Get peer's PEM ceritifcate at index (idx), output to buffer if inLen big
   enough else return error (-1), output length is in *outLen
   SSL_SUCCESS on ok */
int  CyaSSL_get_chain_cert_pem(CYASSL_X509_CHAIN* chain, int idx,
                               unsigned char* buf, int inLen, int* outLen)
{
    const char header[] = "-----BEGIN CERTIFICATE-----\n";
    const char footer[] = "-----END CERTIFICATE-----\n";

    int headerLen = sizeof(header) - 1;
    int footerLen = sizeof(footer) - 1;
    int i;
    int err;

    CYASSL_ENTER("CyaSSL_get_chain_cert_pem");
    if (!chain || !outLen || !buf)
        return BAD_FUNC_ARG;

    /* don't even try if inLen too short */
    if (inLen < headerLen + footerLen + chain->certs[idx].length)
        return BAD_FUNC_ARG;

    /* header */
    XMEMCPY(buf, header, headerLen);
    i = headerLen;

    /* body */
    *outLen = inLen;  /* input to Base64_Encode */
    if ( (err = Base64_Encode(chain->certs[idx].buffer,
                       chain->certs[idx].length, buf + i, (word32*)outLen)) < 0)
        return err;
    i += *outLen;

    /* footer */
    if ( (i + footerLen) > inLen)
        return BAD_FUNC_ARG;
    XMEMCPY(buf + i, footer, footerLen);
    *outLen += headerLen + footerLen;

    return SSL_SUCCESS;
}


/* get session ID */
const byte* CyaSSL_get_sessionID(const CYASSL_SESSION* session)
{
    CYASSL_ENTER("CyaSSL_get_sessionID");
    if (session)
        return session->sessionID;

    return NULL;
}


#endif /* SESSION_CERTS */


#ifndef NO_CERTS
#ifdef  HAVE_PK_CALLBACKS

#ifdef HAVE_ECC

void  CyaSSL_CTX_SetEccSignCb(CYASSL_CTX* ctx, CallbackEccSign cb)
{
    if (ctx)
        ctx->EccSignCb = cb;
}


void  CyaSSL_SetEccSignCtx(CYASSL* ssl, void *ctx)
{
    if (ssl)
        ssl->EccSignCtx = ctx;
}


void* CyaSSL_GetEccSignCtx(CYASSL* ssl)
{
    if (ssl)
        return ssl->EccSignCtx;

    return NULL;
}


void  CyaSSL_CTX_SetEccVerifyCb(CYASSL_CTX* ctx, CallbackEccVerify cb)
{
    if (ctx)
        ctx->EccVerifyCb = cb;
}


void  CyaSSL_SetEccVerifyCtx(CYASSL* ssl, void *ctx)
{
    if (ssl)
        ssl->EccVerifyCtx = ctx;
}


void* CyaSSL_GetEccVerifyCtx(CYASSL* ssl)
{
    if (ssl)
        return ssl->EccVerifyCtx;

    return NULL;
}

#endif /* HAVE_ECC */

#ifndef NO_RSA

void  CyaSSL_CTX_SetRsaSignCb(CYASSL_CTX* ctx, CallbackRsaSign cb)
{
    if (ctx)
        ctx->RsaSignCb = cb;
}


void  CyaSSL_SetRsaSignCtx(CYASSL* ssl, void *ctx)
{
    if (ssl)
        ssl->RsaSignCtx = ctx;
}


void* CyaSSL_GetRsaSignCtx(CYASSL* ssl)
{
    if (ssl)
        return ssl->RsaSignCtx;

    return NULL;
}


void  CyaSSL_CTX_SetRsaVerifyCb(CYASSL_CTX* ctx, CallbackRsaVerify cb)
{
    if (ctx)
        ctx->RsaVerifyCb = cb;
}


void  CyaSSL_SetRsaVerifyCtx(CYASSL* ssl, void *ctx)
{
    if (ssl)
        ssl->RsaVerifyCtx = ctx;
}


void* CyaSSL_GetRsaVerifyCtx(CYASSL* ssl)
{
    if (ssl)
        return ssl->RsaVerifyCtx;

    return NULL;
}

void  CyaSSL_CTX_SetRsaEncCb(CYASSL_CTX* ctx, CallbackRsaEnc cb)
{
    if (ctx)
        ctx->RsaEncCb = cb;
}


void  CyaSSL_SetRsaEncCtx(CYASSL* ssl, void *ctx)
{
    if (ssl)
        ssl->RsaEncCtx = ctx;
}


void* CyaSSL_GetRsaEncCtx(CYASSL* ssl)
{
    if (ssl)
        return ssl->RsaEncCtx;

    return NULL;
}

void  CyaSSL_CTX_SetRsaDecCb(CYASSL_CTX* ctx, CallbackRsaDec cb)
{
    if (ctx)
        ctx->RsaDecCb = cb;
}


void  CyaSSL_SetRsaDecCtx(CYASSL* ssl, void *ctx)
{
    if (ssl)
        ssl->RsaDecCtx = ctx;
}


void* CyaSSL_GetRsaDecCtx(CYASSL* ssl)
{
    if (ssl)
        return ssl->RsaDecCtx;

    return NULL;
}


#endif /* NO_RSA */

#endif /* HAVE_PK_CALLBACKS */
#endif /* NO_CERTS */


#ifdef CYASSL_HAVE_WOLFSCEP
    /* Used by autoconf to see if wolfSCEP is available */
    void CyaSSL_wolfSCEP(void) {}
#endif


#ifdef CYASSL_HAVE_CERT_SERVICE
    /* Used by autoconf to see if cert service is available */
    void CyaSSL_cert_service(void) {}
#endif

