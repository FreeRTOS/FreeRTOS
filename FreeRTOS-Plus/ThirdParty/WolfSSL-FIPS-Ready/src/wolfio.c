/* wolfio.c
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



#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#ifndef WOLFCRYPT_ONLY

#ifdef _WIN32_WCE
    /* On WinCE winsock2.h must be included before windows.h for socket stuff */
    #include <winsock2.h>
#endif

#include <wolfssl/internal.h>
#include <wolfssl/error-ssl.h>
#include <wolfssl/wolfio.h>

#if defined(HAVE_HTTP_CLIENT)
    #include <stdlib.h>   /* strtol() */
#endif

/*
Possible IO enable options:
 * WOLFSSL_USER_IO:     Disables default Embed* callbacks and     default: off
                        allows user to define their own using
                        wolfSSL_CTX_SetIORecv and wolfSSL_CTX_SetIOSend
 * USE_WOLFSSL_IO:      Enables the wolfSSL IO functions          default: off
 * HAVE_HTTP_CLIENT:    Enables HTTP client API's                 default: off
                                     (unless HAVE_OCSP or HAVE_CRL_IO defined)
 * HAVE_IO_TIMEOUT:     Enables support for connect timeout       default: off
 */


/* if user writes own I/O callbacks they can define WOLFSSL_USER_IO to remove
   automatic setting of default I/O functions EmbedSend() and EmbedReceive()
   but they'll still need SetCallback xxx() at end of file
*/

#if defined(USE_WOLFSSL_IO) || defined(HAVE_HTTP_CLIENT)

/* Translates return codes returned from
 * send() and recv() if need be.
 */
static WC_INLINE int TranslateReturnCode(int old, int sd)
{
    (void)sd;

#if defined(FREESCALE_MQX) || defined(FREESCALE_KSDK_MQX)
    if (old == 0) {
        errno = SOCKET_EWOULDBLOCK;
        return -1;  /* convert to BSD style wouldblock as error */
    }

    if (old < 0) {
        errno = RTCS_geterror(sd);
        if (errno == RTCSERR_TCP_CONN_CLOSING)
            return 0;   /* convert to BSD style closing */
        if (errno == RTCSERR_TCP_CONN_RLSD)
            errno = SOCKET_ECONNRESET;
        if (errno == RTCSERR_TCP_TIMED_OUT)
            errno = SOCKET_EAGAIN;
    }
#endif

    return old;
}

static WC_INLINE int wolfSSL_LastError(void)
{
#ifdef USE_WINDOWS_API
    return WSAGetLastError();
#elif defined(EBSNET)
    return xn_getlasterror();
#else
    return errno;
#endif
}

#endif /* USE_WOLFSSL_IO || HAVE_HTTP_CLIENT */


#ifdef OPENSSL_EXTRA
/* Use the WOLFSSL read BIO for receiving data. This is set by the function
 * wolfSSL_set_bio and can also be set by wolfSSL_CTX_SetIORecv.
 *
 * ssl  WOLFSSL struct passed in that has this function set as the receive
 *      callback.
 * buf  buffer to fill with data read
 * sz   size of buf buffer
 * ctx  a user set context
 *
 * returns the amount of data read or want read. See WOLFSSL_CBIO_ERR_* values.
 */
int BioReceive(WOLFSSL* ssl, char* buf, int sz, void* ctx)
{
    int recvd = WOLFSSL_CBIO_ERR_GENERAL;

    WOLFSSL_ENTER("BioReceive");

    if (ssl->biord == NULL) {
        WOLFSSL_MSG("WOLFSSL biord not set");
        return WOLFSSL_CBIO_ERR_GENERAL;
    }

    if (ssl->biord->method && ssl->biord->method->readCb) {
        WOLFSSL_MSG("Calling custom biord");
        recvd = ssl->biord->method->readCb(ssl->biord, buf, sz);
        if (recvd < 0 && recvd != WOLFSSL_CBIO_ERR_WANT_READ)
            return WOLFSSL_CBIO_ERR_GENERAL;
        return recvd;
    }

    switch (ssl->biord->type) {
        case WOLFSSL_BIO_MEMORY:
        case WOLFSSL_BIO_BIO:
            if (wolfSSL_BIO_ctrl_pending(ssl->biord) == 0) {
                WOLFSSL_MSG("BIO want read");
               return WOLFSSL_CBIO_ERR_WANT_READ;
            }
            recvd = wolfSSL_BIO_read(ssl->biord, buf, sz);
            if (recvd <= 0) {
                WOLFSSL_MSG("BIO general error");
                return WOLFSSL_CBIO_ERR_GENERAL;
            }
            break;

       default:
            WOLFSSL_MSG("This BIO type is unknown / unsupported");
            return WOLFSSL_CBIO_ERR_GENERAL;
    }

    (void)ctx;
    return recvd;
}


/* Use the WOLFSSL write BIO for sending data. This is set by the function
 * wolfSSL_set_bio and can also be set by wolfSSL_CTX_SetIOSend.
 *
 * ssl  WOLFSSL struct passed in that has this function set as the send callback.
 * buf  buffer with data to write out
 * sz   size of buf buffer
 * ctx  a user set context
 *
 * returns the amount of data sent or want send. See WOLFSSL_CBIO_ERR_* values.
 */
int BioSend(WOLFSSL* ssl, char *buf, int sz, void *ctx)
{
    int sent = WOLFSSL_CBIO_ERR_GENERAL;

    WOLFSSL_ENTER("BioSend");

    if (ssl->biowr == NULL) {
        WOLFSSL_MSG("WOLFSSL biowr not set");
        return WOLFSSL_CBIO_ERR_GENERAL;
    }

    if (ssl->biowr->method && ssl->biowr->method->writeCb) {
        WOLFSSL_MSG("Calling custom biowr");
        sent = ssl->biowr->method->writeCb(ssl->biowr, buf, sz);
        if (sent < 0) {
            return WOLFSSL_CBIO_ERR_GENERAL;
        }
        return sent;
    }

    switch (ssl->biowr->type) {
        case WOLFSSL_BIO_MEMORY:
        case WOLFSSL_BIO_BIO:
            sent = wolfSSL_BIO_write(ssl->biowr, buf, sz);
            if (sent < 0) {
                return WOLFSSL_CBIO_ERR_GENERAL;
            }
            break;

        default:
            WOLFSSL_MSG("This BIO type is unknown / unsupported");
            return WOLFSSL_CBIO_ERR_GENERAL;
    }
    (void)ctx;

    return sent;
}
#endif


#ifdef USE_WOLFSSL_IO

/* The receive embedded callback
 *  return : nb bytes read, or error
 */
int EmbedReceive(WOLFSSL *ssl, char *buf, int sz, void *ctx)
{
    int sd = *(int*)ctx;
    int recvd;

    recvd = wolfIO_Recv(sd, buf, sz, ssl->rflags);
    if (recvd < 0) {
        int err = wolfSSL_LastError();
        WOLFSSL_MSG("Embed Receive error");

        if (err == SOCKET_EWOULDBLOCK || err == SOCKET_EAGAIN) {
            WOLFSSL_MSG("\tWould block");
            return WOLFSSL_CBIO_ERR_WANT_READ;
        }
        else if (err == SOCKET_ECONNRESET) {
            WOLFSSL_MSG("\tConnection reset");
            return WOLFSSL_CBIO_ERR_CONN_RST;
        }
        else if (err == SOCKET_EINTR) {
            WOLFSSL_MSG("\tSocket interrupted");
            return WOLFSSL_CBIO_ERR_ISR;
        }
        else if (err == SOCKET_ECONNABORTED) {
            WOLFSSL_MSG("\tConnection aborted");
            return WOLFSSL_CBIO_ERR_CONN_CLOSE;
        }
        else {
            WOLFSSL_MSG("\tGeneral error");
            return WOLFSSL_CBIO_ERR_GENERAL;
        }
    }
    else if (recvd == 0) {
        WOLFSSL_MSG("Embed receive connection closed");
        return WOLFSSL_CBIO_ERR_CONN_CLOSE;
    }

    return recvd;
}

/* The send embedded callback
 *  return : nb bytes sent, or error
 */
int EmbedSend(WOLFSSL* ssl, char *buf, int sz, void *ctx)
{
    int sd = *(int*)ctx;
    int sent;

#ifdef WOLFSSL_MAX_SEND_SZ
    if (sz > WOLFSSL_MAX_SEND_SZ)
        sz = WOLFSSL_MAX_SEND_SZ;
#endif

    sent = wolfIO_Send(sd, buf, sz, ssl->wflags);
    if (sent < 0) {
        int err = wolfSSL_LastError();
        WOLFSSL_MSG("Embed Send error");

        if (err == SOCKET_EWOULDBLOCK || err == SOCKET_EAGAIN) {
            WOLFSSL_MSG("\tWould Block");
            return WOLFSSL_CBIO_ERR_WANT_WRITE;
        }
        else if (err == SOCKET_ECONNRESET) {
            WOLFSSL_MSG("\tConnection reset");
            return WOLFSSL_CBIO_ERR_CONN_RST;
        }
        else if (err == SOCKET_EINTR) {
            WOLFSSL_MSG("\tSocket interrupted");
            return WOLFSSL_CBIO_ERR_ISR;
        }
        else if (err == SOCKET_EPIPE) {
            WOLFSSL_MSG("\tSocket EPIPE");
            return WOLFSSL_CBIO_ERR_CONN_CLOSE;
        }
        else {
            WOLFSSL_MSG("\tGeneral error");
            return WOLFSSL_CBIO_ERR_GENERAL;
        }
    }

    return sent;
}


#ifdef WOLFSSL_DTLS

#include <wolfssl/wolfcrypt/sha.h>

#define SENDTO_FUNCTION sendto
#define RECVFROM_FUNCTION recvfrom


/* The receive embedded callback
 *  return : nb bytes read, or error
 */
int EmbedReceiveFrom(WOLFSSL *ssl, char *buf, int sz, void *ctx)
{
    WOLFSSL_DTLS_CTX* dtlsCtx = (WOLFSSL_DTLS_CTX*)ctx;
    int recvd;
    int err;
    int sd = dtlsCtx->rfd;
    int dtls_timeout = wolfSSL_dtls_get_current_timeout(ssl);
    SOCKADDR_S peer;
    XSOCKLENT peerSz = sizeof(peer);

    WOLFSSL_ENTER("EmbedReceiveFrom()");

    /* Don't use ssl->options.handShakeDone since it is true even if
     * we are in the process of renegotiation */
    if (ssl->options.handShakeState == HANDSHAKE_DONE)
        dtls_timeout = 0;

    if (!wolfSSL_get_using_nonblock(ssl)) {
        #ifdef USE_WINDOWS_API
            DWORD timeout = dtls_timeout * 1000;
        #else
            struct timeval timeout;
            XMEMSET(&timeout, 0, sizeof(timeout));
            timeout.tv_sec = dtls_timeout;
        #endif
        if (setsockopt(sd, SOL_SOCKET, SO_RCVTIMEO, (char*)&timeout,
                       sizeof(timeout)) != 0) {
                WOLFSSL_MSG("setsockopt rcvtimeo failed");
        }
    }

    recvd = (int)RECVFROM_FUNCTION(sd, buf, sz, ssl->rflags,
                                  (SOCKADDR*)&peer, &peerSz);

    recvd = TranslateReturnCode(recvd, sd);

    if (recvd < 0) {
        err = wolfSSL_LastError();
        WOLFSSL_MSG("Embed Receive From error");

        if (err == SOCKET_EWOULDBLOCK || err == SOCKET_EAGAIN) {
            if (wolfSSL_dtls_get_using_nonblock(ssl)) {
                WOLFSSL_MSG("\tWould block");
                return WOLFSSL_CBIO_ERR_WANT_READ;
            }
            else {
                WOLFSSL_MSG("\tSocket timeout");
                return WOLFSSL_CBIO_ERR_TIMEOUT;
            }
        }
        else if (err == SOCKET_ECONNRESET) {
            WOLFSSL_MSG("\tConnection reset");
            return WOLFSSL_CBIO_ERR_CONN_RST;
        }
        else if (err == SOCKET_EINTR) {
            WOLFSSL_MSG("\tSocket interrupted");
            return WOLFSSL_CBIO_ERR_ISR;
        }
        else if (err == SOCKET_ECONNREFUSED) {
            WOLFSSL_MSG("\tConnection refused");
            return WOLFSSL_CBIO_ERR_WANT_READ;
        }
        else {
            WOLFSSL_MSG("\tGeneral error");
            return WOLFSSL_CBIO_ERR_GENERAL;
        }
    }
    else {
        if (dtlsCtx->peer.sz > 0
                && peerSz != (XSOCKLENT)dtlsCtx->peer.sz
                && XMEMCMP(&peer, dtlsCtx->peer.sa, peerSz) != 0) {
            WOLFSSL_MSG("    Ignored packet from invalid peer");
            return WOLFSSL_CBIO_ERR_WANT_READ;
        }
    }

    return recvd;
}


/* The send embedded callback
 *  return : nb bytes sent, or error
 */
int EmbedSendTo(WOLFSSL* ssl, char *buf, int sz, void *ctx)
{
    WOLFSSL_DTLS_CTX* dtlsCtx = (WOLFSSL_DTLS_CTX*)ctx;
    int sd = dtlsCtx->wfd;
    int sent;
    int err;

    WOLFSSL_ENTER("EmbedSendTo()");

    sent = (int)SENDTO_FUNCTION(sd, buf, sz, ssl->wflags,
                                (const SOCKADDR*)dtlsCtx->peer.sa,
                                dtlsCtx->peer.sz);

    sent = TranslateReturnCode(sent, sd);

    if (sent < 0) {
        err = wolfSSL_LastError();
        WOLFSSL_MSG("Embed Send To error");

        if (err == SOCKET_EWOULDBLOCK || err == SOCKET_EAGAIN) {
            WOLFSSL_MSG("\tWould Block");
            return WOLFSSL_CBIO_ERR_WANT_WRITE;
        }
        else if (err == SOCKET_ECONNRESET) {
            WOLFSSL_MSG("\tConnection reset");
            return WOLFSSL_CBIO_ERR_CONN_RST;
        }
        else if (err == SOCKET_EINTR) {
            WOLFSSL_MSG("\tSocket interrupted");
            return WOLFSSL_CBIO_ERR_ISR;
        }
        else if (err == SOCKET_EPIPE) {
            WOLFSSL_MSG("\tSocket EPIPE");
            return WOLFSSL_CBIO_ERR_CONN_CLOSE;
        }
        else {
            WOLFSSL_MSG("\tGeneral error");
            return WOLFSSL_CBIO_ERR_GENERAL;
        }
    }

    return sent;
}


#ifdef WOLFSSL_MULTICAST

/* The alternate receive embedded callback for Multicast
 *  return : nb bytes read, or error
 */
int EmbedReceiveFromMcast(WOLFSSL *ssl, char *buf, int sz, void *ctx)
{
    WOLFSSL_DTLS_CTX* dtlsCtx = (WOLFSSL_DTLS_CTX*)ctx;
    int recvd;
    int err;
    int sd = dtlsCtx->rfd;

    WOLFSSL_ENTER("EmbedReceiveFromMcast()");

    recvd = (int)RECVFROM_FUNCTION(sd, buf, sz, ssl->rflags, NULL, NULL);

    recvd = TranslateReturnCode(recvd, sd);

    if (recvd < 0) {
        err = wolfSSL_LastError();
        WOLFSSL_MSG("Embed Receive From error");

        if (err == SOCKET_EWOULDBLOCK || err == SOCKET_EAGAIN) {
            if (wolfSSL_dtls_get_using_nonblock(ssl)) {
                WOLFSSL_MSG("\tWould block");
                return WOLFSSL_CBIO_ERR_WANT_READ;
            }
            else {
                WOLFSSL_MSG("\tSocket timeout");
                return WOLFSSL_CBIO_ERR_TIMEOUT;
            }
        }
        else if (err == SOCKET_ECONNRESET) {
            WOLFSSL_MSG("\tConnection reset");
            return WOLFSSL_CBIO_ERR_CONN_RST;
        }
        else if (err == SOCKET_EINTR) {
            WOLFSSL_MSG("\tSocket interrupted");
            return WOLFSSL_CBIO_ERR_ISR;
        }
        else if (err == SOCKET_ECONNREFUSED) {
            WOLFSSL_MSG("\tConnection refused");
            return WOLFSSL_CBIO_ERR_WANT_READ;
        }
        else {
            WOLFSSL_MSG("\tGeneral error");
            return WOLFSSL_CBIO_ERR_GENERAL;
        }
    }

    return recvd;
}
#endif /* WOLFSSL_MULTICAST */


/* The DTLS Generate Cookie callback
 *  return : number of bytes copied into buf, or error
 */
int EmbedGenerateCookie(WOLFSSL* ssl, byte *buf, int sz, void *ctx)
{
    int sd = ssl->wfd;
    SOCKADDR_S peer;
    XSOCKLENT peerSz = sizeof(peer);
    byte digest[WC_SHA256_DIGEST_SIZE];
    int  ret = 0;

    (void)ctx;

    XMEMSET(&peer, 0, sizeof(peer));
    if (getpeername(sd, (SOCKADDR*)&peer, &peerSz) != 0) {
        WOLFSSL_MSG("getpeername failed in EmbedGenerateCookie");
        return GEN_COOKIE_E;
    }

    ret = wc_Sha256Hash((byte*)&peer, peerSz, digest);
    if (ret != 0)
        return ret;

    if (sz > WC_SHA256_DIGEST_SIZE)
        sz = WC_SHA256_DIGEST_SIZE;
    XMEMCPY(buf, digest, sz);

    return sz;
}

#ifdef WOLFSSL_SESSION_EXPORT

    /* get the peer information in human readable form (ip, port, family)
     * default function assumes BSD sockets
     * can be overridden with wolfSSL_CTX_SetIOGetPeer
     */
    int EmbedGetPeer(WOLFSSL* ssl, char* ip, int* ipSz,
                                                 unsigned short* port, int* fam)
    {
        SOCKADDR_S peer;
        word32     peerSz;
        int        ret;

        if (ssl == NULL || ip == NULL || ipSz == NULL ||
                                                  port == NULL || fam == NULL) {
            return BAD_FUNC_ARG;
        }

        /* get peer information stored in ssl struct */
        peerSz = sizeof(SOCKADDR_S);
        if ((ret = wolfSSL_dtls_get_peer(ssl, (void*)&peer, &peerSz))
                                                               != WOLFSSL_SUCCESS) {
            return ret;
        }

        /* extract family, ip, and port */
        *fam = ((SOCKADDR_S*)&peer)->ss_family;
        switch (*fam) {
            case WOLFSSL_IP4:
                if (XINET_NTOP(*fam, &(((SOCKADDR_IN*)&peer)->sin_addr),
                                                           ip, *ipSz) == NULL) {
                    WOLFSSL_MSG("XINET_NTOP error");
                    return SOCKET_ERROR_E;
                }
                *port = XNTOHS(((SOCKADDR_IN*)&peer)->sin_port);
                break;

            case WOLFSSL_IP6:
            #ifdef WOLFSSL_IPV6
                if (XINET_NTOP(*fam, &(((SOCKADDR_IN6*)&peer)->sin6_addr),
                                                           ip, *ipSz) == NULL) {
                    WOLFSSL_MSG("XINET_NTOP error");
                    return SOCKET_ERROR_E;
                }
                *port = XNTOHS(((SOCKADDR_IN6*)&peer)->sin6_port);
            #endif /* WOLFSSL_IPV6 */
                break;

            default:
                WOLFSSL_MSG("Unknown family type");
                return SOCKET_ERROR_E;
        }
        ip[*ipSz - 1] = '\0'; /* make sure has terminator */
        *ipSz = (word16)XSTRLEN(ip);

        return WOLFSSL_SUCCESS;
    }

    /* set the peer information in human readable form (ip, port, family)
     * default function assumes BSD sockets
     * can be overridden with wolfSSL_CTX_SetIOSetPeer
     */
    int EmbedSetPeer(WOLFSSL* ssl, char* ip, int ipSz,
                                                   unsigned short port, int fam)
    {
        int    ret;
        SOCKADDR_S addr;

        /* sanity checks on arguments */
        if (ssl == NULL || ip == NULL || ipSz < 0 || ipSz > DTLS_EXPORT_IP) {
            return BAD_FUNC_ARG;
        }

        addr.ss_family = fam;
        switch (addr.ss_family) {
            case WOLFSSL_IP4:
                if (XINET_PTON(addr.ss_family, ip,
                                     &(((SOCKADDR_IN*)&addr)->sin_addr)) <= 0) {
                    WOLFSSL_MSG("XINET_PTON error");
                    return SOCKET_ERROR_E;
                }
                ((SOCKADDR_IN*)&addr)->sin_port = XHTONS(port);

                /* peer sa is free'd in SSL_ResourceFree */
                if ((ret = wolfSSL_dtls_set_peer(ssl, (SOCKADDR_IN*)&addr,
                                          sizeof(SOCKADDR_IN)))!= WOLFSSL_SUCCESS) {
                    WOLFSSL_MSG("Import DTLS peer info error");
                    return ret;
                }
                break;

            case WOLFSSL_IP6:
            #ifdef WOLFSSL_IPV6
                if (XINET_PTON(addr.ss_family, ip,
                                   &(((SOCKADDR_IN6*)&addr)->sin6_addr)) <= 0) {
                    WOLFSSL_MSG("XINET_PTON error");
                    return SOCKET_ERROR_E;
                }
                ((SOCKADDR_IN6*)&addr)->sin6_port = XHTONS(port);

                /* peer sa is free'd in SSL_ResourceFree */
                if ((ret = wolfSSL_dtls_set_peer(ssl, (SOCKADDR_IN6*)&addr,
                                         sizeof(SOCKADDR_IN6)))!= WOLFSSL_SUCCESS) {
                    WOLFSSL_MSG("Import DTLS peer info error");
                    return ret;
                }
            #endif /* WOLFSSL_IPV6 */
                break;

            default:
                WOLFSSL_MSG("Unknown address family");
                return BUFFER_E;
        }

        return WOLFSSL_SUCCESS;
    }
#endif /* WOLFSSL_SESSION_EXPORT */
#endif /* WOLFSSL_DTLS */


int wolfIO_Recv(SOCKET_T sd, char *buf, int sz, int rdFlags)
{
    int recvd;

    recvd = (int)RECV_FUNCTION(sd, buf, sz, rdFlags);
    recvd = TranslateReturnCode(recvd, sd);

    return recvd;
}

int wolfIO_Send(SOCKET_T sd, char *buf, int sz, int wrFlags)
{
    int sent;

    sent = (int)SEND_FUNCTION(sd, buf, sz, wrFlags);
    sent = TranslateReturnCode(sent, sd);

    return sent;
}

#endif /* USE_WOLFSSL_IO */


#ifdef HAVE_HTTP_CLIENT

#ifndef HAVE_IO_TIMEOUT
    #define io_timeout_sec 0
#else

    #ifndef DEFAULT_TIMEOUT_SEC
        #define DEFAULT_TIMEOUT_SEC 0 /* no timeout */
    #endif

    static int io_timeout_sec = DEFAULT_TIMEOUT_SEC;

    void wolfIO_SetTimeout(int to_sec)
    {
        io_timeout_sec = to_sec;
    }

    int wolfIO_SetBlockingMode(SOCKET_T sockfd, int non_blocking)
    {
        int ret = 0;

    #ifdef USE_WINDOWS_API
        unsigned long blocking = non_blocking;
        ret = ioctlsocket(sockfd, FIONBIO, &blocking);
        if (ret == SOCKET_ERROR)
            ret = -1;
    #else
        ret = fcntl(sockfd, F_GETFL, 0);
        if (ret >= 0) {
            if (non_blocking)
                ret |= O_NONBLOCK;
            else
                ret &= ~O_NONBLOCK;
            ret = fcntl(sockfd, F_SETFL, ret);
        }
    #endif
        if (ret < 0) {
            WOLFSSL_MSG("wolfIO_SetBlockingMode failed");
        }

        return ret;
    }

    int wolfIO_Select(SOCKET_T sockfd, int to_sec)
    {
        fd_set rfds, wfds;
        int nfds = 0;
        struct timeval timeout = { (to_sec > 0) ? to_sec : 0, 0};
        int ret;

    #ifndef USE_WINDOWS_API
        nfds = (int)sockfd + 1;
    #endif

        FD_ZERO(&rfds);
        FD_SET(sockfd, &rfds);
        wfds = rfds;

        ret = select(nfds, &rfds, &wfds, NULL, &timeout);
        if (ret == 0) {
        #ifdef DEBUG_HTTP
            printf("Timeout: %d\n", ret);
        #endif
            return HTTP_TIMEOUT;
        }
        else if (ret > 0) {
            if (FD_ISSET(sockfd, &wfds)) {
                if (!FD_ISSET(sockfd, &rfds)) {
                    return 0;
                }
            }
        }
        return SOCKET_ERROR_E;
    }
#endif /* HAVE_IO_TIMEOUT */

static int wolfIO_Word16ToString(char* d, word16 number)
{
    int i = 0;
    word16 order = 10000;
    word16 digit;

    if (d == NULL)
        return i;

    if (number == 0)
        d[i++] = '0';
    else {
        while (order) {
            digit = number / order;
            if (i > 0 || digit != 0)
                d[i++] = (char)digit + '0';
            if (digit != 0)
                number %= digit * order;

            order = (order > 1) ? order / 10 : 0;
        }
    }
    d[i] = 0; /* null terminate */

    return i;
}

int wolfIO_TcpConnect(SOCKET_T* sockfd, const char* ip, word16 port, int to_sec)
{
#ifdef HAVE_SOCKADDR
    int ret = 0;
    SOCKADDR_S addr;
    int sockaddr_len = sizeof(SOCKADDR_IN);
    /* use gethostbyname for c99 */
#if defined(HAVE_GETADDRINFO) && !defined(WOLF_C99)
    ADDRINFO hints;
    ADDRINFO* answer = NULL;
    char strPort[6];
#else
    HOSTENT* entry;
    SOCKADDR_IN *sin;
#endif

    if (sockfd == NULL || ip == NULL) {
        return -1;
    }

    XMEMSET(&addr, 0, sizeof(addr));

#ifdef WOLFIO_DEBUG
    printf("TCP Connect: %s:%d\n", ip, port);
#endif

    /* use gethostbyname for c99 */
#if defined(HAVE_GETADDRINFO) && !defined(WOLF_C99)
    XMEMSET(&hints, 0, sizeof(hints));
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_protocol = IPPROTO_TCP;

    if (wolfIO_Word16ToString(strPort, port) == 0) {
        WOLFSSL_MSG("invalid port number for responder");
        return -1;
    }

    if (getaddrinfo(ip, strPort, &hints, &answer) < 0 || answer == NULL) {
        WOLFSSL_MSG("no addr info for responder");
        return -1;
    }

    sockaddr_len = answer->ai_addrlen;
    XMEMCPY(&addr, answer->ai_addr, sockaddr_len);
    freeaddrinfo(answer);
#else
    entry = gethostbyname(ip);
    sin = (SOCKADDR_IN *)&addr;

    if (entry) {
        sin->sin_family = AF_INET;
        sin->sin_port = XHTONS(port);
        XMEMCPY(&sin->sin_addr.s_addr, entry->h_addr_list[0], entry->h_length);
    }
    else {
        WOLFSSL_MSG("no addr info for responder");
        return -1;
    }
#endif

    *sockfd = (SOCKET_T)socket(addr.ss_family, SOCK_STREAM, 0);
#ifdef USE_WINDOWS_API
    if (*sockfd == SOCKET_INVALID)
#else
    if (*sockfd <= SOCKET_INVALID)
#endif
    {
        WOLFSSL_MSG("bad socket fd, out of fds?");
        return -1;
    }

#ifdef HAVE_IO_TIMEOUT
    /* if timeout value provided then set socket non-blocking */
    if (to_sec > 0) {
        wolfIO_SetBlockingMode(*sockfd, 1);
    }
#else
    (void)to_sec;
#endif

    ret = connect(*sockfd, (SOCKADDR *)&addr, sockaddr_len);
#ifdef HAVE_IO_TIMEOUT
    if (ret != 0) {
        if ((errno == EINPROGRESS) && (to_sec > 0)) {
            /* wait for connect to complete */
            ret = wolfIO_Select(*sockfd, to_sec);

            /* restore blocking mode */
            wolfIO_SetBlockingMode(*sockfd, 0);
        }
    }
#endif
    if (ret != 0) {
        WOLFSSL_MSG("Responder tcp connect failed");
        CloseSocket(*sockfd);
        *sockfd = SOCKET_INVALID;
        return -1;
    }
    return ret;
#else
    (void)sockfd;
    (void)ip;
    (void)port;
    (void)to_sec;
    return -1;
#endif /* HAVE_SOCKADDR */
}

#ifndef HTTP_SCRATCH_BUFFER_SIZE
    #define HTTP_SCRATCH_BUFFER_SIZE 512
#endif
#ifndef MAX_URL_ITEM_SIZE
    #define MAX_URL_ITEM_SIZE   80
#endif

int wolfIO_DecodeUrl(const char* url, int urlSz, char* outName, char* outPath,
    word16* outPort)
{
    int result = -1;

    if (url == NULL || urlSz == 0) {
        if (outName)
            *outName = 0;
        if (outPath)
            *outPath = 0;
        if (outPort)
            *outPort = 0;
    }
    else {
        int i, cur;

        /* need to break the url down into scheme, address, and port */
        /*     "http://example.com:8080/" */
        /*     "http://[::1]:443/"        */
        if (XSTRNCMP(url, "http://", 7) == 0) {
            cur = 7;
        } else cur = 0;

        i = 0;
        if (url[cur] == '[') {
            cur++;
            /* copy until ']' */
            while (i < MAX_URL_ITEM_SIZE-1 && cur < urlSz && url[cur] != 0 &&
                    url[cur] != ']') {
                if (outName)
                    outName[i] = url[cur];
                i++; cur++;
            }
            cur++; /* skip ']' */
        }
        else {
            while (i < MAX_URL_ITEM_SIZE-1 && cur < urlSz && url[cur] != 0 &&
                    url[cur] != ':' && url[cur] != '/') {
                if (outName)
                    outName[i] = url[cur];
                i++; cur++;
            }
        }
        if (outName)
            outName[i] = 0;
        /* Need to pick out the path after the domain name */

        if (cur < urlSz && url[cur] == ':') {
            char port[6];
            int j;
            word32 bigPort = 0;
            i = 0;
            cur++;
            while (i < 6 && cur < urlSz && url[cur] != 0 && url[cur] != '/') {
                port[i] = url[cur];
                i++; cur++;
            }

            for (j = 0; j < i; j++) {
                if (port[j] < '0' || port[j] > '9') return -1;
                bigPort = (bigPort * 10) + (port[j] - '0');
            }
            if (outPort)
                *outPort = (word16)bigPort;
        }
        else if (outPort)
            *outPort = 80;


        if (cur < urlSz && url[cur] == '/') {
            i = 0;
            while (i < MAX_URL_ITEM_SIZE-1 && cur < urlSz && url[cur] != 0) {
                if (outPath)
                    outPath[i] = url[cur];
                i++; cur++;
            }
            if (outPath)
                outPath[i] = 0;
        }
        else if (outPath) {
            outPath[0] = '/';
            outPath[1] = 0;
        }

        result = 0;
    }

    return result;
}

static int wolfIO_HttpProcessResponseBuf(int sfd, byte **recvBuf,
    int* recvBufSz, int chunkSz, char* start, int len, int dynType, void* heap)
{
    byte* newRecvBuf = NULL;
    int newRecvSz = *recvBufSz + chunkSz;
    int pos = 0;

    WOLFSSL_MSG("Processing HTTP response");
#ifdef WOLFIO_DEBUG
    printf("HTTP Chunk %d->%d\n", *recvBufSz, chunkSz);
#endif

    (void)heap;
    (void)dynType;

    if (chunkSz < 0 || len < 0) {
        WOLFSSL_MSG("wolfIO_HttpProcessResponseBuf invalid chunk or length size");
        return MEMORY_E;
    }

    if (newRecvSz <= 0) {
        WOLFSSL_MSG("wolfIO_HttpProcessResponseBuf new receive size overflow");
        return MEMORY_E;
    }

    newRecvBuf = (byte*)XMALLOC(newRecvSz, heap, dynType);
    if (newRecvBuf == NULL) {
        WOLFSSL_MSG("wolfIO_HttpProcessResponseBuf malloc failed");
        return MEMORY_E;
    }

    /* if buffer already exists, then we are growing it */
    if (*recvBuf) {
        XMEMCPY(&newRecvBuf[pos], *recvBuf, *recvBufSz);
        XFREE(*recvBuf, heap, dynType);
        pos += *recvBufSz;
        *recvBuf = NULL;
    }

    /* copy the remainder of the httpBuf into the respBuf */
    if (len != 0) {
        if (pos + len <= newRecvSz) {
            XMEMCPY(&newRecvBuf[pos], start, len);
            pos += len;
        }
        else {
            WOLFSSL_MSG("wolfIO_HttpProcessResponseBuf bad size");
            XFREE(newRecvBuf, heap, dynType);
            return -1;
        }
    }

    /* receive the remainder of chunk */
    while (len < chunkSz) {
        int rxSz = wolfIO_Recv(sfd, (char*)&newRecvBuf[pos], chunkSz-len, 0);
        if (rxSz > 0) {
            len += rxSz;
            pos += rxSz;
        }
        else {
            WOLFSSL_MSG("wolfIO_HttpProcessResponseBuf recv failed");
            XFREE(newRecvBuf, heap, dynType);
            return -1;
        }
    }

    *recvBuf = newRecvBuf;
    *recvBufSz = newRecvSz;

    return 0;
}

int wolfIO_HttpProcessResponse(int sfd, const char** appStrList,
    byte** respBuf, byte* httpBuf, int httpBufSz, int dynType, void* heap)
{
    int result = 0;
    int len = 0;
    char *start, *end;
    int respBufSz = 0;
    int isChunked = 0, chunkSz = 0;
    enum phr_state { phr_init, phr_http_start, phr_have_length, phr_have_type,
                     phr_wait_end, phr_get_chunk_len, phr_get_chunk_data,
                     phr_http_end
    } state = phr_init;

    *respBuf = NULL;
    start = end = NULL;
    do {
        if (state == phr_get_chunk_data) {
            /* get chunk of data */
            result = wolfIO_HttpProcessResponseBuf(sfd, respBuf, &respBufSz,
                chunkSz, start, len, dynType, heap);

            state = (result != 0) ? phr_http_end : phr_get_chunk_len;
            end = NULL;
            len = 0;
        }

        /* read data if no \r\n or first time */
        if (end == NULL) {
            result = wolfIO_Recv(sfd, (char*)httpBuf+len, httpBufSz-len-1, 0);
            if (result > 0) {
                len += result;
                start = (char*)httpBuf;
                start[len] = 0;
            }
            else {
                WOLFSSL_MSG("wolfIO_HttpProcessResponse recv http from peer failed");
                return -1;
            }
        }
        end = XSTRSTR(start, "\r\n"); /* locate end */

        /* handle incomplete rx */
        if (end == NULL) {
            if (len != 0)
                XMEMMOVE(httpBuf, start, len);
            start = end = NULL;
        }
        /* when start is "\r\n" */
        else if (end == start) {
            /* if waiting for end or need chunk len */
            if (state == phr_wait_end || state == phr_get_chunk_len) {
                state = (isChunked) ? phr_get_chunk_len : phr_http_end;
                len -= 2; start += 2; /* skip \r\n */
             }
             else {
                WOLFSSL_MSG("wolfIO_HttpProcessResponse header ended early");
                return -1;
             }
        }
        else {
            *end = 0; /* null terminate */
            len -= (int)(end - start) + 2;
                /* adjust len to remove the first line including the /r/n */

        #ifdef WOLFIO_DEBUG
            printf("HTTP Resp: %s\n", start);
        #endif

            switch (state) {
                case phr_init:
                    if (XSTRLEN(start) < 15) { /* 15 is the length of the two
                                          constant strings we're about to
                                          compare against. */
                        WOLFSSL_MSG("wolfIO_HttpProcessResponse HTTP header too short.");
                        return -1;
                    }
                    if (XSTRNCASECMP(start, "HTTP/1", 6) == 0) {
                        start += 9;
                        if (XSTRNCASECMP(start, "200 OK", 6) != 0) {
                            WOLFSSL_MSG("wolfIO_HttpProcessResponse not OK");
                            return -1;
                        }
                        state = phr_http_start;
                    }
                    break;
                case phr_http_start:
                case phr_have_length:
                case phr_have_type:
                    if (XSTRLEN(start) < 13) { /* 13 is the shortest of the following
                                          next lines we're checking for. */
                        WOLFSSL_MSG("wolfIO_HttpProcessResponse content type is too short.");
                        return -1;
                    }

                    if (XSTRNCASECMP(start, "Content-Type:", 13) == 0) {
                        int i;

                        start += 13;
                        while (*start == ' ') start++;

                        /* try and match against appStrList */
                        i = 0;
                        while (appStrList[i] != NULL) {
                            if (XSTRNCASECMP(start, appStrList[i],
                                                XSTRLEN(appStrList[i])) == 0) {
                                break;
                            }
                            i++;
                        }
                        if (appStrList[i] == NULL) {
                            WOLFSSL_MSG("wolfIO_HttpProcessResponse appstr mismatch");
                            return -1;
                        }
                        state = (state == phr_http_start) ? phr_have_type : phr_wait_end;
                    }
                    else if (XSTRNCASECMP(start, "Content-Length:", 15) == 0) {
                        start += 15;
                        while (*start == ' ') start++;
                        chunkSz = XATOI(start);
                        state = (state == phr_http_start) ? phr_have_length : phr_wait_end;
                    }
                    else if (XSTRNCASECMP(start, "Transfer-Encoding:", 18) == 0) {
                        start += 18;
                        while (*start == ' ') start++;
                        if (XSTRNCASECMP(start, "chunked", 7) == 0) {
                            isChunked = 1;
                            state = (state == phr_http_start) ? phr_have_length : phr_wait_end;
                        }
                    }
                    break;
                case phr_get_chunk_len:
                    chunkSz = (int)strtol(start, NULL, 16); /* hex format */
                    state = (chunkSz == 0) ? phr_http_end : phr_get_chunk_data;
                    break;
                case phr_get_chunk_data:
                    /* processing for chunk data done above, since \r\n isn't required */
                case phr_wait_end:
                case phr_http_end:
                    /* do nothing */
                    break;
            } /* switch (state) */

            /* skip to end plus \r\n */
            start = end + 2;
        }
    } while (state != phr_http_end);

    if (!isChunked) {
        result = wolfIO_HttpProcessResponseBuf(sfd, respBuf, &respBufSz, chunkSz,
                                                    start, len, dynType, heap);
    }

    if (result >= 0) {
        result = respBufSz;
    }
    else {
        WOLFSSL_ERROR(result);
    }

    return result;
}
int wolfIO_HttpBuildRequest(const char *reqType, const char *domainName,
                               const char *path, int pathLen, int reqSz, const char *contentType,
                               byte *buf, int bufSize)
{
    return wolfIO_HttpBuildRequest_ex(reqType, domainName, path, pathLen, reqSz, contentType, "", buf, bufSize);
}

    int wolfIO_HttpBuildRequest_ex(const char *reqType, const char *domainName,
                                const char *path, int pathLen, int reqSz, const char *contentType,
                                const char *exHdrs, byte *buf, int bufSize)
    {
    word32 reqTypeLen, domainNameLen, reqSzStrLen, contentTypeLen, exHdrsLen, maxLen;
    char reqSzStr[6];
    char* req = (char*)buf;
    const char* blankStr = " ";
    const char* http11Str = " HTTP/1.1";
    const char* hostStr = "\r\nHost: ";
    const char* contentLenStr = "\r\nContent-Length: ";
    const char* contentTypeStr = "\r\nContent-Type: ";
    const char* singleCrLfStr = "\r\n";
    const char* doubleCrLfStr = "\r\n\r\n";
    word32 blankStrLen, http11StrLen, hostStrLen, contentLenStrLen,
        contentTypeStrLen, singleCrLfStrLen, doubleCrLfStrLen;

    reqTypeLen = (word32)XSTRLEN(reqType);
    domainNameLen = (word32)XSTRLEN(domainName);
    reqSzStrLen = wolfIO_Word16ToString(reqSzStr, (word16)reqSz);
    contentTypeLen = (word32)XSTRLEN(contentType);

    blankStrLen = (word32)XSTRLEN(blankStr);
    http11StrLen = (word32)XSTRLEN(http11Str);
    hostStrLen = (word32)XSTRLEN(hostStr);
    contentLenStrLen = (word32)XSTRLEN(contentLenStr);
    contentTypeStrLen = (word32)XSTRLEN(contentTypeStr);

    if(exHdrs){
        singleCrLfStrLen = (word32)XSTRLEN(singleCrLfStr);
        exHdrsLen = (word32)XSTRLEN(exHdrs);
    } else {
        singleCrLfStrLen = 0;
        exHdrsLen = 0;
    }

    doubleCrLfStrLen = (word32)XSTRLEN(doubleCrLfStr);

    /* determine max length and check it */
    maxLen =
        reqTypeLen +
        blankStrLen +
        pathLen +
        http11StrLen +
        hostStrLen +
        domainNameLen +
        contentLenStrLen +
        reqSzStrLen +
        contentTypeStrLen +
        contentTypeLen +
        singleCrLfStrLen +
        exHdrsLen +
        doubleCrLfStrLen +
        1 /* null term */;
    if (maxLen > (word32)bufSize)
        return 0;

    XSTRNCPY((char*)buf, reqType, bufSize);
    buf += reqTypeLen; bufSize -= reqTypeLen;
    XSTRNCPY((char*)buf, blankStr, bufSize);
    buf += blankStrLen; bufSize -= blankStrLen;
    XSTRNCPY((char*)buf, path, bufSize);
    buf += pathLen; bufSize -= pathLen;
    XSTRNCPY((char*)buf, http11Str, bufSize);
    buf += http11StrLen; bufSize -= http11StrLen;
    if (domainNameLen > 0) {
        XSTRNCPY((char*)buf, hostStr, bufSize);
        buf += hostStrLen; bufSize -= hostStrLen;
        XSTRNCPY((char*)buf, domainName, bufSize);
        buf += domainNameLen; bufSize -= domainNameLen;
    }
    if (reqSz > 0 && reqSzStrLen > 0) {
        XSTRNCPY((char*)buf, contentLenStr, bufSize);
        buf += contentLenStrLen; bufSize -= contentLenStrLen;
        XSTRNCPY((char*)buf, reqSzStr, bufSize);
        buf += reqSzStrLen; bufSize -= reqSzStrLen;
    }
    if (contentTypeLen > 0) {
        XSTRNCPY((char*)buf, contentTypeStr, bufSize);
        buf += contentTypeStrLen; bufSize -= contentTypeStrLen;
        XSTRNCPY((char*)buf, contentType, bufSize);
        buf += contentTypeLen; bufSize -= contentTypeLen;
    }
    if (exHdrsLen > 0)
    {
        XSTRNCPY((char *)buf, singleCrLfStr, bufSize);
        buf += singleCrLfStrLen;
        bufSize -= singleCrLfStrLen;
        XSTRNCPY((char *)buf, exHdrs, bufSize);
        buf += exHdrsLen;
        bufSize -= exHdrsLen;
    }
    XSTRNCPY((char*)buf, doubleCrLfStr, bufSize);
    buf += doubleCrLfStrLen;

#ifdef WOLFIO_DEBUG
    printf("HTTP %s: %s", reqType, req);
#endif

    /* calculate actual length based on original and new pointer */
    return (int)((char*)buf - req);
}


#ifdef HAVE_OCSP

int wolfIO_HttpBuildRequestOcsp(const char* domainName, const char* path,
                                    int ocspReqSz, byte* buf, int bufSize)
{
    const char *cacheCtl = "Cache-Control: no-cache";
    return wolfIO_HttpBuildRequest_ex("POST", domainName, path, (int)XSTRLEN(path),
        ocspReqSz, "application/ocsp-request", cacheCtl, buf, bufSize);
}

/* return: >0 OCSP Response Size
 *         -1 error */
int wolfIO_HttpProcessResponseOcsp(int sfd, byte** respBuf,
                                       byte* httpBuf, int httpBufSz, void* heap)
{
    const char* appStrList[] = {
        "application/ocsp-response",
        NULL
    };

    return wolfIO_HttpProcessResponse(sfd, appStrList,
        respBuf, httpBuf, httpBufSz, DYNAMIC_TYPE_OCSP, heap);
}

/* in default wolfSSL callback ctx is the heap pointer */
int EmbedOcspLookup(void* ctx, const char* url, int urlSz,
                        byte* ocspReqBuf, int ocspReqSz, byte** ocspRespBuf)
{
    SOCKET_T sfd = SOCKET_INVALID;
    word16   port;
    int      ret = -1;
#ifdef WOLFSSL_SMALL_STACK
    char*    path;
    char*    domainName;
#else
    char     path[MAX_URL_ITEM_SIZE];
    char     domainName[MAX_URL_ITEM_SIZE];
#endif

#ifdef WOLFSSL_SMALL_STACK
    path = (char*)XMALLOC(MAX_URL_ITEM_SIZE, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (path == NULL)
        return MEMORY_E;

    domainName = (char*)XMALLOC(MAX_URL_ITEM_SIZE, NULL,
            DYNAMIC_TYPE_TMP_BUFFER);
    if (domainName == NULL) {
        XFREE(path, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        return MEMORY_E;
    }
#endif

    if (ocspReqBuf == NULL || ocspReqSz == 0) {
        WOLFSSL_MSG("OCSP request is required for lookup");
    }
    else if (ocspRespBuf == NULL) {
        WOLFSSL_MSG("Cannot save OCSP response");
    }
    else if (wolfIO_DecodeUrl(url, urlSz, domainName, path, &port) < 0) {
        WOLFSSL_MSG("Unable to decode OCSP URL");
    }
    else {
        /* Note, the library uses the EmbedOcspRespFree() callback to
         * free this buffer. */
        int   httpBufSz = HTTP_SCRATCH_BUFFER_SIZE;
        byte* httpBuf   = (byte*)XMALLOC(httpBufSz, ctx, DYNAMIC_TYPE_OCSP);

        if (httpBuf == NULL) {
            WOLFSSL_MSG("Unable to create OCSP response buffer");
        }
        else {
            httpBufSz = wolfIO_HttpBuildRequestOcsp(domainName, path, ocspReqSz,
                                                            httpBuf, httpBufSz);

            ret = wolfIO_TcpConnect(&sfd, domainName, port, io_timeout_sec);
            if (ret != 0) {
                WOLFSSL_MSG("OCSP Responder connection failed");
            }
            else if (wolfIO_Send(sfd, (char*)httpBuf, httpBufSz, 0) !=
                                                                    httpBufSz) {
                WOLFSSL_MSG("OCSP http request failed");
            }
            else if (wolfIO_Send(sfd, (char*)ocspReqBuf, ocspReqSz, 0) !=
                                                                    ocspReqSz) {
                WOLFSSL_MSG("OCSP ocsp request failed");
            }
            else {
                ret = wolfIO_HttpProcessResponseOcsp(sfd, ocspRespBuf, httpBuf,
                                                 HTTP_SCRATCH_BUFFER_SIZE, ctx);
            }
            if (sfd != SOCKET_INVALID)
                CloseSocket(sfd);
            XFREE(httpBuf, ctx, DYNAMIC_TYPE_OCSP);
        }
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(path,       NULL, DYNAMIC_TYPE_TMP_BUFFER);
    XFREE(domainName, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

/* in default callback ctx is heap hint */
void EmbedOcspRespFree(void* ctx, byte *resp)
{
    if (resp)
        XFREE(resp, ctx, DYNAMIC_TYPE_OCSP);

    (void)ctx;
}
#endif /* HAVE_OCSP */


#if defined(HAVE_CRL) && defined(HAVE_CRL_IO)

int wolfIO_HttpBuildRequestCrl(const char* url, int urlSz,
    const char* domainName, byte* buf, int bufSize)
{
    const char *cacheCtl = "Cache-Control: no-cache";
    return wolfIO_HttpBuildRequest_ex("GET", domainName, url, urlSz, 0, "",
                                   cacheCtl, buf, bufSize);
}

int wolfIO_HttpProcessResponseCrl(WOLFSSL_CRL* crl, int sfd, byte* httpBuf,
    int httpBufSz)
{
    int result;
    byte *respBuf = NULL;

    const char* appStrList[] = {
        "application/pkix-crl",
        "application/x-pkcs7-crl",
        NULL
    };

    result = wolfIO_HttpProcessResponse(sfd, appStrList,
        &respBuf, httpBuf, httpBufSz, DYNAMIC_TYPE_CRL, crl->heap);
    if (result >= 0) {
        result = BufferLoadCRL(crl, respBuf, result, WOLFSSL_FILETYPE_ASN1, 0);
    }
    XFREE(respBuf, crl->heap, DYNAMIC_TYPE_CRL);

    return result;
}

int EmbedCrlLookup(WOLFSSL_CRL* crl, const char* url, int urlSz)
{
    SOCKET_T sfd = SOCKET_INVALID;
    word16   port;
    int      ret = -1;
#ifdef WOLFSSL_SMALL_STACK
    char*    domainName;
#else
    char     domainName[MAX_URL_ITEM_SIZE];
#endif

#ifdef WOLFSSL_SMALL_STACK
    domainName = (char*)XMALLOC(MAX_URL_ITEM_SIZE, crl->heap,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (domainName == NULL) {
        return MEMORY_E;
    }
#endif

    if (wolfIO_DecodeUrl(url, urlSz, domainName, NULL, &port) < 0) {
        WOLFSSL_MSG("Unable to decode CRL URL");
    }
    else {
        int   httpBufSz = HTTP_SCRATCH_BUFFER_SIZE;
        byte* httpBuf   = (byte*)XMALLOC(httpBufSz, crl->heap,
                                                              DYNAMIC_TYPE_CRL);
        if (httpBuf == NULL) {
            WOLFSSL_MSG("Unable to create CRL response buffer");
        }
        else {
            httpBufSz = wolfIO_HttpBuildRequestCrl(url, urlSz, domainName,
                httpBuf, httpBufSz);

            ret = wolfIO_TcpConnect(&sfd, domainName, port, io_timeout_sec);
            if (ret != 0) {
                WOLFSSL_MSG("CRL connection failed");
            }
            else if (wolfIO_Send(sfd, (char*)httpBuf, httpBufSz, 0)
                                                                 != httpBufSz) {
                WOLFSSL_MSG("CRL http get failed");
            }
            else {
                ret = wolfIO_HttpProcessResponseCrl(crl, sfd, httpBuf,
                                                      HTTP_SCRATCH_BUFFER_SIZE);
            }
            if (sfd != SOCKET_INVALID)
                CloseSocket(sfd);
            XFREE(httpBuf, crl->heap, DYNAMIC_TYPE_CRL);
        }
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(domainName, crl->heap, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}
#endif /* HAVE_CRL && HAVE_CRL_IO */

#endif /* HAVE_HTTP_CLIENT */



void wolfSSL_CTX_SetIORecv(WOLFSSL_CTX *ctx, CallbackIORecv CBIORecv)
{
    if (ctx) {
        ctx->CBIORecv = CBIORecv;
    #ifdef OPENSSL_EXTRA
        ctx->cbioFlag |= WOLFSSL_CBIO_RECV;
    #endif
    }
}


void wolfSSL_CTX_SetIOSend(WOLFSSL_CTX *ctx, CallbackIOSend CBIOSend)
{
    if (ctx) {
        ctx->CBIOSend = CBIOSend;
    #ifdef OPENSSL_EXTRA
        ctx->cbioFlag |= WOLFSSL_CBIO_SEND;
    #endif
    }
}


/* sets the IO callback to use for receives at WOLFSSL level */
void wolfSSL_SSLSetIORecv(WOLFSSL *ssl, CallbackIORecv CBIORecv)
{
    if (ssl) {
        ssl->CBIORecv = CBIORecv;
    #ifdef OPENSSL_EXTRA
        ssl->cbioFlag |= WOLFSSL_CBIO_RECV;
    #endif
    }
}


/* sets the IO callback to use for sends at WOLFSSL level */
void wolfSSL_SSLSetIOSend(WOLFSSL *ssl, CallbackIOSend CBIOSend)
{
    if (ssl) {
        ssl->CBIOSend = CBIOSend;
    #ifdef OPENSSL_EXTRA
        ssl->cbioFlag |= WOLFSSL_CBIO_SEND;
    #endif
    }
}


void wolfSSL_SetIOReadCtx(WOLFSSL* ssl, void *rctx)
{
    if (ssl)
        ssl->IOCB_ReadCtx = rctx;
}


void wolfSSL_SetIOWriteCtx(WOLFSSL* ssl, void *wctx)
{
    if (ssl)
        ssl->IOCB_WriteCtx = wctx;
}


void* wolfSSL_GetIOReadCtx(WOLFSSL* ssl)
{
    if (ssl)
        return ssl->IOCB_ReadCtx;

    return NULL;
}


void* wolfSSL_GetIOWriteCtx(WOLFSSL* ssl)
{
    if (ssl)
        return ssl->IOCB_WriteCtx;

    return NULL;
}


void wolfSSL_SetIOReadFlags(WOLFSSL* ssl, int flags)
{
    if (ssl)
        ssl->rflags = flags;
}


void wolfSSL_SetIOWriteFlags(WOLFSSL* ssl, int flags)
{
    if (ssl)
        ssl->wflags = flags;
}


#ifdef WOLFSSL_DTLS

void wolfSSL_CTX_SetGenCookie(WOLFSSL_CTX* ctx, CallbackGenCookie cb)
{
    if (ctx)
        ctx->CBIOCookie = cb;
}


void wolfSSL_SetCookieCtx(WOLFSSL* ssl, void *ctx)
{
    if (ssl)
        ssl->IOCB_CookieCtx = ctx;
}


void* wolfSSL_GetCookieCtx(WOLFSSL* ssl)
{
    if (ssl)
        return ssl->IOCB_CookieCtx;

    return NULL;
}

#ifdef WOLFSSL_SESSION_EXPORT

void wolfSSL_CTX_SetIOGetPeer(WOLFSSL_CTX* ctx, CallbackGetPeer cb)
{
    if (ctx)
        ctx->CBGetPeer = cb;
}


void wolfSSL_CTX_SetIOSetPeer(WOLFSSL_CTX* ctx, CallbackSetPeer cb)
{
    if (ctx)
        ctx->CBSetPeer = cb;
}

#endif /* WOLFSSL_SESSION_EXPORT */
#endif /* WOLFSSL_DTLS */


#ifdef HAVE_NETX

/* The NetX receive callback
 *  return :  bytes read, or error
 */
int NetX_Receive(WOLFSSL *ssl, char *buf, int sz, void *ctx)
{
    NetX_Ctx* nxCtx = (NetX_Ctx*)ctx;
    ULONG left;
    ULONG total;
    ULONG copied = 0;
    UINT  status;

    (void)ssl;

    if (nxCtx == NULL || nxCtx->nxSocket == NULL) {
        WOLFSSL_MSG("NetX Recv NULL parameters");
        return WOLFSSL_CBIO_ERR_GENERAL;
    }

    if (nxCtx->nxPacket == NULL) {
        status = nx_tcp_socket_receive(nxCtx->nxSocket, &nxCtx->nxPacket,
                                       nxCtx->nxWait);
        if (status != NX_SUCCESS) {
            WOLFSSL_MSG("NetX Recv receive error");
            return WOLFSSL_CBIO_ERR_GENERAL;
        }
    }

    if (nxCtx->nxPacket) {
        status = nx_packet_length_get(nxCtx->nxPacket, &total);
        if (status != NX_SUCCESS) {
            WOLFSSL_MSG("NetX Recv length get error");
            return WOLFSSL_CBIO_ERR_GENERAL;
        }

        left = total - nxCtx->nxOffset;
        status = nx_packet_data_extract_offset(nxCtx->nxPacket, nxCtx->nxOffset,
                                               buf, sz, &copied);
        if (status != NX_SUCCESS) {
            WOLFSSL_MSG("NetX Recv data extract offset error");
            return WOLFSSL_CBIO_ERR_GENERAL;
        }

        nxCtx->nxOffset += copied;

        if (copied == left) {
            WOLFSSL_MSG("NetX Recv Drained packet");
            nx_packet_release(nxCtx->nxPacket);
            nxCtx->nxPacket = NULL;
            nxCtx->nxOffset = 0;
        }
    }

    return copied;
}


/* The NetX send callback
 *  return : bytes sent, or error
 */
int NetX_Send(WOLFSSL* ssl, char *buf, int sz, void *ctx)
{
    NetX_Ctx*       nxCtx = (NetX_Ctx*)ctx;
    NX_PACKET*      packet;
    NX_PACKET_POOL* pool;   /* shorthand */
    UINT            status;

    (void)ssl;

    if (nxCtx == NULL || nxCtx->nxSocket == NULL) {
        WOLFSSL_MSG("NetX Send NULL parameters");
        return WOLFSSL_CBIO_ERR_GENERAL;
    }

    pool = nxCtx->nxSocket->nx_tcp_socket_ip_ptr->nx_ip_default_packet_pool;
    status = nx_packet_allocate(pool, &packet, NX_TCP_PACKET,
                                nxCtx->nxWait);
    if (status != NX_SUCCESS) {
        WOLFSSL_MSG("NetX Send packet alloc error");
        return WOLFSSL_CBIO_ERR_GENERAL;
    }

    status = nx_packet_data_append(packet, buf, sz, pool, nxCtx->nxWait);
    if (status != NX_SUCCESS) {
        nx_packet_release(packet);
        WOLFSSL_MSG("NetX Send data append error");
        return WOLFSSL_CBIO_ERR_GENERAL;
    }

    status = nx_tcp_socket_send(nxCtx->nxSocket, packet, nxCtx->nxWait);
    if (status != NX_SUCCESS) {
        nx_packet_release(packet);
        WOLFSSL_MSG("NetX Send socket send error");
        return WOLFSSL_CBIO_ERR_GENERAL;
    }

    return sz;
}


/* like set_fd, but for default NetX context */
void wolfSSL_SetIO_NetX(WOLFSSL* ssl, NX_TCP_SOCKET* nxSocket, ULONG waitOption)
{
    if (ssl) {
        ssl->nxCtx.nxSocket = nxSocket;
        ssl->nxCtx.nxWait   = waitOption;
    }
}

#endif /* HAVE_NETX */


#ifdef MICRIUM

/* Micrium uTCP/IP port, using the NetSock API
 * TCP and UDP are currently supported with the callbacks below.
 *
 * WOLFSSL_SESSION_EXPORT is not yet supported, would need EmbedGetPeer()
 * and EmbedSetPeer() callbacks implemented.
 *
 * HAVE_CRL is not yet supported, would need an EmbedCrlLookup()
 * callback implemented.
 *
 * HAVE_OCSP is not yet supported, would need an EmbedOCSPLookup()
 * callback implemented.
 */

/* The Micrium uTCP/IP send callback
 * return : bytes sent, or error
 */
int MicriumSend(WOLFSSL* ssl, char* buf, int sz, void* ctx)
{
    NET_SOCK_ID sd = *(int*)ctx;
    NET_SOCK_RTN_CODE ret;
    NET_ERR err;

    ret = NetSock_TxData(sd, buf, sz, ssl->wflags, &err);
    if (ret < 0) {
        WOLFSSL_MSG("Embed Send error");

        if (err == NET_ERR_TX) {
            WOLFSSL_MSG("\tWould block");
            return WOLFSSL_CBIO_ERR_WANT_WRITE;

        } else {
            WOLFSSL_MSG("\tGeneral error");
            return WOLFSSL_CBIO_ERR_GENERAL;
        }
    }

    return ret;
}

/* The Micrium uTCP/IP receive callback
 *  return : nb bytes read, or error
 */
int MicriumReceive(WOLFSSL *ssl, char *buf, int sz, void *ctx)
{
    NET_SOCK_ID sd = *(int*)ctx;
    NET_SOCK_RTN_CODE ret;
    NET_ERR err;

#ifdef WOLFSSL_DTLS
    {
        int dtls_timeout = wolfSSL_dtls_get_current_timeout(ssl);
        if (wolfSSL_dtls(ssl)
                     && !wolfSSL_dtls_get_using_nonblock(ssl)
                     && dtls_timeout != 0) {
            /* needs timeout in milliseconds */
            NetSock_CfgTimeoutRxQ_Set(sd, dtls_timeout * 1000, &err);
            if (err != NET_SOCK_ERR_NONE) {
                WOLFSSL_MSG("NetSock_CfgTimeoutRxQ_Set failed");
            }
        }
    }
#endif

    ret = NetSock_RxData(sd, buf, sz, ssl->rflags, &err);
    if (ret < 0) {
        WOLFSSL_MSG("Embed Receive error");

        if (err == NET_ERR_RX || err == NET_SOCK_ERR_RX_Q_EMPTY ||
            err == NET_ERR_FAULT_LOCK_ACQUIRE) {
            if (!wolfSSL_dtls(ssl) || wolfSSL_dtls_get_using_nonblock(ssl)) {
                WOLFSSL_MSG("\tWould block");
                return WOLFSSL_CBIO_ERR_WANT_READ;
            }
            else {
                WOLFSSL_MSG("\tSocket timeout");
                return WOLFSSL_CBIO_ERR_TIMEOUT;
            }

        } else if (err == NET_SOCK_ERR_CLOSED) {
            WOLFSSL_MSG("Embed receive connection closed");
            return WOLFSSL_CBIO_ERR_CONN_CLOSE;

        } else {
            WOLFSSL_MSG("\tGeneral error");
            return WOLFSSL_CBIO_ERR_GENERAL;
        }
    }

    return ret;
}

/* The Micrium uTCP/IP receivefrom callback
 *  return : nb bytes read, or error
 */
int MicriumReceiveFrom(WOLFSSL *ssl, char *buf, int sz, void *ctx)
{
    WOLFSSL_DTLS_CTX* dtlsCtx = (WOLFSSL_DTLS_CTX*)ctx;
    NET_SOCK_ID       sd = dtlsCtx->rfd;
    NET_SOCK_ADDR     peer;
    NET_SOCK_ADDR_LEN peerSz = sizeof(peer);
    NET_SOCK_RTN_CODE ret;
    NET_ERR err;
    int dtls_timeout = wolfSSL_dtls_get_current_timeout(ssl);

    WOLFSSL_ENTER("MicriumReceiveFrom()");

    if (ssl->options.handShakeDone)
        dtls_timeout = 0;

    if (!wolfSSL_dtls_get_using_nonblock(ssl)) {
        /* needs timeout in milliseconds */
        NetSock_CfgTimeoutRxQ_Set(sd, dtls_timeout * 1000, &err);
        if (err != NET_SOCK_ERR_NONE) {
            WOLFSSL_MSG("NetSock_CfgTimeoutRxQ_Set failed");
        }
    }

    ret = NetSock_RxDataFrom(sd, buf, sz, ssl->rflags, &peer, &peerSz,
                             0, 0, 0, &err);
    if (ret < 0) {
        WOLFSSL_MSG("Embed Receive From error");

        if (err == NET_ERR_RX || err == NET_SOCK_ERR_RX_Q_EMPTY ||
            err == NET_ERR_FAULT_LOCK_ACQUIRE) {
            if (wolfSSL_dtls_get_using_nonblock(ssl)) {
                WOLFSSL_MSG("\tWould block");
                return WOLFSSL_CBIO_ERR_WANT_READ;
            }
            else {
                WOLFSSL_MSG("\tSocket timeout");
                return WOLFSSL_CBIO_ERR_TIMEOUT;
            }
        } else {
            WOLFSSL_MSG("\tGeneral error");
            return WOLFSSL_CBIO_ERR_GENERAL;
        }
    }
    else {
        if (dtlsCtx->peer.sz > 0
                && peerSz != (NET_SOCK_ADDR_LEN)dtlsCtx->peer.sz
                && XMEMCMP(&peer, dtlsCtx->peer.sa, peerSz) != 0) {
            WOLFSSL_MSG("\tIgnored packet from invalid peer");
            return WOLFSSL_CBIO_ERR_WANT_READ;
        }
    }

    return ret;
}

/* The Micrium uTCP/IP sendto callback
 *  return : nb bytes sent, or error
 */
int MicriumSendTo(WOLFSSL* ssl, char *buf, int sz, void *ctx)
{
    WOLFSSL_DTLS_CTX* dtlsCtx = (WOLFSSL_DTLS_CTX*)ctx;
    NET_SOCK_ID sd = dtlsCtx->wfd;
    NET_SOCK_RTN_CODE ret;
    NET_ERR err;

    WOLFSSL_ENTER("MicriumSendTo()");

    ret = NetSock_TxDataTo(sd, buf, sz, ssl->wflags,
                           (NET_SOCK_ADDR*)dtlsCtx->peer.sa,
                           (NET_SOCK_ADDR_LEN)dtlsCtx->peer.sz,
                           &err);
    if (err < 0) {
        WOLFSSL_MSG("Embed Send To error");

        if (err == NET_ERR_TX) {
            WOLFSSL_MSG("\tWould block");
            return WOLFSSL_CBIO_ERR_WANT_WRITE;

        } else {
            WOLFSSL_MSG("\tGeneral error");
            return WOLFSSL_CBIO_ERR_GENERAL;
        }
    }

    return ret;
}

/* Micrium DTLS Generate Cookie callback
 *  return : number of bytes copied into buf, or error
 */
int MicriumGenerateCookie(WOLFSSL* ssl, byte *buf, int sz, void *ctx)
{
    NET_SOCK_ADDR peer;
    NET_SOCK_ADDR_LEN peerSz = sizeof(peer);
    byte digest[WC_SHA_DIGEST_SIZE];
    int  ret = 0;

    (void)ctx;

    XMEMSET(&peer, 0, sizeof(peer));
    if (wolfSSL_dtls_get_peer(ssl, (void*)&peer,
                              (unsigned int*)&peerSz) != WOLFSSL_SUCCESS) {
        WOLFSSL_MSG("getpeername failed in MicriumGenerateCookie");
        return GEN_COOKIE_E;
    }

    ret = wc_ShaHash((byte*)&peer, peerSz, digest);
    if (ret != 0)
        return ret;

    if (sz > WC_SHA_DIGEST_SIZE)
        sz = WC_SHA_DIGEST_SIZE;
    XMEMCPY(buf, digest, sz);

    return sz;
}

#endif /* MICRIUM */

#if defined(WOLFSSL_APACHE_MYNEWT) && !defined(WOLFSSL_LWIP)

#include <os/os_error.h>
#include <os/os_mbuf.h>
#include <os/os_mempool.h>

#define MB_NAME "wolfssl_mb"

typedef struct Mynewt_Ctx {
        struct mn_socket *mnSocket;          /* send/recv socket handler */
        struct mn_sockaddr_in mnSockAddrIn;  /* socket address */
        struct os_mbuf *mnPacket;            /* incoming packet handle
                                                for short reads */
        int reading;                         /* reading flag */

        /* private */
        void *mnMemBuffer;                   /* memory buffer for mempool */
        struct os_mempool mnMempool;         /* mempool */
        struct os_mbuf_pool mnMbufpool;      /* mbuf pool */
} Mynewt_Ctx;

void mynewt_ctx_clear(void *ctx) {
    Mynewt_Ctx *mynewt_ctx = (Mynewt_Ctx*)ctx;
    if(!mynewt_ctx) return;

    if(mynewt_ctx->mnPacket) {
        os_mbuf_free_chain(mynewt_ctx->mnPacket);
        mynewt_ctx->mnPacket = NULL;
    }
    os_mempool_clear(&mynewt_ctx->mnMempool);
    XFREE(mynewt_ctx->mnMemBuffer, 0, 0);
    XFREE(mynewt_ctx, 0, 0);
}

/* return Mynewt_Ctx instance */
void* mynewt_ctx_new() {
    int rc = 0;
    Mynewt_Ctx *mynewt_ctx;
    int mem_buf_count = MYNEWT_VAL(WOLFSSL_MNSOCK_MEM_BUF_COUNT);
    int mem_buf_size = MYNEWT_VAL(WOLFSSL_MNSOCK_MEM_BUF_SIZE);
    int mempool_bytes = OS_MEMPOOL_BYTES(mem_buf_count, mem_buf_size);

    mynewt_ctx = (Mynewt_Ctx *)XMALLOC(sizeof(struct Mynewt_Ctx),
                                       NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if(!mynewt_ctx) return NULL;

    XMEMSET(mynewt_ctx, 0, sizeof(Mynewt_Ctx));
    mynewt_ctx->mnMemBuffer = XMALLOC(mempool_bytes, 0, 0);
    if(!mynewt_ctx->mnMemBuffer) {
        mynewt_ctx_clear((void*)mynewt_ctx);
        return NULL;
    }

    rc = os_mempool_init(&mynewt_ctx->mnMempool,
                         mem_buf_count, mem_buf_size,
                         mynewt_ctx->mnMemBuffer, MB_NAME);
    if(rc != 0) {
        mynewt_ctx_clear((void*)mynewt_ctx);
        return NULL;
    }
    rc = os_mbuf_pool_init(&mynewt_ctx->mnMbufpool, &mynewt_ctx->mnMempool,
                           mem_buf_count, mem_buf_size);
    if(rc != 0) {
        mynewt_ctx_clear((void*)mynewt_ctx);
        return NULL;
    }

    return mynewt_ctx;
}

static void mynewt_sock_writable(void *arg, int err);
static void mynewt_sock_readable(void *arg, int err);
static const union mn_socket_cb mynewt_sock_cbs = {
    .socket.writable = mynewt_sock_writable,
    .socket.readable = mynewt_sock_readable,
};
static void mynewt_sock_writable(void *arg, int err)
{
    /* do nothing */
}
static void mynewt_sock_readable(void *arg, int err)
{
    Mynewt_Ctx *mynewt_ctx = (Mynewt_Ctx *)arg;
    if (err && mynewt_ctx->reading) {
        mynewt_ctx->reading = 0;
    }
}

/* The Mynewt receive callback
 *  return :  bytes read, or error
 */
int Mynewt_Receive(WOLFSSL *ssl, char *buf, int sz, void *ctx)
{
    Mynewt_Ctx *mynewt_ctx = (Mynewt_Ctx*)ctx;
    int rc = 0;
    struct mn_sockaddr_in from;
    struct os_mbuf *m;
    int read_sz = 0;
    uint16_t total;

    if (mynewt_ctx == NULL || mynewt_ctx->mnSocket == NULL) {
        WOLFSSL_MSG("Mynewt Recv NULL parameters");
        return WOLFSSL_CBIO_ERR_GENERAL;
    }

    if(mynewt_ctx->mnPacket == NULL) {
        mynewt_ctx->mnPacket = os_mbuf_get_pkthdr(&mynewt_ctx->mnMbufpool, 0);
        if(mynewt_ctx->mnPacket == NULL) {
            return MEMORY_E;
        }

        mynewt_ctx->reading = 1;
        while(mynewt_ctx->reading && rc == 0) {
            rc = mn_recvfrom(mynewt_ctx->mnSocket, &m, (struct mn_sockaddr *) &from);
            if(rc == MN_ECONNABORTED) {
                rc = 0;
                mynewt_ctx->reading = 0;
                break;
            }
            if (!(rc == 0 || rc == MN_EAGAIN)) {
                WOLFSSL_MSG("Mynewt Recv receive error");
                mynewt_ctx->reading = 0;
                break;
            }
            if(rc == 0) {
                int len = OS_MBUF_PKTLEN(m);
                if(len == 0) {
                    break;
                }
                rc = os_mbuf_appendfrom(mynewt_ctx->mnPacket, m, 0, len);
                if(rc != 0) {
                    WOLFSSL_MSG("Mynewt Recv os_mbuf_appendfrom error");
                    break;
                }
                os_mbuf_free_chain(m);
                m = NULL;
            } else if(rc == MN_EAGAIN) {
                /* continue to until reading all of packet data. */
                rc = 0;
                break;
            }
        }
        if(rc != 0) {
            mynewt_ctx->reading = 0;
            os_mbuf_free_chain(mynewt_ctx->mnPacket);
            mynewt_ctx->mnPacket = NULL;
            return rc;
        }
    }

    if(mynewt_ctx->mnPacket) {
        total = OS_MBUF_PKTLEN(mynewt_ctx->mnPacket);
        read_sz = (total >= sz)? sz : total;

        os_mbuf_copydata(mynewt_ctx->mnPacket, 0, read_sz, (void*)buf);
        os_mbuf_adj(mynewt_ctx->mnPacket, read_sz);

        if (read_sz == total) {
            WOLFSSL_MSG("Mynewt Recv Drained packet");
            os_mbuf_free_chain(mynewt_ctx->mnPacket);
            mynewt_ctx->mnPacket = NULL;
        }
    }

    return read_sz;
}

/* The Mynewt send callback
 *  return : bytes sent, or error
 */
int Mynewt_Send(WOLFSSL* ssl, char *buf, int sz, void *ctx)
{
    Mynewt_Ctx *mynewt_ctx = (Mynewt_Ctx*)ctx;
    int rc = 0;
    struct os_mbuf *m;
    int write_sz = 0;
    m = os_msys_get_pkthdr(sz, 0);
    if (!m) {
        WOLFSSL_MSG("Mynewt Send os_msys_get_pkthdr error");
        return WOLFSSL_CBIO_ERR_GENERAL;
    }
    rc = os_mbuf_copyinto(m, 0, buf, sz);
    if (rc != 0) {
        WOLFSSL_MSG("Mynewt Send os_mbuf_copyinto error");
        os_mbuf_free_chain(m);
        return rc;
    }
    rc = mn_sendto(mynewt_ctx->mnSocket, m, (struct mn_sockaddr *)&mynewt_ctx->mnSockAddrIn);
    if(rc != 0) {
        WOLFSSL_MSG("Mynewt Send mn_sendto error");
        os_mbuf_free_chain(m);
        return rc;
    }
    write_sz = sz;
    return write_sz;
}

/* like set_fd, but for default NetX context */
void wolfSSL_SetIO_Mynewt(WOLFSSL* ssl, struct mn_socket* mnSocket, struct mn_sockaddr_in* mnSockAddrIn)
{
    if (ssl && ssl->mnCtx) {
        Mynewt_Ctx *mynewt_ctx = (Mynewt_Ctx *)ssl->mnCtx;
        mynewt_ctx->mnSocket = mnSocket;
        memcpy(&mynewt_ctx->mnSockAddrIn, mnSockAddrIn, sizeof(struct mn_sockaddr_in));
        mn_socket_set_cbs(mynewt_ctx->mnSocket, mnSocket, &mynewt_sock_cbs);
    }
}

#endif /* defined(WOLFSSL_APACHE_MYNEWT) && !defined(WOLFSSL_LWIP) */

#ifdef WOLFSSL_UIP
#include <uip.h>
#include <stdio.h>

/* uIP TCP/IP port, using the native tcp/udp socket api.
 * TCP and UDP are currently supported with the callbacks below.
 *
 */
/* The uIP tcp send callback
 * return : bytes sent, or error
 */
int uIPSend(WOLFSSL* ssl, char* buf, int sz, void* _ctx)
{
    uip_wolfssl_ctx *ctx = (struct uip_wolfssl_ctx *)_ctx;
    int ret;
    unsigned int max_sendlen;
    int total_written = 0;
    (void)ssl;
    do {
        unsigned int bytes_left = sz - total_written;
        max_sendlen = tcp_socket_max_sendlen(&ctx->conn.tcp);
        if (bytes_left > max_sendlen) {
            printf("Send limited by buffer\r\n");
            bytes_left = max_sendlen;
        }
        if (bytes_left == 0) {
            printf("Buffer full!\r\n");
            break;
        }
        ret = tcp_socket_send(&ctx->conn.tcp, (unsigned char *)buf + total_written, bytes_left);
        if (ret <= 0)
            break;
        total_written += ret;
    } while(total_written < sz);
    if (total_written == 0)
        return WOLFSSL_CBIO_ERR_WANT_WRITE;
    return total_written;
}

int uIPSendTo(WOLFSSL* ssl, char* buf, int sz, void* _ctx)
{
    uip_wolfssl_ctx *ctx = (struct uip_wolfssl_ctx *)_ctx;
    int ret = 0;
    (void)ssl;
    ret = udp_socket_sendto(&ctx->conn.udp, (unsigned char *)buf, sz, &ctx->peer_addr, ctx->peer_port );
    if (ret == 0)
        return WOLFSSL_CBIO_ERR_WANT_WRITE;
    return ret;
}

/* The uIP uTCP/IP receive callback
 *  return : nb bytes read, or error
 */
int uIPReceive(WOLFSSL *ssl, char *buf, int sz, void *_ctx)
{
    uip_wolfssl_ctx *ctx = (uip_wolfssl_ctx *)_ctx;
    if (!ctx || !ctx->ssl_rx_databuf)
        return -1;
    (void)ssl;
    if (ctx->ssl_rb_len > 0) {
        if (sz > ctx->ssl_rb_len - ctx->ssl_rb_off)
            sz = ctx->ssl_rb_len - ctx->ssl_rb_off;
        XMEMCPY(buf, ctx->ssl_rx_databuf + ctx->ssl_rb_off, sz);
        ctx->ssl_rb_off += sz;
        if (ctx->ssl_rb_off >= ctx->ssl_rb_len) {
            ctx->ssl_rb_len = 0;
            ctx->ssl_rb_off = 0;
        }
        return sz;
    } else {
        return WOLFSSL_CBIO_ERR_WANT_READ;
    }
}

/* uIP DTLS Generate Cookie callback
 *  return : number of bytes copied into buf, or error
 */
int uIPGenerateCookie(WOLFSSL* ssl, byte *buf, int sz, void *_ctx)
{
    uip_wolfssl_ctx *ctx = (uip_wolfssl_ctx *)_ctx;
    byte token[32];
    byte digest[WC_SHA_DIGEST_SIZE];
    int  ret = 0;
    XMEMSET(token, 0, sizeof(token));
    XMEMCPY(token, &ctx->peer_addr, sizeof(uip_ipaddr_t));
    XMEMCPY(token + sizeof(uip_ipaddr_t), &ctx->peer_port, sizeof(word16));
    ret = wc_ShaHash(token, sizeof(uip_ipaddr_t) + sizeof(word16), digest);
    if (ret != 0)
        return ret;
    if (sz > WC_SHA_DIGEST_SIZE)
        sz = WC_SHA_DIGEST_SIZE;
    XMEMCPY(buf, digest, sz);
    return sz;
}

#endif /* WOLFSSL_UIP */

#ifdef WOLFSSL_GNRC

#include <net/sock.h>
#include <net/sock/tcp.h>
#include <stdio.h>

/* GNRC TCP/IP port, using the native tcp/udp socket api.
 * TCP and UDP are currently supported with the callbacks below.
 *
 */
/* The GNRC tcp send callback
 * return : bytes sent, or error
 */

int GNRC_SendTo(WOLFSSL* ssl, char* buf, int sz, void* _ctx)
{
    sock_tls_t *ctx = (sock_tls_t *)_ctx;
    int ret = 0;
    (void)ssl;
    if (!ctx)
        return WOLFSSL_CBIO_ERR_GENERAL;
    ret = sock_udp_send(&ctx->conn.udp, (unsigned char *)buf, sz, &ctx->peer_addr);
    if (ret == 0)
        return WOLFSSL_CBIO_ERR_WANT_WRITE;
    return ret;
}

/* The GNRC TCP/IP receive callback
 *  return : nb bytes read, or error
 */
int GNRC_ReceiveFrom(WOLFSSL *ssl, char *buf, int sz, void *_ctx)
{
    sock_udp_ep_t ep;
    int ret;
    uint32_t timeout = wolfSSL_dtls_get_current_timeout(ssl) * 1000000;
    sock_tls_t *ctx = (sock_tls_t *)_ctx;
    if (!ctx)
        return WOLFSSL_CBIO_ERR_GENERAL;
    (void)ssl;
    if (wolfSSL_get_using_nonblock(ctx->ssl)) {
        timeout = 0;
    }
    ret = sock_udp_recv(&ctx->conn.udp, buf, sz, timeout, &ep);
    if (ret > 0) {
        if (ctx->peer_addr.port == 0)
            XMEMCPY(&ctx->peer_addr, &ep, sizeof(sock_udp_ep_t));
    }
    if (ret == -ETIMEDOUT) {
        return WOLFSSL_CBIO_ERR_WANT_READ;
    }
    return ret;
}

/* GNRC DTLS Generate Cookie callback
 *  return : number of bytes copied into buf, or error
 */
#define GNRC_MAX_TOKEN_SIZE (32)
int GNRC_GenerateCookie(WOLFSSL* ssl, byte *buf, int sz, void *_ctx)
{
    sock_tls_t *ctx = (sock_tls_t *)_ctx;
    if (!ctx)
        return WOLFSSL_CBIO_ERR_GENERAL;
    byte token[GNRC_MAX_TOKEN_SIZE];
    byte digest[WC_SHA_DIGEST_SIZE];
    int  ret = 0;
    size_t token_size = sizeof(sock_udp_ep_t);
    (void)ssl;
    if (token_size > GNRC_MAX_TOKEN_SIZE)
        token_size = GNRC_MAX_TOKEN_SIZE;
    XMEMSET(token, 0, GNRC_MAX_TOKEN_SIZE);
    XMEMCPY(token, &ctx->peer_addr, token_size);
    ret = wc_ShaHash(token, token_size, digest);
    if (ret != 0)
        return ret;
    if (sz > WC_SHA_DIGEST_SIZE)
        sz = WC_SHA_DIGEST_SIZE;
    XMEMCPY(buf, digest, sz);
    return sz;
}

#endif /* WOLFSSL_GNRC */

#endif /* WOLFCRYPT_ONLY */
