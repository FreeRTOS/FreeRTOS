/* io.c
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

#ifdef _WIN32_WCE
    /* On WinCE winsock2.h must be included before windows.h for socket stuff */
    #include <winsock2.h>
#endif

#include <cyassl/internal.h>
#include <cyassl/error-ssl.h>

/* if user writes own I/O callbacks they can define CYASSL_USER_IO to remove
   automatic setting of default I/O functions EmbedSend() and EmbedReceive()
   but they'll still need SetCallback xxx() at end of file 
*/
#ifndef CYASSL_USER_IO

#ifdef HAVE_LIBZ
    #include "zlib.h"
#endif

#ifndef USE_WINDOWS_API
    #ifdef CYASSL_LWIP
        /* lwIP needs to be configured to use sockets API in this mode */
        /* LWIP_SOCKET 1 in lwip/opt.h or in build */
        #include "lwip/sockets.h"
        #include <errno.h>
        #ifndef LWIP_PROVIDE_ERRNO
            #define LWIP_PROVIDE_ERRNO 1
        #endif
    #elif defined(FREESCALE_MQX)
        #include <posix.h>
        #include <rtcs.h>
    #elif defined(CYASSL_MDK_ARM)
        #if defined(CYASSL_MDK5)
            #include "cmsis_os.h"
            #include "rl_fs.h" 
            #include "rl_net.h" 
        #else
            #include <rtl.h>
        #endif
        #undef RNG
        #include "CYASSL_MDK_ARM.h"
        #undef RNG
        #define RNG CyaSSL_RNG 
        /* for avoiding name conflict in "stm32f2xx.h" */
        static int errno;
    #elif defined(CYASSL_IAR_ARM)
        /* nothing */
    #else
        #include <sys/types.h>
        #include <errno.h>
        #ifndef EBSNET
            #include <unistd.h>
        #endif
        #include <fcntl.h>
        #if !(defined(DEVKITPRO) || defined(HAVE_RTP_SYS) || defined(EBSNET))
            #include <sys/socket.h>
            #include <arpa/inet.h>
            #include <netinet/in.h>
            #include <netdb.h>
            #ifdef __PPU
                #include <netex/errno.h>
            #else
                #include <sys/ioctl.h>
            #endif
        #endif
        #ifdef HAVE_RTP_SYS
            #include <socket.h>
        #endif
        #ifdef EBSNET
            #include "rtipapi.h"  /* errno */
            #include "socket.h"
        #endif
    #endif
#endif /* USE_WINDOWS_API */

#ifdef __sun
    #include <sys/filio.h>
#endif

#ifdef USE_WINDOWS_API 
    /* no epipe yet */
    #ifndef WSAEPIPE
        #define WSAEPIPE       -12345
    #endif
    #define SOCKET_EWOULDBLOCK WSAEWOULDBLOCK
    #define SOCKET_EAGAIN      WSAETIMEDOUT
    #define SOCKET_ECONNRESET  WSAECONNRESET
    #define SOCKET_EINTR       WSAEINTR
    #define SOCKET_EPIPE       WSAEPIPE
    #define SOCKET_ECONNREFUSED WSAENOTCONN
    #define SOCKET_ECONNABORTED WSAECONNABORTED
    #define close(s) closesocket(s)
#elif defined(__PPU)
    #define SOCKET_EWOULDBLOCK SYS_NET_EWOULDBLOCK
    #define SOCKET_EAGAIN      SYS_NET_EAGAIN
    #define SOCKET_ECONNRESET  SYS_NET_ECONNRESET
    #define SOCKET_EINTR       SYS_NET_EINTR
    #define SOCKET_EPIPE       SYS_NET_EPIPE
    #define SOCKET_ECONNREFUSED SYS_NET_ECONNREFUSED
    #define SOCKET_ECONNABORTED SYS_NET_ECONNABORTED
#elif defined(FREESCALE_MQX)
    /* RTCS doesn't have an EWOULDBLOCK error */
    #define SOCKET_EWOULDBLOCK EAGAIN
    #define SOCKET_EAGAIN      EAGAIN
    #define SOCKET_ECONNRESET  RTCSERR_TCP_CONN_RESET
    #define SOCKET_EINTR       EINTR
    #define SOCKET_EPIPE       EPIPE
    #define SOCKET_ECONNREFUSED RTCSERR_TCP_CONN_REFUSED
    #define SOCKET_ECONNABORTED RTCSERR_TCP_CONN_ABORTED
#elif defined(CYASSL_MDK_ARM)
    #if defined(CYASSL_MDK5)
        #define SOCKET_EWOULDBLOCK BSD_ERROR_WOULDBLOCK
        #define SOCKET_EAGAIN      BSD_ERROR_LOCKED
        #define SOCKET_ECONNRESET  BSD_ERROR_CLOSED
        #define SOCKET_EINTR       BSD_ERROR
        #define SOCKET_EPIPE       BSD_ERROR
        #define SOCKET_ECONNREFUSED BSD_ERROR
        #define SOCKET_ECONNABORTED BSD_ERROR
    #else
        #define SOCKET_EWOULDBLOCK SCK_EWOULDBLOCK
        #define SOCKET_EAGAIN      SCK_ELOCKED
        #define SOCKET_ECONNRESET  SCK_ECLOSED
        #define SOCKET_EINTR       SCK_ERROR
        #define SOCKET_EPIPE       SCK_ERROR
        #define SOCKET_ECONNREFUSED SCK_ERROR
        #define SOCKET_ECONNABORTED SCK_ERROR
    #endif
#else
    #define SOCKET_EWOULDBLOCK EWOULDBLOCK
    #define SOCKET_EAGAIN      EAGAIN
    #define SOCKET_ECONNRESET  ECONNRESET
    #define SOCKET_EINTR       EINTR
    #define SOCKET_EPIPE       EPIPE
    #define SOCKET_ECONNREFUSED ECONNREFUSED
    #define SOCKET_ECONNABORTED ECONNABORTED
#endif /* USE_WINDOWS_API */


#ifdef DEVKITPRO
    /* from network.h */
    int net_send(int, const void*, int, unsigned int);
    int net_recv(int, void*, int, unsigned int);
    #define SEND_FUNCTION net_send
    #define RECV_FUNCTION net_recv
#elif defined(CYASSL_LWIP)
    #define SEND_FUNCTION lwip_send
    #define RECV_FUNCTION lwip_recv
#else
    #define SEND_FUNCTION send
    #define RECV_FUNCTION recv
#endif


/* Translates return codes returned from 
 * send() and recv() if need be. 
 */
static INLINE int TranslateReturnCode(int old, int sd)
{
    (void)sd;

#ifdef FREESCALE_MQX
    if (old == 0) {
        errno = SOCKET_EWOULDBLOCK;
        return -1;  /* convert to BSD style wouldblock as error */
    }

    if (old < 0) {
        errno = RTCS_geterror(sd);
        if (errno == RTCSERR_TCP_CONN_CLOSING)
            return 0;   /* convert to BSD style closing */
    }
#endif

    return old;
}

static INLINE int LastError(void)
{
#ifdef USE_WINDOWS_API 
    return WSAGetLastError();
#elif defined(EBSNET)
    return xn_getlasterror();
#else
    return errno;
#endif
}

/* The receive embedded callback
 *  return : nb bytes read, or error
 */
int EmbedReceive(CYASSL *ssl, char *buf, int sz, void *ctx)
{
    int recvd;
    int err;
    int sd = *(int*)ctx;

#ifdef CYASSL_DTLS
    {
        int dtls_timeout = CyaSSL_dtls_get_current_timeout(ssl);
        if (CyaSSL_dtls(ssl)
                     && !CyaSSL_get_using_nonblock(ssl)
                     && dtls_timeout != 0) {
            #ifdef USE_WINDOWS_API
                DWORD timeout = dtls_timeout * 1000;
            #else
                struct timeval timeout;
                XMEMSET(&timeout, 0, sizeof(timeout));
                timeout.tv_sec = dtls_timeout;
            #endif
            if (setsockopt(sd, SOL_SOCKET, SO_RCVTIMEO, (char*)&timeout,
                           sizeof(timeout)) != 0) {
                CYASSL_MSG("setsockopt rcvtimeo failed");
            }
        }
    }
#endif

    recvd = (int)RECV_FUNCTION(sd, buf, sz, ssl->rflags);

    recvd = TranslateReturnCode(recvd, sd);

    if (recvd < 0) {
        err = LastError();
        CYASSL_MSG("Embed Receive error");

        if (err == SOCKET_EWOULDBLOCK || err == SOCKET_EAGAIN) {
            if (!CyaSSL_dtls(ssl) || CyaSSL_get_using_nonblock(ssl)) {
                CYASSL_MSG("    Would block");
                return CYASSL_CBIO_ERR_WANT_READ;
            }
            else {
                CYASSL_MSG("    Socket timeout");
                return CYASSL_CBIO_ERR_TIMEOUT;
            }
        }
        else if (err == SOCKET_ECONNRESET) {
            CYASSL_MSG("    Connection reset");
            return CYASSL_CBIO_ERR_CONN_RST;
        }
        else if (err == SOCKET_EINTR) {
            CYASSL_MSG("    Socket interrupted");
            return CYASSL_CBIO_ERR_ISR;
        }
        else if (err == SOCKET_ECONNREFUSED) {
            CYASSL_MSG("    Connection refused");
            return CYASSL_CBIO_ERR_WANT_READ;
        }
        else if (err == SOCKET_ECONNABORTED) {
            CYASSL_MSG("    Connection aborted");
            return CYASSL_CBIO_ERR_CONN_CLOSE;
        }
        else {
            CYASSL_MSG("    General error");
            return CYASSL_CBIO_ERR_GENERAL;
        }
    }
    else if (recvd == 0) {
        CYASSL_MSG("Embed receive connection closed");
        return CYASSL_CBIO_ERR_CONN_CLOSE;
    }

    return recvd;
}

/* The send embedded callback
 *  return : nb bytes sent, or error
 */
int EmbedSend(CYASSL* ssl, char *buf, int sz, void *ctx)
{
    int sd = *(int*)ctx;
    int sent;
    int len = sz;
    int err;

    sent = (int)SEND_FUNCTION(sd, &buf[sz - len], len, ssl->wflags);

    if (sent < 0) {
        err = LastError();
        CYASSL_MSG("Embed Send error");

        if (err == SOCKET_EWOULDBLOCK || err == SOCKET_EAGAIN) {
            CYASSL_MSG("    Would Block");
            return CYASSL_CBIO_ERR_WANT_WRITE;
        }
        else if (err == SOCKET_ECONNRESET) {
            CYASSL_MSG("    Connection reset");
            return CYASSL_CBIO_ERR_CONN_RST;
        }
        else if (err == SOCKET_EINTR) {
            CYASSL_MSG("    Socket interrupted");
            return CYASSL_CBIO_ERR_ISR;
        }
        else if (err == SOCKET_EPIPE) {
            CYASSL_MSG("    Socket EPIPE");
            return CYASSL_CBIO_ERR_CONN_CLOSE;
        }
        else {
            CYASSL_MSG("    General error");
            return CYASSL_CBIO_ERR_GENERAL;
        }
    }
 
    return sent;
}


#ifdef CYASSL_DTLS

#include <cyassl/ctaocrypt/sha.h>

#ifdef USE_WINDOWS_API
   #define XSOCKLENT int
#else
   #define XSOCKLENT socklen_t
#endif

#define SENDTO_FUNCTION sendto
#define RECVFROM_FUNCTION recvfrom


/* The receive embedded callback
 *  return : nb bytes read, or error
 */
int EmbedReceiveFrom(CYASSL *ssl, char *buf, int sz, void *ctx)
{
    CYASSL_DTLS_CTX* dtlsCtx = (CYASSL_DTLS_CTX*)ctx;
    int recvd;
    int err;
    int sd = dtlsCtx->fd;
    int dtls_timeout = CyaSSL_dtls_get_current_timeout(ssl);
    struct sockaddr_storage peer;
    XSOCKLENT peerSz = sizeof(peer);

    CYASSL_ENTER("EmbedReceiveFrom()");

    if (!CyaSSL_get_using_nonblock(ssl) && dtls_timeout != 0) {
        #ifdef USE_WINDOWS_API
            DWORD timeout = dtls_timeout * 1000;
        #else
            struct timeval timeout;
            XMEMSET(&timeout, 0, sizeof(timeout));
            timeout.tv_sec = dtls_timeout;
        #endif
        if (setsockopt(sd, SOL_SOCKET, SO_RCVTIMEO, (char*)&timeout,
                       sizeof(timeout)) != 0) {
                CYASSL_MSG("setsockopt rcvtimeo failed");
        }
    }

    recvd = (int)RECVFROM_FUNCTION(sd, buf, sz, ssl->rflags,
                                  (struct sockaddr*)&peer, &peerSz);

    recvd = TranslateReturnCode(recvd, sd);

    if (recvd < 0) {
        err = LastError();
        CYASSL_MSG("Embed Receive From error");

        if (err == SOCKET_EWOULDBLOCK || err == SOCKET_EAGAIN) {
            if (CyaSSL_get_using_nonblock(ssl)) {
                CYASSL_MSG("    Would block");
                return CYASSL_CBIO_ERR_WANT_READ;
            }
            else {
                CYASSL_MSG("    Socket timeout");
                return CYASSL_CBIO_ERR_TIMEOUT;
            }
        }
        else if (err == SOCKET_ECONNRESET) {
            CYASSL_MSG("    Connection reset");
            return CYASSL_CBIO_ERR_CONN_RST;
        }
        else if (err == SOCKET_EINTR) {
            CYASSL_MSG("    Socket interrupted");
            return CYASSL_CBIO_ERR_ISR;
        }
        else if (err == SOCKET_ECONNREFUSED) {
            CYASSL_MSG("    Connection refused");
            return CYASSL_CBIO_ERR_WANT_READ;
        }
        else {
            CYASSL_MSG("    General error");
            return CYASSL_CBIO_ERR_GENERAL;
        }
    }
    else {
        if (dtlsCtx->peer.sz > 0
                && peerSz != (XSOCKLENT)dtlsCtx->peer.sz
                && memcmp(&peer, dtlsCtx->peer.sa, peerSz) != 0) {
            CYASSL_MSG("    Ignored packet from invalid peer");
            return CYASSL_CBIO_ERR_WANT_READ;
        }
    }

    return recvd;
}


/* The send embedded callback
 *  return : nb bytes sent, or error
 */
int EmbedSendTo(CYASSL* ssl, char *buf, int sz, void *ctx)
{
    CYASSL_DTLS_CTX* dtlsCtx = (CYASSL_DTLS_CTX*)ctx;
    int sd = dtlsCtx->fd;
    int sent;
    int len = sz;
    int err;

    CYASSL_ENTER("EmbedSendTo()");

    sent = (int)SENDTO_FUNCTION(sd, &buf[sz - len], len, ssl->wflags,
                                dtlsCtx->peer.sa, dtlsCtx->peer.sz);
    if (sent < 0) {
        err = LastError();
        CYASSL_MSG("Embed Send To error");

        if (err == SOCKET_EWOULDBLOCK || err == SOCKET_EAGAIN) {
            CYASSL_MSG("    Would Block");
            return CYASSL_CBIO_ERR_WANT_WRITE;
        }
        else if (err == SOCKET_ECONNRESET) {
            CYASSL_MSG("    Connection reset");
            return CYASSL_CBIO_ERR_CONN_RST;
        }
        else if (err == SOCKET_EINTR) {
            CYASSL_MSG("    Socket interrupted");
            return CYASSL_CBIO_ERR_ISR;
        }
        else if (err == SOCKET_EPIPE) {
            CYASSL_MSG("    Socket EPIPE");
            return CYASSL_CBIO_ERR_CONN_CLOSE;
        }
        else {
            CYASSL_MSG("    General error");
            return CYASSL_CBIO_ERR_GENERAL;
        }
    }
 
    return sent;
}


/* The DTLS Generate Cookie callback
 *  return : number of bytes copied into buf, or error
 */
int EmbedGenerateCookie(CYASSL* ssl, byte *buf, int sz, void *ctx)
{
    int sd = ssl->wfd;
    struct sockaddr_storage peer;
    XSOCKLENT peerSz = sizeof(peer);
    Sha sha;
    byte digest[SHA_DIGEST_SIZE];
    int  ret = 0;

    (void)ctx;

    XMEMSET(&peer, 0, sizeof(peer));
    if (getpeername(sd, (struct sockaddr*)&peer, &peerSz) != 0) {
        CYASSL_MSG("getpeername failed in EmbedGenerateCookie");
        return GEN_COOKIE_E;
    }
    
    ret = InitSha(&sha);
    if (ret != 0)
        return ret;
    ShaUpdate(&sha, (byte*)&peer, peerSz);
    ShaFinal(&sha, digest);

    if (sz > SHA_DIGEST_SIZE)
        sz = SHA_DIGEST_SIZE;
    XMEMCPY(buf, digest, sz);

    return sz;
}

#endif /* CYASSL_DTLS */

#ifdef HAVE_OCSP


static int Word16ToString(char* d, word16 number)
{
    int i = 0;

    if (d != NULL) {
        word16 order = 10000;
        word16 digit;

        if (number == 0) {
            d[i++] = '0';
        }
        else {
            while (order) {
                digit = number / order;
                if (i > 0 || digit != 0) {
                    d[i++] = digit + '0';
                }
                if (digit != 0)
                    number %= digit * order;
                if (order > 1)
                    order /= 10;
                else
                    order = 0;
            }
        }
        d[i] = 0;
    }

    return i;
}


static int tcp_connect(SOCKET_T* sockfd, const char* ip, word16 port)
{
    struct sockaddr_storage addr;
    int sockaddr_len = sizeof(struct sockaddr_in);
    XMEMSET(&addr, 0, sizeof(addr));

    #ifdef HAVE_GETADDRINFO
    {
        struct addrinfo hints;
        struct addrinfo* answer = NULL;
        char strPort[6];

        XMEMSET(&hints, 0, sizeof(hints));
        hints.ai_family = AF_UNSPEC;
        hints.ai_socktype = SOCK_STREAM;
        hints.ai_protocol = IPPROTO_TCP;

        if (Word16ToString(strPort, port) == 0) {
            CYASSL_MSG("invalid port number for OCSP responder");
            return -1;
        }

        if (getaddrinfo(ip, strPort, &hints, &answer) < 0 || answer == NULL) {
            CYASSL_MSG("no addr info for OCSP responder");
            return -1;
        }

        sockaddr_len = answer->ai_addrlen;
        XMEMCPY(&addr, answer->ai_addr, sockaddr_len);
        freeaddrinfo(answer);

    }
    #else /* HAVE_GETADDRINFO */
    {
        struct hostent* entry = gethostbyname(ip);
        struct sockaddr_in *sin = (struct sockaddr_in *)&addr;

        if (entry) {
            sin->sin_family = AF_INET;
            sin->sin_port = htons(port);
            XMEMCPY(&sin->sin_addr.s_addr, entry->h_addr_list[0],
                                                               entry->h_length);
        }
        else {
            CYASSL_MSG("no addr info for OCSP responder");
            return -1;
        }
    }
    #endif /* HAVE_GETADDRINFO */

    *sockfd = socket(addr.ss_family, SOCK_STREAM, 0);
    if (*sockfd < 0) {
        CYASSL_MSG("bad socket fd, out of fds?");
        return -1;
    }

    if (connect(*sockfd, (struct sockaddr *)&addr, sockaddr_len) != 0) {
        CYASSL_MSG("OCSP responder tcp connect failed");
        return -1;
    }

    return 0;
}


static int build_http_request(const char* domainName, const char* path,
                                    int ocspReqSz, byte* buf, int bufSize)
{
    word32 domainNameLen, pathLen, ocspReqSzStrLen, completeLen;
    char ocspReqSzStr[6];

    domainNameLen = (word32)XSTRLEN(domainName);
    pathLen = (word32)XSTRLEN(path);
    ocspReqSzStrLen = Word16ToString(ocspReqSzStr, ocspReqSz);

    completeLen = domainNameLen + pathLen + ocspReqSzStrLen + 84;
    if (completeLen > (word32)bufSize)
        return 0;

    XSTRNCPY((char*)buf, "POST ", 5);
    buf += 5;
    XSTRNCPY((char*)buf, path, pathLen);
    buf += pathLen;
    XSTRNCPY((char*)buf, " HTTP/1.1\r\nHost: ", 17);
    buf += 17;
    XSTRNCPY((char*)buf, domainName, domainNameLen);
    buf += domainNameLen;
    XSTRNCPY((char*)buf, "\r\nContent-Length: ", 18);
    buf += 18;
    XSTRNCPY((char*)buf, ocspReqSzStr, ocspReqSzStrLen);
    buf += ocspReqSzStrLen;
    XSTRNCPY((char*)buf,
                      "\r\nContent-Type: application/ocsp-request\r\n\r\n", 44);

    return completeLen;
}


static int decode_url(const char* url, int urlSz,
    char* outName, char* outPath, word16* outPort)
{
    int result = -1;

    if (outName != NULL && outPath != NULL && outPort != NULL)
    {
        if (url == NULL || urlSz == 0)
        {
            *outName = 0;
            *outPath = 0;
            *outPort = 0;
        }
        else
        {
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
                while (url[cur] != 0 && url[cur] != ']' && cur < urlSz) {
                    outName[i++] = url[cur++];
                }
                cur++; /* skip ']' */
            }
            else {
                while (url[cur] != 0 && url[cur] != ':' &&
                                               url[cur] != '/' && cur < urlSz) {
                    outName[i++] = url[cur++];
                }
            }
            outName[i] = 0;
            /* Need to pick out the path after the domain name */
    
            if (cur < urlSz && url[cur] == ':') {
                char port[6];
                int j;
                word32 bigPort = 0;
                i = 0;
                cur++;
                while (cur < urlSz && url[cur] != 0 && url[cur] != '/' &&
                        i < 6) {
                    port[i++] = url[cur++];
                }
    
                for (j = 0; j < i; j++) {
                    if (port[j] < '0' || port[j] > '9') return -1;
                    bigPort = (bigPort * 10) + (port[j] - '0');
                }
                *outPort = (word16)bigPort;
            }
            else
                *outPort = 80;
    
            if (cur < urlSz && url[cur] == '/') {
                i = 0;
                while (cur < urlSz && url[cur] != 0 && i < 80) {
                    outPath[i++] = url[cur++];
                }
                outPath[i] = 0;
            }
            else {
                outPath[0] = '/';
                outPath[1] = 0;
            }
            result = 0;
        }
    }

    return result;
}


/* return: >0 OCSP Response Size
 *         -1 error */
static int process_http_response(int sfd, byte** respBuf,
                                                  byte* httpBuf, int httpBufSz)
{
    int result;
    int len = 0;
    char *start, *end;
    byte *recvBuf = NULL;
    int recvBufSz = 0;
    enum phr_state { phr_init, phr_http_start, phr_have_length,
                     phr_have_type, phr_wait_end, phr_http_end
    } state = phr_init;

    start = end = NULL;
    do {
        if (end == NULL) {
            result = (int)recv(sfd, (char*)httpBuf+len, httpBufSz-len-1, 0);
            if (result > 0) {
                len += result;
                start = (char*)httpBuf;
                start[len] = 0;
            }
            else {
                CYASSL_MSG("process_http_response recv http from peer failed");
                return -1;
            }
        }
        end = XSTRSTR(start, "\r\n");

        if (end == NULL) {
            if (len != 0)
                XMEMMOVE(httpBuf, start, len);
            start = end = NULL;
        }
        else if (end == start) {
            if (state == phr_wait_end) {
                state = phr_http_end;
                len -= 2;
                start += 2;
             }
             else {
                CYASSL_MSG("process_http_response header ended early");
                return -1;
             }
        }
        else {
            *end = 0;
            len -= (int)(end - start) + 2;
                /* adjust len to remove the first line including the /r/n */

            if (XSTRNCASECMP(start, "HTTP/1", 6) == 0) {
                start += 9;
                if (XSTRNCASECMP(start, "200 OK", 6) != 0 ||
                                                           state != phr_init) {
                    CYASSL_MSG("process_http_response not OK");
                    return -1;
                }
                state = phr_http_start;
            }
            else if (XSTRNCASECMP(start, "Content-Type:", 13) == 0) {
                start += 13;
                while (*start == ' ' && *start != '\0') start++;
                if (XSTRNCASECMP(start, "application/ocsp-response", 25) != 0) {
                    CYASSL_MSG("process_http_response not ocsp-response");
                    return -1;
                }
                
                if (state == phr_http_start) state = phr_have_type;
                else if (state == phr_have_length) state = phr_wait_end;
                else {
                    CYASSL_MSG("process_http_response type invalid state");
                    return -1;
                }
            }
            else if (XSTRNCASECMP(start, "Content-Length:", 15) == 0) {
                start += 15;
                while (*start == ' ' && *start != '\0') start++;
                recvBufSz = atoi(start);

                if (state == phr_http_start) state = phr_have_length;
                else if (state == phr_have_type) state = phr_wait_end;
                else {
                    CYASSL_MSG("process_http_response length invalid state");
                    return -1;
                }
            }
            
            start = end + 2;
        }
    } while (state != phr_http_end);

    recvBuf = XMALLOC(recvBufSz, NULL, DYNAMIC_TYPE_IN_BUFFER);
    if (recvBuf == NULL) {
        CYASSL_MSG("process_http_response couldn't create response buffer");
        return -1;
    }

    /* copy the remainder of the httpBuf into the respBuf */
    if (len != 0)
        XMEMCPY(recvBuf, start, len);

    /* receive the OCSP response data */
    do {
        result = (int)recv(sfd, (char*)recvBuf+len, recvBufSz-len, 0);
        if (result > 0)
            len += result;
        else {
            CYASSL_MSG("process_http_response recv ocsp from peer failed");
            return -1;
        }
    } while (len != recvBufSz);

    *respBuf = recvBuf;
    return recvBufSz;
}


#define SCRATCH_BUFFER_SIZE 512

int EmbedOcspLookup(void* ctx, const char* url, int urlSz,
                        byte* ocspReqBuf, int ocspReqSz, byte** ocspRespBuf)
{
    char domainName[80], path[80];
    int httpBufSz;
    SOCKET_T sfd = 0;
    word16 port;
    int ocspRespSz = 0;
    byte* httpBuf = NULL;

    (void)ctx;

    if (ocspReqBuf == NULL || ocspReqSz == 0) {
        CYASSL_MSG("OCSP request is required for lookup");
        return -1;
    }

    if (ocspRespBuf == NULL) {
        CYASSL_MSG("Cannot save OCSP response");
        return -1;
    }

    if (decode_url(url, urlSz, domainName, path, &port) < 0) {
        CYASSL_MSG("Unable to decode OCSP URL");
        return -1;
    }
    
    /* Note, the library uses the EmbedOcspRespFree() callback to
     * free this buffer. */
    httpBufSz = SCRATCH_BUFFER_SIZE;
    httpBuf = (byte*)XMALLOC(httpBufSz, NULL, DYNAMIC_TYPE_IN_BUFFER);

    if (httpBuf == NULL) {
        CYASSL_MSG("Unable to create OCSP response buffer");
        return -1;
    }

    httpBufSz = build_http_request(domainName, path, ocspReqSz,
                                                        httpBuf, httpBufSz);

    if ((tcp_connect(&sfd, domainName, port) == 0) && (sfd > 0)) {
        int written;
        written = (int)send(sfd, (char*)httpBuf, httpBufSz, 0);
        if (written == httpBufSz) {
            written = (int)send(sfd, (char*)ocspReqBuf, ocspReqSz, 0);
            if (written == ocspReqSz) {
                ocspRespSz = process_http_response(sfd, ocspRespBuf,
                                                 httpBuf, SCRATCH_BUFFER_SIZE);
            }
        }
        close(sfd);
        if (ocspRespSz == 0) {
            CYASSL_MSG("OCSP response was not OK, no OCSP response");
            XFREE(httpBuf, NULL, DYNAMIC_TYPE_IN_BUFFER);
            return -1;
        }
    } else {
        CYASSL_MSG("OCSP Responder connection failed");
        close(sfd);
        XFREE(httpBuf, NULL, DYNAMIC_TYPE_IN_BUFFER);
        return -1;
    }

    XFREE(httpBuf, NULL, DYNAMIC_TYPE_IN_BUFFER);
    return ocspRespSz;
}


void EmbedOcspRespFree(void* ctx, byte *resp)
{
    (void)ctx;

    if (resp)
        XFREE(resp, NULL, DYNAMIC_TYPE_IN_BUFFER);
}


#endif

#endif /* CYASSL_USER_IO */

CYASSL_API void CyaSSL_SetIORecv(CYASSL_CTX *ctx, CallbackIORecv CBIORecv)
{
    ctx->CBIORecv = CBIORecv;
}


CYASSL_API void CyaSSL_SetIOSend(CYASSL_CTX *ctx, CallbackIOSend CBIOSend)
{
    ctx->CBIOSend = CBIOSend;
}


CYASSL_API void CyaSSL_SetIOReadCtx(CYASSL* ssl, void *rctx)
{
	ssl->IOCB_ReadCtx = rctx;
}


CYASSL_API void CyaSSL_SetIOWriteCtx(CYASSL* ssl, void *wctx)
{
	ssl->IOCB_WriteCtx = wctx;
}


CYASSL_API void* CyaSSL_GetIOReadCtx(CYASSL* ssl)
{
    if (ssl)
        return ssl->IOCB_ReadCtx;

    return NULL;
}


CYASSL_API void* CyaSSL_GetIOWriteCtx(CYASSL* ssl)
{
    if (ssl)
        return ssl->IOCB_WriteCtx;

    return NULL;
}


CYASSL_API void CyaSSL_SetIOReadFlags(CYASSL* ssl, int flags)
{
    ssl->rflags = flags; 
}


CYASSL_API void CyaSSL_SetIOWriteFlags(CYASSL* ssl, int flags)
{
    ssl->wflags = flags;
}


#ifdef CYASSL_DTLS

CYASSL_API void CyaSSL_CTX_SetGenCookie(CYASSL_CTX* ctx, CallbackGenCookie cb)
{
    ctx->CBIOCookie = cb;
}


CYASSL_API void CyaSSL_SetCookieCtx(CYASSL* ssl, void *ctx)
{
	ssl->IOCB_CookieCtx = ctx;
}


CYASSL_API void* CyaSSL_GetCookieCtx(CYASSL* ssl)
{
    if (ssl)
	    return ssl->IOCB_CookieCtx;

    return NULL;
}

#endif /* CYASSL_DTLS */


#ifdef HAVE_NETX

/* The NetX receive callback
 *  return :  bytes read, or error
 */
int NetX_Receive(CYASSL *ssl, char *buf, int sz, void *ctx)
{
    NetX_Ctx* nxCtx = (NetX_Ctx*)ctx;
    ULONG left;
    ULONG total;
    ULONG copied = 0;
    UINT  status;

    if (nxCtx == NULL || nxCtx->nxSocket == NULL) {
        CYASSL_MSG("NetX Recv NULL parameters");
        return CYASSL_CBIO_ERR_GENERAL;
    }

    if (nxCtx->nxPacket == NULL) {
        status = nx_tcp_socket_receive(nxCtx->nxSocket, &nxCtx->nxPacket,
                                       nxCtx->nxWait);
        if (status != NX_SUCCESS) {
            CYASSL_MSG("NetX Recv receive error");
            return CYASSL_CBIO_ERR_GENERAL;
        }
    }

    if (nxCtx->nxPacket) {
        status = nx_packet_length_get(nxCtx->nxPacket, &total);
        if (status != NX_SUCCESS) {
            CYASSL_MSG("NetX Recv length get error");
            return CYASSL_CBIO_ERR_GENERAL;
        }

        left = total - nxCtx->nxOffset;
        status = nx_packet_data_extract_offset(nxCtx->nxPacket, nxCtx->nxOffset,
                                               buf, sz, &copied);
        if (status != NX_SUCCESS) {
            CYASSL_MSG("NetX Recv data extract offset error");
            return CYASSL_CBIO_ERR_GENERAL;
        }

        nxCtx->nxOffset += copied;

        if (copied == left) {
            CYASSL_MSG("NetX Recv Drained packet");
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
int NetX_Send(CYASSL* ssl, char *buf, int sz, void *ctx)
{
    NetX_Ctx*       nxCtx = (NetX_Ctx*)ctx;
    NX_PACKET*      packet;
    NX_PACKET_POOL* pool;   /* shorthand */
    UINT            status;

    if (nxCtx == NULL || nxCtx->nxSocket == NULL) {
        CYASSL_MSG("NetX Send NULL parameters");
        return CYASSL_CBIO_ERR_GENERAL;
    }

    pool = nxCtx->nxSocket->nx_tcp_socket_ip_ptr->nx_ip_default_packet_pool;
    status = nx_packet_allocate(pool, &packet, NX_TCP_PACKET,
                                nxCtx->nxWait);
    if (status != NX_SUCCESS) {
        CYASSL_MSG("NetX Send packet alloc error");
        return CYASSL_CBIO_ERR_GENERAL;
    }

    status = nx_packet_data_append(packet, buf, sz, pool, nxCtx->nxWait);
    if (status != NX_SUCCESS) {
        nx_packet_release(packet);
        CYASSL_MSG("NetX Send data append error");
        return CYASSL_CBIO_ERR_GENERAL;
    }

    status = nx_tcp_socket_send(nxCtx->nxSocket, packet, nxCtx->nxWait);
    if (status != NX_SUCCESS) {
        nx_packet_release(packet);
        CYASSL_MSG("NetX Send socket send error");
        return CYASSL_CBIO_ERR_GENERAL;
    }

    return sz;
}


/* like set_fd, but for default NetX context */
void CyaSSL_SetIO_NetX(CYASSL* ssl, NX_TCP_SOCKET* nxSocket, ULONG waitOption)
{
    if (ssl) {
        ssl->nxCtx.nxSocket = nxSocket;
        ssl->nxCtx.nxWait   = waitOption;
    }
}

#endif /* HAVE_NETX */

