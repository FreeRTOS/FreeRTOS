/* wolfssl_adds.c
 *
 * Copyright (C) 2006-2015 wolfSSL Inc.
 *
 * This file is part of wolfSSL. (formerly known as CyaSSL)
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#ifndef _WIN32
    #define HAVE_CONFIG_H
#endif

#include <wolfssl/ssl.h>
#include <wolfssl/wolfcrypt/rsa.h>
#include <wolfssl/wolfcrypt/asn.h>

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <ctype.h>

#ifdef _WIN32
    #include <winsock2.h>
    #include <process.h>
    #ifdef TEST_IPV6            /* don't require newer SDK for IPV4 */
	    #include <ws2tcpip.h>
        #include <wspiapi.h>
    #endif
    #define SOCKET_T int
#else
    #include <string.h>
    #include <unistd.h>
    #include <netdb.h>
    #include <netinet/in.h>
    #include <arpa/inet.h>
    #include <sys/ioctl.h>
    #include <sys/time.h>
    #include <sys/types.h>
    #include <sys/socket.h>
    #include <pthread.h>
    #ifdef NON_BLOCKING
        #include <fcntl.h>
    #endif
    #ifdef TEST_IPV6
        #include <netdb.h>
    #endif
    #define SOCKET_T unsigned int
#endif /* _WIN32 */

#ifdef _MSC_VER
    /* disable conversion warning */
    /* 4996 warning to use MS extensions e.g., strcpy_s instead of strncpy */
    #pragma warning(disable:4244 4996)
#endif

#if defined(__MACH__) || defined(_WIN32)
    #ifndef _SOCKLEN_T
        typedef int socklen_t;
    #endif
#endif


/* HPUX doesn't use socklent_t for third parameter to accept */
#if !defined(__hpux__)
    typedef socklen_t* ACCEPT_THIRD_T;
#else
    typedef int*       ACCEPT_THIRD_T;
#endif


#ifdef _WIN32
    #define CloseSocket(s) closesocket(s)
    #define StartTCP() { WSADATA wsd; WSAStartup(0x0002, &wsd); }
#else
    #define CloseSocket(s) close(s)
    #define StartTCP()
#endif


#ifdef TEST_IPV6
    typedef struct sockaddr_in6 SOCKADDR_IN_T;
    #define AF_INET_V    AF_INET6
#else
    typedef struct sockaddr_in  SOCKADDR_IN_T;
    #define AF_INET_V    AF_INET
#endif


enum {
    SSL_BLOCKING    = 2,
    SSL_NONBLOCKING = 4
};


static int tcp_socket(SOCKET_T* sockfd, SOCKADDR_IN_T* addr, const char* peer,
                       short port)
{
    const char* host = peer;

    /* peer could be in human readable form */
    if (isalpha(peer[0])) {
        struct hostent* entry = gethostbyname(peer);

        if (entry) {
            struct sockaddr_in tmp;
            memset(&tmp, 0, sizeof(struct sockaddr_in));
            memcpy(&tmp.sin_addr.s_addr, entry->h_addr_list[0],entry->h_length);
            host = inet_ntoa(tmp.sin_addr);
        }
        else
            return -1;   /* no entry for host */
    }

    *sockfd = socket(AF_INET, SOCK_STREAM, 0);
    memset(addr, 0, sizeof(SOCKADDR_IN_T));

    addr->sin_family = AF_INET;
    addr->sin_port = htons(port);
    addr->sin_addr.s_addr = inet_addr(host);

#ifdef SO_NOSIGPIPE
    {
        int on = 1;
        socklen_t len = sizeof(on);
        setsockopt(*sockfd, SOL_SOCKET, SO_NOSIGPIPE, &on, len);
    }
#endif

    return 0;
}


static int tcp_connect(SOCKET_T* sockfd, const char* ip, short port)
{
    SOCKADDR_IN_T addr;
    int ret = tcp_socket(sockfd, &addr, ip, port);
    if (ret != 0) return ret;

    if (connect(*sockfd, (const struct sockaddr*)&addr, sizeof(addr)) != 0)
        return -2; /* can't connect */

    return 0;
}


int wolfSSL_swig_connect(WOLFSSL* ssl, const char* server, int port)
{
    SOCKET_T sockfd;
    int ret = tcp_connect(&sockfd, server, port);
    if (ret != 0) return ret;

    wolfSSL_set_fd(ssl, sockfd);

    return wolfSSL_connect(ssl);
}


char* wolfSSL_error_string(int err)
{
    static char buffer[WOLFSSL_MAX_ERROR_SZ];

    return wolfSSL_ERR_error_string(err, buffer);
}


RNG* GetRng(void)
{
    RNG* rng = (RNG*)malloc(sizeof(RNG));

    if (rng)
        if (wc_InitRng(rng) != 0) {
            free(rng);
            rng = 0;
        }

    return rng;
}


RsaKey* GetRsaPrivateKey(const char* keyFile)
{
    RsaKey* key = (RsaKey*)malloc(sizeof(RsaKey));

    if (key) {
        byte   tmp[1024];
        size_t bytes;
        int    ret;
        word32 idx = 0;
        FILE*  file = fopen(keyFile, "rb");

        if (!file) {
            free(key);
            return 0;
        }

        bytes = fread(tmp, 1, sizeof(tmp), file);
        fclose(file);
        wc_InitRsaKey(key, 0);

        ret = wc_RsaPrivateKeyDecode(tmp, &idx, key, (word32)bytes);
        if (ret != 0) {
            wc_FreeRsaKey(key);
            free(key);
            return 0;
        }
    }
    return key;
}


void FillSignStr(unsigned char* dst, const char* src, int size)
{
    memcpy(dst, src, size);
}

