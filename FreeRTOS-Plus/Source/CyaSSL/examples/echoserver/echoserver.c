/* echoserver.c
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

#if defined(CYASSL_MDK_ARM)
        #include <stdio.h>
        #include <string.h>

        #if defined(CYASSL_MDK5)
            #include "cmsis_os.h"
            #include "rl_fs.h" 
            #include "rl_net.h" 
        #else
            #include "rtl.h"
        #endif

        #include "cyassl_MDK_ARM.h"
#endif

#include <cyassl/ssl.h>
#include <cyassl/test.h>

#ifndef NO_MAIN_DRIVER
    #define ECHO_OUT
#endif

#include "examples/echoserver/echoserver.h"


#ifdef SESSION_STATS
    CYASSL_API void PrintSessionStats(void);
#endif

#define SVR_COMMAND_SIZE 256

static void SignalReady(void* args, word16 port)
{
#if defined(_POSIX_THREADS) && defined(NO_MAIN_DRIVER) && !defined(__MINGW32__)
    /* signal ready to tcp_accept */
    func_args* server_args = (func_args*)args;
    tcp_ready* ready = server_args->signal;
    pthread_mutex_lock(&ready->mutex);
    ready->ready = 1;
    ready->port = port;
    pthread_cond_signal(&ready->cond);
    pthread_mutex_unlock(&ready->mutex);
#endif
    (void)args;
    (void)port;
}


THREAD_RETURN CYASSL_THREAD echoserver_test(void* args)
{
    SOCKET_T       sockfd = 0;
    CYASSL_METHOD* method = 0;
    CYASSL_CTX*    ctx    = 0;

    int    doDTLS = 0;
    int    doPSK = 0;
    int    outCreated = 0;
    int    shutDown = 0;
    int    useAnyAddr = 0;
    word16 port = yasslPort;
    int    argc = ((func_args*)args)->argc;
    char** argv = ((func_args*)args)->argv;

#ifdef ECHO_OUT
    FILE* fout = stdout;
    if (argc >= 2) {
        fout = fopen(argv[1], "w");
        outCreated = 1;
    }
    if (!fout) err_sys("can't open output file");
#endif
    (void)outCreated;
    (void)argc;
    (void)argv;

    ((func_args*)args)->return_code = -1; /* error state */

#ifdef CYASSL_DTLS
    doDTLS  = 1;
#endif

#ifdef CYASSL_LEANPSK
    doPSK = 1;
#endif

#if defined(NO_RSA) && !defined(HAVE_ECC)
    doPSK = 1;
#endif

    #if defined(NO_MAIN_DRIVER) && !defined(USE_WINDOWS_API) && \
                      !defined(CYASSL_SNIFFER) && !defined(CYASSL_MDK_SHELL)
        port = 0;
    #endif
    #if defined(USE_ANY_ADDR)
        useAnyAddr = 1;
    #endif
    tcp_listen(&sockfd, &port, useAnyAddr, doDTLS);

#if defined(CYASSL_DTLS)
    method  = CyaDTLSv1_server_method();
#elif  !defined(NO_TLS)
    method = CyaSSLv23_server_method();
#else
    method = CyaSSLv3_server_method();
#endif
    ctx    = CyaSSL_CTX_new(method);
    /* CyaSSL_CTX_set_session_cache_mode(ctx, SSL_SESS_CACHE_OFF); */

#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
    CyaSSL_CTX_set_default_passwd_cb(ctx, PasswordCallBack);
#endif

#ifndef NO_FILESYSTEM
    if (doPSK == 0) {
    #ifdef HAVE_NTRU
        /* ntru */
        if (CyaSSL_CTX_use_certificate_file(ctx, ntruCert, SSL_FILETYPE_PEM)
                != SSL_SUCCESS)
            err_sys("can't load ntru cert file, "
                    "Please run from CyaSSL home dir");

        if (CyaSSL_CTX_use_NTRUPrivateKey_file(ctx, ntruKey)
                != SSL_SUCCESS)
            err_sys("can't load ntru key file, "
                    "Please run from CyaSSL home dir");
    #elif defined(HAVE_ECC)
        /* ecc */
        if (CyaSSL_CTX_use_certificate_file(ctx, eccCert, SSL_FILETYPE_PEM)
                != SSL_SUCCESS)
            err_sys("can't load server cert file, "
                    "Please run from CyaSSL home dir");

        if (CyaSSL_CTX_use_PrivateKey_file(ctx, eccKey, SSL_FILETYPE_PEM)
                != SSL_SUCCESS)
            err_sys("can't load server key file, "
                    "Please run from CyaSSL home dir");
    #elif defined(NO_CERTS)
        /* do nothing, just don't load cert files */
    #else
        /* normal */
        if (CyaSSL_CTX_use_certificate_file(ctx, svrCert, SSL_FILETYPE_PEM)
                != SSL_SUCCESS)
            err_sys("can't load server cert file, "
                    "Please run from CyaSSL home dir");

        if (CyaSSL_CTX_use_PrivateKey_file(ctx, svrKey, SSL_FILETYPE_PEM)
                != SSL_SUCCESS)
            err_sys("can't load server key file, "
                    "Please run from CyaSSL home dir");
    #endif
    } /* doPSK */
#elif !defined(NO_CERTS)
    if (!doPSK) {
        load_buffer(ctx, svrCert, CYASSL_CERT);
        load_buffer(ctx, svrKey,  CYASSL_KEY);
    }
#endif

#if defined(CYASSL_SNIFFER) && !defined(HAVE_NTRU) && !defined(HAVE_ECC)
    /* don't use EDH, can't sniff tmp keys */
    CyaSSL_CTX_set_cipher_list(ctx, "AES256-SHA");
#endif

    if (doPSK) {
#ifndef NO_PSK
        const char *defaultCipherList;

        CyaSSL_CTX_set_psk_server_callback(ctx, my_psk_server_cb);
        CyaSSL_CTX_use_psk_identity_hint(ctx, "cyassl server");
        #ifdef HAVE_NULL_CIPHER
            defaultCipherList = "PSK-NULL-SHA256";
        #else
            defaultCipherList = "PSK-AES128-CBC-SHA256";
        #endif
        if (CyaSSL_CTX_set_cipher_list(ctx, defaultCipherList) != SSL_SUCCESS)
            err_sys("server can't set cipher list 2");
#endif
    }

    SignalReady(args, port);

    while (!shutDown) {
        CYASSL* ssl = 0;
        char    command[SVR_COMMAND_SIZE+1];
        int     echoSz = 0;
        int     clientfd;
        int     firstRead = 1;
        int     gotFirstG = 0;
                
#ifndef CYASSL_DTLS 
        SOCKADDR_IN_T client;
        socklen_t     client_len = sizeof(client);
        clientfd = accept(sockfd, (struct sockaddr*)&client,
                         (ACCEPT_THIRD_T)&client_len);
#else
        clientfd = udp_read_connect(sockfd);
#endif
        if (clientfd == -1) err_sys("tcp accept failed");

        ssl = CyaSSL_new(ctx);
        if (ssl == NULL) err_sys("SSL_new failed");
        CyaSSL_set_fd(ssl, clientfd);
        #if !defined(NO_FILESYSTEM) && !defined(NO_DH)
            CyaSSL_SetTmpDH_file(ssl, dhParam, SSL_FILETYPE_PEM);
        #elif !defined(NO_DH)
            SetDH(ssl);  /* will repick suites with DHE, higher than PSK */
        #endif
        if (CyaSSL_accept(ssl) != SSL_SUCCESS) {
            printf("SSL_accept failed\n");
            CyaSSL_free(ssl);
            CloseSocket(clientfd);
            continue;
        }
#if defined(PEER_INFO)
        showPeer(ssl);
#endif

        while ( (echoSz = CyaSSL_read(ssl, command, sizeof(command)-1)) > 0) {

            if (firstRead == 1) {
                firstRead = 0;  /* browser may send 1 byte 'G' to start */
                if (echoSz == 1 && command[0] == 'G') {
                    gotFirstG = 1;
                    continue;
                }
            }
            else if (gotFirstG == 1 && strncmp(command, "ET /", 4) == 0) {
                strncpy(command, "GET", 4);
                /* fall through to normal GET */
            }
           
            if ( strncmp(command, "quit", 4) == 0) {
                printf("client sent quit command: shutting down!\n");
                shutDown = 1;
                break;
            }
            if ( strncmp(command, "break", 5) == 0) {
                printf("client sent break command: closing session!\n");
                break;
            }
#ifdef SESSION_STATS
            if ( strncmp(command, "printstats", 10) == 0) {
                PrintSessionStats();
                break;
            }
#endif
            if ( strncmp(command, "GET", 3) == 0) {
                char type[]   = "HTTP/1.0 200 ok\r\nContent-type:"
                                " text/html\r\n\r\n";
                char header[] = "<html><body BGCOLOR=\"#ffffff\">\n<pre>\n";
                char body[]   = "greetings from CyaSSL\n";
                char footer[] = "</body></html>\r\n\r\n";
            
                strncpy(command, type, sizeof(type));
                echoSz = sizeof(type) - 1;

                strncpy(&command[echoSz], header, sizeof(header));
                echoSz += (int)sizeof(header) - 1;
                strncpy(&command[echoSz], body, sizeof(body));
                echoSz += (int)sizeof(body) - 1;
                strncpy(&command[echoSz], footer, sizeof(footer));
                echoSz += (int)sizeof(footer);

                if (CyaSSL_write(ssl, command, echoSz) != echoSz)
                    err_sys("SSL_write failed");
                break;
            }
            command[echoSz] = 0;

            #ifdef ECHO_OUT
                fputs(command, fout);
            #endif

            if (CyaSSL_write(ssl, command, echoSz) != echoSz)
                err_sys("SSL_write failed");
        }
#ifndef CYASSL_DTLS
        CyaSSL_shutdown(ssl);
#endif
        CyaSSL_free(ssl);
        CloseSocket(clientfd);
#ifdef CYASSL_DTLS
        tcp_listen(&sockfd, &port, useAnyAddr, doDTLS);
        SignalReady(args, port);
#endif
    }

    CloseSocket(sockfd);
    CyaSSL_CTX_free(ctx);

#ifdef ECHO_OUT
    if (outCreated)
        fclose(fout);
#endif

    ((func_args*)args)->return_code = 0;
    return 0;
}


/* so overall tests can pull in test function */
#ifndef NO_MAIN_DRIVER

    int main(int argc, char** argv)
    {
        func_args args;

#ifdef HAVE_CAVIUM
        int ret = OpenNitroxDevice(CAVIUM_DIRECT, CAVIUM_DEV_ID);
        if (ret != 0)
            err_sys("Cavium OpenNitroxDevice failed");
#endif /* HAVE_CAVIUM */

        StartTCP();

        args.argc = argc;
        args.argv = argv;

        CyaSSL_Init();
#if defined(DEBUG_CYASSL) && !defined(CYASSL_MDK_SHELL)
        CyaSSL_Debugging_ON();
#endif
        if (CurrentDir("echoserver"))
            ChangeDirBack(2);
        else if (CurrentDir("Debug") || CurrentDir("Release"))
            ChangeDirBack(3);
        echoserver_test(&args);
        CyaSSL_Cleanup();

#ifdef HAVE_CAVIUM
        CspShutdown(CAVIUM_DEV_ID);
#endif
        return args.return_code;
    }

        
#endif /* NO_MAIN_DRIVER */




