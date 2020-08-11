/* echoserver.c
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


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <cyassl/ssl.h> /* name change portability layer */
#include <cyassl/ctaocrypt/settings.h>
#ifdef HAVE_ECC
    #include <cyassl/ctaocrypt/ecc.h>   /* ecc_fp_free */
#endif

#if defined(WOLFSSL_MDK_ARM) || defined(WOLFSSL_KEIL_TCP_NET)
        #include <stdio.h>
        #include <string.h>
        #include "cmsis_os.h"
        #include "rl_fs.h"
        #include "rl_net.h"
        #include "wolfssl_MDK_ARM.h"
#endif

#include <cyassl/ssl.h>
#include <cyassl/test.h>

#ifndef NO_MAIN_DRIVER
    #define ECHO_OUT
#endif

#include "examples/echoserver/echoserver.h"

#ifndef NO_WOLFSSL_SERVER

#ifdef WOLFSSL_ASYNC_CRYPT
    static int devId = INVALID_DEVID;
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

    int    ret = 0;
    int    doDTLS = 0;
    int    doPSK;
    int    outCreated = 0;
    int    shutDown = 0;
    int    useAnyAddr = 0;
    word16 port;
    int    argc = ((func_args*)args)->argc;
    char** argv = ((func_args*)args)->argv;
    char   buffer[CYASSL_MAX_ERROR_SZ];

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

#if (defined(NO_RSA) && !defined(HAVE_ECC) && !defined(HAVE_ED25519) && \
                                !defined(HAVE_ED448)) || defined(CYASSL_LEANPSK)
    doPSK = 1;
#else
    doPSK = 0;
#endif

#if defined(NO_MAIN_DRIVER) && !defined(CYASSL_SNIFFER) && \
     !defined(WOLFSSL_MDK_SHELL) && !defined(CYASSL_TIRTOS) && \
     !defined(USE_WINDOWS_API)
    /* Let tcp_listen assign port */
    port = 0;
#else
    /* Use default port */
    port = wolfSSLPort;
#endif

#if defined(USE_ANY_ADDR)
    useAnyAddr = 1;
#endif

#ifdef CYASSL_TIRTOS
    fdOpenSession(Task_self());
#endif

    tcp_listen(&sockfd, &port, useAnyAddr, doDTLS, 0);

#if defined(CYASSL_DTLS)
    method  = CyaDTLSv1_2_server_method();
#elif !defined(NO_TLS)
    method = CyaSSLv23_server_method();
#elif defined(WOLFSSL_ALLOW_SSLV3)
    method = CyaSSLv3_server_method();
#else
    #error "no valid server method built in"
#endif
    ctx    = CyaSSL_CTX_new(method);
    /* CyaSSL_CTX_set_session_cache_mode(ctx, WOLFSSL_SESS_CACHE_OFF); */

#ifdef WOLFSSL_ENCRYPTED_KEYS
    CyaSSL_CTX_set_default_passwd_cb(ctx, PasswordCallBack);
#endif

#if defined(HAVE_SESSION_TICKET) && defined(HAVE_CHACHA) && \
                                    defined(HAVE_POLY1305)
    if (TicketInit() != 0)
        err_sys("unable to setup Session Ticket Key context");
    wolfSSL_CTX_set_TicketEncCb(ctx, myTicketEncCb);
#endif

#ifndef NO_FILESYSTEM
    if (doPSK == 0) {
    #if defined(HAVE_NTRU) && defined(WOLFSSL_STATIC_RSA)
        /* ntru */
        if (CyaSSL_CTX_use_certificate_file(ctx, ntruCertFile, WOLFSSL_FILETYPE_PEM)
                != WOLFSSL_SUCCESS)
            err_sys("can't load ntru cert file, "
                    "Please run from wolfSSL home dir");

        if (CyaSSL_CTX_use_NTRUPrivateKey_file(ctx, ntruKeyFile)
                != WOLFSSL_SUCCESS)
            err_sys("can't load ntru key file, "
                    "Please run from wolfSSL home dir");
    #elif defined(HAVE_ECC) && !defined(CYASSL_SNIFFER)
        /* ecc */
        if (CyaSSL_CTX_use_certificate_file(ctx, eccCertFile, WOLFSSL_FILETYPE_PEM)
                != WOLFSSL_SUCCESS)
            err_sys("can't load server cert file, "
                    "Please run from wolfSSL home dir");

        if (CyaSSL_CTX_use_PrivateKey_file(ctx, eccKeyFile, WOLFSSL_FILETYPE_PEM)
                != WOLFSSL_SUCCESS)
            err_sys("can't load server key file, "
                    "Please run from wolfSSL home dir");
    #elif defined(HAVE_ED25519) && !defined(CYASSL_SNIFFER)
        /* ed25519 */
        if (CyaSSL_CTX_use_certificate_chain_file(ctx, edCertFile)
                != WOLFSSL_SUCCESS)
            err_sys("can't load server cert file, "
                    "Please run from wolfSSL home dir");

        if (CyaSSL_CTX_use_PrivateKey_file(ctx, edKeyFile, WOLFSSL_FILETYPE_PEM)
                != WOLFSSL_SUCCESS)
            err_sys("can't load server key file, "
                    "Please run from wolfSSL home dir");
    #elif defined(HAVE_ED448) && !defined(CYASSL_SNIFFER)
        /* ed448 */
        if (CyaSSL_CTX_use_certificate_chain_file(ctx, ed448CertFile)
                != WOLFSSL_SUCCESS)
            err_sys("can't load server cert file, "
                    "Please run from wolfSSL home dir");

        if (CyaSSL_CTX_use_PrivateKey_file(ctx, ed448KeyFile,
                WOLFSSL_FILETYPE_PEM) != WOLFSSL_SUCCESS)
            err_sys("can't load server key file, "
                    "Please run from wolfSSL home dir");
    #elif defined(NO_CERTS)
        /* do nothing, just don't load cert files */
    #else
        /* normal */
        if (CyaSSL_CTX_use_certificate_file(ctx, svrCertFile, WOLFSSL_FILETYPE_PEM)
                != WOLFSSL_SUCCESS)
            err_sys("can't load server cert file, "
                    "Please run from wolfSSL home dir");

        if (CyaSSL_CTX_use_PrivateKey_file(ctx, svrKeyFile, WOLFSSL_FILETYPE_PEM)
                != WOLFSSL_SUCCESS)
            err_sys("can't load server key file, "
                    "Please run from wolfSSL home dir");
    #endif
    } /* doPSK */
#elif !defined(NO_CERTS)
    if (!doPSK) {
        load_buffer(ctx, svrCertFile, WOLFSSL_CERT);
        load_buffer(ctx, svrKeyFile,  WOLFSSL_KEY);
    }
#endif

#if defined(CYASSL_SNIFFER)
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
        #elif defined(HAVE_AESGCM) && !defined(NO_DH)
            defaultCipherList = "DHE-PSK-AES128-GCM-SHA256";
        #else
            defaultCipherList = "PSK-AES128-CBC-SHA256";
        #endif
        if (CyaSSL_CTX_set_cipher_list(ctx, defaultCipherList) != WOLFSSL_SUCCESS)
            err_sys("server can't set cipher list 2");
#endif
    }

#ifdef WOLFSSL_ASYNC_CRYPT
    ret = wolfAsync_DevOpen(&devId);
    if (ret < 0) {
        printf("Async device open failed\nRunning without async\n");
    }
    wolfSSL_CTX_UseAsync(ctx, devId);
#endif /* WOLFSSL_ASYNC_CRYPT */

    SignalReady(args, port);

    while (!shutDown) {
        CYASSL* ssl = NULL;
        CYASSL* write_ssl = NULL;   /* may have separate w/ HAVE_WRITE_DUP */
        char    command[SVR_COMMAND_SIZE+1];
        int     echoSz = 0;
        int     clientfd;
        int     firstRead = 1;
        int     gotFirstG = 0;
        int     err = 0;
        SOCKADDR_IN_T client;
        socklen_t     client_len = sizeof(client);
#ifndef CYASSL_DTLS
        clientfd = accept(sockfd, (struct sockaddr*)&client,
                         (ACCEPT_THIRD_T)&client_len);
#else
        clientfd = sockfd;
        {
            /* For DTLS, peek at the next datagram so we can get the client's
             * address and set it into the ssl object later to generate the
             * cookie. */
            int n;
            byte b[1500];
            n = (int)recvfrom(clientfd, (char*)b, sizeof(b), MSG_PEEK,
                              (struct sockaddr*)&client, &client_len);
            if (n <= 0)
                err_sys("recvfrom failed");
        }
#endif
        if (WOLFSSL_SOCKET_IS_INVALID(clientfd)) err_sys("tcp accept failed");

        ssl = CyaSSL_new(ctx);
        if (ssl == NULL) err_sys("SSL_new failed");
        CyaSSL_set_fd(ssl, clientfd);
        #ifdef CYASSL_DTLS
            wolfSSL_dtls_set_peer(ssl, &client, client_len);
        #endif
        #if !defined(NO_FILESYSTEM) && !defined(NO_DH) && !defined(NO_ASN)
            CyaSSL_SetTmpDH_file(ssl, dhParamFile, WOLFSSL_FILETYPE_PEM);
        #elif !defined(NO_DH)
            SetDH(ssl);  /* will repick suites with DHE, higher than PSK */
        #endif

        do {
            err = 0; /* Reset error */
            ret = CyaSSL_accept(ssl);
            if (ret != WOLFSSL_SUCCESS) {
                err = CyaSSL_get_error(ssl, 0);
            #ifdef WOLFSSL_ASYNC_CRYPT
                if (err == WC_PENDING_E) {
                    ret = wolfSSL_AsyncPoll(ssl, WOLF_POLL_FLAG_CHECK_HW);
                    if (ret < 0) break;
                }
            #endif
            }
        } while (err == WC_PENDING_E);
        if (ret != WOLFSSL_SUCCESS) {
            printf("SSL_accept error = %d, %s\n", err,
                CyaSSL_ERR_error_string(err, buffer));
            printf("SSL_accept failed\n");
            CyaSSL_free(ssl);
            CloseSocket(clientfd);
            continue;
        }
#if defined(PEER_INFO)
        showPeer(ssl);
#endif

#ifdef HAVE_WRITE_DUP
        write_ssl = wolfSSL_write_dup(ssl);
        if (write_ssl == NULL) {
            printf("wolfSSL_write_dup failed\n");
            CyaSSL_free(ssl);
            CloseSocket(clientfd);
            continue;
        }
#else
        write_ssl = ssl;
#endif

        while (1) {
            do {
                err = 0; /* reset error */
                ret = CyaSSL_read(ssl, command, sizeof(command)-1);
                if (ret <= 0) {
                    err = CyaSSL_get_error(ssl, 0);
                #ifdef WOLFSSL_ASYNC_CRYPT
                    if (err == WC_PENDING_E) {
                        ret = wolfSSL_AsyncPoll(ssl, WOLF_POLL_FLAG_CHECK_HW);
                        if (ret < 0) break;
                    }
                #endif
                }
            } while (err == WC_PENDING_E);
            if (ret <= 0) {
                if (err != WOLFSSL_ERROR_WANT_READ && err != WOLFSSL_ERROR_ZERO_RETURN){
                    printf("SSL_read echo error %d, %s!\n", err,
                        CyaSSL_ERR_error_string(err, buffer));
                }
                break;
            }

            echoSz = ret;

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
#ifdef PRINT_SESSION_STATS
            if ( strncmp(command, "printstats", 10) == 0) {
                CyaSSL_PrintSessionStats();
                break;
            }
#endif
            if (strncmp(command, "GET", 3) == 0) {
                const char resp[] =
                    "HTTP/1.0 200 ok\r\nContent-type: text/html\r\n\r\n"
                    "<html><body BGCOLOR=\"#ffffff\"><pre>\r\n"
                    "greetings from wolfSSL\r\n</pre></body></html>\r\n\r\n";

                echoSz = (int)strlen(resp) + 1;
                if (echoSz > (int)sizeof(command)) {
                    /* Internal error. */
                    err_sys("HTTP response greater than buffer.");
                }
                strncpy(command, resp, sizeof(command));

                do {
                    err = 0; /* reset error */
                    ret = CyaSSL_write(write_ssl, command, echoSz);
                    if (ret <= 0) {
                        err = CyaSSL_get_error(write_ssl, 0);
                    #ifdef WOLFSSL_ASYNC_CRYPT
                        if (err == WC_PENDING_E) {
                            ret = wolfSSL_AsyncPoll(write_ssl, WOLF_POLL_FLAG_CHECK_HW);
                            if (ret < 0) break;
                        }
                    #endif
                    }
                } while (err == WC_PENDING_E);
                if (ret != echoSz) {
                    printf("SSL_write get error = %d, %s\n", err,
                        CyaSSL_ERR_error_string(err, buffer));
                    err_sys("SSL_write get failed");
                }
                break;
            }
            command[echoSz] = 0;

        #ifdef ECHO_OUT
            fputs(command, fout);
        #endif

            do {
                err = 0; /* reset error */
                ret = CyaSSL_write(write_ssl, command, echoSz);
                if (ret <= 0) {
                    err = CyaSSL_get_error(write_ssl, 0);
                #ifdef WOLFSSL_ASYNC_CRYPT
                    if (err == WC_PENDING_E) {
                        ret = wolfSSL_AsyncPoll(write_ssl, WOLF_POLL_FLAG_CHECK_HW);
                        if (ret < 0) break;
                    }
                #endif
                }
            } while (err == WC_PENDING_E);

            if (ret != echoSz) {
                printf("SSL_write echo error = %d, %s\n", err,
                        CyaSSL_ERR_error_string(err, buffer));
                err_sys("SSL_write echo failed");
            }
        }
#ifndef CYASSL_DTLS
        CyaSSL_shutdown(ssl);
#endif
#ifdef HAVE_WRITE_DUP
        CyaSSL_free(write_ssl);
#endif
        CyaSSL_free(ssl);
        CloseSocket(clientfd);
#ifdef CYASSL_DTLS
        tcp_listen(&sockfd, &port, useAnyAddr, doDTLS, 0);
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

#if defined(NO_MAIN_DRIVER) && defined(HAVE_ECC) && defined(FP_ECC) \
                            && defined(HAVE_THREAD_LS)
    ecc_fp_free();  /* free per thread cache */
#endif

#ifdef CYASSL_TIRTOS
    fdCloseSession(Task_self());
#endif

#if defined(HAVE_SESSION_TICKET) && defined(HAVE_CHACHA) && \
                                    defined(HAVE_POLY1305)
    TicketCleanup();
#endif

#ifdef WOLFSSL_ASYNC_CRYPT
    wolfAsync_DevClose(&devId);
#endif

#ifndef CYASSL_TIRTOS
    return 0;
#endif
}

#endif /* !NO_WOLFSSL_SERVER */


/* so overall tests can pull in test function */
#ifndef NO_MAIN_DRIVER

    int main(int argc, char** argv)
    {
        func_args args;

#ifdef HAVE_WNR
        if (wc_InitNetRandom(wnrConfig, NULL, 5000) != 0)
            err_sys("Whitewood netRandom global config failed");
#endif

        StartTCP();

        args.argc = argc;
        args.argv = argv;
        args.return_code = 0;

        CyaSSL_Init();
#if defined(DEBUG_CYASSL) && !defined(CYASSL_MDK_SHELL)
        CyaSSL_Debugging_ON();
#endif
        ChangeToWolfRoot();
#ifndef NO_WOLFSSL_SERVER
        echoserver_test(&args);
#endif
        CyaSSL_Cleanup();

#ifdef HAVE_WNR
        if (wc_FreeNetRandom() < 0)
            err_sys("Failed to free netRandom context");
#endif /* HAVE_WNR */

        return args.return_code;
    }

#endif /* NO_MAIN_DRIVER */
