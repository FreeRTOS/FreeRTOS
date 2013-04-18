/* echoserver.c
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

#include <cyassl/ssl.h>
#include <cyassl/test.h>

#ifndef NO_MAIN_DRIVER
    #define ECHO_OUT
#endif


#ifdef SESSION_STATS
    CYASSL_API void PrintSessionStats(void);
#endif


static void SignalReady(void* args)
{
#if defined(_POSIX_THREADS) && defined(NO_MAIN_DRIVER)
    /* signal ready to tcp_accept */
    func_args* server_args = (func_args*)args;
    tcp_ready* ready = server_args->signal;
    pthread_mutex_lock(&ready->mutex);
    ready->ready = 1;
    pthread_cond_signal(&ready->cond);
    pthread_mutex_unlock(&ready->mutex);
#endif
}


THREAD_RETURN CYASSL_THREAD echoserver_test(void* args)
{
    SOCKET_T       sockfd = 0;
    CYASSL_METHOD* method = 0;
    CYASSL_CTX*    ctx    = 0;

    int    doDTLS = 0;
    int    outCreated = 0;
    int    shutdown = 0;
    int    useAnyAddr = 0;
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

    ((func_args*)args)->return_code = -1; /* error state */

#ifdef CYASSL_DTLS
    doDTLS  = 1;
#endif

    tcp_listen(&sockfd, yasslPort, useAnyAddr, doDTLS);

#if defined(CYASSL_DTLS)
    method  = CyaDTLSv1_server_method();
#elif  !defined(NO_TLS)
    method = CyaSSLv23_server_method();
#else
    method = CyaSSLv3_server_method();
#endif
    ctx    = CyaSSL_CTX_new(method);
    /* CyaSSL_CTX_set_session_cache_mode(ctx, SSL_SESS_CACHE_OFF); */

#ifdef OPENSSL_EXTRA
    CyaSSL_CTX_set_default_passwd_cb(ctx, PasswordCallBack);
#endif

#ifndef NO_FILESYSTEM
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
    #elif HAVE_ECC
        /* ecc */
        if (CyaSSL_CTX_use_certificate_file(ctx, eccCert, SSL_FILETYPE_PEM)
                != SSL_SUCCESS)
            err_sys("can't load server cert file, "
                    "Please run from CyaSSL home dir");

        if (CyaSSL_CTX_use_PrivateKey_file(ctx, eccKey, SSL_FILETYPE_PEM)
                != SSL_SUCCESS)
            err_sys("can't load server key file, "
                    "Please run from CyaSSL home dir");
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
#else
    load_buffer(ctx, svrCert, CYASSL_CERT);
    load_buffer(ctx, svrKey,  CYASSL_KEY);
#endif

#if defined(CYASSL_SNIFFER) && !defined(HAVE_NTRU) && !defined(HAVE_ECC)
    /* don't use EDH, can't sniff tmp keys */
    CyaSSL_CTX_set_cipher_list(ctx, "AES256-SHA");
#endif

    SignalReady(args);

    while (!shutdown) {
        CYASSL* ssl = 0;
        char    command[1024];
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
        #if !defined(NO_FILESYSTEM) && defined(OPENSSL_EXTRA)
            CyaSSL_SetTmpDH_file(ssl, dhParam, SSL_FILETYPE_PEM);
        #else
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

        while ( (echoSz = CyaSSL_read(ssl, command, sizeof(command))) > 0) {

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
                shutdown = 1;
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
                echoSz += sizeof(header) - 1;
                strncpy(&command[echoSz], body, sizeof(body));
                echoSz += sizeof(body) - 1;
                strncpy(&command[echoSz], footer, sizeof(footer));
                echoSz += sizeof(footer);

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
        tcp_listen(&sockfd, yasslPort, useAnyAddr, doDTLS);
        SignalReady(args);
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

        StartTCP();

        args.argc = argc;
        args.argv = argv;

        CyaSSL_Init();
#ifdef DEBUG_CYASSL
        CyaSSL_Debugging_ON();
#endif
        if (CurrentDir("echoserver") || CurrentDir("build"))
            ChangeDirBack(2);
        echoserver_test(&args);
        CyaSSL_Cleanup();

        return args.return_code;
    }

    int myoptind = 0;
    char* myoptarg = NULL;

#endif /* NO_MAIN_DRIVER */



