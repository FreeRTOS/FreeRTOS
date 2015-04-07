/* echoclient.c
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

#include <cyassl/openssl/ssl.h>

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

#include <cyassl/test.h>

#include "examples/echoclient/echoclient.h"

void echoclient_test(void* args)
{
    SOCKET_T sockfd = 0;

    FILE* fin   = stdin  ;
    FILE* fout = stdout;

    int inCreated  = 0;
    int outCreated = 0;

    char msg[1024];
    char reply[1024+1];

    SSL_METHOD* method = 0;
    SSL_CTX*    ctx    = 0;
    SSL*        ssl    = 0;

    int doDTLS = 0;
    int doPSK = 0;
    int sendSz;
    int argc    = 0;
    char** argv = 0;
    word16 port = yasslPort;

    ((func_args*)args)->return_code = -1; /* error state */
    
#ifndef CYASSL_MDK_SHELL
    argc = ((func_args*)args)->argc;
    argv = ((func_args*)args)->argv;
#endif

    if (argc >= 2) {
        fin  = fopen(argv[1], "r"); 
        inCreated = 1;
    }
    if (argc >= 3) {
        fout = fopen(argv[2], "w");
        outCreated = 1;
    }

    if (!fin)  err_sys("can't open input file");
    if (!fout) err_sys("can't open output file");

#ifdef CYASSL_DTLS
    doDTLS  = 1;
#endif

#ifdef CYASSL_LEANPSK 
    doPSK = 1;
#endif

#if defined(NO_RSA) && !defined(HAVE_ECC)
    doPSK = 1;
#endif

#if defined(NO_MAIN_DRIVER) && !defined(USE_WINDOWS_API) && !defined(CYASSL_MDK_SHELL)
    port = ((func_args*)args)->signal->port;
#endif

#if defined(CYASSL_DTLS)
    method  = DTLSv1_client_method();
#elif  !defined(NO_TLS)
    method = CyaSSLv23_client_method();
#else
    method = SSLv3_client_method();
#endif
    ctx    = SSL_CTX_new(method);

#ifndef NO_FILESYSTEM
    #ifndef NO_RSA
    if (SSL_CTX_load_verify_locations(ctx, caCert, 0) != SSL_SUCCESS)
        err_sys("can't load ca file, Please run from CyaSSL home dir");
    #endif
    #ifdef HAVE_ECC
        if (SSL_CTX_load_verify_locations(ctx, eccCert, 0) != SSL_SUCCESS)
            err_sys("can't load ca file, Please run from CyaSSL home dir");
    #endif
#elif !defined(NO_CERTS)
    if (!doPSK)
        load_buffer(ctx, caCert, CYASSL_CA);
#endif

#if defined(CYASSL_SNIFFER) && !defined(HAVE_NTRU) && !defined(HAVE_ECC)
    /* don't use EDH, can't sniff tmp keys */
    SSL_CTX_set_cipher_list(ctx, "AES256-SHA");
#endif
    if (doPSK) {
#ifndef NO_PSK
        const char *defaultCipherList;

        CyaSSL_CTX_set_psk_client_callback(ctx, my_psk_client_cb);
        #ifdef HAVE_NULL_CIPHER
            defaultCipherList = "PSK-NULL-SHA256";
        #else
            defaultCipherList = "PSK-AES128-CBC-SHA256";
        #endif
        if (CyaSSL_CTX_set_cipher_list(ctx,defaultCipherList) !=SSL_SUCCESS)
            err_sys("client can't set cipher list 2");
#endif
    }

#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
    SSL_CTX_set_default_passwd_cb(ctx, PasswordCallBack);
#endif

    #if defined(CYASSL_MDK_ARM)
    CyaSSL_CTX_set_verify(ctx, SSL_VERIFY_NONE, 0);
    #endif

    ssl = SSL_new(ctx);
        

    if (doDTLS) {
        SOCKADDR_IN_T addr;
        build_addr(&addr, yasslIP, port, 1);
        CyaSSL_dtls_set_peer(ssl, &addr, sizeof(addr));
        tcp_socket(&sockfd, 1);
    }
    else {
        tcp_connect(&sockfd, yasslIP, port, 0);
    }
        
    SSL_set_fd(ssl, sockfd);
#if defined(USE_WINDOWS_API) && defined(CYASSL_DTLS) && defined(NO_MAIN_DRIVER)
    /* let echoserver bind first, TODO: add Windows signal like pthreads does */
    Sleep(100);
#endif

    if (SSL_connect(ssl) != SSL_SUCCESS) err_sys("SSL_connect failed");

    while (fgets(msg, sizeof(msg), fin) != 0) {
     
        sendSz = (int)strlen(msg);

        if (SSL_write(ssl, msg, sendSz) != sendSz)
            err_sys("SSL_write failed");

        if (strncmp(msg, "quit", 4) == 0) {
            fputs("sending server shutdown command: quit!\n", fout);
            break;
        }

        if (strncmp(msg, "break", 5) == 0) {
            fputs("sending server session close: break!\n", fout);
            break;
        }

        #ifndef CYASSL_MDK_SHELL
        while (sendSz) {
            int got;
            if ( (got = SSL_read(ssl, reply, sizeof(reply)-1)) > 0) {
                reply[got] = 0;
                fputs(reply, fout);
                fflush(fout) ;
                sendSz -= got;
            }
            else
                break;
        }
        #else
        {
            int got;
            if ( (got = SSL_read(ssl, reply, sizeof(reply)-1)) > 0) {
                reply[got] = 0;
                fputs(reply, fout);
                fflush(fout) ;
                sendSz -= got;
            }
        }
        #endif
    }


#ifdef CYASSL_DTLS
    strncpy(msg, "break", 6);
    sendSz = (int)strlen(msg);
    /* try to tell server done */
    SSL_write(ssl, msg, sendSz);
#else
    SSL_shutdown(ssl);
#endif

    SSL_free(ssl);
    SSL_CTX_free(ctx);

    fflush(fout);
    if (inCreated)  fclose(fin);
    if (outCreated) fclose(fout);

    CloseSocket(sockfd);
    ((func_args*)args)->return_code = 0; 
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

        if (CurrentDir("echoclient"))
            ChangeDirBack(2);
        else if (CurrentDir("Debug") || CurrentDir("Release"))
            ChangeDirBack(3);
        echoclient_test(&args);

        CyaSSL_Cleanup();

#ifdef HAVE_CAVIUM
        CspShutdown(CAVIUM_DEV_ID);
#endif
        return args.return_code;
    }
        
#endif /* NO_MAIN_DRIVER */


