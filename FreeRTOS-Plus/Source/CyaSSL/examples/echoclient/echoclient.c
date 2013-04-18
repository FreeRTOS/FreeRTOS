/* echoclient.c
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

#include <cyassl/openssl/ssl.h>
#include <cyassl/test.h>


void echoclient_test(void* args)
{
    SOCKET_T sockfd = 0;

    FILE* fin  = stdin;
    FILE* fout = stdout;

    int inCreated  = 0;
    int outCreated = 0;

    char send[1024];
    char reply[1024];

    SSL_METHOD* method = 0;
    SSL_CTX*    ctx    = 0;
    SSL*        ssl    = 0;

    int doDTLS = 0;
    int sendSz;
    int argc    = 0;
    char** argv = 0;

    ((func_args*)args)->return_code = -1; /* error state */
    argc = ((func_args*)args)->argc;
    argv = ((func_args*)args)->argv;

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

    tcp_connect(&sockfd, yasslIP, yasslPort, doDTLS);

#if defined(CYASSL_DTLS)
    method  = DTLSv1_client_method();
#elif  !defined(NO_TLS)
    method = CyaSSLv23_client_method();
#else
    method = SSLv3_client_method();
#endif
    ctx    = SSL_CTX_new(method);

#ifndef NO_FILESYSTEM
    if (SSL_CTX_load_verify_locations(ctx, caCert, 0) != SSL_SUCCESS)
        err_sys("can't load ca file, Please run from CyaSSL home dir");
    #ifdef HAVE_ECC
        if (SSL_CTX_load_verify_locations(ctx, eccCert, 0) != SSL_SUCCESS)
            err_sys("can't load ca file, Please run from CyaSSL home dir");
    #endif
#else
    load_buffer(ctx, caCert, CYASSL_CA);
#endif

#if defined(CYASSL_SNIFFER) && !defined(HAVE_NTRU) && !defined(HAVE_ECC)
    /* don't use EDH, can't sniff tmp keys */
    SSL_CTX_set_cipher_list(ctx, "AES256-SHA");
#endif

#ifdef OPENSSL_EXTRA
    SSL_CTX_set_default_passwd_cb(ctx, PasswordCallBack);
#endif
    ssl = SSL_new(ctx);

    SSL_set_fd(ssl, sockfd);
#if defined(USE_WINDOWS_API) && defined(CYASSL_DTLS) && defined(NO_MAIN_DRIVER)
    /* let echoserver bind first, TODO: add Windows signal like pthreads does */
    Sleep(100);
#endif
    if (SSL_connect(ssl) != SSL_SUCCESS) err_sys("SSL_connect failed");

    while (fgets(send, sizeof(send), fin)) {

        sendSz = (int)strlen(send);

        if (SSL_write(ssl, send, sendSz) != sendSz)
            err_sys("SSL_write failed");

        if (strncmp(send, "quit", 4) == 0) {
            fputs("sending server shutdown command: quit!\n", fout);
            break;
        }

        if (strncmp(send, "break", 5) == 0) {
            fputs("sending server session close: break!\n", fout);
            break;
        }

        while (sendSz) {
            int got;
            if ( (got = SSL_read(ssl, reply, sizeof(reply))) > 0) {
                reply[got] = 0;
                fputs(reply, fout);
                sendSz -= got;
            }
            else
                break;
        }
    }

#ifdef CYASSL_DTLS
    strncpy(send, "break", 6);
    sendSz = (int)strlen(send);
    /* try to tell server done */
    SSL_write(ssl, send, sendSz);
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

        StartTCP();

        args.argc = argc;
        args.argv = argv;

        CyaSSL_Init();
#ifdef DEBUG_CYASSL
        CyaSSL_Debugging_ON();
#endif
        if (CurrentDir("echoclient") || CurrentDir("build"))
            ChangeDirBack(2);
        echoclient_test(&args);
        CyaSSL_Cleanup();

        return args.return_code;
    }

    int myoptind = 0;
    char* myoptarg = NULL;

#endif /* NO_MAIN_DRIVER */



