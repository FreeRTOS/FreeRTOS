/* server.c
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


#ifdef CYASSL_CALLBACKS
    int srvHandShakeCB(HandShakeInfo*);
    int srvTimeoutCB(TimeoutInfo*);
    Timeval srvTo;
#endif

#if defined(NON_BLOCKING) || defined(CYASSL_CALLBACKS)
    void NonBlockingSSL_Accept(SSL* ssl)
    {
    #ifndef CYASSL_CALLBACKS
        int ret = SSL_accept(ssl);
    #else
        int ret = CyaSSL_accept_ex(ssl, srvHandShakeCB, srvTimeoutCB, srvTo);
    #endif
        int error = SSL_get_error(ssl, 0);
        while (ret != SSL_SUCCESS && (error == SSL_ERROR_WANT_READ ||
                                      error == SSL_ERROR_WANT_WRITE)) {
            printf("... server would block\n");
            #ifdef USE_WINDOWS_API 
                Sleep(1000);
            #else
                sleep(1);
            #endif
            #ifndef CYASSL_CALLBACKS
                ret = SSL_accept(ssl);
            #else
                ret = CyaSSL_accept_ex(ssl, srvHandShakeCB, srvTimeoutCB,srvTo);
            #endif
            error = SSL_get_error(ssl, 0);
        }
        if (ret != SSL_SUCCESS)
            err_sys("SSL_accept failed");
    }
#endif


THREAD_RETURN CYASSL_THREAD server_test(void* args)
{
    SOCKET_T sockfd   = 0;
    int      clientfd = 0;

    SSL_METHOD* method = 0;
    SSL_CTX*    ctx    = 0;
    SSL*        ssl    = 0;

    char msg[] = "I hear you fa shizzle!";
    char input[1024];
    int  idx;
   
    ((func_args*)args)->return_code = -1; /* error state */
#if defined(CYASSL_DTLS)
    method  = DTLSv1_server_method();
#elif  !defined(NO_TLS)
    method = SSLv23_server_method();
#else
    method = SSLv3_server_method();
#endif
    ctx    = SSL_CTX_new(method);

#ifndef NO_PSK
    /* do PSK */
    SSL_CTX_set_psk_server_callback(ctx, my_psk_server_cb);
    SSL_CTX_use_psk_identity_hint(ctx, "cyassl server");
    SSL_CTX_set_cipher_list(ctx, "PSK-AES256-CBC-SHA");
#else
    /* not using PSK, verify peer with certs */
    SSL_CTX_set_verify(ctx,SSL_VERIFY_PEER | SSL_VERIFY_FAIL_IF_NO_PEER_CERT,0);
#endif

#ifdef OPENSSL_EXTRA
    SSL_CTX_set_default_passwd_cb(ctx, PasswordCallBack);
#endif

#ifndef NO_FILESYSTEM
    /* for client auth */
    if (SSL_CTX_load_verify_locations(ctx, cliCert, 0) != SSL_SUCCESS)
        err_sys("can't load ca file, Please run from CyaSSL home dir");

    #ifdef HAVE_ECC
        if (SSL_CTX_use_certificate_file(ctx, eccCert, SSL_FILETYPE_PEM)
                != SSL_SUCCESS)
            err_sys("can't load server ecc cert file, "
                    "Please run from CyaSSL home dir");

        if (SSL_CTX_use_PrivateKey_file(ctx, eccKey, SSL_FILETYPE_PEM)
                != SSL_SUCCESS)
            err_sys("can't load server ecc key file, "
                    "Please run from CyaSSL home dir");
        /* for client auth */
        if (SSL_CTX_load_verify_locations(ctx, cliEccCert, 0) != SSL_SUCCESS)
            err_sys("can't load ecc ca file, Please run from CyaSSL home dir");

    #elif HAVE_NTRU
        if (SSL_CTX_use_certificate_file(ctx, ntruCert, SSL_FILETYPE_PEM)
                != SSL_SUCCESS)
            err_sys("can't load ntru cert file, "
                    "Please run from CyaSSL home dir");

        if (CyaSSL_CTX_use_NTRUPrivateKey_file(ctx, ntruKey)
                != SSL_SUCCESS)
            err_sys("can't load ntru key file, "
                    "Please run from CyaSSL home dir");
    #else  /* normal */
        if (SSL_CTX_use_certificate_file(ctx, svrCert, SSL_FILETYPE_PEM)
                != SSL_SUCCESS)
            err_sys("can't load server cert chain file, "
                    "Please run from CyaSSL home dir");

        if (SSL_CTX_use_PrivateKey_file(ctx, svrKey, SSL_FILETYPE_PEM)
                != SSL_SUCCESS)
            err_sys("can't load server key file, "
                    "Please run from CyaSSL home dir");
    #endif /* NTRU */
#else
    load_buffer(ctx, cliCert, CYASSL_CA);
    load_buffer(ctx, svrCert, CYASSL_CERT);
    load_buffer(ctx, svrKey,  CYASSL_KEY);
#endif /* NO_FILESYSTEM */

    ssl = SSL_new(ctx);
    tcp_accept(&sockfd, &clientfd, (func_args*)args);
#ifndef CYASSL_DTLS
    CloseSocket(sockfd);
#endif

    SSL_set_fd(ssl, clientfd);
#ifdef NO_PSK
    #if !defined(NO_FILESYSTEM) && defined(OPENSSL_EXTRA)
        CyaSSL_SetTmpDH_file(ssl, dhParam, SSL_FILETYPE_PEM);
    #else
        SetDH(ssl);  /* will repick suites with DHE, higher priority than PSK */
    #endif
#endif

#ifdef NON_BLOCKING
    tcp_set_nonblocking(&clientfd);
    NonBlockingSSL_Accept(ssl);
#else
    #ifndef CYASSL_CALLBACKS
        if (SSL_accept(ssl) != SSL_SUCCESS) {
            int err = SSL_get_error(ssl, 0);
            char buffer[80];
            printf("error = %d, %s\n", err, ERR_error_string(err, buffer));
            err_sys("SSL_accept failed");
        }
    #else
        NonBlockingSSL_Accept(ssl);
    #endif
#endif
    showPeer(ssl);

    idx = SSL_read(ssl, input, sizeof(input));
    if (idx > 0) {
        input[idx] = 0;
        printf("Client message: %s\n", input);
    }
    
    if (SSL_write(ssl, msg, sizeof(msg)) != sizeof(msg))
        err_sys("SSL_write failed");

    SSL_shutdown(ssl);
    SSL_free(ssl);
    SSL_CTX_free(ctx);
    
    CloseSocket(clientfd);
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
        if (CurrentDir("server") || CurrentDir("build"))
            ChangeDirBack(2);
   
        server_test(&args);
        CyaSSL_Cleanup();

        return args.return_code;
    }

#endif /* NO_MAIN_DRIVER */


#ifdef CYASSL_CALLBACKS

    int srvHandShakeCB(HandShakeInfo* info)
    {

        return 0;
    }


    int srvTimeoutCB(TimeoutInfo* info)
    {

        return 0;
    }

#endif


