/* client.c
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

/*
#define TEST_RESUME 
*/


#ifdef CYASSL_CALLBACKS
    int handShakeCB(HandShakeInfo*);
    int timeoutCB(TimeoutInfo*);
    Timeval timeout;
#endif

#if defined(NON_BLOCKING) || defined(CYASSL_CALLBACKS)
    void NonBlockingSSL_Connect(CyaSSL* ssl)
    {
#ifndef CYASSL_CALLBACKS
        int ret = CyaSSL_connect(ssl);
#else
        int ret = CyaSSL_connect_ex(ssl, handShakeCB, timeoutCB, timeout);
#endif
        int error = CyaSSL_get_error(ssl, 0);
        while (ret != SSL_SUCCESS && (error == SSL_ERROR_WANT_READ ||
                                      error == SSL_ERROR_WANT_WRITE)) {
            if (error == SSL_ERROR_WANT_READ)
                printf("... client would read block\n");
            else
                printf("... client would write block\n");
            #ifdef USE_WINDOWS_API 
                Sleep(100);
            #else
                sleep(1);
            #endif
            #ifndef CYASSL_CALLBACKS
                ret = CyaSSL_connect(ssl);
            #else
                ret = CyaSSL_connect_ex(ssl, handShakeCB, timeoutCB, timeout);
            #endif
            error = CyaSSL_get_error(ssl, 0);
        }
        if (ret != SSL_SUCCESS)
            err_sys("SSL_connect failed");
    }
#endif


void client_test(void* args)
{
    SOCKET_T sockfd = 0;

    CYASSL_METHOD*  method  = 0;
    CYASSL_CTX*     ctx     = 0;
    CYASSL*         ssl     = 0;
    
#ifdef TEST_RESUME
    CYASSL*         sslResume = 0;
    CYASSL_SESSION* session = 0;
    char         resumeMsg[] = "resuming cyassl!";
    int          resumeSz    = sizeof(resumeMsg);
#endif

    char msg[64] = "hello cyassl!";
    char reply[1024];
    int  input;
    int  msgSz = strlen(msg);

    int     argc = ((func_args*)args)->argc;
    char**  argv = ((func_args*)args)->argv;

    ((func_args*)args)->return_code = -1; /* error state */

#if defined(CYASSL_DTLS)
    method  = CyaDTLSv1_client_method();
#elif  !defined(NO_TLS)
    method  = CyaSSLv23_client_method();
#else
    method  = CyaSSLv3_client_method();
#endif
    ctx     = CyaSSL_CTX_new(method);

#ifndef NO_PSK
    CyaSSL_CTX_set_psk_client_callback(ctx, my_psk_client_cb);
#endif

#ifdef OPENSSL_EXTRA
    CyaSSL_CTX_set_default_passwd_cb(ctx, PasswordCallBack);
#endif

#if defined(CYASSL_SNIFFER) && !defined(HAVE_NTRU) && !defined(HAVE_ECC)
    /* don't use EDH, can't sniff tmp keys */
    CyaSSL_CTX_set_cipher_list(ctx, "AES256-SHA");
#endif

#ifdef USER_CA_CB
    CyaSSL_CTX_SetCACb(ctx, CaCb);
#endif

#ifndef NO_FILESYSTEM
    if (CyaSSL_CTX_load_verify_locations(ctx, caCert, 0) != SSL_SUCCESS)
        err_sys("can't load ca file, Please run from CyaSSL home dir");
    #ifdef HAVE_ECC
        if (CyaSSL_CTX_load_verify_locations(ctx, eccCert, 0) != SSL_SUCCESS)
            err_sys("can't load ca file, Please run from CyaSSL home dir");
    #endif
#else
    load_buffer(ctx, caCert, CYASSL_CA);
#endif

#ifdef VERIFY_CALLBACK
    CyaSSL_CTX_set_verify(ctx, SSL_VERIFY_PEER, myVerify);
#endif


    if (argc == 3) {
        /*  ./client server securePort  */
        CyaSSL_CTX_set_verify(ctx, SSL_VERIFY_NONE, 0);  /* TODO: add ca cert */
                    /* this is just to allow easy testing of other servers */
        tcp_connect(&sockfd, argv[1], (short)atoi(argv[2]));
    }
    else if (argc == 1) {
        /* ./client          // plain mode */
        /* for client cert authentication if server requests */
#ifndef NO_FILESYSTEM
    #ifdef HAVE_ECC
        if (CyaSSL_CTX_use_certificate_file(ctx, cliEccCert, SSL_FILETYPE_PEM)
                != SSL_SUCCESS)
            err_sys("can't load ecc client cert file, "
                    "Please run from CyaSSL home dir");

        if (CyaSSL_CTX_use_PrivateKey_file(ctx, cliEccKey, SSL_FILETYPE_PEM)
                != SSL_SUCCESS)
            err_sys("can't load ecc client key file, "
                    "Please run from CyaSSL home dir");
    #else
        if (CyaSSL_CTX_use_certificate_file(ctx, cliCert, SSL_FILETYPE_PEM)
                != SSL_SUCCESS)
            err_sys("can't load client cert file, "
                    "Please run from CyaSSL home dir");

        if (CyaSSL_CTX_use_PrivateKey_file(ctx, cliKey, SSL_FILETYPE_PEM)
                != SSL_SUCCESS)
            err_sys("can't load client key file, "
                    "Please run from CyaSSL home dir");
    #endif /* HAVE_ECC */
#else
        load_buffer(ctx, cliCert, CYASSL_CERT);
        load_buffer(ctx, cliKey, CYASSL_KEY);
#endif

        tcp_connect(&sockfd, yasslIP, yasslPort);
    }
    else if (argc == 2) {
        /* time passed in number of connects give average */
        int times = atoi(argv[1]);
        int i = 0;

        double start = current_time(), avg;

        for (i = 0; i < times; i++) {
            tcp_connect(&sockfd, yasslIP, yasslPort);
            ssl = CyaSSL_new(ctx);
            CyaSSL_set_fd(ssl, sockfd);
            if (CyaSSL_connect(ssl) != SSL_SUCCESS)
                err_sys("SSL_connect failed");

            CyaSSL_shutdown(ssl);
            CyaSSL_free(ssl);
            CloseSocket(sockfd);
        }
        avg = current_time() - start;
        avg /= times;
        avg *= 1000;    /* milliseconds */  
        printf("SSL_connect avg took:%6.3f milliseconds\n", avg);

        CyaSSL_CTX_free(ctx);
        ((func_args*)args)->return_code = 0;
        return;
    }
    else
        err_sys("usage: ./client server securePort");

    ssl = CyaSSL_new(ctx);
    CyaSSL_set_fd(ssl, sockfd);
#ifdef HAVE_CRL
    CyaSSL_EnableCRL(ssl, 0);
    CyaSSL_LoadCRL(ssl, crlPemDir, SSL_FILETYPE_PEM, 0);
    CyaSSL_SetCRL_Cb(ssl, CRL_CallBack);
#endif
    if (argc != 3)
        CyaSSL_check_domain_name(ssl, "www.yassl.com");
#ifdef NON_BLOCKING
    tcp_set_nonblocking(&sockfd);
    NonBlockingSSL_Connect(ssl);
#else
    #ifndef CYASSL_CALLBACKS
        if (CyaSSL_connect(ssl) != SSL_SUCCESS) {/* see note at top of README */
            int  err = CyaSSL_get_error(ssl, 0);
            char buffer[80];
            printf("err = %d, %s\n", err, CyaSSL_ERR_error_string(err, buffer));
            err_sys("SSL_connect failed");/* if you're getting an error here  */
        }
    #else
        timeout.tv_sec  = 2;
        timeout.tv_usec = 0;
        NonBlockingSSL_Connect(ssl);  /* will keep retrying on timeout */
    #endif
#endif
    showPeer(ssl);
    
    if (argc == 3) {
        printf("SSL connect ok, sending GET...\n");
        msgSz = 28;
        strncpy(msg, "GET /index.html HTTP/1.0\r\n\r\n", msgSz);
    }
    if (CyaSSL_write(ssl, msg, msgSz) != msgSz)
        err_sys("SSL_write failed");

    input = CyaSSL_read(ssl, reply, sizeof(reply));
    if (input > 0) {
        reply[input] = 0;
        printf("Server response: %s\n", reply);

        if (argc == 3) {  /* get html */
            while (1) {
                input = CyaSSL_read(ssl, reply, sizeof(reply));
                if (input > 0) {
                    reply[input] = 0;
                    printf("%s\n", reply);
                }
                else
                    break;
            }
        }
    }
  
#ifdef TEST_RESUME
    #ifdef CYASSL_DTLS
        strncpy(msg, "break", 6);
        msgSz = (int)strlen(msg);
        /* try to send session close */
        CyaSSL_write(ssl, msg, msgSz);
    #endif
    session   = CyaSSL_get_session(ssl);
    sslResume = CyaSSL_new(ctx);
#endif

    CyaSSL_shutdown(ssl);
    CyaSSL_free(ssl);
    CloseSocket(sockfd);

#ifdef TEST_RESUME
    #ifdef CYASSL_DTLS
        #ifdef USE_WINDOWS_API 
            Sleep(500);
        #else
            sleep(1);
        #endif
    #endif
    if (argc == 3)
        tcp_connect(&sockfd, argv[1], (short)atoi(argv[2]));
    else
        tcp_connect(&sockfd, yasslIP, yasslPort);
    CyaSSL_set_fd(sslResume, sockfd);
    CyaSSL_set_session(sslResume, session);
   
    showPeer(sslResume); 
    if (CyaSSL_connect(sslResume) != SSL_SUCCESS) err_sys("SSL resume failed");

#ifdef OPENSSL_EXTRA
    if (CyaSSL_session_reused(sslResume))
        printf("reused session id\n");
    else
        printf("didn't reuse session id!!!\n");
#endif
  
    if (CyaSSL_write(sslResume, resumeMsg, resumeSz) != resumeSz)
        err_sys("SSL_write failed");

    input = CyaSSL_read(sslResume, reply, sizeof(reply));
    if (input > 0) {
        reply[input] = 0;
        printf("Server resume response: %s\n", reply);
    }

    /* try to send session break */
    CyaSSL_write(sslResume, msg, msgSz); 

    CyaSSL_shutdown(sslResume);
    CyaSSL_free(sslResume);
#endif /* TEST_RESUME */

    CyaSSL_CTX_free(ctx);
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
        if (CurrentDir("client") || CurrentDir("build"))
            ChangeDirBack(2);
   
        client_test(&args);
        CyaSSL_Cleanup();

        return args.return_code;
    }

#endif /* NO_MAIN_DRIVER */



#ifdef CYASSL_CALLBACKS

    int handShakeCB(HandShakeInfo* info)
    {

        return 0;
    }


    int timeoutCB(TimeoutInfo* info)
    {

        return 0;
    }

#endif


