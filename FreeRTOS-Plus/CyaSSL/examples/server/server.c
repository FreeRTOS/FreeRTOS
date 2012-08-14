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


static void Usage(void)
{
    printf("server "    LIBCYASSL_VERSION_STRING
           " NOTE: All files relative to CyaSSL home dir\n");
    printf("-?          Help, print this usage\n");
    printf("-p <num>    Port to listen on, default %d\n", yasslPort);
    printf("-v <num>    SSL version [0-3], SSLv3(0) - TLS1.2(3)), default %d\n",
                                 SERVER_DEFAULT_VERSION);
    printf("-l <str>    Cipher list\n");
    printf("-c <file>   Certificate file,           default %s\n", svrCert);
    printf("-k <file>   Key file,                   default %s\n", svrKey);
    printf("-A <file>   Certificate Authority file, default %s\n", cliCert);
    printf("-d          Disable client cert check\n");
    printf("-b          Bind to any interface instead of localhost only\n");
    printf("-s          Use pre Shared keys\n");
    printf("-u          Use UDP DTLS\n");
}


THREAD_RETURN CYASSL_THREAD server_test(void* args)
{
    SOCKET_T sockfd   = 0;
    int      clientfd = 0;

    SSL_METHOD* method = 0;
    SSL_CTX*    ctx    = 0;
    SSL*        ssl    = 0;

    char   msg[] = "I hear you fa shizzle!";
    char   input[1024];
    int    idx;
    int    ch;
    int    version = SERVER_DEFAULT_VERSION;
    int    doCliCertCheck = 1;
    int    useAnyAddr = 0;
    int    port = yasslPort;
    int    usePsk = 0;
    int    doDTLS = 0;
    int    useNtruKey = 0;
    char*  cipherList = NULL;
    char*  verifyCert = (char*)cliCert;
    char*  ourCert    = (char*)svrCert;
    char*  ourKey     = (char*)svrKey;
    int    argc = ((func_args*)args)->argc;
    char** argv = ((func_args*)args)->argv;

    ((func_args*)args)->return_code = -1; /* error state */

    while ((ch = mygetopt(argc, argv, "?dbsnup:v:l:A:c:k:")) != -1) {
        switch (ch) {
            case '?' :
                Usage();
                exit(EXIT_SUCCESS);

            case 'd' :
                doCliCertCheck = 0;
                break;

            case 'b' :
                useAnyAddr = 1;
                break;

            case 's' :
                usePsk = 1;
                break;

            case 'n' :
                useNtruKey = 1;
                break;

            case 'u' :
                doDTLS  = 1;
                version = -1;  /* DTLS flag */
                break;

            case 'p' :
                port = atoi(myoptarg);
                break;

            case 'v' :
                version = atoi(myoptarg);
                if (version < 0 || version > 3) {
                    Usage();
                    exit(MY_EX_USAGE);
                }
                if (doDTLS)
                    version = -1;  /* stay with DTLS */
                break;

            case 'l' :
                cipherList = myoptarg;
                break;

            case 'A' :
                verifyCert = myoptarg;
                break;

            case 'c' :
                ourCert = myoptarg;
                break;

            case 'k' :
                ourKey = myoptarg;
                break;

            default:
                Usage();
                exit(MY_EX_USAGE);
        }
    }

    argc -= myoptind;
    argv += myoptind;
    myoptind = 0;      /* reset for test cases */

    switch (version) {
        case 0:
            method = SSLv3_server_method();
            break;

        case 1:
            method = TLSv1_server_method();
            break;

        case 2:
            method = TLSv1_1_server_method();
            break;

        case 3:
            method = TLSv1_2_server_method();
            break;

#ifdef CYASSL_DTLS
        case -1:
            method = DTLSv1_server_method();
            break;
#endif

        default:
            err_sys("Bad SSL version");
    }

    if (method == NULL)
        err_sys("unable to get method");

    ctx = SSL_CTX_new(method);
    if (ctx == NULL)
        err_sys("unable to get ctx");

    if (cipherList)
        if (SSL_CTX_set_cipher_list(ctx, cipherList) != SSL_SUCCESS)
            err_sys("can't set cipher list");

    if (SSL_CTX_use_certificate_file(ctx, ourCert, SSL_FILETYPE_PEM)
                                     != SSL_SUCCESS)
        err_sys("can't load server cert file, check file and run from"
                " CyaSSL home dir");


#ifdef HAVE_NTRU
    if (useNtruKey) {
        if (CyaSSL_CTX_use_NTRUPrivateKey_file(ctx, ourKey)
                                               != SSL_SUCCESS)
            err_sys("can't load ntru key file, "
                    "Please run from CyaSSL home dir");
    }
#endif

    if (!useNtruKey) {
        if (SSL_CTX_use_PrivateKey_file(ctx, ourKey, SSL_FILETYPE_PEM)
                                         != SSL_SUCCESS)
            err_sys("can't load server cert file, check file and run from"
                " CyaSSL home dir");
    }

#ifndef NO_PSK
    if (usePsk) {
        SSL_CTX_set_psk_server_callback(ctx, my_psk_server_cb);
        SSL_CTX_use_psk_identity_hint(ctx, "cyassl server");
        if (cipherList == NULL)
            if (SSL_CTX_set_cipher_list(ctx,"PSK-AES256-CBC-SHA") !=SSL_SUCCESS)
                err_sys("can't set cipher list");
    }
#endif

    /* if not using PSK, verify peer with certs */
    if (doCliCertCheck && usePsk == 0) {
        SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER |
                                SSL_VERIFY_FAIL_IF_NO_PEER_CERT,0);
        if (SSL_CTX_load_verify_locations(ctx, verifyCert, 0) != SSL_SUCCESS)
            err_sys("can't load ca file, Please run from CyaSSL home dir");
    }

#ifdef OPENSSL_EXTRA
    SSL_CTX_set_default_passwd_cb(ctx, PasswordCallBack);
#endif

#if defined(CYASSL_SNIFFER) && !defined(HAVE_NTRU) && !defined(HAVE_ECC)
    /* don't use EDH, can't sniff tmp keys */
    if (SSL_CTX_set_cipher_list(ctx, "AES256-SHA") != SSL_SUCCESS)
        err_sys("can't set cipher list");
#endif

    ssl = SSL_new(ctx);
    if (ssl == NULL)
        err_sys("unable to get SSL");

#ifdef HAVE_CRL
    CyaSSL_EnableCRL(ssl, 0);
    CyaSSL_LoadCRL(ssl, crlPemDir, SSL_FILETYPE_PEM, CYASSL_CRL_MONITOR |
                                                     CYASSL_CRL_START_MON);
    CyaSSL_SetCRL_Cb(ssl, CRL_CallBack);
#endif
    tcp_accept(&sockfd, &clientfd, (func_args*)args, port, useAnyAddr, doDTLS);
    if (!doDTLS) 
        CloseSocket(sockfd);

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

    int myoptind = 0;
    char* myoptarg = NULL;

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


