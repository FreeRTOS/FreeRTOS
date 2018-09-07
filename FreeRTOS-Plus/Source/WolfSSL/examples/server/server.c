/* server.c
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
#include <cyassl/ssl.h> /* name change portability layer */

#include <cyassl/ctaocrypt/settings.h>
#ifdef HAVE_ECC
    #include <cyassl/ctaocrypt/ecc.h>   /* ecc_fp_free */
#endif

#if !defined(WOLFSSL_TRACK_MEMORY) && !defined(NO_MAIN_DRIVER)
    /* in case memory tracker wants stats */
    #define WOLFSSL_TRACK_MEMORY
#endif

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
#include <cyassl/openssl/ssl.h>
#include <cyassl/test.h>

#include "examples/server/server.h"


#ifdef CYASSL_CALLBACKS
    int srvHandShakeCB(HandShakeInfo*);
    int srvTimeoutCB(TimeoutInfo*);
    Timeval srvTo;
#endif

#ifndef NO_HANDSHAKE_DONE_CB
    int myHsDoneCb(WOLFSSL* ssl, void* user_ctx);
#endif



static void NonBlockingSSL_Accept(SSL* ssl)
{
#ifndef CYASSL_CALLBACKS
    int ret = SSL_accept(ssl);
#else
    int ret = CyaSSL_accept_ex(ssl, srvHandShakeCB, srvTimeoutCB, srvTo);
#endif
    int error = SSL_get_error(ssl, 0);
    SOCKET_T sockfd = (SOCKET_T)CyaSSL_get_fd(ssl);
    int select_ret;

    while (ret != SSL_SUCCESS && (error == SSL_ERROR_WANT_READ ||
                                  error == SSL_ERROR_WANT_WRITE)) {
        int currTimeout = 1;

        if (error == SSL_ERROR_WANT_READ)
            printf("... server would read block\n");
        else
            printf("... server would write block\n");

#ifdef CYASSL_DTLS
        currTimeout = CyaSSL_dtls_get_current_timeout(ssl);
#endif
        select_ret = tcp_select(sockfd, currTimeout);

        if ((select_ret == TEST_RECV_READY) ||
                                        (select_ret == TEST_ERROR_READY)) {
            #ifndef CYASSL_CALLBACKS
                ret = SSL_accept(ssl);
            #else
                ret = CyaSSL_accept_ex(ssl,
                                    srvHandShakeCB, srvTimeoutCB, srvTo);
            #endif
            error = SSL_get_error(ssl, 0);
        }
        else if (select_ret == TEST_TIMEOUT && !CyaSSL_dtls(ssl)) {
            error = SSL_ERROR_WANT_READ;
        }
#ifdef CYASSL_DTLS
        else if (select_ret == TEST_TIMEOUT && CyaSSL_dtls(ssl) &&
                                            CyaSSL_dtls_got_timeout(ssl) >= 0) {
            error = SSL_ERROR_WANT_READ;
        }
#endif
        else {
            error = SSL_FATAL_ERROR;
        }
    }
    if (ret != SSL_SUCCESS)
        err_sys("SSL_accept failed");
}


static void Usage(void)
{
    printf("server "    LIBCYASSL_VERSION_STRING
           " NOTE: All files relative to wolfSSL home dir\n");
    printf("-?          Help, print this usage\n");
    printf("-p <num>    Port to listen on, not 0, default %d\n", yasslPort);
    printf("-v <num>    SSL version [0-3], SSLv3(0) - TLS1.2(3)), default %d\n",
                                 SERVER_DEFAULT_VERSION);
    printf("-l <str>    Cipher list\n");
    printf("-c <file>   Certificate file,           default %s\n", svrCert);
    printf("-k <file>   Key file,                   default %s\n", svrKey);
    printf("-A <file>   Certificate Authority file, default %s\n", cliCert);
#ifndef NO_DH
    printf("-D <file>   Diffie-Hellman Params file, default %s\n", dhParam);
    printf("-Z <num>    Minimum DH key bits,        default %d\n",
                                 DEFAULT_MIN_DHKEY_BITS);
#endif
    printf("-d          Disable client cert check\n");
    printf("-b          Bind to any interface instead of localhost only\n");
    printf("-s          Use pre Shared keys\n");
    printf("-t          Track wolfSSL memory use\n");
    printf("-u          Use UDP DTLS,"
           " add -v 2 for DTLSv1 (default), -v 3 for DTLSv1.2\n");
    printf("-f          Fewer packets/group messages\n");
    printf("-R          Create server ready file, for external monitor\n");
    printf("-r          Allow one client Resumption\n");
    printf("-N          Use Non-blocking sockets\n");
    printf("-S <str>    Use Host Name Indication\n");
    printf("-w          Wait for bidirectional shutdown\n");
#ifdef HAVE_OCSP
    printf("-o          Perform OCSP lookup on peer certificate\n");
    printf("-O <url>    Perform OCSP lookup using <url> as responder\n");
#endif
#ifdef HAVE_PK_CALLBACKS 
    printf("-P          Public Key Callbacks\n");
#endif
#ifdef HAVE_ANON
    printf("-a          Anonymous server\n");
#endif
}

THREAD_RETURN CYASSL_THREAD server_test(void* args)
{
    SOCKET_T sockfd   = 0;
    SOCKET_T clientfd = 0;

    SSL_METHOD* method = 0;
    SSL_CTX*    ctx    = 0;
    SSL*        ssl    = 0;

    char   msg[] = "I hear you fa shizzle!";
    char   input[80];
    int    idx;
    int    ch;
    int    version = SERVER_DEFAULT_VERSION;
    int    doCliCertCheck = 1;
    int    useAnyAddr = 0;
    word16 port = yasslPort;
    int    usePsk = 0;
    int    useAnon = 0;
    int    doDTLS = 0;
    int    needDH = 0;
    int    useNtruKey   = 0;
    int    nonBlocking  = 0;
    int    trackMemory  = 0;
    int    fewerPackets = 0;
    int    pkCallbacks  = 0;
    int    serverReadyFile = 0;
    int    wc_shutdown     = 0;
    int    resume = 0;            /* do resume, and resume count */
    int    minDhKeyBits = DEFAULT_MIN_DHKEY_BITS;
    int    ret;
    char*  cipherList = NULL;
    const char* verifyCert = cliCert;
    const char* ourCert    = svrCert;
    const char* ourKey     = svrKey;
    const char* ourDhParam = dhParam;
    int    argc = ((func_args*)args)->argc;
    char** argv = ((func_args*)args)->argv;

#ifdef HAVE_SNI
    char*  sniHostName = NULL;
#endif

#ifdef HAVE_OCSP
    int    useOcsp  = 0;
    char*  ocspUrl  = NULL;
#endif

    ((func_args*)args)->return_code = -1; /* error state */

#ifdef NO_RSA
    verifyCert = (char*)cliEccCert;
    ourCert    = (char*)eccCert;
    ourKey     = (char*)eccKey;
#endif
    (void)trackMemory;
    (void)pkCallbacks;
    (void)needDH;
    (void)ourKey;
    (void)ourCert;
    (void)ourDhParam;
    (void)verifyCert;
    (void)useNtruKey;
    (void)doCliCertCheck;
    (void)minDhKeyBits;

#ifdef CYASSL_TIRTOS
    fdOpenSession(Task_self());
#endif

    while ((ch = mygetopt(argc, argv, "?dbstnNufrRawPp:v:l:A:c:k:Z:S:oO:D:"))
                         != -1) {
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

            case 't' :
            #ifdef USE_WOLFSSL_MEMORY
                trackMemory = 1;
            #endif
                break;

            case 'n' :
                useNtruKey = 1;
                break;

            case 'u' :
                doDTLS  = 1;
                break;

            case 'f' :
                fewerPackets = 1;
                break;

            case 'R' :
                serverReadyFile = 1;
                break;

            case 'r' :
                #ifndef NO_SESSION_CACHE
                    resume = 1;
                #endif
                break;

            case 'P' :
            #ifdef HAVE_PK_CALLBACKS 
                pkCallbacks = 1;
            #endif
                break;

            case 'p' :
                port = (word16)atoi(myoptarg);
                #if !defined(NO_MAIN_DRIVER) || defined(USE_WINDOWS_API)
                    if (port == 0)
                        err_sys("port number cannot be 0");
                #endif
                break;

            case 'w' :
                wc_shutdown = 1;
                break;

            case 'v' :
                version = atoi(myoptarg);
                if (version < 0 || version > 3) {
                    Usage();
                    exit(MY_EX_USAGE);
                }
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

            case 'D' :
                #ifndef NO_DH
                    ourDhParam = myoptarg;
                #endif
                break;

            case 'Z' :
                #ifndef NO_DH
                    minDhKeyBits = atoi(myoptarg);
                    if (minDhKeyBits <= 0 || minDhKeyBits > 16000) {
                        Usage();
                        exit(MY_EX_USAGE);
                    }
                #endif
                break;

            case 'N':
                nonBlocking = 1;
                break;

            case 'S' :
                #ifdef HAVE_SNI
                    sniHostName = myoptarg;
                #endif
                break;

            case 'o' :
                #ifdef HAVE_OCSP
                    useOcsp = 1;
                #endif
                break;

            case 'O' :
                #ifdef HAVE_OCSP
                    useOcsp = 1;
                    ocspUrl = myoptarg;
                #endif
                break;

            case 'a' :
                #ifdef HAVE_ANON
                    useAnon = 1;
                #endif
                break;

            default:
                Usage();
                exit(MY_EX_USAGE);
        }
    }

    myoptind = 0;      /* reset for test cases */

    /* sort out DTLS versus TLS versions */
    if (version == CLIENT_INVALID_VERSION) {
        if (doDTLS)
            version = CLIENT_DTLS_DEFAULT_VERSION;
        else
            version = CLIENT_DEFAULT_VERSION;
    }
    else {
        if (doDTLS) {
            if (version == 3)
                version = -2;
            else
                version = -1;
        }
    }

#ifdef USE_CYASSL_MEMORY
    if (trackMemory)
        InitMemoryTracker(); 
#endif

    switch (version) {
#ifndef NO_OLD_TLS
        case 0:
            method = SSLv3_server_method();
            break;

    #ifndef NO_TLS
        case 1:
            method = TLSv1_server_method();
            break;


        case 2:
            method = TLSv1_1_server_method();
            break;

        #endif
#endif

#ifndef NO_TLS
        case 3:
            method = TLSv1_2_server_method();
            break;
#endif
                
#ifdef CYASSL_DTLS
    #ifndef NO_OLD_TLS
        case -1:
            method = DTLSv1_server_method();
            break;
    #endif

        case -2:
            method = DTLSv1_2_server_method();
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

#if defined(HAVE_SESSION_TICKET) && defined(HAVE_CHACHA) && \
                                    defined(HAVE_POLY1305)
    if (TicketInit() != 0)
        err_sys("unable to setup Session Ticket Key context");
    wolfSSL_CTX_set_TicketEncCb(ctx, myTicketEncCb);
#endif

    if (cipherList)
        if (SSL_CTX_set_cipher_list(ctx, cipherList) != SSL_SUCCESS)
            err_sys("server can't set cipher list 1");

#ifdef CYASSL_LEANPSK
    usePsk = 1;
#endif

#if defined(NO_RSA) && !defined(HAVE_ECC)
    usePsk = 1;
#endif

    if (fewerPackets)
        CyaSSL_CTX_set_group_messages(ctx);

#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
    SSL_CTX_set_default_passwd_cb(ctx, PasswordCallBack);
#endif

#if !defined(NO_FILESYSTEM) && !defined(NO_CERTS)
    if (!usePsk && !useAnon) {
        if (SSL_CTX_use_certificate_file(ctx, ourCert, SSL_FILETYPE_PEM)
                                         != SSL_SUCCESS)
            err_sys("can't load server cert file, check file and run from"
                    " wolfSSL home dir");
    }
#endif

#ifndef NO_DH
    wolfSSL_CTX_SetMinDhKey_Sz(ctx, (word16)minDhKeyBits);
#endif

#ifdef HAVE_NTRU
    if (useNtruKey) {
        if (CyaSSL_CTX_use_NTRUPrivateKey_file(ctx, ourKey)
                                               != SSL_SUCCESS)
            err_sys("can't load ntru key file, "
                    "Please run from wolfSSL home dir");
    }
#endif

#if !defined(NO_FILESYSTEM) && !defined(NO_CERTS)
    if (!useNtruKey && !usePsk && !useAnon) {
        if (SSL_CTX_use_PrivateKey_file(ctx, ourKey, SSL_FILETYPE_PEM)
                                         != SSL_SUCCESS)
            err_sys("can't load server private key file, check file and run "
                "from wolfSSL home dir");
    }
#endif

    if (usePsk) {
#ifndef NO_PSK
        SSL_CTX_set_psk_server_callback(ctx, my_psk_server_cb);
        SSL_CTX_use_psk_identity_hint(ctx, "cyassl server");
        if (cipherList == NULL) {
            const char *defaultCipherList;
            #if defined(HAVE_AESGCM) && !defined(NO_DH)
                defaultCipherList = "DHE-PSK-AES128-GCM-SHA256";
                needDH = 1;
            #elif defined(HAVE_NULL_CIPHER)
                defaultCipherList = "PSK-NULL-SHA256";
            #else
                defaultCipherList = "PSK-AES128-CBC-SHA256";
            #endif
            if (SSL_CTX_set_cipher_list(ctx, defaultCipherList) != SSL_SUCCESS)
                err_sys("server can't set cipher list 2");
        }
#endif
    }

    if (useAnon) {
#ifdef HAVE_ANON
        CyaSSL_CTX_allow_anon_cipher(ctx);
        if (cipherList == NULL) {
            if (SSL_CTX_set_cipher_list(ctx, "ADH-AES128-SHA") != SSL_SUCCESS)
                err_sys("server can't set cipher list 4");
        }
#endif
    }

#if !defined(NO_FILESYSTEM) && !defined(NO_CERTS)
    /* if not using PSK, verify peer with certs */
    if (doCliCertCheck && usePsk == 0 && useAnon == 0) {
        SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER |
                                SSL_VERIFY_FAIL_IF_NO_PEER_CERT,0);
        if (SSL_CTX_load_verify_locations(ctx, verifyCert, 0) != SSL_SUCCESS)
            err_sys("can't load ca file, Please run from wolfSSL home dir");
    }
#endif

#if defined(CYASSL_SNIFFER)
    /* don't use EDH, can't sniff tmp keys */
    if (cipherList == NULL) {
        if (SSL_CTX_set_cipher_list(ctx, "AES256-SHA256") != SSL_SUCCESS)
            err_sys("server can't set cipher list 3");
    }
#endif

#ifdef HAVE_SNI
    if (sniHostName)
        if (CyaSSL_CTX_UseSNI(ctx, CYASSL_SNI_HOST_NAME, sniHostName,
                                           XSTRLEN(sniHostName)) != SSL_SUCCESS)
            err_sys("UseSNI failed");
#endif

while (1) {  /* allow resume option */
    if (resume > 1) {  /* already did listen, just do accept */
        if (doDTLS == 0) {
            SOCKADDR_IN_T client;
            socklen_t client_len = sizeof(client);
            clientfd = accept(sockfd, (struct sockaddr*)&client,
                             (ACCEPT_THIRD_T)&client_len);
        } else {
            tcp_listen(&sockfd, &port, useAnyAddr, doDTLS);
            clientfd = udp_read_connect(sockfd);
        }
        #ifdef USE_WINDOWS_API
            if (clientfd == INVALID_SOCKET) err_sys("tcp accept failed");
        #else
            if (clientfd == -1) err_sys("tcp accept failed");
        #endif
    }

    ssl = SSL_new(ctx);
    if (ssl == NULL)
        err_sys("unable to get SSL");

#ifndef NO_HANDSHAKE_DONE_CB
    wolfSSL_SetHsDoneCb(ssl, myHsDoneCb, NULL);
#endif
#ifdef HAVE_CRL
    CyaSSL_EnableCRL(ssl, 0);
    CyaSSL_LoadCRL(ssl, crlPemDir, SSL_FILETYPE_PEM, CYASSL_CRL_MONITOR |
                                                     CYASSL_CRL_START_MON);
    CyaSSL_SetCRL_Cb(ssl, CRL_CallBack);
#endif
#ifdef HAVE_OCSP
    if (useOcsp) {
        if (ocspUrl != NULL) {
            CyaSSL_CTX_SetOCSP_OverrideURL(ctx, ocspUrl);
            CyaSSL_CTX_EnableOCSP(ctx, CYASSL_OCSP_NO_NONCE
                                                    | CYASSL_OCSP_URL_OVERRIDE);
        }
        else
            CyaSSL_CTX_EnableOCSP(ctx, CYASSL_OCSP_NO_NONCE);
    }
#endif
#ifdef HAVE_PK_CALLBACKS
    if (pkCallbacks)
        SetupPkCallbacks(ctx, ssl);
#endif

    if (resume < 2) {  /* do listen and accept */
        tcp_accept(&sockfd, &clientfd, (func_args*)args, port, useAnyAddr,
                   doDTLS, serverReadyFile);
    }

    SSL_set_fd(ssl, clientfd);
    if (usePsk == 0 || useAnon == 1 || cipherList != NULL || needDH == 1) {
        #if !defined(NO_FILESYSTEM) && !defined(NO_DH) && !defined(NO_ASN)
            CyaSSL_SetTmpDH_file(ssl, ourDhParam, SSL_FILETYPE_PEM);
        #elif !defined(NO_DH)
            SetDH(ssl);  /* repick suites with DHE, higher priority than PSK */
        #endif
    }

#ifndef CYASSL_CALLBACKS
    if (nonBlocking) {
        CyaSSL_set_using_nonblock(ssl, 1);
        tcp_set_nonblocking(&clientfd);
        NonBlockingSSL_Accept(ssl);
    } else if (SSL_accept(ssl) != SSL_SUCCESS) {
        int err = SSL_get_error(ssl, 0);
        char buffer[CYASSL_MAX_ERROR_SZ];
        printf("error = %d, %s\n", err, ERR_error_string(err, buffer));
        err_sys("SSL_accept failed");
    }
#else
    NonBlockingSSL_Accept(ssl);
#endif
    showPeer(ssl);

    idx = SSL_read(ssl, input, sizeof(input)-1);
    if (idx > 0) {
        input[idx] = 0;
        printf("Client message: %s\n", input);

    }
    else if (idx < 0) {
        int readErr = SSL_get_error(ssl, 0);
        if (readErr != SSL_ERROR_WANT_READ)
            err_sys("SSL_read failed");
    }

    if (SSL_write(ssl, msg, sizeof(msg)) != sizeof(msg))
        err_sys("SSL_write failed");
        
    #if defined(CYASSL_MDK_SHELL) && defined(HAVE_MDK_RTX)
        os_dly_wait(500) ;
    #elif defined (CYASSL_TIRTOS)
        Task_yield();
    #endif

    if (doDTLS == 0) {
        ret = SSL_shutdown(ssl);
        if (wc_shutdown && ret == SSL_SHUTDOWN_NOT_DONE)
            SSL_shutdown(ssl);    /* bidirectional shutdown */
    }
    SSL_free(ssl);
    if (resume == 1) {
        CloseSocket(clientfd);
        resume++;           /* only do one resume for testing */
        continue;
    }
    break;  /* out of while loop, done with normal and resume option */
}
    SSL_CTX_free(ctx);

    CloseSocket(clientfd);
    CloseSocket(sockfd);
    ((func_args*)args)->return_code = 0;


#if defined(NO_MAIN_DRIVER) && defined(HAVE_ECC) && defined(FP_ECC) \
                            && defined(HAVE_THREAD_LS)
    ecc_fp_free();  /* free per thread cache */
#endif

#ifdef USE_WOLFSSL_MEMORY
    if (trackMemory)
        ShowMemoryTracker();
#endif

#ifdef CYASSL_TIRTOS
    fdCloseSession(Task_self());
#endif

#if defined(HAVE_SESSION_TICKET) && defined(HAVE_CHACHA) && \
                                    defined(HAVE_POLY1305)
    TicketCleanup();
#endif

#ifndef CYASSL_TIRTOS
    return 0;
#endif
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
        if (CurrentDir("_build"))
            ChangeDirBack(1);
        else if (CurrentDir("server"))
            ChangeDirBack(2);
        else if (CurrentDir("Debug") || CurrentDir("Release"))
            ChangeDirBack(3);
   
#ifdef HAVE_STACK_SIZE
        StackSizeCheck(&args, server_test);
#else 
        server_test(&args);
#endif
        CyaSSL_Cleanup();

#ifdef HAVE_CAVIUM
        CspShutdown(CAVIUM_DEV_ID);
#endif
        return args.return_code;
    }

    int myoptind = 0;
    char* myoptarg = NULL;

#endif /* NO_MAIN_DRIVER */


#ifdef CYASSL_CALLBACKS

    int srvHandShakeCB(HandShakeInfo* info)
    {
        (void)info;
        return 0;
    }


    int srvTimeoutCB(TimeoutInfo* info)
    {
        (void)info;
        return 0;
    }

#endif

#ifndef NO_HANDSHAKE_DONE_CB
    int myHsDoneCb(WOLFSSL* ssl, void* user_ctx)
    {
        (void)user_ctx;
        (void)ssl;

        /* printf("Notified HandShake done\n"); */

        /* return negative number to end TLS connection now */
        return 0;
    }
#endif


