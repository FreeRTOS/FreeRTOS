/* client.c
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

#include <wolfssl/ssl.h>

#if defined(WOLFSSL_MDK_ARM)
        #include <stdio.h>
        #include <string.h>

        #if defined(WOLFSSL_MDK5)
            #include "cmsis_os.h"
            #include "rl_fs.h" 
            #include "rl_net.h" 
        #else
            #include "rtl.h"
        #endif

        #include "wolfssl_MDK_ARM.h"
#endif

#include <wolfssl/wolfcrypt/settings.h>

#if !defined(WOLFSSL_TRACK_MEMORY) && !defined(NO_MAIN_DRIVER)
    /* in case memory tracker wants stats */
    #define WOLFSSL_TRACK_MEMORY
#endif

#include <wolfssl/ssl.h>

#include <wolfssl/test.h>

#include "examples/client/client.h"


#ifdef WOLFSSL_CALLBACKS
    int handShakeCB(HandShakeInfo*);
    int timeoutCB(TimeoutInfo*);
    Timeval timeout;
#endif

#ifdef HAVE_SESSION_TICKET
    int sessionTicketCB(WOLFSSL*, const unsigned char*, int, void*);
#endif


static void NonBlockingSSL_Connect(WOLFSSL* ssl)
{
#ifndef WOLFSSL_CALLBACKS
    int ret = wolfSSL_connect(ssl);
#else
    int ret = wolfSSL_connect_ex(ssl, handShakeCB, timeoutCB, timeout);
#endif
    int error = wolfSSL_get_error(ssl, 0);
    SOCKET_T sockfd = (SOCKET_T)wolfSSL_get_fd(ssl);
    int select_ret;

    while (ret != SSL_SUCCESS && (error == SSL_ERROR_WANT_READ ||
                                  error == SSL_ERROR_WANT_WRITE)) {
        int currTimeout = 1;

        if (error == SSL_ERROR_WANT_READ)
            printf("... client would read block\n");
        else
            printf("... client would write block\n");

#ifdef WOLFSSL_DTLS
        currTimeout = wolfSSL_dtls_get_current_timeout(ssl);
#endif
        select_ret = tcp_select(sockfd, currTimeout);

        if ((select_ret == TEST_RECV_READY) ||
                                        (select_ret == TEST_ERROR_READY)) {
            #ifndef WOLFSSL_CALLBACKS
                    ret = wolfSSL_connect(ssl);
            #else
                ret = wolfSSL_connect_ex(ssl,handShakeCB,timeoutCB,timeout);
            #endif
            error = wolfSSL_get_error(ssl, 0);
        }
        else if (select_ret == TEST_TIMEOUT && !wolfSSL_dtls(ssl)) {
            error = SSL_ERROR_WANT_READ;
        }
#ifdef WOLFSSL_DTLS
        else if (select_ret == TEST_TIMEOUT && wolfSSL_dtls(ssl) &&
                                            wolfSSL_dtls_got_timeout(ssl) >= 0) {
            error = SSL_ERROR_WANT_READ;
        }
#endif
        else {
            error = SSL_FATAL_ERROR;
        }
    }
    if (ret != SSL_SUCCESS)
        err_sys("SSL_connect failed");
}


static void Usage(void)
{
    printf("client "    LIBWOLFSSL_VERSION_STRING
           " NOTE: All files relative to wolfSSL home dir\n");
    printf("-?          Help, print this usage\n");
    printf("-h <host>   Host to connect to, default %s\n", wolfSSLIP);
    printf("-p <num>    Port to connect on, not 0, default %d\n", wolfSSLPort);
    printf("-v <num>    SSL version [0-3], SSLv3(0) - TLS1.2(3)), default %d\n",
                                 CLIENT_DEFAULT_VERSION);
    printf("-l <str>    Cipher list\n");
    printf("-c <file>   Certificate file,           default %s\n", cliCert);
    printf("-k <file>   Key file,                   default %s\n", cliKey);
    printf("-A <file>   Certificate Authority file, default %s\n", caCert);
#ifndef NO_DH
    printf("-Z <num>    Minimum DH key bits,        default %d\n",
                                 DEFAULT_MIN_DHKEY_BITS);
#endif
    printf("-b <num>    Benchmark <num> connections and print stats\n");
    printf("-s          Use pre Shared keys\n");
    printf("-t          Track wolfSSL memory use\n");
    printf("-d          Disable peer checks\n");
    printf("-D          Override Date Errors example\n");
    printf("-g          Send server HTTP GET\n");
    printf("-u          Use UDP DTLS,"
           " add -v 2 for DTLSv1 (default), -v 3 for DTLSv1.2\n");
    printf("-m          Match domain name in cert\n");
    printf("-N          Use Non-blocking sockets\n");
    printf("-r          Resume session\n");
    printf("-w          Wait for bidirectional shutdown\n");
#ifdef HAVE_SECURE_RENEGOTIATION
    printf("-R          Allow Secure Renegotiation\n");
    printf("-i          Force client Initiated Secure Renegotiation\n");
#endif
    printf("-f          Fewer packets/group messages\n");
    printf("-x          Disable client cert/key loading\n");
    printf("-X          Driven by eXternal test case\n");
#ifdef SHOW_SIZES
    printf("-z          Print structure sizes\n");
#endif
#ifdef HAVE_SNI
    printf("-S <str>    Use Host Name Indication\n");
#endif
#ifdef HAVE_MAX_FRAGMENT
    printf("-L <num>    Use Maximum Fragment Length [1-5]\n");
#endif
#ifdef HAVE_TRUNCATED_HMAC
    printf("-T          Use Truncated HMAC\n");
#endif
#ifdef HAVE_OCSP
    printf("-o          Perform OCSP lookup on peer certificate\n");
    printf("-O <url>    Perform OCSP lookup using <url> as responder\n");
#endif
#ifdef ATOMIC_USER
    printf("-U          Atomic User Record Layer Callbacks\n");
#endif
#ifdef HAVE_PK_CALLBACKS 
    printf("-P          Public Key Callbacks\n");
#endif
#ifdef HAVE_ANON
    printf("-a          Anonymous client\n");
#endif
#ifdef HAVE_CRL
    printf("-C          Disable CRL\n");
#endif
}

THREAD_RETURN WOLFSSL_THREAD client_test(void* args)
{
    SOCKET_T sockfd = 0;

    WOLFSSL_METHOD*  method  = 0;
    WOLFSSL_CTX*     ctx     = 0;
    WOLFSSL*         ssl     = 0;
    
    WOLFSSL*         sslResume = 0;
    WOLFSSL_SESSION* session = 0;
    char         resumeMsg[] = "resuming wolfssl!";
    int          resumeSz    = sizeof(resumeMsg);

    char msg[32] = "hello wolfssl!";   /* GET may make bigger */
    char reply[80];
    int  input;
    int  msgSz = (int)strlen(msg);

    word16 port   = wolfSSLPort;
    char* host   = (char*)wolfSSLIP;
    const char* domain = "www.wolfssl.com";

    int    ch;
    int    version = CLIENT_INVALID_VERSION;
    int    usePsk   = 0;
    int    useAnon  = 0;
    int    sendGET  = 0;
    int    benchmark = 0;
    int    doDTLS    = 0;
    int    matchName = 0;
    int    doPeerCheck = 1;
    int    nonBlocking = 0;
    int    resumeSession = 0;
    int    wc_shutdown   = 0;
    int    disableCRL    = 0;
    int    externalTest  = 0;
    int    ret;
    int    scr           = 0;    /* allow secure renegotiation */
    int    forceScr      = 0;    /* force client initiaed scr */
    int    trackMemory   = 0;
    int    useClientCert = 1;
    int    fewerPackets  = 0;
    int    atomicUser    = 0;
    int    pkCallbacks   = 0;
    int    overrideDateErrors = 0;
    int    minDhKeyBits  = DEFAULT_MIN_DHKEY_BITS;
    char*  cipherList = NULL;
    const char* verifyCert = caCert;
    const char* ourCert    = cliCert;
    const char* ourKey     = cliKey;

#ifdef HAVE_SNI
    char*  sniHostName = NULL;
#endif
#ifdef HAVE_MAX_FRAGMENT
    byte maxFragment = 0;
#endif
#ifdef HAVE_TRUNCATED_HMAC
    byte  truncatedHMAC = 0;
#endif


#ifdef HAVE_OCSP
    int    useOcsp  = 0;
    char*  ocspUrl  = NULL;
#endif

    int     argc = ((func_args*)args)->argc;
    char**  argv = ((func_args*)args)->argv;

    ((func_args*)args)->return_code = -1; /* error state */

#ifdef NO_RSA
    verifyCert = (char*)eccCert;
    ourCert    = (char*)cliEccCert;
    ourKey     = (char*)cliEccKey;
#endif
    (void)resumeSz;
    (void)session;
    (void)sslResume;
    (void)trackMemory;
    (void)atomicUser;
    (void)pkCallbacks;
    (void)scr;
    (void)forceScr;
    (void)ourKey;
    (void)ourCert;
    (void)verifyCert;
    (void)useClientCert;
    (void)overrideDateErrors;
    (void)disableCRL;
    (void)minDhKeyBits;

    StackTrap();

    while ((ch = mygetopt(argc, argv,
                          "?gdDusmNrwRitfxXUPCh:p:v:l:A:c:k:Z:b:zS:L:ToO:a"))
                                                                        != -1) {
        switch (ch) {
            case '?' :
                Usage();
                exit(EXIT_SUCCESS);

            case 'g' :
                sendGET = 1;
                break;

            case 'd' :
                doPeerCheck = 0;
                break;

            case 'D' :
                overrideDateErrors = 1;
                break;

            case 'C' :
                #ifdef HAVE_CRL
                    disableCRL = 1;
                #endif
                break;

            case 'u' :
                doDTLS  = 1;
                break;

            case 's' :
                usePsk = 1;
                break;

            case 't' :
            #ifdef USE_WOLFSSL_MEMORY
                trackMemory = 1;
            #endif
                break;

            case 'm' :
                matchName = 1;
                break;

            case 'x' :
                useClientCert = 0;
                break;

            case 'X' :
                externalTest = 1;
                break;

            case 'f' :
                fewerPackets = 1;
                break;

            case 'U' :
            #ifdef ATOMIC_USER
                atomicUser = 1;
            #endif
                break;

            case 'P' :
            #ifdef HAVE_PK_CALLBACKS 
                pkCallbacks = 1;
            #endif
                break;

            case 'h' :
                host   = myoptarg;
                domain = myoptarg;
                break;

            case 'p' :
                port = (word16)atoi(myoptarg);
                #if !defined(NO_MAIN_DRIVER) || defined(USE_WINDOWS_API)
                    if (port == 0)
                        err_sys("port number cannot be 0");
                #endif
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

            case 'Z' :
                #ifndef NO_DH
                    minDhKeyBits = atoi(myoptarg);
                    if (minDhKeyBits <= 0 || minDhKeyBits > 16000) {
                        Usage();
                        exit(MY_EX_USAGE);
                    }
                #endif
                break;

            case 'b' :
                benchmark = atoi(myoptarg);
                if (benchmark < 0 || benchmark > 1000000) {
                    Usage();
                    exit(MY_EX_USAGE);
                }
                break;

            case 'N' :
                nonBlocking = 1;
                break;

            case 'r' :
                resumeSession = 1;
                break;

            case 'w' :
                wc_shutdown = 1;
                break;

            case 'R' :
                #ifdef HAVE_SECURE_RENEGOTIATION
                    scr = 1;
                #endif
                break;

            case 'i' :
                #ifdef HAVE_SECURE_RENEGOTIATION
                    scr      = 1;
                    forceScr = 1;
                #endif
                break;

            case 'z' :
                #ifndef WOLFSSL_LEANPSK
                    wolfSSL_GetObjectSize();
                #endif
                break;

            case 'S' :
                #ifdef HAVE_SNI
                    sniHostName = myoptarg;
                #endif
                break;

            case 'L' :
                #ifdef HAVE_MAX_FRAGMENT
                    maxFragment = atoi(myoptarg);
                    if (maxFragment < WOLFSSL_MFL_2_9 ||
                                                maxFragment > WOLFSSL_MFL_2_13) {
                        Usage();
                        exit(MY_EX_USAGE);
                    }
                #endif
                break;

            case 'T' :
                #ifdef HAVE_TRUNCATED_HMAC
                    truncatedHMAC = 1;
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

    if (externalTest) {
        /* detect build cases that wouldn't allow test against wolfssl.com */
        int done = 0;
        (void)done;

        #ifdef NO_RSA
            done = 1;
        #endif

        #ifndef NO_PSK
            done = 1;
        #endif

        #ifdef NO_SHA
            done = 1;  /* external cert chain most likely has SHA */
        #endif

        if (done) {
            printf("external test can't be run in this mode");

            ((func_args*)args)->return_code = 0;
            exit(EXIT_SUCCESS);
        }
    }

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

#ifdef USE_WOLFSSL_MEMORY
    if (trackMemory)
        InitMemoryTracker(); 
#endif

    switch (version) {
#ifndef NO_OLD_TLS
        case 0:
            method = wolfSSLv3_client_method();
            break;
                
                
    #ifndef NO_TLS
        case 1:
            method = wolfTLSv1_client_method();
            break;

        case 2:
            method = wolfTLSv1_1_client_method();
            break;
    #endif /* NO_TLS */
                
#endif  /* NO_OLD_TLS */
                
#ifndef NO_TLS
        case 3:
            method = wolfTLSv1_2_client_method();
            break;
#endif

#ifdef WOLFSSL_DTLS
        #ifndef NO_OLD_TLS
        case -1:
            method = wolfDTLSv1_client_method();
            break;
        #endif

        case -2:
            method = wolfDTLSv1_2_client_method();
            break;
#endif

        default:
            err_sys("Bad SSL version");
            break;
    }

    if (method == NULL)
        err_sys("unable to get method");

    ctx = wolfSSL_CTX_new(method);
    if (ctx == NULL)
        err_sys("unable to get ctx");

    if (cipherList)
        if (wolfSSL_CTX_set_cipher_list(ctx, cipherList) != SSL_SUCCESS)
            err_sys("client can't set cipher list 1");

#ifdef WOLFSSL_LEANPSK
    usePsk = 1;
#endif

#if defined(NO_RSA) && !defined(HAVE_ECC)
    usePsk = 1;
#endif

    if (fewerPackets)
        wolfSSL_CTX_set_group_messages(ctx);

#ifndef NO_DH
    wolfSSL_CTX_SetMinDhKey_Sz(ctx, (word16)minDhKeyBits);
#endif

    if (usePsk) {
#ifndef NO_PSK
        wolfSSL_CTX_set_psk_client_callback(ctx, my_psk_client_cb);
        if (cipherList == NULL) {
            const char *defaultCipherList;
            #if defined(HAVE_AESGCM) && !defined(NO_DH)
                defaultCipherList = "DHE-PSK-AES128-GCM-SHA256";
            #elif defined(HAVE_NULL_CIPHER)
                defaultCipherList = "PSK-NULL-SHA256";
            #else
                defaultCipherList = "PSK-AES128-CBC-SHA256";
            #endif
            if (wolfSSL_CTX_set_cipher_list(ctx,defaultCipherList)
                                                                  !=SSL_SUCCESS)
                err_sys("client can't set cipher list 2");
        }
#endif
        useClientCert = 0;
    }

    if (useAnon) {
#ifdef HAVE_ANON
        if (cipherList == NULL) {
            wolfSSL_CTX_allow_anon_cipher(ctx);
            if (wolfSSL_CTX_set_cipher_list(ctx,"ADH-AES128-SHA") != SSL_SUCCESS)
                err_sys("client can't set cipher list 4");
        }
#endif
        useClientCert = 0;
    }

#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
    wolfSSL_CTX_set_default_passwd_cb(ctx, PasswordCallBack);
#endif

#if defined(WOLFSSL_SNIFFER)
    if (cipherList == NULL) {
        /* don't use EDH, can't sniff tmp keys */
        if (wolfSSL_CTX_set_cipher_list(ctx, "AES256-SHA256") != SSL_SUCCESS) {
            err_sys("client can't set cipher list 3");
        }
    }
#endif

#ifdef HAVE_OCSP
    if (useOcsp) {
        if (ocspUrl != NULL) {
            wolfSSL_CTX_SetOCSP_OverrideURL(ctx, ocspUrl);
            wolfSSL_CTX_EnableOCSP(ctx, WOLFSSL_OCSP_NO_NONCE
                                                    | WOLFSSL_OCSP_URL_OVERRIDE);
        }
        else
            wolfSSL_CTX_EnableOCSP(ctx, WOLFSSL_OCSP_NO_NONCE);
    }
#endif

#ifdef USER_CA_CB
    wolfSSL_CTX_SetCACb(ctx, CaCb);
#endif

#ifdef VERIFY_CALLBACK
    wolfSSL_CTX_set_verify(ctx, SSL_VERIFY_PEER, myVerify);
#endif
#if !defined(NO_FILESYSTEM) && !defined(NO_CERTS)
    if (useClientCert){
        if (wolfSSL_CTX_use_certificate_chain_file(ctx, ourCert) != SSL_SUCCESS)
            err_sys("can't load client cert file, check file and run from"
                    " wolfSSL home dir");

        if (wolfSSL_CTX_use_PrivateKey_file(ctx, ourKey, SSL_FILETYPE_PEM)
                                         != SSL_SUCCESS)
            err_sys("can't load client private key file, check file and run "
                    "from wolfSSL home dir");
    }

    if (!usePsk && !useAnon) {
        if (wolfSSL_CTX_load_verify_locations(ctx, verifyCert,0) != SSL_SUCCESS)
            err_sys("can't load ca file, Please run from wolfSSL home dir");
#ifdef HAVE_ECC
        /* load ecc verify too, echoserver uses it by default w/ ecc */
        if (wolfSSL_CTX_load_verify_locations(ctx, eccCert, 0) != SSL_SUCCESS)
            err_sys("can't load ecc ca file, Please run from wolfSSL home dir");
#endif /* HAVE_ECC */
    }
#endif /* !NO_FILESYSTEM && !NO_CERTS */
#if !defined(NO_CERTS)
    if (!usePsk && !useAnon && doPeerCheck == 0)
        wolfSSL_CTX_set_verify(ctx, SSL_VERIFY_NONE, 0);
    if (!usePsk && !useAnon && overrideDateErrors == 1)
        wolfSSL_CTX_set_verify(ctx, SSL_VERIFY_PEER, myDateCb);
#endif

#ifdef HAVE_CAVIUM
    wolfSSL_CTX_UseCavium(ctx, CAVIUM_DEV_ID);
#endif

#ifdef HAVE_SNI
    if (sniHostName)
        if (wolfSSL_CTX_UseSNI(ctx, 0, sniHostName, XSTRLEN(sniHostName))
                                                                 != SSL_SUCCESS)
            err_sys("UseSNI failed");
#endif
#ifdef HAVE_MAX_FRAGMENT
    if (maxFragment)
        if (wolfSSL_CTX_UseMaxFragment(ctx, maxFragment) != SSL_SUCCESS)
            err_sys("UseMaxFragment failed");
#endif
#ifdef HAVE_TRUNCATED_HMAC
    if (truncatedHMAC)
        if (wolfSSL_CTX_UseTruncatedHMAC(ctx) != SSL_SUCCESS)
            err_sys("UseTruncatedHMAC failed");
#endif
#ifdef HAVE_SESSION_TICKET
    if (wolfSSL_CTX_UseSessionTicket(ctx) != SSL_SUCCESS)
        err_sys("UseSessionTicket failed");
#endif

    if (benchmark) {
        /* time passed in number of connects give average */
        int times = benchmark;
        int loops = resumeSession ? 2 : 1;
        int i = 0;
        WOLFSSL_SESSION* benchSession = NULL;

        while (loops--) {
            int benchResume = resumeSession && loops == 0;
            double start = current_time(), avg;

            for (i = 0; i < times; i++) {
                tcp_connect(&sockfd, host, port, doDTLS);

                ssl = wolfSSL_new(ctx);
                if (benchResume)
                    wolfSSL_set_session(ssl, benchSession);
                wolfSSL_set_fd(ssl, sockfd);
                if (wolfSSL_connect(ssl) != SSL_SUCCESS)
                    err_sys("SSL_connect failed");

                wolfSSL_shutdown(ssl);
                if (i == (times-1) && resumeSession) {
                    benchSession = wolfSSL_get_session(ssl);
                }
                wolfSSL_free(ssl);
                CloseSocket(sockfd);
            }
            avg = current_time() - start;
            avg /= times;
            avg *= 1000;   /* milliseconds */
            if (benchResume)
                printf("wolfSSL_resume  avg took: %8.3f milliseconds\n", avg);
            else
                printf("wolfSSL_connect avg took: %8.3f milliseconds\n", avg);
        }

        wolfSSL_CTX_free(ctx);
        ((func_args*)args)->return_code = 0;

        exit(EXIT_SUCCESS);
    }
    
    #if defined(WOLFSSL_MDK_ARM)
    wolfSSL_CTX_set_verify(ctx, SSL_VERIFY_NONE, 0);
    #endif
    
    ssl = wolfSSL_new(ctx);
    if (ssl == NULL)
        err_sys("unable to get SSL object");
    #ifdef HAVE_SESSION_TICKET
    wolfSSL_set_SessionTicket_cb(ssl, sessionTicketCB, (void*)"initial session");
    #endif
    if (doDTLS) {
        SOCKADDR_IN_T addr;
        build_addr(&addr, host, port, 1);
        wolfSSL_dtls_set_peer(ssl, &addr, sizeof(addr));
        tcp_socket(&sockfd, 1);
    }
    else {
        tcp_connect(&sockfd, host, port, 0);
    }

#ifdef HAVE_POLY1305
    /* use old poly to connect with google server */
    if (!XSTRNCMP(domain, "www.google.com", 14)) {
        if (wolfSSL_use_old_poly(ssl, 1) != 0)
            err_sys("unable to set to old poly");
    }
#endif

    wolfSSL_set_fd(ssl, sockfd);
#ifdef HAVE_CRL
    if (disableCRL == 0) {
        if (wolfSSL_EnableCRL(ssl, WOLFSSL_CRL_CHECKALL) != SSL_SUCCESS)
            err_sys("can't enable crl check");
        if (wolfSSL_LoadCRL(ssl, crlPemDir, SSL_FILETYPE_PEM, 0) != SSL_SUCCESS)
            err_sys("can't load crl, check crlfile and date validity");
        if (wolfSSL_SetCRL_Cb(ssl, CRL_CallBack) != SSL_SUCCESS)
            err_sys("can't set crl callback");
    }
#endif
#ifdef HAVE_SECURE_RENEGOTIATION
    if (scr) {
        if (wolfSSL_UseSecureRenegotiation(ssl) != SSL_SUCCESS)
            err_sys("can't enable secure renegotiation");
    }
#endif
#ifdef ATOMIC_USER
    if (atomicUser)
        SetupAtomicUser(ctx, ssl);
#endif
#ifdef HAVE_PK_CALLBACKS
    if (pkCallbacks)
        SetupPkCallbacks(ctx, ssl);
#endif
    if (matchName && doPeerCheck)
        wolfSSL_check_domain_name(ssl, domain);
#ifndef WOLFSSL_CALLBACKS
    if (nonBlocking) {
        wolfSSL_set_using_nonblock(ssl, 1);
        tcp_set_nonblocking(&sockfd);
        NonBlockingSSL_Connect(ssl);
    }
    else if (wolfSSL_connect(ssl) != SSL_SUCCESS) {
        /* see note at top of README */
        int  err = wolfSSL_get_error(ssl, 0);
        char buffer[WOLFSSL_MAX_ERROR_SZ];
        printf("err = %d, %s\n", err,
                                wolfSSL_ERR_error_string(err, buffer));
        err_sys("SSL_connect failed");
        /* if you're getting an error here  */
    }
#else
    timeout.tv_sec  = 2;
    timeout.tv_usec = 0;
    NonBlockingSSL_Connect(ssl);  /* will keep retrying on timeout */
#endif
    showPeer(ssl);

#ifdef HAVE_SECURE_RENEGOTIATION
    if (scr && forceScr) {
        if (nonBlocking) {
            printf("not doing secure renegotiation on example with"
                   " nonblocking yet");
        } else {
            if (wolfSSL_Rehandshake(ssl) != SSL_SUCCESS) {
                int  err = wolfSSL_get_error(ssl, 0);
                char buffer[WOLFSSL_MAX_ERROR_SZ];
                printf("err = %d, %s\n", err,
                                wolfSSL_ERR_error_string(err, buffer));
                err_sys("wolfSSL_Rehandshake failed");
            }
        }
    }
#endif /* HAVE_SECURE_RENEGOTIATION */

    if (sendGET) {
        printf("SSL connect ok, sending GET...\n");
        msgSz = 28;
        strncpy(msg, "GET /index.html HTTP/1.0\r\n\r\n", msgSz);
        msg[msgSz] = '\0';
    }
    if (wolfSSL_write(ssl, msg, msgSz) != msgSz)
        err_sys("SSL_write failed");

    input = wolfSSL_read(ssl, reply, sizeof(reply)-1);
    if (input > 0) {
        reply[input] = 0;
        printf("Server response: %s\n", reply);

        if (sendGET) {  /* get html */
            while (1) {
                input = wolfSSL_read(ssl, reply, sizeof(reply)-1);
                if (input > 0) {
                    reply[input] = 0;
                    printf("%s\n", reply);
                }
                else
                    break;
            }
        }
    }
    else if (input < 0) {
        int readErr = wolfSSL_get_error(ssl, 0);
        if (readErr != SSL_ERROR_WANT_READ)
            err_sys("wolfSSL_read failed");
    }

#ifndef NO_SESSION_CACHE
    if (resumeSession) {
        session   = wolfSSL_get_session(ssl);
        sslResume = wolfSSL_new(ctx);
    }
#endif

    if (doDTLS == 0) {           /* don't send alert after "break" command */
        ret = wolfSSL_shutdown(ssl);
        if (wc_shutdown && ret == SSL_SHUTDOWN_NOT_DONE)
            wolfSSL_shutdown(ssl);    /* bidirectional shutdown */
    }
#ifdef ATOMIC_USER
    if (atomicUser)
        FreeAtomicUser(ssl);
#endif
    wolfSSL_free(ssl);
    CloseSocket(sockfd);

#ifndef NO_SESSION_CACHE
    if (resumeSession) {
        if (doDTLS) {
            SOCKADDR_IN_T addr;
            #ifdef USE_WINDOWS_API 
                Sleep(500);
            #elif defined(WOLFSSL_TIRTOS)
                Task_sleep(1);
            #else
                sleep(1);
            #endif
            build_addr(&addr, host, port, 1);
            wolfSSL_dtls_set_peer(sslResume, &addr, sizeof(addr));
            tcp_socket(&sockfd, 1);
        }
        else {
            tcp_connect(&sockfd, host, port, 0);
        }
        wolfSSL_set_fd(sslResume, sockfd);
#ifdef HAVE_SECURE_RENEGOTIATION
        if (scr) {
            if (wolfSSL_UseSecureRenegotiation(sslResume) != SSL_SUCCESS)
                err_sys("can't enable secure renegotiation");
        }
#endif
        wolfSSL_set_session(sslResume, session);
#ifdef HAVE_SESSION_TICKET
        wolfSSL_set_SessionTicket_cb(sslResume, sessionTicketCB,
                                    (void*)"resumed session");
#endif
       
        showPeer(sslResume);
#ifndef WOLFSSL_CALLBACKS
        if (nonBlocking) {
            wolfSSL_set_using_nonblock(sslResume, 1);
            tcp_set_nonblocking(&sockfd);
            NonBlockingSSL_Connect(sslResume);
        }
        else if (wolfSSL_connect(sslResume) != SSL_SUCCESS)
            err_sys("SSL resume failed");
#else
        timeout.tv_sec  = 2;
        timeout.tv_usec = 0;
        NonBlockingSSL_Connect(ssl);  /* will keep retrying on timeout */
#endif

        if (wolfSSL_session_reused(sslResume))
            printf("reused session id\n");
        else
            printf("didn't reuse session id!!!\n");

        if (wolfSSL_write(sslResume, resumeMsg, resumeSz) != resumeSz)
            err_sys("SSL_write failed");

        if (nonBlocking) {
            /* give server a chance to bounce a message back to client */
            #ifdef USE_WINDOWS_API
                Sleep(500);
            #elif defined(WOLFSSL_TIRTOS)
                Task_sleep(1);
            #else
                sleep(1);
            #endif
        }

        input = wolfSSL_read(sslResume, reply, sizeof(reply)-1);
        if (input > 0) {
            reply[input] = 0;
            printf("Server resume response: %s\n", reply);
        }

        /* try to send session break */
        wolfSSL_write(sslResume, msg, msgSz); 

        ret = wolfSSL_shutdown(sslResume);
        if (wc_shutdown && ret == SSL_SHUTDOWN_NOT_DONE)
            wolfSSL_shutdown(sslResume);    /* bidirectional shutdown */

        wolfSSL_free(sslResume);
        CloseSocket(sockfd);
    }
#endif /* NO_SESSION_CACHE */

    wolfSSL_CTX_free(ctx);

    ((func_args*)args)->return_code = 0;

#ifdef USE_WOLFSSL_MEMORY
    if (trackMemory)
        ShowMemoryTracker();
#endif /* USE_WOLFSSL_MEMORY */

#if !defined(WOLFSSL_TIRTOS)
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

        wolfSSL_Init();
#if defined(DEBUG_WOLFSSL) && !defined(WOLFSSL_MDK_SHELL) && !defined(STACK_TRAP)
        wolfSSL_Debugging_ON();
#endif
        if (CurrentDir("_build"))
            ChangeDirBack(1);
        else if (CurrentDir("client"))
            ChangeDirBack(2);
        else if (CurrentDir("Debug") || CurrentDir("Release"))
            ChangeDirBack(3);
  
#ifdef HAVE_STACK_SIZE
        StackSizeCheck(&args, client_test);
#else 
        client_test(&args);
#endif
        wolfSSL_Cleanup();

#ifdef HAVE_CAVIUM
        CspShutdown(CAVIUM_DEV_ID);
#endif
        return args.return_code;
    }

    int myoptind = 0;
    char* myoptarg = NULL;

#endif /* NO_MAIN_DRIVER */



#ifdef WOLFSSL_CALLBACKS

    int handShakeCB(HandShakeInfo* info)
    {
        (void)info;
        return 0;
    }


    int timeoutCB(TimeoutInfo* info)
    {
        (void)info;
        return 0;
    }

#endif


#ifdef HAVE_SESSION_TICKET

    int sessionTicketCB(WOLFSSL* ssl,
                        const unsigned char* ticket, int ticketSz,
                        void* ctx)
    {
        (void)ssl;
        (void)ticket;
        printf("Session Ticket CB: ticketSz = %d, ctx = %s\n",
               ticketSz, (char*)ctx);
        return 0;
    }

#endif

