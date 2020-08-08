/* suites.c
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

#include <wolfssl/wolfcrypt/settings.h>

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <wolfssl/ssl.h>
#include <tests/unit.h>
#if defined(HAVE_ECC) && defined(FP_ECC) && defined(HAVE_THREAD_LS) \
                      && (defined(NO_MAIN_DRIVER) || defined(HAVE_STACK_SIZE))
#include <wolfssl/wolfcrypt/ecc.h>
#endif


#define MAX_ARGS 40
#define MAX_COMMAND_SZ 240
#ifdef WOLFSSL_TLS13
    #define MAX_SUITE_SZ 200
#else
    #define MAX_SUITE_SZ 80
#endif
#define NOT_BUILT_IN -123
#if defined(NO_OLD_TLS) || !defined(WOLFSSL_ALLOW_SSLV3) || \
    !defined(WOLFSSL_ALLOW_TLSV10)
    #define VERSION_TOO_OLD -124
#endif

#include "examples/client/client.h"
#include "examples/server/server.h"

#if !defined(NO_WOLFSSL_SERVER) && !defined(NO_WOLFSSL_CLIENT)
static WOLFSSL_CTX* cipherSuiteCtx = NULL;
static char nonblockFlag[] = "-N";
static char noVerifyFlag[] = "-d";
static char disableEMSFlag[] = "-n";
static char flagSep[] = " ";
#if !defined(USE_WINDOWS_API) && !defined(WOLFSSL_TIRTOS)
    static char portFlag[] = "-p";
    static char svrPort[] = "0";
#endif
static char intTestFlag[] = "-H";
static char forceDefCipherListFlag[] = "defCipherList";
static char exitWithRetFlag[] = "exitWithRet";
static char disableDHPrimeTest[] = "-2";

#ifdef WOLFSSL_ASYNC_CRYPT
    static int devId = INVALID_DEVID;
#endif


#ifdef VERSION_TOO_OLD
static int GetTlsVersion(const char* line)
{
    int version = -1;
    const char* find = "-v ";
    const char* begin = strstr(line, find);

    if (begin) {
        begin += 3;

        version = atoi(begin);
    }
    return version;
}

#ifndef WOLFSSL_ALLOW_SSLV3
/* if the protocol version is sslv3 return 1, else 0 */
static int IsSslVersion(const char* line)
{
    int version = GetTlsVersion(line);
    return (version == 0) ? 1 : 0;
}
#endif /* !WOLFSSL_ALLOW_SSLV3 */

#ifndef WOLFSSL_ALLOW_TLSV10
/* if the protocol version is TLSv1.0 return 1, else 0 */
static int IsTls10Version(const char* line)
{
    int version = GetTlsVersion(line);
    return (version == 1) ? 1 : 0;
}
#endif /* !WOLFSSL_ALLOW_TLSV10 */

#ifdef NO_OLD_TLS
/* if the protocol version is less than tls 1.2 return 1, else 0 */
static int IsOldTlsVersion(const char* line)
{
    int version = GetTlsVersion(line);
    return (version < 3) ? 1 : 0;
}
#endif /* NO_OLD_TLS */
#endif /* VERSION_TOO_OLD */


/* if the cipher suite on line is valid store in suite and return 1, else 0 */
static int IsValidCipherSuite(const char* line, char* suite)
{
    int  found = 0;
    int  valid = 0;

    const char* find = "-l ";
    const char* begin = strstr(line, find);
    const char* end;

    suite[0] = '\0';

    if (begin) {
        begin += 3;

        end = XSTRSTR(begin, " ");

        if (end) {
            long len = end - begin;
            if (len > MAX_SUITE_SZ) {
                printf("suite too long!\n");
                return 0;
            }
            XMEMCPY(suite, begin, len);
            suite[len] = '\0';
        }
        else
            XSTRNCPY(suite, begin, MAX_SUITE_SZ);

        suite[MAX_SUITE_SZ] = '\0';
        found = 1;
    }

    /* if QSH not enabled then do not use QSH suite */
    #ifdef HAVE_QSH
        if (XSTRNCMP(suite, "QSH", 3) == 0) {
            if (wolfSSL_CTX_set_cipher_list(cipherSuiteCtx, suite + 4)
                                                                 != WOLFSSL_SUCCESS)
            return 0;
        }
    #endif

    if (found) {
        if (wolfSSL_CTX_set_cipher_list(cipherSuiteCtx, suite) == WOLFSSL_SUCCESS)
            valid = 1;
    }

    return valid;
}

static int IsValidCert(const char* line)
{
    int ret = 1;
#if !defined(NO_FILESYSTEM) && !defined(NO_CERTS)
    WOLFSSL_CTX* ctx;
    size_t i;
    const char* begin;
    char cert[80];
#ifdef WOLFSSL_STATIC_MEMORY
    FILE* fStream = NULL;
    long chkSz = 0;
#endif

    begin = XSTRSTR(line, "-c ");
    if (begin == NULL)
        return 1;

    begin += 3;
    for (i = 0; i < sizeof(cert) - 1 && *begin != ' ' && *begin != '\0'; i++)
        cert[i] = *(begin++);
    cert[i] = '\0';
#ifdef WOLFSSL_STATIC_MEMORY
    fStream = XFOPEN(cert, "rb");
    if (fStream == NULL) {
        printf("Failed to open file %s\n", cert);
        printf("Invalid cert, skipping test\n");
        return 0;
    } else {
        printf("Successfully opened file\n");
    }

    XFSEEK(fStream, 0L, SEEK_END);
    chkSz = XFTELL(fStream);
    XFCLOSE(fStream);
    if (chkSz > LARGEST_MEM_BUCKET) {
        printf("File is larger than largest bucket, skipping this test\n");
        return 0;
    }
#endif

    ctx = wolfSSL_CTX_new(wolfSSLv23_server_method_ex(NULL));
    if (ctx == NULL)
        return 0;
    ret = wolfSSL_CTX_use_certificate_chain_file(ctx, cert) == WOLFSSL_SUCCESS;
    wolfSSL_CTX_free(ctx);
#endif /* !NO_FILESYSTEM && !NO_CERTS */

    (void)line;

    return ret;
}

static int IsValidCA(const char* line)
{
    int ret = 1;
#if !defined(NO_FILESYSTEM) && !defined(NO_CERTS)
    WOLFSSL_CTX* ctx;
    size_t i;
    const char* begin;
    char cert[80];

    begin = XSTRSTR(line, "-A ");
    if (begin == NULL)
        return 1;

    begin += 3;
    for (i = 0; i < sizeof(cert) - 1 && *begin != ' ' && *begin != '\0'; i++)
        cert[i] = *(begin++);
    cert[i] = '\0';

    ctx = wolfSSL_CTX_new(wolfSSLv23_server_method_ex(NULL));
    if (ctx == NULL)
        return 0;
    ret = wolfSSL_CTX_use_certificate_chain_file(ctx, cert) == WOLFSSL_SUCCESS;
    wolfSSL_CTX_free(ctx);
#endif /* !NO_FILESYSTEM && !NO_CERTS */

    (void)line;

    return ret;
}

static int execute_test_case(int svr_argc, char** svr_argv,
                             int cli_argc, char** cli_argv,
                             int addNoVerify, int addNonBlocking,
                             int addDisableEMS, int forceSrvDefCipherList,
                             int forceCliDefCipherList)
{
#ifdef WOLFSSL_TIRTOS
    func_args cliArgs = {0};
    func_args svrArgs = {0};
    cliArgs.argc = cli_argc;
    cliArgs.argv = cli_argv;
    svrArgs.argc = svr_argc;
    svrArgs.argv = svr_argv;
#else
    func_args cliArgs = {cli_argc, cli_argv, 0, NULL, NULL};
    func_args svrArgs = {svr_argc, svr_argv, 0, NULL, NULL};
#endif

    tcp_ready   ready;
    THREAD_TYPE serverThread;
    char        commandLine[MAX_COMMAND_SZ];
    char        cipherSuite[MAX_SUITE_SZ+1];
    int         i;
    size_t      added;
    static      int tests = 1;
#if !defined(USE_WINDOWS_API) && !defined(WOLFSSL_TIRTOS)
    char        portNumber[8];
#endif
    int         cliTestShouldFail = 0, svrTestShouldFail = 0;

    /* Is Valid Cipher and Version Checks */
    /* build command list for the Is checks below */
    commandLine[0] = '\0';
    added = 0;
    for (i = 0; i < svrArgs.argc; i++) {
        added += XSTRLEN(svr_argv[i]) + 2;
        if (added >= MAX_COMMAND_SZ) {
            printf("server command line too long\n");
            break;
        }
        strcat(commandLine, svr_argv[i]);
        strcat(commandLine, flagSep);
    }
    if (IsValidCipherSuite(commandLine, cipherSuite) == 0) {
        #ifdef DEBUG_SUITE_TESTS
            printf("cipher suite %s not supported in build\n", cipherSuite);
        #endif
        return NOT_BUILT_IN;
    }
    if (!IsValidCert(commandLine)) {
        #ifdef DEBUG_SUITE_TESTS
            printf("certificate %s not supported in build\n", commandLine);
        #endif
        return NOT_BUILT_IN;
    }

#ifndef WOLFSSL_ALLOW_SSLV3
    if (IsSslVersion(commandLine) == 1) {
        #ifdef DEBUG_SUITE_TESTS
            printf("protocol version on line %s is too old\n", commandLine);
        #endif
        return VERSION_TOO_OLD;
    }
#endif
#ifndef WOLFSSL_ALLOW_TLSV10
    if (IsTls10Version(commandLine) == 1) {
        #ifdef DEBUG_SUITE_TESTS
            printf("protocol version on line %s is too old\n", commandLine);
        #endif
        return VERSION_TOO_OLD;
    }
#endif
#ifdef NO_OLD_TLS
    if (IsOldTlsVersion(commandLine) == 1) {
        #ifdef DEBUG_SUITE_TESTS
            printf("protocol version on line %s is too old\n", commandLine);
        #endif
        return VERSION_TOO_OLD;
    }
#endif

    /* Build Server Command */
    if (addNoVerify) {
        printf("repeating test with client cert request off\n");
        if (svrArgs.argc >= MAX_ARGS)
            printf("server command line too long\n");
        else
            svr_argv[svrArgs.argc++] = noVerifyFlag;
    }
    if (addNonBlocking) {
        printf("repeating test with non blocking on\n");
        if (svrArgs.argc >= MAX_ARGS)
            printf("server command line too long\n");
        else
            svr_argv[svrArgs.argc++] = nonblockFlag;
    }
    #if !defined(USE_WINDOWS_API) && !defined(WOLFSSL_TIRTOS)
        /* add port */
        if (svrArgs.argc + 2 > MAX_ARGS)
            printf("cannot add the magic port number flag to server\n");
        else {
            svr_argv[svrArgs.argc++] = portFlag;
            svr_argv[svrArgs.argc++] = svrPort;
        }
    #endif
    if (forceSrvDefCipherList) {
        if (svrArgs.argc + 2 > MAX_ARGS)
            printf("cannot add the force def cipher list flag to server\n");
        else {
            svr_argv[svrArgs.argc++] = intTestFlag;
            svr_argv[svrArgs.argc++] = forceDefCipherListFlag;
        }
    }
#ifdef TEST_PK_PRIVKEY
    svr_argv[svrArgs.argc++] = (char*)"-P";
#endif


    /* update server flags list */
    commandLine[0] = '\0';
    added = 0;
    for (i = 0; i < svrArgs.argc; i++) {
        added += XSTRLEN(svr_argv[i]) + 2;
        if (added >= MAX_COMMAND_SZ) {
            printf("server command line too long\n");
            break;
        }
        strcat(commandLine, svr_argv[i]);
        strcat(commandLine, flagSep);
    }
    printf("trying server command line[%d]: %s\n", tests, commandLine);

    tests++; /* test count */

    /* determine based on args if this test is expected to fail */
    if (XSTRSTR(commandLine, exitWithRetFlag) != NULL) {
        svrTestShouldFail = 1;
    }

    InitTcpReady(&ready);

#ifdef WOLFSSL_TIRTOS
    fdOpenSession(Task_self());
#endif

    /* start server */
    svrArgs.signal = &ready;
    start_thread(server_test, &svrArgs, &serverThread);
    wait_tcp_ready(&svrArgs);


    /* Build Client Command */
    if (addNonBlocking) {
        if (cliArgs.argc >= MAX_ARGS)
            printf("cannot add the non block flag to client\n");
        else
            cli_argv[cliArgs.argc++] = nonblockFlag;
    }
    if (addDisableEMS) {
        printf("repeating test without extended master secret\n");
        if (cliArgs.argc >= MAX_ARGS)
            printf("cannot add the disable EMS flag to client\n");
        else
            cli_argv[cliArgs.argc++] = disableEMSFlag;
    }
#if !defined(USE_WINDOWS_API) && !defined(WOLFSSL_TIRTOS)
    if (ready.port != 0) {
        if (cliArgs.argc + 2 > MAX_ARGS)
            printf("cannot add the magic port number flag to client\n");
        else {
            snprintf(portNumber, sizeof(portNumber), "%d", ready.port);
            cli_argv[cliArgs.argc++] = portFlag;
            cli_argv[cliArgs.argc++] = portNumber;
        }
    }
#endif
    if (forceCliDefCipherList) {
        if (cliArgs.argc + 2 > MAX_ARGS)
            printf("cannot add the force def cipher list flag to client\n");
        else {
            cli_argv[cliArgs.argc++] = intTestFlag;
            cli_argv[cliArgs.argc++] = forceDefCipherListFlag;
        }
    }
#ifdef TEST_PK_PRIVKEY
    cli_argv[cliArgs.argc++] = (char*)"-P";
#endif

    commandLine[0] = '\0';
    added = 0;
    for (i = 0; i < cliArgs.argc; i++) {
        added += XSTRLEN(cli_argv[i]) + 2;
        if (added >= MAX_COMMAND_SZ) {
            printf("client command line too long\n");
            break;
        }
        strcat(commandLine, cli_argv[i]);
        strcat(commandLine, flagSep);
    }
    if (!IsValidCA(commandLine)) {
        #ifdef DEBUG_SUITE_TESTS
            printf("certificate %s not supported in build\n", commandLine);
        #endif
        return NOT_BUILT_IN;
    }
    printf("trying client command line[%d]: %s\n", tests, commandLine);

    /* determine based on args if this test is expected to fail */
    if (XSTRSTR(commandLine, exitWithRetFlag) != NULL) {
        cliTestShouldFail = 1;
    }

    /* start client */
    client_test(&cliArgs);

    /* verify results */
    if ((cliArgs.return_code != 0 && cliTestShouldFail == 0) ||
        (cliArgs.return_code == 0 && cliTestShouldFail != 0)) {
        printf("client_test failed\n");
        XEXIT(EXIT_FAILURE);
    }

    join_thread(serverThread);
    if ((svrArgs.return_code != 0 && svrTestShouldFail == 0) ||
        (svrArgs.return_code == 0 && svrTestShouldFail != 0)) {
        printf("server_test failed\n");
        XEXIT(EXIT_FAILURE);
    }

#ifdef WOLFSSL_TIRTOS
    fdCloseSession(Task_self());
#endif
    FreeTcpReady(&ready);

    /* only run the first test for expected failure cases */
    /* the example server/client are not designed to handle expected failure in
        all cases, such as non-blocking, etc... */
    if (svrTestShouldFail || cliTestShouldFail) {
        return NOT_BUILT_IN;
    }

    return 0;
}

static void test_harness(void* vargs)
{
    func_args* args = (func_args*)vargs;
    char* script;
    long  sz, len;
    int   cliMode = 0;   /* server or client command flag, server first */
    int   ret;
    FILE* file;
    char* svrArgs[MAX_ARGS];
    int   svrArgsSz;
    char* cliArgs[MAX_ARGS];
    int   cliArgsSz;
    char* cursor;
    char* comment;
    const char* fname = "tests/test.conf";
    const char* addArgs = NULL;

    if (args->argc == 1) {
        printf("notice: using default file %s\n", fname);
    }
    else if (args->argc == 3) {
        addArgs = args->argv[2];
    }
    else if (args->argc > 3) {
        printf("usage: harness [FILE] [ARG]\n");
        args->return_code = 1;
        return;
    }

    if (args->argc >= 2) {
        fname = args->argv[1];
    }

    file = fopen(fname, "rb");
    if (file == NULL) {
        fprintf(stderr, "unable to open %s\n", fname);
        args->return_code = 1;
        return;
    }
    fseek(file, 0, SEEK_END);
    sz = ftell(file);
    rewind(file);
    if (sz <= 0) {
        fprintf(stderr, "%s is empty\n", fname);
        fclose(file);
        args->return_code = 1;
        return;
    }

    script = (char*)malloc(sz+1);
    if (script == 0) {
        fprintf(stderr, "unable to allocate script buffer\n");
        fclose(file);
        args->return_code = 1;
        return;
    }

    len = fread(script, 1, sz, file);
    if (len != sz) {
        fprintf(stderr, "read error\n");
        fclose(file);
        free(script);
        args->return_code = 1;
        return;
    }

    fclose(file);
    script[sz] = 0;

    cursor = script;
    svrArgsSz = 1;
    svrArgs[0] = args->argv[0];
    cliArgsSz = 1;
    cliArgs[0] = args->argv[0];

    while (*cursor != 0) {
        int do_it = 0;

        switch (*cursor) {
            case '\n':
                /* A blank line triggers test case execution or switches
                   to client mode if we don't have the client command yet */
                if (cliMode == 0)
                    cliMode = 1;  /* switch to client mode processing */
                /* skip extra newlines */
                else
                    do_it = 1;    /* Do It, we have server and client */
                cursor++;
                break;
            case '#':
                /* Ignore lines that start with a # */
                comment = XSTRSEP(&cursor, "\n");
            #ifdef DEBUG_SUITE_TESTS
                printf("%s\n", comment);
            #else
                (void)comment;
            #endif
                break;
            case '-':
            default:
                /* Parameters start with a -. They end in either a newline
                 * or a space. Capture until either, save in Args list. */
                if (cliMode)
                    cliArgs[cliArgsSz++] = XSTRSEP(&cursor, " \n");
                else
                    svrArgs[svrArgsSz++] = XSTRSEP(&cursor, " \n");
                if (*cursor == '\0') /* eof */
                    do_it = 1;
                break;
        }

        if (svrArgsSz == MAX_ARGS || cliArgsSz == MAX_ARGS) {
            fprintf(stderr, "too many arguments, forcing test run\n");
            do_it = 1;
        }

        if (do_it) {
            /* additional arguments processing */
            if (cliArgsSz+2 < MAX_ARGS && svrArgsSz+2 < MAX_ARGS) {
                if (addArgs == NULL || XSTRSTR(addArgs, "doDH") == NULL) {
                    /* The `-2` disable DH prime check is added to all tests by default */
                    cliArgs[cliArgsSz++] = disableDHPrimeTest;
                    svrArgs[svrArgsSz++] = disableDHPrimeTest;
                }
                if (addArgs && XSTRSTR(addArgs, "expFail")) {
                    /* Tests should expect to fail */
                    cliArgs[cliArgsSz++] = intTestFlag;
                    cliArgs[cliArgsSz++] = exitWithRetFlag;
                    svrArgs[svrArgsSz++] = intTestFlag;
                    svrArgs[svrArgsSz++] = exitWithRetFlag;
                }
            }

            ret = execute_test_case(svrArgsSz, svrArgs,
                                    cliArgsSz, cliArgs, 0, 0, 0, 0, 0);
            /* don't repeat if not supported in build */
            if (ret == 0) {
                /* test with default cipher list on server side */
                execute_test_case(svrArgsSz, svrArgs,
                                  cliArgsSz, cliArgs, 0, 0, 0, 1, 0);
                /* test with default cipher list on client side */
                execute_test_case(svrArgsSz, svrArgs,
                                  cliArgsSz, cliArgs, 0, 0, 0, 0, 1);

                execute_test_case(svrArgsSz, svrArgs,
                                  cliArgsSz, cliArgs, 0, 1, 0, 0, 0);
                execute_test_case(svrArgsSz, svrArgs,
                                  cliArgsSz, cliArgs, 1, 0, 0, 0, 0);
                execute_test_case(svrArgsSz, svrArgs,
                                  cliArgsSz, cliArgs, 1, 1, 0, 0, 0);
#ifdef HAVE_EXTENDED_MASTER
                execute_test_case(svrArgsSz, svrArgs,
                                  cliArgsSz, cliArgs, 0, 0, 1, 0, 0);
                execute_test_case(svrArgsSz, svrArgs,
                                  cliArgsSz, cliArgs, 0, 1, 1, 0, 0);
                execute_test_case(svrArgsSz, svrArgs,
                                  cliArgsSz, cliArgs, 1, 0, 1, 0, 0);
                execute_test_case(svrArgsSz, svrArgs,
                                  cliArgsSz, cliArgs, 1, 1, 1, 0, 0);
#endif
            }
            svrArgsSz = 1;
            cliArgsSz = 1;
            cliMode   = 0;
        }
    }

    free(script);
    args->return_code = 0;
}
#endif /* !NO_WOLFSSL_SERVER && !NO_WOLFSSL_CLIENT */


int SuiteTest(int argc, char** argv)
{
#if !defined(NO_WOLFSSL_SERVER) && !defined(NO_WOLFSSL_CLIENT)
    func_args args;
    char argv0[3][80];
    char* myArgv[3];

    printf(" Begin Cipher Suite Tests\n");

    /* setup */
    myArgv[0] = argv0[0];
    myArgv[1] = argv0[1];
    myArgv[2] = argv0[2];
    args.argv = myArgv;
    strcpy(argv0[0], "SuiteTest");

#ifdef WOLFSSL_STATIC_MEMORY
    byte memory[200000];
#endif

    cipherSuiteCtx = wolfSSL_CTX_new(wolfSSLv23_client_method());
    if (cipherSuiteCtx == NULL) {
        printf("can't get cipher suite ctx\n");
        args.return_code = EXIT_FAILURE;
        goto exit;
    }

    /* load in static memory buffer if enabled */
#ifdef WOLFSSL_STATIC_MEMORY
    if (wolfSSL_CTX_load_static_memory(&cipherSuiteCtx, NULL,
                                                   memory, sizeof(memory), 0, 1)
            != WOLFSSL_SUCCESS) {
        printf("unable to load static memory and create ctx");
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
#endif

#ifdef WOLFSSL_ASYNC_CRYPT
    if (wolfAsync_DevOpen(&devId) < 0) {
        printf("Async device open failed");
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
    wolfSSL_CTX_UseAsync(cipherSuiteCtx, devId);
#endif /* WOLFSSL_ASYNC_CRYPT */

    /* support for custom command line tests */
    if (argc > 1) {
        /* Examples:
            ./tests/unit.test tests/test-altchains.conf
            ./tests/unit.test tests/test-fails.conf expFail
            ./tests/unit.test tests/test-dhprime.conf doDH
        */
        args.argc = argc;
        args.argv = argv;
        test_harness(&args);
        if (args.return_code != 0) {
            printf("error from script %d\n", args.return_code);
            args.return_code = EXIT_FAILURE;
        }
        goto exit;
    }

    /* default case */
    args.argc = 1;
    printf("starting default cipher suite tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }

    /* any extra cases will need another argument */
    args.argc = 2;

#ifdef WOLFSSL_OLDTLS_SHA2_CIPHERSUITES
    /* SHA-2 cipher suites in old TLS versions */
    strcpy(argv0[1], "tests/test-sha2.conf");
    printf("starting SHA-2 cipher suite in old TLS versions tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
#endif

#ifdef WOLFSSL_TLS13
    /* add TLSv13 extra suites */
    strcpy(argv0[1], "tests/test-tls13.conf");
    printf("starting TLSv13 extra cipher suite tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
    #ifdef HAVE_ECC
    /* add TLSv13 ECC extra suites */
    strcpy(argv0[1], "tests/test-tls13-ecc.conf");
    printf("starting TLSv13 ECC extra cipher suite tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
    #endif
    #ifndef WOLFSSL_NO_TLS12
    /* add TLSv13 downgrade tets */
    strcpy(argv0[1], "tests/test-tls13-down.conf");
    printf("starting TLSv13 Downgrade extra tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
    #endif
#endif
#if defined(HAVE_CURVE25519) && defined(HAVE_ED25519)
    /* add ED25519 certificate cipher suite tests */
    strcpy(argv0[1], "tests/test-ed25519.conf");
    printf("starting ED25519 extra cipher suite tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
#endif
#if defined(HAVE_CURVE448) && defined(HAVE_ED448)
    /* add ED448 certificate cipher suite tests */
    strcpy(argv0[1], "tests/test-ed448.conf");
    printf("starting ED448 extra cipher suite tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
#endif
#ifdef WOLFSSL_DTLS
    /* add dtls extra suites */
    strcpy(argv0[1], "tests/test-dtls.conf");
    printf("starting dtls extra cipher suite tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
#ifdef WOLFSSL_OLDTLS_SHA2_CIPHERSUITES
    /* add dtls extra suites */
    strcpy(argv0[1], "tests/test-dtls-sha2.conf");
    printf("starting dtls extra cipher suite tests - old TLS sha-2 cs\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
#endif
#endif
#ifdef WOLFSSL_SCTP
    /* add dtls-sctp extra suites */
    strcpy(argv0[1], "tests/test-sctp.conf");
    printf("starting dtls-sctp extra cipher suite tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
#ifdef WOLFSSL_OLDTLS_SHA2_CIPHERSUITES
    /* add dtls-sctp extra suites */
    strcpy(argv0[1], "tests/test-sctp-sha2.conf");
    printf("starting dtls-sctp extra cipher suite tests - old TLS sha-2 cs\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
#endif
#endif
#ifndef WC_STRICT_SIG
#if !defined(NO_RSA) && defined(HAVE_ECC) /* testing mixed ECC/RSA cert */
    /* add extra signature test suites */
    strcpy(argv0[1], "tests/test-sig.conf");
    printf("starting sig extra cipher suite tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
#endif /* HAVE_RSA and HAVE_ECC */
#endif /* !WC_STRICT_SIG */
#ifdef HAVE_QSH
    /* add QSH extra suites */
    strcpy(argv0[1], "tests/test-qsh.conf");
    printf("starting qsh extra cipher suite tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
#ifdef WOLFSSL_OLDTLS_SHA2_CIPHERSUITES
    strcpy(argv0[1], "tests/test-qsh-sha2.conf");
    printf("starting qsh extra cipher suite tests - old TLS sha-2 cs\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
#endif
#endif
#ifndef NO_PSK
    #ifndef WOLFSSL_NO_TLS12
        #if !defined(NO_RSA) || defined(HAVE_ECC)
        /* add psk cipher suites */
        strcpy(argv0[1], "tests/test-psk.conf");
        printf("starting psk cipher suite tests\n");
        test_harness(&args);
        if (args.return_code != 0) {
            printf("error from script %d\n", args.return_code);
            args.return_code = EXIT_FAILURE;
            goto exit;
        }
        #endif
    #endif
    #ifdef WOLFSSL_TLS13
    /* add psk extra suites */
    strcpy(argv0[1], "tests/test-tls13-psk.conf");
    printf("starting TLS 1.3 psk no identity extra cipher suite tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
    #endif
#endif
#if defined(WOLFSSL_ENCRYPTED_KEYS) && !defined(NO_DES3) && !defined(NO_MD5) &&\
    !defined(NO_SHA)
    /* test encrypted keys */
    strcpy(argv0[1], "tests/test-enckeys.conf");
    printf("starting encrypted keys extra cipher suite tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
#endif

#ifdef HAVE_MAX_FRAGMENT
    /* Max fragment cipher suite tests */
    strcpy(argv0[1], "tests/test-maxfrag.conf");
    printf("starting max fragment cipher suite tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }

    #ifdef WOLFSSL_DTLS
    strcpy(argv0[1], "tests/test-maxfrag-dtls.conf");
    printf("starting dtls max fragment cipher suite tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
    #endif
#endif

#ifdef WOLFSSL_ALT_CERT_CHAINS
    /* tests for alt chains */
    strcpy(argv0[1], "tests/test-altchains.conf");
    printf("starting certificate alternate chain cipher suite tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
#else
    /* tests for chains */
    strcpy(argv0[1], "tests/test-chains.conf");
    printf("starting certificate chain cipher suite tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
#endif

#ifdef WOLFSSL_TRUST_PEER_CERT
    /* tests for trusted peer cert */
    strcpy(argv0[1], "tests/test-trustpeer.conf");
    printf("starting trusted peer certificate cipher suite tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }
#endif

    /* tests for dh prime */
    args.argc = 3;
    strcpy(argv0[1], "tests/test-dhprime.conf");
    strcpy(argv0[2], "doDH"); /* add DH prime flag */
    printf("starting tests that expect failure\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }

    /* failure tests */
    args.argc = 3;
    strcpy(argv0[1], "tests/test-fails.conf");
    strcpy(argv0[2], "expFail"); /* tests are expected to fail */
    printf("starting tests that expect failure\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        args.return_code = EXIT_FAILURE;
        goto exit;
    }

exit:
    printf(" End Cipher Suite Tests\n");

    wolfSSL_CTX_free(cipherSuiteCtx);
    wolfSSL_Cleanup();

#if defined(HAVE_ECC) && defined(FP_ECC) && defined(HAVE_THREAD_LS) \
                      && (defined(NO_MAIN_DRIVER) || defined(HAVE_STACK_SIZE))
    wc_ecc_fp_free();  /* free per thread cache */
#endif
#ifdef WOLFSSL_ASYNC_CRYPT
    wolfAsync_DevClose(&devId);
#endif

    return args.return_code;
#else
    return NOT_COMPILED_IN;
#endif /* !NO_WOLFSSL_SERVER && !NO_WOLFSSL_CLIENT */
    (void)argc;
    (void)argv;
}
