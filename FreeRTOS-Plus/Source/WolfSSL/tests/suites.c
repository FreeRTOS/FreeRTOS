/* suites.c
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

#include <wolfssl/wolfcrypt/settings.h>

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <wolfssl/ssl.h>
#include <tests/unit.h>


#define MAX_ARGS 40
#define MAX_COMMAND_SZ 240
#define MAX_SUITE_SZ 80 
#define NOT_BUILT_IN -123
#ifdef NO_OLD_TLS
    #define VERSION_TOO_OLD -124
#endif

#include "examples/client/client.h"
#include "examples/server/server.h"


static WOLFSSL_CTX* cipherSuiteCtx = NULL;
static char nonblockFlag[] = "-N";
static char noVerifyFlag[] = "-d";
static char portFlag[] = "-p";
static char flagSep[] = " ";
static char svrPort[] = "0";


#ifdef NO_OLD_TLS
/* if the protocol version is less than tls 1.2 return 1, else 0 */
static int IsOldTlsVersion(const char* line)
{
    const char* find = "-v ";
    char* begin = strstr(line, find);

    if (begin) {
        int version = -1;

        begin += 3;

        version = atoi(begin);

        if (version < 3)
            return 1;
    }

    return 0;
} 
#endif /* NO_OLD_TLS */


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

        end = strstr(begin, " ");

        if (end) {
            long len = end - begin;
            if (len > MAX_SUITE_SZ) {
                printf("suite too long!\n");
                return 0;
            }
            memcpy(suite, begin, len);
            suite[len] = '\0';
        }
        else
            strncpy(suite, begin, MAX_SUITE_SZ);

        suite[MAX_SUITE_SZ] = '\0';
        found = 1;
    }

    if (found) {
        if (wolfSSL_CTX_set_cipher_list(cipherSuiteCtx, suite) == SSL_SUCCESS)
            valid = 1;
    }

    return valid;
}


static int execute_test_case(int svr_argc, char** svr_argv,
                              int cli_argc, char** cli_argv,
                              int addNoVerify, int addNonBlocking)
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
    size_t      added = 0;
    static      int tests = 1;

    commandLine[0] = '\0';
    for (i = 0; i < svr_argc; i++) {
        added += strlen(svr_argv[i]) + 2;
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

#ifdef NO_OLD_TLS
    if (IsOldTlsVersion(commandLine) == 1) {
        #ifdef DEBUG_SUITE_TESTS
            printf("protocol version on line %s is too old\n", commandLine);
        #endif
        return VERSION_TOO_OLD;
    }
#endif

    if (addNoVerify) {
        printf("repeating test with client cert request off\n"); 
        added += 4;   /* -d plus space plus terminator */
        if (added >= MAX_COMMAND_SZ || svr_argc >= MAX_ARGS)
            printf("server command line too long\n");
        else {
            svr_argv[svr_argc++] = noVerifyFlag;
            svrArgs.argc = svr_argc;
            strcat(commandLine, noVerifyFlag);
            strcat(commandLine, flagSep);
        }
    }
    if (addNonBlocking) {
        printf("repeating test with non blocking on\n"); 
        added += 4;   /* -N plus terminator */
        if (added >= MAX_COMMAND_SZ || svr_argc >= MAX_ARGS)
            printf("server command line too long\n");
        else {
            svr_argv[svr_argc++] = nonblockFlag;
            svrArgs.argc = svr_argc;
            strcat(commandLine, nonblockFlag);
            strcat(commandLine, flagSep);
        }
    }
    #if !defined(USE_WINDOWS_API) && !defined(WOLFSSL_TIRTOS)
        /* add port 0 */
        if (svr_argc + 2 > MAX_ARGS)
            printf("cannot add the magic port number flag to server\n");
        else
        {
            svr_argv[svr_argc++] = portFlag;
            svr_argv[svr_argc++] = svrPort;
            svrArgs.argc = svr_argc;
        }
    #endif
    printf("trying server command line[%d]: %s\n", tests, commandLine);

    commandLine[0] = '\0';
    added = 0;
    for (i = 0; i < cli_argc; i++) {
        added += strlen(cli_argv[i]) + 2;
        if (added >= MAX_COMMAND_SZ) {
            printf("client command line too long\n"); 
            break;
        }
        strcat(commandLine, cli_argv[i]);
        strcat(commandLine, flagSep);
    }
    if (addNonBlocking) {
        added += 4;   /* -N plus space plus terminator  */
        if (added >= MAX_COMMAND_SZ)
            printf("client command line too long\n");
        else  {
            cli_argv[cli_argc++] = nonblockFlag;
            strcat(commandLine, nonblockFlag);
            strcat(commandLine, flagSep);
            cliArgs.argc = cli_argc;
        }
    }
    printf("trying client command line[%d]: %s\n", tests++, commandLine);

    InitTcpReady(&ready);

#ifdef WOLFSSL_TIRTOS
    fdOpenSession(Task_self());
#endif

    /* start server */
    svrArgs.signal = &ready;
    start_thread(server_test, &svrArgs, &serverThread);
    wait_tcp_ready(&svrArgs);
    #if !defined(USE_WINDOWS_API) && !defined(WOLFSSL_TIRTOS)
        if (ready.port != 0)
        {
            if (cli_argc + 2 > MAX_ARGS)
                printf("cannot add the magic port number flag to client\n");
            else {
                char portNumber[8];
                snprintf(portNumber, sizeof(portNumber), "%d", ready.port);
                cli_argv[cli_argc++] = portFlag;
                cli_argv[cli_argc++] = portNumber;
                cliArgs.argc = cli_argc;
            }
        }
    #endif
    /* start client */
    client_test(&cliArgs);

    /* verify results */ 
    if (cliArgs.return_code != 0) {
        printf("client_test failed\n");
        exit(EXIT_FAILURE);
    }

    join_thread(serverThread);
    if (svrArgs.return_code != 0) { 
        printf("server_test failed\n");
        exit(EXIT_FAILURE);
    }

#ifdef WOLFSSL_TIRTOS
    fdCloseSession(Task_self());
#endif
    FreeTcpReady(&ready);
    
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

    if (args->argc == 1) {
        printf("notice: using default file %s\n", fname);
    }
    else if(args->argc != 2) {
        printf("usage: harness [FILE]\n");
        args->return_code = 1;
        return;
    }
    else {
        fname = args->argv[1];
    }

    file = fopen(fname, "r");
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
        fprintf(stderr, "unable to allocte script buffer\n");
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
                else
                    do_it = 1;    /* Do It, we have server and client */
                cursor++;
                break;
            case '#':
                /* Ignore lines that start with a #. */
                comment = strsep(&cursor, "\n");
#ifdef DEBUG_SUITE_TESTS
                printf("%s\n", comment);
#else
                (void)comment;
#endif
                break;
            case '-':
                /* Parameters start with a -. They end in either a newline
                 * or a space. Capture until either, save in Args list. */
                if (cliMode)
                    cliArgs[cliArgsSz++] = strsep(&cursor, " \n");
                else
                    svrArgs[svrArgsSz++] = strsep(&cursor, " \n");
                break;
            default:
                /* Anything from cursor until end of line that isn't the above
                 * is data for a paramter. Just up until the next newline in
                 * the Args list. */
                if (cliMode)
                    cliArgs[cliArgsSz++] = strsep(&cursor, "\n");
                else
                    svrArgs[svrArgsSz++] = strsep(&cursor, "\n");
                if (*cursor == 0)  /* eof */
                    do_it = 1; 
        }

        if (svrArgsSz == MAX_ARGS || cliArgsSz == MAX_ARGS) {
            fprintf(stderr, "too many arguments, forcing test run\n");
            do_it = 1;
        }

        if (do_it) {
            ret = execute_test_case(svrArgsSz, svrArgs, cliArgsSz, cliArgs,0,0);
            /* don't repeat if not supported in build */
            if (ret == 0) {
                execute_test_case(svrArgsSz, svrArgs, cliArgsSz, cliArgs, 0, 1);
                execute_test_case(svrArgsSz, svrArgs, cliArgsSz, cliArgs, 1, 0);
                execute_test_case(svrArgsSz, svrArgs, cliArgsSz, cliArgs, 1, 1);
            }
            svrArgsSz = 1;
            cliArgsSz = 1;
            cliMode   = 0;
        }
    }

    free(script);
    args->return_code = 0;
}


int SuiteTest(void)
{
    func_args args;
    char argv0[2][80];
    char* myArgv[2];

    printf(" Begin Cipher Suite Tests\n");

    /* setup */
    myArgv[0] = argv0[0];
    myArgv[1] = argv0[1];
    args.argv = myArgv;
    strcpy(argv0[0], "SuiteTest");

    (void)test_harness;

    cipherSuiteCtx = wolfSSL_CTX_new(wolfTLSv1_2_client_method());
    if (cipherSuiteCtx == NULL) {
        printf("can't get cipher suite ctx\n");
        exit(EXIT_FAILURE);  
    }

    /* default case */
    args.argc = 1;
    printf("starting default cipher suite tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        exit(EXIT_FAILURE);  
    }

    /* any extra cases will need another argument */
    args.argc = 2;

#ifdef WOLFSSL_DTLS 
    /* add dtls extra suites */
    strcpy(argv0[1], "tests/test-dtls.conf");
    printf("starting dtls extra cipher suite tests\n");
    test_harness(&args);
    if (args.return_code != 0) {
        printf("error from script %d\n", args.return_code);
        exit(EXIT_FAILURE);  
    }
#endif

    printf(" End Cipher Suite Tests\n");

    wolfSSL_CTX_free(cipherSuiteCtx);
    wolfSSL_Cleanup();

    return args.return_code;
}


