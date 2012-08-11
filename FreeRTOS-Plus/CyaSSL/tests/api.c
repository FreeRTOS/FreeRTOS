/* api.c API unit tests
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

#include <stdlib.h>
#include <cyassl/ssl.h>
#define NO_MAIN_DRIVER
#include <cyassl/test.h>
#include "unit.h"

#define TEST_FAIL       (-1)
#define TEST_SUCCESS    (0)

static int test_CyaSSL_Init(void);
static int test_CyaSSL_Cleanup(void);
static int test_CyaSSL_Method_Allocators(void);
static int test_CyaSSL_CTX_new(CYASSL_METHOD *method);
#ifndef NO_FILESYSTEM
static int test_CyaSSL_CTX_use_certificate_file(void);
static int test_CyaSSL_CTX_use_PrivateKey_file(void);
static int test_CyaSSL_CTX_load_verify_locations(void);
static int test_server_CyaSSL_new(void);
static int test_client_CyaSSL_new(void);
static int test_CyaSSL_read_write(void);
#endif

/* test function helpers */
static int test_method(CYASSL_METHOD *method, const char *name);
static int test_method2(CYASSL_METHOD *method, const char *name);
#ifndef NO_FILESYSTEM
static int test_ucf(CYASSL_CTX *ctx, const char* file, int type,
    int cond, const char* name);
static int test_upkf(CYASSL_CTX *ctx, const char* file, int type,
    int cond, const char* name);
static int test_lvl(CYASSL_CTX *ctx, const char* file, const char* path,
    int cond, const char* name);

THREAD_RETURN CYASSL_THREAD test_server_nofail(void*);
void test_client_nofail(void*);
void wait_tcp_ready(func_args*);
#endif

static const char* bogusFile  = "/dev/null";
static const char* testingFmt = "   %s:";
static const char* resultFmt  = " %s\n";
static const char* passed     = "passed";
static const char* failed     = "failed";

/* List of methods found in echoserver.c that I'm skipping for the moment:
 * - CyaSSL_CTX_set_session_cache_mode()
 */

int ApiTest(void)
{
    printf(" Begin API Tests\n");
    test_CyaSSL_Init();
    test_CyaSSL_Method_Allocators();
    test_CyaSSL_CTX_new(CyaSSLv23_server_method());
#ifndef NO_FILESYSTEM
    test_CyaSSL_CTX_use_certificate_file();
    test_CyaSSL_CTX_use_PrivateKey_file();
    test_CyaSSL_CTX_load_verify_locations();
    test_server_CyaSSL_new();
    test_client_CyaSSL_new();
    test_CyaSSL_read_write();
#endif
    test_CyaSSL_Cleanup();
    printf(" End API Tests\n");

    return TEST_SUCCESS;
}

int test_CyaSSL_Init(void)
{
    int result;

    printf(testingFmt, "CyaSSL_Init()");
    result = CyaSSL_Init();
    printf(resultFmt, result ? failed : passed);

    return result;
}

static int test_CyaSSL_Cleanup(void)
{
    int result;

    printf(testingFmt, "CyaSSL_Cleanup()");
    result = CyaSSL_Cleanup();
    printf(resultFmt, result ? failed : passed);

    return result;
}

int test_method(CYASSL_METHOD *method, const char *name)
{
    printf(testingFmt, name);
    if (method == NULL)
    {
        printf(resultFmt, failed);
        return TEST_FAIL;
    }
    XFREE(method, 0, DYNAMIC_TYPE_METHOD);
    printf(resultFmt, passed);
    return TEST_SUCCESS;
}

int test_method2(CYASSL_METHOD *method, const char *name)
{
    printf(testingFmt, name);
    if (method != NULL)
    {
        XFREE(method, 0, DYNAMIC_TYPE_METHOD);
        printf(resultFmt, failed);
        return TEST_FAIL;
    }
    printf(resultFmt, passed);
    return TEST_SUCCESS;
}

int test_CyaSSL_Method_Allocators(void)
{
    test_method(CyaSSLv3_server_method(), "CyaSSLv3_server_method()");
    test_method(CyaSSLv3_client_method(), "CyaSSLv3_client_method()");
    test_method(CyaTLSv1_server_method(), "CyaTLSv1_server_method()");
    test_method(CyaTLSv1_client_method(), "CyaTLSv1_client_method()");
    test_method(CyaTLSv1_1_server_method(), "CyaTLSv1_1_server_method()");
    test_method(CyaTLSv1_1_client_method(), "CyaTLSv1_1_client_method()");
    test_method(CyaTLSv1_2_server_method(), "CyaTLSv1_2_server_method()");
    test_method(CyaTLSv1_2_client_method(), "CyaTLSv1_2_client_method()");
    test_method(CyaSSLv23_client_method(), "CyaSSLv23_client_method()");

#ifdef CYASSL_DTLS
    test_method(CyaDTLSv1_server_method(), "CyaDTLSv1_server_method()");
    test_method(CyaDTLSv1_client_method(), "CyaDTLSv1_client_method()");
#endif /* CYASSL_DTLS */

#ifdef OPENSSL_EXTRA
    test_method2(CyaSSLv2_server_method(), "CyaSSLv2_server_method()");
    test_method2(CyaSSLv2_client_method(), "CyaSSLv2_client_method()");
#endif /* OPENSSL_EXTRA */

    return TEST_SUCCESS;
}

int test_CyaSSL_CTX_new(CYASSL_METHOD *method)
{
    if (method != NULL)
    {
        CYASSL_CTX *ctx;
    
        printf(testingFmt, "CyaSSL_CTX_new(NULL)");
        ctx = CyaSSL_CTX_new(NULL);
        if (ctx != NULL)
        {
            CyaSSL_CTX_free(ctx);
            printf(resultFmt, failed);
        }
        else
            printf(resultFmt, passed);
    
        printf(testingFmt, "CyaSSL_CTX_new(method)");
        ctx = CyaSSL_CTX_new(method);
        if (ctx == NULL)
        {
            printf(resultFmt, failed);
            XFREE(method, 0, DYNAMIC_TYPE_METHOD);
            /* free the method data. if this was successful, freeing
               the CTX frees the method. */
        }
        else
        {
            CyaSSL_CTX_free(ctx);
            printf(resultFmt, passed);
        }
    }
    else
        printf("test_CyaSSL_CTX_new() called without method\n");

    return TEST_SUCCESS;
}

#ifndef NO_FILESYSTEM
/* Helper for testing CyaSSL_CTX_use_certificate_file() */
int test_ucf(CYASSL_CTX *ctx, const char* file, int type, int cond,
    const char* name)
{
    int result;

    printf(testingFmt, name);
    result = CyaSSL_CTX_use_certificate_file(ctx, file, type);
    if (result != cond)
    {
        printf(resultFmt, failed);
        return TEST_FAIL;
    }
    printf(resultFmt, passed);
    return TEST_SUCCESS;
}

int test_CyaSSL_CTX_use_certificate_file(void)
{
    CYASSL_METHOD *method;
    CYASSL_CTX *ctx;

    method = CyaSSLv23_server_method();
    if (method == NULL)
    {
        printf("test_CyaSSL_CTX_use_certificate_file() cannot create method\n");
        return TEST_FAIL;
    }

    ctx = CyaSSL_CTX_new(method);
    if (ctx == NULL)
    {
        printf("test_CyaSSL_CTX_use_certificate_file() cannot create context\n");
        XFREE(method, 0, DYNAMIC_TYPE_METHOD);
        return TEST_FAIL;
    }

    /* setting all parameters to garbage. this should succeed with
        failure */
    /* Then set the parameters to legit values but set each item to
        bogus and call again. Finish with a successful success. */

    test_ucf(NULL, NULL, 9999, SSL_FAILURE,
        "CyaSSL_CTX_use_certificate_file(NULL, NULL, 9999)");
/*  test_ucf(NULL, svrCert, SSL_FILETYPE_PEM, SSL_FAILURE,
        "CyaSSL_CTX_use_certificate_file(NULL, svrCert, SSL_FILETYPE_PEM)");*/
    test_ucf(ctx, bogusFile, SSL_FILETYPE_PEM, SSL_FAILURE,
        "CyaSSL_CTX_use_certificate_file(ctx, bogusFile, SSL_FILETYPE_PEM)");
    test_ucf(ctx, svrCert, 9999, SSL_FAILURE,
        "CyaSSL_CTX_use_certificate_file(ctx, svrCert, 9999)");
    test_ucf(ctx, svrCert, SSL_FILETYPE_PEM, SSL_SUCCESS,
        "CyaSSL_CTX_use_certificate_file(ctx, svrCert, SSL_FILETYPE_PEM)");

    CyaSSL_CTX_free(ctx);
    return TEST_SUCCESS;
}

/* Helper for testing CyaSSL_CTX_use_PrivateKey_file() */
int test_upkf(CYASSL_CTX *ctx, const char* file, int type, int cond,
    const char* name)
{
    int result;

    printf(testingFmt, name);
    result = CyaSSL_CTX_use_PrivateKey_file(ctx, file, type);
    if (result != cond)
    {
        printf(resultFmt, failed);
        return TEST_FAIL;
    }
    printf(resultFmt, passed);
    return TEST_SUCCESS;
}

int test_CyaSSL_CTX_use_PrivateKey_file(void)
{
    CYASSL_METHOD *method;
    CYASSL_CTX *ctx;

    method = CyaSSLv23_server_method();
    if (method == NULL)
    {
        printf("test_CyaSSL_CTX_use_PrivateKey_file() cannot create method\n");
        return TEST_FAIL;
    }

    ctx = CyaSSL_CTX_new(method);
    if (ctx == NULL)
    {
        printf("test_CyaSSL_CTX_use_PrivateKey_file() cannot create context\n");
        XFREE(method, 0, DYNAMIC_TYPE_METHOD);
        return TEST_FAIL;
    }

    test_upkf(NULL, NULL, 9999, SSL_FAILURE,
        "CyaSSL_CTX_use_PrivateKey_file(NULL, NULL, 9999)");
/*  test_upkf(NULL, svrKey, SSL_FILETYPE_PEM, SSL_FAILURE,
        "CyaSSL_CTX_use_PrivateKey_file(NULL, svrKey, SSL_FILETYPE_PEM)");*/
    test_upkf(ctx, bogusFile, SSL_FILETYPE_PEM, SSL_FAILURE,
        "CyaSSL_CTX_use_PrivateKey_file(ctx, bogusFile, SSL_FILETYPE_PEM)");
    test_upkf(ctx, svrKey, 9999, SSL_FAILURE,
        "CyaSSL_CTX_use_PrivateKey_file(ctx, svrKey, 9999)");
    test_upkf(ctx, svrKey, SSL_FILETYPE_PEM, SSL_SUCCESS,
        "CyaSSL_CTX_use_PrivateKey_file(ctx, svrKey, SSL_FILETYPE_PEM)");

    CyaSSL_CTX_free(ctx);
    return TEST_SUCCESS;
}

/* Helper for testing CyaSSL_CTX_load_verify_locations() */
int test_lvl(CYASSL_CTX *ctx, const char* file, const char* path, int cond,
    const char* name)
{
    int result;

    printf(testingFmt, name);
    /*
     * CyaSSL_CTX_load_verify_locations() returns SSL_SUCCESS (1) for 
     * success, SSL_FAILURE (0) for a non-specific failure, or a specific
     * failure code (<0). Need to normalize the return code to 1 or 0.
     */
    result = CyaSSL_CTX_load_verify_locations(ctx, file, path) >= SSL_SUCCESS;
    if (result != cond)
    {
        printf(resultFmt, failed);
        return TEST_FAIL;
    }
    printf(resultFmt, passed);
    return TEST_SUCCESS;
}

int test_CyaSSL_CTX_load_verify_locations(void)
{
    CYASSL_METHOD *method;
    CYASSL_CTX *ctx;

    method = CyaSSLv23_client_method();
    if (method == NULL)
    {
        printf("test_CyaSSL_CTX_load_verify_locations() cannot create method\n");
        return TEST_FAIL;
    }

    ctx = CyaSSL_CTX_new(method);
    if (ctx == NULL)
    {
        printf("test_CyaSSL_CTX_load_verify_locations() cannot create context\n");
        free(method);
        return TEST_FAIL;
    }
    
    test_lvl(NULL, NULL, NULL, SSL_FAILURE,
        "CyaSSL_CTX_load_verify_locations(NULL, NULL, NULL)");
    test_lvl(ctx, NULL, NULL, SSL_FAILURE,
        "CyaSSL_CTX_load_verify_locations(ctx, NULL, NULL)");
    test_lvl(NULL, caCert, NULL, SSL_FAILURE,
        "CyaSSL_CTX_load_verify_locations(ctx, NULL, NULL)");
    test_lvl(ctx, caCert, bogusFile, SSL_FAILURE,
        "CyaSSL_CTX_load_verify_locations(ctx, caCert, bogusFile)");
    /* Add a test for the certs directory path loading. */
    /* There is a leak here. If you load a second cert, the first one
       is lost. */
    test_lvl(ctx, caCert, 0, SSL_SUCCESS,
        "CyaSSL_CTX_load_verify_locations(ctx, caCert, 0)");

    CyaSSL_CTX_free(ctx);
    return TEST_SUCCESS;
}

int test_server_CyaSSL_new(void)
{
    int result;
    CYASSL_CTX *ctx;
    CYASSL_CTX *ctx_nocert;
    CYASSL *ssl;

    ctx = CyaSSL_CTX_new(CyaSSLv23_server_method());
    if (ctx == NULL)
    {
        printf("test_server_CyaSSL_new() cannot create context\n");
        return TEST_FAIL;
    }

    result = CyaSSL_CTX_use_certificate_file(ctx, svrCert, SSL_FILETYPE_PEM);
    if (result == SSL_FAILURE)
    {
        printf("test_server_CyaSSL_new() cannot obtain certificate\n");
        CyaSSL_CTX_free(ctx);
        return TEST_FAIL;
    }

    result = CyaSSL_CTX_use_PrivateKey_file(ctx, svrKey, SSL_FILETYPE_PEM);
    if (result == SSL_FAILURE)
    {
        printf("test_server_CyaSSL_new() cannot obtain key\n");
        CyaSSL_CTX_free(ctx);
        return TEST_FAIL;
    }

    ctx_nocert = CyaSSL_CTX_new(CyaSSLv23_server_method());
    if (ctx_nocert == NULL)
    {
        printf("test_server_CyaSSL_new() cannot create bogus context\n");
        CyaSSL_CTX_free(ctx);
        return TEST_FAIL;
    }

    printf(testingFmt, "CyaSSL_new(NULL) server");
    ssl = CyaSSL_new(NULL);
    if (ssl != NULL)
    {
        printf(resultFmt, failed);
        CyaSSL_free(ssl);
    }
    else
        printf(resultFmt, passed);

    printf(testingFmt, "CyaSSL_new(ctx_nocert) server");
    ssl = CyaSSL_new(ctx_nocert);
    if (ssl != NULL)
    {
        printf(resultFmt, failed);
        CyaSSL_free(ssl);
    }
    else
        printf(resultFmt, passed);

    printf(testingFmt, "CyaSSL_new(ctx) server");
    ssl = CyaSSL_new(ctx);
    if (ssl == NULL)
        printf(resultFmt, failed);
    else
    {
        printf(resultFmt, passed);
        CyaSSL_free(ssl);
    }
    
    CyaSSL_CTX_free(ctx_nocert);
    CyaSSL_CTX_free(ctx);
    return TEST_SUCCESS;
}

int test_client_CyaSSL_new(void)
{
    int result;
    CYASSL_CTX *ctx;
    CYASSL_CTX *ctx_nocert;
    CYASSL *ssl;

    ctx = CyaSSL_CTX_new(CyaSSLv23_client_method());
    if (ctx == NULL)
    {
        printf("test_client_CyaSSL_new() cannot create context\n");
        return TEST_FAIL;
    }

    result = CyaSSL_CTX_load_verify_locations(ctx, caCert, 0);
    if (result == SSL_FAILURE)
    {
        printf("test_client_CyaSSL_new() cannot obtain certificate\n");
        CyaSSL_CTX_free(ctx);
        return TEST_FAIL;
    }

    ctx_nocert = CyaSSL_CTX_new(CyaSSLv23_client_method());
    if (ctx_nocert == NULL)
    {
        printf("test_client_CyaSSL_new() cannot create bogus context\n");
        CyaSSL_CTX_free(ctx);
        return TEST_FAIL;
    }

    printf(testingFmt, "CyaSSL_new(NULL) client");
    ssl = CyaSSL_new(NULL);
    if (ssl != NULL)
    {
        printf(resultFmt, failed);
        CyaSSL_free(ssl);
    }
    else
        printf(resultFmt, passed);

    printf(testingFmt, "CyaSSL_new(ctx_nocert) client");
    ssl = CyaSSL_new(ctx_nocert);
    if (ssl == NULL)
        printf(resultFmt, failed);
    else
    {
        printf(resultFmt, passed);
        CyaSSL_free(ssl);
    }

    printf(testingFmt, "CyaSSL_new(ctx) client");
    ssl = CyaSSL_new(ctx);
    if (ssl == NULL)
        printf(resultFmt, failed);
    else
    {
        printf(resultFmt, passed);
        CyaSSL_free(ssl);
    }

    CyaSSL_CTX_free(ctx_nocert);
    CyaSSL_CTX_free(ctx);
    return TEST_SUCCESS;
}


static int test_CyaSSL_read_write(void)
{
    /* The unit testing for read and write shall happen simutaneously, since
     * one can't do anything with one without the other. (Except for a failure
     * test case.) This function will call all the others that will set up,
     * execute, and report their test findings.
     *
     * Set up the success case first. This function will become the template
     * for the other tests. This should eventually be renamed
     *
     * The success case isn't interesting, how can this fail?
     * - Do not give the client context a CA certificate. The connect should
     *   fail. Do not need server for this?
     * - Using NULL for the ssl object on server. Do not need client for this.
     * - Using NULL for the ssl object on client. Do not need server for this.
     * - Good ssl objects for client and server. Client write() without server
     *   read().
     * - Good ssl objects for client and server. Server write() without client
     *   read().
     * - Forgetting the password callback?
    */
    int test_result = TEST_SUCCESS;
    tcp_ready ready;
    func_args client_args;
    func_args server_args;
    THREAD_TYPE serverThread;

    StartTCP();

    InitTcpReady(&ready);
    server_args.signal = &ready;
    start_thread(test_server_nofail, &server_args, &serverThread);
    wait_tcp_ready(&server_args);
    test_client_nofail(&client_args);
    join_thread(serverThread);

    if (client_args.return_code != TEST_SUCCESS)
    {
        printf(resultFmt, "client failure");
        test_result = TEST_FAIL;
    }
    if (server_args.return_code != TEST_SUCCESS)
    {
        printf(resultFmt, "server failure");
        test_result = TEST_FAIL;
    }

    FreeTcpReady(&ready);

    return test_result;
};


THREAD_RETURN CYASSL_THREAD test_server_nofail(void* args)
{
    SOCKET_T sockfd = 0;
    int clientfd = 0;

    CYASSL_METHOD* method = 0;
    CYASSL_CTX* ctx = 0;
    CYASSL* ssl = 0;

    char msg[] = "I hear you fa shizzle!";
    char input[1024];
    int idx;
   
    ((func_args*)args)->return_code = TEST_FAIL;
    method = CyaSSLv23_server_method();
    ctx = CyaSSL_CTX_new(method);

    CyaSSL_CTX_set_verify(ctx,
                    SSL_VERIFY_PEER | SSL_VERIFY_FAIL_IF_NO_PEER_CERT, 0);

#ifdef OPENSSL_EXTRA
    CyaSSL_CTX_set_default_passwd_cb(ctx, PasswordCallBack);
#endif

    if (CyaSSL_CTX_load_verify_locations(ctx, cliCert, 0) != SSL_SUCCESS)
    {
        /*err_sys("can't load ca file, Please run from CyaSSL home dir");*/
        return 0;
    }
    if (CyaSSL_CTX_use_certificate_file(ctx, svrCert, SSL_FILETYPE_PEM)
            != SSL_SUCCESS)
    {
        /*err_sys("can't load server cert chain file, "
                "Please run from CyaSSL home dir");*/
        return 0;
    }
    if (CyaSSL_CTX_use_PrivateKey_file(ctx, svrKey, SSL_FILETYPE_PEM)
            != SSL_SUCCESS)
    {
        /*err_sys("can't load server key file, "
                "Please run from CyaSSL home dir");*/
        return 0;
    }
    ssl = CyaSSL_new(ctx);
    tcp_accept(&sockfd, &clientfd, (func_args*)args);
#ifndef CYASSL_DTLS
    CloseSocket(sockfd);
#endif

    CyaSSL_set_fd(ssl, clientfd);

#ifdef NO_PSK
    #if !defined(NO_FILESYSTEM) && defined(OPENSSL_EXTRA)
        CyaSSL_SetTmpDH_file(ssl, dhParam, SSL_FILETYPE_PEM);
    #else
        SetDH(ssl);  /* will repick suites with DHE, higher priority than PSK */
    #endif
#endif
    if (CyaSSL_accept(ssl) != SSL_SUCCESS)
    {
        int err = CyaSSL_get_error(ssl, 0);
        char buffer[80];
        printf("error = %d, %s\n", err, CyaSSL_ERR_error_string(err, buffer));
        /*err_sys("SSL_accept failed");*/
        return 0;
    }

    idx = CyaSSL_read(ssl, input, sizeof(input));
    if (idx > 0) {
        input[idx] = 0;
        printf("Client message: %s\n", input);
    }
    
    if (CyaSSL_write(ssl, msg, sizeof(msg)) != sizeof(msg))
    {
        /*err_sys("SSL_write failed");*/
        return 0;
    }

    CyaSSL_shutdown(ssl);
    CyaSSL_free(ssl);
    CyaSSL_CTX_free(ctx);
    
    CloseSocket(clientfd);
    ((func_args*)args)->return_code = TEST_SUCCESS;
    return 0;
}

void test_client_nofail(void* args)
{
    SOCKET_T sockfd = 0;

    CYASSL_METHOD*  method  = 0;
    CYASSL_CTX*     ctx     = 0;
    CYASSL*         ssl     = 0;

    char msg[64] = "hello cyassl!";
    char reply[1024];
    int  input;
    int  msgSz = strlen(msg);

    int     argc = ((func_args*)args)->argc;
    char**  argv = ((func_args*)args)->argv;

    ((func_args*)args)->return_code = TEST_FAIL;
    method = CyaSSLv23_client_method();
    ctx = CyaSSL_CTX_new(method);

#ifdef OPENSSL_EXTRA
    CyaSSL_CTX_set_default_passwd_cb(ctx, PasswordCallBack);
#endif

    if (CyaSSL_CTX_load_verify_locations(ctx, caCert, 0) != SSL_SUCCESS)
    {
        /* err_sys("can't load ca file, Please run from CyaSSL home dir");*/
        return;
    }
    if (CyaSSL_CTX_use_certificate_file(ctx, cliCert, SSL_FILETYPE_PEM)
            != SSL_SUCCESS)
    {
        /*err_sys("can't load client cert file, "
                "Please run from CyaSSL home dir");*/
        return;
    }
    if (CyaSSL_CTX_use_PrivateKey_file(ctx, cliKey, SSL_FILETYPE_PEM)
            != SSL_SUCCESS)
    {
        /*err_sys("can't load client key file, "
                "Please run from CyaSSL home dir");*/
        return;
    }

    tcp_connect(&sockfd, yasslIP, yasslPort);

    ssl = CyaSSL_new(ctx);
    CyaSSL_set_fd(ssl, sockfd);
    if (CyaSSL_connect(ssl) != SSL_SUCCESS)
    {
        int  err = CyaSSL_get_error(ssl, 0);
        char buffer[80];
        printf("err = %d, %s\n", err, CyaSSL_ERR_error_string(err, buffer));
        /*printf("SSL_connect failed");*/
        return;
    }

    if (CyaSSL_write(ssl, msg, msgSz) != msgSz)
    {
        /*err_sys("SSL_write failed");*/
        return;
    }

    input = CyaSSL_read(ssl, reply, sizeof(reply));
    if (input > 0)
    {
        reply[input] = 0;
        printf("Server response: %s\n", reply);
    }

    ((func_args*)args)->return_code = TEST_SUCCESS;
    return;
}



void wait_tcp_ready(func_args* args)
{
#ifdef _POSIX_THREADS
    pthread_mutex_lock(&args->signal->mutex);
    
    if (!args->signal->ready)
        pthread_cond_wait(&args->signal->cond, &args->signal->mutex);
    args->signal->ready = 0; /* reset */

    pthread_mutex_unlock(&args->signal->mutex);
#endif
}


void start_thread(THREAD_FUNC fun, func_args* args, THREAD_TYPE* thread)
{
#ifdef _POSIX_THREADS
    pthread_create(thread, 0, fun, args);
    return;
#else
    *thread = (THREAD_TYPE)_beginthreadex(0, 0, fun, args, 0, 0);
#endif
}


void join_thread(THREAD_TYPE thread)
{
#ifdef _POSIX_THREADS
    pthread_join(thread, 0);
#else
    int res = WaitForSingleObject(thread, INFINITE);
    assert(res == WAIT_OBJECT_0);
    res = CloseHandle(thread);
    assert(res);
#endif
}


void InitTcpReady(tcp_ready* ready)
{
    ready->ready = 0;
#ifdef _POSIX_THREADS
      pthread_mutex_init(&ready->mutex, 0);
      pthread_cond_init(&ready->cond, 0);
#endif
}


void FreeTcpReady(tcp_ready* ready)
{
#ifdef _POSIX_THREADS
    pthread_mutex_destroy(&ready->mutex);
    pthread_cond_destroy(&ready->cond);
#endif
}
#endif /* NO_FILESYSTEM */


