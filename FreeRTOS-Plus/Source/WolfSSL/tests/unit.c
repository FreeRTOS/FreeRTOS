/* unit.c unit tests driver */

/* Name change compatibility layer no longer need to be included here */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#include <stdio.h>
#include <tests/unit.h>


int myoptind = 0;
char* myoptarg = NULL;
int unit_test(int argc, char** argv);

#ifndef NO_TESTSUITE_MAIN_DRIVER
int main(int argc, char** argv)
{
    return unit_test(argc, argv);
}
#endif

int unit_test(int argc, char** argv)
{
    int ret;

    (void)argc;
    (void)argv;
    printf("starting unit tests...\n");

#ifdef HAVE_CAVIUM
    ret = OpenNitroxDevice(CAVIUM_DIRECT, CAVIUM_DEV_ID);
    if (ret != 0)
        err_sys("Cavium OpenNitroxDevice failed");
#endif /* HAVE_CAVIUM */

#ifndef WOLFSSL_TIRTOS
    if (CurrentDir("tests") || CurrentDir("_build"))
        ChangeDirBack(1);
    else if (CurrentDir("Debug") || CurrentDir("Release"))
        ChangeDirBack(3);
#endif

    ApiTest();

    if ( (ret = HashTest()) != 0){
        printf("hash test failed with %d\n", ret);
        return ret;
    }

#ifndef SINGLE_THREADED
    if ( (ret = SuiteTest()) != 0){
        printf("suite test failed with %d\n", ret);
        return ret;
    }
#endif

#ifdef HAVE_CAVIUM
        CspShutdown(CAVIUM_DEV_ID);
#endif

    return 0;
}



void wait_tcp_ready(func_args* args)
{
#ifdef SINGLE_THREADED
    (void)args;
#elif defined(_POSIX_THREADS) && !defined(__MINGW32__)
    pthread_mutex_lock(&args->signal->mutex);
    
    if (!args->signal->ready)
        pthread_cond_wait(&args->signal->cond, &args->signal->mutex);
    args->signal->ready = 0; /* reset */

    pthread_mutex_unlock(&args->signal->mutex);
#else
    (void)args;
#endif
}


void start_thread(THREAD_FUNC fun, func_args* args, THREAD_TYPE* thread)
{
#ifdef SINGLE_THREADED
    (void)fun;
    (void)args;
    (void)thread;
#elif defined(_POSIX_THREADS) && !defined(__MINGW32__)
    pthread_create(thread, 0, fun, args);
    return;
#elif defined (WOLFSSL_TIRTOS)
    /* Initialize the defaults and set the parameters. */
    Task_Params taskParams;
    Task_Params_init(&taskParams);
    taskParams.arg0 = (UArg)args;
    taskParams.stackSize = 65535;
    *thread = Task_create((Task_FuncPtr)fun, &taskParams, NULL);
    if (*thread == NULL) {
        printf("Failed to create new Task\n");
    }
    Task_yield();
#else
    *thread = (THREAD_TYPE)_beginthreadex(0, 0, fun, args, 0, 0);
#endif
}


void join_thread(THREAD_TYPE thread)
{
#ifdef SINGLE_THREADED
    (void)thread;
#elif defined(_POSIX_THREADS) && !defined(__MINGW32__)
    pthread_join(thread, 0);
#elif defined (WOLFSSL_TIRTOS)
    while(1) {
        if (Task_getMode(thread) == Task_Mode_TERMINATED) {
            Task_sleep(5);
            break;
        }
        Task_yield();
    }
#else
    int res = WaitForSingleObject((HANDLE)thread, INFINITE);
    assert(res == WAIT_OBJECT_0);
    res = CloseHandle((HANDLE)thread);
    assert(res);
#endif
}


void InitTcpReady(tcp_ready* ready)
{
    ready->ready = 0;
    ready->port = 0;
#ifdef SINGLE_THREADED
#elif defined(_POSIX_THREADS) && !defined(__MINGW32__)
      pthread_mutex_init(&ready->mutex, 0);
      pthread_cond_init(&ready->cond, 0);
#endif
}


void FreeTcpReady(tcp_ready* ready)
{
#ifdef SINGLE_THREADED
    (void)ready;
#elif defined(_POSIX_THREADS) && !defined(__MINGW32__)
    pthread_mutex_destroy(&ready->mutex);
    pthread_cond_destroy(&ready->cond);
#else
    (void)ready;
#endif
}

