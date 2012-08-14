/* unit.c unit tests driver */
#include <stdio.h>
#include <tests/unit.h>


int myoptind = 0;
char* myoptarg = NULL;


int main(int argc, char** argv)
{
    int ret;

    printf("staring unit tests...\n");

    if ( (ret = ApiTest()) != 0) {
        printf("api test failed with %d\n", ret);
        return ret;
    }

    if ( (ret = HashTest()) != 0){
        printf("hash test failed with %d\n", ret);
        return ret;
    }

    if ( (ret = SuiteTest()) != 0){
        printf("suite test failed with %d\n", ret);
        return ret;
    }

    return 0;
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