#include <pthread.h>
#include <stdlib.h>
#include <errno.h>

#include "wait_for_event.h"

struct event
{
    pthread_mutex_t mutex;
    pthread_cond_t cond;
    bool event_triggered;
};

struct event * event_create()
{
    struct event * ev = malloc( sizeof( struct event ) );

    ev->event_triggered = false;
    pthread_mutex_init( &ev->mutex, NULL );
    pthread_cond_init( &ev->cond, NULL );
    return ev;
}

void event_delete( struct event * ev )
{
    pthread_mutex_destroy( &ev->mutex );
    pthread_cond_destroy( &ev->cond );
    free( ev );
}

bool event_wait( struct event * ev )
{
    pthread_mutex_lock( &ev->mutex );

    while( ev->event_triggered == false )
    {
        pthread_cond_wait( &ev->cond, &ev->mutex );
    }

    pthread_mutex_unlock( &ev->mutex );
    return true;
}
bool event_wait_timed( struct event * ev,
                       time_t ms )
{
    struct timespec ts;
    int ret = 0;

    clock_gettime( CLOCK_REALTIME, &ts );
    //ts.tv_sec += ms;
    ts.tv_nsec += (ms * 1000000);
    pthread_mutex_lock( &ev->mutex );

    while( (ev->event_triggered == false) && (ret == 0) )
    {
        ret = pthread_cond_timedwait( &ev->cond, &ev->mutex, &ts );

        if( ( ret == -1 ) && ( errno == ETIMEDOUT ) )
        {
            return false;
        }
    }

    ev->event_triggered = false;
    pthread_mutex_unlock( &ev->mutex );
    return true;
}

void event_signal( struct event * ev )
{
    pthread_mutex_lock( &ev->mutex );
    ev->event_triggered = true;
    pthread_cond_signal( &ev->cond );
    pthread_mutex_unlock( &ev->mutex );
}
