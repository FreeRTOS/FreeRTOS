/*
 * Copyright (c) 2001-2003 Swedish Institute of Computer Science.
 * Modifications Copyright (c) 2006 Christian Walter <wolti@sil.at>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT
 * SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
 * OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
 * OF SUCH DAMAGE.
 *
 * This file is part of the lwIP TCP/IP stack.
 *
 * Author: Adam Dunkels <adam@sics.se>
 * Modifcations: Christian Walter <wolti@sil.at>
 *
 * $Id: sys_arch.c,v 1.1 2008/08/05 00:10:49 b06862 Exp $
 */

/* ------------------------ System includes ------------------------------- */

#include "stdlib.h"

/* ------------------------ FreeRTOS includes ----------------------------- */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* ------------------------ lwIP includes --------------------------------- */
#include "lwip/debug.h"
#include "lwip/def.h"
#include "lwip/sys.h"
#include "lwip/mem.h"
#include "lwip/sio.h"
#include "lwip/stats.h"

/* ------------------------ Project includes ------------------------------ */

/* ------------------------ Defines --------------------------------------- */
/* This is the number of threads that can be started with sys_thead_new() */
#define SYS_MBOX_SIZE               ( 16 )
#define MS_TO_TICKS( ms )           \
    ( TickType_t )( ( TickType_t ) ( ms ) / portTICK_PERIOD_MS )
#define TICKS_TO_MS( ticks )        \
    ( unsigned long )( ( TickType_t ) ( ticks ) * portTICK_PERIOD_MS )
#define THREAD_STACK_SIZE           ( 256 /*FSL:1024*/ )
#define THREAD_NAME                 "lwIP"

#define THREAD_INIT( tcb ) \
    do { \
        tcb->next = NULL; \
        tcb->pid = ( TaskHandle_t )0; \
        tcb->timeouts.next = NULL; \
    } while( 0 )

/* ------------------------ Type definitions ------------------------------ */
typedef struct sys_tcb
{
    struct sys_tcb *next;
    struct sys_timeouts timeouts;
    TaskHandle_t     pid;
} sys_tcb_t;

/* ------------------------ Prototypes ------------------------------------ */

/* ------------------------ Static functions ------------------------------ */
sys_tcb_t      *sys_thread_current( void );

/* ------------------------ Static variables ------------------------------ */
static sys_tcb_t *tasks = NULL;

/* ------------------------ Start implementation -------------------------- */
void
sys_init( void )
{
    LWIP_ASSERT( "sys_init: not called first", tasks == NULL );
    tasks = NULL;
}

/*
 * This optional function does a "fast" critical region protection and returns
 * the previous protection level. This function is only called during very short
 * critical regions. An embedded system which supports ISR-based drivers might
 * want to implement this function by disabling interrupts. Task-based systems
 * might want to implement this by using a mutex or disabling tasking. This
 * function should support recursive calls from the same task or interrupt. In
 * other words, sys_arch_protect() could be called while already protected. In
 * that case the return value indicates that it is already protected.
 *
 * sys_arch_protect() is only required if your port is supporting an operating
 * system.
 */
sys_prot_t
sys_arch_protect( void )
{
    vPortEnterCritical(  );
    return 1;
}

/*
 * This optional function does a "fast" set of critical region protection to the
 * value specified by pval. See the documentation for sys_arch_protect() for
 * more information. This function is only required if your port is supporting
 * an operating system.
 */
void
sys_arch_unprotect( sys_prot_t pval )
{
    ( void )pval;
    vPortExitCritical(  );
}

/*
 * Prints an assertion messages and aborts execution.
 */
void
sys_assert( const char *msg )
{
	/*FSL:only needed for debugging
	printf(msg);
	printf("\n\r");
	*/
    vPortEnterCritical(  );
    for(;;)
    ;
}

void
sys_debug( const char *const fmt, ... )
{
	/*FSL: same implementation as printf*/

    /*FSL: removed due to lack of space*/
    //printf(fmt);
}

/* ------------------------ Start implementation ( Threads ) -------------- */

/*
 * Starts a new thread with priority "prio" that will begin its execution in the
 * function "thread()". The "arg" argument will be passed as an argument to the
 * thread() function. The argument "ssize" is the requested stack size for the
 * new thread. The id of the new thread is returned. Both the id and the
 * priority are system dependent.
 */
sys_thread_t
sys_thread_new(char *name, void ( *thread ) ( void *arg ), void *arg, int /*size_t*/ stacksize, int prio )
{
    sys_thread_t    thread_hdl = SYS_THREAD_NULL;
    int             i;
    sys_tcb_t      *p;

    /* We disable the FreeRTOS scheduler because it might be the case that the new
     * tasks gets scheduled inside the xTaskCreate function. To prevent this we
     * disable the scheduling. Note that this can happen although we have interrupts
     * disabled because xTaskCreate contains a call to taskYIELD( ).
     */
    vPortEnterCritical(  );

    p = tasks;
    i = 0;
    /* We are called the first time. Initialize it. */
    if( p == NULL )
    {
        p = (sys_tcb_t *)pvPortMalloc( sizeof( sys_tcb_t ) );
        if( p != NULL )
        {
            tasks = p;
        }
    }
    else
    {
        /* First task already counter. */
        i++;
        /* Cycle to the end of the list. */
        while( p->next != NULL )
        {
            i++;
            p = p->next;
        }
        p->next = (sys_tcb_t *)pvPortMalloc( sizeof( sys_tcb_t ) );
        p = p->next;
    }

    if( p != NULL )
    {
        /* Memory allocated. Initialize the data structure. */
        THREAD_INIT( p );

        /* Now q points to a free element in the list. */
        if( xTaskCreate( thread, name, stacksize, arg, prio, &p->pid ) == pdPASS )
        {
            thread_hdl = p;
        }
        else
        {
            vPortFree( p );
        }
    }

    vPortExitCritical(  );
    return thread_hdl;
}

void
sys_arch_thread_remove( sys_thread_t hdl )
{
    sys_tcb_t      *current = tasks, *prev;
    sys_tcb_t      *toremove = hdl;
    TaskHandle_t     pid = ( TaskHandle_t ) 0;

    LWIP_ASSERT( "sys_arch_thread_remove: assertion hdl != NULL failed!", hdl != NULL );

    /* If we have to remove the first task we must update the global "tasks"
     * variable. */
    vPortEnterCritical(  );
    if( hdl != NULL )
    {
        prev = NULL;
        while( ( current != NULL ) && ( current != toremove ) )
        {
            prev = current;
            current = current->next;
        }
        /* Found it. */
        if( current == toremove )
        {
            /* Not the first entry in the list. */
            if( prev != NULL )
            {
                prev->next = toremove->next;
            }
            else
            {
                tasks = toremove->next;
            }
            LWIP_ASSERT( "sys_arch_thread_remove: can't remove thread with timeouts!",
                         toremove->timeouts.next == NULL );
            pid = toremove->pid;
            THREAD_INIT( toremove );
            vPortFree( toremove );
        }
    }
    /* We are done with accessing the shared datastructure. Release the
     * resources.
     */
    vPortExitCritical(  );
    if( pid != ( TaskHandle_t ) 0 )
    {
        vTaskDelete( pid );
        /* not reached. */
    }
}

/*
 * Returns the thread control block for the currently active task. In case
 * of an error the functions returns NULL.
 */
sys_thread_t
sys_arch_thread_current( void )
{
    sys_tcb_t      *p = tasks;
    TaskHandle_t     pid = xTaskGetCurrentTaskHandle(  );

    vPortEnterCritical(  );
    while( ( p != NULL ) && ( p->pid != pid ) )
    {
        p = p->next;
    }
    vPortExitCritical(  );
    return p;
}

/*
 * Returns a pointer to the per-thread sys_timeouts structure. In lwIP,
 * each thread has a list of timeouts which is represented as a linked
 * list of sys_timeout structures. The sys_timeouts structure holds a
 * pointer to a linked list of timeouts. This function is called by
 * the lwIP timeout scheduler and must not return a NULL value.
 *
 * In a single threaded sys_arch implementation, this function will
 * simply return a pointer to a global sys_timeouts variable stored in
 * the sys_arch module.
 */
struct sys_timeouts *
sys_arch_timeouts( void )
{
    sys_tcb_t      *ptask;

    ptask = sys_arch_thread_current(  );
    LWIP_ASSERT( "sys_arch_timeouts: ptask != NULL", ptask != NULL );
    return ptask != NULL ? &( ptask->timeouts ) : NULL;
}

/* ------------------------ Start implementation ( Semaphores ) ----------- */

/* Creates and returns a new semaphore. The "count" argument specifies
 * the initial state of the semaphore.
 */
sys_sem_t
sys_sem_new( u8_t count )
{
    SemaphoreHandle_t xSemaphore;

    vSemaphoreCreateBinary( xSemaphore );
    if( xSemaphore != SYS_SEM_NULL )
    {
        if( count == 0 )
        {
            xSemaphoreTake( xSemaphore, 1 );
        }
#if SYS_STATS == 1
        vPortEnterCritical(  );
        lwip_stats.sys.sem.used++;
        if( lwip_stats.sys.sem.used > lwip_stats.sys.sem.max )
        {
            lwip_stats.sys.sem.max = lwip_stats.sys.sem.used;
        }
        vPortExitCritical(  );
#endif
    }
    else
    {
        LWIP_ASSERT( "sys_sem_new: xSemaphore == SYS_SEM_NULL", xSemaphore != SYS_SEM_NULL );
    }

    return xSemaphore;
}

/* Deallocates a semaphore */
void
sys_sem_free( sys_sem_t sem )
{
    LWIP_ASSERT( "sys_sem_free: sem != SYS_SEM_NULL", sem != SYS_SEM_NULL );
    if( sem != SYS_SEM_NULL )
    {
#if SYS_STATS == 1
        vPortEnterCritical(  );
        lwip_stats.sys.sem.used--;
        vPortExitCritical(  );
#endif
        vQueueDelete( sem );
    }
}

/* Signals a semaphore */
void
sys_sem_signal( sys_sem_t sem )
{
    LWIP_ASSERT( "sys_sem_signal: sem != SYS_SEM_NULL", sem != SYS_SEM_NULL );
    xSemaphoreGive( sem );
}

/*
 * Blocks the thread while waiting for the semaphore to be
 * signaled. If the "timeout" argument is non-zero, the thread should
 * only be blocked for the specified time (measured in
 * milliseconds).
 *
 * If the timeout argument is non-zero, the return value is the number of
 * milliseconds spent waiting for the semaphore to be signaled. If the
 * semaphore wasn't signaled within the specified time, the return value is
 * SYS_ARCH_TIMEOUT. If the thread didn't have to wait for the semaphore
 * (i.e., it was already signaled), the function may return zero.
 *
 * Notice that lwIP implements a function with a similar name,
 * sys_sem_wait(), that uses the sys_arch_sem_wait() function.
 */
u32_t
sys_arch_sem_wait( sys_sem_t sem, u32_t timeout )
{
    portBASE_TYPE   xStatus;
    TickType_t    xTicksStart, xTicksEnd, xTicksElapsed;
    u32_t           timespent;

    LWIP_ASSERT( "sys_arch_sem_wait: sem != SYS_SEM_NULL", sem != SYS_SEM_NULL );
    xTicksStart = xTaskGetTickCount(  );
    if( timeout == 0 )
    {
        do
        {
            xStatus = xSemaphoreTake( sem, MS_TO_TICKS( 100 ) );
        }
        while( xStatus != pdTRUE );
    }
    else
    {
        xStatus = xSemaphoreTake( sem, MS_TO_TICKS( timeout ) );
    }

    /* Semaphore was signaled. */
    if( xStatus == pdTRUE )
    {
        xTicksEnd = xTaskGetTickCount(  );
        xTicksElapsed = xTicksEnd - xTicksStart;
        timespent = TICKS_TO_MS( xTicksElapsed );
    }
    else
    {
        timespent = SYS_ARCH_TIMEOUT;
    }
    return timespent;
}


/* ------------------------ Start implementation ( Mailboxes ) ------------ */

/* Creates an empty mailbox. */
sys_mbox_t
sys_mbox_new( /*paolo:void*/int size )
{
    QueueHandle_t    mbox;

    mbox = xQueueCreate( SYS_MBOX_SIZE/*size*/, sizeof( void * ) );
    if( mbox != SYS_MBOX_NULL )
    {
#if SYS_STATS == 1
        vPortEnterCritical(  );
        lwip_stats.sys.mbox.used++;
        if( lwip_stats.sys.mbox.used > lwip_stats.sys.mbox.max )
        {
            lwip_stats.sys.mbox.max = lwip_stats.sys.mbox.used;
        }
        vPortExitCritical(  );
#endif
    }
    return mbox;
}

/*
  Deallocates a mailbox. If there are messages still present in the
  mailbox when the mailbox is deallocated, it is an indication of a
  programming error in lwIP and the developer should be notified.
*/
void
sys_mbox_free( sys_mbox_t mbox )
{
    void           *msg;

    LWIP_ASSERT( "sys_mbox_free: mbox != SYS_MBOX_NULL", mbox != SYS_MBOX_NULL );
    if( mbox != SYS_MBOX_NULL )
    {
        while( uxQueueMessagesWaiting( mbox ) != 0 )
        {
            if( sys_arch_mbox_fetch( mbox, &msg, 1 ) != SYS_ARCH_TIMEOUT )
            {
                LWIP_ASSERT( "sys_mbox_free: memory leak (msg != NULL)", msg == NULL );
            }
        }
        vQueueDelete( mbox );
#if SYS_STATS == 1
        vPortEnterCritical(  );
        lwip_stats.sys.mbox.used--;
        vPortExitCritical(  );
#endif
    }
}

/*
 * This function sends a message to a mailbox. It is unusual in that no error
 * return is made. This is because the caller is responsible for ensuring that
 * the mailbox queue will not fail. The caller does this by limiting the number
 * of msg structures which exist for a given mailbox.
 */
void
sys_mbox_post( sys_mbox_t mbox, void *data )
{
    portBASE_TYPE   xQueueSent;

    /* Queue must not be full - Otherwise it is an error. */
    xQueueSent = xQueueSend( mbox, &data, 0 );
    LWIP_ASSERT( "sys_mbox_post: xQueueSent == pdPASS", xQueueSent == pdPASS );
}

/*FSL*/
/*
 *Try to post the "msg" to the mailbox. Returns ERR_MEM if this one
 *is full, else, ERR_OK if the "msg" is posted.
 */
err_t
sys_mbox_trypost( sys_mbox_t mbox, void *data )
{
    /* Queue must not be full - Otherwise it is an error. */
    if(xQueueSend( mbox, &data, 0 ) == pdPASS)
    {
    	return ERR_OK;
    }
    else
    {
    	return ERR_MEM;
    }
}

/*
 * Blocks the thread until a message arrives in the mailbox, but does
 * not block the thread longer than "timeout" milliseconds (similar to
 * the sys_arch_sem_wait() function). The "msg" argument is a result
 * parameter that is set by the function (i.e., by doing "*msg =
 * ptr"). The "msg" parameter maybe NULL to indicate that the message
 * should be dropped.
 *
 * Note that a function with a similar name, sys_mbox_fetch(), is
 * implemented by lwIP.
 */
u32_t
sys_arch_mbox_fetch( sys_mbox_t mbox, void **msg, u32_t timeout )
{
    void           *ret_msg;
    portBASE_TYPE   xStatus;
    TickType_t    xTicksStart, xTicksEnd, xTicksElapsed;
    u32_t           timespent;

    LWIP_ASSERT( "sys_arch_mbox_fetch: mbox != SYS_MBOX_NULL", mbox != SYS_MBOX_NULL );
    xTicksStart = xTaskGetTickCount(  );
    if( timeout == 0 )
    {
        do
        {
            xStatus = xQueueReceive( mbox, &ret_msg, MS_TO_TICKS( 100 ) );
        }
        while( xStatus != pdTRUE );
    }
    else
    {
        xStatus = xQueueReceive( mbox, &ret_msg, MS_TO_TICKS( timeout ) );
    }

    if( xStatus == pdTRUE )
    {
        if( msg )
        {
            *msg = ret_msg;
        }
        xTicksEnd = xTaskGetTickCount(  );
        xTicksElapsed = xTicksEnd - xTicksStart;
        timespent = TICKS_TO_MS( xTicksElapsed );
    }
    else
    {
        if( msg )
        {
            *msg = NULL;
        }
        timespent = SYS_ARCH_TIMEOUT;
    }
    return timespent;
}

u32_t
sys_jiffies( void )
{
    TickType_t    xTicks = xTaskGetTickCount(  );

    return ( u32_t )TICKS_TO_MS( xTicks );
}
