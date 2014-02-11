/*
 * Copyright (c) 2001-2003 Swedish Institute of Computer Science.
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
 *
 */

/* lwIP includes. */
#include "lwip/debug.h"
#include "lwip/def.h"
#include "lwip/sys.h"
#include "lwip/mem.h"
#include "lwip/stats.h"

struct timeoutlist
{
	struct sys_timeouts timeouts;
	TaskHandle_t pid;
};

/* This is the number of threads that can be started with sys_thread_new() */
#define SYS_THREAD_MAX 4

static struct timeoutlist s_timeoutlist[SYS_THREAD_MAX];
static u16_t s_nextthread = 0;


/*-----------------------------------------------------------------------------------*/
//  Creates an empty mailbox.
sys_mbox_t sys_mbox_new(int size)
{
	QueueHandle_t mbox;

	( void ) size;

	mbox = xQueueCreate( archMESG_QUEUE_LENGTH, sizeof( void * ) );

#if SYS_STATS
      ++lwip_stats.sys.mbox.used;
      if (lwip_stats.sys.mbox.max < lwip_stats.sys.mbox.used) {
         lwip_stats.sys.mbox.max = lwip_stats.sys.mbox.used;
	  }
#endif /* SYS_STATS */

	return mbox;
}

/*-----------------------------------------------------------------------------------*/
/*
  Deallocates a mailbox. If there are messages still present in the
  mailbox when the mailbox is deallocated, it is an indication of a
  programming error in lwIP and the developer should be notified.
*/
void sys_mbox_free(sys_mbox_t mbox)
{
	if( uxQueueMessagesWaiting( mbox ) )
	{
		/* Line for breakpoint.  Should never break here! */
		portNOP();
#if SYS_STATS
	    lwip_stats.sys.mbox.err++;
#endif /* SYS_STATS */

		// TODO notify the user of failure.
	}

	vQueueDelete( mbox );

#if SYS_STATS
     --lwip_stats.sys.mbox.used;
#endif /* SYS_STATS */
}

/*-----------------------------------------------------------------------------------*/
//   Posts the "msg" to the mailbox.
void sys_mbox_post(sys_mbox_t mbox, void *data)
{
	while ( xQueueSendToBack(mbox, &data, portMAX_DELAY ) != pdTRUE ){}
}


/*-----------------------------------------------------------------------------------*/
//   Try to post the "msg" to the mailbox.
err_t sys_mbox_trypost(sys_mbox_t mbox, void *msg)
{
err_t result;

   if ( xQueueSend( mbox, &msg, 0 ) == pdPASS )
   {
      result = ERR_OK;
   }
   else {
      // could not post, queue must be full
      result = ERR_MEM;

#if SYS_STATS
      lwip_stats.sys.mbox.err++;
#endif /* SYS_STATS */

   }

   return result;
}

/*-----------------------------------------------------------------------------------*/
/*
  Blocks the thread until a message arrives in the mailbox, but does
  not block the thread longer than "timeout" milliseconds (similar to
  the sys_arch_sem_wait() function). The "msg" argument is a result
  parameter that is set by the function (i.e., by doing "*msg =
  ptr"). The "msg" parameter maybe NULL to indicate that the message
  should be dropped.

  The return values are the same as for the sys_arch_sem_wait() function:
  Number of milliseconds spent waiting or SYS_ARCH_TIMEOUT if there was a
  timeout.

  Note that a function with a similar name, sys_mbox_fetch(), is
  implemented by lwIP.
*/
u32_t sys_arch_mbox_fetch(sys_mbox_t mbox, void **msg, u32_t timeout)
{
void *dummyptr;
TickType_t StartTime, EndTime, Elapsed;

	StartTime = xTaskGetTickCount();

	if ( msg == NULL )
	{
		msg = &dummyptr;
	}

	if ( timeout != 0 )
	{
		if ( pdTRUE == xQueueReceive( mbox, &(*msg), timeout / portTICK_PERIOD_MS ) )
		{
			EndTime = xTaskGetTickCount();
			Elapsed = (EndTime - StartTime) * portTICK_PERIOD_MS;

			return ( Elapsed );
		}
		else // timed out blocking for message
		{
			*msg = NULL;

			return SYS_ARCH_TIMEOUT;
		}
	}
	else // block forever for a message.
	{
		while( pdTRUE != xQueueReceive( mbox, &(*msg), portMAX_DELAY ) ){} // time is arbitrary
		EndTime = xTaskGetTickCount();
		Elapsed = (EndTime - StartTime) * portTICK_PERIOD_MS;

		return ( Elapsed ); // return time blocked TODO test
	}
}

/*-----------------------------------------------------------------------------------*/
/*
  Similar to sys_arch_mbox_fetch, but if message is not ready immediately, we'll
  return with SYS_MBOX_EMPTY.  On success, 0 is returned.
*/
u32_t sys_arch_mbox_tryfetch(sys_mbox_t mbox, void **msg)
{
void *dummyptr;

	if ( msg == NULL )
	{
		msg = &dummyptr;
	}

   if ( pdTRUE == xQueueReceive( mbox, &(*msg), 0 ) )
   {
      return ERR_OK;
   }
   else
   {
      return SYS_MBOX_EMPTY;
   }
}

/*-----------------------------------------------------------------------------------*/
//  Creates and returns a new semaphore. The "count" argument specifies
//  the initial state of the semaphore.
sys_sem_t sys_sem_new(u8_t count)
{
	SemaphoreHandle_t  xSemaphore;

	vSemaphoreCreateBinary( xSemaphore );

	if( xSemaphore == NULL )
	{

#if SYS_STATS
      ++lwip_stats.sys.sem.err;
#endif /* SYS_STATS */

		return SYS_SEM_NULL;	// TODO need assert
	}

	if(count == 0)	// Means it can't be taken
	{
		xSemaphoreTake(xSemaphore,1);
	}

#if SYS_STATS
	++lwip_stats.sys.sem.used;
 	if (lwip_stats.sys.sem.max < lwip_stats.sys.sem.used) {
		lwip_stats.sys.sem.max = lwip_stats.sys.sem.used;
	}
#endif /* SYS_STATS */

	return xSemaphore;
}

/*-----------------------------------------------------------------------------------*/
/*
  Blocks the thread while waiting for the semaphore to be
  signaled. If the "timeout" argument is non-zero, the thread should
  only be blocked for the specified time (measured in
  milliseconds).

  If the timeout argument is non-zero, the return value is the number of
  milliseconds spent waiting for the semaphore to be signaled. If the
  semaphore wasn't signaled within the specified time, the return value is
  SYS_ARCH_TIMEOUT. If the thread didn't have to wait for the semaphore
  (i.e., it was already signaled), the function may return zero.

  Notice that lwIP implements a function with a similar name,
  sys_sem_wait(), that uses the sys_arch_sem_wait() function.
*/
u32_t sys_arch_sem_wait(sys_sem_t sem, u32_t timeout)
{
TickType_t StartTime, EndTime, Elapsed;

	StartTime = xTaskGetTickCount();

	if(	timeout != 0)
	{
		if( xSemaphoreTake( sem, timeout / portTICK_PERIOD_MS ) == pdTRUE )
		{
			EndTime = xTaskGetTickCount();
			Elapsed = (EndTime - StartTime) * portTICK_PERIOD_MS;

			return (Elapsed); // return time blocked TODO test
		}
		else
		{
			return SYS_ARCH_TIMEOUT;
		}
	}
	else // must block without a timeout
	{
		while( xSemaphoreTake( sem, portMAX_DELAY ) != pdTRUE ){}
		EndTime = xTaskGetTickCount();
		Elapsed = (EndTime - StartTime) * portTICK_PERIOD_MS;

		return ( Elapsed ); // return time blocked

	}
}

/*-----------------------------------------------------------------------------------*/
// Signals a semaphore
void sys_sem_signal(sys_sem_t sem)
{
	xSemaphoreGive( sem );
}

/*-----------------------------------------------------------------------------------*/
// Deallocates a semaphore
void sys_sem_free(sys_sem_t sem)
{
#if SYS_STATS
      --lwip_stats.sys.sem.used;
#endif /* SYS_STATS */

	vQueueDelete( sem );
}

/*-----------------------------------------------------------------------------------*/
// Initialize sys arch
void sys_init(void)
{
	int i;

	// Initialize the the per-thread sys_timeouts structures
	// make sure there are no valid pids in the list
	for(i = 0; i < SYS_THREAD_MAX; i++)
	{
		s_timeoutlist[i].pid = 0;
		s_timeoutlist[i].timeouts.next = NULL;
	}

	// keep track of how many threads have been created
	s_nextthread = 0;
}

/*-----------------------------------------------------------------------------------*/
/*
  Returns a pointer to the per-thread sys_timeouts structure. In lwIP,
  each thread has a list of timeouts which is represented as a linked
  list of sys_timeout structures. The sys_timeouts structure holds a
  pointer to a linked list of timeouts. This function is called by
  the lwIP timeout scheduler and must not return a NULL value.

  In a single threaded sys_arch implementation, this function will
  simply return a pointer to a global sys_timeouts variable stored in
  the sys_arch module.
*/
struct sys_timeouts *sys_arch_timeouts(void)
{
int i;
TaskHandle_t pid;
struct timeoutlist *tl;

	pid = xTaskGetCurrentTaskHandle( );

	for(i = 0; i < s_nextthread; i++)
	{
		tl = &(s_timeoutlist[i]);
		if(tl->pid == pid)
		{
			return &(tl->timeouts);
		}
	}

	// Error
	return NULL;
}

/*-----------------------------------------------------------------------------------*/
/*-----------------------------------------------------------------------------------*/
// TODO
/*-----------------------------------------------------------------------------------*/
/*
  Starts a new thread with priority "prio" that will begin its execution in the
  function "thread()". The "arg" argument will be passed as an argument to the
  thread() function. The id of the new thread is returned. Both the id and
  the priority are system dependent.
*/
sys_thread_t sys_thread_new(char *name, void (* thread)(void *arg), void *arg, int stacksize, int prio)
{
TaskHandle_t CreatedTask;
int result;

   if ( s_nextthread < SYS_THREAD_MAX )
   {
      result = xTaskCreate( thread, name, stacksize, arg, prio, &CreatedTask );

	   // For each task created, store the task handle (pid) in the timers array.
	   // This scheme doesn't allow for threads to be deleted
	   s_timeoutlist[s_nextthread++].pid = CreatedTask;

	   if(result == pdPASS)
	   {
		   return CreatedTask;
	   }
	   else
	   {
		   return NULL;
	   }
   }
   else
   {
      return NULL;
   }
}

/*
  This optional function does a "fast" critical region protection and returns
  the previous protection level. This function is only called during very short
  critical regions. An embedded system which supports ISR-based drivers might
  want to implement this function by disabling interrupts. Task-based systems
  might want to implement this by using a mutex or disabling tasking. This
  function should support recursive calls from the same task or interrupt. In
  other words, sys_arch_protect() could be called while already protected. In
  that case the return value indicates that it is already protected.

  sys_arch_protect() is only required if your port is supporting an operating
  system.
*/
sys_prot_t sys_arch_protect(void)
{
	vPortEnterCritical();
	return 1;
}

/*
  This optional function does a "fast" set of critical region protection to the
  value specified by pval. See the documentation for sys_arch_protect() for
  more information. This function is only required if your port is supporting
  an operating system.
*/
void sys_arch_unprotect(sys_prot_t pval)
{
	( void ) pval;
	vPortExitCritical();
}

/*
 * Prints an assertion messages and aborts execution.
 */
void sys_assert( const char *msg )
{
	( void ) msg;
	/*FSL:only needed for debugging
	printf(msg);
	printf("\n\r");
	*/
    vPortEnterCritical(  );
    for(;;)
    ;
}
