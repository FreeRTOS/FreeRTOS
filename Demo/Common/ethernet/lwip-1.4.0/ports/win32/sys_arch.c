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

//*****************************************************************************
//
// Include OS functionality.
//
//*****************************************************************************

/* ------------------------ System architecture includes ----------------------------- */
#include "arch/sys_arch.h"

/* ------------------------ lwIP includes --------------------------------- */
#include "lwip/opt.h"

#include "lwip/debug.h"
#include "lwip/def.h"
#include "lwip/sys.h"
#include "lwip/mem.h"
#include "lwip/stats.h"

/*---------------------------------------------------------------------------*
 * Globals:
 *---------------------------------------------------------------------------*/

#if 0
_RB_
struct timeoutlist
{
	struct sys_timeouts timeouts;
	xTaskHandle pid;
};

/* This is the number of threads that can be started with sys_thread_new() */
#define SYS_THREAD_MAX 4

static u16_t s_nextthread = 0;

static struct timeoutlist s_timeoutlist[SYS_THREAD_MAX];
#endif

/*-----------------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*
 * Routine:  sys_mbox_new
 *---------------------------------------------------------------------------*
 * Description:
 *      Creates a new mailbox
 * Inputs:
 *      int size                -- Size of elements in the mailbox
 * Outputs:
 *      sys_mbox_t              -- Handle to new mailbox
 *---------------------------------------------------------------------------*/
err_t sys_mbox_new(sys_mbox_t *mbox, int size)
{
err_t lwip_err= ERR_MEM;

	*mbox = xQueueCreate( size, sizeof( void * ) );

	// Created succesfully?
	if(*mbox != NULL)
	{
		lwip_err = ERR_OK;
#if SYS_STATS
		SYS_STATS_INC(mbox.used);
#endif /* SYS_STATS */
	}

	return lwip_err;
}


/*---------------------------------------------------------------------------*
 * Routine:  sys_mbox_free
 *---------------------------------------------------------------------------*
 * Description:
 *      Deallocates a mailbox. If there are messages still present in the
 *      mailbox when the mailbox is deallocated, it is an indication of a
 *      programming error in lwIP and the developer should be notified.
 * Inputs:
 *      sys_mbox_t mbox         -- Handle of mailbox
 * Outputs:
 *      sys_mbox_t              -- Handle to new mailbox
 *---------------------------------------------------------------------------*/
void sys_mbox_free(sys_mbox_t *mbox)
{
unsigned portBASE_TYPE uxMessagesWaiting;

	uxMessagesWaiting = uxQueueMessagesWaiting( *mbox );
	configASSERT( ( uxMessagesWaiting == 0 ) );

#if SYS_STATS
	if (uxMessagesWaiting != 0U)
	{
		SYS_STATS_INC(mbox.err);
	}

	SYS_STATS_DEC(mbox.used);
#endif /* SYS_STATS */

	vQueueDelete( *mbox );
}

/*---------------------------------------------------------------------------*
 * Routine:  sys_mbox_post
 *---------------------------------------------------------------------------*
 * Description:
 *      Post the "msg" to the mailbox.
 * Inputs:
 *      sys_mbox_t mbox         -- Handle of mailbox
 *      void *data              -- Pointer to data to post
 *---------------------------------------------------------------------------*/
void sys_mbox_post(sys_mbox_t *mbox, void *msg)
{
	while( xQueueSendToBack( *mbox, &msg, portMAX_DELAY ) != pdTRUE );
}

/*---------------------------------------------------------------------------*
 * Routine:  sys_mbox_trypost
 *---------------------------------------------------------------------------*
 * Description:
 *      Try to post the "msg" to the mailbox.  Returns immediately with
 *      error if cannot.
 * Inputs:
 *      sys_mbox_t mbox         -- Handle of mailbox
 *      void *msg               -- Pointer to data to post
 * Outputs:
 *      err_t                   -- ERR_OK if message posted, else ERR_MEM
 *                                  if not.
 *---------------------------------------------------------------------------*/
err_t sys_mbox_trypost(sys_mbox_t *mbox, void *msg)
{
err_t result;

	if ( xQueueSend( *mbox, &msg, 0 ) == pdPASS )
	{
		result = ERR_OK;
	}
	else
	{
		// could not post, queue must be full
		result = ERR_MEM;
#if SYS_STATS
		SYS_STATS_INC(mbox.err);
#endif /* SYS_STATS */
	}
	return result;
}

/*---------------------------------------------------------------------------*
 * Routine:  sys_arch_mbox_fetch
 *---------------------------------------------------------------------------*
 * Description:
 *      Blocks the thread until a message arrives in the mailbox, but does
 *      not block the thread longer than "timeout" milliseconds (similar to
 *      the sys_arch_sem_wait() function). The "msg" argument is a result
 *      parameter that is set by the function (i.e., by doing "*msg =
 *      ptr"). The "msg" parameter maybe NULL to indicate that the message
 *      should be dropped.
 *
 *      The return values are the same as for the sys_arch_sem_wait() function:
 *      Number of milliseconds spent waiting or SYS_ARCH_TIMEOUT if there was a
 *      timeout.
 *
 *      Note that a function with a similar name, sys_mbox_fetch(), is
 *      implemented by lwIP.
 * Inputs:
 *      sys_mbox_t mbox         -- Handle of mailbox
 *      void **msg              -- Pointer to pointer to msg received
 *      u32_t timeout           -- Number of milliseconds until timeout
 * Outputs:
 *      u32_t                   -- SYS_ARCH_TIMEOUT if timeout, else number
 *                                  of milliseconds until received.
 *---------------------------------------------------------------------------*/
u32_t sys_arch_mbox_fetch(sys_mbox_t *mbox, void **msg, u32_t timeout)
{
void *dummyptr;
portTickType StartTime, EndTime, Elapsed;

	StartTime = xTaskGetTickCount();

	if (NULL == msg)
	{
		msg = &dummyptr;
	}

	if (timeout != 0)
	{
		if ( pdTRUE == xQueueReceive( *mbox, &(*msg), timeout / portTICK_RATE_MS ) )
		{
			EndTime = xTaskGetTickCount();
			Elapsed = (EndTime - StartTime) * portTICK_RATE_MS;

			return ( Elapsed );
		}
		else // timed out blocking for message
		{
			*msg = NULL;

			return SYS_ARCH_TIMEOUT;
		}
	}
	else
	{
		while( pdTRUE != xQueueReceive( mbox, &(*msg), portMAX_DELAY ) ); // time is arbitrary
		EndTime = xTaskGetTickCount();
		Elapsed = (EndTime - StartTime) * portTICK_RATE_MS;

		if (Elapsed == 0)
		{
			Elapsed = 1;
		}

		// return time blocked TBD test
		return (Elapsed);
	}
}

/*---------------------------------------------------------------------------*
 * Routine:  sys_arch_mbox_tryfetch
 *---------------------------------------------------------------------------*
 * Description:
 *      Similar to sys_arch_mbox_fetch, but if message is not ready
 *      immediately, we'll return with SYS_MBOX_EMPTY.  On success, 0 is
 *      returned.
 * Inputs:
 *      sys_mbox_t mbox         -- Handle of mailbox
 *      void **msg              -- Pointer to pointer to msg received
 * Outputs:
 *      u32_t                   -- SYS_MBOX_EMPTY if no messages.  Otherwise,
 *                                  return ERR_OK.
 *---------------------------------------------------------------------------*/
u32_t sys_arch_mbox_tryfetch(sys_mbox_t *mbox, void **msg)
{
	void *dummyptr;

	if (msg == NULL)
	{
		msg = &dummyptr;
	}

	if ( pdTRUE == xQueueReceive( *mbox, &(*msg), 0 ) )
	{
		return ERR_OK;
	}
	else
	{
		return SYS_MBOX_EMPTY;
	}
}

/*---------------------------------------------------------------------------*
 * Routine:  sys_sem_new
 *---------------------------------------------------------------------------*
 * Description:
 *      Creates and returns a new semaphore. The "count" argument specifies
 *      the initial state of the semaphore.
 *      NOTE: Currently this routine only creates counts of 1 or 0
 * Inputs:
 *      sys_mbox_t mbox         -- Handle of mailbox
 *      u8_t count              -- Initial count of semaphore (1 or 0)
 * Outputs:
 *      sys_sem_t               -- Created semaphore or 0 if could not create.
 *---------------------------------------------------------------------------*/
err_t sys_sem_new(sys_sem_t *sem, u8_t count)
{
	err_t lwip_err = ERR_MEM;

	vSemaphoreCreateBinary( (*sem) );

	if( *sem != NULL )
	{
		// Means it can't be taken
		if (count == 0)
		{
			xSemaphoreTake(*sem, 1);
		}

		lwip_err = ERR_OK;

#if SYS_STATS
		SYS_STATS_INC(sem.used);
#endif
	}
	else
	{
#if SYS_STATS
		SYS_STATS_INC(sem.err);
#endif
	}

	return lwip_err;
}

/*---------------------------------------------------------------------------*
 * Routine:  sys_arch_sem_wait
 *---------------------------------------------------------------------------*
 * Description:
 *      Blocks the thread while waiting for the semaphore to be
 *      signaled. If the "timeout" argument is non-zero, the thread should
 *      only be blocked for the specified time (measured in
 *      milliseconds).
 *
 *      If the timeout argument is non-zero, the return value is the number of
 *      milliseconds spent waiting for the semaphore to be signaled. If the
 *      semaphore wasn't signaled within the specified time, the return value is
 *      SYS_ARCH_TIMEOUT. If the thread didn't have to wait for the semaphore
 *      (i.e., it was already signaled), the function may return zero.
 *
 *      Notice that lwIP implements a function with a similar name,
 *      sys_sem_wait(), that uses the sys_arch_sem_wait() function.
 * Inputs:
 *      sys_sem_t sem           -- Semaphore to wait on
 *      u32_t timeout           -- Number of milliseconds until timeout
 * Outputs:
 *      u32_t                   -- Time elapsed or SYS_ARCH_TIMEOUT.
 *---------------------------------------------------------------------------*/
u32_t sys_arch_sem_wait(sys_sem_t *sem, u32_t timeout)
{
portTickType StartTime, EndTime, Elapsed;

	StartTime = xTaskGetTickCount();

	if (timeout != 0)
	{
		if( xSemaphoreTake( *sem, timeout / portTICK_RATE_MS ) == pdTRUE )
		{
			EndTime = xTaskGetTickCount();
			Elapsed = (EndTime - StartTime) * portTICK_RATE_MS;

			return (Elapsed); // return time blocked TODO test
		}
		else
		{
			return SYS_ARCH_TIMEOUT;
		}

	}
	else
	{
		while( xSemaphoreTake( sem, portMAX_DELAY ) != pdTRUE );
		EndTime = xTaskGetTickCount();
		Elapsed = (EndTime - StartTime) * portTICK_RATE_MS;

		if (Elapsed == 0)
		{
			Elapsed = 1;
		}

		// return time blocked
		return (Elapsed);
	}
}

/** Create a new mutex
 * @param mutex pointer to the mutex to create
 * @return a new mutex */
err_t sys_mutex_new(sys_mutex_t *mutex) 
{
err_t lwip_err = ERR_MEM;

	*mutex = xQueueCreateMutex();

	if( *mutex != NULL ) 
	{
		lwip_err = ERR_OK;
#if SYS_STATS
		SYS_STATS_INC(mutex.used);
#endif
	} 
	else 
	{
#if SYS_STATS
		SYS_STATS_INC(mutex.err);
#endif
	}
	
	return lwip_err;
}

/** Lock a mutex
 * @param mutex the mutex to lock */
void sys_mutex_lock(sys_mutex_t *mutex)
{
	while( xSemaphoreTake( *mutex, portMAX_DELAY ) != pdPASS );
}

/** Unlock a mutex
 * @param mutex the mutex to unlock */
void sys_mutex_unlock(sys_mutex_t *mutex)
{
	xSemaphoreGive(*mutex);
}


/** Delete a semaphore
 * @param mutex the mutex to delete */
void sys_mutex_free(sys_mutex_t *mutex)
{
#if SYS_STATS
	SYS_STATS_DEC(mutex.used);
#endif /* SYS_STATS */
	vQueueDelete(*mutex);
}


/*---------------------------------------------------------------------------*
 * Routine:  sys_sem_signal
 *---------------------------------------------------------------------------*
 * Description:
 *      Signals (releases) a semaphore
 * Inputs:
 *      sys_sem_t sem           -- Semaphore to signal
 *---------------------------------------------------------------------------*/
void sys_sem_signal(sys_sem_t * sem)
{
	//LWIP_ASSERT( "sys_sem_signal: sem != SYS_SEM_NULL", sem != SYS_SEM_NULL );
	xSemaphoreGive(*sem);
}

/*---------------------------------------------------------------------------*
 * Routine:  sys_sem_free
 *---------------------------------------------------------------------------*
 * Description:
 *      Deallocates a semaphore
 * Inputs:
 *      sys_sem_t sem           -- Semaphore to free
 *---------------------------------------------------------------------------*/
void sys_sem_free(sys_sem_t * sem)
{
	//LWIP_ASSERT( "sys_sem_free: sem != SYS_SEM_NULL", sem != SYS_SEM_NULL );

#if SYS_STATS
	SYS_STATS_DEC(sem.used);
#endif /* SYS_STATS */

	vQueueDelete(*sem);
}

/*---------------------------------------------------------------------------*
 * Routine:  sys_init
 *---------------------------------------------------------------------------*
 * Description:
 *      Initialize sys arch
 *---------------------------------------------------------------------------*/
void sys_init(void)
{
#if 0
	int i;

	// Initialize the the per-thread sys_timeouts structures
	// make sure there are no valid pids in the list
	for (i = 0; i < SYS_THREAD_MAX; i++)
	{
		s_timeoutlist[i].pid = SYS_THREAD_NULL;
	//	s_timeoutlist[i].timeouts.next = NULL;
	}

	// keep track of how many threads have been created
	s_nextthread = 0;
#endif
}

u32_t sys_now(void)
{
	return xTaskGetTickCount();
}

#if 0
_RB_
u32_t sys_jiffies(void)
{
	return UEZTickCounterGet();
}
#endif

/*---------------------------------------------------------------------------*
 * Routine:  sys_arch_timeouts
 *---------------------------------------------------------------------------*
 * Description:
 *      Returns a pointer to the per-thread sys_timeouts structure. In lwIP,
 *      each thread has a list of timeouts which is represented as a linked
 *      list of sys_timeout structures. The sys_timeouts structure holds a
 *      pointer to a linked list of timeouts. This function is called by
 *      the lwIP timeout scheduler and must not return a NULL value.
 *
 *      In a single threaded sys_arch implementation, this function will
 *      simply return a pointer to a global sys_timeouts variable stored in
 *      the sys_arch module.
 * Outputs:
 *      sys_timeouts *          -- Pointer to per-thread timeouts.
 *---------------------------------------------------------------------------*/
#if 0
struct sys_timeouts *sys_arch_timeouts(void)
{
	int i;
	T_uezTask pid;
	struct timeoutlist *tl;

	pid = UEZTaskGetCurrent();

	for (i = 0; i < s_nextthread; i++)
	{
		tl = &(s_timeoutlist[i]);
		if (tl->pid == pid)
		{
		//	return &(tl->timeouts);
		}
	}

	// Error
	return NULL;
}
#endif
/*---------------------------------------------------------------------------*
 * Routine:  sys_thread_new
 *---------------------------------------------------------------------------*
 * Description:
 *      Starts a new thread with priority "prio" that will begin its
 *      execution in the function "thread()". The "arg" argument will be
 *      passed as an argument to the thread() function. The id of the new
 *      thread is returned. Both the id and the priority are system
 *      dependent.
 * Inputs:
 *      char *name              -- Name of thread
 *      void (* thread)(void *arg) -- Pointer to function to run.
 *      void *arg               -- Argument passed into function
 *      int stacksize           -- Required stack amount in bytes
 *      int prio                -- Thread priority
 * Outputs:
 *      sys_thread_t            -- Pointer to per-thread timeouts.
 *---------------------------------------------------------------------------*/
sys_thread_t sys_thread_new(const char *name, void(* thread)(void *arg), void *arg, int stacksize, int prio)
{
xTaskHandle CreatedTask;
int result;

	result = xTaskCreate( thread, ( signed portCHAR * ) name, stacksize, arg, prio, &CreatedTask );

	if(result == pdPASS)
	{
		return CreatedTask;
	}
	else
	{
		return NULL;
	}
}

/*---------------------------------------------------------------------------*
 * Routine:  sys_arch_protect
 *---------------------------------------------------------------------------*
 * Description:
 *      This optional function does a "fast" critical region protection and
 *      returns the previous protection level. This function is only called
 *      during very short critical regions. An embedded system which supports
 *      ISR-based drivers might want to implement this function by disabling
 *      interrupts. Task-based systems might want to implement this by using
 *      a mutex or disabling tasking. This function should support recursive
 *      calls from the same task or interrupt. In other words,
 *      sys_arch_protect() could be called while already protected. In
 *      that case the return value indicates that it is already protected.
 *
 *      sys_arch_protect() is only required if your port is supporting an
 *      operating system.
 * Outputs:
 *      sys_prot_t              -- Previous protection level (not used here)
 *---------------------------------------------------------------------------*/
sys_prot_t sys_arch_protect(void)
{
	vPortEnterCritical();
	return 1;
}

/*---------------------------------------------------------------------------*
 * Routine:  sys_arch_unprotect
 *---------------------------------------------------------------------------*
 * Description:
 *      This optional function does a "fast" set of critical region
 *      protection to the value specified by pval. See the documentation for
 *      sys_arch_protect() for more information. This function is only
 *      required if your port is supporting an operating system.
 * Inputs:
 *      sys_prot_t              -- Previous protection level (not used here)
 *---------------------------------------------------------------------------*/
void sys_arch_unprotect(sys_prot_t pval)
{
	(void) pval;
	taskEXIT_CRITICAL();
}

/*
 * Prints an assertion messages and aborts execution.
 */
void sys_assert(const char *msg)
{
	(void) msg;

	for (;;)
	{
	}
}
/*-------------------------------------------------------------------------*
 * End of File:  sys_arch.c
 *-------------------------------------------------------------------------*/

