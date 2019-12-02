/*
 * Amazon FreeRTOS POSIX V1.1.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file pthread.h
 * @brief Threads.
 *
 * http://pubs.opengroup.org/onlinepubs/9699919799/basedefs/pthread.h.html
 */

#ifndef _FREERTOS_POSIX_PTHREAD_H_
#define _FREERTOS_POSIX_PTHREAD_H_

/* FreeRTOS+POSIX includes. POSIX states that this header shall make symbols
 * defined in sched.h and time.h visible. */
#include "FreeRTOS_POSIX/sched.h"
#include "FreeRTOS_POSIX/time.h"

/**
 * @name pthread detach state.
 */
/**@{ */
#define PTHREAD_CREATE_DETACHED    0       /**< Detached. */
#define PTHREAD_CREATE_JOINABLE    1       /**< Joinable (default). */
/**@} */

/**
 * @name Returned to a single thread after a successful pthread_barrier_wait.
 *
 * @brief POSIX specifies that "The constant PTHREAD_BARRIER_SERIAL_THREAD is defined in
 * <pthread.h> and its value shall be distinct from any other value returned by pthread_barrier_wait()."
 * So it's defined as negative to distinguish it from the errnos, which are positive.
 */
#define PTHREAD_BARRIER_SERIAL_THREAD    ( -2 )

/**
 * @name Mutex types.
 */
/**@{ */
#ifndef PTHREAD_MUTEX_NORMAL
    #define PTHREAD_MUTEX_NORMAL        0                        /**< Non-robust, deadlock on relock, does not remember owner. */
#endif
#ifndef PTHREAD_MUTEX_ERRORCHECK
    #define PTHREAD_MUTEX_ERRORCHECK    1                        /**< Non-robust, error on relock,  remembers owner. */
#endif
#ifndef PTHREAD_MUTEX_RECURSIVE
    #define PTHREAD_MUTEX_RECURSIVE     2                        /**< Non-robust, recursive relock, remembers owner. */
#endif
#ifndef PTHREAD_MUTEX_DEFAULT
    #define PTHREAD_MUTEX_DEFAULT       PTHREAD_MUTEX_NORMAL     /**< PTHREAD_MUTEX_NORMAL (default). */
#endif
/**@} */

/**
 * @name Compile-time initializers.
 *
 * @brief To use PTHREAD_COND_INITIALIZER, posixconfigENABLE_PTHREAD_COND_T needs to be set to 1
 * in port specific POSIX config file.
 *
 * To use PTHREAD_MUTEX_INITIALIZER, posixconfigENABLE_PTHREAD_MUTEX_T needs to be set to 1 in
 * port specific POSIX config file.
 */
/**@{ */
#if posixconfigENABLE_PTHREAD_COND_T == 1
    #define PTHREAD_COND_INITIALIZER    FREERTOS_POSIX_COND_INITIALIZER       /**< pthread_cond_t. */
#endif

#if posixconfigENABLE_PTHREAD_MUTEX_T == 1
    #define PTHREAD_MUTEX_INITIALIZER    FREERTOS_POSIX_MUTEX_INITIALIZER /**< pthread_mutex_t. */
#endif

/**@} */

/**
 * @brief Destroy the thread attributes object.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_attr_destroy.html
 *
 * @retval 0 - Upon successful completion.
 */
int pthread_attr_destroy( pthread_attr_t * attr );

/**
 * @brief Get detachstate attribute.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_attr_getdetachstate.html
 *
 * @retval 0 - Upon successful completion.
 */
int pthread_attr_getdetachstate( const pthread_attr_t * attr,
                                 int * detachstate );

/**
 * @brief Get schedparam attribute.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_attr_getschedparam.html
 *
 * @retval 0 - Upon successful completion.
 */
int pthread_attr_getschedparam( const pthread_attr_t * attr,
                                struct sched_param * param );

/**
 * @brief Get stacksize attribute.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_attr_getstacksize.html
 *
 * @retval 0 - Upon successful completion.
 */
int pthread_attr_getstacksize( const pthread_attr_t * attr,
                               size_t * stacksize );

/**
 * @brief Initialize the thread attributes object.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_attr_init.html
 *
 * @retval 0 - Upon successful completion.
 *
 * @note Currently, only stack size, sched_param, and detach state attributes
 * are supported. Also see pthread_attr_get*() and pthread_attr_set*().
 */
int pthread_attr_init( pthread_attr_t * attr );

/**
 * @brief Set detachstate attribute.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_attr_setdetachstate.html
 *
 * @retval 0 - Upon successful completion
 * @retval EINVAL - The value of detachstate is not valid. Currently, supported detach states are --
 *                  PTHREAD_CREATE_DETACHED and PTHREAD_CREATE_JOINABLE.
 */
int pthread_attr_setdetachstate( pthread_attr_t * attr,
                                 int detachstate );

/**
 * @brief Set schedparam attribute.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_attr_setschedparam.html
 *
 * @retval 0 - Upon successful completion.
 * @retval EINVAL - The value of param is not valid.
 * @retval ENOTSUP - An attempt was made to set the attribute to an unsupported value.
 */
int pthread_attr_setschedparam( pthread_attr_t * attr,
                                const struct sched_param * param );

/**
 * @brief Set the schedpolicy attribute.
 *
 * http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_attr_setschedpolicy.html
 *
 * @retval 0 - Upon successful completion.
 *
 * @warning This function is a stub and always returns 0.
 */
int pthread_attr_setschedpolicy( pthread_attr_t * attr,
                                 int policy );

/**
 * @brief Set stacksize attribute.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_attr_setstacksize.html
 *
 * @retval 0 - Upon successful completion.
 * @retval EINVAL - The value of stacksize is less than {PTHREAD_STACK_MIN}.
 */
int pthread_attr_setstacksize( pthread_attr_t * attr,
                               size_t stacksize );

/**
 * @brief Destroy a barrier object.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_barrier_destroy.html
 *
 * @retval 0 - Upon successful completion.
 *
 * @note This function does not validate whether there is any thread blocking on the barrier before destroying.
 */
int pthread_barrier_destroy( pthread_barrier_t * barrier );

/**
 * @brief Initialize a barrier object.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_barrier_init.html
 *
 * @retval 0 - Upon successful completion.
 * @retval EINVAL - The value specified by count is equal to zero.
 * @retval ENOMEM - count cannot fit into FreeRTOS event group type OR insufficient memory exists to initialize the barrier.
 *
 * @note attr is ignored.
 *
 * @note pthread_barrier_init() is implemented with FreeRTOS event group.
 * To ensure count fits in event group, count may be at most 8 when configUSE_16_BIT_TICKS is 1;
 * it may be at most 24 otherwise. configUSE_16_BIT_TICKS is configured in application FreeRTOSConfig.h
 * file, which defines how many bits tick count type has. See further details and limitation about event
 * group and configUSE_16_BIT_TICKS in FreeRTOS site.
 */
int pthread_barrier_init( pthread_barrier_t * barrier,
                          const pthread_barrierattr_t * attr,
                          unsigned count );

/**
 * @brief Synchronize at a barrier.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_barrier_wait.html
 *
 * @retval PTHREAD_BARRIER_SERIAL_THREAD - Upon successful completion, the first thread.
 * @retval 0 - Upon successful completion, other thread(s).
 */
int pthread_barrier_wait( pthread_barrier_t * barrier );

/**
 * @brief Thread creation.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_create.html
 *
 * @retval 0 - Upon successful completion.
 * @retval EAGAIN - Insufficient memory for either thread structure or task creation.
 */
int pthread_create( pthread_t * thread,
                    const pthread_attr_t * attr,
                    void *( *startroutine )( void * ),
                    void * arg );

/**
 * @brief Broadcast a condition.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_cond_broadcast.html
 *
 * @retval 0 - Upon successful completion.
 */
int pthread_cond_broadcast( pthread_cond_t * cond );

/**
 * @brief Destroy condition variables.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_cond_destroy.html
 *
 * @retval 0 - Upon successful completion.
 */
int pthread_cond_destroy( pthread_cond_t * cond );

/**
 * @brief Initialize condition variables.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_cond_init.html
 *
 * @retval 0 - Upon successful completion.
 * @retval ENOMEM - Insufficient memory exists to initialize the condition variable.
 *
 * @note attr is ignored and treated as NULL. Default setting is always used.
 */
int pthread_cond_init( pthread_cond_t * cond,
                       const pthread_condattr_t * attr );

/**
 * @brief Signal a condition.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_cond_signal.html
 *
 * @retval 0 - Upon successful completion.
 */
int pthread_cond_signal( pthread_cond_t * cond );

/**
 * @brief Wait on a condition with a timeout.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_cond_timedwait.html
 *
 * @retval 0 - Upon successful completion.
 * @retval EINVAL - The abstime argument passed in does not refer to an initialized structure OR
 *                  the abstime parameter specified a nanoseconds field value less than zero or
 *                  greater than or equal to 1000 million.
 * @retval ETIMEDOUT - The time specified by abstime to pthread_cond_timedwait() has passed.
 */
int pthread_cond_timedwait( pthread_cond_t * cond,
                            pthread_mutex_t * mutex,
                            const struct timespec * abstime );

/**
 * @brief Wait on a condition.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_cond_wait.html
 *
 * @retval 0 - Upon successful completion.
 */
int pthread_cond_wait( pthread_cond_t * cond,
                       pthread_mutex_t * mutex );

/**
 * @brief Compare thread IDs.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_equal.html
 *
 * @retval 0 - t1 and t2 are both not NULL && equal.
 * @retval non-zero - otherwise.
 */
int pthread_equal( pthread_t t1,
                   pthread_t t2 );

/**
 * @brief Thread termination.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_exit.html
 *
 * @retval void - this function cannot return to its caller.
 */
void pthread_exit( void * value_ptr );

/**
 * @brief Dynamic thread scheduling parameters access.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_getschedparam.html
 *
 * @retval 0 - Upon successful completion.
 *
 * @note policy is always set to SCHED_OTHER by this function.
 */
int pthread_getschedparam( pthread_t thread,
                           int * policy,
                           struct sched_param * param );

/**
 * @brief Wait for thread termination.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_join.html
 *
 * @retval 0 - Upon successful completion.
 * @retval EDEADLK - The value specified by the thread argument to pthread_join() does not refer
 *                   to a joinable thread OR multiple simultaneous calls to pthread_join()
 *                   specifying the same target thread OR the value specified by the thread argument
 *                   to pthread_join() refers to the calling thread.
 */
int pthread_join( pthread_t thread,
                  void ** retval );

/**
 * @brief Destroy a mutex.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_mutex_destroy.html
 *
 * @retval 0 - Upon successful completion.
 *
 * @note If there exists a thread holding this mutex, this function returns 0 with mutex not being destroyed.
 */
int pthread_mutex_destroy( pthread_mutex_t * mutex );

/**
 * @brief Initialize a mutex.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_mutex_init.html
 *
 * @retval 0 - Upon successful completion.
 * @retval ENOMEM - Insufficient memory exists to initialize the mutex structure.
 * @retval EAGAIN - Unable to initialize the mutex structure member(s).
 */
int pthread_mutex_init( pthread_mutex_t * mutex,
                        const pthread_mutexattr_t * attr );

/**
 * @brief Lock a mutex.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_mutex_lock.html
 *
 * @retval 0 - Upon successful completion.
 * @retval EINVAL - the abstime parameter specified a nanoseconds field value less than zero
 *                  or greater than or equal to 1000 million.
 * @retval EDEADLK - The mutex type is PTHREAD_MUTEX_ERRORCHECK and the current thread already
 *                   owns the mutex.
 */
int pthread_mutex_lock( pthread_mutex_t * mutex );

/**
 * @brief Lock a mutex with timeout.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_mutex_timedlock.html
 *
 * @retval 0 - Upon successful completion.
 * @retval EINVAL - The abstime argument passed in does not refer to an initialized structure OR
 *                  the abstime parameter specified a nanoseconds field value less than zero or
 *                  greater than or equal to 1000 million.
 * @retval EDEADLK - The mutex type is PTHREAD_MUTEX_ERRORCHECK and the current thread already owns the mutex.
 * @retval ETIMEDOUT - The mutex could not be locked before the specified timeout expired.
 */
int pthread_mutex_timedlock( pthread_mutex_t * mutex,
                             const struct timespec * abstime );

/**
 * @brief Attempt to lock a mutex. Fail immediately if mutex is already locked.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_mutex_trylock.html
 *
 * @retval 0 - Upon successful completion.
 * @retval EINVAL - the abstime parameter specified a nanoseconds field value less than zero
 *                  or greater than or equal to 1000 million.
 * @retval EDEADLK - The mutex type is PTHREAD_MUTEX_ERRORCHECK and the current thread already
 *                   owns the mutex.
 * @retval EBUSY - The mutex could not be acquired because it was already locked.
 */
int pthread_mutex_trylock( pthread_mutex_t * mutex );

/**
 * @brief Unlock a mutex.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_mutex_unlock.html
 *
 * @retval 0 - Upon successful completion.
 * @retval EPERM - The mutex type is PTHREAD_MUTEX_ERRORCHECK or PTHREAD_MUTEX_RECURSIVE, and
 *                 the current thread does not own the mutex.
 */
int pthread_mutex_unlock( pthread_mutex_t * mutex );

/**
 * @brief Destroy the mutex attributes object.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_mutexattr_destroy.html
 *
 * @retval 0 - Upon successful completion.
 */
int pthread_mutexattr_destroy( pthread_mutexattr_t * attr );

/**
 * @brief Get the mutex type attribute.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_mutexattr_gettype.html
 *
 * @retval 0 - Upon successful completion.
 */
int pthread_mutexattr_gettype( const pthread_mutexattr_t * attr,
                               int * type );

/**
 * @brief Initialize the mutex attributes object.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_mutexattr_init.html
 *
 * @retval 0 - Upon successful completion.
 *
 * @note Currently, only the type attribute is supported. Also see pthread_mutexattr_settype()
 *       and pthread_mutexattr_gettype().
 */
int pthread_mutexattr_init( pthread_mutexattr_t * attr );

/**
 * @brief Set the mutex type attribute.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_mutexattr_settype.html
 *
 * @retval 0 - Upon successful completion.
 * @retval EINVAL - The value type is invalid.
 */
int pthread_mutexattr_settype( pthread_mutexattr_t * attr,
                               int type );

/**
 * @brief Get the calling thread ID.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_self.html
 *
 * @retval the thread ID of the calling thread.
 */
pthread_t pthread_self( void );

/**
 * @brief Dynamic thread scheduling parameters access.
 *
 * @see http://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_setschedparam.html
 *
 * @note policy is ignored; only priority (param.sched_priority) may be changed.
 *
 * @retval 0 - Upon successful completion.
 */
int pthread_setschedparam( pthread_t thread,
                           int policy,
                           const struct sched_param * param );

#endif /* _FREERTOS_POSIX_PTHREAD_H_ */
