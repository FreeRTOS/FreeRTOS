/*
 * IoT Platform V1.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 */

/**
 * @file iot_threads.h
 * @brief Threading and synchronization functions used by libraries in this SDK.
 */

#ifndef IOT_THREADS_H_
#define IOT_THREADS_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdbool.h>
#include <stdint.h>

/* Platform layer types include. */
#include "types/iot_platform_types.h"

/**
 * @functionspage{platform_threads,platform thread management,Thread Management}
 * - @functionname{platform_threads_function_createdetachedthread}
 * - @functionname{platform_threads_function_mutexcreate}
 * - @functionname{platform_threads_function_mutexdestroy}
 * - @functionname{platform_threads_function_mutexlock}
 * - @functionname{platform_threads_function_mutextrylock}
 * - @functionname{platform_threads_function_mutexunlock}
 * - @functionname{platform_threads_function_semaphorecreate}
 * - @functionname{platform_threads_function_semaphoredestroy}
 * - @functionname{platform_threads_function_semaphoregetcount}
 * - @functionname{platform_threads_function_semaphorewait}
 * - @functionname{platform_threads_function_semaphoretrywait}
 * - @functionname{platform_threads_function_semaphoretimedwait}
 * - @functionname{platform_threads_function_semaphorepost}
 */

/**
 * @functionpage{Iot_CreateDetachedThread,platform_threads,createdetachedthread}
 * @functionpage{IotMutex_Create,platform_threads,mutexcreate}
 * @functionpage{IotMutex_Destroy,platform_threads,mutexdestroy}
 * @functionpage{IotMutex_Lock,platform_threads,mutexlock}
 * @functionpage{IotMutex_TryLock,platform_threads,mutextrylock}
 * @functionpage{IotMutex_Unlock,platform_threads,mutexunlock}
 * @functionpage{IotSemaphore_Create,platform_threads,semaphorecreate}
 * @functionpage{IotSemaphore_Destroy,platform_threads,semaphoredestroy}
 * @functionpage{IotSemaphore_GetCount,platform_threads,semaphoregetcount}
 * @functionpage{IotSemaphore_Wait,platform_threads,semaphorewait}
 * @functionpage{IotSemaphore_TryWait,platform_threads,semaphoretrywait}
 * @functionpage{IotSemaphore_TimedWait,platform_threads,semaphoretimedwait}
 * @functionpage{IotSemaphore_Post,platform_threads,semaphorepost}
 */

/**
 * @brief Create a new detached thread, i.e. a thread that cleans up after itself.
 *
 * This function creates a new thread. Threads created by this function exit
 * upon returning from the thread routine. Any resources taken must be freed
 * by the exiting thread.
 *
 * @param[in] threadRoutine The function this thread should run.
 * @param[in] pArgument The argument passed to `threadRoutine`.
 * @param[in] priority Represents the priority of the new thread, as defined by
 * the system. The value #IOT_THREAD_DEFAULT_PRIORITY (i.e. `0`) must be used to
 * represent the system default for thread priority.
 * @param[in] stackSize Represents the stack size of the new thread, as defined
 * by the system. The value #IOT_THREAD_DEFAULT_STACK_SIZE (i.e. `0`) must be used
 * to represent the system default for stack size.
 *
 * @return `true` if the new thread was successfully created; `false` otherwise.
 *
 * @code{c}
 * // Thread routine.
 * void threadRoutine( void * pArgument );
 *
 * // Run threadRoutine in a detached thread, using default priority and stack size.
 * if( Iot_CreateDetachedThread( threadRoutine,
 *                               NULL,
 *                               IOT_THREAD_DEFAULT_PRIORITY,
 *                               IOT_THREAD_DEFAULT_STACK_SIZE ) == true )
 * {
 *     // Success
 * }
 * else
 * {
 *     // Failure, no thread was created.
 * }
 * @endcode
 */
/* @[declare_platform_threads_createdetachedthread] */
bool Iot_CreateDetachedThread( IotThreadRoutine_t threadRoutine,
                               void * pArgument,
                               int32_t priority,
                               size_t stackSize );
/* @[declare_platform_threads_createdetachedthread] */

/**
 * @brief Create a new mutex.
 *
 * This function creates a new, unlocked mutex. It must be called on an uninitialized
 * #IotMutex_t. This function must not be called on an already-initialized #IotMutex_t.
 *
 * @param[in] pNewMutex Pointer to the memory that will hold the new mutex.
 * @param[in] recursive Set to `true` to create a recursive mutex, i.e. a mutex that
 * may be locked multiple times by the same thread. If the system does not support
 * recursive mutexes, this function should do nothing and return `false`.
 *
 * @return `true` if mutex creation succeeds; `false` otherwise.
 *
 * @see @ref platform_threads_function_mutexdestroy
 *
 * <b>Example</b>
 * @code{c}
 * IotMutex_t mutex;
 *
 * // Create non-recursive mutex.
 * if( IotMutex_Create( &mutex, false ) == true )
 * {
 *     // Lock and unlock the mutex...
 *
 *     // Destroy the mutex when it's no longer needed.
 *     IotMutex_Destroy( &mutex );
 * }
 * @endcode
 */
/* @[declare_platform_threads_mutexcreate] */
bool IotMutex_Create( IotMutex_t * pNewMutex, bool recursive );
/* @[declare_platform_threads_mutexcreate] */

/**
 * @brief Free resources used by a mutex.
 *
 * This function frees resources used by a mutex. It must be called on an initialized
 * #IotMutex_t. No other mutex functions should be called on `pMutex` after calling
 * this function (unless the mutex is re-created).
 *
 * @param[in] pMutex The mutex to destroy.
 *
 * @warning This function must not be called on a locked mutex.
 * @see @ref platform_threads_function_mutexcreate
 */
/* @[declare_platform_threads_mutexdestroy] */
void IotMutex_Destroy( IotMutex_t * pMutex );
/* @[declare_platform_threads_mutexdestroy] */

/**
 * @brief Lock a mutex. This function should only return when the mutex is locked;
 * it is not expected to fail.
 *
 * This function blocks and waits until a mutex is available. It waits forever
 * (deadlocks) if `pMutex` is already locked and never unlocked.
 *
 * @param[in] pMutex The mutex to lock.
 *
 * @see @ref platform_threads_function_mutextrylock for a nonblocking lock.
 */
/* @[declare_platform_threads_mutexlock] */
void IotMutex_Lock( IotMutex_t * pMutex );
/* @[declare_platform_threads_mutexlock] */

/**
 * @brief Attempt to lock a mutex. Return immediately if the mutex is not available.
 *
 * If `pMutex` is available, this function immediately locks it and returns.
 * Otherwise, this function returns without locking `pMutex`.
 *
 * @param[in] pMutex The mutex to lock.
 *
 * @return `true` if the mutex was successfully locked; `false` if the mutex was
 * not available.
 *
 * @see @ref platform_threads_function_mutexlock for a blocking lock.
 */
/* @[declare_platform_threads_mutextrylock] */
bool IotMutex_TryLock( IotMutex_t * pMutex );
/* @[declare_platform_threads_mutextrylock] */

/**
 * @brief Unlock a mutex. This function should only return when the mutex is unlocked;
 * it is not expected to fail.
 *
 * Unlocks a locked mutex. `pMutex` must have been locked by the thread calling
 * this function.
 *
 * @param[in] pMutex The mutex to unlock.
 *
 * @note This function should not be called on a mutex that is already unlocked.
 */
/* @[declare_platform_threads_mutexunlock] */
void IotMutex_Unlock( IotMutex_t * pMutex );
/* @[declare_platform_threads_mutexunlock] */

/**
 * @brief Create a new counting semaphore.
 *
 * This function creates a new counting semaphore with a given initial and
 * maximum value. It must be called on an uninitialized #IotSemaphore_t.
 * This function must not be called on an already-initialized #IotSemaphore_t.
 *
 * @param[in] pNewSemaphore Pointer to the memory that will hold the new semaphore.
 * @param[in] initialValue The semaphore should be initialized with this value.
 * @param[in] maxValue The maximum value the semaphore will reach.
 *
 * @return `true` if semaphore creation succeeds; `false` otherwise.
 *
 * @see @ref platform_threads_function_semaphoredestroy
 *
 * <b>Example</b>
 * @code{c}
 * IotSemaphore_t sem;
 *
 * // Create a locked binary semaphore.
 * if( IotSemaphore_Create( &sem, 0, 1 ) == true )
 * {
 *     // Unlock the semaphore.
 *     IotSemaphore_Post( &sem );
 *
 *     // Destroy the semaphore when it's no longer needed.
 *     IotSemaphore_Destroy( &sem );
 * }
 * @endcode
 */
/* @[declare_platform_threads_semaphorecreate] */
bool IotSemaphore_Create( IotSemaphore_t * pNewSemaphore,
                          uint32_t initialValue,
                          uint32_t maxValue );
/* @[declare_platform_threads_semaphorecreate] */

/**
 * @brief Free resources used by a semaphore.
 *
 * This function frees resources used by a semaphore. It must be called on an initialized
 * #IotSemaphore_t. No other semaphore functions should be called on `pSemaphore` after
 * calling this function (unless the semaphore is re-created).
 *
 * @param[in] pSemaphore The semaphore to destroy.
 *
 * @warning This function must not be called on a semaphore with waiting threads.
 * @see @ref platform_threads_function_semaphorecreate
 */
/* @[declare_platform_threads_semaphoredestroy] */
void IotSemaphore_Destroy( IotSemaphore_t * pSemaphore );
/* @[declare_platform_threads_semaphoredestroy] */

/**
 * @brief Query the current count of the semaphore.
 *
 * This function queries a counting semaphore for its current value. A counting
 * semaphore's value is always 0 or positive.
 *
 * @param[in] pSemaphore The semaphore to query.
 *
 * @return The current count of the semaphore. This function should not fail.
 */
/* @[declare_platform_threads_semaphoregetcount] */
uint32_t IotSemaphore_GetCount( IotSemaphore_t * pSemaphore );
/* @[declare_platform_threads_semaphoregetcount] */

/**
 * @brief Wait on (lock) a semaphore. This function should only return when the
 * semaphore wait succeeds; it is not expected to fail.
 *
 * This function blocks and waits until a counting semaphore is positive. It
 * waits forever (deadlocks) if `pSemaphore` has a count `0` that is never
 * [incremented](@ref platform_threads_function_semaphorepost).
 *
 * @param[in] pSemaphore The semaphore to lock.
 *
 * @see @ref platform_threads_function_semaphoretrywait for a nonblocking wait;
 * @ref platform_threads_function_semaphoretimedwait for a wait with timeout.
 */
/* @[declare_platform_threads_semaphorewait] */
void IotSemaphore_Wait( IotSemaphore_t * pSemaphore );
/* @[declare_platform_threads_semaphorewait] */

/**
 * @brief Attempt to wait on (lock) a semaphore. Return immediately if the semaphore
 * is not available.
 *
 * If the count of `pSemaphore` is positive, this function immediately decrements
 * the semaphore and returns. Otherwise, this function returns without decrementing
 * `pSemaphore`.
 *
 * @param[in] pSemaphore The semaphore to lock.
 *
 * @return `true` if the semaphore wait succeeded; `false` if the semaphore has
 * a count of `0`.
 *
 * @see @ref platform_threads_function_semaphorewait for a blocking wait;
 * @ref platform_threads_function_semaphoretimedwait for a wait with timeout.
 */
/* @[declare_platform_threads_semaphoretrywait] */
bool IotSemaphore_TryWait( IotSemaphore_t * pSemaphore );
/* @[declare_platform_threads_semaphoretrywait] */

/**
 * @brief Attempt to wait on (lock) a semaphore with a timeout.
 *
 * This function blocks and waits until a counting semaphore is positive
 * <i>or</i> its timeout expires (whichever is sooner). It decrements
 * `pSemaphore` and returns `true` if the semaphore is positive at some
 * time during the wait. If `pSemaphore` is always `0` during the wait,
 * this function returns `false`.
 *
 * @param[in] pSemaphore The semaphore to lock.
 * @param[in] timeoutMs Relative timeout of semaphore lock. This function returns
 * false if the semaphore couldn't be locked within this timeout.
 *
 * @return `true` if the semaphore wait succeeded; `false` if it timed out.
 *
 * @see @ref platform_threads_function_semaphoretrywait for a nonblocking wait;
 * @ref platform_threads_function_semaphorewait for a blocking wait.
 */
/* @[declare_platform_threads_semaphoretimedwait] */
bool IotSemaphore_TimedWait( IotSemaphore_t * pSemaphore,
                             uint32_t timeoutMs );
/* @[declare_platform_threads_semaphoretimedwait] */

/**
 * @brief Post to (unlock) a semaphore. This function should only return when the
 * semaphore post succeeds; it is not expected to fail.
 *
 * This function increments the count of a semaphore. Any thread may call this
 * function to increment a semaphore's count.
 *
 * @param[in] pSemaphore The semaphore to unlock.
 */
/* @[declare_platform_threads_semaphorepost] */
void IotSemaphore_Post( IotSemaphore_t * pSemaphore );
/* @[declare_platform_threads_semaphorepost] */

#endif /* ifndef IOT_THREADS_H_ */
