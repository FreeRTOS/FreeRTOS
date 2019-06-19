/*
 * Amazon FreeRTOS Common V1.0.0
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
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file iot_static_memory.h
 * @brief Common functions for managing static buffers. Only used when
 * @ref IOT_STATIC_MEMORY_ONLY is `1`.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* The functions in this file should only exist in static memory only mode, hence
 * the check for IOT_STATIC_MEMORY_ONLY in the double inclusion guard. */
#if !defined( IOT_STATIC_MEMORY_H_ ) && ( IOT_STATIC_MEMORY_ONLY == 1 )
#define IOT_STATIC_MEMORY_H_

/* Standard includes. */
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/**
 * @functionspage{static_memory,static memory component}
 * - @functionname{static_memory_function_init}
 * - @functionname{static_memory_function_cleanup}
 * - @functionname{static_memory_function_findfree}
 * - @functionname{static_memory_function_returninuse}
 * - @functionname{static_memory_function_messagebuffersize}
 * - @functionname{static_memory_function_mallocmessagebuffer}
 * - @functionname{static_memory_function_freemessagebuffer}
 */

/*----------------------- Initialization and cleanup ------------------------*/

/**
 * @functionpage{IotStaticMemory_Init,static_memory,init}
 * @functionpage{IotStaticMemory_Cleanup,static_memory,cleanup}
 */

/**
 * @brief One-time initialization function for static memory.
 *
 * This function performs internal setup of static memory. <b>It must be called
 * once (and only once) before calling any other static memory function.</b>
 * Calling this function more than once without first calling
 * @ref static_memory_function_cleanup may result in a crash.
 *
 * @return `true` if initialization succeeded; `false` otherwise.
 *
 * @attention This function is called by `IotSdk_Init` and does not need to be
 * called by itself.
 *
 * @warning No thread-safety guarantees are provided for this function.
 *
 * @see static_memory_function_cleanup
 */
/* @[declare_static_memory_init] */
bool IotStaticMemory_Init( void );
/* @[declare_static_memory_init] */

/**
 * @brief One-time deinitialization function for static memory.
 *
 * This function frees resources taken in @ref static_memory_function_init.
 * It should be called after to clean up static memory. After this function
 * returns, @ref static_memory_function_init must be called again before
 * calling any other static memory function.
 *
 * @attention This function is called by `IotSdk_Cleanup` and does not need
 * to be called by itself.
 *
 * @warning No thread-safety guarantees are provided for this function.
 *
 * @see static_memory_function_init
 */
/* @[declare_static_memory_cleanup] */
void IotStaticMemory_Cleanup( void );
/* @[declare_static_memory_cleanup] */

/*------------------------- Buffer allocation and free ----------------------*/

/**
 * @functionpage{IotStaticMemory_FindFree,static_memory,findfree}
 * @functionpage{IotStaticMemory_ReturnInUse,static_memory,returninuse}
 */

/**
 * @brief Find a free buffer using the "in-use" flags.
 *
 * If a free buffer is found, this function marks the buffer in-use. This function
 * is common to the static memory implementation.
 *
 * @param[in] pInUse The "in-use" flags to search.
 * @param[in] limit How many flags to check, i.e. the size of `pInUse`.
 *
 * @return The index of a free buffer; `-1` if no free buffers are available.
 *
 * <b>Example</b>:
 * @code{c}
 * // To use this function, first declare two arrays. One provides the statically-allocated
 * // objects, the other provides flags to determine which objects are in-use.
 * #define NUMBER_OF_OBJECTS    ...
 * #define OBJECT_SIZE          ...
 * static bool _pInUseObjects[ NUMBER_OF_OBJECTS ] = { 0 };
 * static uint8_t _pObjects[ NUMBER_OF_OBJECTS ][ OBJECT_SIZE ] = { { 0 } }; // Placeholder for objects.
 *
 * // The function to statically allocate objects. Must have the same signature
 * // as malloc().
 * void * Iot_MallocObject( size_t size )
 * {
 *     int32_t freeIndex = -1;
 *     void * pNewObject = NULL;
 *
 *     // Check that sizes match. 
 *     if( size != OBJECT_SIZE )
 *     {
 *         // Get the index of a free object.
 *         freeIndex = IotStaticMemory_FindFree( _pInUseMessageBuffers,
 *                                               IOT_MESSAGE_BUFFERS );
 *
 *         if( freeIndex != -1 )
 *         {
 *             pNewBuffer = &( _pMessageBuffers[ freeIndex ][ 0 ] );
 *         }
 *     }
 *
 *     return pNewBuffer;
 * }
 * @endcode
 */
/* @[declare_static_memory_findfree] */
int32_t IotStaticMemory_FindFree( bool * pInUse,
                                  size_t limit );
/* @[declare_static_memory_findfree] */

/**
 * @brief Return an "in-use" buffer.
 *
 * This function is common to the static memory implementation.
 *
 * @param[in] ptr Pointer to the buffer to return.
 * @param[in] pPool The pool of buffers that the in-use buffer was allocated from.
 * @param[in] pInUse The "in-use" flags for pPool.
 * @param[in] limit How many buffers (and flags) to check while searching for ptr.
 * @param[in] elementSize The size of a single element in pPool.
 *
 * <b>Example</b>:
 * @code{c}
 * // To use this function, first declare two arrays. One provides the statically-allocated
 * // objects, the other provides flags to determine which objects are in-use.
 * #define NUMBER_OF_OBJECTS    ...
 * #define OBJECT_SIZE          ...
 * static bool _pInUseObjects[ NUMBER_OF_OBJECTS ] = { 0 };
 * static uint8_t _pObjects[ NUMBER_OF_OBJECTS ][ OBJECT_SIZE ] = { { 0 } }; // Placeholder for objects.
 *
 * // The function to free statically-allocated objects. Must have the same signature
 * // as free().
 * void Iot_FreeObject( void * ptr )
 * {
 *     IotStaticMemory_ReturnInUse( ptr,
 *                                 _pObjects,
 *                                 _pInUseObjects,
 *                                 NUMBER_OF_OBJECTS,
 *                                 OBJECT_SIZE );
 * }
 * @endcode
 */
/* @[declare_static_memory_returninuse] */
void IotStaticMemory_ReturnInUse( void * ptr,
                                  void * pPool,
                                  bool * pInUse,
                                  size_t limit,
                                  size_t elementSize );
/* @[declare_static_memory_returninuse] */

/*------------------------ Message buffer management ------------------------*/

/**
 * @functionpage{Iot_MessageBufferSize,static_memory,messagebuffersize}
 * @functionpage{Iot_MallocMessageBuffer,static_memory,mallocmessagebuffer}
 * @functionpage{Iot_FreeMessageBuffer,static_memory,freemessagebuffer}
 */

/**
 * @brief Get the fixed size of a message buffer.
 *
 * The size of the message buffers are known at compile time, but it is a [constant]
 * (@ref IOT_MESSAGE_BUFFER_SIZE) that may not be visible to all source files.
 * This function allows other source files to know the size of a message buffer.
 *
 * @return The size, in bytes, of a single message buffer.
 */
/* @[declare_static_memory_messagebuffersize] */
size_t Iot_MessageBufferSize( void );
/* @[declare_static_memory_messagebuffersize] */

/**
 * @brief Get an empty message buffer.
 *
 * This function is the analog of [malloc]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html)
 * for message buffers.
 *
 * @param[in] size Requested size for a message buffer.
 *
 * @return Pointer to the start of a message buffer. If the `size` argument is larger
 * than the [fixed size of a message buffer](@ref IOT_MESSAGE_BUFFER_SIZE)
 * or no message buffers are available, `NULL` is returned.
 */
/* @[declare_static_memory_mallocmessagebuffer] */
void * Iot_MallocMessageBuffer( size_t size );
/* @[declare_static_memory_mallocmessagebuffer] */

/**
 * @brief Free an in-use message buffer.
 *
 * This function is the analog of [free]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html)
 * for message buffers.
 *
 * @param[in] ptr Pointer to the message buffer to free.
 */
/* @[declare_static_memory_freemessagebuffer] */
void Iot_FreeMessageBuffer( void * ptr );
/* @[declare_static_memory_freemessagebuffer] */
 
#endif /* if !defined( IOT_STATIC_MEMORY_H_ ) && ( IOT_STATIC_MEMORY_ONLY == 1 ) */
