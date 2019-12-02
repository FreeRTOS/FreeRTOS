/*
 * AWS IoT Shadow V2.1.0
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
 * @file aws_iot_shadow_static_memory.c
 * @brief Implementation of Shadow static memory functions.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* This file should only be compiled if dynamic memory allocation is forbidden. */
#if IOT_STATIC_MEMORY_ONLY == 1

/* Standard includes. */
#include <stdbool.h>
#include <stddef.h>
#include <string.h>

/* Static memory include. */
#include "iot_static_memory.h"

/* Shadow internal include. */
#include "private/aws_iot_shadow_internal.h"

/*-----------------------------------------------------------*/

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Provide default values for undefined configuration constants.
 */
#ifndef AWS_IOT_SHADOW_MAX_IN_PROGRESS_OPERATIONS
    #define AWS_IOT_SHADOW_MAX_IN_PROGRESS_OPERATIONS    ( 10 )
#endif
#ifndef AWS_IOT_SHADOW_SUBSCRIPTIONS
    #define AWS_IOT_SHADOW_SUBSCRIPTIONS                 ( 2 )
#endif
/** @endcond */

/* Validate static memory configuration settings. */
#if AWS_IOT_SHADOW_MAX_IN_PROGRESS_OPERATIONS <= 0
    #error "AWS_IOT_SHADOW_MAX_IN_PROGRESS_OPERATIONS cannot be 0 or negative."
#endif
#if AWS_IOT_SHADOW_SUBSCRIPTIONS <= 0
    #error "AWS_IOT_SHADOW_SUBSCRIPTIONS cannot be 0 or negative."
#endif

/**
 * @brief The size of a static memory Shadow subscription.
 *
 * Since the pThingName member of #_shadowSubscription_t is variable-length,
 * the constant `AWS_IOT_MAX_THING_NAME_LENGTH` is used for the length of
 * #_shadowSubscription_t.pThingName.
 */
#define SHADOW_SUBSCRIPTION_SIZE    ( sizeof( _shadowSubscription_t ) + AWS_IOT_MAX_THING_NAME_LENGTH )

/*-----------------------------------------------------------*/

/*
 * Static memory buffers and flags, allocated and zeroed at compile-time.
 */
static uint32_t _pInUseShadowOperations[ AWS_IOT_SHADOW_MAX_IN_PROGRESS_OPERATIONS ] = { 0U };                     /**< @brief Shadow operation in-use flags. */
static _shadowOperation_t _pShadowOperations[ AWS_IOT_SHADOW_MAX_IN_PROGRESS_OPERATIONS ] = { { .link = { 0 } } }; /**< @brief Shadow operations. */

static uint32_t _pInUseShadowSubscriptions[ AWS_IOT_SHADOW_SUBSCRIPTIONS ] = { 0U };                        /**< @brief Shadow subscription in-use flags. */
static char _pShadowSubscriptions[ AWS_IOT_SHADOW_SUBSCRIPTIONS ][ SHADOW_SUBSCRIPTION_SIZE ] = { { 0 } };  /**< @brief Shadow subscriptions. */

/*-----------------------------------------------------------*/

void * AwsIotShadow_MallocOperation( size_t size )
{
    int32_t freeIndex = -1;
    void * pNewOperation = NULL;

    /* Check size argument. */
    if( size == sizeof( _shadowOperation_t ) )
    {
        /* Find a free Shadow operation. */
        freeIndex = IotStaticMemory_FindFree( _pInUseShadowOperations,
                                              AWS_IOT_SHADOW_MAX_IN_PROGRESS_OPERATIONS );

        if( freeIndex != -1 )
        {
            pNewOperation = &( _pShadowOperations[ freeIndex ] );
        }
    }

    return pNewOperation;
}

/*-----------------------------------------------------------*/

void AwsIotShadow_FreeOperation( void * ptr )
{
    /* Return the in-use Shadow operation. */
    IotStaticMemory_ReturnInUse( ptr,
                                 _pShadowOperations,
                                 _pInUseShadowOperations,
                                 AWS_IOT_SHADOW_MAX_IN_PROGRESS_OPERATIONS,
                                 sizeof( _shadowOperation_t ) );
}

/*-----------------------------------------------------------*/

void * AwsIotShadow_MallocSubscription( size_t size )
{
    int32_t freeIndex = -1;
    void * pNewSubscription = NULL;

    if( size <= SHADOW_SUBSCRIPTION_SIZE )
    {
        /* Get the index of a free Shadow subscription. */
        freeIndex = IotStaticMemory_FindFree( _pInUseShadowSubscriptions,
                                              AWS_IOT_SHADOW_SUBSCRIPTIONS );

        if( freeIndex != -1 )
        {
            pNewSubscription = &( _pShadowSubscriptions[ freeIndex ][ 0 ] );
        }
    }

    return pNewSubscription;
}

/*-----------------------------------------------------------*/

void AwsIotShadow_FreeSubscription( void * ptr )
{
    /* Return the in-use Shadow subscription. */
    IotStaticMemory_ReturnInUse( ptr,
                                 _pShadowSubscriptions,
                                 _pInUseShadowSubscriptions,
                                 AWS_IOT_SHADOW_SUBSCRIPTIONS,
                                 SHADOW_SUBSCRIPTION_SIZE );
}

/*-----------------------------------------------------------*/

#endif
