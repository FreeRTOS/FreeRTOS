/*
 * AWS IoT Jobs V1.0.0
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
 */

/**
 * @file aws_iot_jobs_static_memory.c
 * @brief Implementation of Jobs static memory functions.
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

/* Jobs internal include. */
#include "private/aws_iot_jobs_internal.h"

/*-----------------------------------------------------------*/

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Provide default values for undefined configuration constants.
 */
#ifndef AWS_IOT_JOBS_MAX_IN_PROGRESS_OPERATIONS
    #define AWS_IOT_JOBS_MAX_IN_PROGRESS_OPERATIONS    ( 10 )
#endif
#ifndef AWS_IOT_JOBS_SUBSCRIPTIONS
    #define AWS_IOT_JOBS_SUBSCRIPTIONS                 ( 2 )
#endif
/** @endcond */

/* Validate static memory configuration settings. */
#if AWS_IOT_JOBS_MAX_IN_PROGRESS_OPERATIONS <= 0
    #error "AWS_IOT_JOBS_MAX_IN_PROGRESS_OPERATIONS cannot be 0 or negative."
#endif
#if AWS_IOT_JOBS_SUBSCRIPTIONS <= 0
    #error "AWS_IOT_JOBS_SUBSCRIPTIONS cannot be 0 or negative."
#endif

/**
 * @brief The size of a static memory Jobs operation.
 *
 * Since the pJobId member of #_jobsOperation_t is variable-length,
 * the constant `JOBS_MAX_ID_LENGTH` is used for the length of
 * #_jobsOperation_t.pJobId.
 */
#define JOBS_OPERATION_SIZE    ( sizeof( _jobsOperation_t ) + JOBS_MAX_ID_LENGTH )

/**
 * @brief The size of a static memory Jobs subscription.
 *
 * Since the pThingName member of #_jobsSubscription_t is variable-length,
 * the constant `AWS_IOT_MAX_THING_NAME_LENGTH` is used for the length of
 * #_jobsSubscription_t.pThingName.
 */
#define JOBS_SUBSCRIPTION_SIZE    ( sizeof( _jobsSubscription_t ) + AWS_IOT_MAX_THING_NAME_LENGTH )

/*-----------------------------------------------------------*/

/*
 * Static memory buffers and flags, allocated and zeroed at compile-time.
 */
static uint32_t _pInUseJobsOperations[ AWS_IOT_JOBS_MAX_IN_PROGRESS_OPERATIONS ] = { 0U };                   /**< @brief Jobs operation in-use flags. */
static char _pJobsOperations[ AWS_IOT_JOBS_MAX_IN_PROGRESS_OPERATIONS ][ JOBS_OPERATION_SIZE ] = { { 0 } }; /**< @brief Jobs operations. */

static uint32_t _pInUseJobsSubscriptions[ AWS_IOT_JOBS_SUBSCRIPTIONS ] = { 0U };                             /**< @brief Jobs subscription in-use flags. */
static char _pJobsSubscriptions[ AWS_IOT_JOBS_SUBSCRIPTIONS ][ JOBS_SUBSCRIPTION_SIZE ] = { { 0 } };         /**< @brief Jobs subscriptions. */

/*-----------------------------------------------------------*/

void * AwsIotJobs_MallocOperation( size_t size )
{
    int32_t freeIndex = -1;
    void * pNewOperation = NULL;

    /* Check size argument. */
    if( size <= JOBS_OPERATION_SIZE )
    {
        /* Find a free Jobs operation. */
        freeIndex = IotStaticMemory_FindFree( _pInUseJobsOperations,
                                              AWS_IOT_JOBS_MAX_IN_PROGRESS_OPERATIONS );

        if( freeIndex != -1 )
        {
            pNewOperation = &( _pJobsOperations[ freeIndex ] );
        }
    }

    return pNewOperation;
}

/*-----------------------------------------------------------*/

void AwsIotJobs_FreeOperation( void * ptr )
{
    /* Return the in-use Jobs operation. */
    IotStaticMemory_ReturnInUse( ptr,
                                 _pJobsOperations,
                                 _pInUseJobsOperations,
                                 AWS_IOT_JOBS_MAX_IN_PROGRESS_OPERATIONS,
                                 JOBS_OPERATION_SIZE );
}

/*-----------------------------------------------------------*/

void * AwsIotJobs_MallocSubscription( size_t size )
{
    int32_t freeIndex = -1;
    void * pNewSubscription = NULL;

    if( size <= JOBS_SUBSCRIPTION_SIZE )
    {
        /* Get the index of a free Jobs subscription. */
        freeIndex = IotStaticMemory_FindFree( _pInUseJobsSubscriptions,
                                              AWS_IOT_JOBS_SUBSCRIPTIONS );

        if( freeIndex != -1 )
        {
            pNewSubscription = &( _pJobsSubscriptions[ freeIndex ][ 0 ] );
        }
    }

    return pNewSubscription;
}

/*-----------------------------------------------------------*/

void AwsIotJobs_FreeSubscription( void * ptr )
{
    /* Return the in-use Jobs subscription. */
    IotStaticMemory_ReturnInUse( ptr,
                                 _pJobsSubscriptions,
                                 _pInUseJobsSubscriptions,
                                 AWS_IOT_JOBS_SUBSCRIPTIONS,
                                 JOBS_SUBSCRIPTION_SIZE );
}

/*-----------------------------------------------------------*/

#endif
