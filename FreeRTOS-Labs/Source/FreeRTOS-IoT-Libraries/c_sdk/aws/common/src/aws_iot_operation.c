/*
 * AWS IoT Common V1.0.0
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
 * @file aws_iot_operation.c
 * @brief Functions for common AWS IoT operations.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* Platform threads include. */
#include "platform/iot_threads.h"

/* AWS IoT include. */
#include "aws_iot.h"

/* Error handling include. */
#include "iot_error.h"

/*-----------------------------------------------------------*/

bool AwsIot_InitLists( IotListDouble_t * pPendingOperationsList,
                       IotListDouble_t * pSubscriptionsList,
                       IotMutex_t * pPendingOperationsMutex,
                       IotMutex_t * pSubscriptionsMutex )
{
    IOT_FUNCTION_ENTRY( bool, true );

    /* Flags to track cleanup. */
    bool operationsMutexCreated = false;
    bool subscriptionsMutexCreated = false;

    /* Create the mutex guarding the pending operations list. */
    operationsMutexCreated = IotMutex_Create( pPendingOperationsMutex, false );

    if( operationsMutexCreated == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    /* Create the mutex guarding the subscriptions list. */
    subscriptionsMutexCreated = IotMutex_Create( pSubscriptionsMutex, false );

    if( subscriptionsMutexCreated == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    /* Initialize lists. */
    IotListDouble_Create( pPendingOperationsList );
    IotListDouble_Create( pSubscriptionsList );

    IOT_FUNCTION_CLEANUP_BEGIN();

    /* Clean up on error. */
    if( status == false )
    {
        if( operationsMutexCreated == true )
        {
            IotMutex_Destroy( pPendingOperationsMutex );
        }
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

bool AwsIot_GenerateOperationTopic( const AwsIotTopicInfo_t * pTopicInfo,
                                    char ** pTopicBuffer,
                                    uint16_t * pOperationTopicLength )
{
    bool status = true;
    uint16_t bufferLength = 0;
    uint16_t operationTopicLength = 0;
    char * pBuffer = NULL;

    /* Calculate the required topic buffer length. */
    bufferLength = ( uint16_t ) ( AWS_IOT_TOPIC_PREFIX_LENGTH +
                                  pTopicInfo->thingNameLength +
                                  pTopicInfo->operationNameLength +
                                  pTopicInfo->longestSuffixLength );

    /* Allocate memory for the topic buffer if no topic buffer is given. */
    if( *pTopicBuffer == NULL )
    {
        pBuffer = pTopicInfo->mallocString( ( size_t ) bufferLength );

        if( pBuffer == NULL )
        {
            status = false;
        }
    }
    /* Otherwise, use the given topic buffer. */
    else
    {
        pBuffer = *pTopicBuffer;
    }

    if( status == true )
    {
        /* Copy the AWS IoT topic prefix into the topic buffer. */
        ( void ) memcpy( pBuffer, AWS_IOT_TOPIC_PREFIX, AWS_IOT_TOPIC_PREFIX_LENGTH );
        operationTopicLength = ( uint16_t ) ( operationTopicLength + AWS_IOT_TOPIC_PREFIX_LENGTH );

        /* Copy the Thing Name into the topic buffer. */
        ( void ) memcpy( pBuffer + operationTopicLength,
                         pTopicInfo->pThingName,
                         pTopicInfo->thingNameLength );
        operationTopicLength = ( uint16_t ) ( operationTopicLength + pTopicInfo->thingNameLength );

        /* Copy the Shadow operation string into the topic buffer. */
        ( void ) memcpy( pBuffer + operationTopicLength,
                         pTopicInfo->pOperationName,
                         pTopicInfo->operationNameLength );
        operationTopicLength = ( uint16_t ) ( operationTopicLength + pTopicInfo->operationNameLength );

        /* Set the output parameters. */
        if( *pTopicBuffer == NULL )
        {
            *pTopicBuffer = pBuffer;
        }

        *pOperationTopicLength = operationTopicLength;
    }

    return status;
}

/*-----------------------------------------------------------*/
