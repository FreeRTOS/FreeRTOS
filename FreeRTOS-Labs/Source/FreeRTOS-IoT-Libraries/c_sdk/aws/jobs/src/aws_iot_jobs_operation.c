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
 * @file aws_iot_jobs_operation.c
 * @brief Implements functions that process Jobs operations.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* Jobs internal include. */
#include "private/aws_iot_jobs_internal.h"

/* Platform threads include. */
#include "platform/iot_threads.h"

/* Error handling include. */
#include "iot_error.h"

/* MQTT include. */
#include "iot_mqtt.h"

/*-----------------------------------------------------------*/

#if LIBRARY_LOG_LEVEL > IOT_LOG_NONE

/**
 * @brief Printable names for each of the Jobs operations.
 */
    const char * const _pAwsIotJobsOperationNames[] =
    {
        "GET PENDING",
        "START NEXT",
        "DESCRIBE",
        "UPDATE",
        "SET NOTIFY-PENDING",
        "SET NOTIFY-NEXT"
    };
#endif /* if LIBRARY_LOG_LEVEL > IOT_LOG_NONE */

/*-----------------------------------------------------------*/

/**
 * @brief First parameter to #_jobsOperation_match.
 */
typedef struct _operationMatchParams
{
    _jobsOperationType_t type; /**< @brief GET PENDING, START NEXT, DESCRIBE, or UPDATE. */
    const char * pThingName;   /**< @brief Thing Name of Jobs operation. */
    size_t thingNameLength;    /**< @brief Length of #_operationMatchParams_t.pThingName. */
    const char * pResponse;    /**< @brief Jobs response document. */
    size_t responseLength;     /**< @brief Length of #_operationMatchParams_t.pResponse. */
} _operationMatchParams_t;

/*-----------------------------------------------------------*/

/**
 * @brief Match a received Jobs response with a Jobs operation awaiting a
 * response.
 *
 * @param[in] pOperationLink Pointer to the link member of the #_jobsOperation_t
 * to check.
 * @param[in] pMatch Pointer to an #_operationMatchParams_t.
 *
 * @return `true` if `pMatch` matches the received response; `false` otherwise.
 */
static bool _jobsOperation_match( const IotLink_t * pOperationLink,
                                  void * pMatch );

/**
 * @brief Invoked when a Jobs response is received for Jobs GET PENDING.
 *
 * @param[in] pArgument Ignored.
 * @param[in] pMessage Received Jobs response (as an MQTT PUBLISH message).
 */
static void _getPendingCallback( void * pArgument,
                                 IotMqttCallbackParam_t * pMessage );

/**
 * @brief Invoked when a Jobs response is received for a Jobs START NEXT.
 *
 * @param[in] pArgument Ignored.
 * @param[in] pMessage Received Jobs response (as an MQTT PUBLISH message).
 */
static void _startNextCallback( void * pArgument,
                                IotMqttCallbackParam_t * pMessage );

/**
 * @brief Invoked when a Jobs response is received for Jobs DESCRIBE.
 *
 * @param[in] pArgument Ignored.
 * @param[in] pMessage Received Jobs response (as an MQTT PUBLISH message).
 */
static void _describeCallback( void * pArgument,
                               IotMqttCallbackParam_t * pMessage );

/**
 * @brief Invoked when a Jobs response is received for a Jobs UPDATE.
 *
 * @param[in] pArgument Ignored.
 * @param[in] pMessage Received Jobs response (as an MQTT PUBLISH message).
 */
static void _updateCallback( void * pArgument,
                             IotMqttCallbackParam_t * pMessage );

/**
 * @brief Common function for processing received Jobs responses.
 *
 * @param[in] type GET PENDING, START NEXT, DESCRIBE, or UPDATE.
 * @param[in] pMessage Received Jobs response (as an MQTT PUBLISH message).
 */
static void _commonOperationCallback( _jobsOperationType_t type,
                                      IotMqttCallbackParam_t * pMessage );

/**
 * @brief Notify of a completed Jobs operation.
 *
 * @param[in] pOperation The operation which completed.
 *
 * Depending on the parameters passed to a user-facing Jobs function, the
 * notification will cause @ref jobs_function_wait to return or invoke a
 * user-provided callback.
 */
static void _notifyCompletion( _jobsOperation_t * pOperation );

/**
 * @brief Get a Jobs subscription to use with a Jobs operation.
 *
 * This function may use an existing Jobs subscription, or it may allocate a
 * new one.
 *
 * @param[in] pRequestInfo Common Jobs request parameters.
 * @param[in] pTopicBuffer Contains the topic to use for subscribing.
 * @param[in] operationTopicLength The length of the base topic in `pTopicBuffer`.
 * @param[in] pOperation Jobs operation that needs a subscription.
 * @param[out] pFreeTopicBuffer Whether the caller may free `pTopicBuffer`
 * (which may be assigned to a subscription).
 *
 * @return #AWS_IOT_JOBS_SUCCESS or #AWS_IOT_JOBS_NO_MEMORY
 */
static AwsIotJobsError_t _findSubscription( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                            char * pTopicBuffer,
                                            uint16_t operationTopicLength,
                                            _jobsOperation_t * pOperation,
                                            bool * pFreeTopicBuffer );

/*-----------------------------------------------------------*/

/**
 * @brief List of active Jobs operations awaiting a response from the Jobs
 * service.
 */
IotListDouble_t _AwsIotJobsPendingOperations = { 0 };

/**
 * @brief Protects #_AwsIotJobsPendingOperations from concurrent access.
 */
IotMutex_t _AwsIotJobsPendingOperationsMutex;

/*-----------------------------------------------------------*/

static bool _jobsOperation_match( const IotLink_t * pOperationLink,
                                  void * pMatch )
{
    /* Because this function is called from a container function, the given link
     * must never be NULL. */
    AwsIotJobs_Assert( pOperationLink != NULL );

    _jobsOperation_t * pOperation = IotLink_Container( _jobsOperation_t,
                                                       pOperationLink,
                                                       link );
    _operationMatchParams_t * pParam = ( _operationMatchParams_t * ) pMatch;
    _jobsSubscription_t * pSubscription = pOperation->pSubscription;
    const char * pClientToken = NULL;
    size_t clientTokenLength = 0;

    /* Check for matching Thing Name and operation type. */
    bool match = ( pOperation->type == pParam->type ) &&
                 ( pParam->thingNameLength == pSubscription->thingNameLength ) &&
                 ( strncmp( pParam->pThingName,
                            pSubscription->pThingName,
                            pParam->thingNameLength ) == 0 );

    if( match == true )
    {
        IotLogDebug( "Verifying client tokens for Jobs %s.",
                     _pAwsIotJobsOperationNames[ pParam->type ] );

        /* Check the response for a client token. */
        match = AwsIot_GetClientToken( pParam->pResponse,
                                       pParam->responseLength,
                                       &pClientToken,
                                       &clientTokenLength );

        /* If the response contains a client token, check for a match. */
        if( match == true )
        {
            match = ( pOperation->clientTokenLength == clientTokenLength ) &&
                    ( strncmp( pOperation->pClientToken, pClientToken, clientTokenLength ) == 0 );
        }
        else
        {
            IotLogWarn( "Received a Jobs %s response with no client token. "
                        "This is possibly a response to a bad JSON document:\r\n%.*s",
                        _pAwsIotJobsOperationNames[ pParam->type ],
                        pParam->responseLength,
                        pParam->pResponse );
        }
    }

    return match;
}

/*-----------------------------------------------------------*/

static void _getPendingCallback( void * pArgument,
                                 IotMqttCallbackParam_t * pMessage )
{
    /* Silence warnings about unused parameter. */
    ( void ) pArgument;

    _commonOperationCallback( JOBS_GET_PENDING, pMessage );
}

/*-----------------------------------------------------------*/

static void _startNextCallback( void * pArgument,
                                IotMqttCallbackParam_t * pMessage )
{
    /* Silence warnings about unused parameter. */
    ( void ) pArgument;

    _commonOperationCallback( JOBS_START_NEXT, pMessage );
}

/*-----------------------------------------------------------*/

static void _describeCallback( void * pArgument,
                               IotMqttCallbackParam_t * pMessage )
{
    /* Silence warnings about unused parameter. */
    ( void ) pArgument;

    _commonOperationCallback( JOBS_DESCRIBE, pMessage );
}

/*-----------------------------------------------------------*/

static void _updateCallback( void * pArgument,
                             IotMqttCallbackParam_t * pMessage )
{
    /* Silence warnings about unused parameter. */
    ( void ) pArgument;

    _commonOperationCallback( JOBS_UPDATE, pMessage );
}

/*-----------------------------------------------------------*/

static void _commonOperationCallback( _jobsOperationType_t type,
                                      IotMqttCallbackParam_t * pMessage )
{
    _jobsOperation_t * pOperation = NULL;
    IotLink_t * pOperationLink = NULL;
    _operationMatchParams_t param = { 0 };
    AwsIotStatus_t status = AWS_IOT_UNKNOWN;
    uint32_t flags = 0;

    /* Set operation type and response. */
    param.type = type;
    param.pResponse = pMessage->u.message.info.pPayload;
    param.responseLength = pMessage->u.message.info.payloadLength;

    /* Parse the Thing Name from the MQTT topic name. */
    if( AwsIot_ParseThingName( pMessage->u.message.info.pTopicName,
                               pMessage->u.message.info.topicNameLength,
                               &( param.pThingName ),
                               &( param.thingNameLength ) ) == false )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Lock the pending operations list for exclusive access. */
    IotMutex_Lock( &( _AwsIotJobsPendingOperationsMutex ) );

    /* Search for a matching pending operation. */
    pOperationLink = IotListDouble_FindFirstMatch( &_AwsIotJobsPendingOperations,
                                                   NULL,
                                                   _jobsOperation_match,
                                                   &param );

    /* Find and remove the first Jobs operation of the given type. */
    if( pOperationLink == NULL )
    {
        /* Operation is not pending. It may have already been processed. Return
         * without doing anything */
        IotMutex_Unlock( &( _AwsIotJobsPendingOperationsMutex ) );

        IotLogWarn( "Jobs %s callback received an unknown operation.",
                    _pAwsIotJobsOperationNames[ type ] );

        IOT_GOTO_CLEANUP();
    }
    else
    {
        pOperation = IotLink_Container( _jobsOperation_t, pOperationLink, link );

        /* Copy the flags from the Jobs operation. */
        flags = pOperation->flags;

        /* Remove a non-waitable operation from the pending operation list.
         * Waitable operations are removed by the Wait function. */
        if( ( flags & AWS_IOT_JOBS_FLAG_WAITABLE ) == 0 )
        {
            IotListDouble_Remove( &( pOperation->link ) );
            IotMutex_Unlock( &( _AwsIotJobsPendingOperationsMutex ) );
        }
    }

    /* Parse the status from the topic name. */
    status = AwsIot_ParseStatus( pMessage->u.message.info.pTopicName,
                                 pMessage->u.message.info.topicNameLength );

    switch( status )
    {
        case AWS_IOT_ACCEPTED:
        case AWS_IOT_REJECTED:
            _AwsIotJobs_ParseResponse( status,
                                       pMessage->u.message.info.pPayload,
                                       pMessage->u.message.info.payloadLength,
                                       pOperation );
            break;

        default:
            IotLogWarn( "Unknown status for %s of %.*s Jobs. Ignoring message.",
                        _pAwsIotJobsOperationNames[ type ],
                        pOperation->pSubscription->thingNameLength,
                        pOperation->pSubscription->pThingName );

            pOperation->status = AWS_IOT_JOBS_BAD_RESPONSE;

            break;
    }

    _notifyCompletion( pOperation );

    /* For waitable operations, unlock the pending operation list mutex to allow
     * the Wait function to run. */
    if( ( flags & AWS_IOT_JOBS_FLAG_WAITABLE ) == AWS_IOT_JOBS_FLAG_WAITABLE )
    {
        IotMutex_Unlock( &( _AwsIotJobsPendingOperationsMutex ) );
    }

    /* This function has no return value and no cleanup, but uses the cleanup
     * label to exit on error. */
    IOT_FUNCTION_CLEANUP_BEGIN();
}

/*-----------------------------------------------------------*/

static void _notifyCompletion( _jobsOperation_t * pOperation )
{
    AwsIotJobsCallbackParam_t callbackParam = { .callbackType = ( AwsIotJobsCallbackType_t ) 0 };
    _jobsSubscription_t * pSubscription = pOperation->pSubscription,
                        * pRemovedSubscription = NULL;

    /* If the operation is waiting, post to its wait semaphore and return. */
    if( ( pOperation->flags & AWS_IOT_JOBS_FLAG_WAITABLE ) == AWS_IOT_JOBS_FLAG_WAITABLE )
    {
        IotSemaphore_Post( &( pOperation->notify.waitSemaphore ) );
    }
    else
    {
        /* Decrement the reference count. This also removes subscriptions if the
         * count reaches 0. */
        IotMutex_Lock( &_AwsIotJobsSubscriptionsMutex );
        _AwsIotJobs_DecrementReferences( pOperation,
                                         pSubscription->pTopicBuffer,
                                         &pRemovedSubscription );
        IotMutex_Unlock( &_AwsIotJobsSubscriptionsMutex );

        /* Set the subscription pointer used for the user callback based on whether
         * a subscription was removed from the list. */
        if( pRemovedSubscription != NULL )
        {
            pSubscription = pRemovedSubscription;
        }

        AwsIotJobs_Assert( pSubscription != NULL );

        /* Invoke the user callback if provided. */
        if( pOperation->notify.callback.function != NULL )
        {
            /* Set the common members of the callback parameter. */
            callbackParam.callbackType = ( AwsIotJobsCallbackType_t ) pOperation->type;
            callbackParam.mqttConnection = pOperation->mqttConnection;
            callbackParam.pThingName = pSubscription->pThingName;
            callbackParam.thingNameLength = pSubscription->thingNameLength;
            callbackParam.u.operation.result = pOperation->status;
            callbackParam.u.operation.reference = pOperation;
            callbackParam.u.operation.pResponse = pOperation->pJobsResponse;
            callbackParam.u.operation.responseLength = pOperation->jobsResponseLength;

            pOperation->notify.callback.function( pOperation->notify.callback.pCallbackContext,
                                                  &callbackParam );
        }

        /* Destroy a removed subscription. */
        if( pRemovedSubscription != NULL )
        {
            _AwsIotJobs_DestroySubscription( pRemovedSubscription );
        }

        _AwsIotJobs_DestroyOperation( pOperation );
    }
}

/*-----------------------------------------------------------*/

static AwsIotJobsError_t _findSubscription( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                            char * pTopicBuffer,
                                            uint16_t operationTopicLength,
                                            _jobsOperation_t * pOperation,
                                            bool * pFreeTopicBuffer )
{
    AwsIotJobsError_t status = AWS_IOT_JOBS_SUCCESS;
    _jobsSubscription_t * pSubscription = NULL;

    /* Lookup table for Jobs operation callbacks. */
    const AwsIotMqttCallbackFunction_t jobsCallbacks[ JOBS_OPERATION_COUNT ] =
    {
        _getPendingCallback,
        _startNextCallback,
        _describeCallback,
        _updateCallback
    };

    /* Lock the subscriptions mutex for exclusive access. */
    IotMutex_Lock( &_AwsIotJobsSubscriptionsMutex );

    /* Check for an existing subscription. This function will attempt to allocate
     * a new subscription if not found. */
    pSubscription = _AwsIotJobs_FindSubscription( pRequestInfo->pThingName,
                                                  pRequestInfo->thingNameLength,
                                                  true );

    if( pSubscription == NULL )
    {
        status = AWS_IOT_JOBS_NO_MEMORY;
    }
    else
    {
        /* Ensure that the subscription Thing Name matches. */
        AwsIotJobs_Assert( pSubscription != NULL );
        AwsIotJobs_Assert( pSubscription->thingNameLength == pRequestInfo->thingNameLength );
        AwsIotJobs_Assert( strncmp( pSubscription->pThingName,
                                    pRequestInfo->pThingName,
                                    pRequestInfo->thingNameLength ) == 0 );

        /* Set the subscription object for the Jobs operation. */
        pOperation->pSubscription = pSubscription;

        /* Assign the topic buffer to the subscription to use for unsubscribing if
         * the subscription has no topic buffer. */
        if( pSubscription->pTopicBuffer == NULL )
        {
            pSubscription->pTopicBuffer = pTopicBuffer;

            /* Don't free the topic buffer if it was allocated to the subscription. */
            *pFreeTopicBuffer = false;
        }
        else
        {
            *pFreeTopicBuffer = true;
        }

        /* Increment the reference count for this Jobs operation's
         * subscriptions. */
        status = _AwsIotJobs_IncrementReferences( pOperation,
                                                  pTopicBuffer,
                                                  operationTopicLength,
                                                  jobsCallbacks[ pOperation->type ] );

        if( status != AWS_IOT_JOBS_SUCCESS )
        {
            /* Failed to add subscriptions for a Jobs operation. The reference
             * count was not incremented. Check if this subscription should be
             * deleted. */
            _AwsIotJobs_RemoveSubscription( pSubscription, NULL );
        }
    }

    /* Unlock the Jobs subscription list mutex. */
    IotMutex_Unlock( &_AwsIotJobsSubscriptionsMutex );

    return status;
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t _AwsIotJobs_CreateOperation( _jobsOperationType_t type,
                                               const AwsIotJobsRequestInfo_t * pRequestInfo,
                                               const _jsonRequestContents_t * pRequestContents,
                                               uint32_t flags,
                                               const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                               _jobsOperation_t ** pNewOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_SUCCESS );
    size_t operationSize = sizeof( _jobsOperation_t );
    _jobsOperation_t * pOperation = NULL;

    IotLogDebug( "Creating operation record for Jobs %s.",
                 _pAwsIotJobsOperationNames[ type ] );

    /* The Job ID must be saved for DESCRIBE and UPDATE operations. */
    if( ( type == JOBS_DESCRIBE ) || ( type == JOBS_UPDATE ) )
    {
        /* Ensure a valid Job ID is provided. */
        AwsIotJobs_Assert( pRequestInfo->pJobId != NULL );
        AwsIotJobs_Assert( pRequestInfo->jobIdLength > 1 );
        AwsIotJobs_Assert( pRequestInfo->jobIdLength <= JOBS_MAX_ID_LENGTH );

        operationSize += pRequestInfo->jobIdLength;
    }

    /* Allocate memory for a new Jobs operation. */
    pOperation = AwsIotJobs_MallocOperation( operationSize );

    if( pOperation == NULL )
    {
        IotLogError( "Failed to allocate memory for Jobs %s.",
                     _pAwsIotJobsOperationNames[ type ] );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_NO_MEMORY );
    }

    /* Clear the operation data. */
    ( void ) memset( pOperation, 0x00, sizeof( _jobsOperation_t ) );

    /* Set the remaining common members of the Jobs operation. */
    pOperation->type = type;
    pOperation->flags = flags;
    pOperation->status = AWS_IOT_JOBS_STATUS_PENDING;
    pOperation->mallocResponse = pRequestInfo->mallocResponse;

    /* Save the Job ID for DESCRIBE and UPDATE operations. */
    if( ( type == JOBS_DESCRIBE ) || ( type == JOBS_UPDATE ) )
    {
        pOperation->jobIdLength = pRequestInfo->jobIdLength;

        ( void ) memcpy( pOperation->pJobId, pRequestInfo->pJobId, pRequestInfo->jobIdLength );
    }

    /* Generate a Jobs request document. */
    status = _AwsIotJobs_GenerateJsonRequest( type,
                                              pRequestInfo,
                                              pRequestContents,
                                              pOperation );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Check if the waitable flag is set. If it is, create a semaphore to
     * wait on. */
    if( ( flags & AWS_IOT_JOBS_FLAG_WAITABLE ) == AWS_IOT_JOBS_FLAG_WAITABLE )
    {
        if( IotSemaphore_Create( &( pOperation->notify.waitSemaphore ), 0, 1 ) == false )
        {
            IotLogError( "Failed to create semaphore for waitable Jobs %s.",
                         _pAwsIotJobsOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_NO_MEMORY );
        }
    }
    else
    {
        /* If the waitable flag isn't set but a callback is, copy the callback
         * information. */
        if( pCallbackInfo != NULL )
        {
            pOperation->notify.callback = *pCallbackInfo;
        }
    }

    IOT_FUNCTION_CLEANUP_BEGIN();

    /* Clean up on error. */
    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        if( pOperation != NULL )
        {
            if( pOperation->pJobsRequest != NULL )
            {
                AwsIotJobs_FreeString( ( void * ) ( pOperation->pJobsRequest ) );
            }

            AwsIotJobs_FreeOperation( pOperation );
        }
    }
    else
    {
        /* Set the output parameter. */
        *pNewOperation = pOperation;
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

void _AwsIotJobs_DestroyOperation( void * pData )
{
    _jobsOperation_t * pOperation = ( _jobsOperation_t * ) pData;

    AwsIotJobs_Assert( pOperation != NULL );

    IotLogDebug( "Destroying Jobs operation %s.",
                 _pAwsIotJobsOperationNames[ pOperation->type ] );

    /* Check if a wait semaphore was created for this operation. */
    if( ( pOperation->flags & AWS_IOT_JOBS_FLAG_WAITABLE ) == AWS_IOT_JOBS_FLAG_WAITABLE )
    {
        /* Destroy the wait semaphore */
        IotSemaphore_Destroy( &( pOperation->notify.waitSemaphore ) );
    }

    /* Free any Jobs request documents. */
    if( pOperation->pJobsRequest != NULL )
    {
        AwsIotJobs_Assert( pOperation->jobsRequestLength > 0 );

        AwsIotJobs_FreeString( ( void * ) ( pOperation->pJobsRequest ) );
    }

    /* Free the memory used to hold operation data. */
    AwsIotJobs_FreeOperation( pOperation );
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t _AwsIotJobs_GenerateJobsTopic( _jobsOperationType_t type,
                                                 const AwsIotJobsRequestInfo_t * pRequestInfo,
                                                 char ** pTopicBuffer,
                                                 uint16_t * pOperationTopicLength )
{
    AwsIotJobsError_t status = AWS_IOT_JOBS_SUCCESS;
    AwsIotTopicInfo_t topicInfo = { 0 };
    char pJobOperationName[ JOBS_LONGEST_SUFFIX_LENGTH ] = { 0 };
    uint16_t operationNameLength = 0;

    /* Lookup table for Jobs operation strings. */
    const char * const pOperationString[ JOBS_OPERATION_COUNT ] =
    {
        JOBS_GET_PENDING_OPERATION_STRING, /* Jobs get pending operation. */
        JOBS_START_NEXT_OPERATION_STRING,  /* Jobs start next operation. */
        JOBS_DESCRIBE_OPERATION_STRING,    /* Jobs describe operation */
        JOBS_UPDATE_OPERATION_STRING       /* Jobs update operation. */
    };

    /* Lookup table for Jobs operation string lengths. */
    const uint16_t pOperationStringLength[ JOBS_OPERATION_COUNT ] =
    {
        JOBS_GET_PENDING_OPERATION_STRING_LENGTH, /* Jobs get pending operation */
        JOBS_START_NEXT_OPERATION_STRING_LENGTH,  /* Jobs start next operation. */
        JOBS_DESCRIBE_OPERATION_STRING_LENGTH,    /* Jobs describe operation */
        JOBS_UPDATE_OPERATION_STRING_LENGTH       /* Jobs update operation. */
    };

    /* Ensure type is valid. */
    AwsIotJobs_Assert( ( type == JOBS_GET_PENDING ) || ( type == JOBS_START_NEXT ) ||
                       ( type == JOBS_DESCRIBE ) || ( type == JOBS_UPDATE ) );

    /* Set the members needed to generate an operation topic. */
    topicInfo.pThingName = pRequestInfo->pThingName;
    topicInfo.thingNameLength = pRequestInfo->thingNameLength;
    topicInfo.longestSuffixLength = JOBS_LONGEST_SUFFIX_LENGTH;
    topicInfo.mallocString = AwsIotJobs_MallocString;

    /* Job operations that require a Job ID require additional processing to
     * create an operation name with the Job ID. */
    if( ( type == JOBS_DESCRIBE ) || ( type == JOBS_UPDATE ) )
    {
        /* Ensure Job ID length is valid. */
        AwsIotJobs_Assert( pRequestInfo->jobIdLength > 0 );
        AwsIotJobs_Assert( pRequestInfo->jobIdLength <= JOBS_MAX_ID_LENGTH );

        /* Construct the Jobs operation name with the Job ID. */
        ( void ) memcpy( pJobOperationName, "/jobs/", 6 );
        operationNameLength = 6;

        ( void ) memcpy( pJobOperationName + operationNameLength,
                         pRequestInfo->pJobId,
                         pRequestInfo->jobIdLength );
        operationNameLength = ( uint16_t ) ( pRequestInfo->jobIdLength + operationNameLength );

        ( void ) memcpy( pJobOperationName + operationNameLength,
                         pOperationString[ type ],
                         pOperationStringLength[ type ] );
        operationNameLength = ( uint16_t ) ( operationNameLength + pOperationStringLength[ type ] );

        topicInfo.pOperationName = pJobOperationName;
        topicInfo.operationNameLength = operationNameLength;
    }
    else
    {
        topicInfo.pOperationName = pOperationString[ type ];
        topicInfo.operationNameLength = pOperationStringLength[ type ];
    }

    if( AwsIot_GenerateOperationTopic( &topicInfo,
                                       pTopicBuffer,
                                       pOperationTopicLength ) == false )
    {
        status = AWS_IOT_JOBS_NO_MEMORY;
    }

    return status;
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t _AwsIotJobs_ProcessOperation( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                                _jobsOperation_t * pOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_STATUS_PENDING );
    char * pTopicBuffer = NULL;
    uint16_t operationTopicLength = 0;
    bool freeTopicBuffer = true;
    IotMqttPublishInfo_t publishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;
    IotMqttError_t publishStatus = IOT_MQTT_STATUS_PENDING;

    IotLogDebug( "Processing Jobs operation %s for Thing %.*s.",
                 _pAwsIotJobsOperationNames[ pOperation->type ],
                 pRequestInfo->thingNameLength,
                 pRequestInfo->pThingName );

    /* Set the operation's MQTT connection. */
    pOperation->mqttConnection = pRequestInfo->mqttConnection;

    /* Generate the operation topic buffer. */
    status = _AwsIotJobs_GenerateJobsTopic( pOperation->type,
                                            pRequestInfo,
                                            &pTopicBuffer,
                                            &operationTopicLength );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        IotLogError( "No memory for Jobs operation topic buffer." );

        IOT_GOTO_CLEANUP();
    }

    /* Get a subscription object for this Jobs operation. */
    status = _findSubscription( pRequestInfo,
                                pTopicBuffer,
                                operationTopicLength,
                                pOperation,
                                &freeTopicBuffer );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        /* No subscription was found and no subscription could be allocated. */
        IOT_GOTO_CLEANUP();
    }

    /* Set the members for PUBLISH retry. */
    publishInfo.qos = pRequestInfo->qos;
    publishInfo.retryLimit = pRequestInfo->retryLimit;
    publishInfo.retryMs = pRequestInfo->retryMs;

    /* Set the payload as the Jobs request. */
    publishInfo.pPayload = pOperation->pJobsRequest;
    publishInfo.payloadLength = pOperation->jobsRequestLength;

    /* Set the operation topic name. */
    publishInfo.pTopicName = pTopicBuffer;
    publishInfo.topicNameLength = operationTopicLength;

    IotLogDebug( "Jobs %s message will be published to topic %.*s",
                 _pAwsIotJobsOperationNames[ pOperation->type ],
                 publishInfo.topicNameLength,
                 publishInfo.pTopicName );

    /* Add Jobs operation to the pending operations list. */
    IotMutex_Lock( &( _AwsIotJobsPendingOperationsMutex ) );
    IotListDouble_InsertHead( &( _AwsIotJobsPendingOperations ),
                              &( pOperation->link ) );
    IotMutex_Unlock( &( _AwsIotJobsPendingOperationsMutex ) );

    /* Publish to the Jobs topic name. */
    publishStatus = IotMqtt_PublishSync( pOperation->mqttConnection,
                                         &publishInfo,
                                         0,
                                         _AwsIotJobsMqttTimeoutMs );

    if( publishStatus != IOT_MQTT_SUCCESS )
    {
        IotLogError( "Failed to publish MQTT message to %s %.*s Jobs, error %s.",
                     _pAwsIotJobsOperationNames[ pOperation->type ],
                     pRequestInfo->thingNameLength,
                     pRequestInfo->pThingName,
                     IotMqtt_strerror( publishStatus ) );

        /* Convert the MQTT "NO MEMORY" error to a Jobs "NO MEMORY" error. */
        if( publishStatus == IOT_MQTT_NO_MEMORY )
        {
            status = AWS_IOT_JOBS_NO_MEMORY;
        }
        else
        {
            status = AWS_IOT_JOBS_MQTT_ERROR;
        }

        /* If the "keep subscriptions" flag is not set, decrement the reference
         * count. */
        if( ( pOperation->flags & AWS_IOT_JOBS_FLAG_KEEP_SUBSCRIPTIONS ) == 0 )
        {
            IotMutex_Lock( &_AwsIotJobsSubscriptionsMutex );
            _AwsIotJobs_DecrementReferences( pOperation,
                                             pTopicBuffer,
                                             NULL );
            IotMutex_Unlock( &_AwsIotJobsSubscriptionsMutex );
        }

        /* Remove Jobs operation from the pending operations list. */
        IotMutex_Lock( &( _AwsIotJobsPendingOperationsMutex ) );
        IotListDouble_Remove( &( pOperation->link ) );
        IotMutex_Unlock( &( _AwsIotJobsPendingOperationsMutex ) );
    }
    else
    {
        IotLogDebug( "Jobs %s PUBLISH message successfully sent.",
                     _pAwsIotJobsOperationNames[ pOperation->type ] );
    }

    IOT_FUNCTION_CLEANUP_BEGIN();

    /* Free the topic buffer used by this function if it was not assigned to a
     * subscription. */
    if( ( freeTopicBuffer == true ) && ( pTopicBuffer != NULL ) )
    {
        AwsIotJobs_FreeString( pTopicBuffer );
    }

    /* Destroy the Jobs operation on failure. */
    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        _AwsIotJobs_DestroyOperation( pOperation );
    }
    else
    {
        /* Convert successful return code to "status pending", as the Jobs
         * library is now waiting for a response from the service. */
        status = AWS_IOT_JOBS_STATUS_PENDING;
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/
