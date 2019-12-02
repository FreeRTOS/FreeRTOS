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
 * @file aws_iot_jobs_api.c
 * @brief Implements the user-facing functions of the Jobs library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* Platform threads include. */
#include "platform/iot_threads.h"

/* Jobs internal include. */
#include "private/aws_iot_jobs_internal.h"

/* Error handling include. */
#include "iot_error.h"

/* MQTT include. */
#include "iot_mqtt.h"

/* Validate Jobs configuration settings. */
#if AWS_IOT_JOBS_ENABLE_ASSERTS != 0 && AWS_IOT_JOBS_ENABLE_ASSERTS != 1
    #error "AWS_IOT_JOBS_ENABLE_ASSERTS must be 0 or 1."
#endif
#if AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS <= 0
    #error "AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS cannot be 0 or negative."
#endif
#if AWS_IOT_JOBS_NOTIFY_CALLBACKS <= 0
    #error "AWS_IOT_JOBS_NOTIFY_CALLBACKS cannot be 0 or negative."
#endif

/**
 * @brief Returned by @ref _getCallbackIndex when there's no space in the callback array.
 */
#define NO_SPACE_FOR_CALLBACK     ( -1 )

/**
 * @brief Returned by @ref _getCallbackIndex when a searching for an oldCallback that
 * does not exist.
 */
#define OLD_CALLBACK_NOT_FOUND    ( -2 )

/*-----------------------------------------------------------*/

/**
 * @brief Check if the library is initialized.
 *
 * @return `true` if AwsIotJobs_Init was called; `false` otherwise.
 */
static bool _checkInit( void );

/**
 * @brief Validate the #AwsIotJobsRequestInfo_t passed to a Jobs API function.
 *
 * @param[in] type The Jobs API function type.
 * @param[in] pRequestInfo The request info passed to a Jobs API function.
 * @param[in] flags Flags used by the Jobs API function.
 * @param[in] pCallbackInfo The callback info passed with the request info.
 * @param[in] pOperation Operation reference pointer passed to a Jobs API function.
 *
 * @return #AWS_IOT_JOBS_SUCCESS or #AWS_IOT_JOBS_BAD_PARAMETER.
 */
static AwsIotJobsError_t _validateRequestInfo( _jobsOperationType_t type,
                                               const AwsIotJobsRequestInfo_t * pRequestInfo,
                                               uint32_t flags,
                                               const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                               const AwsIotJobsOperation_t * pOperation );

/**
 * @brief Validate the #AwsIotJobsUpdateInfo_t passed to a Jobs API function.
 *
 * @param[in] type The Jobs API function type.
 * @param[in] pUpdateInfo The update info passed to a Jobs API function.
 *
 * @return #AWS_IOT_JOBS_SUCCESS or #AWS_IOT_JOBS_BAD_PARAMETER.
 */
static AwsIotJobsError_t _validateUpdateInfo( _jobsOperationType_t type,
                                              const AwsIotJobsUpdateInfo_t * pUpdateInfo );

/**
 * @brief Gets an element of the callback array to modify.
 *
 * @param[in] type The type of callback to modify.
 * @param[in] pSubscription Subscription object that holds the callback array.
 * @param[in] pCallbackInfo User provided callback info.
 *
 * @return The index of the callback array to modify; on error:
 * - #NO_SPACE_FOR_CALLBACK if no free spaces are available
 * - #OLD_CALLBACK_NOT_FOUND if an old callback to remove was specified, but that function does not exist.
 *
 * @note This function should be called with the subscription list mutex locked.
 */
static int32_t _getCallbackIndex( _jobsCallbackType_t type,
                                  _jobsSubscription_t * pSubscription,
                                  const AwsIotJobsCallbackInfo_t * pCallbackInfo );

/**
 * @brief Common function for setting Jobs callbacks.
 *
 * @param[in] mqttConnection The MQTT connection to use.
 * @param[in] type Type of Jobs callback.
 * @param[in] pThingName Thing Name for Jobs callback.
 * @param[in] thingNameLength Length of `pThingName`.
 * @param[in] pCallbackInfo Callback information to set.
 *
 * @return #AWS_IOT_JOBS_SUCCESS, #AWS_IOT_JOBS_BAD_PARAMETER,
 * #AWS_IOT_JOBS_NO_MEMORY, or #AWS_IOT_JOBS_MQTT_ERROR.
 */
static AwsIotJobsError_t _setCallbackCommon( IotMqttConnection_t mqttConnection,
                                             _jobsCallbackType_t type,
                                             const char * pThingName,
                                             size_t thingNameLength,
                                             const AwsIotJobsCallbackInfo_t * pCallbackInfo );

/**
 * @brief Change the subscriptions for Jobs callbacks, either by subscribing
 * or unsubscribing.
 *
 * @param[in] mqttConnection The MQTT connection to use.
 * @param[in] type Type of Jobs callback.
 * @param[in] pSubscription Jobs subscriptions object for callback.
 * @param[in] mqttOperation Either @ref mqtt_function_subscribesync or
 * @ref mqtt_function_unsubscribesync.
 *
 * @return #AWS_IOT_JOBS_SUCCESS, #AWS_IOT_JOBS_NO_MEMORY, or
 * #AWS_IOT_JOBS_MQTT_ERROR.
 */
static AwsIotJobsError_t _modifyCallbackSubscriptions( IotMqttConnection_t mqttConnection,
                                                       _jobsCallbackType_t type,
                                                       _jobsSubscription_t * pSubscription,
                                                       AwsIotMqttFunction_t mqttOperation );

/**
 * @brief Invoked when a document is received on the Jobs NOTIFY PENDING callback.
 *
 * @param[in] pArgument Ignored.
 * @param[in] pMessage The received Jobs document (as an MQTT PUBLISH message).
 */
static void _notifyPendingCallbackWrapper( void * pArgument,
                                           IotMqttCallbackParam_t * pMessage );

/**
 * @brief Invoked when a document is received on the Jobs NOTIFY NEXT callback.
 *
 * @param[in] pArgument Ignored.
 * @param[in] pMessage The received Jobs document (as an MQTT PUBLISH message).
 */
static void _notifyNextCallbackWrapper( void * pArgument,
                                        IotMqttCallbackParam_t * pMessage );

/**
 * @brief Common function for incoming Jobs callbacks.
 *
 * @param[in] type Jobs callback type.
 * @param[in] pMessage The received Jobs callback document (as an MQTT PUBLISH
 * message).
 */
static void _callbackWrapperCommon( _jobsCallbackType_t type,
                                    IotMqttCallbackParam_t * pMessage );

/*-----------------------------------------------------------*/

/**
 * @brief Tracks whether @ref jobs_function_init has been called.
 *
 * API functions will fail if @ref jobs_function_init was not called.
 */
static uint32_t _initCalled = 0;

/**
 * @brief Timeout used for MQTT operations.
 */
uint32_t _AwsIotJobsMqttTimeoutMs = AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS;

#if LIBRARY_LOG_LEVEL > IOT_LOG_NONE

/**
 * @brief Printable names for the Jobs callbacks.
 */
    const char * const _pAwsIotJobsCallbackNames[] =
    {
        "NOTIFY PENDING",
        "NOTIFY NEXT"
    };
#endif

/*-----------------------------------------------------------*/

static bool _checkInit( void )
{
    bool status = true;

    if( _initCalled == 0 )
    {
        IotLogError( "AwsIotJobs_Init was not called." );

        status = false;
    }

    return status;
}

/*-----------------------------------------------------------*/

static AwsIotJobsError_t _validateRequestInfo( _jobsOperationType_t type,
                                               const AwsIotJobsRequestInfo_t * pRequestInfo,
                                               uint32_t flags,
                                               const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                               const AwsIotJobsOperation_t * pOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_SUCCESS );

    /* Check that the given MQTT connection is valid. */
    if( pRequestInfo->mqttConnection == IOT_MQTT_CONNECTION_INITIALIZER )
    {
        IotLogError( "MQTT connection is not initialized for Jobs %s.",
                     _pAwsIotJobsOperationNames[ type ] );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
    }

    /* Check Thing Name. */
    if( AwsIot_ValidateThingName( pRequestInfo->pThingName,
                                  pRequestInfo->thingNameLength ) == false )
    {
        IotLogError( "Thing Name is not valid for Jobs %s.",
                     _pAwsIotJobsOperationNames[ type ] );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
    }

    /* Checks for waitable operations. */
    if( ( flags & AWS_IOT_JOBS_FLAG_WAITABLE ) == AWS_IOT_JOBS_FLAG_WAITABLE )
    {
        if( pOperation == NULL )
        {
            IotLogError( "Reference must be provided for a waitable Jobs %s.",
                         _pAwsIotJobsOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }

        if( pRequestInfo->mallocResponse == NULL )
        {
            IotLogError( "Memory allocation function must be set for waitable Jobs %s.",
                         _pAwsIotJobsOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }

        if( pCallbackInfo != NULL )
        {
            IotLogError( "Callback should not be set for a waitable Jobs %s.",
                         _pAwsIotJobsOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
    }

    /* Check that a callback function is set. */
    if( pCallbackInfo != NULL )
    {
        if( pCallbackInfo->function == NULL )
        {
            IotLogError( "Callback function must be set for Jobs %s callback.",
                         _pAwsIotJobsOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
    }

    /* Check client token length. */
    if( pRequestInfo->pClientToken != AWS_IOT_JOBS_CLIENT_TOKEN_AUTOGENERATE )
    {
        if( pRequestInfo->clientTokenLength == 0 )
        {
            IotLogError( "Client token length must be set for Jobs %s.",
                         _pAwsIotJobsOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }

        if( pRequestInfo->clientTokenLength > AWS_IOT_CLIENT_TOKEN_MAX_LENGTH )
        {
            IotLogError( "Client token for Jobs %s cannot be longer than %d.",
                         _pAwsIotJobsOperationNames[ type ],
                         AWS_IOT_CLIENT_TOKEN_MAX_LENGTH );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
    }

    /* Check Job ID for DESCRIBE and UPDATE. */
    if( ( type == JOBS_DESCRIBE ) || ( type == JOBS_UPDATE ) )
    {
        if( ( pRequestInfo->pJobId == NULL ) || ( pRequestInfo->jobIdLength == 0 ) )
        {
            IotLogError( "Job ID must be set for Jobs %s.",
                         _pAwsIotJobsOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }

        if( pRequestInfo->jobIdLength > JOBS_MAX_ID_LENGTH )
        {
            IotLogError( "Job ID for Jobs %s cannot be longer than %d.",
                         _pAwsIotJobsOperationNames[ type ],
                         JOBS_MAX_ID_LENGTH );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
    }

    /* A Job ID (not $next job) must be specified for UPDATE. */
    if( type == JOBS_UPDATE )
    {
        if( ( pRequestInfo->jobIdLength == AWS_IOT_JOBS_NEXT_JOB_LENGTH ) &&
            ( strncmp( AWS_IOT_JOBS_NEXT_JOB,
                       pRequestInfo->pJobId,
                       AWS_IOT_JOBS_NEXT_JOB_LENGTH ) == 0 ) )
        {
            IotLogError( "Job ID $next is not valid for Jobs UPDATE." );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

static AwsIotJobsError_t _validateUpdateInfo( _jobsOperationType_t type,
                                              const AwsIotJobsUpdateInfo_t * pUpdateInfo )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_SUCCESS );

    /* Only START NEXT and UPDATE operations need an update info. */
    AwsIotJobs_Assert( ( type == JOBS_START_NEXT ) || ( type == JOBS_UPDATE ) );

    /* Check that Job status to report is valid for Jobs UPDATE. */
    if( type == JOBS_UPDATE )
    {
        switch( pUpdateInfo->newStatus )
        {
            case AWS_IOT_JOB_STATE_IN_PROGRESS:
            case AWS_IOT_JOB_STATE_FAILED:
            case AWS_IOT_JOB_STATE_SUCCEEDED:
            case AWS_IOT_JOB_STATE_REJECTED:
                break;

            default:
                IotLogError( "Job state %s is not valid for Jobs UPDATE.",
                             AwsIotJobs_StateName( pUpdateInfo->newStatus ) );

                IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
    }

    /* Check that step timeout is valid. */
    if( ( pUpdateInfo->stepTimeoutInMinutes != AWS_IOT_JOBS_NO_TIMEOUT ) &&
        ( pUpdateInfo->stepTimeoutInMinutes != AWS_IOT_JOBS_CANCEL_TIMEOUT ) )
    {
        if( pUpdateInfo->stepTimeoutInMinutes < 1 )
        {
            IotLogError( "Step timeout for Jobs %s must be at least 1.",
                         _pAwsIotJobsOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
        else if( pUpdateInfo->stepTimeoutInMinutes > JOBS_MAX_TIMEOUT )
        {
            IotLogError( "Step timeout for Jobs %s cannot exceed %d.",
                         _pAwsIotJobsOperationNames[ type ],
                         JOBS_MAX_TIMEOUT );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
    }

    /* Check status details. */
    if( pUpdateInfo->pStatusDetails != AWS_IOT_JOBS_NO_STATUS_DETAILS )
    {
        if( pUpdateInfo->statusDetailsLength == 0 )
        {
            IotLogError( "Status details length not set for Jobs %s.",
                         _pAwsIotJobsOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }

        if( pUpdateInfo->statusDetailsLength > JOBS_MAX_STATUS_DETAILS_LENGTH )
        {
            IotLogError( "Status details length for Jobs %s cannot exceed %d.",
                         _pAwsIotJobsOperationNames[ type ],
                         JOBS_MAX_STATUS_DETAILS_LENGTH );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

static int32_t _getCallbackIndex( _jobsCallbackType_t type,
                                  _jobsSubscription_t * pSubscription,
                                  const AwsIotJobsCallbackInfo_t * pCallbackInfo )
{
    int32_t callbackIndex = 0;

    /* Find the matching oldFunction. */
    if( pCallbackInfo->oldFunction != NULL )
    {
        for( callbackIndex = 0; callbackIndex < AWS_IOT_JOBS_NOTIFY_CALLBACKS; callbackIndex++ )
        {
            if( pSubscription->callbacks[ type ][ callbackIndex ].function == pCallbackInfo->oldFunction )
            {
                /* oldFunction found. */
                break;
            }
        }

        if( callbackIndex == AWS_IOT_JOBS_NOTIFY_CALLBACKS )
        {
            /* oldFunction not found. */
            callbackIndex = OLD_CALLBACK_NOT_FOUND;
        }
    }
    /* Find space for a new callback. */
    else
    {
        for( callbackIndex = 0; callbackIndex < AWS_IOT_JOBS_NOTIFY_CALLBACKS; callbackIndex++ )
        {
            if( pSubscription->callbacks[ type ][ callbackIndex ].function == NULL )
            {
                break;
            }
        }

        if( callbackIndex == AWS_IOT_JOBS_NOTIFY_CALLBACKS )
        {
            /* No memory for new callback. */
            callbackIndex = NO_SPACE_FOR_CALLBACK;
        }
    }

    return callbackIndex;
}

/*-----------------------------------------------------------*/

static AwsIotJobsError_t _setCallbackCommon( IotMqttConnection_t mqttConnection,
                                             _jobsCallbackType_t type,
                                             const char * pThingName,
                                             size_t thingNameLength,
                                             const AwsIotJobsCallbackInfo_t * pCallbackInfo )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_SUCCESS );
    bool subscriptionMutexLocked = false;
    _jobsSubscription_t * pSubscription = NULL;
    int32_t callbackIndex = 0;

    /* Check that AwsIotJobs_Init was called. */
    if( _checkInit() == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_NOT_INITIALIZED );
    }

    /* Validate Thing Name. */
    if( AwsIot_ValidateThingName( pThingName, thingNameLength ) == false )
    {
        IotLogError( "Thing Name for Jobs %s callback is not valid.",
                     _pAwsIotJobsCallbackNames[ type ] );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
    }

    /* Check that a callback parameter is provided. */
    if( pCallbackInfo == NULL )
    {
        IotLogError( "Callback parameter must be provided for Jobs %s callback.",
                     _pAwsIotJobsCallbackNames[ type ] );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
    }

    /* The oldFunction member must be set when removing or replacing a callback. */
    if( pCallbackInfo->function == NULL )
    {
        if( pCallbackInfo->oldFunction == NULL )
        {
            IotLogError( "Both oldFunction and function pointers cannot be NULL for Jobs %s callback.",
                         _pAwsIotJobsCallbackNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
    }

    IotLogInfo( "(%.*s) Modifying Jobs %s callback.",
                thingNameLength,
                pThingName,
                _pAwsIotJobsCallbackNames[ type ] );

    /* Lock the subscription list mutex to check for an existing subscription
     * object. */
    IotMutex_Lock( &_AwsIotJobsSubscriptionsMutex );
    subscriptionMutexLocked = true;

    /* Check for an existing subscription. This function will attempt to allocate
     * a new subscription if not found. */
    pSubscription = _AwsIotJobs_FindSubscription( pThingName, thingNameLength, true );

    if( pSubscription == NULL )
    {
        /* No existing subscription was found, and no new subscription could be
         * allocated. */
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_NO_MEMORY );
    }

    /* Get the index of the callback element to modify. */
    callbackIndex = _getCallbackIndex( type, pSubscription, pCallbackInfo );

    switch( callbackIndex )
    {
        case NO_SPACE_FOR_CALLBACK:
            IotLogError( "No memory for a new Jobs %s callback.",
                         _pAwsIotJobsCallbackNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_NO_MEMORY );

        case OLD_CALLBACK_NOT_FOUND:
            IotLogWarn( "Requested replacement function for Jobs %s callback not found.",
                        _pAwsIotJobsCallbackNames[ type ] );

            /* A subscription may have been allocated, but the callback operation can't
             * proceed. Check if the subscription should be removed. */
            _AwsIotJobs_RemoveSubscription( pSubscription, NULL );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );

        default:
            break;
    }

    /* Check for an existing callback. */
    if( pSubscription->callbacks[ type ][ callbackIndex ].function != NULL )
    {
        /* Replace existing callback. */
        if( pCallbackInfo->function != NULL )
        {
            IotLogInfo( "(%.*s) Found existing %s callback. Replacing callback.",
                        thingNameLength,
                        pThingName,
                        _pAwsIotJobsCallbackNames[ type ] );

            pSubscription->callbacks[ type ][ callbackIndex ] = *pCallbackInfo;
        }
        /* Remove existing callback. */
        else
        {
            IotLogInfo( "(%.*s) Removing existing %s callback.",
                        thingNameLength,
                        pThingName,
                        _pAwsIotJobsCallbackNames[ type ] );

            /* Clear the callback information and unsubscribe. */
            ( void ) memset( &( pSubscription->callbacks[ type ][ callbackIndex ] ),
                             0x00,
                             sizeof( AwsIotJobsCallbackInfo_t ) );
            ( void ) _modifyCallbackSubscriptions( mqttConnection,
                                                   type,
                                                   pSubscription,
                                                   IotMqtt_UnsubscribeSync );

            /* Check if this subscription object can be removed. */
            _AwsIotJobs_RemoveSubscription( pSubscription, NULL );
        }
    }
    /* No existing callback. */
    else
    {
        /* Add new callback. */
        IotLogInfo( "(%.*s) Adding new %s callback.",
                    thingNameLength,
                    pThingName,
                    _pAwsIotJobsCallbackNames[ type ] );

        status = _modifyCallbackSubscriptions( mqttConnection,
                                               type,
                                               pSubscription,
                                               IotMqtt_SubscribeSync );

        if( status == AWS_IOT_JOBS_SUCCESS )
        {
            pSubscription->callbacks[ type ][ callbackIndex ] = *pCallbackInfo;
        }
        else
        {
            /* On failure, check if this subscription can be removed. */
            _AwsIotJobs_RemoveSubscription( pSubscription, NULL );
        }
    }

    IOT_FUNCTION_CLEANUP_BEGIN();

    if( subscriptionMutexLocked == true )
    {
        IotMutex_Unlock( &_AwsIotJobsSubscriptionsMutex );
    }

    IotLogInfo( "(%.*s) Jobs %s callback operation complete with result %s.",
                thingNameLength,
                pThingName,
                _pAwsIotJobsCallbackNames[ type ],
                AwsIotJobs_strerror( status ) );

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

static AwsIotJobsError_t _modifyCallbackSubscriptions( IotMqttConnection_t mqttConnection,
                                                       _jobsCallbackType_t type,
                                                       _jobsSubscription_t * pSubscription,
                                                       AwsIotMqttFunction_t mqttOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_SUCCESS );
    int32_t i = 0;
    IotMqttError_t mqttStatus = IOT_MQTT_STATUS_PENDING;
    IotMqttSubscription_t subscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;
    AwsIotTopicInfo_t topicInfo = { 0 };
    char * pTopicFilter = NULL;
    uint16_t topicFilterLength = 0;

    /* Lookup table for Jobs callback suffixes. */
    const char * const pCallbackSuffix[ JOBS_CALLBACK_COUNT ] =
    {
        JOBS_NOTIFY_PENDING_CALLBACK_STRING, /* Notify pending callback. */
        JOBS_NOTIFY_NEXT_CALLBACK_STRING     /* Notify next callback. */
    };

    /* Lookup table for Jobs callback suffix lengths. */
    const uint16_t pCallbackSuffixLength[ JOBS_CALLBACK_COUNT ] =
    {
        JOBS_NOTIFY_PENDING_CALLBACK_STRING_LENGTH, /* Notify pending callback. */
        JOBS_NOTIFY_NEXT_CALLBACK_STRING_LENGTH     /* Notify next callback. */
    };

    /* Lookup table for Jobs callback function wrappers. */
    const AwsIotMqttCallbackFunction_t pCallbackWrapper[ JOBS_CALLBACK_COUNT ] =
    {
        _notifyPendingCallbackWrapper, /* Notify pending callback. */
        _notifyNextCallbackWrapper,    /* Notify next callback. */
    };

    /* MQTT operation may only be subscribe or unsubscribe. */
    AwsIotJobs_Assert( ( mqttOperation == IotMqtt_SubscribeSync ) ||
                       ( mqttOperation == IotMqtt_UnsubscribeSync ) );

    /* Check if any subscriptions are currently registered for this type. */
    for( i = 0; i < AWS_IOT_JOBS_NOTIFY_CALLBACKS; i++ )
    {
        if( pSubscription->callbacks[ type ][ i ].function != NULL )
        {
            /* No action is needed when another callback exists. */
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_SUCCESS );
        }
    }

    /* Use the subscription's topic buffer if available. */
    if( pSubscription->pTopicBuffer != NULL )
    {
        pTopicFilter = pSubscription->pTopicBuffer;
    }

    /* Generate the topic for the MQTT subscription. */
    topicInfo.pThingName = pSubscription->pThingName;
    topicInfo.thingNameLength = pSubscription->thingNameLength;
    topicInfo.longestSuffixLength = JOBS_LONGEST_SUFFIX_LENGTH;
    topicInfo.mallocString = AwsIotJobs_MallocString;
    topicInfo.pOperationName = pCallbackSuffix[ type ];
    topicInfo.operationNameLength = pCallbackSuffixLength[ type ];

    if( AwsIot_GenerateOperationTopic( &topicInfo,
                                       &pTopicFilter,
                                       &topicFilterLength ) == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_NO_MEMORY );
    }

    IotLogDebug( "%s subscription for %.*s",
                 mqttOperation == IotMqtt_SubscribeSync ? "Adding" : "Removing",
                 topicFilterLength,
                 pTopicFilter );

    /* Set the members of the MQTT subscription. */
    subscription.qos = IOT_MQTT_QOS_1;
    subscription.pTopicFilter = pTopicFilter;
    subscription.topicFilterLength = topicFilterLength;
    subscription.callback.pCallbackContext = NULL;
    subscription.callback.function = pCallbackWrapper[ type ];

    /* Call the MQTT operation function. */
    mqttStatus = mqttOperation( mqttConnection,
                                &subscription,
                                1,
                                0,
                                _AwsIotJobsMqttTimeoutMs );

    /* Check the result of the MQTT operation. */
    if( mqttStatus != IOT_MQTT_SUCCESS )
    {
        IotLogError( "Failed to %s callback for %.*s %s callback, error %s.",
                     mqttOperation == IotMqtt_SubscribeSync ? "subscribe to" : "unsubscribe from",
                     pSubscription->thingNameLength,
                     pSubscription->pThingName,
                     _pAwsIotJobsCallbackNames[ type ],
                     IotMqtt_strerror( mqttStatus ) );

        /* Convert the MQTT "NO MEMORY" error to a Jobs "NO MEMORY" error. */
        if( mqttStatus == IOT_MQTT_NO_MEMORY )
        {
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_NO_MEMORY );
        }
        else
        {
            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_MQTT_ERROR );
        }
    }

    IotLogDebug( "Successfully %s %.*s Jobs %s callback.",
                 mqttOperation == IotMqtt_SubscribeSync ? "subscribed to" : "unsubscribed from",
                 pSubscription->thingNameLength,
                 pSubscription->pThingName,
                 _pAwsIotJobsCallbackNames[ type ] );

    IOT_FUNCTION_CLEANUP_BEGIN();

    /* MQTT subscribe should check the subscription topic buffer. */
    if( mqttOperation == IotMqtt_SubscribeSync )
    {
        /* If the current subscription has no topic buffer, assign it the current
         * topic buffer. */
        if( pSubscription->pTopicBuffer == NULL )
        {
            pSubscription->pTopicBuffer = pTopicFilter;
        }
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

static void _notifyPendingCallbackWrapper( void * pArgument,
                                           IotMqttCallbackParam_t * pMessage )
{
    /* Silence warnings about unused parameters. */
    ( void ) pArgument;

    _callbackWrapperCommon( NOTIFY_PENDING_CALLBACK,
                            pMessage );
}

/*-----------------------------------------------------------*/

static void _notifyNextCallbackWrapper( void * pArgument,
                                        IotMqttCallbackParam_t * pMessage )
{
    /* Silence warnings about unused parameters. */
    ( void ) pArgument;

    _callbackWrapperCommon( NOTIFY_NEXT_CALLBACK,
                            pMessage );
}

/*-----------------------------------------------------------*/

static void _callbackWrapperCommon( _jobsCallbackType_t type,
                                    IotMqttCallbackParam_t * pMessage )
{
    int32_t callbackIndex = 0;
    AwsIotJobsCallbackInfo_t callbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
    AwsIotJobsCallbackParam_t callbackParam = { .callbackType = ( AwsIotJobsCallbackType_t ) 0 };
    _jobsSubscription_t * pSubscription = NULL;
    const char * pThingName = NULL;
    size_t thingNameLength = 0;

    /* Parse the Thing Name from the topic. */
    if( AwsIot_ParseThingName( pMessage->u.message.info.pTopicName,
                               pMessage->u.message.info.topicNameLength,
                               &pThingName,
                               &thingNameLength ) == false )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Search for a matching subscription. */
    IotMutex_Lock( &_AwsIotJobsSubscriptionsMutex );

    pSubscription = _AwsIotJobs_FindSubscription( pThingName,
                                                  thingNameLength,
                                                  false );

    if( pSubscription != NULL )
    {
        /* Increment callback reference count to prevent the subscription object from being
         * freed while callbacks are running. */
        pSubscription->callbackReferences++;
    }

    IotMutex_Unlock( &_AwsIotJobsSubscriptionsMutex );

    if( pSubscription != NULL )
    {
        /* Invoke all callbacks for this Thing. */
        for( callbackIndex = 0; callbackIndex < AWS_IOT_JOBS_NOTIFY_CALLBACKS; callbackIndex++ )
        {
            /* Copy the callback function and parameter, as it may be modified at any time. */
            IotMutex_Lock( &_AwsIotJobsSubscriptionsMutex );
            callbackInfo = pSubscription->callbacks[ type ][ callbackIndex ];
            IotMutex_Unlock( &_AwsIotJobsSubscriptionsMutex );

            if( callbackInfo.function != NULL )
            {
                /* Set the callback type. Jobs callbacks are enumerated after the operations. */
                callbackParam.callbackType = ( AwsIotJobsCallbackType_t ) ( type + JOBS_OPERATION_COUNT );

                /* Set the remaining members of the callback param. */
                callbackParam.mqttConnection = pMessage->mqttConnection;
                callbackParam.pThingName = pThingName;
                callbackParam.thingNameLength = thingNameLength;
                callbackParam.u.callback.pDocument = pMessage->u.message.info.pPayload;
                callbackParam.u.callback.documentLength = pMessage->u.message.info.payloadLength;

                /* Invoke the callback function. */
                callbackInfo.function( callbackInfo.pCallbackContext,
                                       &callbackParam );
            }
        }

        /* Callbacks are finished. Decrement reference count and check if subscription
         * object should be destroyed. */
        IotMutex_Lock( &_AwsIotJobsSubscriptionsMutex );

        pSubscription->callbackReferences--;
        AwsIotJobs_Assert( pSubscription->callbackReferences >= 0 );

        _AwsIotJobs_RemoveSubscription( pSubscription, NULL );

        IotMutex_Unlock( &_AwsIotJobsSubscriptionsMutex );
    }

    /* This function uses cleanup sections to exit on error. */
    IOT_FUNCTION_CLEANUP_BEGIN();
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_Init( uint32_t mqttTimeoutMs )
{
    AwsIotJobsError_t status = AWS_IOT_JOBS_SUCCESS;
    bool listInitStatus = false;

    if( _initCalled == 0 )
    {
        listInitStatus = AwsIot_InitLists( &_AwsIotJobsPendingOperations,
                                           &_AwsIotJobsSubscriptions,
                                           &_AwsIotJobsPendingOperationsMutex,
                                           &_AwsIotJobsSubscriptionsMutex );

        if( listInitStatus == false )
        {
            IotLogInfo( "Failed to create Jobs lists." );

            status = AWS_IOT_JOBS_INIT_FAILED;
        }
        else
        {
            /* Save the MQTT timeout option. */
            if( mqttTimeoutMs != 0 )
            {
                _AwsIotJobsMqttTimeoutMs = mqttTimeoutMs;
            }

            /* Set the flag that specifies initialization is complete. */
            _initCalled = 1;

            IotLogInfo( "Jobs library successfully initialized." );
        }
    }
    else
    {
        IotLogWarn( "AwsIotJobs_Init called with library already initialized." );
    }

    return status;
}

/*-----------------------------------------------------------*/

void AwsIotJobs_Cleanup( void )
{
    if( _initCalled == 1 )
    {
        _initCalled = 0;

        /* Remove and free all items in the Jobs pending operation list. */
        IotMutex_Lock( &_AwsIotJobsPendingOperationsMutex );
        IotListDouble_RemoveAll( &_AwsIotJobsPendingOperations,
                                 _AwsIotJobs_DestroyOperation,
                                 offsetof( _jobsOperation_t, link ) );
        IotMutex_Unlock( &_AwsIotJobsPendingOperationsMutex );

        /* Remove and free all items in the Jobs subscription list. */
        IotMutex_Lock( &_AwsIotJobsSubscriptionsMutex );
        IotListDouble_RemoveAll( &_AwsIotJobsSubscriptions,
                                 _AwsIotJobs_DestroySubscription,
                                 offsetof( _jobsSubscription_t, link ) );
        IotMutex_Unlock( &_AwsIotJobsSubscriptionsMutex );

        /* Restore the default MQTT timeout. */
        _AwsIotJobsMqttTimeoutMs = AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS;

        /* Destroy Jobs library mutexes. */
        IotMutex_Destroy( &_AwsIotJobsPendingOperationsMutex );
        IotMutex_Destroy( &_AwsIotJobsSubscriptionsMutex );

        IotLogInfo( "Jobs library cleanup done." );
    }
    else
    {
        IotLogWarn( "AwsIotJobs_Init was not called before AwsIotShadow_Cleanup." );
    }
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_GetPendingAsync( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                              uint32_t flags,
                                              const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                              AwsIotJobsOperation_t * const pGetPendingOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_STATUS_PENDING );
    _jobsOperation_t * pOperation = NULL;

    /* Check that AwsIotJobs_Init was called. */
    if( _checkInit() == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_NOT_INITIALIZED );
    }

    /* Check request info. */
    status = _validateRequestInfo( JOBS_GET_PENDING,
                                   pRequestInfo,
                                   flags,
                                   pCallbackInfo,
                                   pGetPendingOperation );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Allocate a new Jobs operation. */
    status = _AwsIotJobs_CreateOperation( JOBS_GET_PENDING,
                                          pRequestInfo,
                                          NULL,
                                          flags,
                                          pCallbackInfo,
                                          &pOperation );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        /* No memory for Jobs operation. */
        IOT_GOTO_CLEANUP();
    }

    /* Set the reference if provided. This must be done before the Jobs operation
     * is processed. */
    if( pGetPendingOperation != NULL )
    {
        *pGetPendingOperation = pOperation;
    }

    /* Process the Jobs operation. This subscribes to any required topics and
     * sends the MQTT message for the Jobs operation. */
    status = _AwsIotJobs_ProcessOperation( pRequestInfo, pOperation );

    /* If the Jobs operation failed, clear the now invalid reference. */
    if( ( status != AWS_IOT_JOBS_STATUS_PENDING ) && ( pGetPendingOperation != NULL ) )
    {
        *pGetPendingOperation = AWS_IOT_JOBS_OPERATION_INITIALIZER;
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_GetPendingSync( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                             uint32_t flags,
                                             uint32_t timeoutMs,
                                             AwsIotJobsResponse_t * const pJobsResponse )
{
    AwsIotJobsError_t status = AWS_IOT_JOBS_STATUS_PENDING;
    AwsIotJobsOperation_t getPendingOperation = AWS_IOT_JOBS_OPERATION_INITIALIZER;

    /* Set the waitable flag. */
    flags |= AWS_IOT_JOBS_FLAG_WAITABLE;

    /* Call the asynchronous Jobs Get Pending function. */
    status = AwsIotJobs_GetPendingAsync( pRequestInfo,
                                         flags,
                                         NULL,
                                         &getPendingOperation );

    /* Wait for the Jobs Get Pending operation to complete. */
    if( status == AWS_IOT_JOBS_STATUS_PENDING )
    {
        status = AwsIotJobs_Wait( getPendingOperation,
                                  timeoutMs,
                                  pJobsResponse );
    }

    return status;
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_StartNextAsync( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                             const AwsIotJobsUpdateInfo_t * pUpdateInfo,
                                             uint32_t flags,
                                             const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                             AwsIotJobsOperation_t * const pStartNextOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_STATUS_PENDING );
    _jobsOperation_t * pOperation = NULL;
    _jsonRequestContents_t requestContents = { 0 };

    /* Check that AwsIotJobs_Init was called. */
    if( _checkInit() == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_NOT_INITIALIZED );
    }

    /* Check request info. */
    status = _validateRequestInfo( JOBS_START_NEXT,
                                   pRequestInfo,
                                   flags,
                                   pCallbackInfo,
                                   pStartNextOperation );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Check update info. */
    status = _validateUpdateInfo( JOBS_START_NEXT,
                                  pUpdateInfo );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Allocate a new Jobs operation. */
    requestContents.pUpdateInfo = pUpdateInfo;

    status = _AwsIotJobs_CreateOperation( JOBS_START_NEXT,
                                          pRequestInfo,
                                          &requestContents,
                                          flags,
                                          pCallbackInfo,
                                          &pOperation );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        /* No memory for Jobs operation. */
        IOT_GOTO_CLEANUP();
    }

    /* Set the reference if provided. This must be done before the Jobs operation
     * is processed. */
    if( pStartNextOperation != NULL )
    {
        *pStartNextOperation = pOperation;
    }

    /* Process the Jobs operation. This subscribes to any required topics and
     * sends the MQTT message for the Jobs operation. */
    status = _AwsIotJobs_ProcessOperation( pRequestInfo, pOperation );

    /* If the Jobs operation failed, clear the now invalid reference. */
    if( ( status != AWS_IOT_JOBS_STATUS_PENDING ) && ( pStartNextOperation != NULL ) )
    {
        *pStartNextOperation = AWS_IOT_JOBS_OPERATION_INITIALIZER;
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_StartNextSync( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                            const AwsIotJobsUpdateInfo_t * pUpdateInfo,
                                            uint32_t flags,
                                            uint32_t timeoutMs,
                                            AwsIotJobsResponse_t * const pJobsResponse )
{
    AwsIotJobsError_t status = AWS_IOT_JOBS_STATUS_PENDING;
    AwsIotJobsOperation_t startNextOperation = AWS_IOT_JOBS_OPERATION_INITIALIZER;

    /* Set the waitable flag. */
    flags |= AWS_IOT_JOBS_FLAG_WAITABLE;

    /* Call the asynchronous Jobs Start Next function. */
    status = AwsIotJobs_StartNextAsync( pRequestInfo,
                                        pUpdateInfo,
                                        flags,
                                        NULL,
                                        &startNextOperation );

    /* Wait for the Jobs Start Next operation to complete. */
    if( status == AWS_IOT_JOBS_STATUS_PENDING )
    {
        status = AwsIotJobs_Wait( startNextOperation,
                                  timeoutMs,
                                  pJobsResponse );
    }

    return status;
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_DescribeAsync( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                            int32_t executionNumber,
                                            bool includeJobDocument,
                                            uint32_t flags,
                                            const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                            AwsIotJobsOperation_t * const pDescribeOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_STATUS_PENDING );
    _jobsOperation_t * pOperation = NULL;
    _jsonRequestContents_t requestContents = { 0 };

    /* Check that AwsIotJobs_Init was called. */
    if( _checkInit() == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_NOT_INITIALIZED );
    }

    /* Check request info. */
    status = _validateRequestInfo( JOBS_DESCRIBE,
                                   pRequestInfo,
                                   flags,
                                   pCallbackInfo,
                                   pDescribeOperation );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Allocate a new Jobs operation. */
    requestContents.describe.executionNumber = executionNumber;
    requestContents.describe.includeJobDocument = includeJobDocument;

    status = _AwsIotJobs_CreateOperation( JOBS_DESCRIBE,
                                          pRequestInfo,
                                          &requestContents,
                                          flags,
                                          pCallbackInfo,
                                          &pOperation );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        /* No memory for Jobs operation. */
        IOT_GOTO_CLEANUP();
    }

    /* Set the reference if provided. This must be done before the Jobs operation
     * is processed. */
    if( pDescribeOperation != NULL )
    {
        *pDescribeOperation = pOperation;
    }

    /* Process the Jobs operation. This subscribes to any required topics and
     * sends the MQTT message for the Jobs operation. */
    status = _AwsIotJobs_ProcessOperation( pRequestInfo, pOperation );

    /* If the Jobs operation failed, clear the now invalid reference. */
    if( ( status != AWS_IOT_JOBS_STATUS_PENDING ) && ( pDescribeOperation != NULL ) )
    {
        *pDescribeOperation = AWS_IOT_JOBS_OPERATION_INITIALIZER;
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_DescribeSync( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                           int32_t executionNumber,
                                           bool includeJobDocument,
                                           uint32_t flags,
                                           uint32_t timeoutMs,
                                           AwsIotJobsResponse_t * const pJobsResponse )
{
    AwsIotJobsError_t status = AWS_IOT_JOBS_STATUS_PENDING;
    AwsIotJobsOperation_t describeOperation = AWS_IOT_JOBS_OPERATION_INITIALIZER;

    /* Set the waitable flag. */
    flags |= AWS_IOT_JOBS_FLAG_WAITABLE;

    /* Call the asynchronous Jobs Describe function. */
    status = AwsIotJobs_DescribeAsync( pRequestInfo,
                                       executionNumber,
                                       includeJobDocument,
                                       flags,
                                       NULL,
                                       &describeOperation );

    /* Wait for the Jobs Describe operation to complete. */
    if( status == AWS_IOT_JOBS_STATUS_PENDING )
    {
        status = AwsIotJobs_Wait( describeOperation,
                                  timeoutMs,
                                  pJobsResponse );
    }

    return status;
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_UpdateAsync( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                          const AwsIotJobsUpdateInfo_t * pUpdateInfo,
                                          uint32_t flags,
                                          const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                          AwsIotJobsOperation_t * const pUpdateOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_STATUS_PENDING );
    _jobsOperation_t * pOperation = NULL;
    _jsonRequestContents_t requestContents = { 0 };

    /* Check that AwsIotJobs_Init was called. */
    if( _checkInit() == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_NOT_INITIALIZED );
    }

    /* Check request info. */
    status = _validateRequestInfo( JOBS_UPDATE,
                                   pRequestInfo,
                                   flags,
                                   pCallbackInfo,
                                   pUpdateOperation );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Check update info. */
    status = _validateUpdateInfo( JOBS_UPDATE,
                                  pUpdateInfo );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Allocate a new Jobs operation. */
    requestContents.pUpdateInfo = pUpdateInfo;

    status = _AwsIotJobs_CreateOperation( JOBS_UPDATE,
                                          pRequestInfo,
                                          &requestContents,
                                          flags,
                                          pCallbackInfo,
                                          &pOperation );

    if( status != AWS_IOT_JOBS_SUCCESS )
    {
        /* No memory for Jobs operation. */
        IOT_GOTO_CLEANUP();
    }

    /* Set the reference if provided. This must be done before the Jobs operation
     * is processed. */
    if( pUpdateOperation != NULL )
    {
        *pUpdateOperation = pOperation;
    }

    /* Process the Jobs operation. This subscribes to any required topics and
     * sends the MQTT message for the Jobs operation. */
    status = _AwsIotJobs_ProcessOperation( pRequestInfo, pOperation );

    /* If the Jobs operation failed, clear the now invalid reference. */
    if( ( status != AWS_IOT_JOBS_STATUS_PENDING ) && ( pUpdateOperation != NULL ) )
    {
        *pUpdateOperation = AWS_IOT_JOBS_OPERATION_INITIALIZER;
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_UpdateSync( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                         const AwsIotJobsUpdateInfo_t * pUpdateInfo,
                                         uint32_t flags,
                                         uint32_t timeoutMs,
                                         AwsIotJobsResponse_t * const pJobsResponse )
{
    AwsIotJobsError_t status = AWS_IOT_JOBS_STATUS_PENDING;
    AwsIotJobsOperation_t updateOperation = AWS_IOT_JOBS_OPERATION_INITIALIZER;

    /* Set the waitable flag. */
    flags |= AWS_IOT_JOBS_FLAG_WAITABLE;

    /* Call the asynchronous Jobs Update function. */
    status = AwsIotJobs_UpdateAsync( pRequestInfo,
                                     pUpdateInfo,
                                     flags,
                                     NULL,
                                     &updateOperation );

    /* Wait for the Jobs Update operation to complete. */
    if( status == AWS_IOT_JOBS_STATUS_PENDING )
    {
        status = AwsIotJobs_Wait( updateOperation,
                                  timeoutMs,
                                  pJobsResponse );
    }

    return status;
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_Wait( AwsIotJobsOperation_t operation,
                                   uint32_t timeoutMs,
                                   AwsIotJobsResponse_t * const pJobsResponse )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_STATUS_PENDING );

    /* Check that AwsIotJobs_Init was called. */
    if( _checkInit() == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_NOT_INITIALIZED );
    }

    /* Check that reference is set. */
    if( operation == NULL )
    {
        IotLogError( "Operation reference cannot be NULL." );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
    }

    /* Check that reference is waitable. */
    if( ( operation->flags & AWS_IOT_JOBS_FLAG_WAITABLE ) == 0 )
    {
        IotLogError( "Operation is not waitable." );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
    }

    /* Check that output parameter is set. */
    if( pJobsResponse == NULL )
    {
        IotLogError( "Output Jobs response parameter must be set for Jobs %s.",
                     _pAwsIotJobsOperationNames[ operation->type ] );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
    }

    /* Wait for a response to the Jobs operation. */
    if( IotSemaphore_TimedWait( &( operation->notify.waitSemaphore ),
                                timeoutMs ) == true )
    {
        status = operation->status;
    }
    else
    {
        status = AWS_IOT_JOBS_TIMEOUT;
    }

    /* Remove the completed operation from the pending operation list. */
    IotMutex_Lock( &( _AwsIotJobsPendingOperationsMutex ) );
    IotListDouble_Remove( &( operation->link ) );
    IotMutex_Unlock( &( _AwsIotJobsPendingOperationsMutex ) );

    /* Decrement the reference count. This also removes subscriptions if the
     * count reaches 0. */
    IotMutex_Lock( &_AwsIotJobsSubscriptionsMutex );
    _AwsIotJobs_DecrementReferences( operation,
                                     operation->pSubscription->pTopicBuffer,
                                     NULL );
    IotMutex_Unlock( &_AwsIotJobsSubscriptionsMutex );

    /* Set the output parameters. Jobs responses are available on success or
     * when the Jobs service returns an error document. */
    if( ( status == AWS_IOT_JOBS_SUCCESS ) || ( status > AWS_IOT_JOBS_INVALID_TOPIC ) )
    {
        AwsIotJobs_Assert( operation->pJobsResponse != NULL );
        AwsIotJobs_Assert( operation->jobsResponseLength > 0 );

        pJobsResponse->pJobsResponse = operation->pJobsResponse;
        pJobsResponse->jobsResponseLength = operation->jobsResponseLength;
    }

    /* Destroy the Jobs operation. */
    _AwsIotJobs_DestroyOperation( operation );

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_SetNotifyPendingCallback( IotMqttConnection_t mqttConnection,
                                                       const char * pThingName,
                                                       size_t thingNameLength,
                                                       uint32_t flags,
                                                       const AwsIotJobsCallbackInfo_t * pNotifyPendingCallback )
{
    /* Flags are not currently used by this function. */
    ( void ) flags;

    return _setCallbackCommon( mqttConnection,
                               NOTIFY_PENDING_CALLBACK,
                               pThingName,
                               thingNameLength,
                               pNotifyPendingCallback );
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_SetNotifyNextCallback( IotMqttConnection_t mqttConnection,
                                                    const char * pThingName,
                                                    size_t thingNameLength,
                                                    uint32_t flags,
                                                    const AwsIotJobsCallbackInfo_t * pNotifyNextCallback )
{
    /* Flags are not currently used by this function. */
    ( void ) flags;

    return _setCallbackCommon( mqttConnection,
                               NOTIFY_NEXT_CALLBACK,
                               pThingName,
                               thingNameLength,
                               pNotifyNextCallback );
}

/*-----------------------------------------------------------*/

const char * AwsIotJobs_strerror( AwsIotJobsError_t status )
{
    const char * pMessage = NULL;

    switch( status )
    {
        case AWS_IOT_JOBS_SUCCESS:
            pMessage = "SUCCESS";
            break;

        case AWS_IOT_JOBS_STATUS_PENDING:
            pMessage = "STATUS PENDING";
            break;

        case AWS_IOT_JOBS_INIT_FAILED:
            pMessage = "INIT FAILED";
            break;

        case AWS_IOT_JOBS_BAD_PARAMETER:
            pMessage = "BAD PARAMETER";
            break;

        case AWS_IOT_JOBS_NO_MEMORY:
            pMessage = "NO MEMORY";
            break;

        case AWS_IOT_JOBS_MQTT_ERROR:
            pMessage = "MQTT ERROR";
            break;

        case AWS_IOT_JOBS_BAD_RESPONSE:
            pMessage = "BAD RESPONSE";
            break;

        case AWS_IOT_JOBS_TIMEOUT:
            pMessage = "TIMEOUT";
            break;

        case AWS_IOT_JOBS_NOT_INITIALIZED:
            pMessage = "NOT INITIALIZED";
            break;

        case AWS_IOT_JOBS_INVALID_TOPIC:
            pMessage = "FAILED: INVALID TOPIC";
            break;

        case AWS_IOT_JOBS_INVALID_JSON:
            pMessage = "FAILED: INVALID JSON";
            break;

        case AWS_IOT_JOBS_INVALID_REQUEST:
            pMessage = "FAILED: INVALID REQUEST";
            break;

        case AWS_IOT_JOBS_INVALID_STATE:
            pMessage = "FAILED: INVALID STATE TRANSITION";
            break;

        case AWS_IOT_JOBS_NOT_FOUND:
            pMessage = "FAILED: NOT FOUND";
            break;

        case AWS_IOT_JOBS_VERSION_MISMATCH:
            pMessage = "FAILED: VERSION MISMATCH";
            break;

        case AWS_IOT_JOBS_INTERNAL_ERROR:
            pMessage = "FAILED: INTERNAL ERROR";
            break;

        case AWS_IOT_JOBS_THROTTLED:
            pMessage = "FAILED: THROTTLED";
            break;

        case AWS_IOT_JOBS_TERMINAL_STATE:
            pMessage = "FAILED: TERMINAL STATE";
            break;

        default:
            pMessage = "INVALID STATUS";
            break;
    }

    return pMessage;
}

/*-----------------------------------------------------------*/

const char * AwsIotJobs_StateName( AwsIotJobState_t state )
{
    const char * pMessage = NULL;

    switch( state )
    {
        case AWS_IOT_JOB_STATE_QUEUED:
            pMessage = "QUEUED";
            break;

        case AWS_IOT_JOB_STATE_IN_PROGRESS:
            pMessage = "IN PROGRESS";
            break;

        case AWS_IOT_JOB_STATE_FAILED:
            pMessage = "FAILED";
            break;

        case AWS_IOT_JOB_STATE_SUCCEEDED:
            pMessage = "SUCCEEDED";
            break;

        case AWS_IOT_JOB_STATE_CANCELED:
            pMessage = "CANCELED";
            break;

        case AWS_IOT_JOB_STATE_TIMED_OUT:
            pMessage = "TIMED OUT";
            break;

        case AWS_IOT_JOB_STATE_REJECTED:
            pMessage = "REJECTED";
            break;

        case AWS_IOT_JOB_STATE_REMOVED:
            pMessage = "REMOVED";
            break;

        default:
            pMessage = "INVALID STATE";
            break;
    }

    return pMessage;
}

/*-----------------------------------------------------------*/
