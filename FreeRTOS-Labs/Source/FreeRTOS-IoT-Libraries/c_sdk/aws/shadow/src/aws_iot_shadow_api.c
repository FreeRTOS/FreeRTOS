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
 * @file aws_iot_shadow_api.c
 * @brief Implements the user-facing functions of the Shadow library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* Shadow internal include. */
#include "private/aws_iot_shadow_internal.h"

/* Error handling include. */
#include "iot_error.h"

/* Platform layer includes. */
#include "platform/iot_threads.h"

/* MQTT include. */
#include "iot_mqtt.h"

/* Validate Shadow configuration settings. */
#if AWS_IOT_SHADOW_ENABLE_ASSERTS != 0 && AWS_IOT_SHADOW_ENABLE_ASSERTS != 1
    #error "AWS_IOT_SHADOW_ENABLE_ASSERTS must be 0 or 1."
#endif
#if AWS_IOT_SHADOW_DEFAULT_MQTT_TIMEOUT_MS <= 0
    #error "AWS_IOT_SHADOW_DEFAULT_MQTT_TIMEOUT_MS cannot be 0 or negative."
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Check if the library is initialized.
 *
 * @return `true` if AwsIotShadow_Init was called; `false` otherwise.
 */
static bool _checkInit( void );

/**
 * @brief Checks Thing Name and flags parameters passed to Shadow API functions.
 *
 * @param[in] type The Shadow API function type.
 * @param[in] pThingName Thing Name passed to Shadow API function.
 * @param[in] thingNameLength Length of `pThingName`.
 * @param[in] flags Flags passed to Shadow API function.
 * @param[in] pCallbackInfo Callback info passed to Shadow API function.
 * @param[in] pOperation Operation reference pointer passed to Shadow API function.
 *
 * @return #AWS_IOT_SHADOW_SUCCESS or #AWS_IOT_SHADOW_BAD_PARAMETER.
 */
static AwsIotShadowError_t _validateThingNameFlags( _shadowOperationType_t type,
                                                    const char * pThingName,
                                                    size_t thingNameLength,
                                                    uint32_t flags,
                                                    const AwsIotShadowCallbackInfo_t * pCallbackInfo,
                                                    const AwsIotShadowOperation_t * pOperation );

/**
 * @brief Checks document info parameter passed to Shadow API functions.
 *
 * @param[in] type The Shadow API function type.
 * @param[in] flags Flags passed to Shadow API function.
 * @param[in] pDocumentInfo Document info passed to Shadow API function.
 *
 * @return #AWS_IOT_SHADOW_SUCCESS or #AWS_IOT_SHADOW_BAD_PARAMETER.
 */
static AwsIotShadowError_t _validateDocumentInfo( _shadowOperationType_t type,
                                                  uint32_t flags,
                                                  const AwsIotShadowDocumentInfo_t * pDocumentInfo );

/**
 * @brief Common function for setting Shadow callbacks.
 *
 * @param[in] mqttConnection The MQTT connection to use.
 * @param[in] type Type of Shadow callback.
 * @param[in] pThingName Thing Name for Shadow callback.
 * @param[in] thingNameLength Length of `pThingName`.
 * @param[in] pCallbackInfo Callback information to set.
 *
 * @return #AWS_IOT_SHADOW_SUCCESS, #AWS_IOT_SHADOW_BAD_PARAMETER,
 * #AWS_IOT_SHADOW_NO_MEMORY, or #AWS_IOT_SHADOW_MQTT_ERROR.
 */
static AwsIotShadowError_t _setCallbackCommon( IotMqttConnection_t mqttConnection,
                                               _shadowCallbackType_t type,
                                               const char * pThingName,
                                               size_t thingNameLength,
                                               const AwsIotShadowCallbackInfo_t * pCallbackInfo );

/**
 * @brief Change the subscriptions for Shadow callbacks, either by subscribing
 * or unsubscribing.
 *
 * @param[in] mqttConnection The MQTT connection to use.
 * @param[in] type Type of Shadow callback.
 * @param[in] pSubscription Shadow subscriptions object for callback.
 * @param[in] mqttOperation Either @ref mqtt_function_subscribesync or
 * @ref mqtt_function_unsubscribesync.
 *
 * @return #AWS_IOT_SHADOW_SUCCESS, #AWS_IOT_SHADOW_NO_MEMORY, or
 * #AWS_IOT_SHADOW_MQTT_ERROR.
 */
static AwsIotShadowError_t _modifyCallbackSubscriptions( IotMqttConnection_t mqttConnection,
                                                         _shadowCallbackType_t type,
                                                         _shadowSubscription_t * pSubscription,
                                                         AwsIotMqttFunction_t mqttOperation );

/**
 * @brief Common function for incoming Shadow callbacks.
 *
 * @param[in] type Shadow callback type.
 * @param[in] pMessage The received Shadow callback document (as an MQTT PUBLISH
 * message).
 */
static void _callbackWrapperCommon( _shadowCallbackType_t type,
                                    IotMqttCallbackParam_t * pMessage );

/**
 * @brief Invoked when a document is received on the Shadow DELTA callback.
 *
 * @param[in] pArgument Ignored.
 * @param[in] pMessage The received DELTA document (as an MQTT PUBLISH message).
 */
static void _deltaCallbackWrapper( void * pArgument,
                                   IotMqttCallbackParam_t * pMessage );

/**
 * @brief Invoked when a document is received on the Shadow UPDATED callback.
 *
 * @param[in] pArgument Ignored.
 * @param[in] pMessage The received UPDATED document (as an MQTT PUBLISH message).
 */
static void _updatedCallbackWrapper( void * pArgument,
                                     IotMqttCallbackParam_t * pMessage );

/*-----------------------------------------------------------*/

/**
 * @brief Tracks whether @ref shadow_function_init has been called.
 *
 * API functions will fail if @ref shadow_function_init was not called.
 */
static uint32_t _initCalled = 0;

/**
 * @brief Timeout used for MQTT operations.
 */
uint32_t _AwsIotShadowMqttTimeoutMs = AWS_IOT_SHADOW_DEFAULT_MQTT_TIMEOUT_MS;

#if LIBRARY_LOG_LEVEL > IOT_LOG_NONE

/**
 * @brief Printable names for the Shadow callbacks.
 */
    const char * const _pAwsIotShadowCallbackNames[] =
    {
        "DELTA",
        "UPDATED"
    };
#endif

/*-----------------------------------------------------------*/

static bool _checkInit( void )
{
    bool status = true;

    if( _initCalled == 0 )
    {
        IotLogError( "AwsIotShadow_Init was not called." );

        status = false;
    }

    return status;
}

/*-----------------------------------------------------------*/

static AwsIotShadowError_t _validateThingNameFlags( _shadowOperationType_t type,
                                                    const char * pThingName,
                                                    size_t thingNameLength,
                                                    uint32_t flags,
                                                    const AwsIotShadowCallbackInfo_t * pCallbackInfo,
                                                    const AwsIotShadowOperation_t * pOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotShadowError_t, AWS_IOT_SHADOW_SUCCESS );

    /* Type is not used when logging is disabled. */
    ( void ) type;

    /* Check Thing Name. */
    if( AwsIot_ValidateThingName( pThingName, thingNameLength ) == false )
    {
        IotLogError( "Thing Name for Shadow %s is not valid.",
                     _pAwsIotShadowOperationNames[ type ] );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_BAD_PARAMETER );
    }

    /* Check the waitable operation flag. */
    if( ( flags & AWS_IOT_SHADOW_FLAG_WAITABLE ) == AWS_IOT_SHADOW_FLAG_WAITABLE )
    {
        /* Check that a reference pointer is provided for a waitable operation. */
        if( pOperation == NULL )
        {
            IotLogError( "Reference must be set for a waitable Shadow %s.",
                         _pAwsIotShadowOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_BAD_PARAMETER );
        }

        /* A callback should not be set for a waitable operation. */
        if( pCallbackInfo != NULL )
        {
            IotLogError( "Callback should not be set for a waitable Shadow %s.",
                         _pAwsIotShadowOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_BAD_PARAMETER );
        }
    }

    /* A callback info must be passed to a non-waitable GET. */
    if( ( type == SHADOW_GET ) &&
        ( ( flags & AWS_IOT_SHADOW_FLAG_WAITABLE ) == 0 ) &&
        ( pCallbackInfo == NULL ) )
    {
        IotLogError( "Callback info must be provided for non-waitable Shadow GET." );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_BAD_PARAMETER );
    }

    /* Check that a callback function is set. */
    if( ( pCallbackInfo != NULL ) &&
        ( pCallbackInfo->function == NULL ) )
    {
        IotLogError( "Callback function must be set for Shadow %s callback.",
                     _pAwsIotShadowOperationNames[ type ] );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_BAD_PARAMETER );
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

static AwsIotShadowError_t _validateDocumentInfo( _shadowOperationType_t type,
                                                  uint32_t flags,
                                                  const AwsIotShadowDocumentInfo_t * pDocumentInfo )
{
    IOT_FUNCTION_ENTRY( AwsIotShadowError_t, AWS_IOT_SHADOW_SUCCESS );

    /* This function should only be called for Shadow GET or UPDATE. */
    AwsIotShadow_Assert( ( type == SHADOW_GET ) || ( type == SHADOW_UPDATE ) );

    /* Check QoS. */
    if( pDocumentInfo->qos != IOT_MQTT_QOS_0 )
    {
        if( pDocumentInfo->qos != IOT_MQTT_QOS_1 )
        {
            IotLogError( "QoS for Shadow %d must be 0 or 1.",
                         _pAwsIotShadowOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_BAD_PARAMETER );
        }
    }

    /* Check the retry parameters. */
    if( pDocumentInfo->retryLimit > 0 )
    {
        if( pDocumentInfo->retryMs == 0 )
        {
            IotLogError( "Retry time of Shadow %s must be positive.",
                         _pAwsIotShadowOperationNames[ type ] );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_BAD_PARAMETER );
        }
    }

    /* Check members relevant to a Shadow GET. */
    if( type == SHADOW_GET )
    {
        /* Check memory allocation function for waitable GET. */
        if( ( ( flags & AWS_IOT_SHADOW_FLAG_WAITABLE ) == AWS_IOT_SHADOW_FLAG_WAITABLE ) &&
            ( pDocumentInfo->u.get.mallocDocument == NULL ) )
        {
            IotLogError( "Memory allocation function must be set for waitable Shadow GET." );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_BAD_PARAMETER );
        }
    }
    /* Check members relevant to a Shadow UPDATE. */
    else
    {
        /* Check UPDATE document pointer and length. */
        if( ( pDocumentInfo->u.update.pUpdateDocument == NULL ) ||
            ( pDocumentInfo->u.update.updateDocumentLength == 0 ) )
        {
            IotLogError( "Shadow document for Shadow UPDATE cannot be NULL or"
                         " have length 0." );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_BAD_PARAMETER );
        }
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

static AwsIotShadowError_t _setCallbackCommon( IotMqttConnection_t mqttConnection,
                                               _shadowCallbackType_t type,
                                               const char * pThingName,
                                               size_t thingNameLength,
                                               const AwsIotShadowCallbackInfo_t * pCallbackInfo )
{
    IOT_FUNCTION_ENTRY( AwsIotShadowError_t, AWS_IOT_SHADOW_SUCCESS );
    bool subscriptionMutexLocked = false;
    _shadowSubscription_t * pSubscription = NULL;

    /* Check that AwsIotShadow_Init was called. */
    if( _checkInit() == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_NOT_INITIALIZED );
    }

    /* Check parameters. */
    status = _validateThingNameFlags( ( _shadowOperationType_t ) ( type + SHADOW_OPERATION_COUNT ),
                                      pThingName,
                                      thingNameLength,
                                      0,
                                      pCallbackInfo,
                                      NULL );

    if( status != AWS_IOT_SHADOW_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    IotLogInfo( "(%.*s) Modifying Shadow %s callback.",
                thingNameLength,
                pThingName,
                _pAwsIotShadowCallbackNames[ type ] );

    /* Lock the subscription list mutex to check for an existing subscription
     * object. */
    IotMutex_Lock( &( _AwsIotShadowSubscriptionsMutex ) );
    subscriptionMutexLocked = true;

    /* Check for an existing subscription. This function will attempt to allocate
     * a new subscription if not found. */
    pSubscription = _AwsIotShadow_FindSubscription( pThingName,
                                                    thingNameLength,
                                                    true );

    if( pSubscription == NULL )
    {
        /* No existing subscription was found, and no new subscription could be
         * allocated. */
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_NO_MEMORY );
    }

    /* Check for an existing callback. */
    if( pSubscription->callbacks[ type ].function != NULL )
    {
        /* Replace existing callback. */
        if( pCallbackInfo != NULL )
        {
            IotLogInfo( "(%.*s) Found existing %s callback. Replacing callback.",
                        thingNameLength,
                        pThingName,
                        _pAwsIotShadowCallbackNames[ type ] );

            pSubscription->callbacks[ type ] = *pCallbackInfo;
        }
        /* Remove existing callback. */
        else
        {
            IotLogInfo( "(%.*s) Removing existing %s callback.",
                        thingNameLength,
                        pThingName,
                        _pAwsIotShadowCallbackNames[ type ] );

            /* Unsubscribe, then clear the callback information. */
            ( void ) _modifyCallbackSubscriptions( mqttConnection,
                                                   type,
                                                   pSubscription,
                                                   IotMqtt_UnsubscribeSync );
            ( void ) memset( &( pSubscription->callbacks[ type ] ),
                             0x00,
                             sizeof( AwsIotShadowCallbackInfo_t ) );

            /* Check if this subscription object can be removed. */
            _AwsIotShadow_RemoveSubscription( pSubscription, NULL );
        }
    }
    /* No existing callback. */
    else
    {
        /* Add new callback. */
        if( pCallbackInfo != NULL )
        {
            IotLogInfo( "(%.*s) Adding new %s callback.",
                        thingNameLength,
                        pThingName,
                        _pAwsIotShadowCallbackNames[ type ] );

            status = _modifyCallbackSubscriptions( mqttConnection,
                                                   type,
                                                   pSubscription,
                                                   IotMqtt_SubscribeSync );

            if( status == AWS_IOT_SHADOW_SUCCESS )
            {
                pSubscription->callbacks[ type ] = *pCallbackInfo;
            }
            else
            {
                /* On failure, check if this subscription can be removed. */
                _AwsIotShadow_RemoveSubscription( pSubscription, NULL );
            }
        }
        /* Do nothing; set return value to success. */
        else
        {
            status = AWS_IOT_SHADOW_SUCCESS;
        }
    }

    IOT_FUNCTION_CLEANUP_BEGIN();

    if( subscriptionMutexLocked == true )
    {
        IotMutex_Unlock( &( _AwsIotShadowSubscriptionsMutex ) );
    }

    IotLogInfo( "(%.*s) Shadow %s callback operation complete with result %s.",
                thingNameLength,
                pThingName,
                _pAwsIotShadowCallbackNames[ type ],
                AwsIotShadow_strerror( status ) );

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

static AwsIotShadowError_t _modifyCallbackSubscriptions( IotMqttConnection_t mqttConnection,
                                                         _shadowCallbackType_t type,
                                                         _shadowSubscription_t * pSubscription,
                                                         AwsIotMqttFunction_t mqttOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotShadowError_t, AWS_IOT_SHADOW_SUCCESS );
    IotMqttError_t mqttStatus = IOT_MQTT_STATUS_PENDING;
    IotMqttSubscription_t subscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;
    char * pTopicFilter = NULL;
    uint16_t operationTopicLength = 0;

    /* Lookup table for Shadow callback suffixes. */
    const char * const pCallbackSuffix[ SHADOW_CALLBACK_COUNT ] =
    {
        SHADOW_DELTA_SUFFIX,  /* Delta callback. */
        SHADOW_UPDATED_SUFFIX /* Updated callback. */
    };

    /* Lookup table for Shadow callback suffix lengths. */
    const uint16_t pCallbackSuffixLength[ SHADOW_CALLBACK_COUNT ] =
    {
        SHADOW_DELTA_SUFFIX_LENGTH,  /* Delta callback. */
        SHADOW_UPDATED_SUFFIX_LENGTH /* Updated callback. */
    };

    /* Lookup table for Shadow callback function wrappers. */
    const AwsIotMqttCallbackFunction_t pCallbackWrapper[ SHADOW_CALLBACK_COUNT ] =
    {
        _deltaCallbackWrapper,   /* Delta callback. */
        _updatedCallbackWrapper, /* Updated callback. */
    };

    /* MQTT operation may only be subscribe or unsubscribe. */
    AwsIotShadow_Assert( ( mqttOperation == IotMqtt_SubscribeSync ) ||
                         ( mqttOperation == IotMqtt_UnsubscribeSync ) );

    /* Use the subscription's topic buffer if available. */
    if( pSubscription->pTopicBuffer != NULL )
    {
        pTopicFilter = pSubscription->pTopicBuffer;
    }

    /* Generate the prefix portion of the Shadow callback topic filter. Both
     * callbacks share the same callback as the Shadow Update operation. */
    status = _AwsIotShadow_GenerateShadowTopic( SHADOW_UPDATE,
                                                pSubscription->pThingName,
                                                pSubscription->thingNameLength,
                                                &pTopicFilter,
                                                &operationTopicLength );

    if( status != AWS_IOT_SHADOW_SUCCESS )
    {
        IOT_GOTO_CLEANUP();
    }

    /* Place the callback suffix in the topic filter. */
    ( void ) memcpy( pTopicFilter + operationTopicLength,
                     pCallbackSuffix[ type ],
                     pCallbackSuffixLength[ type ] );

    IotLogDebug( "%s subscription for %.*s",
                 mqttOperation == IotMqtt_SubscribeSync ? "Adding" : "Removing",
                 operationTopicLength + pCallbackSuffixLength[ type ],
                 pTopicFilter );

    /* Set the members of the MQTT subscription. */
    subscription.qos = IOT_MQTT_QOS_1;
    subscription.pTopicFilter = pTopicFilter;
    subscription.topicFilterLength = ( uint16_t ) ( operationTopicLength + pCallbackSuffixLength[ type ] );
    subscription.callback.pCallbackContext = NULL;
    subscription.callback.function = pCallbackWrapper[ type ];

    /* Call the MQTT operation function. */
    mqttStatus = mqttOperation( mqttConnection,
                                &subscription,
                                1,
                                0,
                                _AwsIotShadowMqttTimeoutMs );

    /* Check the result of the MQTT operation. */
    if( mqttStatus != IOT_MQTT_SUCCESS )
    {
        IotLogError( "Failed to %s callback for %.*s %s callback, error %s.",
                     mqttOperation == IotMqtt_SubscribeSync ? "subscribe to" : "unsubscribe from",
                     pSubscription->thingNameLength,
                     pSubscription->pThingName,
                     _pAwsIotShadowCallbackNames[ type ],
                     IotMqtt_strerror( mqttStatus ) );

        /* Convert the MQTT "NO MEMORY" error to a Shadow "NO MEMORY" error. */
        IOT_SET_AND_GOTO_CLEANUP( SHADOW_CONVERT_STATUS_CODE_MQTT_TO_SHADOW( mqttStatus ) );
    }

    IotLogDebug( "Successfully %s %.*s Shadow %s callback.",
                 mqttOperation == IotMqtt_SubscribeSync ? "subscribed to" : "unsubscribed from",
                 pSubscription->thingNameLength,
                 pSubscription->pThingName,
                 _pAwsIotShadowCallbackNames[ type ] );

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

static void _callbackWrapperCommon( _shadowCallbackType_t type,
                                    IotMqttCallbackParam_t * pMessage )
{
    AwsIotShadowCallbackInfo_t callbackInfo = AWS_IOT_SHADOW_CALLBACK_INFO_INITIALIZER;
    AwsIotShadowCallbackParam_t callbackParam = { .callbackType = ( AwsIotShadowCallbackType_t ) 0 };
    _shadowSubscription_t * pSubscription = NULL;
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
    IotMutex_Lock( &_AwsIotShadowSubscriptionsMutex );

    pSubscription = _AwsIotShadow_FindSubscription( pThingName,
                                                    thingNameLength,
                                                    false );

    if( pSubscription == NULL )
    {
        /* No subscription found. */
        IotMutex_Unlock( &_AwsIotShadowSubscriptionsMutex );
        IOT_GOTO_CLEANUP();
    }

    /* Ensure that a callback function is set. */
    AwsIotShadow_Assert( pSubscription->callbacks[ type ].function != NULL );

    /* Copy the subscription callback info, as the subscription may be modified
     * when the subscriptions mutex is released. */
    callbackInfo = pSubscription->callbacks[ type ];

    IotMutex_Unlock( &_AwsIotShadowSubscriptionsMutex );

    /* Set the callback type. Shadow callbacks are enumerated after the operations. */
    callbackParam.callbackType = ( AwsIotShadowCallbackType_t ) ( type + SHADOW_OPERATION_COUNT );

    /* Set the remaining members of the callback param. */
    callbackParam.mqttConnection = pMessage->mqttConnection;
    callbackParam.pThingName = pThingName;
    callbackParam.thingNameLength = thingNameLength;
    callbackParam.u.callback.pDocument = pMessage->u.message.info.pPayload;
    callbackParam.u.callback.documentLength = pMessage->u.message.info.payloadLength;

    /* Invoke the callback function. */
    callbackInfo.function( callbackInfo.pCallbackContext,
                           &callbackParam );

    /* This function uses cleanup sections to exit on error. */
    IOT_FUNCTION_CLEANUP_BEGIN();
}

/*-----------------------------------------------------------*/

static void _deltaCallbackWrapper( void * pArgument,
                                   IotMqttCallbackParam_t * pMessage )
{
    /* Silence warnings about unused parameters. */
    ( void ) pArgument;

    _callbackWrapperCommon( DELTA_CALLBACK, pMessage );
}

/*-----------------------------------------------------------*/

static void _updatedCallbackWrapper( void * pArgument,
                                     IotMqttCallbackParam_t * pMessage )
{
    /* Silence warnings about unused parameters. */
    ( void ) pArgument;

    _callbackWrapperCommon( UPDATED_CALLBACK, pMessage );
}

/*-----------------------------------------------------------*/

AwsIotShadowError_t AwsIotShadow_Init( uint32_t mqttTimeoutMs )
{
    AwsIotShadowError_t status = AWS_IOT_SHADOW_SUCCESS;
    bool listInitStatus = false;

    if( _initCalled == 0 )
    {
        /* Initialize Shadow lists and mutexes. */
        listInitStatus = AwsIot_InitLists( &_AwsIotShadowPendingOperations,
                                           &_AwsIotShadowSubscriptions,
                                           &_AwsIotShadowPendingOperationsMutex,
                                           &_AwsIotShadowSubscriptionsMutex );

        if( listInitStatus == false )
        {
            IotLogInfo( "Failed to create Shadow lists." );

            status = AWS_IOT_SHADOW_INIT_FAILED;
        }
        else
        {
            /* Save the MQTT timeout option. */
            if( mqttTimeoutMs != 0 )
            {
                _AwsIotShadowMqttTimeoutMs = mqttTimeoutMs;
            }

            /* Set the flag that specifies initialization is complete. */
            _initCalled = 1;

            IotLogInfo( "Shadow library successfully initialized." );
        }
    }
    else
    {
        IotLogWarn( "AwsIotShadow_Init called with library already initialized." );
    }

    return status;
}

/*-----------------------------------------------------------*/

void AwsIotShadow_Cleanup( void )
{
    if( _initCalled == 1 )
    {
        _initCalled = 0;

        /* Remove and free all items in the Shadow pending operation list. */
        IotMutex_Lock( &( _AwsIotShadowPendingOperationsMutex ) );
        IotListDouble_RemoveAll( &( _AwsIotShadowPendingOperations ),
                                 _AwsIotShadow_DestroyOperation,
                                 offsetof( _shadowOperation_t, link ) );
        IotMutex_Unlock( &( _AwsIotShadowPendingOperationsMutex ) );

        /* Remove and free all items in the Shadow subscription list. */
        IotMutex_Lock( &( _AwsIotShadowSubscriptionsMutex ) );
        IotListDouble_RemoveAll( &( _AwsIotShadowSubscriptions ),
                                 _AwsIotShadow_DestroySubscription,
                                 offsetof( _shadowSubscription_t, link ) );
        IotMutex_Unlock( &( _AwsIotShadowSubscriptionsMutex ) );

        /* Destroy Shadow library mutexes. */
        IotMutex_Destroy( &( _AwsIotShadowPendingOperationsMutex ) );
        IotMutex_Destroy( &( _AwsIotShadowSubscriptionsMutex ) );

        /* Restore the default MQTT timeout. */
        _AwsIotShadowMqttTimeoutMs = AWS_IOT_SHADOW_DEFAULT_MQTT_TIMEOUT_MS;

        IotLogInfo( "Shadow library cleanup done." );
    }
    else
    {
        IotLogWarn( "AwsIotShadow_Init was not called before AwsIotShadow_Cleanup." );
    }
}

/*-----------------------------------------------------------*/

AwsIotShadowError_t AwsIotShadow_DeleteAsync( IotMqttConnection_t mqttConnection,
                                              const char * pThingName,
                                              size_t thingNameLength,
                                              uint32_t flags,
                                              const AwsIotShadowCallbackInfo_t * pCallbackInfo,
                                              AwsIotShadowOperation_t * const pDeleteOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotShadowError_t, AWS_IOT_SHADOW_STATUS_PENDING );
    _shadowOperation_t * pOperation = NULL;

    /* Check that AwsIotShadow_Init was called. */
    if( _checkInit() == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_NOT_INITIALIZED );
    }

    /* Validate the Thing Name and flags for Shadow DELETE. */
    status = _validateThingNameFlags( SHADOW_DELETE,
                                      pThingName,
                                      thingNameLength,
                                      flags,
                                      pCallbackInfo,
                                      pDeleteOperation );

    if( status != AWS_IOT_SHADOW_SUCCESS )
    {
        /* The Thing Name or some flag was invalid. */
        IOT_GOTO_CLEANUP();
    }

    /* Allocate a new Shadow operation for DELETE. */
    status = _AwsIotShadow_CreateOperation( &pOperation,
                                            SHADOW_DELETE,
                                            flags,
                                            pCallbackInfo );

    if( status != AWS_IOT_SHADOW_SUCCESS )
    {
        /* No memory for a new Shadow operation. */
        IOT_GOTO_CLEANUP();
    }

    /* Check the members set by Shadow operation creation. */
    AwsIotShadow_Assert( pOperation != NULL );
    AwsIotShadow_Assert( pOperation->type == SHADOW_DELETE );
    AwsIotShadow_Assert( pOperation->flags == flags );
    AwsIotShadow_Assert( pOperation->status == AWS_IOT_SHADOW_STATUS_PENDING );

    /* Set the reference if provided. This must be done before the Shadow operation
     * is processed. */
    if( pDeleteOperation != NULL )
    {
        *pDeleteOperation = pOperation;
    }

    /* Process the Shadow operation. This subscribes to any required topics and
     * sends the MQTT message for the Shadow operation. */
    status = _AwsIotShadow_ProcessOperation( mqttConnection,
                                             pThingName,
                                             thingNameLength,
                                             pOperation,
                                             NULL );

    /* If the Shadow operation failed, clear the now invalid reference. */
    if( ( status != AWS_IOT_SHADOW_STATUS_PENDING ) && ( pDeleteOperation != NULL ) )
    {
        *pDeleteOperation = AWS_IOT_SHADOW_OPERATION_INITIALIZER;
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

AwsIotShadowError_t AwsIotShadow_DeleteSync( IotMqttConnection_t mqttConnection,
                                             const char * pThingName,
                                             size_t thingNameLength,
                                             uint32_t flags,
                                             uint32_t timeoutMs )
{
    AwsIotShadowError_t status = AWS_IOT_SHADOW_STATUS_PENDING;
    AwsIotShadowOperation_t deleteOperation = AWS_IOT_SHADOW_OPERATION_INITIALIZER;

    /* Set the waitable flag. */
    flags |= AWS_IOT_SHADOW_FLAG_WAITABLE;

    /* Call the asynchronous Shadow delete function. */
    status = AwsIotShadow_DeleteAsync( mqttConnection,
                                       pThingName,
                                       thingNameLength,
                                       flags,
                                       NULL,
                                       &deleteOperation );

    /* Wait for the Shadow delete operation to complete. */
    if( status == AWS_IOT_SHADOW_STATUS_PENDING )
    {
        status = AwsIotShadow_Wait( deleteOperation, timeoutMs, NULL, NULL );
    }

    /* Ensure that a status was set. */
    AwsIotShadow_Assert( status != AWS_IOT_SHADOW_STATUS_PENDING );

    return status;
}

/*-----------------------------------------------------------*/

AwsIotShadowError_t AwsIotShadow_GetAsync( IotMqttConnection_t mqttConnection,
                                           const AwsIotShadowDocumentInfo_t * pGetInfo,
                                           uint32_t flags,
                                           const AwsIotShadowCallbackInfo_t * pCallbackInfo,
                                           AwsIotShadowOperation_t * const pGetOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotShadowError_t, AWS_IOT_SHADOW_STATUS_PENDING );
    _shadowOperation_t * pOperation = NULL;

    /* Check that AwsIotShadow_Init was called. */
    if( _checkInit() == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_NOT_INITIALIZED );
    }

    /* Validate the Thing Name and flags for Shadow GET. */
    status = _validateThingNameFlags( SHADOW_GET,
                                      pGetInfo->pThingName,
                                      pGetInfo->thingNameLength,
                                      flags,
                                      pCallbackInfo,
                                      pGetOperation );

    if( status != AWS_IOT_SHADOW_SUCCESS )
    {
        /* The Thing Name or some flag was invalid. */
        IOT_GOTO_CLEANUP();
    }

    /* Validate the document info for Shadow GET. */
    status = _validateDocumentInfo( SHADOW_GET,
                                    flags,
                                    pGetInfo );

    if( status != AWS_IOT_SHADOW_SUCCESS )
    {
        /* Document info was invalid. */
        IOT_GOTO_CLEANUP();
    }

    /* Allocate a new Shadow operation for GET. */
    status = _AwsIotShadow_CreateOperation( &pOperation,
                                            SHADOW_GET,
                                            flags,
                                            pCallbackInfo );

    if( status != AWS_IOT_SHADOW_SUCCESS )
    {
        /* No memory for a new Shadow operation. */
        IOT_GOTO_CLEANUP();
    }

    /* Check the members set by Shadow operation creation. */
    AwsIotShadow_Assert( pOperation != NULL );
    AwsIotShadow_Assert( pOperation->type == SHADOW_GET );
    AwsIotShadow_Assert( pOperation->flags == flags );
    AwsIotShadow_Assert( pOperation->status == AWS_IOT_SHADOW_STATUS_PENDING );

    /* Copy the memory allocation function. */
    pOperation->u.get.mallocDocument = pGetInfo->u.get.mallocDocument;

    /* Set the reference if provided. This must be done before the Shadow operation
     * is processed. */
    if( pGetOperation != NULL )
    {
        *pGetOperation = pOperation;
    }

    /* Process the Shadow operation. This subscribes to any required topics and
     * sends the MQTT message for the Shadow operation. */
    status = _AwsIotShadow_ProcessOperation( mqttConnection,
                                             pGetInfo->pThingName,
                                             pGetInfo->thingNameLength,
                                             pOperation,
                                             pGetInfo );

    /* If the Shadow operation failed, clear the now invalid reference. */
    if( ( status != AWS_IOT_SHADOW_STATUS_PENDING ) && ( pGetOperation != NULL ) )
    {
        *pGetOperation = AWS_IOT_SHADOW_OPERATION_INITIALIZER;
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

AwsIotShadowError_t AwsIotShadow_GetSync( IotMqttConnection_t mqttConnection,
                                          const AwsIotShadowDocumentInfo_t * pGetInfo,
                                          uint32_t flags,
                                          uint32_t timeoutMs,
                                          const char ** const pShadowDocument,
                                          size_t * const pShadowDocumentLength )
{
    AwsIotShadowError_t status = AWS_IOT_SHADOW_STATUS_PENDING;
    AwsIotShadowOperation_t getOperation = AWS_IOT_SHADOW_OPERATION_INITIALIZER;

    /* Set the waitable flag. */
    flags |= AWS_IOT_SHADOW_FLAG_WAITABLE;

    /* Call the asynchronous Shadow get function. */
    status = AwsIotShadow_GetAsync( mqttConnection,
                                    pGetInfo,
                                    flags,
                                    NULL,
                                    &getOperation );

    /* Wait for the Shadow get operation to complete. */
    if( status == AWS_IOT_SHADOW_STATUS_PENDING )
    {
        status = AwsIotShadow_Wait( getOperation,
                                    timeoutMs,
                                    pShadowDocument,
                                    pShadowDocumentLength );
    }

    /* Ensure that a status was set. */
    AwsIotShadow_Assert( status != AWS_IOT_SHADOW_STATUS_PENDING );

    return status;
}

/*-----------------------------------------------------------*/

AwsIotShadowError_t AwsIotShadow_UpdateAsync( IotMqttConnection_t mqttConnection,
                                              const AwsIotShadowDocumentInfo_t * pUpdateInfo,
                                              uint32_t flags,
                                              const AwsIotShadowCallbackInfo_t * pCallbackInfo,
                                              AwsIotShadowOperation_t * const pUpdateOperation )
{
    IOT_FUNCTION_ENTRY( AwsIotShadowError_t, AWS_IOT_SHADOW_STATUS_PENDING );
    _shadowOperation_t * pOperation = NULL;
    const char * pClientToken = NULL;
    size_t clientTokenLength = 0;

    /* Check that AwsIotShadow_Init was called. */
    if( _checkInit() == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_NOT_INITIALIZED );
    }

    /* Validate the Thing Name and flags for Shadow UPDATE. */
    status = _validateThingNameFlags( SHADOW_UPDATE,
                                      pUpdateInfo->pThingName,
                                      pUpdateInfo->thingNameLength,
                                      flags,
                                      pCallbackInfo,
                                      pUpdateOperation );

    if( status != AWS_IOT_SHADOW_SUCCESS )
    {
        /* The Thing Name or some flag was invalid. */
        IOT_GOTO_CLEANUP();
    }

    /* Validate the document info for Shadow UPDATE. */
    status = _validateDocumentInfo( SHADOW_UPDATE,
                                    flags,
                                    pUpdateInfo );

    if( status != AWS_IOT_SHADOW_SUCCESS )
    {
        /* Document info was invalid. */
        IOT_GOTO_CLEANUP();
    }

    /* Check UPDATE document for a client token. */
    if( AwsIot_GetClientToken( pUpdateInfo->u.update.pUpdateDocument,
                               pUpdateInfo->u.update.updateDocumentLength,
                               &pClientToken,
                               &clientTokenLength ) == false )
    {
        IotLogError( "Shadow document for Shadow UPDATE does not contain a valid client token." );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_BAD_PARAMETER );
    }

    /* Allocate a new Shadow operation for UPDATE. */
    status = _AwsIotShadow_CreateOperation( &pOperation,
                                            SHADOW_UPDATE,
                                            flags,
                                            pCallbackInfo );

    if( status != AWS_IOT_SHADOW_SUCCESS )
    {
        /* No memory for a new Shadow operation. */
        IOT_GOTO_CLEANUP();
    }

    /* Check the members set by Shadow operation creation. */
    AwsIotShadow_Assert( pOperation != NULL );
    AwsIotShadow_Assert( pOperation->type == SHADOW_UPDATE );
    AwsIotShadow_Assert( pOperation->flags == flags );
    AwsIotShadow_Assert( pOperation->status == AWS_IOT_SHADOW_STATUS_PENDING );

    /* Allocate memory for the client token. */
    pOperation->u.update.pClientToken = AwsIotShadow_MallocString( clientTokenLength );

    if( pOperation->u.update.pClientToken == NULL )
    {
        IotLogError( "Failed to allocate memory for Shadow update client token." );
        _AwsIotShadow_DestroyOperation( pOperation );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_NO_MEMORY );
    }

    /* Copy the client token. The client token must be copied in case the application
     * frees the buffer containing it. */
    ( void ) memcpy( ( void * ) pOperation->u.update.pClientToken,
                     pClientToken,
                     clientTokenLength );
    pOperation->u.update.clientTokenLength = clientTokenLength;

    /* Set the reference if provided. This must be done before the Shadow operation
     * is processed. */
    if( pUpdateOperation != NULL )
    {
        *pUpdateOperation = pOperation;
    }

    /* Process the Shadow operation. This subscribes to any required topics and
     * sends the MQTT message for the Shadow operation. */
    status = _AwsIotShadow_ProcessOperation( mqttConnection,
                                             pUpdateInfo->pThingName,
                                             pUpdateInfo->thingNameLength,
                                             pOperation,
                                             pUpdateInfo );

    /* If the Shadow operation failed, clear the now invalid reference. */
    if( ( status != AWS_IOT_SHADOW_STATUS_PENDING ) && ( pUpdateOperation != NULL ) )
    {
        *pUpdateOperation = AWS_IOT_SHADOW_OPERATION_INITIALIZER;
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

AwsIotShadowError_t AwsIotShadow_UpdateSync( IotMqttConnection_t mqttConnection,
                                             const AwsIotShadowDocumentInfo_t * pUpdateInfo,
                                             uint32_t flags,
                                             uint32_t timeoutMs )
{
    AwsIotShadowError_t status = AWS_IOT_SHADOW_STATUS_PENDING;
    AwsIotShadowOperation_t updateOperation = AWS_IOT_SHADOW_OPERATION_INITIALIZER;

    /* Set the waitable flag. */
    flags |= AWS_IOT_SHADOW_FLAG_WAITABLE;

    /* Call the asynchronous Shadow update function. */
    status = AwsIotShadow_UpdateAsync( mqttConnection,
                                       pUpdateInfo,
                                       flags,
                                       NULL,
                                       &updateOperation );

    /* Wait for the Shadow update operation to complete. */
    if( status == AWS_IOT_SHADOW_STATUS_PENDING )
    {
        status = AwsIotShadow_Wait( updateOperation, timeoutMs, NULL, NULL );
    }

    /* Ensure that a status was set. */
    AwsIotShadow_Assert( status != AWS_IOT_SHADOW_STATUS_PENDING );

    return status;
}

/*-----------------------------------------------------------*/

AwsIotShadowError_t AwsIotShadow_Wait( AwsIotShadowOperation_t operation,
                                       uint32_t timeoutMs,
                                       const char ** const pShadowDocument,
                                       size_t * const pShadowDocumentLength )
{
    IOT_FUNCTION_ENTRY( AwsIotShadowError_t, AWS_IOT_SHADOW_STATUS_PENDING );

    /* Check that AwsIotShadow_Init was called. */
    if( _checkInit() == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_NOT_INITIALIZED );
    }

    /* Check that reference is set. */
    if( operation == NULL )
    {
        IotLogError( "Operation reference cannot be NULL." );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_BAD_PARAMETER );
    }

    /* Check that reference is waitable. */
    if( ( operation->flags & AWS_IOT_SHADOW_FLAG_WAITABLE ) == 0 )
    {
        IotLogError( "Operation is not waitable." );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_BAD_PARAMETER );
    }

    /* Check that output parameters are set for a Shadow GET. */
    if( operation->type == SHADOW_GET )
    {
        if( ( pShadowDocument == NULL ) || ( pShadowDocumentLength == NULL ) )
        {
            IotLogError( "Output buffer and size pointer must be set for Shadow GET." );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_SHADOW_BAD_PARAMETER );
        }
    }

    /* Wait for a response to the Shadow operation. */
    if( IotSemaphore_TimedWait( &( operation->notify.waitSemaphore ),
                                timeoutMs ) == true )
    {
        status = operation->status;
    }
    else
    {
        status = AWS_IOT_SHADOW_TIMEOUT;
    }

    /* Remove the completed operation from the pending operation list. */
    IotMutex_Lock( &( _AwsIotShadowPendingOperationsMutex ) );
    IotListDouble_Remove( &( operation->link ) );
    IotMutex_Unlock( &( _AwsIotShadowPendingOperationsMutex ) );

    /* Decrement the reference count. This also removes subscriptions if the
     * count reaches 0. */
    IotMutex_Lock( &_AwsIotShadowSubscriptionsMutex );
    _AwsIotShadow_DecrementReferences( operation,
                                       operation->pSubscription->pTopicBuffer,
                                       NULL );
    IotMutex_Unlock( &_AwsIotShadowSubscriptionsMutex );

    /* Set the output parameters for Shadow GET. */
    if( ( operation->type == SHADOW_GET ) &&
        ( status == AWS_IOT_SHADOW_SUCCESS ) )
    {
        *pShadowDocument = operation->u.get.pDocument;
        *pShadowDocumentLength = operation->u.get.documentLength;
    }

    /* Destroy the Shadow operation. */
    _AwsIotShadow_DestroyOperation( operation );

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

AwsIotShadowError_t AwsIotShadow_SetDeltaCallback( IotMqttConnection_t mqttConnection,
                                                   const char * pThingName,
                                                   size_t thingNameLength,
                                                   uint32_t flags,
                                                   const AwsIotShadowCallbackInfo_t * pDeltaCallback )
{
    /* Flags are currently not used by this function. */
    ( void ) flags;

    return _setCallbackCommon( mqttConnection,
                               DELTA_CALLBACK,
                               pThingName,
                               thingNameLength,
                               pDeltaCallback );
}

/*-----------------------------------------------------------*/

AwsIotShadowError_t AwsIotShadow_SetUpdatedCallback( IotMqttConnection_t mqttConnection,
                                                     const char * pThingName,
                                                     size_t thingNameLength,
                                                     uint32_t flags,
                                                     const AwsIotShadowCallbackInfo_t * pUpdatedCallback )
{
    /* Flags are currently not used by this function. */
    ( void ) flags;

    return _setCallbackCommon( mqttConnection,
                               UPDATED_CALLBACK,
                               pThingName,
                               thingNameLength,
                               pUpdatedCallback );
}

/*-----------------------------------------------------------*/

const char * AwsIotShadow_strerror( AwsIotShadowError_t status )
{
    const char * pMessage = NULL;

    switch( status )
    {
        case AWS_IOT_SHADOW_SUCCESS:
            pMessage = "SUCCESS";
            break;

        case AWS_IOT_SHADOW_STATUS_PENDING:
            pMessage = "STATUS PENDING";
            break;

        case AWS_IOT_SHADOW_INIT_FAILED:
            pMessage = "INITIALIZATION FAILED";
            break;

        case AWS_IOT_SHADOW_BAD_PARAMETER:
            pMessage = "BAD PARAMETER";
            break;

        case AWS_IOT_SHADOW_NO_MEMORY:
            pMessage = "NO MEMORY";
            break;

        case AWS_IOT_SHADOW_MQTT_ERROR:
            pMessage = "MQTT LIBRARY ERROR";
            break;

        case AWS_IOT_SHADOW_BAD_RESPONSE:
            pMessage = "BAD RESPONSE RECEIVED";
            break;

        case AWS_IOT_SHADOW_TIMEOUT:
            pMessage = "TIMEOUT";
            break;

        case AWS_IOT_SHADOW_NOT_INITIALIZED:
            pMessage = "NOT INITIALIZED";
            break;

        case AWS_IOT_SHADOW_BAD_REQUEST:
            pMessage = "REJECTED: 400 BAD REQUEST";
            break;

        case AWS_IOT_SHADOW_UNAUTHORIZED:
            pMessage = "REJECTED: 401 UNAUTHORIZED";
            break;

        case AWS_IOT_SHADOW_FORBIDDEN:
            pMessage = "REJECTED: 403 FORBIDDEN";
            break;

        case AWS_IOT_SHADOW_NOT_FOUND:
            pMessage = "REJECTED: 404 NOT FOUND";
            break;

        case AWS_IOT_SHADOW_CONFLICT:
            pMessage = "REJECTED: 409 VERSION CONFLICT";
            break;

        case AWS_IOT_SHADOW_TOO_LARGE:
            pMessage = "REJECTED: 413 PAYLOAD TOO LARGE";
            break;

        case AWS_IOT_SHADOW_UNSUPPORTED:
            pMessage = "REJECTED: 415 UNSUPPORTED ENCODING";
            break;

        case AWS_IOT_SHADOW_TOO_MANY_REQUESTS:
            pMessage = "REJECTED: 429 TOO MANY REQUESTS";
            break;

        case AWS_IOT_SHADOW_SERVER_ERROR:
            pMessage = "500 SERVER ERROR";
            break;

        default:
            pMessage = "INVALID STATUS";
            break;
    }

    return pMessage;
}

/*-----------------------------------------------------------*/
