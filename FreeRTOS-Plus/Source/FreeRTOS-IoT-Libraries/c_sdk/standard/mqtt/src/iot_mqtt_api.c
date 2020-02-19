/*
 * IoT MQTT V2.1.1
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file iot_mqtt_api.c
 * @brief Implements most user-facing functions of the MQTT library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* MQTT internal include. */
#include "private/iot_mqtt_internal.h"

/* Platform layer includes. */
#include "platform/iot_clock.h"
#include "platform/iot_threads.h"

/* Atomics include. */
#include "iot_atomic.h"

/* Validate MQTT configuration settings. */
#if ( IOT_MQTT_ENABLE_ASSERTS != 0 ) && ( IOT_MQTT_ENABLE_ASSERTS != 1 )
    #error "IOT_MQTT_ENABLE_ASSERTS must be 0 or 1."
#endif
#if ( AWS_IOT_MQTT_ENABLE_METRICS != 0 ) && ( AWS_IOT_MQTT_ENABLE_METRICS != 1 )
    #error "AWS_IOT_MQTT_ENABLE_METRICS must be 0 or 1."
#endif
#if ( IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES != 0 ) && ( IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES != 1 )
    #error "IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES must be 0 or 1."
#endif
#if IOT_MQTT_RESPONSE_WAIT_MS <= 0
    #error "IOT_MQTT_RESPONSE_WAIT_MS cannot be 0 or negative."
#endif
#if IOT_MQTT_RETRY_MS_CEILING <= 0
    #error "IOT_MQTT_RETRY_MS_CEILING cannot be 0 or negative."
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Uninitialized value for @ref _initCalled.
 */
#define MQTT_LIBRARY_UNINITIALIZED    ( ( uint32_t ) 0 )

/**
 * @brief Initialized value for @ref _initCalled.
 */
#define MQTT_LIBRARY_INITIALIZED      ( ( uint32_t ) 1 )

/*-----------------------------------------------------------*/

/**
 * @brief Check if the library is initialized.
 *
 * @return `true` if IotMqtt_Init was called; `false` otherwise.
 */
static bool _checkInit( void );

/**
 * @brief Set the unsubscribed flag of an MQTT subscription.
 *
 * @param[in] pSubscriptionLink Pointer to the link member of an #_mqttSubscription_t.
 * @param[in] pMatch Not used.
 *
 * @return Always returns `true`.
 */
static bool _mqttSubscription_setUnsubscribe( const IotLink_t * const pSubscriptionLink,
                                              void * pMatch );

/**
 * @brief Destroy an MQTT subscription if its reference count is 0.
 *
 * @param[in] pData The subscription to destroy. This parameter is of type
 * `void*` for compatibility with [free]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
static void _mqttSubscription_tryDestroy( void * pData );

/**
 * @brief Decrement the reference count of an MQTT operation and attempt to
 * destroy it.
 *
 * @param[in] pData The operation data to destroy. This parameter is of type
 * `void*` for compatibility with [free]
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
static void _mqttOperation_tryDestroy( void * pData );

/**
 * @brief Initialize the keep-alive operation for an MQTT connection.
 *
 * @param[in] pNetworkInfo User-provided network information for the new
 * connection.
 * @param[in] keepAliveSeconds User-provided keep-alive interval.
 * @param[out] pMqttConnection The MQTT connection associated with the keep-alive.
 *
 * @return `true` if the keep-alive job was successfully created; `false` otherwise.
 */
static bool _createKeepAliveOperation( const IotMqttNetworkInfo_t * pNetworkInfo,
                                       uint16_t keepAliveSeconds,
                                       _mqttConnection_t * pMqttConnection );

/**
 * @brief Initialize a network connection, creating it if necessary.
 *
 * @param[in] pNetworkInfo User-provided network information for the connection
 * connection.
 * @param[out] pNetworkConnection On success, the created and/or initialized network connection.
 * @param[out] pCreatedNewNetworkConnection On success, `true` if a new network connection was created; `false` if an existing one will be used.
 *
 * @return Any #IotNetworkError_t, as defined by the network stack.
 */
static IotNetworkError_t _createNetworkConnection( const IotMqttNetworkInfo_t * pNetworkInfo,
                                                   IotNetworkConnection_t * pNetworkConnection,
                                                   bool * pCreatedNewNetworkConnection );

/**
 * @brief Creates a new MQTT connection and initializes its members.
 *
 * @param[in] awsIotMqttMode Specifies if this connection is to an AWS IoT MQTT server.
 * @param[in] pNetworkInfo User-provided network information for the new
 * connection.
 * @param[in] keepAliveSeconds User-provided keep-alive interval for the new connection.
 *
 * @return Pointer to a newly-created MQTT connection; `NULL` on failure.
 */
static _mqttConnection_t * _createMqttConnection( bool awsIotMqttMode,
                                                  const IotMqttNetworkInfo_t * pNetworkInfo,
                                                  uint16_t keepAliveSeconds );

/**
 * @brief Destroys the members of an MQTT connection.
 *
 * @param[in] pMqttConnection Which connection to destroy.
 */
static void _destroyMqttConnection( _mqttConnection_t * pMqttConnection );

/**
 * @brief Common setup function for subscribe and unsubscribe operations.
 *
 * See @ref mqtt_function_subscribeasync or @ref mqtt_function_unsubscribeasync for a
 * description of the parameters and return values.
 */
static IotMqttError_t _subscriptionCommonSetup( IotMqttOperationType_t operation,
                                                IotMqttConnection_t mqttConnection,
                                                const IotMqttSubscription_t * pSubscriptionList,
                                                size_t subscriptionCount,
                                                uint32_t flags,
                                                const IotMqttOperation_t * const pOperationReference );

/**
 * @brief Utility function for creating and serializing subscription requests.
 *
 * See @ref mqtt_function_subscribeasync or @ref mqtt_function_unsubscribeasync for a
 * description of the parameters and return values.
 */
static IotMqttError_t _subscriptionCreateAndSerialize( IotMqttOperationType_t operation,
                                                       IotMqttConnection_t mqttConnection,
                                                       IotMqttSerializeSubscribe_t serializeSubscription,
                                                       const IotMqttSubscription_t * pSubscriptionList,
                                                       size_t subscriptionCount,
                                                       uint32_t flags,
                                                       const IotMqttCallbackInfo_t * pCallbackInfo,
                                                       _mqttOperation_t ** ppSubscriptionOperation );

/**
 * @brief Utility function for sending/scheduling a subscribe, unsubscribe or publish message.
 *
 * @param[in] pMqttOperation Reference to MQTT operation.
 * @param[in] flags Flags which modify the behavior of this function.
 *
 * @return #IOT_MQTT_SUCCESS or #IOT_MQTT_SCHEDULING_ERROR.
 */
static IotMqttError_t _sendMqttMessage( _mqttOperation_t * pMqttOperation,
                                        uint32_t flags );

/**
 * @brief The common component of both @ref mqtt_function_subscribeasync and @ref
 * mqtt_function_unsubscribeasync.
 *
 * See @ref mqtt_function_subscribeasync or @ref mqtt_function_unsubscribeasync for a
 * description of the parameters and return values.
 */
static IotMqttError_t _subscriptionCommon( IotMqttOperationType_t operation,
                                           IotMqttConnection_t mqttConnection,
                                           IotMqttSerializeSubscribe_t serializeSubscription,
                                           const IotMqttSubscription_t * pSubscriptionList,
                                           size_t subscriptionCount,
                                           uint32_t flags,
                                           const IotMqttCallbackInfo_t * pCallbackInfo,
                                           IotMqttOperation_t * const pOperationReference );

/**
 * @brief Set an operation reference if provided.
 *
 * @param[out] pOperationReference Operation reference provided by the application.
 * @param[in] pNewOperation Operation to set.
 */
static void _setOperationReference( IotMqttOperation_t * const pOperationReference,
                                    _mqttOperation_t * pNewOperation );

/**
 * @brief Wait for an MQTT operation to complete.
 *
 * See @ref mqtt_function_wait for a description of the parameters and return values.
 */
static IotMqttError_t _waitForOperation( IotMqttOperation_t operation,
                                         uint32_t timeoutMs );

/**
 * @brief Utility function for scheduling ping request after connection with
 * with the broker is established.
 *
 * @param[in] pMqttConnection MQTT connection reference.
 *
 * @return #IOT_MQTT_SUCCESS, #IOT_MQTT_SCHEDULING_ERROR.
 */
static IotMqttError_t _scheduleKeepAlive( IotMqttConnection_t pMqttConnection );

/**
 * @brief Utility function for sending connect request.
 *
 * @param[in] pOperation CONNECT operation reference.
 * @param[in] timeoutMs How many milliseconds to wait for CONN_ACK.
 *
 * @return #IOT_MQTT_SUCCESS, #IOT_MQTT_BAD_PARAMETER, #IOT_MQTT_NETWORK_ERROR.
 */
static IotMqttError_t _sendConnectRequest( _mqttOperation_t * pOperation,
                                           uint32_t timeoutMs );

/**
 * @brief Utility function for adding subscriptions to connect request.
 *
 * @param[in] pOperation CONNECT operation reference.
 * @param[in] pMqttConnection MQTT connection reference.
 * @param[in] pConnectInfo MQTT connection information.
 *
 * @return #IOT_MQTT_SUCCESS, #IOT_MQTT_NO_MEMORY
 */
static IotMqttError_t _addSubscriptions( _mqttOperation_t * pOperation,
                                         IotMqttConnection_t pMqttConnection,
                                         const IotMqttConnectInfo_t * pConnectInfo );

/**
 * @brief Utility function for handling MQTT connect failure.
 *
 * @param[in] pMqttConnection MQTT connection reference.
 * @param[in] pNetworkConnection Network connection reference.
 * @param[in] pNetworkInfo User-provided network information.
 * @param[in] pOperation CONNECT operation reference.
 * @param[in] ownNetworkConnection if true, connection needs to be closed.
 *
 */
static void _handleConnectFailure( IotMqttConnection_t pMqttConnection,
                                   IotNetworkConnection_t pNetworkConnection,
                                   const IotMqttNetworkInfo_t * pNetworkInfo,
                                   _mqttOperation_t * pOperation,
                                   bool ownNetworkConnection );

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Declaration of local MQTT serializer override selectors
 */
#if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
    SERIALIZER_OVERRIDE_SELECTOR( IotMqttSerializePingreq_t,
                                  _getMqttPingreqSerializer,
                                  _IotMqtt_SerializePingreq,
                                  serialize.pingreq )
    SERIALIZER_OVERRIDE_SELECTOR( IotMqtt_SerializePublish_t,
                                  _getMqttPublishSerializer,
                                  _IotMqtt_SerializePublish,
                                  serialize.publish )
    SERIALIZER_OVERRIDE_SELECTOR( IotMqttFreePacket_t,
                                  _getMqttFreePacketFunc,
                                  _IotMqtt_FreePacket,
                                  freePacket )
    SERIALIZER_OVERRIDE_SELECTOR( IotMqttSerializeSubscribe_t,
                                  _getMqttSubscribeSerializer,
                                  _IotMqtt_SerializeSubscribe,
                                  serialize.subscribe )
    SERIALIZER_OVERRIDE_SELECTOR( IotMqttSerializeSubscribe_t,
                                  _getMqttUnsubscribeSerializer,
                                  _IotMqtt_SerializeUnsubscribe,
                                  serialize.unsubscribe )
    SERIALIZER_OVERRIDE_SELECTOR( IotMqttSerializeConnect_t,
                                  _getMqttConnectSerializer,
                                  _IotMqtt_SerializeConnect,
                                  serialize.connect )
    SERIALIZER_OVERRIDE_SELECTOR( IotMqttSerializeDisconnect_t,
                                  _getMqttDisconnectSerializer,
                                  _IotMqtt_SerializeDisconnect,
                                  serialize.disconnect )
#else /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */
    #define _getMqttPingreqSerializer( pSerializer )        _IotMqtt_SerializePingreq
    #define _getMqttPublishSerializer( pSerializer )        _IotMqtt_SerializePublish
    #define _getMqttFreePacketFunc( pSerializer )           _IotMqtt_FreePacket
    #define _getMqttSubscribeSerializer( pSerializer )      _IotMqtt_SerializeSubscribe
    #define _getMqttUnsubscribeSerializer( pSerializer )    _IotMqtt_SerializeUnsubscribe
    #define _getMqttConnectSerializer( pSerializer )        _IotMqtt_SerializeConnect
    #define _getMqttDisconnectSerializer( pSerializer )     _IotMqtt_SerializeDisconnect
#endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */
/** @endcond */

/*-----------------------------------------------------------*/

/**
 * @brief Place holder packet identifier used when
 * _IotMqtt_AddSubscriptions is called with previous subscriptions lists.
 * Any non-zero value is acceptable, since this value is never sent out to
 * the broker.
 */
#define IOT_MQTT_PREVIOUS_SUBSCRIPTIONS_PACKET_ID    1

/*-----------------------------------------------------------*/

/**
 * @brief Tracks whether @ref mqtt_function_init has been called.
 *
 * API functions will fail if @ref mqtt_function_init was not called.
 */
static volatile uint32_t _initCalled = MQTT_LIBRARY_UNINITIALIZED;

/*-----------------------------------------------------------*/

static bool _checkInit( void )
{
    bool status = true;

    if( _initCalled == MQTT_LIBRARY_UNINITIALIZED )
    {
        IotLogError( "IotMqtt_Init was not called." );

        status = false;
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool _mqttSubscription_setUnsubscribe( const IotLink_t * const pSubscriptionLink,
                                              void * pMatch )
{
    /* Because this function is called from a container function, the given link
     * must never be NULL. */
    IotMqtt_Assert( pSubscriptionLink != NULL );

    /* Casting `pSubscriptionLink` to uint8_t * is done only to calculate the
     * starting address of the struct and does not modify the link it points to.
     * Adding parentheses to parameters of IotLink_Container is not applicable
     * because it uses type-casting and offsetof, and would cause compiling errors. */
    /* coverity[misra_c_2012_rule_11_8_violation] */
    /* coverity[misra_c_2012_rule_20_7_violation] */
    /* coverity[caretline] */
    _mqttSubscription_t * pSubscription = IotLink_Container( _mqttSubscription_t,
                                                             pSubscriptionLink,
                                                             link );

    /* Silence warnings about unused parameters. */
    ( void ) pMatch;

    /* Set the unsubscribed flag. */
    pSubscription->unsubscribed = true;

    return true;
}

/*-----------------------------------------------------------*/

static void _mqttSubscription_tryDestroy( void * pData )
{
    _mqttSubscription_t * pSubscription = ( _mqttSubscription_t * ) pData;

    /* Reference count must not be negative. */
    IotMqtt_Assert( pSubscription->references >= 0 );

    /* Unsubscribed flag should be set. */
    IotMqtt_Assert( pSubscription->unsubscribed == true );

    /* Free the subscription if it has no references. */
    if( pSubscription->references == 0 )
    {
        IotMqtt_FreeSubscription( pSubscription );
    }
}

/*-----------------------------------------------------------*/

static void _mqttOperation_tryDestroy( void * pData )
{
    _mqttOperation_t * pOperation = ( _mqttOperation_t * ) pData;
    taskPoolError_t taskPoolStatus = TASKPOOL_SUCCESS;

    /* Incoming PUBLISH operations may always be freed. */
    if( pOperation->incomingPublish == true )
    {
        /* Try to cancel the job only if it is initialised. */
        if( taskPoolIsJobInitialised( &( pOperation->job ) ) )
        {
            /* Cancel the incoming PUBLISH operation's job. */
            taskPoolStatus = taskPoolTryCancel( &( pOperation->job ) );

            /* If the operation's job was not canceled, it must be already executing.
             * Any other return value is invalid. */
            IotMqtt_Assert( ( taskPoolStatus == TASKPOOL_SUCCESS ) ||
                            ( taskPoolStatus == TASKPOOL_ILLEGAL_OPERATION ) );
        }
        else
        {
            taskPoolStatus = TASKPOOL_GENERAL_FAILURE;
        }

        /* Check if the incoming PUBLISH job was canceled. */
        if( taskPoolStatus == TASKPOOL_SUCCESS )
        {
            /* Job was canceled. Process incoming PUBLISH now to clean up. */
            _IotMqtt_ProcessIncomingPublish( &( pOperation->job ),
                                             pOperation );
        }
    }
    else
    {
        /* Decrement reference count and destroy operation if possible. */
        if( _IotMqtt_DecrementOperationReferences( pOperation, true ) == true )
        {
            _IotMqtt_DestroyOperation( pOperation );
        }
    }
}

/*-----------------------------------------------------------*/

static bool _createKeepAliveOperation( const IotMqttNetworkInfo_t * pNetworkInfo,
                                       uint16_t keepAliveSeconds,
                                       _mqttConnection_t * pMqttConnection )
{
    bool status = true;
    IotMqttError_t serializeStatus = IOT_MQTT_SUCCESS;

    /* Network information is not used when MQTT packet serializers are disabled. */
    ( void ) pNetworkInfo;

    /* Set PINGREQ operation members. */
    pMqttConnection->pingreq.u.operation.type = IOT_MQTT_PINGREQ;

    /* Convert the keep-alive interval to milliseconds. */
    pMqttConnection->pingreq.u.operation.periodic.ping.keepAliveMs = ( uint32_t ) keepAliveSeconds * 1000U;
    pMqttConnection->pingreq.u.operation.periodic.ping.nextPeriodMs = ( uint32_t ) keepAliveSeconds * 1000U;

    /* Generate a PINGREQ packet. */
    serializeStatus = _getMqttPingreqSerializer( pNetworkInfo->pMqttSerializer )( &( pMqttConnection->pingreq.u.operation.pMqttPacket ),
                                                                                  &( pMqttConnection->pingreq.u.operation.packetSize ) );

    if( serializeStatus != IOT_MQTT_SUCCESS )
    {
        IotLogError( "Failed to allocate PINGREQ packet for new connection." );

        status = false;
    }
    else
    {
        /* Create the task pool job that processes keep-alive. */
        taskPoolInitializeJob( _IotMqtt_ProcessKeepAlive,
                               pMqttConnection,
                               &( pMqttConnection->pingreq.job ) );

        /* Keep-alive references its MQTT connection, so increment reference. */
        ( pMqttConnection->references )++;
    }

    return status;
}

/*-----------------------------------------------------------*/

static IotNetworkError_t _createNetworkConnection( const IotMqttNetworkInfo_t * pNetworkInfo,
                                                   IotNetworkConnection_t * pNetworkConnection,
                                                   bool * pCreatedNewNetworkConnection )
{
    IotNetworkError_t status = IOT_NETWORK_SUCCESS;

    /* Network info must not be NULL. */
    if( pNetworkInfo == NULL )
    {
        IotLogError( "Network information cannot be NULL." );

        status = IOT_NETWORK_BAD_PARAMETER;
    }
    else if( pNetworkInfo->createNetworkConnection == true )
    {
        /* Create a new network connection if requested. Otherwise, copy the existing
         * network connection. */
        status = pNetworkInfo->pNetworkInterface->create( pNetworkInfo->u.setup.pNetworkServerInfo,
                                                          pNetworkInfo->u.setup.pNetworkCredentialInfo,
                                                          pNetworkConnection );

        if( status == IOT_NETWORK_SUCCESS )
        {
            /* This MQTT connection owns the network connection it created and
             * should destroy it on cleanup. */
            *pCreatedNewNetworkConnection = true;
        }
        else
        {
            IotLogError( "Failed to create network connection: %d", status );
        }
    }
    else
    {
        /* A connection already exists; the caller should not destroy
         * it on cleanup. */
        *pNetworkConnection = pNetworkInfo->u.pNetworkConnection;
        *pCreatedNewNetworkConnection = false;
    }

    return status;
}

/*-----------------------------------------------------------*/

static _mqttConnection_t * _createMqttConnection( bool awsIotMqttMode,
                                                  const IotMqttNetworkInfo_t * pNetworkInfo,
                                                  uint16_t keepAliveSeconds )
{
    bool status = true;
    _mqttConnection_t * pMqttConnection = NULL;
    bool referencesMutexCreated = false, subscriptionMutexCreated = false;

    /* Allocate memory for the new MQTT connection. */
    pMqttConnection = IotMqtt_MallocConnection( sizeof( _mqttConnection_t ) );

    if( pMqttConnection == NULL )
    {
        IotLogError( "Failed to allocate memory for new connection." );

        status = false;
    }
    else
    {
        /* Clear the MQTT connection, then copy the MQTT server mode, network
         * interface, and disconnect callback. */
        ( void ) memset( pMqttConnection, 0x00, sizeof( _mqttConnection_t ) );
        pMqttConnection->awsIotMqttMode = awsIotMqttMode;
        pMqttConnection->pNetworkInterface = pNetworkInfo->pNetworkInterface;
        pMqttConnection->disconnectCallback = pNetworkInfo->disconnectCallback;

        /* Start a new MQTT connection with a reference count of 1. */
        pMqttConnection->references = 1;

        /* Create the references mutex for a new connection. It is a recursive mutex. */
        referencesMutexCreated = IotMutex_Create( &( pMqttConnection->referencesMutex ), true );

        if( referencesMutexCreated == false )
        {
            IotLogError( "Failed to create references mutex for new connection." );

            status = false;
        }
    }

    if( status == true )
    {
        /* Create the subscription mutex for a new connection. */
        subscriptionMutexCreated = IotMutex_Create( &( pMqttConnection->subscriptionMutex ), false );

        if( subscriptionMutexCreated == false )
        {
            IotLogError( "Failed to create subscription mutex for new connection." );

            status = false;
        }
        else
        {
            /* Create the new connection's subscription and operation lists. */
            IotListDouble_Create( &( pMqttConnection->subscriptionList ) );
            IotListDouble_Create( &( pMqttConnection->pendingProcessing ) );
            IotListDouble_Create( &( pMqttConnection->pendingResponse ) );

            /* Check if keep-alive is active for this connection. */
            if( keepAliveSeconds != 0U )
            {
                status = _createKeepAliveOperation( pNetworkInfo,
                                                    keepAliveSeconds,
                                                    pMqttConnection );
            }
        }
    }

    /* Clean up mutexes and connection if this function failed. */
    if( status == false )
    {
        if( subscriptionMutexCreated == true )
        {
            IotMutex_Destroy( &( pMqttConnection->subscriptionMutex ) );
        }

        if( referencesMutexCreated == true )
        {
            IotMutex_Destroy( &( pMqttConnection->referencesMutex ) );
        }

        if( pMqttConnection != NULL )
        {
            IotMqtt_FreeConnection( pMqttConnection );
            pMqttConnection = NULL;
        }
    }

    return pMqttConnection;
}

/*-----------------------------------------------------------*/

static void _destroyMqttConnection( _mqttConnection_t * pMqttConnection )
{
    IotNetworkError_t networkStatus = IOT_NETWORK_SUCCESS;

    /* Clean up keep-alive if still allocated. */
    if( pMqttConnection->pingreq.u.operation.periodic.ping.keepAliveMs != 0U )
    {
        IotLogDebug( "(MQTT connection %p) Cleaning up keep-alive.", pMqttConnection );

        _getMqttFreePacketFunc( pMqttConnection->pSerializer )( pMqttConnection->pingreq.u.operation.pMqttPacket );

        /* Clear data about the keep-alive. */
        pMqttConnection->pingreq.u.operation.periodic.ping.keepAliveMs = 0;
        pMqttConnection->pingreq.u.operation.pMqttPacket = NULL;
        pMqttConnection->pingreq.u.operation.packetSize = 0;

        /* Decrement reference count. */
        pMqttConnection->references--;
    }

    /* A connection to be destroyed should have no keep-alive and at most 1
     * reference. */
    IotMqtt_Assert( pMqttConnection->references <= 1 );
    IotMqtt_Assert( pMqttConnection->pingreq.u.operation.periodic.ping.keepAliveMs == 0U );
    IotMqtt_Assert( pMqttConnection->pingreq.u.operation.pMqttPacket == NULL );
    IotMqtt_Assert( pMqttConnection->pingreq.u.operation.packetSize == 0U );

    /* Remove all subscriptions. */
    IotMutex_Lock( &( pMqttConnection->subscriptionMutex ) );
    IotListDouble_RemoveAllMatches( &( pMqttConnection->subscriptionList ),
                                    _mqttSubscription_setUnsubscribe,
                                    NULL,
                                    _mqttSubscription_tryDestroy,
                                    offsetof( _mqttSubscription_t, link ) );
    IotMutex_Unlock( &( pMqttConnection->subscriptionMutex ) );

    /* Destroy an owned network connection. */
    if( pMqttConnection->ownNetworkConnection == true )
    {
        networkStatus = pMqttConnection->pNetworkInterface->destroy( pMqttConnection->pNetworkConnection );

        if( networkStatus != IOT_NETWORK_SUCCESS )
        {
            IotLogWarn( "(MQTT connection %p) Failed to destroy network connection.",
                        pMqttConnection );
        }
        else
        {
            IotLogInfo( "(MQTT connection %p) Network connection destroyed.",
                        pMqttConnection );
        }
    }

    /* Destroy mutexes. */
    IotMutex_Destroy( &( pMqttConnection->referencesMutex ) );
    IotMutex_Destroy( &( pMqttConnection->subscriptionMutex ) );

    IotLogDebug( "(MQTT connection %p) Connection destroyed.", pMqttConnection );

    /* Free connection. */
    IotMqtt_FreeConnection( pMqttConnection );
}

/*-----------------------------------------------------------*/

static IotMqttError_t _subscriptionCommonSetup( IotMqttOperationType_t operation,
                                                IotMqttConnection_t mqttConnection,
                                                const IotMqttSubscription_t * pSubscriptionList,
                                                size_t subscriptionCount,
                                                uint32_t flags,
                                                const IotMqttOperation_t * const pOperationReference )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    /* This function should only be called for subscribe or unsubscribe. */
    IotMqtt_Assert( ( operation == IOT_MQTT_SUBSCRIBE ) ||
                    ( operation == IOT_MQTT_UNSUBSCRIBE ) );

    /* Check that IotMqtt_Init was called. */
    if( _checkInit() == false )
    {
        status = IOT_MQTT_NOT_INITIALIZED;
    }
    else
    {
        /* Check that all elements in the subscription list are valid. */
        if( _IotMqtt_ValidateSubscriptionList( operation,
                                               mqttConnection->awsIotMqttMode,
                                               pSubscriptionList,
                                               subscriptionCount ) == false )
        {
            status = IOT_MQTT_BAD_PARAMETER;
        }
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Check that a reference pointer is provided for a waitable operation. */
        if( ( flags & IOT_MQTT_FLAG_WAITABLE ) == IOT_MQTT_FLAG_WAITABLE )
        {
            if( pOperationReference == NULL )
            {
                IotLogError( "Reference must be provided for a waitable %s.",
                             IotMqtt_OperationType( operation ) );

                status = IOT_MQTT_BAD_PARAMETER;
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _subscriptionCreateAndSerialize( IotMqttOperationType_t operation,
                                                       IotMqttConnection_t mqttConnection,
                                                       IotMqttSerializeSubscribe_t serializeSubscription,
                                                       const IotMqttSubscription_t * pSubscriptionList,
                                                       size_t subscriptionCount,
                                                       uint32_t flags,
                                                       const IotMqttCallbackInfo_t * pCallbackInfo,
                                                       _mqttOperation_t ** ppSubscriptionOperation )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    _mqttOperation_t * pSubscriptionOperation = NULL;

    /* Create a subscription operation. */
    status = _IotMqtt_CreateOperation( mqttConnection,
                                       flags,
                                       pCallbackInfo,
                                       ppSubscriptionOperation );

    if( status == IOT_MQTT_SUCCESS )
    {
        pSubscriptionOperation = ( *ppSubscriptionOperation );


        /* Check the subscription operation data and set the operation type. */
        IotMqtt_Assert( pSubscriptionOperation->u.operation.status == IOT_MQTT_STATUS_PENDING );
        IotMqtt_Assert( pSubscriptionOperation->u.operation.periodic.retry.limit == 0U );
        pSubscriptionOperation->u.operation.type = operation;

        /* Generate a subscription packet from the subscription list. */
        status = serializeSubscription( pSubscriptionList,
                                        subscriptionCount,
                                        &( pSubscriptionOperation->u.operation.pMqttPacket ),
                                        &( pSubscriptionOperation->u.operation.packetSize ),
                                        &( pSubscriptionOperation->u.operation.packetIdentifier ) );
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Check the serialized MQTT packet. */
        IotMqtt_Assert( pSubscriptionOperation->u.operation.pMqttPacket != NULL );
        IotMqtt_Assert( pSubscriptionOperation->u.operation.packetSize > 0U );
    }

    return status;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _sendMqttMessage( _mqttOperation_t * pMqttOperation,
                                        uint32_t flags )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    IotMqtt_Assert( pMqttOperation != NULL );

    /* Send the SUBSCRIBE packet. */
    if( ( flags & MQTT_INTERNAL_FLAG_BLOCK_ON_SEND ) == MQTT_INTERNAL_FLAG_BLOCK_ON_SEND )
    {
        _IotMqtt_ProcessSend( &( pMqttOperation->job ), pMqttOperation );
    }
    else
    {
        status = _IotMqtt_ScheduleOperation( pMqttOperation,
                                             _IotMqtt_ProcessSend,
                                             0 );
    }

    return status;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _subscriptionCommon( IotMqttOperationType_t operation,
                                           IotMqttConnection_t mqttConnection,
                                           IotMqttSerializeSubscribe_t serializeSubscription,
                                           const IotMqttSubscription_t * pSubscriptionList,
                                           size_t subscriptionCount,
                                           uint32_t flags,
                                           const IotMqttCallbackInfo_t * pCallbackInfo,
                                           IotMqttOperation_t * const pOperationReference )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    _mqttOperation_t * pSubscriptionOperation = NULL;

    /* Create and serialize the subscription operation. */
    status = _subscriptionCreateAndSerialize( operation,
                                              mqttConnection,
                                              serializeSubscription,
                                              pSubscriptionList,
                                              subscriptionCount,
                                              flags,
                                              pCallbackInfo,
                                              &pSubscriptionOperation );

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Add the subscription list for a SUBSCRIBE. */
        if( operation == IOT_MQTT_SUBSCRIBE )
        {
            status = _IotMqtt_AddSubscriptions( mqttConnection,
                                                pSubscriptionOperation->u.operation.packetIdentifier,
                                                pSubscriptionList,
                                                subscriptionCount );
        }
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Set the reference, if provided. */
        _setOperationReference( pOperationReference, pSubscriptionOperation );

        /* Send or schedule subscribe request. */
        status = _sendMqttMessage( pSubscriptionOperation, flags );

        if( status != IOT_MQTT_SUCCESS )
        {
            IotLogError( "(MQTT connection %p) Failed to schedule %s for sending.",
                         mqttConnection,
                         IotMqtt_OperationType( operation ) );

            if( operation == IOT_MQTT_SUBSCRIBE )
            {
                _IotMqtt_RemoveSubscriptionByPacket( mqttConnection,
                                                     pSubscriptionOperation->u.operation.packetIdentifier,
                                                     MQTT_REMOVE_ALL_SUBSCRIPTIONS );
            }

            /* Clear the previously set (and now invalid) reference. */
            _setOperationReference( pOperationReference, IOT_MQTT_OPERATION_INITIALIZER );
        }
    }

    /* Clean up if this function failed. */
    if( status != IOT_MQTT_SUCCESS )
    {
        if( pSubscriptionOperation != NULL )
        {
            _IotMqtt_DestroyOperation( pSubscriptionOperation );
        }
    }
    else
    {
        status = IOT_MQTT_STATUS_PENDING;

        IotLogInfo( "(MQTT connection %p) %s operation scheduled.",
                    mqttConnection,
                    IotMqtt_OperationType( operation ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

static void _setOperationReference( IotMqttOperation_t * const pOperationReference,
                                    _mqttOperation_t * pNewOperation )
{
    if( pOperationReference != NULL )
    {
        *pOperationReference = pNewOperation;
    }
}

/*-----------------------------------------------------------*/

static IotMqttError_t _waitForOperation( IotMqttOperation_t operation,
                                         uint32_t timeoutMs )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    if( IotSemaphore_TimedWait( &( operation->u.operation.notify.waitSemaphore ),
                                timeoutMs ) == false )
    {
        status = IOT_MQTT_TIMEOUT;

        /* Attempt to cancel the job of the timed out operation. */
        ( void ) _IotMqtt_DecrementOperationReferences( operation, true );

        /* Clean up lingering subscriptions from a timed-out SUBSCRIBE. */
        if( operation->u.operation.type == IOT_MQTT_SUBSCRIBE )
        {
            IotLogDebug( "(MQTT connection %p, SUBSCRIBE operation %p) Cleaning up"
                         " subscriptions of timed-out SUBSCRIBE.",
                         operation->pMqttConnection,
                         operation );

            _IotMqtt_RemoveSubscriptionByPacket( operation->pMqttConnection,
                                                 operation->u.operation.packetIdentifier,
                                                 MQTT_REMOVE_ALL_SUBSCRIPTIONS );
        }
    }
    else
    {
        /* Retrieve the status of the completed operation. */
        status = operation->u.operation.status;
    }

    /* Coverity finds a MISRA 13.2 violation in this log statement as the order
     * of evaluation for IotMqtt_OperationType and IotMqtt_strerror is not
     * defined. This is not an issue as these functions do not change data and
     * only convert codes into constant strings. */
    /* coverity[misra_c_2012_rule_13_2_violation] */
    IotLogInfo( "(MQTT connection %p, %s operation %p) Wait complete with result %s.",
                operation->pMqttConnection,
                IotMqtt_OperationType( operation->u.operation.type ),
                operation,
                IotMqtt_strerror( status ) );

    return status;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _scheduleKeepAlive( IotMqttConnection_t pMqttConnection )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    taskPoolError_t taskPoolStatus = TASKPOOL_SUCCESS;

    /* Check if a keep-alive job should be scheduled. */
    if( pMqttConnection->pingreq.u.operation.periodic.ping.keepAliveMs != 0U )
    {
        IotLogDebug( "Scheduling first MQTT keep-alive job." );

        taskPoolStatus = taskPoolScheduleDeferred( &( pMqttConnection->pingreq.job ),
                                                   pMqttConnection->pingreq.u.operation.periodic.ping.nextPeriodMs );
    }

    if( taskPoolStatus != TASKPOOL_SUCCESS )
    {
        status = IOT_MQTT_SCHEDULING_ERROR;
    }

    return status;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _sendConnectRequest( _mqttOperation_t * pOperation,
                                           uint32_t timeoutMs )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    IotMqtt_Assert( pOperation != NULL );

    /* Check the serialized MQTT packet. */
    IotMqtt_Assert( pOperation->u.operation.pMqttPacket != NULL );
    IotMqtt_Assert( pOperation->u.operation.packetSize > 0U );

    /* Send the CONNECT packet. */
    _IotMqtt_ProcessSend( &( pOperation->job ), pOperation );

    /* Wait for the CONNECT operation to complete, i.e. wait for CONNACK. */
    status = IotMqtt_Wait( pOperation, timeoutMs );

    return status;
}

/*-----------------------------------------------------------*/

static IotMqttError_t _addSubscriptions( _mqttOperation_t * pOperation,
                                         IotMqttConnection_t pMqttConnection,
                                         const IotMqttConnectInfo_t * pConnectInfo )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;

    IotMqtt_Assert( pOperation != NULL );
    IotMqtt_Assert( pConnectInfo != NULL );

    /* Ensure the members set by operation creation and serialization
     * are appropriate for a blocking CONNECT. */
    IotMqtt_Assert( pOperation->u.operation.status == IOT_MQTT_STATUS_PENDING );
    IotMqtt_Assert( ( pOperation->u.operation.flags & IOT_MQTT_FLAG_WAITABLE )
                    == IOT_MQTT_FLAG_WAITABLE );
    IotMqtt_Assert( pOperation->u.operation.periodic.retry.limit == 0U );

    /* Set the operation type. */
    pOperation->u.operation.type = IOT_MQTT_CONNECT;

    /* Add previous session subscriptions. */
    if( pConnectInfo->pPreviousSubscriptions != NULL )
    {
        /* Previous subscription count should have been validated as nonzero. */
        IotMqtt_Assert( pConnectInfo->previousSubscriptionCount > 0U );

        status = _IotMqtt_AddSubscriptions( pMqttConnection,
                                            IOT_MQTT_PREVIOUS_SUBSCRIPTIONS_PACKET_ID,
                                            pConnectInfo->pPreviousSubscriptions,
                                            pConnectInfo->previousSubscriptionCount );
    }

    return status;
}

/*-----------------------------------------------------------*/

static void _handleConnectFailure( IotMqttConnection_t pMqttConnection,
                                   IotNetworkConnection_t pNetworkConnection,
                                   const IotMqttNetworkInfo_t * pNetworkInfo,
                                   _mqttOperation_t * pOperation,
                                   bool ownNetworkConnection )
{
    IotNetworkError_t networkStatus = IOT_NETWORK_SUCCESS;

    /* The network connection must be closed if it was created. */
    if( ownNetworkConnection == true )
    {
        networkStatus = pNetworkInfo->pNetworkInterface->close( pNetworkConnection );

        if( networkStatus != IOT_NETWORK_SUCCESS )
        {
            IotLogWarn( "Failed to close network connection." );
        }
        else
        {
            IotLogInfo( "Network connection closed on error." );
        }
    }

    if( pOperation != NULL )
    {
        _IotMqtt_DestroyOperation( pOperation );
    }

    if( pMqttConnection != NULL )
    {
        _destroyMqttConnection( pMqttConnection );
    }
}

/*-----------------------------------------------------------*/

bool _IotMqtt_IncrementConnectionReferences( _mqttConnection_t * pMqttConnection )
{
    bool disconnected = false;

    /* Lock the mutex protecting the reference count. */
    IotMutex_Lock( &( pMqttConnection->referencesMutex ) );

    /* Reference count must not be negative. */
    IotMqtt_Assert( pMqttConnection->references >= 0 );

    /* Read connection status. */
    disconnected = pMqttConnection->disconnected;

    /* Increment the connection's reference count if it is not disconnected. */
    if( disconnected == false )
    {
        ( pMqttConnection->references )++;

        /* In some implementations IotLogDebug() maps to C standard printing API
         * that needs specific primitive types for format specifiers. Also,
         * inttypes.h may not be available on some C99 compilers, despite
         * stdint.h being available. */
        /* coverity[misra_c_2012_directive_4_6_violation] */
        IotLogDebug( "(MQTT connection %p) Reference count changed from %ld to %ld.",
                     pMqttConnection,
                     ( long int ) pMqttConnection->references - 1,
                     ( long int ) pMqttConnection->references );
    }
    else
    {
        IotLogWarn( "(MQTT connection %p) Attempt to use closed connection.", pMqttConnection );
    }

    IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

    return( disconnected == false );
}

/*-----------------------------------------------------------*/

void _IotMqtt_DecrementConnectionReferences( _mqttConnection_t * pMqttConnection )
{
    bool destroyConnection = false;

    /* Lock the mutex protecting the reference count. */
    IotMutex_Lock( &( pMqttConnection->referencesMutex ) );

    /* Decrement reference count. It must not be negative. */
    ( pMqttConnection->references )--;
    IotMqtt_Assert( pMqttConnection->references >= 0 );

    /* In some implementations IotLogDebug() maps to C standard printing API
     * that needs specific primitive types for format specifiers. Also,
     * inttypes.h may not be available on some C99 compilers, despite stdint.h
     * being available. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    IotLogDebug( "(MQTT connection %p) Reference count changed from %ld to %ld.",
                 pMqttConnection,
                 ( long int ) pMqttConnection->references + 1,
                 ( long int ) pMqttConnection->references );

    /* Check if this connection may be destroyed. */
    if( pMqttConnection->references == 0 )
    {
        destroyConnection = true;
    }

    IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

    /* Destroy an unreferenced MQTT connection. */
    if( destroyConnection == true )
    {
        IotLogDebug( "(MQTT connection %p) Connection will be destroyed now.",
                     pMqttConnection );
        _destroyMqttConnection( pMqttConnection );
    }
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_Init( void )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    uint32_t allowInitialization = Atomic_CompareAndSwap_u32( &_initCalled,
                                                              MQTT_LIBRARY_INITIALIZED,
                                                              MQTT_LIBRARY_UNINITIALIZED );

    if( allowInitialization == 1U )
    {

        /* Initialize the task pool module, which is a dependency for the HTTPS library. */
        taskPoolCreateSystemTaskPool(); 

        /* Call any additional serializer initialization function if serializer
         * overrides are enabled. */
        #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
            #ifdef _IotMqtt_InitSerializeAdditional
                if( _IotMqtt_InitSerializeAdditional() == false )
                {
                    /* Log initialization status. */
                    IotLogError( "Failed to initialize MQTT library serializer. " );

                    status = IOT_MQTT_INIT_FAILED;
                }

                if( status == IOT_MQTT_SUCCESS )
            #endif /* ifdef _IotMqtt_InitSerializeAdditional */
        #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */
        {
            IotLogInfo( "MQTT library successfully initialized." );
        }
    }
    else
    {
        IotLogWarn( "IotMqtt_Init called with library already initialized." );
    }

    return status;
}

/*-----------------------------------------------------------*/

void IotMqtt_Cleanup( void )
{
    uint32_t allowCleanup = Atomic_CompareAndSwap_u32( &_initCalled,
                                                       MQTT_LIBRARY_UNINITIALIZED,
                                                       MQTT_LIBRARY_INITIALIZED );

    if( allowCleanup == 1U )
    {
        /* Call any additional serializer cleanup initialization function if serializer
         * overrides are enabled. */
        #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
            #ifdef _IotMqtt_CleanupSerializeAdditional
                _IotMqtt_CleanupSerializeAdditional();
            #endif
        #endif

        IotLogInfo( "MQTT library cleanup done." );
    }
    else
    {
        IotLogWarn( "IotMqtt_Init was not called before IotMqtt_Cleanup." );
    }
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_Connect( const IotMqttNetworkInfo_t * pNetworkInfo,
                                const IotMqttConnectInfo_t * pConnectInfo,
                                uint32_t timeoutMs,
                                IotMqttConnection_t * const pMqttConnection )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    bool ownNetworkConnection = false;
    IotNetworkError_t networkStatus = IOT_NETWORK_SUCCESS;
    IotNetworkConnection_t pNetworkConnection = NULL;
    _mqttOperation_t * pOperation = NULL;
    _mqttConnection_t * pNewMqttConnection = NULL;

    /* Check that IotMqtt_Init was called. */
    if( _checkInit() == false )
    {
        status = IOT_MQTT_NOT_INITIALIZED;
    }
    /* Validate network interface and connect info. */
    else if( _IotMqtt_ValidateConnect( pConnectInfo ) == false )
    {
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else
    {
        networkStatus = _createNetworkConnection( pNetworkInfo,
                                                  &pNetworkConnection,
                                                  &ownNetworkConnection );

        if( networkStatus != IOT_NETWORK_SUCCESS )
        {
            status = IOT_MQTT_NETWORK_ERROR;
        }
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        IotLogInfo( "Establishing new MQTT connection." );

        /* Initialize a new MQTT connection object. */
        pNewMqttConnection = _createMqttConnection( pConnectInfo->awsIotMqttMode,
                                                    pNetworkInfo,
                                                    pConnectInfo->keepAliveSeconds );

        if( pNewMqttConnection == NULL )
        {
            status = IOT_MQTT_NO_MEMORY;
        }
    }

    /* Set the MQTT receive callback. */
    if( status == IOT_MQTT_SUCCESS )
    {
        /* Set the network connection associated with the MQTT connection. */
        pNewMqttConnection->pNetworkConnection = pNetworkConnection;
        pNewMqttConnection->ownNetworkConnection = ownNetworkConnection;

        /* Set the MQTT packet serializer overrides. */
        #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
            pNewMqttConnection->pSerializer = pNetworkInfo->pMqttSerializer;
        #else
            pNewMqttConnection->pSerializer = NULL;
        #endif

        networkStatus = pNewMqttConnection->pNetworkInterface->setReceiveCallback( pNetworkConnection,
                                                                                   IotMqtt_ReceiveCallback,
                                                                                   pNewMqttConnection );

        if( networkStatus != IOT_NETWORK_SUCCESS )
        {
            IotLogError( "Failed to set MQTT network receive callback." );

            status = IOT_MQTT_NETWORK_ERROR;
        }
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Create a CONNECT operation. */
        status = _IotMqtt_CreateOperation( pNewMqttConnection,
                                           IOT_MQTT_FLAG_WAITABLE,
                                           NULL,
                                           &pOperation );
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Add subscriptions to the operation */
        status = _addSubscriptions( pOperation,
                                    pNewMqttConnection,
                                    pConnectInfo );
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Convert the connect info and will info objects to an MQTT CONNECT packet. */
        status = _getMqttConnectSerializer( pNetworkInfo->pMqttSerializer )( pConnectInfo,
                                                                             &( pOperation->u.operation.pMqttPacket ),
                                                                             &( pOperation->u.operation.packetSize ) );
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Send the CONNECT packet */
        status = _sendConnectRequest( pOperation, timeoutMs );

        /* The call to wait inside _sendConnectRequest cleans up
         * the CONNECT operation, so set the pointer to NULL. */
        pOperation = NULL;

        /* When a connection is successfully established, schedule keep-alive job. */
        if( status == IOT_MQTT_SUCCESS )
        {
            status = _scheduleKeepAlive( pNewMqttConnection );
        }
    }

    if( status != IOT_MQTT_SUCCESS )
    {
        IotLogError( "Failed to establish new MQTT connection, error %s.",
                     IotMqtt_strerror( status ) );

        _handleConnectFailure( pNewMqttConnection,
                               pNetworkConnection,
                               pNetworkInfo,
                               pOperation,
                               ownNetworkConnection );
    }
    else
    {
        IotLogInfo( "New MQTT connection %p established.", pMqttConnection );

        /* Set the output parameter. */
        *pMqttConnection = pNewMqttConnection;
    }

    return status;
}

/*-----------------------------------------------------------*/

void IotMqtt_Disconnect( IotMqttConnection_t mqttConnection,
                         uint32_t flags )
{
    bool disconnected = false, initCalled = false;
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    _mqttOperation_t * pOperation = NULL;

    /* Check that IotMqtt_Init was called. */
    initCalled = _checkInit();

    if( initCalled == false )
    {
        status = IOT_MQTT_STATUS_PENDING;
    }
    else
    {
        /* Only send a DISCONNECT packet if the connection is active and the "cleanup only"
         * flag is not set. */
        if( ( flags & IOT_MQTT_FLAG_CLEANUP_ONLY ) == IOT_MQTT_FLAG_CLEANUP_ONLY )
        {
            status = IOT_MQTT_STATUS_PENDING;
        }
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Read the connection status. */
        IotMutex_Lock( &( mqttConnection->referencesMutex ) );
        disconnected = mqttConnection->disconnected;
        IotMutex_Unlock( &( mqttConnection->referencesMutex ) );

        if( disconnected == true )
        {
            status = IOT_MQTT_STATUS_PENDING;
        }
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        IotLogInfo( "(MQTT connection %p) Disconnecting connection.", mqttConnection );

        /* Create a DISCONNECT operation. This function blocks until the DISCONNECT
         * packet is sent, so it sets IOT_MQTT_FLAG_WAITABLE. */
        status = _IotMqtt_CreateOperation( mqttConnection,
                                           IOT_MQTT_FLAG_WAITABLE,
                                           NULL,
                                           &pOperation );

        if( status == IOT_MQTT_SUCCESS )
        {
            /* Ensure that the members set by operation creation and serialization
             * are appropriate for a blocking DISCONNECT. */
            IotMqtt_Assert( pOperation->u.operation.status == IOT_MQTT_STATUS_PENDING );
            IotMqtt_Assert( ( pOperation->u.operation.flags & IOT_MQTT_FLAG_WAITABLE )
                            == IOT_MQTT_FLAG_WAITABLE );
            IotMqtt_Assert( pOperation->u.operation.periodic.retry.limit == 0U );

            /* Set the operation type. */
            pOperation->u.operation.type = IOT_MQTT_DISCONNECT;

            /* Generate a DISCONNECT packet. */
            status = _getMqttDisconnectSerializer( mqttConnection->pSerializer )( &( pOperation->u.operation.pMqttPacket ),
                                                                                  &( pOperation->u.operation.packetSize ) );
        }
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Check the serialized MQTT packet. */
        IotMqtt_Assert( pOperation->u.operation.pMqttPacket != NULL );
        IotMqtt_Assert( pOperation->u.operation.packetSize > 0U );

        /* Send the DISCONNECT packet. */
        _IotMqtt_ProcessSend( &( pOperation->job ), pOperation );

        /* Wait a short time for the DISCONNECT packet to be transmitted. */
        status = IotMqtt_Wait( pOperation,
                               IOT_MQTT_RESPONSE_WAIT_MS );

        /* A wait on DISCONNECT should only ever return SUCCESS, TIMEOUT,
         * or NETWORK ERROR. */
        if( status == IOT_MQTT_SUCCESS )
        {
            IotLogInfo( "(MQTT connection %p) Connection disconnected.", mqttConnection );
        }
        else
        {
            IotMqtt_Assert( ( status == IOT_MQTT_TIMEOUT ) ||
                            ( status == IOT_MQTT_NETWORK_ERROR ) );

            IotLogWarn( "(MQTT connection %p) DISCONNECT not sent, error %s.",
                        mqttConnection,
                        IotMqtt_strerror( status ) );
        }
    }

    if( initCalled == true )
    {
        /* Close the underlying network connection. This also cleans up keep-alive.
         * Coverity finds a USE_AFTER_FREE error at this line. This is a false positive.
         *
         * This error is triggered by a dereference of 'mqttConnection' in
         * '_IotMqtt_CloseNetworkConnection'. Coverity assumes that 'mqttConnection'
         * was freed in '_IotMqtt_CreateOperation' above, where cleanup code will
         * free 'pNewMqttConnection' upon allocation failure.
         *
         * This will never happen as a valid MQTT connection passed to this
         * function always has a positive reference count; therefore,
         * '_IotMqtt_CreateOperation' will not free it. Only unreferenced MQTT
         * connections will be freed.
         *
         * The annotation below suppresses this Coverity error.
         */
        /* coverity[deref_arg] */
        _IotMqtt_CloseNetworkConnection( IOT_MQTT_DISCONNECT_CALLED,
                                         mqttConnection );

        /* Check if the connection may be destroyed. */
        IotMutex_Lock( &( mqttConnection->referencesMutex ) );

        /* At this point, the connection should be marked disconnected. */
        IotMqtt_Assert( mqttConnection->disconnected == true );

        /* Attempt cancel and destroy each operation in the connection's lists. */
        IotListDouble_RemoveAll( &( mqttConnection->pendingProcessing ),
                                 _mqttOperation_tryDestroy,
                                 offsetof( _mqttOperation_t, link ) );

        IotListDouble_RemoveAll( &( mqttConnection->pendingResponse ),
                                 _mqttOperation_tryDestroy,
                                 offsetof( _mqttOperation_t, link ) );

        IotMutex_Unlock( &( mqttConnection->referencesMutex ) );

        /* Decrement the connection reference count and destroy it if possible. */
        _IotMqtt_DecrementConnectionReferences( mqttConnection );
    }
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_SubscribeAsync( IotMqttConnection_t mqttConnection,
                                       const IotMqttSubscription_t * pSubscriptionList,
                                       size_t subscriptionCount,
                                       uint32_t flags,
                                       const IotMqttCallbackInfo_t * pCallbackInfo,
                                       IotMqttOperation_t * const pSubscribeOperation )
{
    IotMqttError_t status = _subscriptionCommonSetup( IOT_MQTT_SUBSCRIBE,
                                                      mqttConnection,
                                                      pSubscriptionList,
                                                      subscriptionCount,
                                                      flags,
                                                      pSubscribeOperation );

    if( IOT_MQTT_SUCCESS == status )
    {
        status = _subscriptionCommon( IOT_MQTT_SUBSCRIBE,
                                      mqttConnection,
                                      _getMqttSubscribeSerializer( mqttConnection->pSerializer ),
                                      pSubscriptionList,
                                      subscriptionCount,
                                      flags,
                                      pCallbackInfo,
                                      pSubscribeOperation );
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_SubscribeSync( IotMqttConnection_t mqttConnection,
                                      const IotMqttSubscription_t * pSubscriptionList,
                                      size_t subscriptionCount,
                                      uint32_t flags,
                                      uint32_t timeoutMs )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttOperation_t subscribeOperation = IOT_MQTT_OPERATION_INITIALIZER;

    /* Flags are not used, but the parameter is present for future compatibility. */
    ( void ) flags;

    /* Call the asynchronous SUBSCRIBE function. */
    status = IotMqtt_SubscribeAsync( mqttConnection,
                                     pSubscriptionList,
                                     subscriptionCount,
                                     IOT_MQTT_FLAG_WAITABLE | MQTT_INTERNAL_FLAG_BLOCK_ON_SEND,
                                     NULL,
                                     &subscribeOperation );

    /* Wait for the SUBSCRIBE operation to complete. */
    if( status == IOT_MQTT_STATUS_PENDING )
    {
        status = IotMqtt_Wait( subscribeOperation, timeoutMs );
    }

    /* Ensure that a status was set. */
    IotMqtt_Assert( status != IOT_MQTT_STATUS_PENDING );

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_UnsubscribeAsync( IotMqttConnection_t mqttConnection,
                                         const IotMqttSubscription_t * pSubscriptionList,
                                         size_t subscriptionCount,
                                         uint32_t flags,
                                         const IotMqttCallbackInfo_t * pCallbackInfo,
                                         IotMqttOperation_t * const pUnsubscribeOperation )
{
    IotMqttError_t status = _subscriptionCommonSetup( IOT_MQTT_UNSUBSCRIBE,
                                                      mqttConnection,
                                                      pSubscriptionList,
                                                      subscriptionCount,
                                                      flags,
                                                      pUnsubscribeOperation );

    if( IOT_MQTT_SUCCESS == status )
    {
        /* Remove the MQTT subscription list for an UNSUBSCRIBE. */
        _IotMqtt_RemoveSubscriptionByTopicFilter( mqttConnection,
                                                  pSubscriptionList,
                                                  subscriptionCount );

        status = _subscriptionCommon( IOT_MQTT_UNSUBSCRIBE,
                                      mqttConnection,
                                      _getMqttUnsubscribeSerializer( mqttConnection->pSerializer ),
                                      pSubscriptionList,
                                      subscriptionCount,
                                      flags,
                                      pCallbackInfo,
                                      pUnsubscribeOperation );
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_UnsubscribeSync( IotMqttConnection_t mqttConnection,
                                        const IotMqttSubscription_t * pSubscriptionList,
                                        size_t subscriptionCount,
                                        uint32_t flags,
                                        uint32_t timeoutMs )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttOperation_t unsubscribeOperation = IOT_MQTT_OPERATION_INITIALIZER;

    /* Flags are not used, but the parameter is present for future compatibility. */
    ( void ) flags;

    /* Call the asynchronous UNSUBSCRIBE function. */
    status = IotMqtt_UnsubscribeAsync( mqttConnection,
                                       pSubscriptionList,
                                       subscriptionCount,
                                       IOT_MQTT_FLAG_WAITABLE | MQTT_INTERNAL_FLAG_BLOCK_ON_SEND,
                                       NULL,
                                       &unsubscribeOperation );

    /* Wait for the UNSUBSCRIBE operation to complete. */
    if( status == IOT_MQTT_STATUS_PENDING )
    {
        status = IotMqtt_Wait( unsubscribeOperation, timeoutMs );
    }

    /* Ensure that a status was set. */
    IotMqtt_Assert( status != IOT_MQTT_STATUS_PENDING );

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_PublishAsync( IotMqttConnection_t mqttConnection,
                                     const IotMqttPublishInfo_t * pPublishInfo,
                                     uint32_t flags,
                                     const IotMqttCallbackInfo_t * pCallbackInfo,
                                     IotMqttOperation_t * const pPublishOperation )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    _mqttOperation_t * pOperation = NULL;
    uint8_t ** pPacketIdentifierHigh = NULL;

    /* Check that IotMqtt_Init was called. */
    if( _checkInit() == false )
    {
        status = IOT_MQTT_NOT_INITIALIZED;
    }
    else if( _IotMqtt_ValidatePublish( mqttConnection->awsIotMqttMode,
                                       pPublishInfo,
                                       flags,
                                       pCallbackInfo,
                                       pPublishOperation ) == false )
    {
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else
    {
        /* Create a PUBLISH operation. */
        status = _IotMqtt_CreateOperation( mqttConnection,
                                           flags,
                                           pCallbackInfo,
                                           &pOperation );
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Check the PUBLISH operation data and set the operation type. */
        IotMqtt_Assert( pOperation->u.operation.status == IOT_MQTT_STATUS_PENDING );
        pOperation->u.operation.type = IOT_MQTT_PUBLISH_TO_SERVER;

        /* In AWS IoT MQTT mode, a pointer to the packet identifier must be saved. */
        if( mqttConnection->awsIotMqttMode == true )
        {
            pPacketIdentifierHigh = &( pOperation->u.operation.pPacketIdentifierHigh );
        }

        /* Generate a PUBLISH packet from pPublishInfo. */
        status = _getMqttPublishSerializer( mqttConnection->pSerializer )( pPublishInfo,
                                                                           &( pOperation->u.operation.pMqttPacket ),
                                                                           &( pOperation->u.operation.packetSize ),
                                                                           &( pOperation->u.operation.packetIdentifier ),
                                                                           pPacketIdentifierHigh );
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        /* Check the serialized MQTT packet. */
        IotMqtt_Assert( pOperation->u.operation.pMqttPacket != NULL );
        IotMqtt_Assert( pOperation->u.operation.packetSize > 0U );

        /* Initialize PUBLISH retry if retryLimit is set. */
        if( pPublishInfo->retryLimit > 0U )
        {
            /* A QoS 0 PUBLISH may not be retried. */
            if( pPublishInfo->qos != IOT_MQTT_QOS_0 )
            {
                pOperation->u.operation.periodic.retry.limit = pPublishInfo->retryLimit;
                pOperation->u.operation.periodic.retry.nextPeriodMs = pPublishInfo->retryMs;
            }
        }

        /* Set the reference, if provided. */
        if( pPublishInfo->qos != IOT_MQTT_QOS_0 )
        {
            _setOperationReference( pPublishOperation, pOperation );
        }

        /* Send the PUBLISH packet. */
        status = _sendMqttMessage( pOperation, flags );

        if( status != IOT_MQTT_SUCCESS )
        {
            IotLogError( "(MQTT connection %p) Failed to enqueue PUBLISH for sending.",
                         mqttConnection );

            /* Clear the previously set (and now invalid) reference. */
            if( pPublishInfo->qos != IOT_MQTT_QOS_0 )
            {
                _setOperationReference( pPublishOperation, IOT_MQTT_OPERATION_INITIALIZER );
            }
        }
    }

    /* Clean up the PUBLISH operation if this function fails. Otherwise, set the
     * appropriate return code based on QoS. */

    if( status != IOT_MQTT_SUCCESS )
    {
        if( pOperation != NULL )
        {
            _IotMqtt_DestroyOperation( pOperation );
        }
    }
    else
    {
        if( pPublishInfo->qos > IOT_MQTT_QOS_0 )
        {
            status = IOT_MQTT_STATUS_PENDING;
        }

        IotLogInfo( "(MQTT connection %p) MQTT PUBLISH operation queued.",
                    mqttConnection );
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_PublishSync( IotMqttConnection_t mqttConnection,
                                    const IotMqttPublishInfo_t * pPublishInfo,
                                    uint32_t flags,
                                    uint32_t timeoutMs )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttOperation_t publishOperation = IOT_MQTT_OPERATION_INITIALIZER,
                       * pPublishOperation = NULL;
    /* Set only the "serial" flag. */
    uint32_t syncFlags = MQTT_INTERNAL_FLAG_BLOCK_ON_SEND;

    /* Flags are currently ignored. */
    ( void ) flags;

    /* Set the waitable flag and reference for QoS 1 PUBLISH. */
    if( pPublishInfo->qos == IOT_MQTT_QOS_1 )
    {
        syncFlags |= IOT_MQTT_FLAG_WAITABLE;
        pPublishOperation = &publishOperation;
    }

    /* Call the asynchronous PUBLISH function. */
    status = IotMqtt_PublishAsync( mqttConnection,
                                   pPublishInfo,
                                   syncFlags,
                                   NULL,
                                   pPublishOperation );

    /* Wait for a queued QoS 1 PUBLISH to complete. */
    if( pPublishInfo->qos == IOT_MQTT_QOS_1 )
    {
        if( status == IOT_MQTT_STATUS_PENDING )
        {
            status = IotMqtt_Wait( publishOperation, timeoutMs );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t IotMqtt_Wait( IotMqttOperation_t operation,
                             uint32_t timeoutMs )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    _mqttConnection_t * pMqttConnection = NULL;

    /* Check that IotMqtt_Init was called. */
    if( _checkInit() == false )
    {
        status = IOT_MQTT_NOT_INITIALIZED;
    }
    /* Validate the given operation reference. */
    else if( _IotMqtt_ValidateOperation( operation ) == false )
    {
        status = IOT_MQTT_BAD_PARAMETER;
    }
    else
    {
        /* Check the MQTT connection status. */
        pMqttConnection = operation->pMqttConnection;
    }

    if( status == IOT_MQTT_SUCCESS )
    {
        IotMutex_Lock( &( pMqttConnection->referencesMutex ) );

        if( pMqttConnection->disconnected == true )
        {
            IotLogError( "(MQTT connection %p, %s operation %p) MQTT connection is closed. "
                         "Operation cannot be waited on.",
                         pMqttConnection,
                         IotMqtt_OperationType( operation->u.operation.type ),
                         operation );

            status = IOT_MQTT_NETWORK_ERROR;
        }
        else
        {
            IotLogInfo( "(MQTT connection %p, %s operation %p) Waiting for operation completion.",
                        pMqttConnection,
                        IotMqtt_OperationType( operation->u.operation.type ),
                        operation );
        }

        IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

        /* Only wait on an operation if the MQTT connection is active. */
        if( status == IOT_MQTT_SUCCESS )
        {
            status = _waitForOperation( operation, timeoutMs );
        }

        /* Wait is finished; decrement operation reference count. */
        if( _IotMqtt_DecrementOperationReferences( operation, false ) == true )
        {
            _IotMqtt_DestroyOperation( operation );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

const char * IotMqtt_strerror( IotMqttError_t status )
{
    const char * pMessage = NULL;

    switch( status )
    {
        case IOT_MQTT_SUCCESS:
            pMessage = "SUCCESS";
            break;

        case IOT_MQTT_STATUS_PENDING:
            pMessage = "PENDING";
            break;

        case IOT_MQTT_INIT_FAILED:
            pMessage = "INITIALIZATION FAILED";
            break;

        case IOT_MQTT_BAD_PARAMETER:
            pMessage = "BAD PARAMETER";
            break;

        case IOT_MQTT_NO_MEMORY:
            pMessage = "NO MEMORY";
            break;

        case IOT_MQTT_NETWORK_ERROR:
            pMessage = "NETWORK ERROR";
            break;

        case IOT_MQTT_SCHEDULING_ERROR:
            pMessage = "SCHEDULING ERROR";
            break;

        case IOT_MQTT_BAD_RESPONSE:
            pMessage = "BAD RESPONSE RECEIVED";
            break;

        case IOT_MQTT_TIMEOUT:
            pMessage = "TIMEOUT";
            break;

        case IOT_MQTT_SERVER_REFUSED:
            pMessage = "SERVER REFUSED";
            break;

        case IOT_MQTT_RETRY_NO_RESPONSE:
            pMessage = "NO RESPONSE";
            break;

        case IOT_MQTT_NOT_INITIALIZED:
            pMessage = "NOT INITIALIZED";
            break;

        default:
            pMessage = "INVALID STATUS";
            break;
    }

    return pMessage;
}

/*-----------------------------------------------------------*/

const char * IotMqtt_OperationType( IotMqttOperationType_t operation )
{
    const char * pMessage = NULL;

    switch( operation )
    {
        case IOT_MQTT_CONNECT:
            pMessage = "CONNECT";
            break;

        case IOT_MQTT_PUBLISH_TO_SERVER:
            pMessage = "PUBLISH";
            break;

        case IOT_MQTT_PUBACK:
            pMessage = "PUBACK";
            break;

        case IOT_MQTT_SUBSCRIBE:
            pMessage = "SUBSCRIBE";
            break;

        case IOT_MQTT_UNSUBSCRIBE:
            pMessage = "UNSUBSCRIBE";
            break;

        case IOT_MQTT_PINGREQ:
            pMessage = "PINGREQ";
            break;

        case IOT_MQTT_DISCONNECT:
            pMessage = "DISCONNECT";
            break;

        default:
            pMessage = "INVALID OPERATION";
            break;
    }

    return pMessage;
}

/*-----------------------------------------------------------*/

/* Provide access to internal functions and variables if testing. */
/* IOT_BUILD_TESTS is defined outside the code base, e.g. passed in by build command. */
/* coverity[misra_c_2012_rule_20_9_violation] */
/* coverity[caretline] */
#if IOT_BUILD_TESTS == 1
    #include "iot_test_access_mqtt_api.c"
#endif
