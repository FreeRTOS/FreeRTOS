/*
 * Amazon FreeRTOS MQTT V2.0.0
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
 * @file iot_mqtt_agent.c
 * @brief MQTT Agent implementation. Provides backwards compatibility between
 * MQTT v2 and MQTT v1.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "semphr.h"

/* MQTT v1 includes. */
#include "iot_mqtt_agent.h"
#include "iot_mqtt_agent_config.h"
#include "iot_mqtt_agent_config_defaults.h"

/* MQTT v2 include. */
#include "iot_mqtt.h"

/* Platform network include. */
#include "platform/iot_network_freertos.h"

/*-----------------------------------------------------------*/

/**
 * @brief Converts FreeRTOS ticks to milliseconds.
 */
#define mqttTICKS_TO_MS( xTicks )    ( xTicks * 1000 / configTICK_RATE_HZ )

/*-----------------------------------------------------------*/

/**
 * @brief Stores data to convert between the MQTT v1 subscription callback
 * and the MQTT v2 subscription callback.
 */
#if ( mqttconfigENABLE_SUBSCRIPTION_MANAGEMENT == 1 )
    typedef struct MQTTCallback
    {
        BaseType_t xInUse;                                                     /**< Whether this instance is in-use. */
        MQTTPublishCallback_t xFunction;                                       /**< MQTT v1 callback function. */
        void * pvParameter;                                                    /**< Parameter to xFunction. */

        uint16_t usTopicFilterLength;                                          /**< Length of pcTopicFilter. */
        char pcTopicFilter[ mqttconfigSUBSCRIPTION_MANAGER_MAX_TOPIC_LENGTH ]; /**< Topic filter. */
    } MQTTCallback_t;
#endif

/**
 * @brief Stores data on an active MQTT connection.
 */
typedef struct MQTTConnection
{
    IotMqttConnection_t xMQTTConnection; /**< MQTT v2 connection handle. */
    MQTTAgentCallback_t pxCallback;      /**< MQTT v1 global callback. */
    void * pvUserData;                   /**< Parameter to pxCallback. */
    StaticSemaphore_t xConnectionMutex;  /**< Protects from concurrent accesses. */
    #if ( mqttconfigENABLE_SUBSCRIPTION_MANAGEMENT == 1 )
        MQTTCallback_t xCallbacks        /**< Conversion table of MQTT v1 to MQTT v2 subscription callbacks. */
        [ mqttconfigSUBSCRIPTION_MANAGER_MAX_SUBSCRIPTIONS ];
    #endif
} MQTTConnection_t;

/*-----------------------------------------------------------*/

/**
 * @brief Convert an MQTT v2 return code to an MQTT v1 return code.
 *
 * @param[in] xMqttStatus The MQTT v2 return code.
 *
 * @return An equivalent MQTT v1 return code.
 */
static inline MQTTAgentReturnCode_t prvConvertReturnCode( IotMqttError_t xMqttStatus );

/**
 * @brief Wraps an MQTT v1 publish callback.
 *
 * @param[in] pvParameter The MQTT connection.
 * @param[in] pxPublish Information about the incoming publish.
 */
static void prvPublishCallbackWrapper( void * pvParameter,
                                       IotMqttCallbackParam_t * const pxPublish );

/**
 * @brief Wraps an MQTT v1 disconnect callback.
 *
 * @param[in] pvCallbackContext The MQTT connection.
 * @param[in] pxDisconnect Information about the disconnect.
 */
static void prvDisconnectCallbackWrapper( void * pvParameter,
                                          IotMqttCallbackParam_t * pxDisconnect );

#if ( mqttconfigENABLE_SUBSCRIPTION_MANAGEMENT == 1 )

/**
 * @brief Store an MQTT v1 callback in the conversion table.
 *
 * @param[in] pxConnection Where to store the callback.
 * @param[in] pcTopicFilter Topic filter to store.
 * @param[in] usTopicFilterLength Length of pcTopicFilter.
 * @param[in] xCallback MQTT v1 callback to store.
 * @param[in] pvParameter Parameter to xCallback.
 *
 * @return pdPASS if the callback was successfully stored; pdFAIL otherwise.
 */
    static BaseType_t prvStoreCallback( MQTTConnection_t * const pxConnection,
                                        const char * const pcTopicFilter,
                                        uint16_t usTopicFilterLength,
                                        MQTTPublishCallback_t xCallback,
                                        void * pvParameter );

/**
 * @brief Search the callback conversion table for the given topic filter.
 *
 * @param[in] pxConnection The connection containing the conversion table.
 * @param[in] pcTopicFilter The topic filter to search for.
 * @param[in] usTopicFilterLength The length of pcTopicFilter.
 *
 * @return A pointer to the callback entry if found; NULL otherwise.
 * @note This function should be called with pxConnection->xConnectionMutex
 * locked.
 */
    static MQTTCallback_t * prvFindCallback( MQTTConnection_t * const pxConnection,
                                             const char * const pcTopicFilter,
                                             uint16_t usTopicFilterLength );

/**
 * @brief Remove a topic filter from the callback conversion table.
 *
 * @param[in] pxConnection The connection containing the conversion table.
 * @param[in] pcTopicFilter The topic filter to remove.
 * @param[in] usTopicFilterLength The length of pcTopic.
 */
    static void prvRemoveCallback( MQTTConnection_t * const pxConnection,
                                   const char * const pcTopicFilter,
                                   uint16_t usTopicFilterLength );
#endif /* if ( mqttconfigENABLE_SUBSCRIPTION_MANAGEMENT == 1 ) */

/*-----------------------------------------------------------*/

/**
 * @brief The number of available MQTT brokers, controlled by the constant
 * mqttconfigMAX_BROKERS;
 */
static UBaseType_t uxAvailableBrokers = mqttconfigMAX_BROKERS;

/*-----------------------------------------------------------*/

static inline MQTTAgentReturnCode_t prvConvertReturnCode( IotMqttError_t xMqttStatus )
{
    MQTTAgentReturnCode_t xStatus = eMQTTAgentSuccess;

    switch( xMqttStatus )
    {
        case IOT_MQTT_SUCCESS:
        case IOT_MQTT_STATUS_PENDING:
            xStatus = eMQTTAgentSuccess;
            break;

        case IOT_MQTT_TIMEOUT:
            xStatus = eMQTTAgentTimeout;
            break;

        default:
            xStatus = eMQTTAgentFailure;
            break;
    }

    return xStatus;
}

/*-----------------------------------------------------------*/

static void prvPublishCallbackWrapper( void * pvParameter,
                                       IotMqttCallbackParam_t * const pxPublish )
{
    BaseType_t xStatus = pdPASS;
    size_t xBufferSize = 0;
    uint8_t * pucMqttBuffer = NULL;
    MQTTBool_t xCallbackReturn = eMQTTFalse;
    MQTTConnection_t * pxConnection = ( MQTTConnection_t * ) pvParameter;
    MQTTAgentCallbackParams_t xPublishData = { .xMQTTEvent = eMQTTAgentPublish };

    /* Calculate the size of the MQTT buffer that must be allocated. */
    if( xStatus == pdPASS )
    {
        xBufferSize = pxPublish->u.message.info.topicNameLength +
                      pxPublish->u.message.info.payloadLength;

        /* Check for overflow. */
        if( ( xBufferSize < pxPublish->u.message.info.topicNameLength ) ||
            ( xBufferSize < pxPublish->u.message.info.payloadLength ) )
        {
            mqttconfigDEBUG_LOG( ( "Incoming PUBLISH message and topic name length too large.\r\n" ) );
            xStatus = pdFAIL;
        }
    }

    /* Allocate an MQTT buffer for the callback. */
    if( xStatus == pdPASS )
    {
        pucMqttBuffer = pvPortMalloc( xBufferSize );

        if( pucMqttBuffer == NULL )
        {
            mqttconfigDEBUG_LOG( ( "Failed to allocate memory for MQTT buffer.\r\n" ) );
            xStatus = pdFAIL;
        }
        else
        {
            /* Copy the topic name and payload. The topic name and payload must be
             * copied in case the user decides to take ownership of the MQTT buffer.
             * The original buffer containing the MQTT topic name and payload may
             * contain further unprocessed packets and must remain property of the
             * MQTT library. Therefore, the topic name and payload are copied into
             * another buffer for the user. */
            ( void ) memcpy( pucMqttBuffer,
                             pxPublish->u.message.info.pTopicName,
                             pxPublish->u.message.info.topicNameLength );
            ( void ) memcpy( pucMqttBuffer + pxPublish->u.message.info.topicNameLength,
                             pxPublish->u.message.info.pPayload,
                             pxPublish->u.message.info.payloadLength );

            /* Set the members of the callback parameter. */
            xPublishData.xMQTTEvent = eMQTTAgentPublish;
            xPublishData.u.xPublishData.pucTopic = pucMqttBuffer;
            xPublishData.u.xPublishData.usTopicLength = pxPublish->u.message.info.topicNameLength;
            xPublishData.u.xPublishData.pvData = pucMqttBuffer + pxPublish->u.message.info.topicNameLength;
            xPublishData.u.xPublishData.ulDataLength = ( uint32_t ) pxPublish->u.message.info.payloadLength;
            xPublishData.u.xPublishData.xQos = ( MQTTQoS_t ) pxPublish->u.message.info.qos;
            xPublishData.u.xPublishData.xBuffer = pucMqttBuffer;
        }
    }

    if( xStatus == pdPASS )
    {
        #if ( mqttconfigENABLE_SUBSCRIPTION_MANAGEMENT == 1 )
            /* When subscription management is enabled, search for a matching subscription. */
            MQTTCallback_t * pxCallbackEntry = prvFindCallback( pxConnection,
                                                                pxPublish->u.message.pTopicFilter,
                                                                pxPublish->u.message.topicFilterLength );

            /* Check if a matching MQTT v1 subscription was found. */
            if( pxCallbackEntry != NULL )
            {
                /* Invoke the topic-specific callback if it exists. */
                if( pxCallbackEntry->xFunction != NULL )
                {
                    xCallbackReturn = pxCallbackEntry->xFunction( pxCallbackEntry->pvParameter,
                                                                  &( xPublishData.u.xPublishData ) );
                }
                else
                {
                    /* Otherwise, invoke the global callback. */
                    if( pxConnection->pxCallback != NULL )
                    {
                        xCallbackReturn = ( MQTTBool_t ) pxConnection->pxCallback( pxConnection->pvUserData,
                                                                                   &xPublishData );
                    }
                }
            }
        #else /* if ( mqttconfigENABLE_SUBSCRIPTION_MANAGEMENT == 1 ) */

            /* When subscription management is disabled, invoke the global callback
             * if one exists. */

            /* When subscription management is disabled, the topic filter must be "#". */
            mqttconfigASSERT( *( xPublish.message.pTopicFilter ) == '#' );
            mqttconfigASSERT( xPublish.message.topicFilterLength == 1 );

            if( pxConnection->pxCallback != NULL )
            {
                xCallbackReturn = ( MQTTBool_t ) pxConnection->pxCallback( pxConnection->pvUserData,
                                                                           &xPublishData );
            }
        #endif /* if ( mqttconfigENABLE_SUBSCRIPTION_MANAGEMENT == 1 ) */
    }

    /* Free the MQTT buffer if the user did not take ownership of it. */
    if( ( xCallbackReturn == eMQTTFalse ) && ( pucMqttBuffer != NULL ) )
    {
        vPortFree( pucMqttBuffer );
    }
}

/*-----------------------------------------------------------*/

static void prvDisconnectCallbackWrapper( void * pvParameter,
                                          IotMqttCallbackParam_t * pxDisconnect )
{
    MQTTConnection_t * pxConnection = ( MQTTConnection_t * ) pvParameter;
    MQTTAgentCallbackParams_t xCallbackParams = { .xMQTTEvent = eMQTTAgentDisconnect };

    ( void ) pxDisconnect;

    /* This function should only be called if a callback was set. */
    mqttconfigASSERT( pxConnection->pxCallback != NULL );

    /* Invoke the MQTT v1 callback. Ignore the return value. */
    pxConnection->pxCallback( pxConnection->pvUserData,
                              &xCallbackParams );
}

/*-----------------------------------------------------------*/

#if ( mqttconfigENABLE_SUBSCRIPTION_MANAGEMENT == 1 )
    static BaseType_t prvStoreCallback( MQTTConnection_t * const pxConnection,
                                        const char * const pcTopicFilter,
                                        uint16_t usTopicFilterLength,
                                        MQTTPublishCallback_t xCallback,
                                        void * pvParameter )
    {
        MQTTCallback_t * pxCallback = NULL;
        BaseType_t xStatus = pdFAIL, i = 0;

        /* Prevent other tasks from modifying stored callbacks while this function
         * runs. */
        if( xSemaphoreTake( ( QueueHandle_t ) &( pxConnection->xConnectionMutex ),
                            portMAX_DELAY ) == pdTRUE )
        {
            /* Check if the topic filter already has an entry. */
            pxCallback = prvFindCallback( pxConnection, pcTopicFilter, usTopicFilterLength );

            if( pxCallback == NULL )
            {
                /* If no entry was found, find a free entry. */
                for( i = 0; i < mqttconfigSUBSCRIPTION_MANAGER_MAX_SUBSCRIPTIONS; i++ )
                {
                    if( pxConnection->xCallbacks[ i ].xInUse == pdFALSE )
                    {
                        pxConnection->xCallbacks[ i ].xInUse = pdTRUE;
                        pxCallback = &( pxConnection->xCallbacks[ i ] );
                        break;
                    }
                }
            }

            /* Set the members of the callback entry. */
            if( i < mqttconfigSUBSCRIPTION_MANAGER_MAX_SUBSCRIPTIONS )
            {
                pxCallback->pvParameter = pvParameter;
                pxCallback->usTopicFilterLength = usTopicFilterLength;
                pxCallback->xFunction = xCallback;
                ( void ) strncpy( pxCallback->pcTopicFilter, pcTopicFilter, usTopicFilterLength );
                xStatus = pdPASS;
            }

            ( void ) xSemaphoreGive( ( QueueHandle_t ) &( pxConnection->xConnectionMutex ) );
        }

        return xStatus;
    }

/*-----------------------------------------------------------*/

    static MQTTCallback_t * prvFindCallback( MQTTConnection_t * const pxConnection,
                                             const char * const pcTopicFilter,
                                             uint16_t usTopicFilterLength )
    {
        BaseType_t i = 0;
        MQTTCallback_t * pxResult = NULL;

        /* Search the callback conversion table for the topic filter. */
        for( i = 0; i < mqttconfigSUBSCRIPTION_MANAGER_MAX_SUBSCRIPTIONS; i++ )
        {
            if( ( pxConnection->xCallbacks[ i ].usTopicFilterLength == usTopicFilterLength ) &&
                ( strncmp( pxConnection->xCallbacks[ i ].pcTopicFilter,
                           pcTopicFilter,
                           usTopicFilterLength ) == 0 ) )
            {
                pxResult = &( pxConnection->xCallbacks[ i ] );
                break;
            }
        }

        return pxResult;
    }

/*-----------------------------------------------------------*/

    static void prvRemoveCallback( MQTTConnection_t * const pxConnection,
                                   const char * const pcTopicFilter,
                                   uint16_t usTopicFilterLength )
    {
        MQTTCallback_t * pxCallback = NULL;

        /* Prevent other tasks from modifying stored callbacks while this function
         * runs. */
        if( xSemaphoreTake( ( QueueHandle_t ) &( pxConnection->xConnectionMutex ),
                            portMAX_DELAY ) == pdTRUE )
        {
            /* Find the given topic filter. */
            pxCallback = prvFindCallback( pxConnection, pcTopicFilter, usTopicFilterLength );

            if( pxCallback != NULL )
            {
                /* Clear the callback entry. */
                mqttconfigASSERT( pxCallback->xInUse == pdTRUE );
                ( void ) memset( pxCallback, 0x00, sizeof( MQTTCallback_t ) );
            }

            ( void ) xSemaphoreGive( ( QueueHandle_t ) &( pxConnection->xConnectionMutex ) );
        }
    }
#endif /* if ( mqttconfigENABLE_SUBSCRIPTION_MANAGEMENT == 1 ) */

/*-----------------------------------------------------------*/

IotMqttConnection_t MQTT_AGENT_Getv2Connection( MQTTAgentHandle_t xMQTTHandle )
{
    MQTTConnection_t * pxConnection = ( MQTTConnection_t * ) xMQTTHandle;

    return pxConnection->xMQTTConnection;
}

/*-----------------------------------------------------------*/

BaseType_t MQTT_AGENT_Init( void )
{
    BaseType_t xStatus = pdFALSE;

    /* Call the initialization function of MQTT v2. */
    if( IotMqtt_Init() == IOT_MQTT_SUCCESS )
    {
        xStatus = pdTRUE;
    }

    return xStatus;
}

/*-----------------------------------------------------------*/

MQTTAgentReturnCode_t MQTT_AGENT_Create( MQTTAgentHandle_t * const pxMQTTHandle )
{
    MQTTConnection_t * pxNewConnection = NULL;
    MQTTAgentReturnCode_t xStatus = eMQTTAgentSuccess;

    /* Check how many brokers are available; fail if all brokers are in use. */
    taskENTER_CRITICAL();
    {
        if( uxAvailableBrokers == 0 )
        {
            xStatus = eMQTTAgentFailure;
        }
        else
        {
            uxAvailableBrokers--;
            mqttconfigASSERT( uxAvailableBrokers <= mqttconfigMAX_BROKERS );
        }
    }
    taskEXIT_CRITICAL();

    /* Allocate memory for an MQTT connection. */
    if( xStatus == eMQTTAgentSuccess )
    {
        pxNewConnection = pvPortMalloc( sizeof( MQTTConnection_t ) );

        if( pxNewConnection == NULL )
        {
            xStatus = eMQTTAgentFailure;

            taskENTER_CRITICAL();
            {
                uxAvailableBrokers++;
                mqttconfigASSERT( uxAvailableBrokers <= mqttconfigMAX_BROKERS );
            }
            taskEXIT_CRITICAL();
        }
        else
        {
            ( void ) memset( pxNewConnection, 0x00, sizeof( MQTTConnection_t ) );
            pxNewConnection->xMQTTConnection = IOT_MQTT_CONNECTION_INITIALIZER;
        }
    }

    /* Create the connection mutex and set the output parameter. */
    if( xStatus == eMQTTAgentSuccess )
    {
        ( void ) xSemaphoreCreateMutexStatic( &( pxNewConnection->xConnectionMutex ) );
        *pxMQTTHandle = ( MQTTAgentHandle_t ) pxNewConnection;
    }

    return xStatus;
}

/*-----------------------------------------------------------*/

MQTTAgentReturnCode_t MQTT_AGENT_Delete( MQTTAgentHandle_t xMQTTHandle )
{
    MQTTConnection_t * pxConnection = ( MQTTConnection_t * ) xMQTTHandle;

    /* Clean up any allocated MQTT or network resources. */
    if( pxConnection->xMQTTConnection != IOT_MQTT_CONNECTION_INITIALIZER )
    {
        IotMqtt_Disconnect( pxConnection->xMQTTConnection, IOT_MQTT_FLAG_CLEANUP_ONLY );
        pxConnection->xMQTTConnection = IOT_MQTT_CONNECTION_INITIALIZER;
    }

    /* Free memory used by the MQTT connection. */
    vPortFree( pxConnection );

    /* Increment the number of available brokers. */
    taskENTER_CRITICAL();
    {
        uxAvailableBrokers++;
        mqttconfigASSERT( uxAvailableBrokers <= mqttconfigMAX_BROKERS );
    }
    taskEXIT_CRITICAL();

    return eMQTTAgentSuccess;
}

/*-----------------------------------------------------------*/

MQTTAgentReturnCode_t MQTT_AGENT_Connect( MQTTAgentHandle_t xMQTTHandle,
                                          const MQTTAgentConnectParams_t * const pxConnectParams,
                                          TickType_t xTimeoutTicks )
{
    MQTTAgentReturnCode_t xStatus = eMQTTAgentSuccess;
    IotMqttError_t xMqttStatus = IOT_MQTT_STATUS_PENDING;
    MQTTConnection_t * pxConnection = ( MQTTConnection_t * ) xMQTTHandle;
    IotNetworkServerInfo_t xServerInfo = { 0 };
    IotNetworkCredentials_t xCredentials = AWS_IOT_NETWORK_CREDENTIALS_AFR_INITIALIZER, * pxCredentials = NULL;
    IotMqttNetworkInfo_t xNetworkInfo = IOT_MQTT_NETWORK_INFO_INITIALIZER;
    IotMqttConnectInfo_t xMqttConnectInfo = IOT_MQTT_CONNECT_INFO_INITIALIZER;

    /* Copy the global callback and parameter. */
    pxConnection->pxCallback = pxConnectParams->pxCallback;
    pxConnection->pvUserData = pxConnectParams->pvUserData;

    /* Set the TLS info for a secured connection. */
    if( ( pxConnectParams->xSecuredConnection == pdTRUE ) ||
        ( ( pxConnectParams->xFlags & mqttagentREQUIRE_TLS ) == mqttagentREQUIRE_TLS ) )
    {
        pxCredentials = &xCredentials;

        /* Set the server certificate. Other credentials are set by the initializer. */
        xCredentials.pRootCa = pxConnectParams->pcCertificate;
        xCredentials.rootCaSize = ( size_t ) pxConnectParams->ulCertificateSize;

        /* Disable ALPN if requested. */
        if( ( pxConnectParams->xFlags & mqttagentUSE_AWS_IOT_ALPN_443 ) == 0 )
        {
            xCredentials.pAlpnProtos = NULL;
        }

        /* Disable SNI if requested. */
        if( ( pxConnectParams->xURLIsIPAddress == pdTRUE ) ||
            ( ( pxConnectParams->xFlags & mqttagentURL_IS_IP_ADDRESS ) == mqttagentURL_IS_IP_ADDRESS ) )
        {
            xCredentials.disableSni = true;
        }
    }

    /* Set the server info. */
    xServerInfo.pHostName = pxConnectParams->pcURL;
    xServerInfo.port = pxConnectParams->usPort;

    /* Set the members of the network info. */
    xNetworkInfo.createNetworkConnection = true;
    xNetworkInfo.u.setup.pNetworkServerInfo = &xServerInfo;
    xNetworkInfo.u.setup.pNetworkCredentialInfo = pxCredentials;
    xNetworkInfo.pNetworkInterface = IOT_NETWORK_INTERFACE_AFR;

    if( pxConnectParams->pxCallback != NULL )
    {
        xNetworkInfo.disconnectCallback.function = prvDisconnectCallbackWrapper;
        xNetworkInfo.disconnectCallback.pCallbackContext = pxConnection;
    }

    /* Set the members of the MQTT connect info. */
    xMqttConnectInfo.awsIotMqttMode = true;
    xMqttConnectInfo.cleanSession = true;
    xMqttConnectInfo.pClientIdentifier = ( const char * ) ( pxConnectParams->pucClientId );
    xMqttConnectInfo.clientIdentifierLength = pxConnectParams->usClientIdLength;
    xMqttConnectInfo.keepAliveSeconds = mqttconfigKEEP_ALIVE_INTERVAL_SECONDS;

    /* Call MQTT v2's CONNECT function. */
    xMqttStatus = IotMqtt_Connect( &xNetworkInfo,
                                   &xMqttConnectInfo,
                                   mqttTICKS_TO_MS( xTimeoutTicks ),
                                   &( pxConnection->xMQTTConnection ) );
    xStatus = prvConvertReturnCode( xMqttStatus );

    /* Add a subscription to "#" to support the global callback when subscription
     * manager is disabled. */
    #if ( mqttconfigENABLE_SUBSCRIPTION_MANAGEMENT == 0 )
        IotMqttSubscription_t xGlobalSubscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;
        IotMqttReference_t xGlobalSubscriptionRef = IOT_MQTT_REFERENCE_INITIALIZER;

        if( xStatus == eMQTTAgentSuccess )
        {
            xGlobalSubscription.pTopicFilter = "#";
            xGlobalSubscription.topicFilterLength = 1;
            xGlobalSubscription.qos = 0;
            xGlobalSubscription.callback.param1 = pxConnection;
            xGlobalSubscription.callback.function = prvPublishCallbackWrapper;

            xMqttStatus = IotMqtt_Subscribe( pxConnection->xMQTTConnection,
                                             &xGlobalSubscription,
                                             1,
                                             IOT_MQTT_FLAG_WAITABLE,
                                             NULL,
                                             &xGlobalSubscriptionRef );
            xStatus = prvConvertReturnCode( xMqttStatus );
        }

        /* Wait for the subscription to "#" to complete. */
        if( xStatus == eMQTTAgentSuccess )
        {
            xMqttStatus = IotMqtt_Wait( xGlobalSubscriptionRef,
                                        mqttTICKS_TO_MS( xTimeoutTicks ) );
            xStatus = prvConvertReturnCode( xMqttStatus );
        }
    #endif /* if ( mqttconfigENABLE_SUBSCRIPTION_MANAGEMENT == 1 ) */

    return xStatus;
}

/*-----------------------------------------------------------*/

MQTTAgentReturnCode_t MQTT_AGENT_Disconnect( MQTTAgentHandle_t xMQTTHandle,
                                             TickType_t xTimeoutTicks )
{
    MQTTConnection_t * pxConnection = ( MQTTConnection_t * ) xMQTTHandle;

    /* MQTT v2's DISCONNECT function does not have a timeout argument. */
    ( void ) xTimeoutTicks;

    /* Check that the connection is established. */
    if( pxConnection->xMQTTConnection != IOT_MQTT_CONNECTION_INITIALIZER )
    {
        /* Call MQTT v2's DISCONNECT function. */
        IotMqtt_Disconnect( pxConnection->xMQTTConnection,
                            0 );
        pxConnection->xMQTTConnection = IOT_MQTT_CONNECTION_INITIALIZER;
    }

    return eMQTTAgentSuccess;
}

/*-----------------------------------------------------------*/

MQTTAgentReturnCode_t MQTT_AGENT_Subscribe( MQTTAgentHandle_t xMQTTHandle,
                                            const MQTTAgentSubscribeParams_t * const pxSubscribeParams,
                                            TickType_t xTimeoutTicks )
{
    MQTTAgentReturnCode_t xStatus = eMQTTAgentSuccess;
    IotMqttError_t xMqttStatus = IOT_MQTT_STATUS_PENDING;
    MQTTConnection_t * pxConnection = ( MQTTConnection_t * ) xMQTTHandle;
    IotMqttSubscription_t xSubscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;

    /* Store the topic filter if subscription management is enabled. */
    #if ( mqttconfigENABLE_SUBSCRIPTION_MANAGEMENT == 1 )
        /* Check topic filter length. */
        if( pxSubscribeParams->usTopicLength > mqttconfigSUBSCRIPTION_MANAGER_MAX_TOPIC_LENGTH )
        {
            xStatus = eMQTTAgentFailure;
        }

        /* Store the subscription. */
        if( prvStoreCallback( pxConnection,
                              ( const char * ) pxSubscribeParams->pucTopic,
                              pxSubscribeParams->usTopicLength,
                              pxSubscribeParams->pxPublishCallback,
                              pxSubscribeParams->pvPublishCallbackContext ) == pdFAIL )
        {
            xStatus = eMQTTAgentFailure;
        }
    #endif /* if ( mqttconfigENABLE_SUBSCRIPTION_MANAGEMENT == 1 ) */

    /* Call MQTT v2 blocking SUBSCRIBE function. */
    if( xStatus == eMQTTAgentSuccess )
    {
        /* Set the members of the MQTT subscription. */
        xSubscription.pTopicFilter = ( const char * ) ( pxSubscribeParams->pucTopic );
        xSubscription.topicFilterLength = pxSubscribeParams->usTopicLength;
        xSubscription.qos = ( IotMqttQos_t ) pxSubscribeParams->xQoS;
        xSubscription.callback.pCallbackContext = pxConnection;
        xSubscription.callback.function = prvPublishCallbackWrapper;

        xMqttStatus = IotMqtt_TimedSubscribe( pxConnection->xMQTTConnection,
                                              &xSubscription,
                                              1,
                                              0,
                                              mqttTICKS_TO_MS( xTimeoutTicks ) );
        xStatus = prvConvertReturnCode( xMqttStatus );
    }

    return xStatus;
}

/*-----------------------------------------------------------*/

MQTTAgentReturnCode_t MQTT_AGENT_Unsubscribe( MQTTAgentHandle_t xMQTTHandle,
                                              const MQTTAgentUnsubscribeParams_t * const pxUnsubscribeParams,
                                              TickType_t xTimeoutTicks )
{
    IotMqttError_t xMqttStatus = IOT_MQTT_STATUS_PENDING;
    MQTTConnection_t * pxConnection = ( MQTTConnection_t * ) xMQTTHandle;
    IotMqttSubscription_t xSubscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;

    /* Remove any subscription callback that may be registered. */
    #if ( mqttconfigENABLE_SUBSCRIPTION_MANAGEMENT == 1 )
        prvRemoveCallback( pxConnection,
                           ( const char * ) ( pxUnsubscribeParams->pucTopic ),
                           pxUnsubscribeParams->usTopicLength );
    #endif

    /* Set the members of the subscription to remove. */
    xSubscription.pTopicFilter = ( const char * ) ( pxUnsubscribeParams->pucTopic );
    xSubscription.topicFilterLength = pxUnsubscribeParams->usTopicLength;
    xSubscription.callback.pCallbackContext = pxConnection;
    xSubscription.callback.function = prvPublishCallbackWrapper;

    /* Call MQTT v2 blocking UNSUBSCRIBE function. */
    xMqttStatus = IotMqtt_TimedUnsubscribe( pxConnection->xMQTTConnection,
                                            &xSubscription,
                                            1,
                                            0,
                                            mqttTICKS_TO_MS( xTimeoutTicks ) );

    return prvConvertReturnCode( xMqttStatus );
}

/*-----------------------------------------------------------*/

MQTTAgentReturnCode_t MQTT_AGENT_Publish( MQTTAgentHandle_t xMQTTHandle,
                                          const MQTTAgentPublishParams_t * const pxPublishParams,
                                          TickType_t xTimeoutTicks )
{
    IotMqttError_t xMqttStatus = IOT_MQTT_STATUS_PENDING;
    MQTTConnection_t * pxConnection = ( MQTTConnection_t * ) xMQTTHandle;
    IotMqttPublishInfo_t xPublishInfo = IOT_MQTT_PUBLISH_INFO_INITIALIZER;

    /* Set the members of the publish info. */
    xPublishInfo.pTopicName = ( const char * ) pxPublishParams->pucTopic;
    xPublishInfo.topicNameLength = pxPublishParams->usTopicLength;
    xPublishInfo.qos = ( IotMqttQos_t ) pxPublishParams->xQoS;
    xPublishInfo.pPayload = ( const void * ) pxPublishParams->pvData;
    xPublishInfo.payloadLength = pxPublishParams->ulDataLength;

    /* Call the MQTT v2 blocking PUBLISH function. */
    xMqttStatus = IotMqtt_TimedPublish( pxConnection->xMQTTConnection,
                                        &xPublishInfo,
                                        0,
                                        mqttTICKS_TO_MS( xTimeoutTicks ) );

    return prvConvertReturnCode( xMqttStatus );
}

/*-----------------------------------------------------------*/

MQTTAgentReturnCode_t MQTT_AGENT_ReturnBuffer( MQTTAgentHandle_t xMQTTHandle,
                                               MQTTBufferHandle_t xBufferHandle )
{
    ( void ) xMQTTHandle;

    /* Free the MQTT buffer. */
    vPortFree( xBufferHandle );

    return eMQTTAgentSuccess;
}

/*-----------------------------------------------------------*/
