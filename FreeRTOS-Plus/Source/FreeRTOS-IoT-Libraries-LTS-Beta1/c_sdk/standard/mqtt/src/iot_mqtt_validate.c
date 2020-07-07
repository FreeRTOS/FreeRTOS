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
 * @file iot_mqtt_validate.c
 * @brief Implements functions that validate the structs of the MQTT library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* MQTT internal include. */
#include "private/iot_mqtt_internal.h"

/**
 * @brief Check that an #IotMqttPublishInfo_t is valid.
 *
 * @param[in] awsIotMqttMode Specifies if this PUBLISH packet is being sent to
 * an AWS IoT MQTT server.
 * @param[in] maximumPayloadLength Maximum payload length.
 * @param[in] pPublishTypeDescription String describing the publish type.
 * @param[in] pPublishInfo The #IotMqttPublishInfo_t to validate.
 *
 * @return `true` if `pPublishInfo` is valid; `false` otherwise.
 */
static bool _validatePublish( bool awsIotMqttMode,
                              size_t maximumPayloadLength,
                              const char * pPublishTypeDescription,
                              const IotMqttPublishInfo_t * pPublishInfo );

/**
 * @brief Check that the payload inside #IotMqttPublishInfo_t is valid.
 *
 * @param[in] pPublishInfo The #IotMqttPublishInfo_t to validate.
 * @param[in] maximumPayloadLength Maximum payload length.
 * @param[in] pPublishTypeDescription String describing the publish type.
 *
 * @return `true` if payload is valid; `false` otherwise
 */
static bool _validatePublishPayload( const IotMqttPublishInfo_t * pPublishInfo,
                                     size_t maximumPayloadLength,
                                     const char * pPublishTypeDescription );


/**
 * @brief Check that an #IotMqttQos_t is valid.
 *
 * @param[in] qos The QoS to check.
 *
 * @return `true` if `qos` is valid; `false` otherwise.
 */
static bool _validateQos( IotMqttQos_t qos );

/**
 * @brief Check that a string is valid.
 *
 * @param[in] pString The string to check.
 * @param[in] length Length of string to check.
 *
 * @return `true` if `pString` is valid; `false` otherwise.
 */
static bool _validateString( const char * pString,
                             uint16_t length );

/**
 * @brief Check that a list of subscriptions is valid.
 *
 * @param[in] awsIotMqttMode Whether to enforce list length restrictions from AWS IoT.
 * @param[in] pListStart First element of the list.
 * @param[in] listSize Length of the list.
 *
 * @return `true` if `pListStart` is valid; `false` otherwise.
 */
static bool _validateListSize( bool awsIotMqttMode,
                               const IotMqttSubscription_t * pListStart,
                               size_t listSize );

/**
 * @brief Check that a single subscription is valid.
 *
 * @param[in] awsIotMqttMode Whether to enforce the topic filter restrictions from AWS IoT.
 * @param[in] operation Either #IOT_MQTT_SUBSCRIBE or #IOT_MQTT_UNSUBSCRIBE.
 * @param[in] pSubscription The subscription to check.
 *
 * @return `true` if `pSubscription` is valid; `false` otherwise.
 */
static bool _validateSubscription( bool awsIotMqttMode,
                                   IotMqttOperationType_t operation,
                                   const IotMqttSubscription_t * pSubscription );

/**
 * @brief Check that the MQTT `+` wildcard is being used correctly.
 *
 * @param[in] index Index of `+` in the topic filter.
 * @param[in] pSubscription Subscription with the topic filter to check.
 *
 * @return `true` if the `+` wildcard is valid; `false` otherwise.
 */
static bool _validateWildcardPlus( uint16_t index,
                                   const IotMqttSubscription_t * pSubscription );

/**
 * @brief Check that the MQTT `#` wildcard is being used correctly.
 *
 * @param[in] index Index of `#` in the topic filter.
 * @param[in] pSubscription Subscription with the topic filter to check.
 *
 * @return `true` if the `#` wildcard is valid; `false` otherwise.
 */
static bool _validateWildcardHash( uint16_t index,
                                   const IotMqttSubscription_t * pSubscription );

/**
 * @brief Validate the MQTT client identifier.
 *
 * @param[in] pConnectInfo The #IotMqttConnectInfo_t containing the client identifier
 * to validate.
 *
 * @return `true` if client identifier is valid, `false` otherwise.
 */
static bool _validateClientId( const IotMqttConnectInfo_t * pConnectInfo );

/*-----------------------------------------------------------*/

static bool _validateQos( IotMqttQos_t qos )
{
    bool status = false;

    switch( qos )
    {
        case IOT_MQTT_QOS_0:
        case IOT_MQTT_QOS_1:
            status = true;
            break;

        default:
            IotLogError( "QoS must be either 0 or 1." );

            break;
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool _validateString( const char * pString,
                             uint16_t length )
{
    bool status = true;

    if( pString == NULL )
    {
        status = false;
    }
    else if( length == 0U )
    {
        status = false;
    }
    else
    {
        status = true;
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool _validatePublishPayload( const IotMqttPublishInfo_t * pPublishInfo,
                                     size_t maximumPayloadLength,
                                     const char * pPublishTypeDescription )
{
    bool status = true;

    /* This parameter is not used when logging is disabled. */
    ( void ) pPublishTypeDescription;

    if( pPublishInfo->payloadLength != 0U )
    {
        if( pPublishInfo->payloadLength > maximumPayloadLength )
        {
            IotLogError( "%s payload size of %zu exceeds maximum length of %zu.",
                         pPublishTypeDescription,
                         pPublishInfo->payloadLength,
                         maximumPayloadLength );

            status = false;
        }
        else if( pPublishInfo->pPayload == NULL )
        {
            IotLogError( "Nonzero payload length cannot have a NULL payload." );

            status = false;
        }
        else
        {
            /* Empty else MISRA 15.7 */
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool _validatePublish( bool awsIotMqttMode,
                              size_t maximumPayloadLength,
                              const char * pPublishTypeDescription,
                              const IotMqttPublishInfo_t * pPublishInfo )
{
    bool status = true;

    /* Check for NULL. */
    if( pPublishInfo == NULL )
    {
        IotLogError( "Publish information cannot be NULL." );

        status = false;
    }
    /* Check topic name for NULL or zero-length. */
    else
    {
        status = _validateString( pPublishInfo->pTopicName, pPublishInfo->topicNameLength );

        if( status != true )
        {
            IotLogError( "Publish topic name must be set." );
        }
    }

    if( status == true )
    {
        status = _validatePublishPayload( pPublishInfo,
                                          maximumPayloadLength,
                                          pPublishTypeDescription );
    }

    if( status == true )
    {
        /* Check for a valid QoS. */
        status = _validateQos( pPublishInfo->qos );
    }

    if( status == true )
    {
        /* Check the retry parameters. */
        if( pPublishInfo->retryLimit > 0U )
        {
            if( pPublishInfo->retryMs == 0U )
            {
                IotLogError( "Publish retry time must be positive." );

                status = false;
            }
        }
    }

    if( status == true )
    {
        /* Check for compatibility with AWS IoT MQTT server. */
        if( awsIotMqttMode == true )
        {
            /* Check for retained message. */
            if( pPublishInfo->retain == true )
            {
                IotLogError( "AWS IoT does not support retained publish messages." );

                status = false;
            }

            /* Check topic name length. */
            if( pPublishInfo->topicNameLength > AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH )
            {
                IotLogError( "AWS IoT does not support topic names longer than %d bytes.",
                             AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH );

                status = false;
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool _validateListSize( bool awsIotMqttMode,
                               const IotMqttSubscription_t * pListStart,
                               size_t listSize )
{
    bool status = true;

    /* Check for empty list. */
    if( pListStart == NULL )
    {
        IotLogError( "Subscription list pointer cannot be NULL." );

        status = false;
    }
    else if( listSize == 0U )
    {
        IotLogError( "Empty subscription list." );

        status = false;
    }
    else
    {
        /* AWS IoT supports at most 8 topic filters in a single SUBSCRIBE packet. */
        if( awsIotMqttMode == true )
        {
            if( listSize > AWS_IOT_MQTT_SERVER_MAX_TOPIC_FILTERS_PER_SUBSCRIBE )
            {
                IotLogError( "AWS IoT does not support more than %d topic filters per "
                             "subscription request.",
                             AWS_IOT_MQTT_SERVER_MAX_TOPIC_FILTERS_PER_SUBSCRIBE );

                status = false;
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool _validateSubscription( bool awsIotMqttMode,
                                   IotMqttOperationType_t operation,
                                   const IotMqttSubscription_t * pSubscription )
{
    bool status = true;
    uint16_t i = 0;

    /* Check for a valid QoS and callback function when subscribing. */
    if( operation == IOT_MQTT_SUBSCRIBE )
    {
        if( pSubscription->callback.function == NULL )
        {
            IotLogError( "Callback function must be set." );

            status = false;
        }
        else
        {
            status = _validateQos( pSubscription->qos );
        }
    }

    /* Check subscription topic filter. */
    if( status == true )
    {
        status = _validateString( pSubscription->pTopicFilter, pSubscription->topicFilterLength );

        if( status == false )
        {
            IotLogError( "Subscription topic filter must be set." );
        }
    }

    /* Check topic filter length compatibility with AWS IoT MQTT server. */
    if( status == true )
    {
        if( awsIotMqttMode == true )
        {
            if( pSubscription->topicFilterLength > AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH )
            {
                IotLogError( "AWS IoT does not support topic filters longer than %d bytes.",
                             AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH );

                status = false;
            }
        }
    }

    if( status == true )
    {
        /* Check that the wildcards '+' and '#' are being used correctly. */
        for( i = 0; i < pSubscription->topicFilterLength; i++ )
        {
            if( pSubscription->pTopicFilter[ i ] == '+' )
            {
                status = _validateWildcardPlus( i, pSubscription );
            }
            else if( pSubscription->pTopicFilter[ i ] == '#' )
            {
                status = _validateWildcardHash( i, pSubscription );
            }
            else
            {
                /* Empty else MISRA 15.7 */
            }

            if( status == false )
            {
                break;
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool _validateWildcardPlus( uint16_t index,
                                   const IotMqttSubscription_t * pSubscription )
{
    bool status = true;

    /* Unless '+' is the first character in the filter, it must be preceded by '/'. */
    if( index > 0U )
    {
        if( pSubscription->pTopicFilter[ index - 1U ] != '/' )
        {
            IotLogError( "Invalid topic filter %.*s -- '+' must be preceded by '/'.",
                         pSubscription->topicFilterLength,
                         pSubscription->pTopicFilter );

            status = false;
        }
    }

    if( status == true )
    {
        /* Unless '+' is the last character in the filter, it must be succeeded by '/'. */
        if( index < ( pSubscription->topicFilterLength - 1U ) )
        {
            if( pSubscription->pTopicFilter[ index + 1U ] != '/' )
            {
                IotLogError( "Invalid topic filter %.*s -- '+' must be succeeded by '/'.",
                             pSubscription->topicFilterLength,
                             pSubscription->pTopicFilter );

                status = false;
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool _validateWildcardHash( uint16_t index,
                                   const IotMqttSubscription_t * pSubscription )
{
    bool status = true;

    /* '#' must be the last character in the filter. */
    if( index != ( pSubscription->topicFilterLength - 1U ) )
    {
        IotLogError( "Invalid topic filter %.*s -- '#' must be the last character.",
                     pSubscription->topicFilterLength,
                     pSubscription->pTopicFilter );

        status = false;
    }

    if( status == true )
    {
        /* Unless '#' is standalone, it must be preceded by '/'. */
        if( pSubscription->topicFilterLength > 1U )
        {
            if( pSubscription->pTopicFilter[ index - 1U ] != '/' )
            {
                IotLogError( "Invalid topic filter %.*s -- '#' must be preceded by '/'.",
                             pSubscription->topicFilterLength,
                             pSubscription->pTopicFilter );

                status = false;
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool _validateClientId( const IotMqttConnectInfo_t * pConnectInfo )
{
    bool status = true;
    uint16_t maxClientIdLength = MQTT_SERVER_MAX_CLIENTID_LENGTH;
    bool enforceMaxClientIdLength = false;

    /* Check that a client identifier was set. */
    if( pConnectInfo->pClientIdentifier == NULL )
    {
        IotLogError( "Client identifier must be set." );

        status = false;
    }

    /* Check for a zero-length client identifier. Zero-length client identifiers
     * are not allowed with persistent sessions. */
    if( status == true )
    {
        if( pConnectInfo->clientIdentifierLength == 0U )
        {
            IotLogWarn( "A zero-length client identifier was provided." );

            if( pConnectInfo->cleanSession == false )
            {
                IotLogError( "A zero-length client identifier cannot be used with a persistent session." );

                status = false;
            }
        }
    }

    /* The AWS IoT MQTT service enforces a client ID length limit. */
    if( pConnectInfo->awsIotMqttMode == true )
    {
        maxClientIdLength = AWS_IOT_MQTT_SERVER_MAX_CLIENTID_LENGTH;
        enforceMaxClientIdLength = true;
    }

    if( status == true )
    {
        if( pConnectInfo->clientIdentifierLength > maxClientIdLength )
        {
            if( enforceMaxClientIdLength == false )
            {
                IotLogWarn( "A client identifier length of %hu is longer than %hu, "
                            "which is "
                            "the longest client identifier a server must accept.",
                            pConnectInfo->clientIdentifierLength,
                            maxClientIdLength );
            }
            else
            {
                IotLogError( "A client identifier length of %hu exceeds the "
                             "maximum supported length of %hu.",
                             pConnectInfo->clientIdentifierLength,
                             maxClientIdLength );

                status = false;
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

bool _IotMqtt_ValidateConnect( const IotMqttConnectInfo_t * pConnectInfo )
{
    bool status = true;

    /* Check for NULL. */
    if( pConnectInfo == NULL )
    {
        IotLogError( "MQTT connection information cannot be NULL." );

        status = false;
    }
    else
    {
        /* Check client identifier.*/
        status = _validateClientId( pConnectInfo );
    }

    if( status == true )
    {
        /* Check that the number of persistent session subscriptions is valid. */
        if( pConnectInfo->pPreviousSubscriptions != NULL )
        {
            status = _IotMqtt_ValidateSubscriptionList( IOT_MQTT_SUBSCRIBE,
                                                        pConnectInfo->awsIotMqttMode,
                                                        pConnectInfo->pPreviousSubscriptions,
                                                        pConnectInfo->previousSubscriptionCount );
        }
    }

    if( status == true )
    {
        /* Check that keep alive is not too short. */
        if( pConnectInfo->keepAliveSeconds != 0U )
        {
            /* After sending a PINGREQ, we wait for IOT_MQTT_RESPONSE_WAIT_MS to
             * receive the corresponding PINGRESP. If the PINGRESP is received within
             * IOT_MQTT_RESPONSE_WAIT_MS, we schedule another job to send PINGREQ.
             * If the IOT_MQTT_RESPONSE_WAIT_MS is longer than keep alive interval,
             * we will fail to send PINGRESP on time. */
            if( ( pConnectInfo->keepAliveSeconds * 1000U ) <= IOT_MQTT_RESPONSE_WAIT_MS )
            {
                IotLogError( "Keep alive interval %u ms must be longer than response wait time %u ms.",
                             pConnectInfo->keepAliveSeconds * 1000U,
                             IOT_MQTT_RESPONSE_WAIT_MS );

                status = false;
            }
        }
    }

    if( status == true )
    {
        /* If will info is provided, check that it is valid. */
        if( pConnectInfo->pWillInfo != NULL )
        {
            status = _IotMqtt_ValidateLwtPublish( pConnectInfo->awsIotMqttMode,
                                                  pConnectInfo->pWillInfo );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

bool _IotMqtt_ValidatePublish( bool awsIotMqttMode,
                               const IotMqttPublishInfo_t * pPublishInfo,
                               uint32_t flags,
                               const IotMqttCallbackInfo_t * pCallbackInfo,
                               const IotMqttOperation_t * const pPublishOperation )
{
    bool status = true;
    size_t maximumPayloadLength = MQTT_SERVER_MAX_PUBLISH_PAYLOAD_LENGTH;

    if( awsIotMqttMode == true )
    {
        maximumPayloadLength = AWS_IOT_MQTT_SERVER_MAX_PUBLISH_PAYLOAD_LENGTH;
    }

    status = _validatePublish( awsIotMqttMode,
                               maximumPayloadLength,
                               "Publish",
                               pPublishInfo );

    if( status == true )
    {
        /* Check that no notification is requested for a QoS 0 publish. */
        if( pPublishInfo->qos == IOT_MQTT_QOS_0 )
        {
            if( pCallbackInfo != NULL )
            {
                IotLogError( "QoS 0 PUBLISH should not have notification parameters set." );

                status = false;
            }
            else if( ( flags & IOT_MQTT_FLAG_WAITABLE ) != 0U )
            {
                IotLogError( "QoS 0 PUBLISH should not have notification parameters set." );

                status = false;
            }
            else
            {
                /* Empty else MISRA 15.7 */
            }

            if( pPublishOperation != NULL )
            {
                IotLogWarn( "Ignoring reference parameter for QoS 0 publish." );
            }
        }

        /* Check that a reference pointer is provided for a waitable operation. */
        if( ( flags & IOT_MQTT_FLAG_WAITABLE ) == IOT_MQTT_FLAG_WAITABLE )
        {
            if( pPublishOperation == NULL )
            {
                IotLogError( "Reference must be provided for a waitable PUBLISH." );

                status = false;
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

bool _IotMqtt_ValidateLwtPublish( bool awsIotMqttMode,
                                  const IotMqttPublishInfo_t * pLwtPublishInfo )
{
    return _validatePublish( awsIotMqttMode,
                             MQTT_SERVER_MAX_LWT_PAYLOAD_LENGTH,
                             "LWT",
                             pLwtPublishInfo );
}

/*-----------------------------------------------------------*/

bool _IotMqtt_ValidateOperation( IotMqttOperation_t operation )
{
    bool status = true;

    /* Check for NULL. */
    if( operation == NULL )
    {
        IotLogError( "Operation reference cannot be NULL." );

        status = false;
    }
    else
    {
        /* Check that reference is waitable. */
        if( ( operation->u.operation.flags & IOT_MQTT_FLAG_WAITABLE ) != IOT_MQTT_FLAG_WAITABLE )
        {
            IotLogError( "Operation is not waitable." );

            status = false;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

bool _IotMqtt_ValidateSubscriptionList( IotMqttOperationType_t operation,
                                        bool awsIotMqttMode,
                                        const IotMqttSubscription_t * pListStart,
                                        size_t listSize )
{
    bool status = true;
    size_t i = 0;

    /* Operation must be either subscribe or unsubscribe. */
    IotMqtt_Assert( ( operation == IOT_MQTT_SUBSCRIBE ) ||
                    ( operation == IOT_MQTT_UNSUBSCRIBE ) );

    /* Check that subscription list is valid. */
    status = _validateListSize( awsIotMqttMode,
                                pListStart,
                                listSize );

    if( status == true )
    {
        /* Check each member of the subscription list. */
        for( i = 0; i < listSize; i++ )
        {
            status = _validateSubscription( awsIotMqttMode,
                                            operation,
                                            &( pListStart[ i ] ) );

            if( status == false )
            {
                break;
            }
        }
    }

    return status;
}

/*-----------------------------------------------------------*/
