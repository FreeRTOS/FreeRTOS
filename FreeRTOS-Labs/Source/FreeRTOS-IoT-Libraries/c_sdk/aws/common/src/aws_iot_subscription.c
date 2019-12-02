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
 * @file aws_iot_subscription.c
 * @brief Functions for common AWS IoT subscriptions.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* AWS IoT include. */
#include "aws_iot.h"

/* Error handling include. */
#include "iot_error.h"

/* MQTT include. */
#include "iot_mqtt.h"

/**
 * @brief Modify subscriptions, either by unsubscribing or subscribing.
 *
 * @param[in] mqttOperation Either @ref mqtt_function_subscribesync or @ref
 * mqtt_function_unsubscribesync.
 * @param[in] pSubscriptionInfo Information needed to process an MQTT
 * operation.
 * @param[in] pTopicFilter The topic filter to modify.
 * @param[in] topicFilterLength The length of `pTopicFilter`.
 *
 * @return See the return values of @ref mqtt_function_subscribesync or
 * @ref mqtt_function_unsubscribesync.
 */
static IotMqttError_t _modifySubscriptions( AwsIotMqttFunction_t mqttOperation,
                                            const AwsIotSubscriptionInfo_t * pSubscriptionInfo,
                                            const char * pTopicFilter,
                                            uint16_t topicFilterLength );

/*-----------------------------------------------------------*/

static IotMqttError_t _modifySubscriptions( AwsIotMqttFunction_t mqttOperation,
                                            const AwsIotSubscriptionInfo_t * pSubscriptionInfo,
                                            const char * pTopicFilter,
                                            uint16_t topicFilterLength )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    IotMqttSubscription_t subscription = IOT_MQTT_SUBSCRIPTION_INITIALIZER;

    /* Per the AWS IoT documentation, topic subscriptions are QoS 1. */
    subscription.qos = IOT_MQTT_QOS_1;

    /* Set the members of the subscription parameter. */
    subscription.pTopicFilter = pTopicFilter;
    subscription.topicFilterLength = topicFilterLength;
    subscription.callback.pCallbackContext = NULL;
    subscription.callback.function = pSubscriptionInfo->callbackFunction;

    /* Call the MQTT operation function.
     * Subscription count is 1 in this case.
     * None of the flags are set in this call. Hence 0 is passed for flags.
     * Please refer to documentation for AwsIotMqttFunction_t for more details.
     */
    status = mqttOperation( pSubscriptionInfo->mqttConnection,
                            &subscription,
                            1,
                            0,
                            pSubscriptionInfo->timeout );

    return status;
}

/*-----------------------------------------------------------*/

IotMqttError_t AwsIot_ModifySubscriptions( AwsIotMqttFunction_t mqttOperation,
                                           const AwsIotSubscriptionInfo_t * pSubscriptionInfo )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_STATUS_PENDING );
    IotMqttError_t acceptedStatus = IOT_MQTT_STATUS_PENDING;
    uint16_t topicFilterLength = 0;

    /* Place the topic "accepted" suffix at the end of the topic buffer. */
    ( void ) memcpy( pSubscriptionInfo->pTopicFilterBase
                     + pSubscriptionInfo->topicFilterBaseLength,
                     AWS_IOT_ACCEPTED_SUFFIX,
                     AWS_IOT_ACCEPTED_SUFFIX_LENGTH );
    topicFilterLength = ( uint16_t ) ( pSubscriptionInfo->topicFilterBaseLength
                                       + AWS_IOT_ACCEPTED_SUFFIX_LENGTH );

    /* Modify the subscription to the "accepted" topic. */
    acceptedStatus = _modifySubscriptions( mqttOperation,
                                           pSubscriptionInfo,
                                           pSubscriptionInfo->pTopicFilterBase,
                                           topicFilterLength );

    if( acceptedStatus != IOT_MQTT_SUCCESS )
    {
        IOT_SET_AND_GOTO_CLEANUP( acceptedStatus );
    }

    /* Place the topic "rejected" suffix at the end of the topic buffer. */
    ( void ) memcpy( pSubscriptionInfo->pTopicFilterBase
                     + pSubscriptionInfo->topicFilterBaseLength,
                     AWS_IOT_REJECTED_SUFFIX,
                     AWS_IOT_REJECTED_SUFFIX_LENGTH );
    topicFilterLength = ( uint16_t ) ( pSubscriptionInfo->topicFilterBaseLength
                                       + AWS_IOT_REJECTED_SUFFIX_LENGTH );

    /* Modify the subscription to the "rejected" topic. */
    status = _modifySubscriptions( mqttOperation,
                                   pSubscriptionInfo,
                                   pSubscriptionInfo->pTopicFilterBase,
                                   topicFilterLength );

    IOT_FUNCTION_CLEANUP_BEGIN();

    /* Clean up on error. */
    if( status != IOT_MQTT_SUCCESS )
    {
        /* Remove the subscription to the "accepted" topic if the subscription
         * to the "rejected" topic failed. */
        if( ( mqttOperation == IotMqtt_SubscribeSync ) &&
            ( acceptedStatus == IOT_MQTT_SUCCESS ) )
        {
            /* Place the topic "accepted" suffix at the end of the topic buffer. */
            ( void ) memcpy( pSubscriptionInfo->pTopicFilterBase
                             + pSubscriptionInfo->topicFilterBaseLength,
                             AWS_IOT_ACCEPTED_SUFFIX,
                             AWS_IOT_ACCEPTED_SUFFIX_LENGTH );
            topicFilterLength = ( uint16_t ) ( pSubscriptionInfo->topicFilterBaseLength
                                               + AWS_IOT_ACCEPTED_SUFFIX_LENGTH );

            ( void ) _modifySubscriptions( IotMqtt_UnsubscribeSync,
                                           pSubscriptionInfo,
                                           pSubscriptionInfo->pTopicFilterBase,
                                           topicFilterLength );
        }
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/
