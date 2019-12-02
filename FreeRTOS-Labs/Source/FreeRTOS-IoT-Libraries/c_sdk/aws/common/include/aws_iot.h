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
 * @file aws_iot.h
 * @brief Provides routines and constants that are common to AWS IoT libraries.
 * This header should not be included in typical application code.
 */

#ifndef AWS_IOT_H_
#define AWS_IOT_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdbool.h>
#include <stdint.h>

/* Platform types include. */
#include "types/iot_platform_types.h"

/* MQTT types include. */
#include "types/iot_mqtt_types.h"

/**
 * @brief The longest Thing Name accepted by AWS IoT, per the [AWS IoT
 * Service Limits](https://docs.aws.amazon.com/general/latest/gr/aws_service_limits.html#limits_iot).
 */
#define AWS_IOT_MAX_THING_NAME_LENGTH      ( 128 )

/**
 * @brief The common prefix of all AWS IoT MQTT topics.
 */
#define AWS_IOT_TOPIC_PREFIX               "$aws/things/"

/**
 * @brief The length of #AWS_IOT_TOPIC_PREFIX.
 */
#define AWS_IOT_TOPIC_PREFIX_LENGTH        ( ( uint16_t ) ( sizeof( AWS_IOT_TOPIC_PREFIX ) - 1 ) )

/**
 * @brief The suffix for an AWS IoT operation "accepted" topic.
 */
#define AWS_IOT_ACCEPTED_SUFFIX            "/accepted"

/**
 * @brief The length of #AWS_IOT_ACCEPTED_SUFFIX.
 */
#define AWS_IOT_ACCEPTED_SUFFIX_LENGTH     ( ( uint16_t ) ( sizeof( AWS_IOT_ACCEPTED_SUFFIX ) - 1 ) )

/**
 * @brief The suffix for an AWS IoT operation "rejected" topic.
 */
#define AWS_IOT_REJECTED_SUFFIX            "/rejected"

/**
 * @brief The length of #AWS_IOT_REJECTED_SUFFIX.
 */
#define AWS_IOT_REJECTED_SUFFIX_LENGTH     ( ( uint16_t ) ( sizeof( AWS_IOT_REJECTED_SUFFIX ) - 1 ) )

/**
 * @brief The JSON key used to represent client tokens for AWS IoT.
 */
#define AWS_IOT_CLIENT_TOKEN_KEY           "clientToken"

/**
 * @brief The length of #AWS_IOT_CLIENT_TOKEN_KEY.
 */
#define AWS_IOT_CLIENT_TOKEN_KEY_LENGTH    ( sizeof( AWS_IOT_CLIENT_TOKEN_KEY ) - 1 )

/**
 * @brief The length of the longest client token allowed by AWS IoT.
 */
#define AWS_IOT_CLIENT_TOKEN_MAX_LENGTH    ( 64 )

/**
 * @brief A flag to represent persistent subscriptions in a subscriptions
 * object.
 *
 * Its value is negative to distinguish it from valid subscription counts, which
 * are 0 or positive.
 */
#define AWS_IOT_PERSISTENT_SUBSCRIPTION    ( -1 )

/**
 * @brief Function pointer representing an MQTT blocking operation.
 *
 * Currently, this is used to represent @ref mqtt_function_subscribesync or
 * @ref mqtt_function_unsubscribesync.
 *
 * @param[in] mqttConnection The MQTT connection to use for the subscription.
 * @param[in] pSubscriptionList Pointer to the first element in the array of
 * subscriptions.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] flags Flags which modify the behavior of this function. See @ref mqtt_constants_flags.
 * Currently, flags are ignored by this function; this parameter is for
 * future-compatibility.
 * @param[in] timeoutMs If the MQTT server does not acknowledge the subscriptions within
 * this timeout in milliseconds, this function returns #IOT_MQTT_TIMEOUT.
 *
 * @return One of the following:
 * - #IOT_MQTT_SUCCESS
 * - #IOT_MQTT_NOT_INITIALIZED
 * - #IOT_MQTT_BAD_PARAMETER
 * - #IOT_MQTT_NO_MEMORY
 * - #IOT_MQTT_NETWORK_ERROR
 * - #IOT_MQTT_SCHEDULING_ERROR
 * - #IOT_MQTT_BAD_RESPONSE
 * - #IOT_MQTT_TIMEOUT
 * - #IOT_MQTT_SERVER_REFUSED
 */
typedef IotMqttError_t ( * AwsIotMqttFunction_t )( IotMqttConnection_t mqttConnection,
                                                   const IotMqttSubscription_t * pSubscriptionList,
                                                   size_t subscriptionCount,
                                                   uint32_t flags,
                                                   uint32_t timeoutMs );

/**
 * @brief Function pointer representing an MQTT library callback function.
 *
 * @param[in] pArgument Ignored.
 * @param[in] pMessage The received DELTA document (as an MQTT PUBLISH message).
 */
typedef void ( * AwsIotMqttCallbackFunction_t )( void * pArgument,
                                                 IotMqttCallbackParam_t * pMessage );

/**
 * @brief Enumerations representing each of the statuses that may be parsed
 * from a topic.
 */
typedef enum AwsIotStatus
{
    AWS_IOT_ACCEPTED = 0, /**< Operation accepted. */
    AWS_IOT_REJECTED = 1, /**< Operation rejected. */
    AWS_IOT_UNKNOWN = 2   /**< Unknown status (neither accepted nor rejected). */
} AwsIotStatus_t;

/**
 * @brief Information required to generate a topic for AWS IoT.
 */
typedef struct AwsIotTopicInfo
{
    const char * pThingName;                 /**< @brief The Thing Name associated with the operation. */
    size_t thingNameLength;                  /**< @brief The length of `pThingName`. */
    const char * pOperationName;             /**< @brief The operation name to place in the topic. */
    uint16_t operationNameLength;            /**< @brief The length of `pOperationName`. */
    uint16_t longestSuffixLength;            /**< @brief The length of longest suffix that will be placed at the end of the topic. */
    void * ( *mallocString )( size_t size ); /**< @brief Function used to allocate a string, if needed. */
} AwsIotTopicInfo_t;

/**
 * @brief Information needed to modify AWS IoT subscription topics.
 *
 * @warning The buffer passed as `pTopicFilterBase` must be large enough to
 * accommodate the "/accepted" and "/rejected" suffixes.
 */
typedef struct AwsIotSubscriptionInfo_t
{
    IotMqttConnection_t mqttConnection;            /**< @brief The MQTT connection to use. */
    AwsIotMqttCallbackFunction_t callbackFunction; /**< @brief Callback function for MQTT subscribe. */
    uint32_t timeout;                              /**< @brief Timeout for MQTT function. */

    /* Topic filter. */
    char * pTopicFilterBase;        /**< @brief Contains the base topic filter, without "/accepted" or "/rejected". */
    uint16_t topicFilterBaseLength; /**< @brief Length of the base topic filter. */
} AwsIotSubscriptionInfo_t;

/**
 * @brief Thing Name and length, used to match subscriptions.
 */
typedef struct AwsIotThingName
{
    const char * pThingName; /**< @brief Thing Name to compare. */
    size_t thingNameLength;  /**< @brief Length of `pThingName`. */
} AwsIotThingName_t;

/**
 * @brief Initializes the lists used by AWS IoT operations.
 *
 * @param[in] pPendingOperationsList The list that holds pending operations for
 * a library.
 * @param[in] pSubscriptionsList The list that holds subscriptions for a library.
 * @param[in] pPendingOperationsMutex The mutex that guards the pending operations
 * list.
 * @param[in] pSubscriptionsMutex The mutex that guards the subscriptions list.
 *
 * @return `true` if all initialization succeeded; `false` otherwise.
 */
bool AwsIot_InitLists( IotListDouble_t * pPendingOperationsList,
                       IotListDouble_t * pSubscriptionsList,
                       IotMutex_t * pPendingOperationsMutex,
                       IotMutex_t * pSubscriptionsMutex );

/**
 * @brief Checks that a Thing Name is valid for AWS IoT.
 *
 * @param[in] pThingName Thing Name to validate.
 * @param[in] thingNameLength Length of `pThingName`.
 *
 * @return `true` if `pThingName` is valid; `false` otherwise.
 */
bool AwsIot_ValidateThingName( const char * pThingName,
                               size_t thingNameLength );

/**
 * @brief Extracts the client token from a JSON document.
 *
 * The client token is used to differentiate AWS IoT operations. It is unique per
 * operation.
 *
 * @param[in] pJsonDocument The JSON document to parse.
 * @param[in] jsonDocumentLength The length of `pJsonDocument`.
 * @param[out] pClientToken Set to point to the client token in `pJsonDocument`.
 * @param[out] pClientTokenLength Set to the length of the client token.
 *
 * @return `true` if the client token was found; `false` otherwise. The output
 * parameters are only valid if this function returns `true`.
 */
bool AwsIot_GetClientToken( const char * pJsonDocument,
                            size_t jsonDocumentLength,
                            const char ** pClientToken,
                            size_t * pClientTokenLength );

/**
 * @brief Parse the Thing Name from an MQTT topic.
 *
 * @param[in] pTopicName The topic to parse.
 * @param[in] topicNameLength The length of `pTopicName`.
 * @param[out] pThingName Set to point to the Thing Name.
 * @param[out] pThingNameLength Set to the length of the Thing Name.
 *
 * @return `true` if a Thing Name was successfully parsed; `false` otherwise. The output
 * parameters are only valid if this function returns `true`.
 */
bool AwsIot_ParseThingName( const char * pTopicName,
                            uint16_t topicNameLength,
                            const char ** pThingName,
                            size_t * pThingNameLength );

/**
 * @brief Parse the operation status (accepted or rejected) from an MQTT topic.
 *
 * @param[in] pTopicName The topic to parse.
 * @param[in] topicNameLength The length of `pTopicName`.
 *
 * @return Any #AwsIotStatus_t.
 */
AwsIotStatus_t AwsIot_ParseStatus( const char * pTopicName,
                                   uint16_t topicNameLength );

/**
 * @brief Generate a topic to use for an AWS IoT operation.
 *
 * @param[in] pTopicInfo Information needed to generate an AWS IoT topic.
 * @param[in,out] pTopicBuffer Where to place the generated topic. An existing
 * buffer may be passed in. If `NULL`, this function will attempt to allocate a
 * new buffer.
 * @param[out] pOperationTopicLength Set to the length of the generated topic.
 *
 * @warning This function does not check the length of `pTopicBuffer`! Any provided
 * buffer must be long enough to accommodate the Thing Name, operation name, and
 * any other suffixes.
 *
 * @return `true` if the topic was successfully generated; `false` otherwise.
 * This function will always succeed when an input buffer is provided.
 */
bool AwsIot_GenerateOperationTopic( const AwsIotTopicInfo_t * pTopicInfo,
                                    char ** pTopicBuffer,
                                    uint16_t * pOperationTopicLength );

/**
 * @brief Add or remove subscriptions for AWS IoT operations.
 *
 * @param[in] mqttOperation Either @ref mqtt_function_subscribesync or
 * @ref mqtt_function_unsubscribesync.
 * @param[in] pSubscriptionInfo Information needed to process an MQTT
 * operation.
 *
 * @return See the return values of @ref mqtt_function_subscribesync or
 * @ref mqtt_function_unsubscribesync.
 */
IotMqttError_t AwsIot_ModifySubscriptions( AwsIotMqttFunction_t mqttOperation,
                                           const AwsIotSubscriptionInfo_t * pSubscriptionInfo );

#endif /* ifndef AWS_IOT_H_ */
