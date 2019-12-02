/*
 * AWS IoT Shadow V2.1.0
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
 * @file aws_iot_shadow_types.h
 * @brief Types of the Thing Shadow library.
 */

#ifndef AWS_IOT_SHADOW_TYPES_H_
#define AWS_IOT_SHADOW_TYPES_H_

/* The config header is always included first. */
#include "iot_config.h"

/* MQTT types include. */
#include "types/iot_mqtt_types.h"

/*--------------------------- Shadow handle types ---------------------------*/

/**
 * @handles{shadow,Shadow library}
 */

/**
 * @ingroup shadow_datatypes_handles
 * @brief Opaque handle that references an in-progress Shadow operation.
 *
 * Set as an output parameter of @ref shadow_function_deleteasync, @ref shadow_function_getasync,
 * and @ref shadow_function_updateasync. These functions send a message to the Shadow
 * service requesting a Shadow operation; the result of this operation is unknown
 * until the Shadow service sends a response. Therefore, this handle serves as a
 * reference to Shadow operations awaiting a response from the Shadow service.
 *
 * This reference will be valid from the successful return of @ref shadow_function_deleteasync,
 * @ref shadow_function_getasync, or @ref shadow_function_updateasync. The reference becomes
 * invalid once the [completion callback](@ref AwsIotShadowCallbackInfo_t) is invoked,
 * or @ref shadow_function_wait returns.
 *
 * @initializer{AwsIotShadowOperation_t,AWS_IOT_SHADOW_OPERATION_INITIALIZER}
 *
 * @see @ref shadow_function_wait and #AWS_IOT_SHADOW_FLAG_WAITABLE for waiting on
 * a reference; or #AwsIotShadowCallbackInfo_t and #AwsIotShadowCallbackParam_t for an
 * asynchronous notification of completion.
 */
typedef struct _shadowOperation * AwsIotShadowOperation_t;

/*------------------------- Shadow enumerated types -------------------------*/

/**
 * @enums{shadow,Shadow library}
 */

/**
 * @ingroup shadow_datatypes_enums
 * @brief Return codes of [Shadow functions](@ref shadow_functions).
 *
 * The function @ref shadow_function_strerror can be used to get a return code's
 * description.
 *
 * The values between 400 (#AWS_IOT_SHADOW_BAD_REQUEST) and 500
 * (#AWS_IOT_SHADOW_SERVER_ERROR) may be returned by the Shadow service when it
 * rejects a Shadow operation. See [this page]
 * (https://docs.aws.amazon.com/iot/latest/developerguide/device-shadow-error-messages.html)
 * for more information.
 */
typedef enum AwsIotShadowError
{
    /**
     * @brief Shadow operation completed successfully.
     *
     * Functions that may return this value:
     * - @ref shadow_function_init
     * - @ref shadow_function_wait
     * - @ref shadow_function_deletesync
     * - @ref shadow_function_getsync
     * - @ref shadow_function_updatesync
     * - @ref shadow_function_setdeltacallback
     * - @ref shadow_function_setupdatedcallback
     * - @ref shadow_function_removepersistentsubscriptions
     *
     * Will also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     * when successful.
     */
    AWS_IOT_SHADOW_SUCCESS = 0,

    /**
     * @brief Shadow operation queued, awaiting result.
     *
     * Functions that may return this value:
     * - @ref shadow_function_deleteasync
     * - @ref shadow_function_getasync
     * - @ref shadow_function_updateasync
     */
    AWS_IOT_SHADOW_STATUS_PENDING = 1,

    /**
     * @brief Initialization failed.
     *
     * Functions that may return this value:
     * - @ref shadow_function_init
     */
    AWS_IOT_SHADOW_INIT_FAILED = 2,

    /**
     * @brief At least one parameter is invalid.
     *
     * Functions that may return this value:
     * - @ref shadow_function_deleteasync and @ref shadow_function_deletesync
     * - @ref shadow_function_getasync and @ref shadow_function_getsync
     * - @ref shadow_function_updateasync and @ref shadow_function_updatesync
     * - @ref shadow_function_wait
     * - @ref shadow_function_setdeltacallback
     * - @ref shadow_function_setupdatedcallback
     */
    AWS_IOT_SHADOW_BAD_PARAMETER = 3,

    /**
     * @brief Shadow operation failed because of memory allocation failure.
     *
     * Functions that may return this value:
     * - @ref shadow_function_deleteasync and @ref shadow_function_deletesync
     * - @ref shadow_function_getasync and @ref shadow_function_getsync
     * - @ref shadow_function_updateasync and @ref shadow_function_updatesync
     * - @ref shadow_function_setdeltacallback
     * - @ref shadow_function_setupdatedcallback
     */
    AWS_IOT_SHADOW_NO_MEMORY = 4,

    /**
     * @brief Shadow operation failed because of failure in MQTT library.
     *
     * Check the Shadow library logs for the error code returned by the MQTT
     * library.
     *
     * Functions that may return this value:
     * - @ref shadow_function_deleteasync and @ref shadow_function_deletesync
     * - @ref shadow_function_getasync and @ref shadow_function_getsync
     * - @ref shadow_function_updateasync and @ref shadow_function_updatesync
     * - @ref shadow_function_setdeltacallback
     * - @ref shadow_function_setupdatedcallback
     * - @ref shadow_function_removepersistentsubscriptions
     */
    AWS_IOT_SHADOW_MQTT_ERROR = 5,

    /**
     * @brief Response received from Shadow service not understood.
     *
     * Functions that may return this value:
     * - @ref shadow_function_deletesync
     * - @ref shadow_function_getsync
     * - @ref shadow_function_updatesync
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_BAD_RESPONSE = 7,

    /**
     * @brief A blocking Shadow operation timed out.
     *
     * Functions that may return this value:
     * - @ref shadow_function_deletesync
     * - @ref shadow_function_getsync
     * - @ref shadow_function_updatesync
     * - @ref shadow_function_wait
     * - @ref shadow_function_setdeltacallback
     * - @ref shadow_function_setupdatedcallback
     */
    AWS_IOT_SHADOW_TIMEOUT = 8,

    /**
     * @brief An API function was called before @ref shadow_function_init.
     *
     * Functions that may return this value:
     * - @ref shadow_function_deleteasync and @ref shadow_function_deletesync
     * - @ref shadow_function_getasync and @ref shadow_function_getsync
     * - @ref shadow_function_updateasync and @ref shadow_function_updatesync
     * - @ref shadow_function_wait
     * - @ref shadow_function_setdeltacallback
     * - @ref shadow_function_setupdatedcallback
     */
    AWS_IOT_SHADOW_NOT_INITIALIZED = 11,

    /**
     * @brief Shadow operation rejected: Bad request.
     *
     * Functions that may return this value:
     * - @ref shadow_function_deletesync
     * - @ref shadow_function_getsync
     * - @ref shadow_function_updatesync
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_BAD_REQUEST = 400,

    /**
     * @brief Shadow operation rejected: Unauthorized.
     *
     * Functions that may return this value:
     * - @ref shadow_function_deletesync
     * - @ref shadow_function_getsync
     * - @ref shadow_function_updatesync
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_UNAUTHORIZED = 401,

    /**
     * @brief Shadow operation rejected: Forbidden.
     *
     * Functions that may return this value:
     * - @ref shadow_function_deletesync
     * - @ref shadow_function_getsync
     * - @ref shadow_function_updatesync
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_FORBIDDEN = 403,

    /**
     * @brief Shadow operation rejected: Thing not found.
     *
     * Functions that may return this value:
     * - @ref shadow_function_deletesync
     * - @ref shadow_function_getsync
     * - @ref shadow_function_updatesync
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_NOT_FOUND = 404,

    /**
     * @brief Shadow operation rejected: Version conflict.
     *
     * Functions that may return this value:
     * - @ref shadow_function_deletesync
     * - @ref shadow_function_getsync
     * - @ref shadow_function_updatesync
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_CONFLICT = 409,

    /**
     * @brief Shadow operation rejected: The payload exceeds the maximum size
     * allowed.
     *
     * Functions that may return this value:
     * - @ref shadow_function_deletesync
     * - @ref shadow_function_getsync
     * - @ref shadow_function_updatesync
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_TOO_LARGE = 413,

    /**
     * @brief Shadow operation rejected: Unsupported document encoding; supported
     * encoding is UTF-8.
     *
     * Functions that may return this value:
     * - @ref shadow_function_deletesync
     * - @ref shadow_function_getsync
     * - @ref shadow_function_updatesync
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_UNSUPPORTED = 415,

    /**
     * @brief Shadow operation rejected: The Device Shadow service will generate
     * this error message when there are more than 10 in-flight requests.
     *
     * Functions that may return this value:
     * - @ref shadow_function_deletesync
     * - @ref shadow_function_getsync
     * - @ref shadow_function_updatesync
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_TOO_MANY_REQUESTS = 429,

    /**
     * @brief Shadow operation rejected: Internal service failure.
     *
     * Functions that may return this value:
     * - @ref shadow_function_deletesync
     * - @ref shadow_function_getsync
     * - @ref shadow_function_updatesync
     * - @ref shadow_function_wait
     *
     * May also be the value of a Shadow operation completion callback's<br>
     * [AwsIotShadowCallbackParam_t.operation.result](@ref AwsIotShadowCallbackParam_t.result)
     */
    AWS_IOT_SHADOW_SERVER_ERROR = 500,
} AwsIotShadowError_t;

/**
 * @ingroup shadow_datatypes_enums
 * @brief Types of Shadow library callbacks.
 *
 * One of these values will be placed in #AwsIotShadowCallbackParam_t.callbackType
 * to identify the reason for invoking a callback function.
 */
typedef enum AwsIotShadowCallbackType
{
    AWS_IOT_SHADOW_DELETE_COMPLETE, /**< Callback invoked because a [Shadow delete](@ref shadow_function_deleteasync) completed. */
    AWS_IOT_SHADOW_GET_COMPLETE,    /**< Callback invoked because a [Shadow get](@ref shadow_function_getasync) completed. */
    AWS_IOT_SHADOW_UPDATE_COMPLETE, /**< Callback invoked because a [Shadow update](@ref shadow_function_updateasync) completed. */
    AWS_IOT_SHADOW_DELTA_CALLBACK,  /**< Callback invoked for an incoming message on a [Shadow delta](@ref shadow_function_setdeltacallback) topic. */
    AWS_IOT_SHADOW_UPDATED_CALLBACK /**< Callback invoked for an incoming message on a [Shadow updated](@ref shadow_function_setupdatedcallback) topic. */
} AwsIotShadowCallbackType_t;

/*------------------------- Shadow parameter structs ------------------------*/

/**
 * @paramstructs{shadow,Shadow}
 */

/**
 * @ingroup shadow_datatypes_paramstructs
 * @brief Parameter to a Shadow callback function.
 *
 * @paramfor Shadow callback functions
 *
 * The Shadow library passes this struct to a callback function whenever a
 * Shadow operation completes or a message is received on a Shadow delta or
 * updated topic.
 *
 * The valid members of this struct are different based on
 * #AwsIotShadowCallbackParam_t.callbackType. If the callback type is
 * #AWS_IOT_SHADOW_DELETE_COMPLETE, #AWS_IOT_SHADOW_GET_COMPLETE, or
 * #AWS_IOT_SHADOW_UPDATE_COMPLETE, then #AwsIotShadowCallbackParam_t.operation
 * is valid. Otherwise, if the callback type is #AWS_IOT_SHADOW_DELTA_CALLBACK
 * or #AWS_IOT_SHADOW_UPDATED_CALLBACK, then #AwsIotShadowCallbackParam_t.callback
 * is valid.
 *
 * @attention Any pointers in this callback parameter may be freed as soon as the
 * [callback function](@ref AwsIotShadowCallbackInfo_t.function) returns. Therefore,
 * data must be copied if it is needed after the callback function returns.
 * @attention The Shadow library may set strings that are not NULL-terminated.
 *
 * @see #AwsIotShadowCallbackInfo_t for the signature of a callback function.
 */
typedef struct AwsIotShadowCallbackParam
{
    AwsIotShadowCallbackType_t callbackType; /**< @brief Reason for invoking the Shadow callback function to provide context. */

    const char * pThingName;                 /**< @brief The Thing Name associated with this Shadow callback. */
    size_t thingNameLength;                  /**< @brief Length of #AwsIotShadowCallbackParam_t.pThingName. */

    IotMqttConnection_t mqttConnection;      /**< @brief The MQTT connection associated with the Shadow callback. */

    union
    {
        /* Valid for completed Shadow operations. */
        struct
        {
            /* Valid for a completed Shadow GET operation. */
            struct
            {
                const char * pDocument;        /**< @brief Retrieved Shadow document. */
                size_t documentLength;         /**< @brief Length of retrieved Shadow document. */
            } get;                             /**< @brief Retrieved Shadow document, valid only for a completed [Shadow Get](@ref shadow_function_getasync). */

            AwsIotShadowError_t result;        /**< @brief Result of Shadow operation, e.g. succeeded or failed. */
            AwsIotShadowOperation_t reference; /**< @brief Reference to the Shadow operation that completed. */
        } operation;                           /**< @brief Information on a completed Shadow operation. */

        /* Valid for a message on a Shadow delta or updated topic. */
        struct
        {
            const char * pDocument; /**< @brief Shadow delta or updated document. */
            size_t documentLength;  /**< @brief Length of Shadow delta or updated document. */
        } callback;                 /**< @brief Shadow document from an incoming delta or updated topic. */
    } u;                            /**< @brief Valid member depends on callback type. */
} AwsIotShadowCallbackParam_t;

/**
 * @ingroup shadow_datatypes_paramstructs
 * @brief Information on a user-provided Shadow callback function.
 *
 * @paramfor @ref shadow_function_deleteasync, @ref shadow_function_getasync, @ref
 * shadow_function_updateasync, @ref shadow_function_setdeltacallback, @ref
 * shadow_function_setupdatedcallback
 *
 * Provides a function to be invoked when a Shadow operation completes or when a
 * Shadow document is received on a callback topic (delta or updated).
 *
 * @initializer{AwsIotShadowCallbackInfo_t,AWS_IOT_SHADOW_CALLBACK_INFO_INITIALIZER}
 */
typedef struct AwsIotShadowCallbackInfo
{
    void * pCallbackContext; /**< @brief The first parameter to pass to the callback function. */

    /**
     * @brief User-provided callback function signature.
     *
     * @param[in] pCallbackContext #AwsIotShadowCallbackInfo_t.pCallbackContext
     * @param[in] pCallbackParam Details on the outcome of the Shadow
     * operation or an incoming Shadow document.
     *
     * @see #AwsIotShadowCallbackParam_t for more information on the second parameter.
     */
    void ( * function )( void * pCallbackContext,
                         AwsIotShadowCallbackParam_t * pCallbackParam );
} AwsIotShadowCallbackInfo_t;

/**
 * @ingroup shadow_datatypes_paramstructs
 * @brief Information on a Shadow document for @ref shadow_function_getasync or @ref
 * shadow_function_updateasync.
 *
 * @paramfor @ref shadow_function_getasync, @ref shadow_function_updateasync
 *
 * The valid members of this struct are different based on whether this struct
 * is passed to @ref shadow_function_getasync or @ref shadow_function_updateasync. When
 * passed to @ref shadow_function_getasync, the `get` member is valid. When passed to
 * @ref shadow_function_updateasync, the `update` member is valid. All other members
 * must always be set.
 *
 * @initializer{AwsIotShadowDocumentInfo_t,AWS_IOT_SHADOW_DOCUMENT_INFO_INITIALIZER}
 */
typedef struct AwsIotShadowDocumentInfo
{
    const char * pThingName; /**< @brief The Thing Name associated with this Shadow document. */
    size_t thingNameLength;  /**< @brief Length of #AwsIotShadowDocumentInfo_t.pThingName. */

    IotMqttQos_t qos;        /**< @brief QoS when sending a Shadow get or update message. See #IotMqttPublishInfo_t.qos. */
    uint32_t retryLimit;     /**< @brief Maximum number of retries for a Shadow get or update message. See #IotMqttPublishInfo_t.retryLimit. */
    uint32_t retryMs;        /**< @brief First retry time for a Shadow get or update message. See IotMqttPublishInfo_t.retryMs. */

    union
    {
        /* Valid for Shadow get. */
        struct
        {
            /**
             * @brief Function to allocate memory for an incoming Shadow document.
             *
             * @param[in] documentLength Length of the document that needs to
             * be allocated.
             * This only needs to be set if #AWS_IOT_SHADOW_FLAG_WAITABLE is passed to
             * @ref shadow_function_getasync.
             */
            void *( *mallocDocument )( size_t documentLength );
        } get; /**< @brief Valid members for @ref shadow_function_getasync. */

        /* Valid for Shadow update. */
        struct
        {
            const char * pUpdateDocument; /**< @brief The Shadow document to send in the update. */
            size_t updateDocumentLength;  /**< @brief Length of Shadow update document. */
        } update;                         /**< @brief Valid members for @ref shadow_function_updateasync. */
    } u;                                  /**< @brief Valid member depends on operation type. */
} AwsIotShadowDocumentInfo_t;

/*------------------------ Shadow defined constants -------------------------*/

/**
 * @constantspage{shadow,Shadow library}
 *
 * @section shadow_constants_initializers Shadow Initializers
 * @brief Provides default values for the data types of the Shadow library.
 *
 * @snippet this define_shadow_initializers
 *
 * All user-facing data types of the Shadow library should be initialized
 * using one of the following.
 *
 * @warning Failing to initialize a Shadow data type with the appropriate
 * initializer may result in undefined behavior!
 * @note The initializers may change at any time in future versions, but their
 * names will remain the same.
 *
 * <b>Example</b>
 * @code{c}
 * AwsIotShadowCallbackInfo_t callbackInfo = AWS_IOT_SHADOW_CALLBACK_INFO_INITIALIZER;
 * AwsIotShadowDocumentInfo_t documentInfo = AWS_IOT_SHADOW_DOCUMENT_INFO_INITIALIZER;
 * AwsIotShadowOperation_t operation = AWS_IOT_SHADOW_OPERATION_INITIALIZER;
 * @endcode
 *
 * @section shadow_constants_flags Shadow Function Flags
 * @brief Flags that modify the behavior of Shadow library functions.
 *
 * Flags should be bitwise-ORed with each other to change the behavior of
 * Shadow library functions.
 *
 * The following flags are valid for the Shadow operation functions:
 * @ref shadow_function_deleteasync, @ref shadow_function_getasync, @ref shadow_function_updateasync,
 * and their blocking versions.
 * - #AWS_IOT_SHADOW_FLAG_WAITABLE <br>
 *   @copybrief AWS_IOT_SHADOW_FLAG_WAITABLE
 * - #AWS_IOT_SHADOW_FLAG_KEEP_SUBSCRIPTIONS <br>
 *   @copybrief AWS_IOT_SHADOW_FLAG_KEEP_SUBSCRIPTIONS
 *
 * The following flags are valid for @ref shadow_function_removepersistentsubscriptions.
 * These flags are not valid for the Shadow operation functions.
 * - #AWS_IOT_SHADOW_FLAG_REMOVE_DELETE_SUBSCRIPTIONS <br>
 *   @copybrief AWS_IOT_SHADOW_FLAG_REMOVE_DELETE_SUBSCRIPTIONS
 * - #AWS_IOT_SHADOW_FLAG_REMOVE_GET_SUBSCRIPTIONS <br>
 *   @copybrief AWS_IOT_SHADOW_FLAG_REMOVE_GET_SUBSCRIPTIONS
 * - #AWS_IOT_SHADOW_FLAG_REMOVE_UPDATE_SUBSCRIPTIONS <br>
 *   @copybrief AWS_IOT_SHADOW_FLAG_REMOVE_UPDATE_SUBSCRIPTIONS
 *
 * @note The values of the flags may change at any time in future versions, but
 * their names will remain the same. Additionally, flags which may be used at
 * the same time will be bitwise-exclusive of each other.
 */

/* @[define_shadow_initializers] */
#define AWS_IOT_SHADOW_CALLBACK_INFO_INITIALIZER    { 0 }        /**< @brief Initializer for #AwsIotShadowCallbackInfo_t. */
#define AWS_IOT_SHADOW_DOCUMENT_INFO_INITIALIZER    { 0 }        /**< @brief Initializer for #AwsIotShadowDocumentInfo_t. */
#define AWS_IOT_SHADOW_OPERATION_INITIALIZER        NULL         /**< @brief Initializer for #AwsIotShadowOperation_t. */
/* @[define_shadow_initializers] */

/**
 * @brief Allows the use of @ref shadow_function_wait for blocking until completion.
 *
 * This flag is only valid if passed to the functions @ref shadow_function_deleteasync,
 * @ref shadow_function_getasync, or @ref shadow_function_updateasync.
 *
 * An #AwsIotShadowOperation_t <b>MUST</b> be provided if this flag is set.
 * Additionally, an #AwsIotShadowCallbackInfo_t <b>MUST NOT</b> be provided.
 *
 * @note If this flag is set, @ref shadow_function_wait <b>MUST</b> be called to
 * clean up resources.
 */
#define AWS_IOT_SHADOW_FLAG_WAITABLE                       ( 0x00000001 )

/**
 * @brief Maintain the subscriptions for the Shadow operation topics, even after
 * this function returns.
 *
 * This flag is only valid if passed to the functions @ref shadow_function_deleteasync,
 * @ref shadow_function_getasync, @ref shadow_function_updateasync, or their blocking versions.
 *
 * The Shadow service reports results of Shadow operations by publishing
 * messages to MQTT topics. By default, the functions @ref shadow_function_deleteasync,
 * @ref shadow_function_getasync, and @ref shadow_function_updateasync subscribe to the
 * necessary topics, wait for the Shadow service to publish the result of the
 * Shadow operation, then unsubscribe from those topics. This workflow is suitable
 * for infrequent Shadow operations, but is inefficient for frequent, periodic
 * Shadow operations (where subscriptions for the Shadow operation topics would be
 * constantly added and removed).
 *
 * This flag causes @ref shadow_function_deleteasync, @ref shadow_function_getasync, or
 * @ref shadow_function_updateasync to maintain Shadow operation topic subscriptions,
 * even after the function returns. These subscriptions may then be used by a
 * future call to the same function.
 *
 * This flags only needs to be set once, after which subscriptions are maintained
 * and reused for a specific Thing Name and Shadow function. The function @ref
 * shadow_function_removepersistentsubscriptions may be used to remove
 * subscriptions maintained by this flag.
 */
#define AWS_IOT_SHADOW_FLAG_KEEP_SUBSCRIPTIONS             ( 0x00000002 )

/**
 * @brief Remove the persistent subscriptions from a Shadow delete operation.
 *
 * This flag is only valid if passed to the function @ref
 * shadow_function_removepersistentsubscriptions.
 *
 * This flag may be passed to @ref shadow_function_removepersistentsubscriptions
 * to remove any subscriptions for a specific Thing Name maintained by a previous
 * call to @ref shadow_function_deleteasync or @ref shadow_function_deletesync.
 *
 * @warning Do not call @ref shadow_function_removepersistentsubscriptions with
 * this flag for Thing Names with any in-progress Shadow delete operations.
 */
#define AWS_IOT_SHADOW_FLAG_REMOVE_DELETE_SUBSCRIPTIONS    ( 0x00000001 )

/**
 * @brief Remove the persistent subscriptions from a Shadow get operation.
 *
 * This flag is only valid if passed to the function @ref
 * shadow_function_removepersistentsubscriptions.
 *
 * This flag may be passed to @ref shadow_function_removepersistentsubscriptions
 * to remove any subscriptions for a specific Thing Name maintained by a previous
 * call to @ref shadow_function_getasync or @ref shadow_function_getsync.
 *
 * @warning Do not call @ref shadow_function_removepersistentsubscriptions with
 * this flag for Thing Names with any in-progress Shadow get operations.
 */
#define AWS_IOT_SHADOW_FLAG_REMOVE_GET_SUBSCRIPTIONS       ( 0x00000002 )

/**
 * @brief Remove the persistent subscriptions from a Shadow update operation.
 *
 * This flag is only valid if passed to the function @ref
 * shadow_function_removepersistentsubscriptions.
 *
 * This flag may be passed to @ref shadow_function_removepersistentsubscriptions
 * to remove any subscriptions for a specific Thing Name maintained by a previous
 * call to @ref shadow_function_updateasync or @ref shadow_function_updatesync.
 *
 * @warning Do not call @ref shadow_function_removepersistentsubscriptions with
 * this flag for Thing Names with any in-progress Shadow update operations.
 */
#define AWS_IOT_SHADOW_FLAG_REMOVE_UPDATE_SUBSCRIPTIONS    ( 0x00000004 )

#endif /* ifndef AWS_IOT_SHADOW_TYPES_H_ */
