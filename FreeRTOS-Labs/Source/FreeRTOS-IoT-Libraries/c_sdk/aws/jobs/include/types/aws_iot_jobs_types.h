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
 * @file aws_iot_jobs_types.h
 * @brief Types of the Jobs library.
 */

#ifndef AWS_IOT_JOBS_TYPES_H_
#define AWS_IOT_JOBS_TYPES_H_

/* The config header is always included first. */
#include "iot_config.h"

/* MQTT types include. */
#include "types/iot_mqtt_types.h"

/*---------------------------- Jobs handle types ----------------------------*/

/**
 * @handles{jobs,Jobs library}
 */

/**
 * @ingroup jobs_datatypes_handles
 * @brief Opaque handle that references an in-progress Jobs operation.
 *
 * Set as an output parameter of @ref jobs_function_getpendingasync, @ref jobs_function_startnextasync,
 * @ref jobs_function_describeasync, and @ref jobs_function_updateasync. These functions send a
 * message to the Jobs service requesting a Jobs operation; the result of this operation
 * is unknown until the Jobs service sends a response. Therefore, this handle serves as a
 * reference to Jobs operations awaiting a response from the Jobs service.
 *
 * This reference will be valid from the successful return of @ref jobs_function_getpendingasync,
 * @ref jobs_function_startnextasync, @ref jobs_function_describeasync, and @ref jobs_function_updateasync.
 * The reference becomes invalid once the [completion callback](@ref AwsIotJobsCallbackInfo_t)
 * is invoked, or @ref jobs_function_wait returns.
 *
 * @initializer{AwsIotJobsOperation_t,AWS_IOT_JOBS_OPERATION_INITIALIZER}
 *
 * @see @ref jobs_function_wait and #AWS_IOT_JOBS_FLAG_WAITABLE for waiting on
 * a reference; or #AwsIotJobsCallbackInfo_t and #AwsIotJobsCallbackParam_t for an
 * asynchronous notification of completion.
 */
typedef struct _jobsOperation * AwsIotJobsOperation_t;

/*-------------------------- Jobs enumerated types --------------------------*/

/**
 * @enums{jobs,Jobs library}
 */

/**
 * @ingroup jobs_datatypes_enums
 * @brief Return codes of [Jobs functions](@ref jobs_functions).
 *
 * The function @ref jobs_function_strerror can be used to get a return code's
 * description.
 *
 * The values between #AWS_IOT_JOBS_INVALID_TOPIC and #AWS_IOT_JOBS_TERMINAL_STATE
 * may be returned by the Jobs service upon failure of a Jobs operation. See [this page]
 * (https://docs.aws.amazon.com/iot/latest/developerguide/jobs-api.html#jobs-mqtt-error-response)
 * for more information.
 */
typedef enum AwsIotJobsError
{
    /**
     * @brief Jobs operation completed successfully.
     *
     * Functions that may return this value:
     * - @ref jobs_function_init
     * - @ref jobs_function_wait
     * - @ref jobs_function_getpendingsync
     * - @ref jobs_function_startnextsync
     * - @ref jobs_function_describesync
     * - @ref jobs_function_updatesync
     * - @ref jobs_function_setnotifypendingcallback
     * - @ref jobs_function_setnotifynextcallback
     * - @ref jobs_function_removepersistentsubscriptions
     *
     * Will also be the value of a Jobs operation completion callback's<br>
     * [AwsIotJobsCallbackParam_t.operation.result](@ref AwsIotJobsCallbackParam_t.result)
     * when successful.
     */
    AWS_IOT_JOBS_SUCCESS = 0,

    /**
     * @brief Jobs operation queued, awaiting result.
     *
     * Functions that may return this value:
     * - @ref jobs_function_getpendingasync
     * - @ref jobs_function_startnextasync
     * - @ref jobs_function_describeasync
     * - @ref jobs_function_updateasync
     */
    AWS_IOT_JOBS_STATUS_PENDING = 1,

    /**
     * @brief Initialization failed.
     *
     * Functions that may return this value:
     * - @ref jobs_function_init
     */
    AWS_IOT_JOBS_INIT_FAILED = 2,

    /**
     * @brief At least one parameter is invalid.
     *
     * Functions that may return this value:
     * - @ref jobs_function_getpendingasync and @ref jobs_function_getpendingsync
     * - @ref jobs_function_startnextasync and @ref jobs_function_startnextsync
     * - @ref jobs_function_describeasync and @ref jobs_function_describesync
     * - @ref jobs_function_updateasync and @ref jobs_function_updatesync
     * - @ref jobs_function_wait
     * - @ref jobs_function_setnotifypendingcallback
     * - @ref jobs_function_setnotifynextcallback
     * - @ref jobs_function_removepersistentsubscriptions
     */
    AWS_IOT_JOBS_BAD_PARAMETER = 3,

    /**
     * @brief Jobs operation failed because of memory allocation failure.
     *
     * Functions that may return this value:
     * - @ref jobs_function_getpendingasync and @ref jobs_function_getpendingsync
     * - @ref jobs_function_startnextasync and @ref jobs_function_startnextsync
     * - @ref jobs_function_describeasync and @ref jobs_function_describesync
     * - @ref jobs_function_updateasync and @ref jobs_function_updatesync
     * - @ref jobs_function_setnotifypendingcallback
     * - @ref jobs_function_setnotifynextcallback
     */
    AWS_IOT_JOBS_NO_MEMORY = 4,

    /**
     * @brief Jobs operation failed because of failure in MQTT library.
     *
     * Functions that may return this value:
     * - @ref jobs_function_getpendingasync and @ref jobs_function_getpendingsync
     * - @ref jobs_function_startnextasync and @ref jobs_function_startnextsync
     * - @ref jobs_function_describeasync and @ref jobs_function_describesync
     * - @ref jobs_function_updateasync and @ref jobs_function_updatesync
     * - @ref jobs_function_setnotifypendingcallback
     * - @ref jobs_function_setnotifynextcallback
     * - @ref jobs_function_removepersistentsubscriptions
     */
    AWS_IOT_JOBS_MQTT_ERROR = 5,

    /**
     * @brief Response received from Jobs service not understood.
     *
     * Functions that may return this value:
     * - @ref jobs_function_getpendingsync
     * - @ref jobs_function_startnextsync
     * - @ref jobs_function_describesync
     * - @ref jobs_function_updatesync
     * - @ref jobs_function_wait
     *
     * May also be the value of a Jobs operation completion callback's<br>
     * [AwsIotJobsCallbackParam_t.operation.result](@ref AwsIotJobsCallbackParam_t.result).
     */
    AWS_IOT_JOBS_BAD_RESPONSE = 7,

    /**
     * @brief A blocking Jobs operation timed out.
     *
     * Functions that may return this value:
     * - @ref jobs_function_getpendingsync
     * - @ref jobs_function_startnextsync
     * - @ref jobs_function_describesync
     * - @ref jobs_function_updatesync
     * - @ref jobs_function_wait
     * - @ref jobs_function_setnotifypendingcallback
     * - @ref jobs_function_setnotifynextcallback
     */
    AWS_IOT_JOBS_TIMEOUT = 8,

    /**
     * @brief An API function was called before @ref jobs_function_init.
     *
     * Functions that may return this value:
     * - @ref jobs_function_getpendingasync and @ref jobs_function_getpendingsync
     * - @ref jobs_function_startnextasync and @ref jobs_function_startnextsync
     * - @ref jobs_function_describeasync and @ref jobs_function_describesync
     * - @ref jobs_function_updateasync and @ref jobs_function_updatesync
     * - @ref jobs_function_wait
     * - @ref jobs_function_setnotifypendingcallback
     * - @ref jobs_function_setnotifynextcallback
     */
    AWS_IOT_JOBS_NOT_INITIALIZED = 11,

    /**
     * @brief Jobs operation failed: A request was sent to an unknown topic.
     *
     * Functions that may return this value:
     * - @ref jobs_function_getpendingsync
     * - @ref jobs_function_startnextsync
     * - @ref jobs_function_describesync
     * - @ref jobs_function_updatesync
     * - @ref jobs_function_wait
     *
     * May also be the value of a Jobs operation completion callback's<br>
     * [AwsIotJobsCallbackParam_t.operation.result](@ref AwsIotJobsCallbackParam_t.result).
     */
    AWS_IOT_JOBS_INVALID_TOPIC = 12,

    /**
     * @brief Jobs operation failed: The contents of the request were not understood.
     *
     * Jobs requests must be UTF-8 encoded JSON documents.
     *
     * Functions that may return this value:
     * - @ref jobs_function_getpendingsync
     * - @ref jobs_function_startnextsync
     * - @ref jobs_function_describesync
     * - @ref jobs_function_updatesync
     * - @ref jobs_function_wait
     *
     * May also be the value of a Jobs operation completion callback's<br>
     * [AwsIotJobsCallbackParam_t.operation.result](@ref AwsIotJobsCallbackParam_t.result).
     */
    AWS_IOT_JOBS_INVALID_JSON = 13,

    /**
     * @brief Jobs operation failed: The contents of the request were invalid.
     *
     * Functions that may return this value:
     * - @ref jobs_function_getpendingsync
     * - @ref jobs_function_startnextsync
     * - @ref jobs_function_describesync
     * - @ref jobs_function_updatesync
     * - @ref jobs_function_wait
     *
     * May also be the value of a Jobs operation completion callback's<br>
     * [AwsIotJobsCallbackParam_t.operation.result](@ref AwsIotJobsCallbackParam_t.result).
     */
    AWS_IOT_JOBS_INVALID_REQUEST = 14,

    /**
     * @brief Jobs operation failed: An update attempted to change the job execution
     * to an invalid state.
     *
     * Functions that may return this value:
     * - @ref jobs_function_startnextsync
     * - @ref jobs_function_updatesync
     * - @ref jobs_function_wait
     *
     * May also be the value of a Jobs operation completion callback's<br>
     * [AwsIotJobsCallbackParam_t.operation.result](@ref AwsIotJobsCallbackParam_t.result)
     * following a call to @ref jobs_function_startnextasync or @ref jobs_function_updateasync.
     */
    AWS_IOT_JOBS_INVALID_STATE = 15,

    /**
     * @brief Jobs operation failed: The specified job execution does not exist.
     *
     * * Functions that may return this value:
     * - @ref jobs_function_describesync
     * - @ref jobs_function_updatesync
     * - @ref jobs_function_wait
     *
     * May also be the value of a Jobs operation completion callback's<br>
     * [AwsIotJobsCallbackParam_t.operation.result](@ref AwsIotJobsCallbackParam_t.result)
     * following a call to @ref jobs_function_describeasync or @ref jobs_function_updateasync.
     */
    AWS_IOT_JOBS_NOT_FOUND = 16,

    /**
     * @brief Jobs operation failed: The Jobs service expected a version that did
     * not match what was in the request.
     *
     * * Functions that may return this value:
     * - @ref jobs_function_updatesync
     * - @ref jobs_function_wait
     *
     * May also be the value of a Jobs operation completion callback's<br>
     * [AwsIotJobsCallbackParam_t.operation.result](@ref AwsIotJobsCallbackParam_t.result)
     * following a call to @ref jobs_function_updateasync.
     */
    AWS_IOT_JOBS_VERSION_MISMATCH = 17,

    /**
     * @brief Jobs operation failed: The Jobs service encountered an internal error.
     *
     * Functions that may return this value:
     * - @ref jobs_function_getpendingsync
     * - @ref jobs_function_startnextsync
     * - @ref jobs_function_describesync
     * - @ref jobs_function_updatesync
     * - @ref jobs_function_wait
     *
     * May also be the value of a Jobs operation completion callback's<br>
     * [AwsIotJobsCallbackParam_t.operation.result](@ref AwsIotJobsCallbackParam_t.result).
     */
    AWS_IOT_JOBS_INTERNAL_ERROR = 18,

    /**
     * @brief Jobs operation failed: The request was throttled.
     *
     * Functions that may return this value:
     * - @ref jobs_function_getpendingsync
     * - @ref jobs_function_startnextsync
     * - @ref jobs_function_describesync
     * - @ref jobs_function_updatesync
     * - @ref jobs_function_wait
     *
     * May also be the value of a Jobs operation completion callback's<br>
     * [AwsIotJobsCallbackParam_t.operation.result](@ref AwsIotJobsCallbackParam_t.result).
     */
    AWS_IOT_JOBS_THROTTLED = 19,

    /**
     * @brief Jobs operation failed: Attempt to describe a Job in a terminal state.
     *
     * Functions that may return this value:
     * - @ref jobs_function_describesync
     * - @ref jobs_function_wait
     *
     * May also be the value of a Jobs operation completion callback's<br>
     * [AwsIotJobsCallbackParam_t.operation.result](@ref AwsIotJobsCallbackParam_t.result)
     * following a call to @ref jobs_function_describeasync.
     */
    AWS_IOT_JOBS_TERMINAL_STATE = 20
} AwsIotJobsError_t;

/**
 * @ingroup jobs_datatypes_enums
 * @brief Possible states of jobs.
 *
 * The function @ref jobs_function_statename can be used to get a state's
 * description.
 *
 * See [this page]
 * (https://docs.aws.amazon.com/iot/latest/apireference/API_iot-jobs-data_JobExecutionState.html)
 * for more information on Job states.
 */
typedef enum AwsIotJobState
{
    /**
     * @brief A Job is queued and awaiting execution.
     */
    AWS_IOT_JOB_STATE_QUEUED,

    /**
     * @brief A Job is currently executing.
     */
    AWS_IOT_JOB_STATE_IN_PROGRESS,

    /**
     * @brief A Job has failed. This is a terminal state.
     */
    AWS_IOT_JOB_STATE_FAILED,

    /**
     * @brief A Job has succeeded. This is a terminal state.
     */
    AWS_IOT_JOB_STATE_SUCCEEDED,

    /**
     * @brief A Job was canceled. This is a terminal state.
     */
    AWS_IOT_JOB_STATE_CANCELED,

    /**
     * @brief A Job's timer has expired. This is a terminal state.
     *
     * Jobs are considered timed out if they remain [IN_PROGRESS]
     * (@ref AWS_IOT_JOB_STATE_IN_PROGRESS) for more than their
     * `inProgressTimeoutInMinutes` property or a [Job update](@ref jobs_function_updateasync)
     * was not sent within [stepTimeoutInMinutes](@ref AwsIotJobsUpdateInfo_t.stepTimeoutInMinutes).
     */
    AWS_IOT_JOB_STATE_TIMED_OUT,

    /**
     * @brief A Job was rejected by the device. This is a terminal state.
     */
    AWS_IOT_JOB_STATE_REJECTED,

    /**
     * @brief A Job was removed. This is a terminal state.
     */
    AWS_IOT_JOB_STATE_REMOVED
} AwsIotJobState_t;

/**
 * @ingroup jobs_datatypes_enums
 * @brief Types of Jobs library callbacks.
 *
 * One of these values will be placed in #AwsIotJobsCallbackParam_t.callbackType
 * to identify the reason for invoking a callback function.
 */
typedef enum AwsIotJobsCallbackType
{
    AWS_IOT_JOBS_GET_PENDING_COMPLETE = 0,    /**< Callback invoked because a [Jobs get pending](@ref jobs_function_getpendingasync) completed. */
    AWS_IOT_JOBS_START_NEXT_COMPLETE = 1,     /**< Callback invoked because a [Jobs start next](@ref jobs_function_startnextasync) completed. */
    AWS_IOT_JOBS_DESCRIBE_COMPLETE = 2,       /**< Callback invoked because a [Jobs describe](@ref jobs_function_describeasync) completed. */
    AWS_IOT_JOBS_UPDATE_COMPLETE = 3,         /**< Callback invoked because a [Jobs update](@ref jobs_function_updateasync) completed. */
    AWS_IOT_JOBS_NOTIFY_PENDING_CALLBACK = 4, /**< Callback invoked for an incoming message on a [Jobs notify-pending](@ref jobs_function_setnotifypendingcallback) topic. */
    AWS_IOT_JOBS_NOTIFY_NEXT_CALLBACK = 5     /**< Callback invoked for an incoming message on a [Jobs notify-next](@ref jobs_function_setnotifynextcallback) topic. */
} AwsIotJobsCallbackType_t;

/*-------------------------- Jobs parameter structs -------------------------*/

/**
 * @paramstructs{jobs,Jobs library}
 */

/**
 * @ingroup jobs_datatypes_paramstructs
 * @brief Parameter to a Jobs callback function.
 *
 * @paramfor Jobs callback functions
 *
 * The Jobs library passes this struct to a callback function whenever a
 * Jobs operation completes or a message is received on a Jobs notify-pending
 * or notify-next topic.
 *
 * The valid members of this struct are different based on
 * #AwsIotJobsCallbackParam_t.callbackType. If the callback type is
 * #AWS_IOT_JOBS_GET_PENDING_COMPLETE, #AWS_IOT_JOBS_START_NEXT_COMPLETE,
 * #AWS_IOT_JOBS_DESCRIBE_COMPLETE, or #AWS_IOT_JOBS_UPDATE_COMPLETE, then
 * #AwsIotJobsCallbackParam_t.operation is valid. Otherwise, if the callback type
 * is #AWS_IOT_JOBS_NOTIFY_PENDING_CALLBACK or #AWS_IOT_JOBS_NOTIFY_NEXT_CALLBACK,
 * then #AwsIotJobsCallbackParam_t.callback is valid.
 *
 * @attention Any pointers in this callback parameter may be freed as soon as the
 * [callback function](@ref AwsIotJobsCallbackInfo_t.function) returns. Therefore,
 * data must be copied if it is needed after the callback function returns.
 * @attention The Jobs library may set strings that are not NULL-terminated.
 *
 * @see #AwsIotJobsCallbackInfo_t for the signature of a callback function.
 */
typedef struct AwsIotJobsCallbackParam
{
    AwsIotJobsCallbackType_t callbackType; /**< @brief Reason for invoking the Jobs callback function to provide context. */

    const char * pThingName;               /**< @brief The Thing Name associated with this Jobs callback. */
    size_t thingNameLength;                /**< @brief Length of #AwsIotJobsCallbackParam_t.pThingName. */

    IotMqttConnection_t mqttConnection;    /**< @brief The MQTT connection associated with the Jobs callback. */

    union
    {
        /* Valid for completed Jobs operations. */
        struct
        {
            AwsIotJobsError_t result;        /**< @brief Result of Jobs operation, e.g. succeeded or failed. */
            AwsIotJobsOperation_t reference; /**< @brief Reference to the Jobs operation that completed. */

            const char * pResponse;          /**< @brief Response retrieved from the Jobs service. */
            size_t responseLength;           /**< @brief Length of retrieved response. */
        } operation;                         /**< @brief Information on a completed Jobs operation. */

        /* Valid for a message on a Jobs notify-pending or notify-next topic. */
        struct
        {
            const char * pDocument; /**< @brief Job execution document received on callback. */
            size_t documentLength;  /**< @brief Length of job execution document. */
        } callback;                 /**< @brief Jobs document from an incoming delta or updated topic. */
    } u;                            /**< @brief Valid member depends on callback type. */
} AwsIotJobsCallbackParam_t;

/**
 * @ingroup jobs_datatypes_paramstructs
 * @brief Information on a user-provided Jobs callback function.
 *
 * @paramfor @ref jobs_function_getpendingasync, @ref jobs_function_startnextasync,
 * @ref jobs_function_describeasync, @ref jobs_function_updateasync,
 * @ref jobs_function_setnotifypendingcallback, @ref jobs_function_setnotifynextcallback
 *
 * Provides a function to be invoked when a Jobs operation completes or when a
 * Jobs document is received on a callback topic (notify-pending or notify-next).
 *
 * @initializer{AwsIotJobsCallbackInfo_t,AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER}
 */
typedef struct AwsIotJobsCallbackInfo
{
    void * pCallbackContext; /**< @brief The first parameter to pass to the callback function. */

    /**
     * @brief User-provided callback function signature.
     *
     * @param[in] void* #AwsIotJobsCallbackInfo_t.pCallbackContext
     * @param[in] AwsIotJobsCallbackParam_t* Details on the outcome of the Jobs
     * operation or an incoming Job document.
     *
     * @see #AwsIotJobsCallbackParam_t for more information on the second parameter.
     */
    void ( * function )( void *,
                         AwsIotJobsCallbackParam_t * );

    /**
     * @brief Callback function to replace when passed to @ref jobs_function_setnotifynextcallback
     * or @ref jobs_function_setnotifypendingcallback.
     *
     * This member is ignored by Jobs operation functions.
     *
     * The number of callbacks of each type that may be registered for each Thing
     * is limited by @ref AWS_IOT_JOBS_NOTIFY_CALLBACKS. If @ref AWS_IOT_JOBS_NOTIFY_CALLBACKS
     * is `2`, that means that a maximum of `2` NOTIFY PENDING and `2` NOTIFY NEXT callbacks
     * (`4` total callbacks) may be set. This member is used to replace an existing callback
     * with a new one.
     *
     * To add a new callback:
     * @code{c}
     * AwsIotJobsCallbackInfo_t callbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
     *
     * callbackInfo.function = _newCallback;
     * callbackInfo.oldFunction = NULL;
     * @endcode
     *
     * For example, if the function `_oldCallback()` is currently registered:
     * - To replace `_oldCallback()` with a new callback function `_newCallback()`:
     * @code{c}
     * AwsIotJobsCallbackInfo_t callbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
     *
     * callbackInfo.function = _newCallback;
     * callbackInfo.oldFunction = _oldCallback;
     * @endcode
     * - To remove `_oldCallback()`:
     * @code{c}
     * AwsIotJobsCallbackInfo_t callbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
     *
     * callbackInfo.function = NULL;
     * callbackInfo.oldFunction = _oldCallback;
     * @endcode
     */
    void ( * oldFunction )( void *,
                            AwsIotJobsCallbackParam_t * );
} AwsIotJobsCallbackInfo_t;

/**
 * @ingroup jobs_datatypes_paramstructs
 * @brief Common information provided to Jobs requests.
 *
 * @paramfor @ref jobs_function_getpendingasync, @ref jobs_function_getpendingsync,
 * @ref jobs_function_startnextasync, @ref jobs_function_startnextsync
 * @ref jobs_function_describeasync, @ref jobs_function_describesync,
 * @ref jobs_function_updateasync, @ref jobs_function_updatesync
 *
 * @initializer{AwsIotJobsRequestInfo_t,AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER}
 */
typedef struct AwsIotJobsRequestInfo
{
    /**
     * @brief The MQTT connection to use for the Jobs request.
     */
    IotMqttConnection_t mqttConnection;

    /* These members allow Jobs commands to be retried. Be careful that duplicate
     * commands do no cause unexpected application behavior. Use of QoS 0 is recommended. */
    IotMqttQos_t qos;        /**< @brief QoS when sending the Jobs command. See #IotMqttPublishInfo_t.qos. */
    uint32_t retryLimit;     /**< @brief Maximum number of retries for the Jobs command. See #IotMqttPublishInfo_t.retryLimit. */
    uint32_t retryMs;        /**< @brief First retry time for the Jobs command. See IotMqttPublishInfo_t.retryMs. */

    /**
     * @brief Function to allocate memory for an incoming response.
     *
     * This only needs to be set if #AWS_IOT_JOBS_FLAG_WAITABLE is passed.
     */
    void * ( *mallocResponse )( size_t );

    /**
     * @brief The Thing Name associated with the Job.
     */
    const char * pThingName;

    /**
     * @brief Length of #AwsIotJobsRequestInfo_t.pThingName.
     */
    size_t thingNameLength;

    /**
     * @brief The Job ID to update.
     *
     * This may be set to #AWS_IOT_JOBS_NEXT_JOB to update the next pending Job.
     * When using #AWS_IOT_JOBS_NEXT_JOB, #AwsIotJobsRequestInfo_t.jobIdLength
     * should be set to #AWS_IOT_JOBS_NEXT_JOB_LENGTH.
     *
     * This parameter is ignored for calls to @ref jobs_function_getpendingasync,
     * @ref jobs_function_getpendingsync, @ref jobs_function_startnextasync,
     * and @ref jobs_function_startnextsync.
     */
    const char * pJobId;

    /**
     * @brief Length of #AwsIotJobsRequestInfo_t.pJobId.
     *
     * This parameter is ignored for calls to @ref jobs_function_getpendingasync,
     * @ref jobs_function_getpendingsync, @ref jobs_function_startnextasync,
     * and @ref jobs_function_startnextsync.
     */
    size_t jobIdLength;

    /**
     * @brief An arbitrary string that identifies this Job update to the Jobs
     * service.
     *
     * The recommended value is #AWS_IOT_JOBS_CLIENT_TOKEN_AUTOGENERATE.
     */
    const char * pClientToken;

    /**
     * @brief Length of #AwsIotJobsRequestInfo_t.pClientToken.
     */
    size_t clientTokenLength;
} AwsIotJobsRequestInfo_t;

/**
 * @ingroup jobs_datatypes_paramstructs
 * @brief Output parameter of blocking Jobs API functions.
 *
 * @paramfor @ref jobs_function_getpendingsync, @ref jobs_function_startnextsync,
 * @ref jobs_function_describesync, @ref jobs_function_updatesync,
 * @ref jobs_function_wait
 *
 * Provides the response received from the Jobs service. The buffer for the
 * response is allocated with #AwsIotJobsRequestInfo_t.mallocResponse.
 *
 * @initializer{AwsIotJobsResponse_t,AWS_IOT_JOBS_RESPONSE_INITIALIZER}
 */
typedef struct AwsIotJobsResponse
{
    const char * pJobsResponse; /**< @brief JSON response received from the Jobs service. */
    size_t jobsResponseLength;  /**< @brief Length of #AwsIotJobsResponse_t.pJobsResponse. */
} AwsIotJobsResponse_t;

/**
 * @ingroup jobs_datatypes_paramstructs
 * @brief Information on a Job update for @ref jobs_function_startnextasync and
 * @ref jobs_function_updateasync. These functions modify a Job's state.
 *
 * @paramfor @ref jobs_function_startnextasync, @ref jobs_function_startnextsync,
 * @ref jobs_function_updateasync, and @ref jobs_function_updatesync.
 *
 * @initializer{AwsIotJobsUpdateInfo_t,AWS_IOT_JOBS_UPDATE_INFO_INITIALIZER}
 */
typedef struct AwsIotJobsUpdateInfo
{
    /**
     * @brief The new status to report as a Job execution update.
     *
     * Valid values are:
     * - #AWS_IOT_JOB_STATE_IN_PROGRESS
     * - #AWS_IOT_JOB_STATE_FAILED
     * - #AWS_IOT_JOB_STATE_SUCCEEDED
     * - #AWS_IOT_JOB_STATE_REJECTED
     *
     * This parameter is ignored for calls to @ref jobs_function_startnextasync and
     * @ref jobs_function_startnextsync. These functions always set the state
     * to #AWS_IOT_JOB_STATE_IN_PROGRESS.
     */
    AwsIotJobState_t newStatus;

    /**
     * @brief The expected current version of job execution.
     *
     * Each time a Job update is sent (for the same `JobId`), the version stored
     * on the AWS IoT Jobs service is updated. If this value does not match the
     * value stored by the Jobs service, the Job update is rejected with the code
     * #AWS_IOT_JOBS_VERSION_MISMATCH.
     *
     * This value is useful for ensuring the order of Job updates, i.e. that the
     * Jobs service does not overwrite a later update with a previous one. If not
     * needed, it can be set to #AWS_IOT_JOBS_NO_VERSION.
     *
     * This parameter is ignored for calls to @ref jobs_function_startnextasync and
     * @ref jobs_function_startnextsync.
     */
    uint32_t expectedVersion;

    /**
     * @brief An application-defined value that identifies a Job execution on a
     * specific device.
     *
     * The Jobs service provides commands for tracking the status of Job execution
     * on a specific target. Therefore, this value is used to provide a unique
     * identifier of a specific Job execution on a specific target.
     *
     * This value is optional. It may be set to #AWS_IOT_JOBS_NO_EXECUTION_NUMBER
     * if not needed.
     *
     * This parameter is ignored for calls to @ref jobs_function_startnextasync and
     * @ref jobs_function_startnextsync.
     */
    int32_t executionNumber;

    /**
     * @brief The amount of time (in minutes) before a new Job update must be reported.
     *
     * If this timeout expires without a new Job update being reported (for the same
     * `jobId`), the Job's status is set to #AWS_IOT_JOB_STATE_TIMED_OUT. Sending a
     * new Job update will reset this step timeout; a value of #AWS_IOT_JOBS_NO_TIMEOUT
     * will clear any previous step timeout.
     *
     * Valid values are between 1 and 10,080 (7 days). This value is optional. It may
     * be set to #AWS_IOT_JOBS_NO_TIMEOUT if not needed.
     */
    int32_t stepTimeoutInMinutes;

    /**
     * @brief Whether the Job response document should contain the `JobExecutionState`.
     *
     * The default value is `false`.
     *
     * This parameter is ignored for calls to @ref jobs_function_startnextasync and
     * @ref jobs_function_startnextsync.
     */
    bool includeJobExecutionState;

    /**
     * @brief Whether the Job response document should contain the `JobDocument`.
     *
     * The default value is `false`.
     *
     * This parameter is ignored for calls to @ref jobs_function_startnextasync and
     * @ref jobs_function_startnextsync.
     */
    bool includeJobDocument;

    /**
     * @brief An application-defined set of JSON name-value pairs that describe
     * the status of Job execution.
     *
     * This value is optional. It may be set to #AWS_IOT_JOBS_NO_STATUS_DETAILS
     * if not needed.
     */
    const char * pStatusDetails;

    /**
     * @brief Length of #AwsIotJobsUpdateInfo_t.pStatusDetails.
     */
    size_t statusDetailsLength;
} AwsIotJobsUpdateInfo_t;

/*------------------------- Jobs defined constants --------------------------*/

/**
 * @brief Set #AwsIotJobsRequestInfo_t.pJobId to this value to use the next pending
 * Job as the Job ID.
 *
 * @note The value of this constant may change at any time in future versions, but
 * its name will remain the same.
 */
#define AWS_IOT_JOBS_NEXT_JOB                     ( "$next" )

/**
 * @brief Length of #AWS_IOT_JOBS_NEXT_JOB.
 *
 * Set #AwsIotJobsRequestInfo_t.jobIdLength to this value when using
 * #AWS_IOT_JOBS_NEXT_JOB.
 *
 * @note The value of this constant may change at any time in future versions, but
 * its name will remain the same.
 */
#define AWS_IOT_JOBS_NEXT_JOB_LENGTH              ( sizeof( AWS_IOT_JOBS_NEXT_JOB ) - 1 )

/**
 * @brief Set #AwsIotJobsRequestInfo_t.pClientToken to this value to automatically
 * generate a client token for the Jobs request.
 *
 * @note The value of this constant may change at any time in future versions, but
 * its name will remain the same.
 */
#define AWS_IOT_JOBS_CLIENT_TOKEN_AUTOGENERATE    ( NULL )

/**
 * @brief Set #AwsIotJobsUpdateInfo_t.expectedVersion to this value to omit the
 * version in the Jobs request.
 *
 * @note The value of this constant may change at any time in future versions, but
 * its name will remain the same.
 */
#define AWS_IOT_JOBS_NO_VERSION                   ( 0 )

/**
 * @brief Set #AwsIotJobsUpdateInfo_t.executionNumber to this value or pass it to
 * @ref jobs_function_describeasync to omit the execution number in the Jobs request.
 *
 * @note The value of this constant may change at any time in future versions, but
 * its name will remain the same.
 */
#define AWS_IOT_JOBS_NO_EXECUTION_NUMBER          ( -1 )

/**
 * @brief Set #AwsIotJobsUpdateInfo_t.stepTimeoutInMinutes to this value to omit the
 * step timeout in the Jobs request.
 *
 * @note The value of this constant may change at any time in future versions, but
 * its name will remain the same.
 */
#define AWS_IOT_JOBS_NO_TIMEOUT                   ( 0 )

/**
 * @brief Set #AwsIotJobsUpdateInfo_t.stepTimeoutInMinutes to this value to cancel
 * any previously set step timeout.
 *
 * The Jobs service will return an (InvalidRequest)[@ref AWS_IOT_JOBS_INVALID_REQUEST]
 * error if this value is used without an existing step timeout.
 *
 * @note The value of this constant may change at any time in future versions, but
 * its name will remain the same.
 */
#define AWS_IOT_JOBS_CANCEL_TIMEOUT               ( -1 )

/**
 * @brief Set #AwsIotJobsUpdateInfo_t.pStatusDetails to this value to omit the
 * status details in the Jobs request.
 *
 * @note The value of this constant may change at any time in future versions, but
 * its name will remain the same.
 */
#define AWS_IOT_JOBS_NO_STATUS_DETAILS            ( NULL )

/**
 * @constantspage{jobs,Jobs library}
 *
 * @section jobs_constants_initializers Jobs Initializers
 * @brief Provides default values for the data types of the Jobs library.
 *
 * @snippet this define_jobs_initializers
 *
 * All user-facing data types of the Jobs library should be initialized
 * using one of the following.
 *
 * @warning Failing to initialize a Jobs data type with the appropriate
 * initializer may result in undefined behavior!
 * @note The initializers may change at any time in future versions, but their
 * names will remain the same.
 *
 * <b>Example</b>
 * @code{c}
 * AwsIotJobsCallbackInfo_t callbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
 * AwsIotJobsRequestInfo_t requestInfo = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;
 * AwsIotJobsUpdateInfo_t updateInfo = AWS_IOT_JOBS_UPDATE_INFO_INITIALIZER;
 * AwsIotJobsOperation_t operation = AWS_IOT_JOBS_OPERATION_INITIALIZER;
 * AwsIotJobsResponse_t response = AWS_IOT_JOBS_RESPONSE_INITIALIZER;
 * @endcode
 *
 * @section jobs_constants_flags Jobs Function Flags
 * @brief Flags that modify the behavior of Jobs library functions.
 *
 * Flags should be bitwise-ORed with each other to change the behavior of
 * Jobs library functions.
 *
 * The following flags are valid for the Jobs operation functions:
 * @ref jobs_function_getpendingasync, @ref jobs_function_startnextasync,
 * @ref jobs_function_describeasync, @ref jobs_function_updateasync,
 * and their blocking versions.
 * - #AWS_IOT_JOBS_FLAG_WAITABLE <br>
 *   @copybrief AWS_IOT_JOBS_FLAG_WAITABLE
 * - #AWS_IOT_JOBS_FLAG_KEEP_SUBSCRIPTIONS <br>
 *   @copybrief AWS_IOT_JOBS_FLAG_KEEP_SUBSCRIPTIONS
 *
 * The following flags are valid for @ref jobs_function_removepersistentsubscriptions.
 * These flags are not valid for the Jobs operation functions.
 * - #AWS_IOT_JOBS_FLAG_REMOVE_GET_PENDING_SUBSCRIPTIONS <br>
 *   @copybrief AWS_IOT_JOBS_FLAG_REMOVE_GET_PENDING_SUBSCRIPTIONS
 * - #AWS_IOT_JOBS_FLAG_REMOVE_START_NEXT_SUBSCRIPTIONS <br>
 *   @copybrief AWS_IOT_JOBS_FLAG_REMOVE_START_NEXT_SUBSCRIPTIONS
 * - #AWS_IOT_JOBS_FLAG_REMOVE_DESCRIBE_SUBSCRIPTIONS <br>
 *   @copybrief AWS_IOT_JOBS_FLAG_REMOVE_DESCRIBE_SUBSCRIPTIONS
 * - #AWS_IOT_JOBS_FLAG_REMOVE_UPDATE_SUBSCRIPTIONS <br>
 *   @copybrief AWS_IOT_JOBS_FLAG_REMOVE_UPDATE_SUBSCRIPTIONS
 *
 * @note The values of the flags may change at any time in future versions, but
 * their names will remain the same. Additionally, flags which may be used at
 * the same time will be bitwise-exclusive of each other.
 */

/* @[define_jobs_initializers] */
#define AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER    { 0 } /**< @brief Initializer for #AwsIotJobsCallbackInfo_t. */
/** @brief Initializer for #AwsIotJobsRequestInfo_t. */
#define AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER \
    { .pClientToken = AWS_IOT_JOBS_CLIENT_TOKEN_AUTOGENERATE }
/** @brief Initializer for #AwsIotJobsUpdateInfo_t. */
#define AWS_IOT_JOBS_UPDATE_INFO_INITIALIZER               \
    { .newStatus = AWS_IOT_JOB_STATE_IN_PROGRESS,          \
      .expectedVersion = AWS_IOT_JOBS_NO_VERSION,          \
      .executionNumber = AWS_IOT_JOBS_NO_EXECUTION_NUMBER, \
      .stepTimeoutInMinutes = AWS_IOT_JOBS_NO_TIMEOUT,     \
      .includeJobExecutionState = false,                   \
      .includeJobDocument = false,                         \
      .pStatusDetails = AWS_IOT_JOBS_NO_STATUS_DETAILS }
#define AWS_IOT_JOBS_OPERATION_INITIALIZER    NULL  /**< @brief Initializer for #AwsIotJobsOperation_t. */
#define AWS_IOT_JOBS_RESPONSE_INITIALIZER     { 0 } /**< @brief Initializer for #AwsIotJobsResponse_t. */
/* @[define_jobs_initializers] */

/**
 * @brief Allows the use of @ref jobs_function_wait for blocking until completion.
 *
 * This flag is only valid if passed to the functions @ref jobs_function_getpendingasync,
 * @ref jobs_function_startnextasync, @ref jobs_function_describeasync, or @ref jobs_function_updateasync.
 *
 * An #AwsIotJobsOperation_t <b>MUST</b> be provided if this flag is set.
 * Additionally, an #AwsIotJobsCallbackInfo_t <b>MUST NOT</b> be provided.
 *
 * When this flag is set, #AwsIotJobsRequestInfo_t.mallocResponse must be set
 * to a function that can be used to allocate memory to hold an incoming response.
 *
 * @note If this flag is set, @ref jobs_function_wait <b>MUST</b> be called to
 * clean up resources.
 */
#define AWS_IOT_JOBS_FLAG_WAITABLE                            ( 0x00000001 )

/**
 * @brief Maintain the subscriptions for the Jobs operation topics, even after
 * this function returns.
 *
 * This flag is only valid if passed to the functions @ref jobs_function_getpendingasync,
 * @ref jobs_function_startnextasync, @ref jobs_function_describeasync, or @ref jobs_function_updateasync,
 * and their blocking versions.
 *
 * The Jobs service reports results of Jobs operations by publishing
 * messages to MQTT topics. By default, the Job operation functions subscribe to the
 * necessary topics, wait for the Jobs service to publish the result of the
 * Jobs operation, then unsubscribe from those topics. This workflow is suitable
 * for infrequent Jobs operations, but is inefficient for frequent, periodic
 * Jobs operations (where subscriptions for the Jobs operation topics would be
 * constantly added and removed).
 *
 * This flag causes the Jobs operation functions to maintain Jobs operation
 * topic subscriptions, even after the function returns. These subscriptions
 * may then be used by a future call to the same function.
 *
 * This flags only needs to be set once, after which subscriptions are maintained
 * and reused for a specific Thing Name and Jobs function. The function @ref
 * jobs_function_removepersistentsubscriptions may be used to remove
 * subscriptions maintained by this flag.
 */
#define AWS_IOT_JOBS_FLAG_KEEP_SUBSCRIPTIONS                  ( 0x00000002 )

/**
 * @brief Remove the persistent subscriptions from a Jobs get pending operation.
 *
 * This flag is only valid if passed to the function @ref
 * jobs_function_removepersistentsubscriptions.
 *
 * This flag may be passed to @ref jobs_function_removepersistentsubscriptions
 * to remove any subscriptions for a specific Thing Name maintained by a previous
 * call to @ref jobs_function_getpendingasync or @ref jobs_function_getpendingsync.
 *
 * @warning Do not call @ref jobs_function_removepersistentsubscriptions with
 * this flag for Thing Names with any in-progress Jobs get pending operations.
 */
#define AWS_IOT_JOBS_FLAG_REMOVE_GET_PENDING_SUBSCRIPTIONS    ( 0x00000001 )

/**
 * @brief Remove the persistent subscriptions from a Jobs start next operation.
 *
 * This flag is only valid if passed to the function @ref
 * jobs_function_removepersistentsubscriptions.
 *
 * This flag may be passed to @ref jobs_function_removepersistentsubscriptions
 * to remove any subscriptions for a specific Thing Name maintained by a previous
 * call to @ref jobs_function_startnextasync or @ref jobs_function_startnextsync.
 *
 * @warning Do not call @ref jobs_function_removepersistentsubscriptions with
 * this flag for Thing Names with any in-progress Jobs start next operations.
 */
#define AWS_IOT_JOBS_FLAG_REMOVE_START_NEXT_SUBSCRIPTIONS     ( 0x00000002 )

/**
 * @brief Remove the persistent subscriptions from a Jobs describe operation.
 *
 * This flag is only valid if passed to the function @ref
 * jobs_function_removepersistentsubscriptions.
 *
 * This flag may be passed to @ref jobs_function_removepersistentsubscriptions
 * to remove any subscriptions for a specific Thing Name maintained by a previous
 * call to @ref jobs_function_describeasync or @ref jobs_function_describesync.
 *
 * @warning Do not call @ref jobs_function_removepersistentsubscriptions with
 * this flag for Thing Names with any in-progress Jobs describe operations.
 */
#define AWS_IOT_JOBS_FLAG_REMOVE_DESCRIBE_SUBSCRIPTIONS       ( 0x00000004 )

/**
 * @brief Remove the persistent subscriptions from a Jobs update operation.
 *
 * This flag is only valid if passed to the function @ref
 * jobs_function_removepersistentsubscriptions.
 *
 * This flag may be passed to @ref jobs_function_removepersistentsubscriptions
 * to remove any subscriptions for a specific Thing Name maintained by a previous
 * call to @ref jobs_function_updateasync or @ref jobs_function_updatesync.
 *
 * @warning Do not call @ref jobs_function_removepersistentsubscriptions with
 * this flag for Thing Names with any in-progress Jobs update operations.
 */
#define AWS_IOT_JOBS_FLAG_REMOVE_UPDATE_SUBSCRIPTIONS         ( 0x00000008 )

#endif /* ifndef AWS_IOT_JOBS_TYPES_H_ */
