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
 * @file aws_iot_jobs.h
 * @brief User-facing functions of the Jobs library.
 */

#ifndef AWS_IOT_JOBS_H_
#define AWS_IOT_JOBS_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Jobs types include. */
#include "types/aws_iot_jobs_types.h"

/*------------------------- Jobs library functions --------------------------*/

/**
 * @functionspage{jobs,Jobs library}
 * - @functionname{jobs_function_init}
 * - @functionname{jobs_function_cleanup}
 * - @functionname{jobs_function_getpendingasync}
 * - @functionname{jobs_function_getpendingsync}
 * - @functionname{jobs_function_startnextasync}
 * - @functionname{jobs_function_startnextsync}
 * - @functionname{jobs_function_describeasync}
 * - @functionname{jobs_function_describesync}
 * - @functionname{jobs_function_updateasync}
 * - @functionname{jobs_function_updatesync}
 * - @functionname{jobs_function_wait}
 * - @functionname{jobs_function_setnotifypendingcallback}
 * - @functionname{jobs_function_setnotifynextcallback}
 * - @functionname{jobs_function_removepersistentsubscriptions}
 * - @functionname{jobs_function_strerror}
 * - @functionname{jobs_function_statename}
 */

/**
 * @functionpage{AwsIotJobs_Init,jobs,init}
 * @functionpage{AwsIotJobs_Cleanup,jobs,cleanup}
 * @functionpage{AwsIotJobs_GetPendingAsync,jobs,getpendingasync}
 * @functionpage{AwsIotJobs_GetPendingSync,jobs,getpendingsync}
 * @functionpage{AwsIotJobs_StartNextAsync,jobs,startnextasync}
 * @functionpage{AwsIotJobs_StartNextSync,jobs,startnextsync}
 * @functionpage{AwsIotJobs_DescribeAsync,jobs,describeasync}
 * @functionpage{AwsIotJobs_DescribeSync,jobs,describesync}
 * @functionpage{AwsIotJobs_UpdateAsync,jobs,updateasync}
 * @functionpage{AwsIotJobs_UpdateSync,jobs,updatesync}
 * @functionpage{AwsIotJobs_Wait,jobs,wait}
 * @functionpage{AwsIotJobs_SetNotifyPendingCallback,jobs,setnotifypendingcallback}
 * @functionpage{AwsIotJobs_SetNotifyNextCallback,jobs,setnotifynextcallback}
 * @functionpage{AwsIotJobs_RemovePersistentSubscriptions,jobs,removepersistentsubscriptions}
 * @functionpage{AwsIotJobs_strerror,jobs,strerror}
 * @functionpage{AwsIotJobs_StateName,jobs,statename}
 */

/**
 * @brief One-time initialization function for the Jobs library.
 *
 * This function performs internal setup of the Jobs library. <b>It must be
 * called once (and only once) before calling any other Jobs function.</b>
 * Calling this function more than once without first calling @ref
 * jobs_function_cleanup may result in a crash.
 *
 * @param[in] mqttTimeoutMs The amount of time (in milliseconds) that the Jobs
 * library will wait for MQTT operations. Optional; set this to `0` to use
 * @ref AWS_IOT_JOBS_DEFAULT_MQTT_TIMEOUT_MS.
 *
 * @return One of the following:
 * - #AWS_IOT_JOBS_SUCCESS
 * - #AWS_IOT_JOBS_INIT_FAILED
 *
 * @warning No thread-safety guarantees are provided for this function.
 *
 * @see @ref jobs_function_cleanup
 */
/* @[declare_jobs_init] */
AwsIotJobsError_t AwsIotJobs_Init( uint32_t mqttTimeoutMs );
/* @[declare_jobs_init] */

/**
 * @brief One-time deinitialization function for the Jobs library.
 *
 * This function frees resources taken in @ref jobs_function_init and deletes
 * any [persistent subscriptions.](@ref AWS_IOT_JOBS_FLAG_KEEP_SUBSCRIPTIONS)
 * It should be called to clean up the Jobs library. After this function returns,
 * @ref jobs_function_init must be called again before calling any other Jobs
 * function.
 *
 * @warning No thread-safety guarantees are provided for this function.
 *
 * @see @ref jobs_function_init
 */
/* @[declare_jobs_cleanup] */
void AwsIotJobs_Cleanup( void );
/* @[declare_jobs_cleanup] */

/**
 * @brief Get the list of all pending jobs for a Thing and receive an asynchronous
 * notification when the response arrives.
 *
 * This function implements the [GetPendingJobExecutions]
 * (https://docs.aws.amazon.com/iot/latest/developerguide/jobs-api.html#mqtt-getpendingjobexecutions)
 * command of the Jobs API, which gets the list of all Jobs for a Thing that are
 * not in a terminal state. The list of retrieved Jobs is returned as the `pResponse`
 * member in #AwsIotJobsCallbackParam_t, or through the #AwsIotJobsResponse_t
 * parameter of @ref jobs_function_wait.
 *
 * @param[in] pRequestInfo Jobs request parameters.
 * @param[in] flags Flags which modify the behavior of the Jobs request. See
 * @ref jobs_constants_flags.
 * @param[in] pCallbackInfo Asynchronous notification of this function's completion.
 * @param[out] pGetPendingOperation Set to a handle by which this operation may be referenced
 * after this function returns. This reference is invalidated once the Jobs operation
 * completes.
 *
 * @return This function will return #AWS_IOT_JOBS_STATUS_PENDING upon successfully
 * queuing the Jobs operation.
 * @return If this function fails before queuing the Jobs operation, it will return one of:
 * - #AWS_IOT_JOBS_NOT_INITIALIZED
 * - #AWS_IOT_JOBS_BAD_PARAMETER
 * - #AWS_IOT_JOBS_NO_MEMORY
 * @return Upon successful completion of the Jobs operation (either through an #AwsIotJobsCallbackInfo_t
 * or @ref jobs_function_wait), the status will be #AWS_IOT_JOBS_SUCCESS.
 * @return Should the Jobs operation fail, the status will be one of:
 * - #AWS_IOT_JOBS_NO_MEMORY (Memory could not be allocated for incoming document)
 * - #AWS_IOT_JOBS_MQTT_ERROR
 * - #AWS_IOT_JOBS_BAD_RESPONSE
 * - A Jobs failure reason between #AWS_IOT_JOBS_INVALID_TOPIC and #AWS_IOT_JOBS_TERMINAL_STATE.
 *
 * @see @ref jobs_function_getpendingsync for a blocking variant of this function.
 *
 * <b>Example</b>
 * @code{c}
 * #define THING_NAME "Test_device"
 * #define THING_NAME_LENGTH ( sizeof( THING_NAME ) - 1 )
 *
 * // Signature of Jobs callback function.
 * void _jobsCallback( void * pCallbackContext, AwsIotJobsCallbackParam_t * pCallbackParam );
 *
 * AwsIotJobsOperation_t getPendingOperation = AWS_IOT_JOBS_OPERATION_INITIALIZER;
 * AwsIotJobsRequestInfo_t requestInfo = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;
 * AwsIotJobsCallbackInfo_t callbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
 *
 * // Set the request info.
 * requestInfo.mqttConnection = _mqttConnection;
 * requestInfo.pThingName = THING_NAME;
 * requestInfo.thingNameLength = THING_NAME_LENGTH;
 *
 * // Set the callback function to invoke.
 * callbackInfo.function = _jobsCallback;
 *
 * // Queue Jobs GET PENDING.
 * AwsIotJobsError_t getPendingResult = AwsIotJobs_GetPendingAsync( &requestInfo,
 *                                                                  0,
 *                                                                  &callbackInfo,
 *                                                                  &getPendingOperation );
 *
 * // GET PENDING should have returned AWS_IOT_JOBS_STATUS_PENDING. The function
 * // _jobsCallback will be invoked once the Jobs response is received.
 * @endcode
 */
/* @[declare_jobs_getpendingasync] */
AwsIotJobsError_t AwsIotJobs_GetPendingAsync( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                              uint32_t flags,
                                              const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                              AwsIotJobsOperation_t * const pGetPendingOperation );
/* @[declare_jobs_getpendingasync] */

/**
 * @brief Get the list of all pending jobs for a Thing with a timeout for receiving
 * the response.
 *
 * This function queues a Jobs GET PENDING, then waits for the result. Internally,
 * this function is a call to @ref jobs_function_getpendingasync followed by
 * @ref jobs_function_wait. See @ref jobs_function_getpendingasync for more information
 * on the Jobs GET PENDING command.
 *
 * @param[in] pRequestInfo Jobs request parameters.
 * @param[in] flags Flags which modify the behavior of the Jobs request. See
 * @ref jobs_constants_flags.
 * @param[in] timeoutMs If a response is not received within this timeout, this
 * function returns #AWS_IOT_JOBS_TIMEOUT.
 * @param[out] pJobsResponse The response received from the Jobs service.
 *
 * @return One of the following:
 * - #AWS_IOT_JOBS_SUCCESS
 * - #AWS_IOT_JOBS_NOT_INITIALIZED
 * - #AWS_IOT_JOBS_BAD_PARAMETER
 * - #AWS_IOT_JOBS_NO_MEMORY
 * - #AWS_IOT_JOBS_MQTT_ERROR
 * - #AWS_IOT_JOBS_BAD_RESPONSE
 * - #AWS_IOT_JOBS_TIMEOUT
 * - A Jobs failure reason between #AWS_IOT_JOBS_INVALID_TOPIC and #AWS_IOT_JOBS_TERMINAL_STATE.
 */
/* @[declare_jobs_getpendingsync] */
AwsIotJobsError_t AwsIotJobs_GetPendingSync( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                             uint32_t flags,
                                             uint32_t timeoutMs,
                                             AwsIotJobsResponse_t * const pJobsResponse );
/* @[declare_jobs_getpendingsync] */

/**
 * @brief Start the next pending job execution for a Thing and receive an asynchronous
 * notification when the response arrives.
 *
 * This function implements the [StartNextPendingJobExecution]
 * (https://docs.aws.amazon.com/iot/latest/developerguide/jobs-api.html#mqtt-startnextpendingjobexecution)
 * command of the Jobs API, which gets and starts the next pending job execution
 * for a Thing.
 *
 * @param[in] pRequestInfo Jobs request parameters.
 * @param[in] pUpdateInfo Jobs update parameters.
 * @param[in] flags Flags which modify the behavior of the Jobs request. See
 * @ref jobs_constants_flags.
 * @param[in] pCallbackInfo Asynchronous notification of this function's completion.
 * @param[out] pStartNextOperation Set to a handle by which this operation may be referenced
 * after this function returns. This reference is invalidated once the Jobs operation
 * completes.
 *
 * @return This function will return #AWS_IOT_JOBS_STATUS_PENDING upon successfully
 * queuing the Jobs operation.
 * @return If this function fails before queuing the Jobs operation, it will return one of:
 * - #AWS_IOT_JOBS_NOT_INITIALIZED
 * - #AWS_IOT_JOBS_BAD_PARAMETER
 * - #AWS_IOT_JOBS_NO_MEMORY
 * @return Upon successful completion of the Jobs operation (either through an #AwsIotJobsCallbackInfo_t
 * or @ref jobs_function_wait), the status will be #AWS_IOT_JOBS_SUCCESS.
 * @return Should the Jobs operation fail, the status will be one of:
 * - #AWS_IOT_JOBS_NO_MEMORY (Memory could not be allocated for incoming document)
 * - #AWS_IOT_JOBS_MQTT_ERROR
 * - #AWS_IOT_JOBS_BAD_RESPONSE
 * - A Jobs failure reason between #AWS_IOT_JOBS_INVALID_TOPIC and #AWS_IOT_JOBS_TERMINAL_STATE.
 *
 * @see @ref jobs_function_startnextsync for a blocking variant of this function.
 *
 * <b>Example</b>
 * @code{c}
 * #define THING_NAME "Test_device"
 * #define THING_NAME_LENGTH ( sizeof( THING_NAME ) - 1 )
 *
 * // Signature of Jobs callback function.
 * void _jobsCallback( void * pCallbackContext, AwsIotJobsCallbackParam_t * pCallbackParam );
 *
 * AwsIotJobsOperation_t startNextOperation = AWS_IOT_JOBS_OPERATION_INITIALIZER;
 * AwsIotJobsRequestInfo_t requestInfo = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;
 * AwsIotJobsUpdateInfo_t updateInfo = AWS_IOT_JOBS_UPDATE_INFO_INITIALIZER;
 * AwsIotJobsCallbackInfo_t callbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
 *
 * // Set the request info. The update info generally does not need to be
 * // changed, as its defaults are suitable.
 * requestInfo.mqttConnection = _mqttConnection;
 * requestInfo.pThingName = THING_NAME;
 * requestInfo.thingNameLength = THING_NAME_LENGTH;
 *
 * // Set the callback function to invoke.
 * callbackInfo.function = _jobsCallback;
 *
 * // Queue Jobs START NEXT.
 * AwsIotJobsError_t startNextResult = AwsIotJobs_StartNextAsync( &requestInfo,
 *                                                                &updateInfo,
 *                                                                0,
 *                                                                &callbackInfo,
 *                                                                &startNextOperation );
 *
 * // START NEXT should have returned AWS_IOT_JOBS_STATUS_PENDING. The function
 * // _jobsCallback will be invoked once the Jobs response is received.
 * @endcode
 */
/* @[declare_jobs_startnextasync] */
AwsIotJobsError_t AwsIotJobs_StartNextAsync( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                             const AwsIotJobsUpdateInfo_t * pUpdateInfo,
                                             uint32_t flags,
                                             const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                             AwsIotJobsOperation_t * const pStartNextOperation );
/* @[declare_jobs_startnextasync] */

/**
 * @brief Start the next pending job execution for a Thing with a timeout for
 * receiving the response.
 *
 * This function queues a Jobs START NEXT, then waits for the result. Internally,
 * this function is a call to @ref jobs_function_startnextasync followed by
 * @ref jobs_function_wait. See @ref jobs_function_startnextasync for more information
 * on the Jobs START NEXT command.
 *
 * @param[in] pRequestInfo Jobs request parameters.
 * @param[in] pUpdateInfo Jobs update parameters.
 * @param[in] flags Flags which modify the behavior of the Jobs request. See
 * @ref jobs_constants_flags.
 * @param[in] timeoutMs If a response is not received within this timeout, this
 * function returns #AWS_IOT_JOBS_TIMEOUT.
 * @param[out] pJobsResponse The response received from the Jobs service.
 *
 * @return One of the following:
 * - #AWS_IOT_JOBS_SUCCESS
 * - #AWS_IOT_JOBS_NOT_INITIALIZED
 * - #AWS_IOT_JOBS_BAD_PARAMETER
 * - #AWS_IOT_JOBS_NO_MEMORY
 * - #AWS_IOT_JOBS_MQTT_ERROR
 * - #AWS_IOT_JOBS_BAD_RESPONSE
 * - #AWS_IOT_JOBS_TIMEOUT
 * - A Jobs failure reason between #AWS_IOT_JOBS_INVALID_TOPIC and #AWS_IOT_JOBS_TERMINAL_STATE.
 */
/* @[declare_jobs_startnextsync] */
AwsIotJobsError_t AwsIotJobs_StartNextSync( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                            const AwsIotJobsUpdateInfo_t * pUpdateInfo,
                                            uint32_t flags,
                                            uint32_t timeoutMs,
                                            AwsIotJobsResponse_t * const pJobsResponse );
/* @[declare_jobs_startnextsync] */

/**
 * @brief Get detailed information about a job execution and receive an asynchronous
 * notification when the response arrives.
 *
 * This function implements the [DescribeJobExecution]
 * (https://docs.aws.amazon.com/iot/latest/developerguide/jobs-api.html#mqtt-describejobexecution)
 * command of the Jobs API, which gets detailed information about a job execution.
 * The description is returned as the `pResponse` member in #AwsIotJobsCallbackParam_t,
 * or through the #AwsIotJobsResponse_t parameter of @ref jobs_function_wait.
 *
 * @param[in] pRequestInfo Jobs request parameters.
 * @param[in] executionNumber The execution number to describe. Optional; pass
 * #AWS_IOT_JOBS_NO_EXECUTION_NUMBER to ignore.
 * @param[in] includeJobDocument Whether the response should include the full
 * Job document.
 * @param[in] flags Flags which modify the behavior of the Jobs request. See
 * @ref jobs_constants_flags.
 * @param[in] pCallbackInfo Asynchronous notification of this function's completion.
 * @param[out] pDescribeOperation Set to a handle by which this operation may be referenced
 * after this function returns. This reference is invalidated once the Jobs operation
 * completes.
 *
 * @return This function will return #AWS_IOT_JOBS_STATUS_PENDING upon successfully
 * queuing the Jobs operation.
 * @return If this function fails before queuing the Jobs operation, it will return one of:
 * - #AWS_IOT_JOBS_NOT_INITIALIZED
 * - #AWS_IOT_JOBS_BAD_PARAMETER
 * - #AWS_IOT_JOBS_NO_MEMORY
 * @return Upon successful completion of the Jobs operation (either through an #AwsIotJobsCallbackInfo_t
 * or @ref jobs_function_wait), the status will be #AWS_IOT_JOBS_SUCCESS.
 * @return Should the Jobs operation fail, the status will be one of:
 * - #AWS_IOT_JOBS_NO_MEMORY (Memory could not be allocated for incoming document)
 * - #AWS_IOT_JOBS_MQTT_ERROR
 * - #AWS_IOT_JOBS_BAD_RESPONSE
 * - A Jobs failure reason between #AWS_IOT_JOBS_INVALID_TOPIC and #AWS_IOT_JOBS_TERMINAL_STATE.
 *
 * @see @ref jobs_function_describesync for a blocking variant of this function.
 *
 * <b>Example</b>
 * @code{c}
 * #define THING_NAME "Test_device"
 * #define THING_NAME_LENGTH ( sizeof( THING_NAME ) - 1 )
 *
 * // Signature of Jobs callback function.
 * void _jobsCallback( void * pCallbackContext, AwsIotJobsCallbackParam_t * pCallbackParam );
 *
 * AwsIotJobsOperation_t describeOperation = AWS_IOT_JOBS_OPERATION_INITIALIZER;
 * AwsIotJobsRequestInfo_t requestInfo = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;
 * AwsIotJobsCallbackInfo_t callbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
 *
 * // Set the request info.
 * requestInfo.mqttConnection = _mqttConnection;
 * requestInfo.pThingName = THING_NAME;
 * requestInfo.thingNameLength = THING_NAME_LENGTH;
 *
 * // Describe the next Job. Or, this may be set to a specific Job ID.
 * requestInfo.pJobId = AWS_IOT_JOBS_NEXT_JOB;
 * requestInfo.jobIdLength = AWS_IOT_JOBS_NEXT_JOB_LENGTH;
 *
 * // Set the callback function to invoke.
 * callbackInfo.function = _jobsCallback;
 *
 * // Queue Jobs DESCRIBE.
 * AwsIotJobsError_t describeResult = AwsIotJobs_DescribeAsync( &requestInfo,
 *                                                              AWS_IOT_JOBS_NO_EXECUTION_NUMBER,
 *                                                              false,
 *                                                              0,
 *                                                              &callbackInfo,
 *                                                              &describeOperation );
 *
 * // DESCRIBE should have returned AWS_IOT_JOBS_STATUS_PENDING. The function
 * // _jobsCallback will be invoked once the Jobs response is received.
 * @endcode
 */
/* @[declare_jobs_describeasync] */
AwsIotJobsError_t AwsIotJobs_DescribeAsync( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                            int32_t executionNumber,
                                            bool includeJobDocument,
                                            uint32_t flags,
                                            const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                            AwsIotJobsOperation_t * const pDescribeOperation );
/* @[declare_jobs_describeasync] */

/**
 * @brief Get detailed information about a job execution with a timeout for receiving
 * the response.
 *
 * This function queues a Jobs DESCRIBE, then waits for the result. Internally,
 * this function is a call to @ref jobs_function_describeasync followed by
 * @ref jobs_function_wait. See @ref jobs_function_describeasync for more information
 * on the Jobs DESCRIBE command.
 *
 * @param[in] pRequestInfo Jobs request parameters.
 * @param[in] executionNumber The execution number to describe. Optional; pass
 * #AWS_IOT_JOBS_NO_EXECUTION_NUMBER to ignore.
 * @param[in] includeJobDocument Whether the response should include the full
 * Job document.
 * @param[in] flags Flags which modify the behavior of the Jobs request. See
 * @ref jobs_constants_flags.
 * @param[in] timeoutMs If a response is not received within this timeout, this
 * function returns #AWS_IOT_JOBS_TIMEOUT.
 * @param[out] pJobsResponse The response received from the Jobs service.
 *
 * @return One of the following:
 * - #AWS_IOT_JOBS_SUCCESS
 * - #AWS_IOT_JOBS_NOT_INITIALIZED
 * - #AWS_IOT_JOBS_BAD_PARAMETER
 * - #AWS_IOT_JOBS_NO_MEMORY
 * - #AWS_IOT_JOBS_MQTT_ERROR
 * - #AWS_IOT_JOBS_BAD_RESPONSE
 * - #AWS_IOT_JOBS_TIMEOUT
 * - A Jobs failure reason between #AWS_IOT_JOBS_INVALID_TOPIC and #AWS_IOT_JOBS_TERMINAL_STATE.
 */
/* @[declare_jobs_describesync] */
AwsIotJobsError_t AwsIotJobs_DescribeSync( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                           int32_t executionNumber,
                                           bool includeJobDocument,
                                           uint32_t flags,
                                           uint32_t timeoutMs,
                                           AwsIotJobsResponse_t * const pJobsResponse );
/* @[declare_jobs_describesync] */

/**
 * @brief Update the status of a job execution and receive an asynchronous
 * notification when the Job update completes.
 *
 * This function implements the [UpdateJobExecution]
 * (https://docs.aws.amazon.com/iot/latest/developerguide/jobs-api.html#mqtt-updatejobexecution)
 * command of the Jobs API, which updates the status of a Job execution.
 *
 * @param[in] pRequestInfo Jobs request parameters.
 * @param[in] pUpdateInfo Jobs update parameters.
 * @param[in] flags Flags which modify the behavior of the Jobs request. See
 * @ref jobs_constants_flags.
 * @param[in] pCallbackInfo Asynchronous notification of this function's completion.
 * @param[out] pUpdateOperation Set to a handle by which this operation may be referenced
 * after this function returns. This reference is invalidated once the Jobs operation
 * completes.
 *
 * @return This function will return #AWS_IOT_JOBS_STATUS_PENDING upon successfully
 * queuing the Jobs operation.
 * @return If this function fails before queuing the Jobs operation, it will return one of:
 * - #AWS_IOT_JOBS_NOT_INITIALIZED
 * - #AWS_IOT_JOBS_BAD_PARAMETER
 * - #AWS_IOT_JOBS_NO_MEMORY
 * @return Upon successful completion of the Jobs operation (either through an #AwsIotJobsCallbackInfo_t
 * or @ref jobs_function_wait), the status will be #AWS_IOT_JOBS_SUCCESS.
 * @return Should the Jobs operation fail, the status will be one of:
 * - #AWS_IOT_JOBS_NO_MEMORY (Memory could not be allocated for incoming document)
 * - #AWS_IOT_JOBS_MQTT_ERROR
 * - #AWS_IOT_JOBS_BAD_RESPONSE
 * - A Jobs failure reason between #AWS_IOT_JOBS_INVALID_TOPIC and #AWS_IOT_JOBS_TERMINAL_STATE.
 *
 * @see @ref jobs_function_updatesync for a blocking variant of this function.
 *
 * <b>Example</b>
 * @code{c}
 * #define THING_NAME "Test_device"
 * #define THING_NAME_LENGTH ( sizeof( THING_NAME ) - 1 )
 *
 * // Signature of Jobs callback function.
 * void _jobsCallback( void * pCallbackContext, AwsIotJobsCallbackParam_t * pCallbackParam );
 *
 * AwsIotJobsOperation_t updateOperation = AWS_IOT_JOBS_OPERATION_INITIALIZER;
 * AwsIotJobsRequestInfo_t requestInfo = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;
 * AwsIotJobsUpdateInfo_t updateInfo = AWS_IOT_JOBS_UPDATE_INFO_INITIALIZER;
 * AwsIotJobsCallbackInfo_t callbackInfo = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
 *
 * // Set the request info.
 * requestInfo.mqttConnection = _mqttConnection;
 * requestInfo.pThingName = THING_NAME;
 * requestInfo.thingNameLength = THING_NAME_LENGTH;
 *
 * // A Job ID must be set. AWS_IOT_JOBS_NEXT_JOB is not valid for UPDATE.
 * requestInfo.pJobId = "job-id";
 * requestInfo.jobIdLength = 6;
 *
 * // Set the update info.
 * updateInfo.newStatus = AWS_IOT_JOB_STATE_SUCCEEDED;
 *
 * // Set the callback function to invoke.
 * callbackInfo.function = _jobsCallback;
 *
 * // Queue Jobs UPDATE.
 * AwsIotJobsError_t updateResult = AwsIotJobs_UpdateAsync( &requestInfo,
 *                                                          &updateInfo,
 *                                                          0,
 *                                                          &callbackInfo,
 *                                                          &updateOperation );
 *
 * // UPDATE should have returned AWS_IOT_JOBS_STATUS_PENDING. The function
 * // _jobsCallback will be invoked once the Jobs response is received.
 * @endcode
 */
/* @[declare_jobs_updateasync] */
AwsIotJobsError_t AwsIotJobs_UpdateAsync( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                          const AwsIotJobsUpdateInfo_t * pUpdateInfo,
                                          uint32_t flags,
                                          const AwsIotJobsCallbackInfo_t * pCallbackInfo,
                                          AwsIotJobsOperation_t * const pUpdateOperation );
/* @[declare_jobs_updateasync] */

/**
 * @brief Update the status of a job execution with a timeout for receiving the
 * response.
 *
 * This function queues a Jobs UPDATE, then waits for the result. Internally,
 * this function is a call to @ref jobs_function_updateasync followed by
 * @ref jobs_function_wait. See @ref jobs_function_updateasync for more information
 * on the Jobs UPDATE command.
 *
 * @param[in] pRequestInfo Jobs request parameters.
 * @param[in] pUpdateInfo Jobs update parameters.
 * @param[in] flags Flags which modify the behavior of the Jobs request. See
 * @ref jobs_constants_flags.
 * @param[in] timeoutMs If a response is not received within this timeout, this
 * function returns #AWS_IOT_JOBS_TIMEOUT.
 * @param[out] pJobsResponse The response received from the Jobs service.
 *
 * @return One of the following:
 * - #AWS_IOT_JOBS_SUCCESS
 * - #AWS_IOT_JOBS_NOT_INITIALIZED
 * - #AWS_IOT_JOBS_BAD_PARAMETER
 * - #AWS_IOT_JOBS_NO_MEMORY
 * - #AWS_IOT_JOBS_MQTT_ERROR
 * - #AWS_IOT_JOBS_BAD_RESPONSE
 * - #AWS_IOT_JOBS_TIMEOUT
 * - A Jobs failure reason between #AWS_IOT_JOBS_INVALID_TOPIC and #AWS_IOT_JOBS_TERMINAL_STATE.
 */
/* @[declare_jobs_updatesync] */
AwsIotJobsError_t AwsIotJobs_UpdateSync( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                         const AwsIotJobsUpdateInfo_t * pUpdateInfo,
                                         uint32_t flags,
                                         uint32_t timeoutMs,
                                         AwsIotJobsResponse_t * const pJobsResponse );
/* @[declare_jobs_updatesync] */

/**
 * @brief Wait for a Jobs operation to complete.
 *
 * This function blocks to wait for a [GET PENDING](@ref jobs_function_getpendingasync),
 * [START NEXT](@ref jobs_function_startnextasync), [DESCRIBE](@ref jobs_function_describeasync),
 * or [UPDATE](@ref jobs_function_updateasync) operation to complete. These operations are
 * by default asynchronous; the function calls queue an operation for processing,
 * and a callback is invoked once the operation is complete.
 *
 * To use this function, the flag #AWS_IOT_JOBS_FLAG_WAITABLE must have been
 * set in the operation's function call. Additionally, this function must always
 * be called with any waitable operation to clean up resources.
 *
 * Regardless of its return value, this function always clean up resources used
 * by the waitable operation. This means `operation` is invalidated as soon as
 * this function returns, even if it returns #AWS_IOT_JOBS_TIMEOUT or another
 * error.
 *
 * @param[in] operation Reference to the Jobs operation to wait for. The flag
 * #AWS_IOT_JOBS_FLAG_WAITABLE must have been set for this operation.
 * @param[in] timeoutMs How long to wait before returning #AWS_IOT_JOBS_TIMEOUT.
 * @param[out] pJobsResponse The response received from the Jobs service.
 *
 * @return One of the following:
 * - #AWS_IOT_JOBS_SUCCESS
 * - #AWS_IOT_JOBS_NOT_INITIALIZED
 * - #AWS_IOT_JOBS_BAD_PARAMETER
 * - #AWS_IOT_JOBS_BAD_RESPONSE
 * - #AWS_IOT_JOBS_TIMEOUT
 * - A Jobs failure reason between #AWS_IOT_JOBS_INVALID_TOPIC and #AWS_IOT_JOBS_TERMINAL_STATE.
 *
 * <b>Example</b>:
 * @code{c}
 * #define THING_NAME "Test_device"
 * #define THING_NAME_LENGTH ( sizeof( THING_NAME ) - 1 )
 *
 * AwsIotJobsOperation_t updateOperation = AWS_IOT_JOBS_OPERATION_INITIALIZER;
 * AwsIotJobsRequestInfo_t requestInfo = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;
 * AwsIotJobsUpdateInfo_t updateInfo = AWS_IOT_JOBS_UPDATE_INFO_INITIALIZER;
 * AwsIotJobsResponse_t jobsResponse = AWS_IOT_JOBS_RESPONSE_INITIALIZER;
 *
 * // Set the request info.
 * requestInfo.mqttConnection = _mqttConnection;
 * requestInfo.pThingName = THING_NAME;
 * requestInfo.thingNameLength = THING_NAME_LENGTH;
 *
 * // Set the function used to allocate memory for an incoming response.
 * requestInfo.mallocResponse = malloc;
 *
 * // A Job ID must be set. AWS_IOT_JOBS_NEXT_JOB is not valid for UPDATE.
 * requestInfo.pJobId = "job-id";
 * requestInfo.jobIdLength = 6;
 *
 * // Set the update info.
 * updateInfo.newStatus = AWS_IOT_JOB_STATE_SUCCEEDED;
 *
 * // Queue Jobs UPDATE.
 * AwsIotJobsError_t updateResult = AwsIotJobs_UpdateAsync( &requestInfo,
 *                                                          &updateInfo,
 *                                                          AWS_IOT_JOBS_FLAG_WAITABLE,
 *                                                          NULL,
 *                                                          &updateOperation );
 *
 * // UPDATE should have returned AWS_IOT_JOBS_STATUS_PENDING. The call to wait
 * // returns once the result of the UPDATE is available or the timeout expires.
 * if( updateResult == AWS_IOT_JOBS_STATUS_PENDING )
 * {
 *     updateResult = AwsIotJobs_Wait( updateOperation, 5000, &jobsResponse );
 *
 *     if( updateResult == AWS_IOT_JOBS_SUCCESS )
 *     {
 *         // Jobs operation succeeded. Do something with the Jobs response.
 *
 *         // Once the Jobs response is no longer needed, free it.
 *         free( jobsResponse.pJobsResponse );
 *     }
 *     else
 *     {
 *         // Jobs operation failed.
 *     }
 * }
 * @endcode
 */
/* @[declare_jobs_wait] */
AwsIotJobsError_t AwsIotJobs_Wait( AwsIotJobsOperation_t operation,
                                   uint32_t timeoutMs,
                                   AwsIotJobsResponse_t * const pJobsResponse );
/* @[declare_jobs_wait] */

/**
 * @brief Set a callback to be invoked when the list of pending Jobs changes.
 *
 * The Jobs service publishes a [JobExecutionsChanged]
 * (https://docs.aws.amazon.com/iot/latest/developerguide/jobs-api.html#mqtt-jobexecutionschanged)
 * message to the `jobs/notify` topic whenever a Job execution is added to or
 * removed from the list of pending Job executions for a Thing. The message sent is
 * useful for monitoring the list of pending Job executions.
 *
 * A <i>NOTIFY PENDING</i> callback may be invoked whenever a message is published
 * to `jobs/notify`. Each Thing may have up to @ref AWS_IOT_JOBS_NOTIFY_CALLBACKS
 * NOTIFY PENDING callbacks set. This function modifies the NOTIFY PENDING callback
 * for a specific Thing depending on the `pNotifyPendingCallback` parameter and the
 * presence of any existing NOTIFY PENDING callback.
 * - When no existing NOTIFY PENDING callback exists for a specific Thing, a new
 * callback is added.
 * - If there is an existing NOTIFY PENDING callback and `pNotifyPendingCallback` is not `NULL`,
 * then the existing callback function and parameter are replaced with `pNotifyPendingCallback`.
 * - If there is an existing NOTIFY PENDING callback and `pNotifyPendingCallback` is `NULL`,
 * then the callback is removed.
 *
 * The member @ref AwsIotJobsCallbackInfo_t.oldFunction must be used to select an
 * already-registered callback function for replacement or removal when @ref
 * AWS_IOT_JOBS_NOTIFY_CALLBACKS is greater than `1`. When multiple callbacks are
 * set, all of them will be invoked when a message is received.
 *
 * @param[in] mqttConnection The MQTT connection to use for the subscription to `jobs/notify`.
 * @param[in] pThingName The subscription to `jobs/notify` will be added for
 * this Thing Name.
 * @param[in] thingNameLength The length of `pThingName`.
 * @param[in] flags This parameter is for future-compatibility. Currently, flags are
 * not supported for this function and this parameter is ignored.
 * @param[in] pNotifyPendingCallback Callback function to invoke for incoming messages.
 *
 * @return One of the following:
 * - #AWS_IOT_JOBS_SUCCESS
 * - #AWS_IOT_JOBS_NOT_INITIALIZED
 * - #AWS_IOT_JOBS_BAD_PARAMETER
 * - #AWS_IOT_JOBS_NO_MEMORY
 * - #AWS_IOT_JOBS_MQTT_ERROR
 * - #AWS_IOT_JOBS_TIMEOUT
 *
 * @see @ref jobs_function_setnotifynextcallback for the function to register callbacks
 * for next Job changes.
 *
 * <b>Example</b>:
 * @code{c}
 * #define THING_NAME "Test_device"
 * #define THING_NAME_LENGTH ( sizeof( THING_NAME ) - 1 )
 *
 * AwsIotJobsError_t result = AWS_IOT_JOBS_STATUS_PENDING;
 * AwsIotJobsCallbackInfo_t notifyPendingCallback = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
 *
 * // _jobsCallback will be invoked when any messages are received.
 * notifyPendingCallback.function = _jobsCallback;
 *
 * // Set the NOTIFY PENDING callback for the Thing "Test_device".
 * result = AwsIotJobs_SetNotifyPendingCallback( mqttConnection,
 *                                               THING_NAME,
 *                                               THING_NAME_LENGTH,
 *                                               0,
 *                                               &notifyPendingCallback );
 *
 * // Check if the callback was successfully set.
 * if( status == AWS_IOT_JOBS_SUCCESS )
 * {
 *     // The callback will now be invoked whenever the list of pending Job
 *     // executions changes.
 *
 *     // Once the callback is no longer needed, it may be removed by passing
 *     // NULL as the callback function and specifying the function to remove.
 *     notifyPendingCallback.function = NULL;
 *     notifyPendingCallback.oldFunction = _jobsCallback;
 *
 *     status = AwsIotJobs_SetNotifyPendingCallback( mqttConnection,
 *                                                   THING_NAME,
 *                                                   THING_NAME_LENGTH,
 *                                                   0,
 *                                                   &notifyPendingCallback );
 *
 *     // The return value from removing a callback should always be success.
 *     assert( status == AWS_IOT_JOBS_SUCCESS );
 * }
 * @endcode
 */
/* @[declare_jobs_setnotifypendingcallback] */
AwsIotJobsError_t AwsIotJobs_SetNotifyPendingCallback( IotMqttConnection_t mqttConnection,
                                                       const char * pThingName,
                                                       size_t thingNameLength,
                                                       uint32_t flags,
                                                       const AwsIotJobsCallbackInfo_t * pNotifyPendingCallback );
/* @[declare_jobs_setnotifypendingcallback] */

/**
 * @brief Set a callback to be invoked when the next pending Job changes.
 *
 * The Jobs service publishes a [NextJobExecutionChanged]
 * (https://docs.aws.amazon.com/iot/latest/developerguide/jobs-api.html#mqtt-nextjobexecutionchanged)
 * message to the `jobs/notify-next` topic whenever the next Job execution in
 * the list of pending Job executions changes for a Thing. The message sent is
 * useful for being notified of changes to the next Job.
 *
 * A <i>NOTIFY NEXT</i> callback may be invoked whenever a message is published
 * to `jobs/notify-next`. Each Thing may have up to @ref AWS_IOT_JOBS_NOTIFY_CALLBACKS
 * NOTIFY NEXT callbacks set.  This function modifies the NOTIFY NEXT callback for
 * a specific Thing depending on the `pNotifyNextCallback` parameter and the presence
 * of any existing NOTIFY NEXT callback.
 * - When no existing NOTIFY NEXT callback exists for a specific Thing, a new
 * callback is added.
 * - If there is an existing NOTIFY NEXT callback and `pNotifyNextCallback` is not `NULL`,
 * then the existing callback function and parameter are replaced with `pNotifyNextCallback`.
 * - If there is an existing NOTIFY NEXT callback and `pNotifyNextCallback` is `NULL`,
 * then the callback is removed.
 *
 * The member @ref AwsIotJobsCallbackInfo_t.oldFunction must be used to select an
 * already-registered callback function for replacement or removal when @ref
 * AWS_IOT_JOBS_NOTIFY_CALLBACKS is greater than `1`. When multiple callbacks are
 * set, all of them will be invoked when a message is received.
 *
 * @param[in] mqttConnection The MQTT connection to use for the subscription to `jobs/notify-next`.
 * @param[in] pThingName The subscription to `jobs/notify-next` will be added for
 * this Thing Name.
 * @param[in] thingNameLength The length of `pThingName`.
 * @param[in] flags This parameter is for future-compatibility. Currently, flags are
 * not supported for this function and this parameter is ignored.
 * @param[in] pNotifyNextCallback Callback function to invoke for incoming messages.
 *
 * @return One of the following:
 * - #AWS_IOT_JOBS_SUCCESS
 * - #AWS_IOT_JOBS_NOT_INITIALIZED
 * - #AWS_IOT_JOBS_BAD_PARAMETER
 * - #AWS_IOT_JOBS_NO_MEMORY
 * - #AWS_IOT_JOBS_MQTT_ERROR
 * - #AWS_IOT_JOBS_TIMEOUT
 *
 * @see @ref jobs_function_setnotifypendingcallback for the function to register callbacks
 * for all pending Job changes.
 *
 * <b>Example</b>:
 * @code{c}
 * #define THING_NAME "Test_device"
 * #define THING_NAME_LENGTH ( sizeof( THING_NAME ) - 1 )
 *
 * AwsIotJobsError_t result = AWS_IOT_JOBS_STATUS_PENDING;
 * AwsIotJobsCallbackInfo_t notifyNextCallback = AWS_IOT_JOBS_CALLBACK_INFO_INITIALIZER;
 *
 * // _jobsCallback will be invoked when any messages are received.
 * notifyNextCallback.function = _jobsCallback;
 *
 * // Set the NOTIFY NEXT callback for the Thing "Test_device".
 * result = AwsIotJobs_SetNotifyNextCallback( mqttConnection,
 *                                            THING_NAME,
 *                                            THING_NAME_LENGTH,
 *                                            0,
 *                                            &notifyNextCallback );
 *
 * // Check if the callback was successfully set.
 * if( status == AWS_IOT_JOBS_SUCCESS )
 * {
 *     // The callback will now be invoked whenever the next pending Job
 *     // execution changes.
 *
 *     // Once the callback is no longer needed, it may be removed by passing
 *     // NULL as the callback function and specifying the function to remove.
 *     notifyNextCallback.function = NULL;
 *     notifyNextCallback.oldFunction = _jobsCallback;
 *
 *     status = AwsIotJobs_SetNotifyNextCallback( mqttConnection,
 *                                                THING_NAME,
 *                                                THING_NAME_LENGTH,
 *                                                0,
 *                                                &notifyNextCallback );
 *
 *     // The return value from removing a callback should always be success.
 *     assert( status == AWS_IOT_JOBS_SUCCESS );
 * }
 * @endcode
 */
/* @[declare_jobs_setnotifynextcallback] */
AwsIotJobsError_t AwsIotJobs_SetNotifyNextCallback( IotMqttConnection_t mqttConnection,
                                                    const char * pThingName,
                                                    size_t thingNameLength,
                                                    uint32_t flags,
                                                    const AwsIotJobsCallbackInfo_t * pNotifyNextCallback );
/* @[declare_jobs_setnotifynextcallback] */

/**
 * @brief Remove persistent Jobs operation topic subscriptions.
 *
 * Passing the flag @ref AWS_IOT_JOBS_FLAG_KEEP_SUBSCRIPTIONS to @ref jobs_function_getpendingasync,
 * @ref jobs_function_startnextasync, @ref jobs_function_describeasync, @ref jobs_function_updateasync,
 * or their blocking versions causes the Jobs operation topic subscriptions to be
 * maintained for future calls to the same function. If a persistent subscription for a
 * Jobs topic are no longer needed, this function may be used to remove it.
 *
 * @param[in] pRequestInfo Jobs request info. Only the [pThingName]
 * (@ref #AwsIotJobsRequestInfo_t.pThingName), [thingNameLength]
 * (@ref #AwsIotJobsRequestInfo_t.thingNameLength), and [mqttConnection]
 * (@ref #AwsIotJobsRequestInfo_t.mqttConnection) members need to be set for this
 * function.
 * @param[in] flags Flags that determine which subscriptions to remove. Valid values are
 * the bitwise OR of the following individual flags:
 * - @ref AWS_IOT_JOBS_FLAG_REMOVE_GET_PENDING_SUBSCRIPTIONS
 * - @ref AWS_IOT_JOBS_FLAG_REMOVE_START_NEXT_SUBSCRIPTIONS
 * - @ref AWS_IOT_JOBS_FLAG_REMOVE_DESCRIBE_SUBSCRIPTIONS
 * - @ref AWS_IOT_JOBS_FLAG_REMOVE_UPDATE_SUBSCRIPTIONS
 *
 * @return On success:
 * - #AWS_IOT_JOBS_SUCCESS
 * @return If an MQTT UNSUBSCRIBE packet cannot be sent, one of the following:
 * - #AWS_IOT_JOBS_NO_MEMORY
 * - #AWS_IOT_JOBS_MQTT_ERROR
 *
 * @note @ref jobs_function_cleanup removes persistent sessions as well.
 *
 * @warning This function is not safe to call with any in-progress operations!
 * It also does not affect NOTIFY PENDING and NOTIFY NEXT callbacks registered
 * with @ref jobs_function_setnotifypendingcallback and
 * @ref jobs_function_setnotifynextcallback, respectively. (See documentation for
 * those functions on how to remove their callbacks).
 */
/* @[declare_jobs_removepersistentsubscriptions] */
AwsIotJobsError_t AwsIotJobs_RemovePersistentSubscriptions( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                                            uint32_t flags );
/* @[declare_jobs_removepersistentsubscriptions] */

/*-------------------------- Jobs helper functions --------------------------*/

/**
 * @brief Returns a string that describes an #AwsIotJobsError_t.
 *
 * Like POSIX's `strerror`, this function returns a string describing a return
 * code. In this case, the return code is a Jobs library error code, `status`.
 *
 * The string returned by this function <b>MUST</b> be treated as read-only: any
 * attempt to modify its contents may result in a crash. Therefore, this function
 * is limited to usage in logging.
 *
 * @param[in] status The status to describe.
 *
 * @return A read-only string that describes `status`.
 *
 * @warning The string returned by this function must never be modified.
 */
/* @[declare_jobs_strerror] */
const char * AwsIotJobs_strerror( AwsIotJobsError_t status );
/* @[declare_jobs_strerror] */

/**
 * @brief Returns a string that describes an #AwsIotJobState_t.
 *
 * This function returns a string describing a Job state, `state`.
 *
 * The string returned by this function <b>MUST</b> be treated as read-only: any
 * attempt to modify its contents may result in a crash. Therefore, this function
 * is limited to usage in logging.
 *
 * @param[in] state The job state to describe.
 *
 * @return A read-only string that describes `state`.
 *
 * @warning The string returned by this function must never be modified.
 */
/* @[declare_jobs_statename] */
const char * AwsIotJobs_StateName( AwsIotJobState_t state );
/* @[declare_jobs_statename] */

#endif /* ifndef AWS_IOT_JOBS_H_ */
