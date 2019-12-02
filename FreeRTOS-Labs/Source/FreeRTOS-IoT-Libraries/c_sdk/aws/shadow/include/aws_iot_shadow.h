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
 * @file aws_iot_shadow.h
 * @brief User-facing functions of the Shadow library.
 */

#ifndef AWS_IOT_SHADOW_H_
#define AWS_IOT_SHADOW_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Shadow types include. */
#include "types/aws_iot_shadow_types.h"

/*------------------------ Shadow library functions -------------------------*/

/**
 * @functionspage{shadow,Shadow library}
 * - @functionname{shadow_function_init}
 * - @functionname{shadow_function_cleanup}
 * - @functionname{shadow_function_deleteasync}
 * - @functionname{shadow_function_deletesync}
 * - @functionname{shadow_function_getasync}
 * - @functionname{shadow_function_getsync}
 * - @functionname{shadow_function_updateasync}
 * - @functionname{shadow_function_updatesync}
 * - @functionname{shadow_function_wait}
 * - @functionname{shadow_function_setdeltacallback}
 * - @functionname{shadow_function_setupdatedcallback}
 * - @functionname{shadow_function_removepersistentsubscriptions}
 * - @functionname{shadow_function_strerror}
 */

/**
 * @functionpage{AwsIotShadow_Init,shadow,init}
 * @functionpage{AwsIotShadow_Cleanup,shadow,cleanup}
 * @functionpage{AwsIotShadow_DeleteAsync,shadow,deleteasync}
 * @functionpage{AwsIotShadow_DeleteSync,shadow,deletesync}
 * @functionpage{AwsIotShadow_GetAsync,shadow,getasync}
 * @functionpage{AwsIotShadow_GetSync,shadow,getsync}
 * @functionpage{AwsIotShadow_UpdateAsync,shadow,updateasync}
 * @functionpage{AwsIotShadow_UpdateSync,shadow,updatesync}
 * @functionpage{AwsIotShadow_Wait,shadow,wait}
 * @functionpage{AwsIotShadow_SetDeltaCallback,shadow,setdeltacallback}
 * @functionpage{AwsIotShadow_SetUpdatedCallback,shadow,setupdatedcallback}
 * @functionpage{AwsIotShadow_RemovePersistentSubscriptions,shadow,removepersistentsubscriptions}
 * @functionpage{AwsIotShadow_strerror,shadow,strerror}
 */

/**
 * @brief One-time initialization function for the Shadow library.
 *
 * This function performs internal setup of the Shadow library. <b>It must be
 * called once (and only once) before calling any other Shadow function.</b>
 * Calling this function more than once without first calling @ref
 * shadow_function_cleanup may result in a crash.
 *
 * @param[in] mqttTimeout The amount of time (in milliseconds) that the Shadow
 * library will wait for MQTT operations. Optional; set this to `0` to use
 * @ref AWS_IOT_SHADOW_DEFAULT_MQTT_TIMEOUT_MS.
 *
 * @return One of the following:
 * - #AWS_IOT_SHADOW_SUCCESS
 * - #AWS_IOT_SHADOW_INIT_FAILED
 *
 * @warning No thread-safety guarantees are provided for this function.
 *
 * @see @ref shadow_function_cleanup
 */
/* @[declare_shadow_init] */
AwsIotShadowError_t AwsIotShadow_Init( uint32_t mqttTimeout );
/* @[declare_shadow_init] */

/**
 * @brief One-time deinitialization function for the Shadow library.
 *
 * This function frees resources taken in @ref shadow_function_init and deletes
 * any [persistent subscriptions.](@ref AWS_IOT_SHADOW_FLAG_KEEP_SUBSCRIPTIONS)
 * It should be called to clean up the Shadow library. After this function returns,
 * @ref shadow_function_init must be called again before calling any other Shadow
 * function.
 *
 * @warning No thread-safety guarantees are provided for this function.
 *
 * @see @ref shadow_function_init
 */
/* @[declare_shadow_cleanup] */
void AwsIotShadow_Cleanup( void );
/* @[declare_shadow_cleanup] */

/**
 * @brief Delete a Thing Shadow and receive an asynchronous notification when
 * the Delete completes.
 *
 * This function deletes any existing Shadow document for the given Thing Name.
 * If the given Thing has no Shadow and this function is called, the result will
 * be #AWS_IOT_SHADOW_NOT_FOUND.
 *
 * Deleting a Shadow involves sending an MQTT message to AWS IoT and waiting on
 * a response. This message will always be sent at [MQTT QoS 0](@ref #IOT_MQTT_QOS_0).
 *
 * @param[in] mqttConnection The MQTT connection to use for Shadow delete.
 * @param[in] pThingName The Thing Name associated with the Shadow to delete.
 * @param[in] thingNameLength The length of `pThingName`.
 * @param[in] flags Flags which modify the behavior of this function. See @ref shadow_constants_flags.
 * @param[in] pCallbackInfo Asynchronous notification of this function's completion.
 * @param[out] pDeleteOperation Set to a handle by which this operation may be referenced
 * after this function returns. This reference is invalidated once the Shadow delete
 * completes.
 *
 * @return This function will return #AWS_IOT_SHADOW_STATUS_PENDING upon successfully
 * queuing a Shadow delete.
 * @return If this function fails before queuing a Shadow delete, it will return one of:
 * - #AWS_IOT_SHADOW_NOT_INITIALIZED
 * - #AWS_IOT_SHADOW_BAD_PARAMETER
 * - #AWS_IOT_SHADOW_NO_MEMORY
 * @return Upon successful completion of the Shadow delete (either through an #AwsIotShadowCallbackInfo_t
 * or #AwsIotShadow_Wait), the status will be #AWS_IOT_SHADOW_SUCCESS.
 * @return Should the Shadow delete fail, the status will be one of:
 * - #AWS_IOT_SHADOW_MQTT_ERROR
 * - #AWS_IOT_SHADOW_BAD_RESPONSE
 * - A Shadow service rejection reason between 400 (#AWS_IOT_SHADOW_BAD_REQUEST)
 * and 500 (#AWS_IOT_SHADOW_SERVER_ERROR)
 *
 * @see @ref shadow_function_deletesync for a blocking variant of this function.
 *
 * <b>Example</b>
 * @code{c}
 * #define THING_NAME "Test_device"
 * #define THING_NAME_LENGTH ( sizeof( THING_NAME ) - 1 )
 *
 * // Shadow operation handle.
 * AwsIotShadowOperation_t deleteOperation = AWS_IOT_SHADOW_OPERATION_INITIALIZER;
 *
 * // Queue a Shadow delete.
 * AwsIotShadowError_t deleteResult = AwsIotShadow_DeleteAsync( mqttConnection,
 *                                                              THING_NAME,
 *                                                              THING_NAME_LENGTH,
 *                                                              AWS_IOT_SHADOW_FLAG_WAITABLE,
 *                                                              NULL,
 *                                                              &deleteOperation );
 *
 * // Shadow delete should return AWS_IOT_SHADOW_STATUS_PENDING upon success.
 * if( deleteResult == AWS_IOT_SHADOW_STATUS_PENDING )
 * {
 *     // Wait for the Shadow delete to complete.
 *     deleteResult = AwsIotShadow_Wait( deleteOperation, 5000 );
 *
 *     // Delete result should be AWS_IOT_SHADOW_SUCCESS upon successfully
 *     // deleting an existing Shadow.
 * }
 * @endcode
 */
/* @[declare_shadow_deleteasync] */
AwsIotShadowError_t AwsIotShadow_DeleteAsync( IotMqttConnection_t mqttConnection,
                                              const char * pThingName,
                                              size_t thingNameLength,
                                              uint32_t flags,
                                              const AwsIotShadowCallbackInfo_t * pCallbackInfo,
                                              AwsIotShadowOperation_t * const pDeleteOperation );
/* @[declare_shadow_deleteasync] */

/**
 * @brief Delete a Thing Shadow with a timeout.
 *
 * This function queues a Shadow delete, then waits for the result. Internally, this
 * function is a call to @ref shadow_function_deleteasync followed by @ref shadow_function_wait.
 * See @ref shadow_function_deleteasync for more information on the Shadow delete operation.
 *
 * @param[in] mqttConnection The MQTT connection to use for Shadow delete.
 * @param[in] pThingName The Thing Name associated with the Shadow to delete.
 * @param[in] thingNameLength The length of `pThingName`.
 * @param[in] flags Flags which modify the behavior of this function. See @ref shadow_constants_flags.
 * @param[in] timeoutMs If the Shadow service does not respond to the Shadow delete
 * within this timeout, this function returns #AWS_IOT_SHADOW_TIMEOUT.
 *
 * @return One of the following:
 * - #AWS_IOT_SHADOW_SUCCESS
 * - #AWS_IOT_SHADOW_NOT_INITIALIZED
 * - #AWS_IOT_SHADOW_BAD_PARAMETER
 * - #AWS_IOT_SHADOW_NO_MEMORY
 * - #AWS_IOT_SHADOW_MQTT_ERROR
 * - #AWS_IOT_SHADOW_BAD_RESPONSE
 * - #AWS_IOT_SHADOW_TIMEOUT
 * - A Shadow service rejection reason between 400 (#AWS_IOT_SHADOW_BAD_REQUEST)
 * and 500 (#AWS_IOT_SHADOW_SERVER_ERROR)
 */
/* @[declare_shadow_deletesync] */
AwsIotShadowError_t AwsIotShadow_DeleteSync( IotMqttConnection_t mqttConnection,
                                             const char * pThingName,
                                             size_t thingNameLength,
                                             uint32_t flags,
                                             uint32_t timeoutMs );
/* @[declare_shadow_deletesync] */

/**
 * @brief Retrieve a Thing Shadow and receive an asynchronous notification when
 * the Shadow document is received.
 *
 * This function retrieves the Thing Shadow document currently stored by the
 * Shadow service. If a given Thing has no Shadow and this function is called,
 * the result will be #AWS_IOT_SHADOW_NOT_FOUND.
 *
 * Shadow documents may be large, and their size is not known beforehand.
 * Therefore, this function works best when memory is dynamically allocated.
 * Because the Shadow document is retrieved in an MQTT PUBLISH packet, the MQTT
 * library will allocate a buffer for the Shadow document using #IotMqtt_MallocMessage.
 *
 * The MQTT library may free the buffer for a retrieved Shadow document as soon
 * as the [Shadow completion callback](@ref AwsIotShadowCallbackInfo_t) returns.
 * Therefore, any data needed later must be copied from the Shadow document.
 * Similarly, if the flag #AWS_IOT_SHADOW_FLAG_WAITABLE is given to this function
 * (which indicates that the Shadow document will be needed after the Shadow
 * operation completes), #AwsIotShadowDocumentInfo_t.mallocDocument must be
 * provided to allocate a longer-lasting buffer.
 *
 * @note Because of the potentially large size of complete Shadow documents, it is more
 * memory-efficient for most applications to use [delta callbacks]
 * (@ref shadow_function_setdeltacallback) to retrieve Shadows from
 * the Shadow service.
 *
 * @param[in] mqttConnection The MQTT connection to use for Shadow get.
 * @param[in] pGetInfo Shadow document parameters.
 * @param[in] flags Flags which modify the behavior of this function. See @ref shadow_constants_flags.
 * @param[in] pCallbackInfo Asynchronous notification of this function's completion.
 * @param[out] pGetOperation Set to a handle by which this operation may be referenced
 * after this function returns. This reference is invalidated once the Shadow get
 * completes.
 *
 * @return This function will return #AWS_IOT_SHADOW_STATUS_PENDING upon successfully
 * queuing a Shadow get.
 * @return If this function fails before queuing a Shadow get, it will return one of:
 * - #AWS_IOT_SHADOW_NOT_INITIALIZED
 * - #AWS_IOT_SHADOW_BAD_PARAMETER
 * - #AWS_IOT_SHADOW_NO_MEMORY
 * @return Upon successful completion of the Shadow get (either through an #AwsIotShadowCallbackInfo_t
 * or #AwsIotShadow_Wait), the status will be #AWS_IOT_SHADOW_SUCCESS.
 * @return Should the Shadow get fail, the status will be one of:
 * - #AWS_IOT_SHADOW_NO_MEMORY (Memory could not be allocated for incoming document)
 * - #AWS_IOT_SHADOW_MQTT_ERROR
 * - #AWS_IOT_SHADOW_BAD_RESPONSE
 * - A Shadow service rejection reason between 400 (#AWS_IOT_SHADOW_BAD_REQUEST)
 * and 500 (#AWS_IOT_SHADOW_SERVER_ERROR)
 *
 * @see @ref shadow_function_getsync for a blocking variant of this function.
 *
 * <b>Example</b>
 * @code{c}
 * // Shadow get completion callback. The retrieved document will be in
 * // pCallbackParam. Any data in the retrieved document needed after this
 * // function returns must be copied.
 * void _processRetrievedDocument( void * pCallbackContext,
 *                                 AwsIotShadowCallbackParam_t * pCallbackParam );
 *
 * // Parameters and return value of Shadow get.
 * AwsIotShadowError_t result = AWS_IOT_SHADOW_STATUS_PENDING;
 * AwsIotShadowDocumentInfo_t getInfo = { ... };
 * uint32_t timeout = 5000; // 5 seconds
 *
 * // Callback for get completion.
 * AwsIotShadowCallbackInfo_t getCallback = AWS_IOT_SHADOW_CALLBACK_INFO_INITIALIZER;
 * getCallback.function = _processRetrievedDocument;
 *
 * // Shadow get operation.
 * result = AwsIotShadow_GetAsync( mqttConnection,
 *                                 &getInfo,
 *                                 0,
 *                                 &getCallback,
 *                                 NULL );
 *
 * // Get should have returned AWS_IOT_SHADOW_STATUS_PENDING. The function
 * // _processRetrievedDocument will be invoked once the Shadow get completes.
 * @endcode
 *
 * See @ref shadow_function_wait <b>Example 2</b> for an example of using this
 * function with #AWS_IOT_SHADOW_FLAG_WAITABLE and @ref shadow_function_wait.
 */
/* @[declare_shadow_getasync] */
AwsIotShadowError_t AwsIotShadow_GetAsync( IotMqttConnection_t mqttConnection,
                                           const AwsIotShadowDocumentInfo_t * pGetInfo,
                                           uint32_t flags,
                                           const AwsIotShadowCallbackInfo_t * pCallbackInfo,
                                           AwsIotShadowOperation_t * const pGetOperation );
/* @[declare_shadow_getasync] */

/**
 * @brief Retrieve a Thing Shadow with a timeout.
 *
 * This function queues a Shadow get, then waits for the result. Internally, this
 * function is a call to @ref shadow_function_getasync followed by @ref shadow_function_wait.
 * See @ref shadow_function_getasync for more information on the Shadow get operation.
 *
 * @param[in] mqttConnection The MQTT connection to use for Shadow get.
 * @param[in] pGetInfo Shadow document parameters.
 * @param[in] flags Flags which modify the behavior of this function. See @ref shadow_constants_flags.
 * @param[in] timeoutMs If the Shadow service does not respond to the Shadow get
 * within this timeout, this function returns #AWS_IOT_SHADOW_TIMEOUT.
 * @param[out] pShadowDocument A pointer to a buffer containing the Shadow document
 * retrieved by a Shadow get is placed here. The buffer was allocated with the function
 * `pGetInfo->get.mallocDocument`. This output parameter is only valid if this function
 * returns #AWS_IOT_SHADOW_SUCCESS.
 * @param[out] pShadowDocumentLength The length of the Shadow document in
 * `pShadowDocument` is placed here. This output parameter is only valid if this function
 * returns #AWS_IOT_SHADOW_SUCCESS.
 *
 * @return One of the following:
 * - #AWS_IOT_SHADOW_SUCCESS
 * - #AWS_IOT_SHADOW_NOT_INITIALIZED
 * - #AWS_IOT_SHADOW_BAD_PARAMETER
 * - #AWS_IOT_SHADOW_NO_MEMORY
 * - #AWS_IOT_SHADOW_MQTT_ERROR
 * - #AWS_IOT_SHADOW_BAD_RESPONSE
 * - #AWS_IOT_SHADOW_TIMEOUT
 * - A Shadow service rejection reason between 400 (#AWS_IOT_SHADOW_BAD_REQUEST)
 * and 500 (#AWS_IOT_SHADOW_SERVER_ERROR)
 */
/* @[declare_shadow_getsync] */
AwsIotShadowError_t AwsIotShadow_GetSync( IotMqttConnection_t mqttConnection,
                                          const AwsIotShadowDocumentInfo_t * pGetInfo,
                                          uint32_t flags,
                                          uint32_t timeoutMs,
                                          const char ** const pShadowDocument,
                                          size_t * const pShadowDocumentLength );
/* @[declare_shadow_getsync] */

/**
 * @brief Send a Thing Shadow update and receive an asynchronous notification when
 * the Shadow Update completes.
 *
 * This function modifies the Thing Shadow document stored by the Shadow service.
 * If a given Thing has no Shadow and this function is called, then a new Shadow
 * is created.
 *
 * New JSON keys in the Shadow document will be appended. For example, if the Shadow service
 * currently has a document containing key `example1` and this function sends a document
 * only containing key `example2`, then the resulting document in the Shadow service
 * will contain both `example1` and `example2`.
 *
 * Existing JSON keys in the Shadow document will be replaced. For example, if the Shadow
 * service currently has a document containing `"example1": [0,1,2]` and this function sends
 * a document containing key `"example1": [1,2,3]`, then the resulting document in the Shadow
 * service will contain `"example1": [1,2,3]`.
 *
 * Successful Shadow updates will trigger the [Shadow updated callback]
 * (@ref shadow_function_setupdatedcallback). If the resulting Shadow document contains
 * different `desired` and `reported` keys, then the [Shadow delta callback]
 * (@ref shadow_function_setdeltacallback) will be triggered as well.
 *
 * @attention All documents passed to this function must contain a `clientToken`.
 * The [client token]
 * (https://docs.aws.amazon.com/iot/latest/developerguide/device-shadow-document.html#client-token)
 * is a string used to distinguish between Shadow updates. They are limited to 64
 * characters; attempting to use a client token longer than 64 characters will
 * cause the Shadow update to fail. They must be unique at any given time, i.e.
 * they may be reused <i>as long as no two Shadow updates are using the same
 * client token at the same time</i>.
 *
 * @param[in] mqttConnection The MQTT connection to use for Shadow update.
 * @param[in] pUpdateInfo Shadow document parameters.
 * @param[in] flags Flags which modify the behavior of this function. See @ref shadow_constants_flags.
 * @param[in] pCallbackInfo Asynchronous notification of this function's completion.
 * @param[out] pUpdateOperation Set to a handle by which this operation may be referenced
 * after this function returns. This reference is invalidated once the Shadow update
 * completes.
 *
 * @return This function will return #AWS_IOT_SHADOW_STATUS_PENDING upon successfully
 * queuing a Shadow update.
 * @return If this function fails before queuing a Shadow update, it will return one of:
 * - #AWS_IOT_SHADOW_NOT_INITIALIZED
 * - #AWS_IOT_SHADOW_BAD_PARAMETER
 * - #AWS_IOT_SHADOW_NO_MEMORY
 * @return Upon successful completion of the Shadow update (either through an #AwsIotShadowCallbackInfo_t
 * or #AwsIotShadow_Wait), the status will be #AWS_IOT_SHADOW_SUCCESS.
 * @return Should the Shadow update fail, the status will be one of:
 * - #AWS_IOT_SHADOW_MQTT_ERROR
 * - #AWS_IOT_SHADOW_BAD_RESPONSE
 * - A Shadow service rejection reason between 400 (#AWS_IOT_SHADOW_BAD_REQUEST)
 * and 500 (#AWS_IOT_SHADOW_SERVER_ERROR)
 *
 * @see @ref shadow_function_updatesync for a blocking variant of this function.
 *
 * <b>Example</b>
 * @code{c}
 * // Shadow update completion callback.
 * void _updateComplete( void * pCallbackContext,
 *                       AwsIotShadowCallbackParam_t * pCallbackParam );
 *
 * // Parameters and return value of Shadow update.
 * AwsIotShadowError_t result = AWS_IOT_SHADOW_STATUS_PENDING;
 * AwsIotShadowDocumentInfo_t updateInfo = { ... };
 * uint32_t timeout = 5000; // 5 seconds
 *
 * // Set Shadow document to send.
 * updateInfo.update.pUpdateDocument = "{...}"; // Must contain clientToken
 * updateInfo.update.updateDocumentLength = strlen( updateInfo.update.pUpdateDocument );
 *
 * // Callback for update completion.
 * AwsIotShadowCallbackInfo_t updateCallback = AWS_IOT_SHADOW_CALLBACK_INFO_INITIALIZER;
 * updateCallback.function = _updateComplete;
 *
 * // Shadow update operation.
 * result = AwsIotShadow_UpdateAsync( mqttConnection,
 *                                    &updateInfo,
 *                                    0,
 *                                    &updateCallback,
 *                                    NULL );
 *
 * // Update should have returned AWS_IOT_SHADOW_STATUS_PENDING. The function
 * // _updateComplete will be invoked once the Shadow update completes.
 * @endcode
 *
 * See @ref shadow_function_wait <b>Example 1</b> for an example of using this
 * function with #AWS_IOT_SHADOW_FLAG_WAITABLE and @ref shadow_function_wait.
 */
/* @[declare_shadow_updateasync] */
AwsIotShadowError_t AwsIotShadow_UpdateAsync( IotMqttConnection_t mqttConnection,
                                              const AwsIotShadowDocumentInfo_t * pUpdateInfo,
                                              uint32_t flags,
                                              const AwsIotShadowCallbackInfo_t * pCallbackInfo,
                                              AwsIotShadowOperation_t * const pUpdateOperation );
/* @[declare_shadow_updateasync] */

/**
 * @brief Send a Thing Shadow update with a timeout.
 *
 * This function queues a Shadow update, then waits for the result. Internally, this
 * function is a call to @ref shadow_function_updateasync followed by @ref shadow_function_wait.
 * See @ref shadow_function_updateasync for more information on the Shadow update operation.
 *
 * @param[in] mqttConnection The MQTT connection to use for Shadow update.
 * @param[in] pUpdateInfo Shadow document parameters.
 * @param[in] flags Flags which modify the behavior of this function. See @ref shadow_constants_flags.
 * @param[in] timeoutMs If the Shadow service does not respond to the Shadow update
 * within this timeout, this function returns #AWS_IOT_SHADOW_TIMEOUT.
 *
 * @return One of the following:
 * - #AWS_IOT_SHADOW_SUCCESS
 * - #AWS_IOT_SHADOW_NOT_INITIALIZED
 * - #AWS_IOT_SHADOW_BAD_PARAMETER
 * - #AWS_IOT_SHADOW_NO_MEMORY
 * - #AWS_IOT_SHADOW_MQTT_ERROR
 * - #AWS_IOT_SHADOW_BAD_RESPONSE
 * - #AWS_IOT_SHADOW_TIMEOUT
 * - A Shadow service rejection reason between 400 (#AWS_IOT_SHADOW_BAD_REQUEST)
 * and 500 (#AWS_IOT_SHADOW_SERVER_ERROR)
 */
/* @[declare_shadow_updatesync] */
AwsIotShadowError_t AwsIotShadow_UpdateSync( IotMqttConnection_t mqttConnection,
                                             const AwsIotShadowDocumentInfo_t * pUpdateInfo,
                                             uint32_t flags,
                                             uint32_t timeoutMs );
/* @[declare_shadow_updatesync] */

/**
 * @brief Wait for a Shadow operation to complete.
 *
 * This function blocks to wait for a [delete](@ref shadow_function_deleteasync),
 * [get](@ref shadow_function_getasync), or [update](@ref shadow_function_updateasync) to
 * complete. These operations are by default asynchronous; the function calls
 * queue an operation for processing, and a callback is invoked once the operation
 * is complete.
 *
 * To use this function, the flag #AWS_IOT_SHADOW_FLAG_WAITABLE must have been
 * set in the operation's function call. Additionally, this function must always
 * be called with any waitable operation to clean up resources.
 *
 * Regardless of its return value, this function always clean up resources used
 * by the waitable operation. This means `operation` is invalidated as soon as
 * this function returns, even if it returns #AWS_IOT_SHADOW_TIMEOUT or another
 * error.
 *
 * @param[in] operation Reference to the Shadow operation to wait for. The flag
 * #AWS_IOT_SHADOW_FLAG_WAITABLE must have been set for this operation.
 * @param[in] timeoutMs How long to wait before returning #AWS_IOT_SHADOW_TIMEOUT.
 * @param[out] pShadowDocument A pointer to a buffer containing the Shadow document
 * retrieved by a [Shadow get](@ref shadow_function_getasync) is placed here. The buffer
 * was allocated with the function #AwsIotShadowDocumentInfo_t.mallocDocument passed
 * to @ref shadow_function_getasync. This parameter is only valid for a [Shadow get]
 * (@ref shadow_function_getasync) and ignored for other Shadow operations. This output
 * parameter is only valid if this function returns #AWS_IOT_SHADOW_SUCCESS.
 * @param[out] pShadowDocumentLength The length of the Shadow document in
 * `pShadowDocument` is placed here. This parameter is only valid for a [Shadow get]
 * (@ref shadow_function_getasync) and ignored for other Shadow operations. This output
 * parameter is only valid if this function returns #AWS_IOT_SHADOW_SUCCESS.
 *
 * @return One of the following:
 * - #AWS_IOT_SHADOW_SUCCESS
 * - #AWS_IOT_SHADOW_NOT_INITIALIZED
 * - #AWS_IOT_SHADOW_BAD_PARAMETER
 * - #AWS_IOT_SHADOW_BAD_RESPONSE
 * - #AWS_IOT_SHADOW_TIMEOUT
 * - A Shadow service rejection reason between 400 (#AWS_IOT_SHADOW_BAD_REQUEST)
 * and 500 (#AWS_IOT_SHADOW_SERVER_ERROR)
 *
 * <b>Example 1 (Shadow Update)</b>
 * @code{c}
 * AwsIotShadowError_t result = AWS_IOT_SHADOW_STATUS_PENDING;
 * AwsIotShadowDocumentInfo_t updateInfo = { ... };
 *
 * // Reference and timeout.
 * AwsIotShadowOperation_t updateOperation = AWS_IOT_SHADOW_OPERATION_INITIALIZER;
 * uint32_t timeout = 5000; // 5 seconds
 *
 * // Shadow update operation.
 * result = AwsIotShadow_UpdateAsync( mqttConnection,
 *                                    &updateInfo,
 *                                    AWS_IOT_SHADOW_FLAG_WAITABLE,
 *                                    NULL,
 *                                    &updateOperation );
 *
 * // Update should have returned AWS_IOT_SHADOW_STATUS_PENDING. The call to wait
 * // returns once the result of the update is available or the timeout expires.
 * if( result == AWS_IOT_SHADOW_STATUS_PENDING )
 * {
 *     // The last two parameters are ignored for a Shadow update.
 *     result = AwsIotShadow_Wait( updateOperation, timeout, NULL, NULL );
 *
 *     // After the call to wait, the result of the update is known
 *     // (not AWS_IOT_SHADOW_STATUS_PENDING).
 *     assert( result != AWS_IOT_SHADOW_STATUS_PENDING );
 * }
 * @endcode
 *
 * <b>Example 2 (Shadow Get)</b>
 * @code{c}
 * AwsIotShadowError_t result = AWS_IOT_SHADOW_STATUS_PENDING;
 * AwsIotShadowDocumentInfo_t getInfo = { ... };
 *
 * // Reference and timeout.
 * AwsIotShadowOperation_t getOperation = AWS_IOT_SHADOW_OPERATION_INITIALIZER;
 * uint32_t timeout = 5000; // 5 seconds
 *
 * // Buffer pointer and size for retrieved Shadow document.
 * const char * pShadowDocument = NULL;
 * size_t documentLength = 0;
 *
 * // Buffer allocation function must be set for a waitable Shadow get.
 * getInfo.get.mallocDocument = malloc;
 *
 * // Shadow get operation.
 * result = AwsIotShadow_GetAsync( mqttConnection,
 *                                 &getInfo,
 *                                 AWS_IOT_SHADOW_FLAG_WAITABLE,
 *                                 NULL,
 *                                 &getOperation );
 *
 * // Get should have returned AWS_IOT_SHADOW_STATUS_PENDING. The call to wait
 * // returns once the result of the get is available or the timeout expires.
 * if( result == AWS_IOT_SHADOW_STATUS_PENDING )
 * {
 *     // The last two parameters must be set for a Shadow get.
 *     result = AwsIotShadow_Wait( getOperation, timeout, &pShadowDocument, &documentLength );
 *
 *     // After the call to wait, the result of the get is known
 *     // (not AWS_IOT_SHADOW_STATUS_PENDING).
 *     assert( result != AWS_IOT_SHADOW_STATUS_PENDING );
 *
 *     // The retrieved Shadow document is only valid for a successful Shadow get.
 *     if( result == AWS_IOT_SHADOW_SUCCESS )
 *     {
 *         // Do something with the Shadow document...
 *
 *         // Free the Shadow document when finished.
 *         free( pShadowDocument );
 *     }
 * }
 * @endcode
 */
/* @[declare_shadow_wait] */
AwsIotShadowError_t AwsIotShadow_Wait( AwsIotShadowOperation_t operation,
                                       uint32_t timeoutMs,
                                       const char ** const pShadowDocument,
                                       size_t * const pShadowDocumentLength );
/* @[declare_shadow_wait] */

/**
 * @brief Set a callback to be invoked when the Thing Shadow `desired` and `reported`
 * states differ.
 *
 * A Thing Shadow contains `reported` and `desired` states, meant to represent
 * the current device status and some desired status, respectively. When the
 * `reported` and `desired` states differ, the Thing Shadow service generates a
 * <i>delta document</i> and publishes it to the topic `update/delta`. Devices
 * with a subscription for this topic will receive the delta document and may act
 * based on the different `reported` and `desired` states. See [this page]
 * (https://docs.aws.amazon.com/iot/latest/developerguide/using-device-shadows.html#delta-state)
 * for more information about using delta documents.
 *
 * A <i>delta callback</i> may be invoked whenever a delta document is generated.
 * Each Thing may have a single delta callback set. This function modifies the delta
 * callback for a specific Thing depending on the `pDeltaCallback` parameter and
 * the presence of any existing delta callback:
 * - When no existing delta callback exists for a specific Thing, a new delta
 * callback is added.
 * - If there is an existing delta callback and `pDeltaCallback` is not `NULL`, then
 * the existing callback function and parameter are replaced with `pDeltaCallback`.
 * - If there is an existing subscription and `pDeltaCallback` is `NULL`, then the
 * delta callback is removed.
 *
 * This function is always blocking; it may block for up to the default MQTT
 * timeout. This timeout is set as a parameter to @ref shadow_function_init,
 * and defaults to @ref AWS_IOT_SHADOW_DEFAULT_MQTT_TIMEOUT_MS if not set. If
 * this function's underlying MQTT operations fail to complete within this
 * timeout, then this function returns #AWS_IOT_SHADOW_TIMEOUT.
 *
 * @param[in] mqttConnection The MQTT connection to use for the subscription to
 * `update/delta`.
 * @param[in] pThingName The subscription to `update/delta` will be added for
 * this Thing Name.
 * @param[in] thingNameLength The length of `pThingName`.
 * @param[in] flags This parameter is for future-compatibility. Currently, flags
 * are not supported for this function and this parameter is ignored.
 * @param[in] pDeltaCallback Callback function to invoke for incoming delta
 * documents.
 *
 * @return One of the following:
 * - #AWS_IOT_SHADOW_SUCCESS
 * - #AWS_IOT_SHADOW_NOT_INITIALIZED
 * - #AWS_IOT_SHADOW_BAD_PARAMETER
 * - #AWS_IOT_SHADOW_NO_MEMORY
 * - #AWS_IOT_SHADOW_MQTT_ERROR
 * - #AWS_IOT_SHADOW_TIMEOUT
 *
 * @return This function always returns #AWS_IOT_SHADOW_SUCCESS when replacing or
 * removing existing delta callbacks.
 *
 * @see @ref shadow_function_setupdatedcallback for the function to register
 * callbacks for all Shadow updates.
 *
 * <b>Example</b>
 * @code{c}
 * #define THING_NAME "Test_device"
 * #define THING_NAME_LENGTH ( sizeof( THING_NAME ) - 1 )
 *
 * AwsIotShadowError_t result = AWS_IOT_SHADOW_STATUS_PENDING;
 * AwsIotShadowCallbackInfo_t deltaCallback = AWS_IOT_SHADOW_CALLBACK_INFO_INITIALIZER;
 *
 * // _deltaCallbackFunction will be invoked when a delta document is received.
 * deltaCallback.function = _deltaCallbackFunction;
 *
 * // Set the delta callback for the Thing "Test_device".
 * result = AwsIotShadow_SetDeltaCallback( mqttConnection,
 *                                         THING_NAME,
 *                                         THING_NAME_LENGTH,
 *                                         0,
 *                                         &deltaCallback );
 *
 * // Check if callback was successfully set.
 * if( result == AWS_IOT_SHADOW_SUCCESS )
 * {
 *     AwsIotShadowDocumentInfo_t updateInfo = AWS_IOT_SHADOW_DOCUMENT_INFO_INITIALIZER;
 *
 *     // Set the Thing Name for Shadow update.
 *     updateInfo.pThingName = THING_NAME;
 *     updateInfo.thingNameLength = THING_NAME_LENGTH;
 *
 *     // Set the Shadow document to send. This document has different "reported"
 *     // and "desired" states. It represents a scenario where a device is currently
 *     // off, but is being ordered to turn on.
 *     updateInfo.update.pUpdateDocument =
 *     "{"
 *          "\"state\": {"
 *              "\"reported\": { \"deviceOn\": false },"
 *              "\"desired\": { \"deviceOn\": true }"
 *          "}"
 *     "}";
 *     updateInfo.update.updateDocumentLength = strlen( updateInfo.update.pUpdateDocument );
 *
 *     // Send the Shadow document with different "reported" and desired states.
 *     result = AwsIotShadow_UpdateSync( mqttConnection,
 *                                       &updateInfo,
 *                                       0,
 *                                       0,
 *                                       5000 );
 *
 *     // After the update is successfully sent, the function _deltaCallbackFunction
 *     // will be invoked once the Shadow service generates and sends a delta document.
 *     // The delta document will contain the different "deviceOn" states, as well as
 *     // metadata.
 *
 *     // Once the delta callback is no longer needed, it may be removed by passing
 *     // NULL as pDeltaCallback.
 *     result = AwsIotShadow_SetDeltaCallback( mqttConnection,
 *                                             THING_NAME,
 *                                             THING_NAME_LENGTH,
 *                                             0,
 *                                             NULL );
 *
 *     // The return value from removing a delta callback should always be success.
 *     assert( result == AWS_IOT_SHADOW_SUCCESS );
 * }
 * @endcode
 */
/* @[declare_shadow_setdeltacallback] */
AwsIotShadowError_t AwsIotShadow_SetDeltaCallback( IotMqttConnection_t mqttConnection,
                                                   const char * pThingName,
                                                   size_t thingNameLength,
                                                   uint32_t flags,
                                                   const AwsIotShadowCallbackInfo_t * pDeltaCallback );
/* @[declare_shadow_setdeltacallback] */

/**
 * @brief Set a callback to be invoked when a Thing Shadow changes.
 *
 * The Shadow service publishes a state document to the `update/documents` topic
 * whenever a Thing Shadow is successfully updated. This document reports the
 * complete previous and current Shadow documents in `previous` and `current`
 * sections, respectively. Therefore, the `update/documents` topic is useful
 * for monitoring Shadow updates.
 *
 * An <i>updated callback</i> may be invoked whenever a document is published to
 * `update/documents`. Each Thing may have a single updated callback set. This function
 * modifies the updated callback for a specific Thing depending on the `pUpdatedCallback`
 * parameter and the presence of any existing updated callback.
 * - When no existing updated callback exists for a specific Thing, a new updated
 * callback is added.
 * - If there is an existing updated callback and `pUpdatedCallback` is not `NULL`,
 * then the existing callback function and parameter are replaced with `pUpdatedCallback`.
 * - If there is an existing updated callback and `pUpdatedCallback` is `NULL`,
 * then the updated callback is removed.
 *
 * @param[in] mqttConnection The MQTT connection to use for the subscription to `update/documents`.
 * @param[in] pThingName The subscription to `update/documents` will be added for
 * this Thing Name.
 * @param[in] thingNameLength The length of `pThingName`.
 * @param[in] flags This parameter is for future-compatibility. Currently, flags are
 * not supported for this function and this parameter is ignored.
 * @param[in] pUpdatedCallback Callback function to invoke for incoming updated documents.
 *
 * @return One of the following:
 * - #AWS_IOT_SHADOW_SUCCESS
 * - #AWS_IOT_SHADOW_NOT_INITIALIZED
 * - #AWS_IOT_SHADOW_BAD_PARAMETER
 * - #AWS_IOT_SHADOW_NO_MEMORY
 * - #AWS_IOT_SHADOW_MQTT_ERROR
 * - #AWS_IOT_SHADOW_TIMEOUT
 *
 * @note Documents published to `update/documents` will be large, as they contain 2
 * complete Shadow state documents. If an updated callback is used, ensure that the
 * device has sufficient memory for incoming documents.
 *
 * @see @ref shadow_function_setdeltacallback for the function to register callbacks
 * for delta documents.
 *
 * <b>Example</b>
 * @code{c}
 * #define THING_NAME "Test_device"
 * #define THING_NAME_LENGTH ( sizeof( THING_NAME ) - 1 )
 *
 * AwsIotShadowError_t result = AWS_IOT_SHADOW_STATUS_PENDING;
 * AwsIotShadowCallbackInfo_t updatedCallback = AWS_IOT_SHADOW_CALLBACK_INFO_INITIALIZER;
 *
 * // _updatedCallbackFunction will be invoked when an updated document is received.
 * updatedCallback.function = _updatedCallbackFunction;
 *
 * // Set the updated callback for the Thing "Test_device".
 * result = AwsIotShadow_SetUpdatedCallback( mqttConnection,
 *                                           THING_NAME,
 *                                           THING_NAME_LENGTH,
 *                                           0,
 *                                           &updatedCallback );
 *
 * // Check if the callback was successfully set.
 * if( result == AWS_IOT_SHADOW_SUCCESS )
 * {
 *     AwsIotShadowDocumentInfo_t updateInfo = AWS_IOT_SHADOW_DOCUMENT_INFO_INITIALIZER;
 *
 *     // Set the Thing Name for Shadow update.
 *     updateInfo.pThingName = THING_NAME;
 *     updateInfo.thingNameLength = THING_NAME_LENGTH;
 *
 *     // Set the Shadow document to send. Any Shadow update will trigger the
 *     // updated callback.
 *     updateInfo.update.pUpdateDocument =
 *     "{"
 *          "\"state\": {"
 *              "\"reported\": { \"deviceOn\": false }"
 *          "}"
 *     "}";
 *     updateInfo.update.updateDocumentLength = strlen( updateInfo.update.pUpdateDocument );
 *
 *     // Send the Shadow document. A successful update will trigger the updated callback.
 *     result = AwsIotShadow_UpdateSync( mqttConnection,
 *                                       &updateInfo,
 *                                       0,
 *                                       0,
 *                                       5000 );
 *
 *     // After a successful Shadow update, the updated callback will be invoked.
 *
 *     // Once the updated callback is no longer needed, it may be removed by
 *     // passing NULL as pUpdatedCallback.
 *     result = AwsIotShadow_SetUpdatedCallback( mqttConnection,
 *                                               THING_NAME,
 *                                               THING_NAME_LENGTH,
 *                                               NULL );
 *
 *     // The return value from removing an updated callback should always be
 *     // success.
 *     assert( result == AWS_IOT_SHADOW_SUCCESS );
 * }
 * @endcode
 */
/* @[declare_shadow_setupdatedcallback] */
AwsIotShadowError_t AwsIotShadow_SetUpdatedCallback( IotMqttConnection_t mqttConnection,
                                                     const char * pThingName,
                                                     size_t thingNameLength,
                                                     uint32_t flags,
                                                     const AwsIotShadowCallbackInfo_t * pUpdatedCallback );
/* @[declare_shadow_setupdatedcallback] */

/**
 * @brief Remove persistent Thing Shadow operation topic subscriptions.
 *
 * Passing the flag @ref AWS_IOT_SHADOW_FLAG_KEEP_SUBSCRIPTIONS to @ref shadow_function_deleteasync,
 * @ref shadow_function_getasync, @ref shadow_function_updateasync, or their blocking versions.
 * causes the Shadow operation topic subscriptions to be maintained for future calls to the
 * same function. If a persistent subscription for a Shadow topic are no longer needed,
 * this function may be used to remove it.
 *
 * @param[in] mqttConnection The MQTT connection associated with the persistent subscription.
 * @param[in] pThingName The Thing Name associated with the persistent subscription.
 * @param[in] thingNameLength The length of `pThingName`.
 * @param[in] flags Flags that determine which subscriptions to remove. Valid values are
 * the bitwise OR of the following individual flags:
 * - @ref AWS_IOT_SHADOW_FLAG_REMOVE_DELETE_SUBSCRIPTIONS
 * - @ref AWS_IOT_SHADOW_FLAG_REMOVE_GET_SUBSCRIPTIONS
 * - @ref AWS_IOT_SHADOW_FLAG_REMOVE_UPDATE_SUBSCRIPTIONS
 *
 * @return On success:
 * - #AWS_IOT_SHADOW_SUCCESS
 * @return If an MQTT UNSUBSCRIBE packet cannot be sent, one of the following:
 * - #AWS_IOT_SHADOW_NO_MEMORY
 * - #AWS_IOT_SHADOW_MQTT_ERROR
 *
 * @note @ref shadow_function_cleanup removes all persistent subscriptions as well.
 *
 * @warning This function is not safe to call with any in-progress operations!
 * It also does not affect delta and updated callbacks registered with @ref
 * shadow_function_setdeltacallback and @ref shadow_function_setupdatedcallback,
 * respectively. (See documentation for those functions on how to remove their
 * callbacks).
 */
/* @[declare_shadow_removepersistentsubscriptions] */
AwsIotShadowError_t AwsIotShadow_RemovePersistentSubscriptions( IotMqttConnection_t mqttConnection,
                                                                const char * pThingName,
                                                                size_t thingNameLength,
                                                                uint32_t flags );
/* @[declare_shadow_removepersistentsubscriptions] */

/*------------------------- Shadow helper functions -------------------------*/

/**
 * @brief Returns a string that describes an #AwsIotShadowError_t.
 *
 * Like POSIX's `strerror`, this function returns a string describing a return
 * code. In this case, the return code is a Shadow library error code, `status`.
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
/* @[declare_shadow_strerror] */
const char * AwsIotShadow_strerror( AwsIotShadowError_t status );
/* @[declare_shadow_strerror] */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Backwards compatibility macros for previous function names.
 */
#define AwsIotShadow_Delete         AwsIotShadow_DeleteAsync
#define AwsIotShadow_TimedDelete    AwsIotShadow_DeleteSync
#define AwsIotShadow_Get            AwsIotShadow_GetAsync
#define AwsIotShadow_TimedGet       AwsIotShadow_GetSync
#define AwsIotShadow_Update         AwsIotShadow_UpdateAsync
#define AwsIotShadow_TimedUpdate    AwsIotShadow_UpdateSync
/** @endcond */

#endif /* ifndef AWS_IOT_SHADOW_H_ */
