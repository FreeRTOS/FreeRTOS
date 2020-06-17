/*
 * FreeRTOS OTA V1.2.0
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
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

#ifndef __AWS_IOT_OTA_MQTT__H__
#define __AWS_IOT_OTA_MQTT__H__

/* OTA includes. */
#include "aws_iot_ota_agent.h"
#include "aws_iot_ota_agent_internal.h"

/**
 * @brief Check for available OTA job over MQTT.
 *
 * This function Request for the next available OTA job from the job service
 * by publishing a "get next job" message to the job service.
 *
 * @param[in] pxAgentCtx The OTA agent context.
 *
 * @return The OTA error code. See OTA Agent error codes information in aws_iot_ota_agent.h.
 */

OTA_Err_t prvRequestJob_Mqtt( OTA_AgentContext_t * pxAgentCtx );

/**
 * @brief Initialize file transfer over MQTT.
 *
 * This function initializes the file transfer after the OTA job is parsed and accepted
 * by subscribing to the data streaming topics.
 *
 * @param[in] pxAgentCtx The OTA agent context.
 *
 * @return The OTA error code. See OTA Agent error codes information in aws_iot_ota_agent.h.
 */

OTA_Err_t prvInitFileTransfer_Mqtt( OTA_AgentContext_t * pxAgentCtx );

/**
 * @brief Request File block over MQTT.
 *
 * This function is used for requesting a file block over MQTT using the
 * file context.
 *
 * @param[in] pxAgentCtx The OTA agent context.
 *
 * @return The OTA PAL layer error code combined with the MCU specific error code. See OTA Agent
 * error codes information in aws_iot_ota_agent.h.
 */

OTA_Err_t prvRequestFileBlock_Mqtt( OTA_AgentContext_t * pxAgentCtx );

/**
 * @brief Decode a cbor encoded fileblock.
 *
 * This function is used for decoding a file block received over MQTT & encoded in cbor.
 *
 * @param[in] pucMessageBuffer The message to be decoded.
 * @param[in] xMessageSize     The size of the message in bytes.
 * @param[out] plFileId        The server file ID.
 * @param[out] plBlockId       The file block ID.
 * @param[out] plBlockSize     The file block size.
 * @param[out] ppucPayload     The payload.
 * @param[out] pxPayloadSize   The payload size.
 *
 * @return The OTA PAL layer error code combined with the MCU specific error code. See OTA Agent
 * error codes information in aws_iot_ota_agent.h.
 */

OTA_Err_t prvDecodeFileBlock_Mqtt( uint8_t * pucMessageBuffer,
                                   size_t xMessageSize,
                                   int32_t * plFileId,
                                   int32_t * plBlockId,
                                   int32_t * plBlockSize,
                                   uint8_t ** ppucPayload,
                                   size_t * pxPayloadSize );

/**
 * @brief Cleanup related to OTA over MQTT.
 *
 * This function perfroms cleanup by unsubscribing from any topics that were
 * subscribed for performing OTA over MQTT.
 *
 * @param[in] pxAgentCtx The OTA agent context.
 *
 * @return The OTA error code. See OTA Agent error codes information in aws_iot_ota_agent.h.
 */

OTA_Err_t prvCleanup_Mqtt( OTA_AgentContext_t * pxAgentCtx );

/**
 * @brief Update job status over MQTT.
 *
 * This function updates the OTA job status over MQTT with information like in progress, completion
 * or failure.
 *
 * @param[in] pxAgentCtx The OTA agent context.
 *
 * @param[in] eStatus The OTA job status which should be updated. @see OTA_JobStatus_t.
 *
 * @param[in] lReason The major reason for the status update.
 *
 * @param[in] lSubReason The platform specific reason.
 *
 * @return The OTA error code. See OTA Agent error codes information in aws_iot_ota_agent.h.
 */

OTA_Err_t prvUpdateJobStatus_Mqtt( OTA_AgentContext_t * pxAgentCtx,
                                   OTA_JobStatus_t eStatus,
                                   int32_t lReason,
                                   int32_t lSubReason );


#endif /* ifndef __AWS_IOT_OTA_MQTT__H__ */
