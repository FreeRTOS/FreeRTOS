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

#ifndef __AWS_IOT_OTA_INTERFACE__H__
#define __AWS_IOT_OTA_INTERFACE__H__

/* OTA includes. */
#include "aws_iot_ota_agent.h"
#include "aws_iot_ota_agent_internal.h"

/* General Constants. */

/* OTA control protocol constants. */
#define OTA_CONTROL_OVER_MQTT     0x00000001

/* OTA data protocol constants. */
#define OTA_DATA_OVER_MQTT        0x00000001
#define OTA_DATA_OVER_HTTP        0x00000002
#define OTA_DATA_NUM_PROTOCOLS    ( 2U )


/**
 * @brief Represents the OTA control interface functions.
 *
 * The functions in this structure are used for the control operations
 * during over the air updates like OTA job status updates.
 */
typedef struct
{
    OTA_Err_t ( * prvRequestJob )( OTA_AgentContext_t * pAgentCtx );
    OTA_Err_t ( * prvUpdateJobStatus )( OTA_AgentContext_t * pxAgentCtx,
                                        OTA_JobStatus_t eStatus,
                                        int32_t lReason,
                                        int32_t lSubReason );
} OTA_ControlInterface_t;

/**
 * @brief Represents the OTA data interface functions.
 *
 * The functions in this structure are used for the data operations
 * during over the air updates like requesting file blocks.
 */
typedef struct
{
    OTA_Err_t ( * prvInitFileTransfer )( OTA_AgentContext_t * pAgentCtx );
    OTA_Err_t ( * prvRequestFileBlock )( OTA_AgentContext_t * pAgentCtx );
    OTA_Err_t ( * prvDecodeFileBlock )( uint8_t * pucMessageBuffer,
                                        size_t xMessageSize,
                                        int32_t * plFileId,
                                        int32_t * plBlockId,
                                        int32_t * plBlockSize,
                                        uint8_t ** ppucPayload,
                                        size_t * pxPayloadSize );
    OTA_Err_t ( * prvCleanup )( OTA_AgentContext_t * pAgentCtx );
} OTA_DataInterface_t;

/**
 * @brief Set control interface for OTA operations.
 *
 * This function updates the OTA control operation functions as per the config
 * options selected.
 *
 * @param[out] pxControlInterface OTA Control interface.
 *
 */
void prvSetControlInterface( OTA_ControlInterface_t * pxControlInterface );

/**
 * @brief Set data interface for OTA operations.
 *
 * This function updates the OTA data operation functions as per the config
 * options selected.
 *
 * @param[out] pxDataInterface OTA data interface.
 *
 */

OTA_Err_t prvSetDataInterface( OTA_DataInterface_t * pxDataInterface,
                               const uint8_t * pucProtocol );

#endif /* ifndef __AWS_IOT_OTA_INTERFACE__H__ */
