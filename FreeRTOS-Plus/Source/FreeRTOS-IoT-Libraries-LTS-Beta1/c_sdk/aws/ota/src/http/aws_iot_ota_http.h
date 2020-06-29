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

#ifndef __AWS_OTA_HTTP__H__
#define __AWS_OTA_HTTP__H__

/* OTA includes. */
#include "aws_iot_ota_agent.h"
#include "aws_iot_ota_agent_internal.h"


OTA_Err_t _AwsIotOTA_InitFileTransfer_HTTP( OTA_AgentContext_t * pxAgentCtx );

OTA_Err_t _AwsIotOTA_RequestDataBlock_HTTP( OTA_AgentContext_t * pxAgentCtx );

OTA_Err_t _AwsIotOTA_DecodeFileBlock_HTTP( uint8_t * pMessageBuffer,
                                           size_t messageSize,
                                           int32_t * pFileId,
                                           int32_t * pBlockId,
                                           int32_t * pBlockSize,
                                           uint8_t ** pPayload,
                                           size_t * pPayloadSize );

OTA_Err_t _AwsIotOTA_Cleanup_HTTP( OTA_AgentContext_t * pxAgentCtx );

#endif /* ifndef __AWS_OTA_HTTP__H__ */
