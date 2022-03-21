/*
 * FreeRTOS V202112.00
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/**
 * @file freertos_agent_message.h
 * @brief Functions to interact with queues.
 */
#ifndef FREERTOS_AGENT_MESSAGE_H
#define FREERTOS_AGENT_MESSAGE_H

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"

/* Include MQTT agent messaging interface. */
#include "core_mqtt_agent_message_interface.h"

/**
 * @ingroup mqtt_agent_struct_types
 * @brief Context with which tasks may deliver messages to the agent.
 */
struct MQTTAgentMessageContext
{
    QueueHandle_t queue;
};

/*-----------------------------------------------------------*/

/**
 * @brief Send a message to the specified context.
 * Must be thread safe.
 *
 * @param[in] pMsgCtx An #MQTTAgentMessageContext_t.
 * @param[in] pCommandToSend Pointer to address to send to queue.
 * @param[in] blockTimeMs Block time to wait for a send.
 *
 * @return `true` if send was successful, else `false`.
 */
bool Agent_MessageSend( const MQTTAgentMessageContext_t * pMsgCtx,
                        MQTTAgentCommand_t * const * pCommandToSend,
                        uint32_t blockTimeMs );

/**
 * @brief Receive a message from the specified context.
 * Must be thread safe.
 *
 * @param[in] pMsgCtx An #MQTTAgentMessageContext_t.
 * @param[in] pReceivedCommand Pointer to write address of received command.
 * @param[in] blockTimeMs Block time to wait for a receive.
 *
 * @return `true` if receive was successful, else `false`.
 */
bool Agent_MessageReceive( const MQTTAgentMessageContext_t * pMsgCtx,
                           MQTTAgentCommand_t ** pReceivedCommand,
                           uint32_t blockTimeMs );

#endif /* FREERTOS_AGENT_MESSAGE_H */
