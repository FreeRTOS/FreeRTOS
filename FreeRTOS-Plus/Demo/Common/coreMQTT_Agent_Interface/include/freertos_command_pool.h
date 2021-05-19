/*
 * FreeRTOS V202104.00
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
 * @file freertos_command_pool.h
 * @brief Functions to obtain and release a command.
 */
#ifndef FREERTOS_COMMAND_POOL_H
#define FREERTOS_COMMAND_POOL_H

/* MQTT agent includes. */
#include "core_mqtt_agent.h"

/**
 * @brief Initialize the common task pool. Not thread safe.
 */
void Agent_InitializePool( void );

/**
 * @brief Obtain a MQTTAgentCommand_t structure from the pool of structures managed by the agent.
 *
 * @note MQTTAgentCommand_t structures hold everything the MQTT agent needs to process a
 * command that originates from application.  Examples of commands are PUBLISH and
 * SUBSCRIBE.  The MQTTAgentCommand_t structure must persist for the duration of the command's
 * operation so are obtained from a pool of statically allocated structures when a
 * new command is created, and returned to the pool when the command is complete.
 * The MQTT_COMMAND_CONTEXTS_POOL_SIZE configuration file constant defines how many
 * structures the pool contains.
 *
 * @param[in] blockTimeMs The length of time the calling task should remain in the
 * Blocked state (so not consuming any CPU time) to wait for a MQTTAgentCommand_t structure to
 * become available should one not be immediately at the time of the call.
 *
 * @return A pointer to a MQTTAgentCommand_t structure if one becomes available before
 * blockTimeMs time expired, otherwise NULL.
 */
MQTTAgentCommand_t * Agent_GetCommand( uint32_t blockTimeMs );

/**
 * @brief Give a MQTTAgentCommand_t structure back to the the pool of structures managed by
 * the agent.
 *
 * @note MQTTAgentCommand_t structures hold everything the MQTT agent needs to process a
 * command that originates from application.  Examples of commands are PUBLISH and
 * SUBSCRIBE.  The MQTTAgentCommand_t structure must persist for the duration of the command's
 * operation so are obtained from a pool of statically allocated structures when a
 * new command is created, and returned to the pool when the command is complete.
 * The MQTT_COMMAND_CONTEXTS_POOL_SIZE configuration file constant defines how many
 * structures the pool contains.
 *
 * @param[in] pCommandToRelease A pointer to the MQTTAgentCommand_t structure to return to
 * the pool.  The structure must first have been obtained by calling
 * Agent_GetCommand(), otherwise Agent_ReleaseCommand() will
 * have no effect.
 *
 * @return true if the MQTTAgentCommand_t structure was returned to the pool, otherwise false.
 */
bool Agent_ReleaseCommand( MQTTAgentCommand_t * pCommandToRelease );

#endif /* FREERTOS_COMMAND_POOL_H */
