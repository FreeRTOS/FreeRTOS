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
 
#ifndef CORE_MQTT_CONFIG_H
#define CORE_MQTT_CONFIG_H

/**************************************************/
/******* DO NOT CHANGE the following order ********/
/**************************************************/

/* Include logging header files and define logging macros in the following order:
 * 1. Include the header file "logging_levels.h".
 * 2. Define the LIBRARY_LOG_NAME and LIBRARY_LOG_LEVEL macros depending on
 * the logging configuration for MQTT.
 * 3. Include the header file "logging_stack.h", if logging is enabled for MQTT.
 */

#include "logging_levels.h"

/* Logging configuration for the MQTT library. */
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME    "MQTT"
#endif

#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_ERROR
#endif

/* Prototype for the function used to print to console on Windows simulator
 * of FreeRTOS.
 * The function prints to the console before the network is connected;
 * then a UDP port after the network has connected. */
extern void vLoggingPrintf( const char * pcFormatString,
                            ... );

/* Map the SdkLog macro to the logging function to enable logging
 * on Windows simulator. */
#ifndef SdkLog
    #define SdkLog( message )    vLoggingPrintf message
#endif
#include "logging_stack.h"
/************ End of logging configuration ****************/

/**
 * @brief The maximum number of MQTT PUBLISH messages that may be pending
 * acknowledgement at any time.
 *
 * QoS 1 and 2 MQTT PUBLISHes require acknowledgment from the server before
 * they can be completed. While they are awaiting the acknowledgment, the
 * client must maintain information about their state. The value of this
 * macro sets the limit on how many simultaneous PUBLISH states an MQTT
 * context maintains.
 */
#define MQTT_STATE_ARRAY_MAX_COUNT    10U

 /*********************** coreMQTT Agent Configurations **********************/
 /**
  * @brief The maximum number of pending acknowledgments to track for a single
  * connection.
  *
  * @note The MQTT agent tracks MQTT commands (such as PUBLISH and SUBSCRIBE) th
  * at are still waiting to be acknowledged.  MQTT_AGENT_MAX_OUTSTANDING_ACKS set
  * the maximum number of acknowledgments that can be outstanding at any one time.
  * The higher this number is the greater the agent's RAM consumption will be.
  */
#define MQTT_AGENT_MAX_OUTSTANDING_ACKS         ( 20U )

  /**
   * @brief Time in MS that the MQTT agent task will wait in the Blocked state (so
   * not using any CPU time) for a command to arrive in its command queue before
   * exiting the blocked state so it can call MQTT_ProcessLoop().
   *
   * @note It is important MQTT_ProcessLoop() is called often if there is known
   * MQTT traffic, but calling it too often can take processing time away from
   * lower priority tasks and waste CPU time and power.
   */
#define MQTT_AGENT_MAX_EVENT_QUEUE_WAIT_TIME    ( 1000 )

   /**
    * @brief The number of command structures to allocate in the pool
    * for the agent.
    */
#define MQTT_COMMAND_CONTEXTS_POOL_SIZE         10


#endif /* ifndef CORE_MQTT_CONFIG_H */
