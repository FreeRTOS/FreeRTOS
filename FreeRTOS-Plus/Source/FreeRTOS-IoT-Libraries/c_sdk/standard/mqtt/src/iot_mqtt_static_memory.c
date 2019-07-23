/*
 * Amazon FreeRTOS MQTT V2.0.0
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
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file iot_mqtt_static_memory.c
 * @brief Implementation of MQTT static memory functions.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* This file should only be compiled if dynamic memory allocation is forbidden. */
#if IOT_STATIC_MEMORY_ONLY == 1

/* Standard includes. */
#include <stdbool.h>
#include <stddef.h>
#include <string.h>

/* Static memory include. */
#include "private/iot_static_memory.h"

/* MQTT internal include. */
#include "private/iot_mqtt_internal.h"

/*-----------------------------------------------------------*/

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * Provide default values for undefined configuration constants.
 */
#ifndef IOT_MQTT_CONNECTIONS
    #define IOT_MQTT_CONNECTIONS                   ( 1 )
#endif
#ifndef IOT_MQTT_MAX_IN_PROGRESS_OPERATIONS
    #define IOT_MQTT_MAX_IN_PROGRESS_OPERATIONS    ( 10 )
#endif
#ifndef IOT_MQTT_SUBSCRIPTIONS
    #define IOT_MQTT_SUBSCRIPTIONS                 ( 8 )
#endif
/** @endcond */

/* Validate static memory configuration settings. */
#if IOT_MQTT_CONNECTIONS <= 0
    #error "IOT_MQTT_CONNECTIONS cannot be 0 or negative."
#endif
#if IOT_MQTT_MAX_IN_PROGRESS_OPERATIONS <= 0
    #error "IOT_MQTT_MAX_IN_PROGRESS_OPERATIONS cannot be 0 or negative."
#endif
#if IOT_MQTT_SUBSCRIPTIONS <= 0
    #error "IOT_MQTT_SUBSCRIPTIONS cannot be 0 or negative."
#endif

/**
 * @brief The size of a static memory MQTT subscription.
 *
 * Since the pTopic member of #_mqttSubscription_t is variable-length, the constant
 * #AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH is used for the length of
 * #_mqttSubscription_t.pTopicFilter.
 */
#define MQTT_SUBSCRIPTION_SIZE    ( sizeof( _mqttSubscription_t ) + AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH )

/*-----------------------------------------------------------*/

/*
 * Static memory buffers and flags, allocated and zeroed at compile-time.
 */
static bool _pInUseMqttConnections[ IOT_MQTT_CONNECTIONS ] = { 0 };                               /**< @brief MQTT connection in-use flags. */
static _mqttConnection_t _pMqttConnections[ IOT_MQTT_CONNECTIONS ] = { { 0 } };                   /**< @brief MQTT connections. */

static bool _pInUseMqttOperations[ IOT_MQTT_MAX_IN_PROGRESS_OPERATIONS ] = { 0 };                        /**< @brief MQTT operation in-use flags. */
static _mqttOperation_t _pMqttOperations[ IOT_MQTT_MAX_IN_PROGRESS_OPERATIONS ] = { { .link = { 0 } } }; /**< @brief MQTT operations. */

static bool _pInUseMqttSubscriptions[ IOT_MQTT_SUBSCRIPTIONS ] = { 0 };                           /**< @brief MQTT subscription in-use flags. */
static char _pMqttSubscriptions[ IOT_MQTT_SUBSCRIPTIONS ][ MQTT_SUBSCRIPTION_SIZE ] = { { 0 } };  /**< @brief MQTT subscriptions. */

/*-----------------------------------------------------------*/

void * IotMqtt_MallocConnection( size_t size )
{
    int32_t freeIndex = -1;
    void * pNewConnection = NULL;

    /* Check size argument. */
    if( size == sizeof( _mqttConnection_t ) )
    {
        /* Find a free MQTT connection. */
        freeIndex = IotStaticMemory_FindFree( _pInUseMqttConnections,
                                              IOT_MQTT_CONNECTIONS );

        if( freeIndex != -1 )
        {
            pNewConnection = &( _pMqttConnections[ freeIndex ] );
        }
    }

    return pNewConnection;
}

/*-----------------------------------------------------------*/

void IotMqtt_FreeConnection( void * ptr )
{
    /* Return the in-use MQTT connection. */
    IotStaticMemory_ReturnInUse( ptr,
                                 _pMqttConnections,
                                 _pInUseMqttConnections,
                                 IOT_MQTT_CONNECTIONS,
                                 sizeof( _mqttConnection_t ) );
}

/*-----------------------------------------------------------*/

void * IotMqtt_MallocOperation( size_t size )
{
    int32_t freeIndex = -1;
    void * pNewOperation = NULL;

    /* Check size argument. */
    if( size == sizeof( _mqttOperation_t ) )
    {
        /* Find a free MQTT operation. */
        freeIndex = IotStaticMemory_FindFree( _pInUseMqttOperations,
                                              IOT_MQTT_MAX_IN_PROGRESS_OPERATIONS );

        if( freeIndex != -1 )
        {
            pNewOperation = &( _pMqttOperations[ freeIndex ] );
        }
    }

    return pNewOperation;
}

/*-----------------------------------------------------------*/

void IotMqtt_FreeOperation( void * ptr )
{
    /* Return the in-use MQTT operation. */
    IotStaticMemory_ReturnInUse( ptr,
                                 _pMqttOperations,
                                 _pInUseMqttOperations,
                                 IOT_MQTT_MAX_IN_PROGRESS_OPERATIONS,
                                 sizeof( _mqttOperation_t ) );
}

/*-----------------------------------------------------------*/

void * IotMqtt_MallocSubscription( size_t size )
{
    int32_t freeIndex = -1;
    void * pNewSubscription = NULL;

    if( size <= MQTT_SUBSCRIPTION_SIZE )
    {
        /* Get the index of a free MQTT subscription. */
        freeIndex = IotStaticMemory_FindFree( _pInUseMqttSubscriptions,
                                              IOT_MQTT_SUBSCRIPTIONS );

        if( freeIndex != -1 )
        {
            pNewSubscription = &( _pMqttSubscriptions[ freeIndex ][ 0 ] );
        }
    }

    return pNewSubscription;
}

/*-----------------------------------------------------------*/

void IotMqtt_FreeSubscription( void * ptr )
{
    /* Return the in-use MQTT subscription. */
    IotStaticMemory_ReturnInUse( ptr,
                                 _pMqttSubscriptions,
                                 _pInUseMqttSubscriptions,
                                 IOT_MQTT_SUBSCRIPTIONS,
                                 MQTT_SUBSCRIPTION_SIZE );
}

/*-----------------------------------------------------------*/

#endif
