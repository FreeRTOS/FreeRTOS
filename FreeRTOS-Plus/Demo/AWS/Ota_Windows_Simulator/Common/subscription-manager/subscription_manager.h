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
 * @file subscription_manager.h
 * @brief Functions for managing MQTT subscriptions.
 */
#ifndef SUBSCRIPTION_MANAGER_H
#define SUBSCRIPTION_MANAGER_H

/**************************************************/
/******* DO NOT CHANGE the following order ********/
/**************************************************/

/* Logging related header files are required to be included in the following order:
 * 1. Include the header file "logging_levels.h".
 * 2. Define LIBRARY_LOG_NAME and  LIBRARY_LOG_LEVEL.
 * 3. Include the header file "logging_stack.h".
 */

/* Include header that defines log levels. */
#include "logging_levels.h"

/* Logging configuration for the Subscription Manager module. */
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME     "Subscription Manager"
#endif
#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_ERROR
#endif

#include "logging_stack.h"


/* Demo config include. */
#include "demo_config.h"

/* core MQTT include. */
#include "core_mqtt.h"


/**
 * @brief Maximum number of subscriptions maintained by the subscription manager
 * simultaneously in a list.
 */
#ifndef SUBSCRIPTION_MANAGER_MAX_SUBSCRIPTIONS
    #define SUBSCRIPTION_MANAGER_MAX_SUBSCRIPTIONS    10U
#endif

/**
 * @brief Callback function called when receiving a publish.
 *
 * @param[in] pvIncomingPublishCallbackContext The incoming publish callback context.
 * @param[in] pxPublishInfo Deserialized publish information.
 */
typedef void (* IncomingPubCallback_t )( void * pvIncomingPublishCallbackContext,
                                         MQTTPublishInfo_t * pxPublishInfo );

/**
 * @brief An element in the list of subscriptions.
 *
 * This subscription manager implementation expects that the array of the
 * subscription elements used for storing subscriptions to be initialized to 0.
 *
 * @note This implementation allows multiple tasks to subscribe to the same topic.
 * In this case, another element is added to the subscription list, differing
 * in the intended publish callback. Also note that the topic filters are not
 * copied in the subscription manager and hence the topic filter strings need to
 * stay in scope until unsubscribed.
 */
typedef struct subscriptionElement
{
    IncomingPubCallback_t pxIncomingPublishCallback;
    void * pvIncomingPublishCallbackContext;
    uint16_t usFilterStringLength;
    const char * pcSubscriptionFilterString;
} SubscriptionElement_t;

/**
 * @brief Add a subscription to the subscription list.
 *
 * @note Multiple tasks can be subscribed to the same topic with different
 * context-callback pairs. However, a single context-callback pair may only be
 * associated to the same topic filter once.
 *
 * @param[in] pxSubscriptionList  The pointer to the subscription list array.
 * @param[in] pcTopicFilterString Topic filter string of subscription.
 * @param[in] usTopicFilterLength Length of topic filter string.
 * @param[in] pxIncomingPublishCallback Callback function for the subscription.
 * @param[in] pvIncomingPublishCallbackContext Context for the subscription callback.
 *
 * @return `true` if subscription added or exists, `false` if insufficient memory.
 */
bool addSubscription( SubscriptionElement_t * pxSubscriptionList,
                      const char * pcTopicFilterString,
                      uint16_t usTopicFilterLength,
                      IncomingPubCallback_t pxIncomingPublishCallback,
                      void * pvIncomingPublishCallbackContext );

/**
 * @brief Remove a subscription from the subscription list.
 *
 * @note If the topic filter exists multiple times in the subscription list,
 * then every instance of the subscription will be removed.
 *
 * @param[in] pxSubscriptionList  The pointer to the subscription list array.
 * @param[in] pcTopicFilterString Topic filter of subscription.
 * @param[in] usTopicFilterLength Length of topic filter.
 */
void removeSubscription( SubscriptionElement_t * pxSubscriptionList,
                         const char * pcTopicFilterString,
                         uint16_t usTopicFilterLength );

/**
 * @brief Handle incoming publishes by invoking the callbacks registered
 * for the incoming publish's topic filter.
 *
 * @param[in] pxSubscriptionList  The pointer to the subscription list array.
 * @param[in] pxPublishInfo Info of incoming publish.
 *
 * @return `true` if an application callback could be invoked;
 *  `false` otherwise.
 */
bool handleIncomingPublishes( SubscriptionElement_t * pxSubscriptionList,
                              MQTTPublishInfo_t * pxPublishInfo );

#endif /* SUBSCRIPTION_MANAGER_H */
