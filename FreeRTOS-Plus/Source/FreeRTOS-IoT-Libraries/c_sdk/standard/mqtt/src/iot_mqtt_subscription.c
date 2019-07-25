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
 * @file iot_mqtt_subscription.c
 * @brief Implements functions that manage subscriptions for an MQTT connection.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdbool.h>
#include <string.h>

/* Error handling include. */
#include "private/iot_error.h"

/* MQTT internal include. */
#include "private/iot_mqtt_internal.h"

/* Platform layer includes. */
#include "platform/iot_threads.h"

/*-----------------------------------------------------------*/

/**
 * @brief First parameter to #_topicMatch.
 */
typedef struct _topicMatchParams
{
    const char * pTopicName;  /**< @brief The topic name to parse. */
    uint16_t topicNameLength; /**< @brief Length of #_topicMatchParams_t.pTopicName. */
    bool exactMatchOnly;      /**< @brief Whether to allow wildcards or require exact matches. */
} _topicMatchParams_t;

/**
 * @brief First parameter to #_packetMatch.
 */
typedef struct _packetMatchParams
{
    uint16_t packetIdentifier; /**< Packet identifier to match. */
    int32_t order;             /**< Order to match. Set to `-1` to ignore. */
} _packetMatchParams_t;

/*-----------------------------------------------------------*/

/**
 * @brief Matches a topic name (from a publish) with a topic filter (from a
 * subscription).
 *
 * @param[in] pSubscriptionLink Pointer to the link member of an #_mqttSubscription_t.
 * @param[in] pMatch Pointer to a #_topicMatchParams_t.
 *
 * @return `true` if the arguments match the subscription topic filter; `false`
 * otherwise.
 */
static bool _topicMatch( const IotLink_t * pSubscriptionLink,
                         void * pMatch );

/**
 * @brief Matches a packet identifier and order.
 *
 * @param[in] pSubscriptionLink Pointer to the link member of an #_mqttSubscription_t.
 * @param[in] pMatch Pointer to a #_packetMatchParams_t.
 *
 * @return `true` if the arguments match the subscription's packet info; `false`
 * otherwise.
 */
static bool _packetMatch( const IotLink_t * pSubscriptionLink,
                          void * pMatch );

/*-----------------------------------------------------------*/

static bool _topicMatch( const IotLink_t * pSubscriptionLink,
                         void * pMatch )
{
    IOT_FUNCTION_ENTRY( bool, false );
    uint16_t nameIndex = 0, filterIndex = 0;

    /* Because this function is called from a container function, the given link
     * must never be NULL. */
    IotMqtt_Assert( pSubscriptionLink != NULL );

    _mqttSubscription_t * pSubscription = IotLink_Container( _mqttSubscription_t,
                                                             pSubscriptionLink,
                                                             link );
    _topicMatchParams_t * pParam = ( _topicMatchParams_t * ) pMatch;

    /* Extract the relevant strings and lengths from parameters. */
    const char * pTopicName = pParam->pTopicName;
    const char * pTopicFilter = pSubscription->pTopicFilter;
    const uint16_t topicNameLength = pParam->topicNameLength;
    const uint16_t topicFilterLength = pSubscription->topicFilterLength;

    /* Check for an exact match. */
    if( topicNameLength == topicFilterLength )
    {
        status = ( strncmp( pTopicName, pTopicFilter, topicNameLength ) == 0 );

        IOT_GOTO_CLEANUP();
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* If the topic lengths are different but an exact match is required, return
     * false. */
    if( pParam->exactMatchOnly == true )
    {
        IOT_SET_AND_GOTO_CLEANUP( false );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    while( ( nameIndex < topicNameLength ) && ( filterIndex < topicFilterLength ) )
    {
        /* Check if the character in the topic name matches the corresponding
         * character in the topic filter string. */
        if( pTopicName[ nameIndex ] == pTopicFilter[ filterIndex ] )
        {
            /* Handle special corner cases as documented by the MQTT protocol spec. */

            /* Filter "sport/#" also matches "sport" since # includes the parent level. */
            if( nameIndex == topicNameLength - 1 )
            {
                if( filterIndex == topicFilterLength - 3 )
                {
                    if( pTopicFilter[ filterIndex + 1 ] == '/' )
                    {
                        if( pTopicFilter[ filterIndex + 2 ] == '#' )
                        {
                            IOT_SET_AND_GOTO_CLEANUP( true );
                        }
                        else
                        {
                            EMPTY_ELSE_MARKER;
                        }
                    }
                    else
                    {
                        EMPTY_ELSE_MARKER;
                    }
                }
                else
                {
                    EMPTY_ELSE_MARKER;
                }
            }
            else
            {
                EMPTY_ELSE_MARKER;
            }

            /* Filter "sport/+" also matches the "sport/" but not "sport". */
            if( nameIndex == topicNameLength - 1 )
            {
                if( filterIndex == topicFilterLength - 2 )
                {
                    if( pTopicFilter[ filterIndex + 1 ] == '+' )
                    {
                        IOT_SET_AND_GOTO_CLEANUP( true );
                    }
                    else
                    {
                        EMPTY_ELSE_MARKER;
                    }
                }
                else
                {
                    EMPTY_ELSE_MARKER;
                }
            }
            else
            {
                EMPTY_ELSE_MARKER;
            }
        }
        else
        {
            /* Check for wildcards. */
            if( pTopicFilter[ filterIndex ] == '+' )
            {
                /* Move topic name index to the end of the current level.
                 * This is identified by '/'. */
                while( nameIndex < topicNameLength && pTopicName[ nameIndex ] != '/' )
                {
                    nameIndex++;
                }

                /* Increment filter index to skip '/'. */
                filterIndex++;
                continue;
            }
            else if( pTopicFilter[ filterIndex ] == '#' )
            {
                /* Subsequent characters don't need to be checked if the for the
                 * multi-level wildcard. */
                IOT_SET_AND_GOTO_CLEANUP( true );
            }
            else
            {
                /* Any character mismatch other than '+' or '#' means the topic
                 * name does not match the topic filter. */
                IOT_SET_AND_GOTO_CLEANUP( false );
            }
        }

        /* Increment indexes. */
        nameIndex++;
        filterIndex++;
    }

    /* If the end of both strings has been reached, they match. */
    if( ( nameIndex == topicNameLength ) && ( filterIndex == topicFilterLength ) )
    {
        IOT_SET_AND_GOTO_CLEANUP( true );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

static bool _packetMatch( const IotLink_t * pSubscriptionLink,
                          void * pMatch )
{
    bool match = false;

    /* Because this function is called from a container function, the given link
     * must never be NULL. */
    IotMqtt_Assert( pSubscriptionLink != NULL );

    _mqttSubscription_t * pSubscription = IotLink_Container( _mqttSubscription_t,
                                                             pSubscriptionLink,
                                                             link );
    _packetMatchParams_t * pParam = ( _packetMatchParams_t * ) pMatch;

    /* Compare packet identifiers. */
    if( pParam->packetIdentifier == pSubscription->packetInfo.identifier )
    {
        /* Compare orders if order is not -1. */
        if( pParam->order == -1 )
        {
            match = true;
        }
        else
        {
            match = ( ( size_t ) pParam->order ) == pSubscription->packetInfo.order;
        }
    }

    /* If this subscription should be removed, check the reference count. */
    if( match == true )
    {
        /* Reference count must not be negative. */
        IotMqtt_Assert( pSubscription->references >= 0 );

        /* If the reference count is positive, this subscription cannot be
         * removed yet because there are subscription callbacks using it. */
        if( pSubscription->references > 0 )
        {
            match = false;

            /* Set the unsubscribed flag. The last active subscription callback
             * will remove and clean up this subscription. */
            pSubscription->unsubscribed = true;
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    return match;
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_AddSubscriptions( _mqttConnection_t * pMqttConnection,
                                          uint16_t subscribePacketIdentifier,
                                          const IotMqttSubscription_t * pSubscriptionList,
                                          size_t subscriptionCount )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    size_t i = 0;
    _mqttSubscription_t * pNewSubscription = NULL;
    IotLink_t * pSubscriptionLink = NULL;
    _topicMatchParams_t topicMatchParams = { .exactMatchOnly = true };

    IotMutex_Lock( &( pMqttConnection->subscriptionMutex ) );

    for( i = 0; i < subscriptionCount; i++ )
    {
        /* Check if this topic filter is already registered. */
        topicMatchParams.pTopicName = pSubscriptionList[ i ].pTopicFilter;
        topicMatchParams.topicNameLength = pSubscriptionList[ i ].topicFilterLength;
        pSubscriptionLink = IotListDouble_FindFirstMatch( &( pMqttConnection->subscriptionList ),
                                                          NULL,
                                                          _topicMatch,
                                                          &topicMatchParams );

        if( pSubscriptionLink != NULL )
        {
            pNewSubscription = IotLink_Container( _mqttSubscription_t, pSubscriptionLink, link );

            /* The lengths of exactly matching topic filters must match. */
            IotMqtt_Assert( pNewSubscription->topicFilterLength == pSubscriptionList[ i ].topicFilterLength );

            /* Replace the callback and packet info with the new parameters. */
            pNewSubscription->callback = pSubscriptionList[ i ].callback;
            pNewSubscription->packetInfo.identifier = subscribePacketIdentifier;
            pNewSubscription->packetInfo.order = i;
        }
        else
        {
            /* Allocate memory for a new subscription. */
            pNewSubscription = IotMqtt_MallocSubscription( sizeof( _mqttSubscription_t ) +
                                                           pSubscriptionList[ i ].topicFilterLength );

            if( pNewSubscription == NULL )
            {
                status = IOT_MQTT_NO_MEMORY;
                break;
            }
            else
            {
                /* Clear the new subscription. */
                ( void ) memset( pNewSubscription,
                                 0x00,
                                 sizeof( _mqttSubscription_t ) + pSubscriptionList[ i ].topicFilterLength );

                /* Set the members of the new subscription and add it to the list. */
                pNewSubscription->packetInfo.identifier = subscribePacketIdentifier;
                pNewSubscription->packetInfo.order = i;
                pNewSubscription->callback = pSubscriptionList[ i ].callback;
                pNewSubscription->topicFilterLength = pSubscriptionList[ i ].topicFilterLength;
                ( void ) memcpy( pNewSubscription->pTopicFilter,
                                 pSubscriptionList[ i ].pTopicFilter,
                                 ( size_t ) ( pSubscriptionList[ i ].topicFilterLength ) );

                IotListDouble_InsertHead( &( pMqttConnection->subscriptionList ),
                                          &( pNewSubscription->link ) );
            }
        }
    }

    IotMutex_Unlock( &( pMqttConnection->subscriptionMutex ) );

    /* If memory allocation failed, remove all previously added subscriptions. */
    if( status != IOT_MQTT_SUCCESS )
    {
        _IotMqtt_RemoveSubscriptionByTopicFilter( pMqttConnection,
                                                  pSubscriptionList,
                                                  i );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    return status;
}

/*-----------------------------------------------------------*/

void _IotMqtt_InvokeSubscriptionCallback( _mqttConnection_t * pMqttConnection,
                                          IotMqttCallbackParam_t * pCallbackParam )
{
    _mqttSubscription_t * pSubscription = NULL;
    IotLink_t * pCurrentLink = NULL, * pNextLink = NULL;
    void * pCallbackContext = NULL;

    void ( * callbackFunction )( void *,
                                 IotMqttCallbackParam_t * ) = NULL;
    _topicMatchParams_t topicMatchParams = { 0 };

    topicMatchParams.pTopicName = pCallbackParam->u.message.info.pTopicName;
    topicMatchParams.topicNameLength = pCallbackParam->u.message.info.topicNameLength;
    topicMatchParams.exactMatchOnly = false;

    /* Prevent any other thread from modifying the subscription list while this
     * function is searching. */
    IotMutex_Lock( &( pMqttConnection->subscriptionMutex ) );

    /* Search the subscription list for all matching subscriptions starting at
     * the list head. */
    while( true )
    {
        pCurrentLink = IotListDouble_FindFirstMatch( &( pMqttConnection->subscriptionList ),
                                                     pCurrentLink,
                                                     _topicMatch,
                                                     &topicMatchParams );

        /* No subscription found. Exit loop. */
        if( pCurrentLink == NULL )
        {
            break;
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }

        /* Subscription found. Calculate pointer to subscription object. */
        pSubscription = IotLink_Container( _mqttSubscription_t, pCurrentLink, link );

        /* Subscription validation should not have allowed a NULL callback function. */
        IotMqtt_Assert( pSubscription->callback.function != NULL );

        /* Increment the subscription's reference count. */
        ( pSubscription->references )++;

        /* Copy the necessary members of the subscription before releasing the
         * subscription list mutex. */
        pCallbackContext = pSubscription->callback.pCallbackContext;
        callbackFunction = pSubscription->callback.function;

        /* Unlock the subscription list mutex. */
        IotMutex_Unlock( &( pMqttConnection->subscriptionMutex ) );

        /* Set the members of the callback parameter. */
        pCallbackParam->mqttConnection = pMqttConnection;
        pCallbackParam->u.message.pTopicFilter = pSubscription->pTopicFilter;
        pCallbackParam->u.message.topicFilterLength = pSubscription->topicFilterLength;

        /* Invoke the subscription callback. */
        callbackFunction( pCallbackContext, pCallbackParam );

        /* Lock the subscription list mutex to decrement the reference count. */
        IotMutex_Lock( &( pMqttConnection->subscriptionMutex ) );

        /* Decrement the reference count. It must still be positive. */
        ( pSubscription->references )--;
        IotMqtt_Assert( pSubscription->references >= 0 );

        /* Save the pointer to the next link in case this subscription is freed. */
        pNextLink = pCurrentLink->pNext;

        /* Remove this subscription if it has no references and the unsubscribed
         * flag is set. */
        if( pSubscription->unsubscribed == true )
        {
            /* An unsubscribed subscription should have been removed from the list. */
            IotMqtt_Assert( IotLink_IsLinked( &( pSubscription->link ) ) == false );

            /* Free subscriptions with no references. */
            if( pSubscription->references == 0 )
            {
                IotMqtt_FreeSubscription( pSubscription );
            }
            else
            {
                EMPTY_ELSE_MARKER;
            }
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }

        /* Move current link pointer. */
        pCurrentLink = pNextLink;
    }

    IotMutex_Unlock( &( pMqttConnection->subscriptionMutex ) );

    _IotMqtt_DecrementConnectionReferences( pMqttConnection );
}

/*-----------------------------------------------------------*/

void _IotMqtt_RemoveSubscriptionByPacket( _mqttConnection_t * pMqttConnection,
                                          uint16_t packetIdentifier,
                                          int32_t order )
{
    _packetMatchParams_t packetMatchParams = { 0 };

    packetMatchParams.packetIdentifier = packetIdentifier;
    packetMatchParams.order = order;

    IotMutex_Lock( &( pMqttConnection->subscriptionMutex ) );
    IotListDouble_RemoveAllMatches( &( pMqttConnection->subscriptionList ),
                                    _packetMatch,
                                    ( void * ) ( &packetMatchParams ),
                                    IotMqtt_FreeSubscription,
                                    offsetof( _mqttSubscription_t, link ) );
    IotMutex_Unlock( &( pMqttConnection->subscriptionMutex ) );
}

/*-----------------------------------------------------------*/

void _IotMqtt_RemoveSubscriptionByTopicFilter( _mqttConnection_t * pMqttConnection,
                                               const IotMqttSubscription_t * pSubscriptionList,
                                               size_t subscriptionCount )
{
    size_t i = 0;
    _mqttSubscription_t * pSubscription = NULL;
    IotLink_t * pSubscriptionLink = NULL;
    _topicMatchParams_t topicMatchParams = { 0 };

    /* Prevent any other thread from modifying the subscription list while this
     * function is running. */
    IotMutex_Lock( &( pMqttConnection->subscriptionMutex ) );

    /* Find and remove each topic filter from the list. */
    for( i = 0; i < subscriptionCount; i++ )
    {
        topicMatchParams.pTopicName = pSubscriptionList[ i ].pTopicFilter;
        topicMatchParams.topicNameLength = pSubscriptionList[ i ].topicFilterLength;
        topicMatchParams.exactMatchOnly = true;

        pSubscriptionLink = IotListDouble_FindFirstMatch( &( pMqttConnection->subscriptionList ),
                                                          NULL,
                                                          _topicMatch,
                                                          &topicMatchParams );

        if( pSubscriptionLink != NULL )
        {
            pSubscription = IotLink_Container( _mqttSubscription_t, pSubscriptionLink, link );

            /* Reference count must not be negative. */
            IotMqtt_Assert( pSubscription->references >= 0 );

            /* Remove subscription from list. */
            IotListDouble_Remove( pSubscriptionLink );

            /* Check the reference count. This subscription cannot be removed if
             * there are subscription callbacks using it. */
            if( pSubscription->references > 0 )
            {
                /* Set the unsubscribed flag. The last active subscription callback
                 * will remove and clean up this subscription. */
                pSubscription->unsubscribed = true;
            }
            else
            {
                /* Free a subscription with no references. */
                IotMqtt_FreeSubscription( pSubscription );
            }
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }

    IotMutex_Unlock( &( pMqttConnection->subscriptionMutex ) );
}

/*-----------------------------------------------------------*/

bool IotMqtt_IsSubscribed( IotMqttConnection_t mqttConnection,
                           const char * pTopicFilter,
                           uint16_t topicFilterLength,
                           IotMqttSubscription_t * const pCurrentSubscription )
{
    bool status = false;
    _mqttSubscription_t * pSubscription = NULL;
    IotLink_t * pSubscriptionLink = NULL;
    _topicMatchParams_t topicMatchParams = { 0 };

    topicMatchParams.pTopicName = pTopicFilter;
    topicMatchParams.topicNameLength = topicFilterLength;
    topicMatchParams.exactMatchOnly = true;

    /* Prevent any other thread from modifying the subscription list while this
     * function is running. */
    IotMutex_Lock( &( mqttConnection->subscriptionMutex ) );

    /* Search for a matching subscription. */
    pSubscriptionLink = IotListDouble_FindFirstMatch( &( mqttConnection->subscriptionList ),
                                                      NULL,
                                                      _topicMatch,
                                                      &topicMatchParams );

    /* Check if a matching subscription was found. */
    if( pSubscriptionLink != NULL )
    {
        pSubscription = IotLink_Container( _mqttSubscription_t, pSubscriptionLink, link );

        /* Copy the matching subscription to the output parameter. */
        if( pCurrentSubscription != NULL )
        {
            pCurrentSubscription->pTopicFilter = pTopicFilter;
            pCurrentSubscription->topicFilterLength = topicFilterLength;
            pCurrentSubscription->qos = IOT_MQTT_QOS_0;
            pCurrentSubscription->callback = pSubscription->callback;
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }

        status = true;
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    IotMutex_Unlock( &( mqttConnection->subscriptionMutex ) );

    return status;
}

/*-----------------------------------------------------------*/

/* Provide access to internal functions and variables if testing. */
#if IOT_BUILD_TESTS == 1
    #include "iot_test_access_mqtt_subscription.c"
#endif
