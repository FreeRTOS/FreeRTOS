/*
 * IoT MQTT V2.1.1
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
    int32_t order;             /**< Order to match. Set to #MQTT_REMOVE_ALL_SUBSCRIPTIONS to ignore. */
} _packetMatchParams_t;

/*-----------------------------------------------------------*/

/**
 * @brief Handle special corner cases regarding wildcards at the end of topic
 * filters, as documented by the MQTT protocol spec.
 *
 * @param[in] pTopicFilter The topic filter containing the wildcard.
 * @param[in] nameIndex Index of the topic name being examined.
 * @param[in] filterIndex Index of the topic filter being examined.
 * @param[in] topicNameLength Length of the topic name being examined.
 * @param[in] topicFilterLength Length of the topic filter being examined.
 * @param[out] pMatch Whether the topic filter and topic name match.
 *
 * @return `true` if the caller of this function should exit; `false` if the caller
 * should continue parsing the topics.
 */
static bool _matchEndWildcards( const char * pTopicFilter,
                                uint16_t topicNameLength,
                                uint16_t topicFilterLength,
                                uint16_t nameIndex,
                                uint16_t filterIndex,
                                bool * pMatch );

/**
 * @brief Attempt to match characters in a topic filter by wildcards.
 *
 * @param[in] pTopicFilter The topic filter containing the wildcard.
 * @param[in] pTopicName The topic name to check.
 * @param[in] topicNameLength Length of the topic name.
 * @param[in] filterIndex Index of the wildcard in the topic filter.
 * @param[in,out] pNameIndex Index of character in topic name. This variable is
 * advanced for `+` wildcards.
 * @param[out] pMatch Whether the topic filter and topic name match.
 *
 * @return `true` if the caller of this function should exit; `false` if the caller
 * should continue parsing the topics.
 */
static bool _matchWildcards( const char * pTopicFilter,
                             const char * pTopicName,
                             uint16_t topicNameLength,
                             uint16_t filterIndex,
                             uint16_t * pNameIndex,
                             bool * pMatch );

/**
 * @brief Match a topic name and topic filter while allowing the use of wildcards.
 *
 * @param[in] pTopicName The topic name to check.
 * @param[in] topicNameLength Length of `pTopicName`.
 * @param[in] pTopicFilter The topic filter to check.
 * @param[in] topicFilterLength Length of `pTopicFilter`.
 *
 * @return `true` if the topic name and topic filter match; `false` otherwise.
 */
static bool _topicFilterMatch( const char * pTopicName,
                               uint16_t topicNameLength,
                               const char * pTopicFilter,
                               uint16_t topicFilterLength );

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
static bool _topicMatch( const IotLink_t * const pSubscriptionLink,
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
static bool _packetMatch( const IotLink_t * const pSubscriptionLink,
                          void * pMatch );

/*-----------------------------------------------------------*/

static bool _matchEndWildcards( const char * pTopicFilter,
                                uint16_t topicNameLength,
                                uint16_t topicFilterLength,
                                uint16_t nameIndex,
                                uint16_t filterIndex,
                                bool * pMatch )
{
    bool status = false, endChar = false;

    /* Determine if the last character is reached for both topic name and topic
     * filter for the '#' wildcard. */
    endChar = ( nameIndex == ( topicNameLength - 1U ) ) && ( filterIndex == ( topicFilterLength - 3U ) );

    if( endChar == true )
    {
        /* Determine if the topic filter ends with the '#' wildcard. */
        status = ( pTopicFilter[ filterIndex + 2U ] == '#' );
    }

    if( status == false )
    {
        /* Determine if the last character is reached for both topic name and topic
         * filter for the '+' wildcard. */
        endChar = ( nameIndex == ( topicNameLength - 1U ) ) && ( filterIndex == ( topicFilterLength - 2U ) );

        if( endChar == true )
        {
            /* Filter "sport/+" also matches the "sport/" but not "sport". */
            status = ( pTopicFilter[ filterIndex + 1U ] == '+' );
        }
    }

    *pMatch = status;

    return status;
}

/*-----------------------------------------------------------*/

static bool _matchWildcards( const char * pTopicFilter,
                             const char * pTopicName,
                             uint16_t topicNameLength,
                             uint16_t filterIndex,
                             uint16_t * pNameIndex,
                             bool * pMatch )
{
    bool status = false;

    /* Check for wildcards. */
    if( pTopicFilter[ filterIndex ] == '+' )
    {
        /* Move topic name index to the end of the current level.
         * This is identified by '/'. */
        while( ( *pNameIndex < topicNameLength ) && ( pTopicName[ *pNameIndex ] != '/' ) )
        {
            ( *pNameIndex )++;
        }

        ( *pNameIndex )--;
    }
    else if( pTopicFilter[ filterIndex ] == '#' )
    {
        /* Subsequent characters don't need to be checked for the
         * multi-level wildcard. */
        *pMatch = true;
        status = true;
    }
    else
    {
        /* Any character mismatch other than '+' or '#' means the topic
         * name does not match the topic filter. */
        *pMatch = false;
        status = true;
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool _topicFilterMatch( const char * pTopicName,
                               uint16_t topicNameLength,
                               const char * pTopicFilter,
                               uint16_t topicFilterLength )
{
    bool status = false, matchFound = false;
    uint16_t nameIndex = 0, filterIndex = 0;

    while( ( nameIndex < topicNameLength ) && ( filterIndex < topicFilterLength ) )
    {
        /* Check if the character in the topic name matches the corresponding
         * character in the topic filter string. */
        if( pTopicName[ nameIndex ] == pTopicFilter[ filterIndex ] )
        {
            /* Handle special corner cases regarding wildcards at the end of
             * topic filters, as documented by the MQTT protocol spec. */
            matchFound = _matchEndWildcards( pTopicFilter,
                                             topicNameLength,
                                             topicFilterLength,
                                             nameIndex,
                                             filterIndex,
                                             &status );
        }
        else
        {
            /* Check for matching wildcards. */
            matchFound = _matchWildcards( pTopicFilter,
                                          pTopicName,
                                          topicNameLength,
                                          filterIndex,
                                          &nameIndex,
                                          &status );
        }

        if( matchFound == true )
        {
            break;
        }

        /* Increment indexes. */
        nameIndex++;
        filterIndex++;
    }

    if( status == false )
    {
        /* If the end of both strings has been reached, they match. */
        status = ( ( nameIndex == topicNameLength ) && ( filterIndex == topicFilterLength ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool _topicMatch( const IotLink_t * const pSubscriptionLink,
                         void * pMatch )
{
    bool status = false;

    /* This function is called from a container function; the caller
     * will never pass NULL. */
    IotMqtt_Assert( pSubscriptionLink != NULL );

    /* Casting `pSubscriptionLink` to uint8_t * is done only to calculate the
     * starting address of the struct and does not modify the link it points to.
     * Adding parentheses to parameters of IotLink_Container is not applicable
     * because it uses type-casting and offsetof, and would cause compiling errors. */
    /* coverity[misra_c_2012_rule_11_8_violation] */
    /* coverity[misra_c_2012_rule_20_7_violation] */
    /* coverity[caretline] */
    const _mqttSubscription_t * pSubscription = IotLink_Container( _mqttSubscription_t,
                                                                   pSubscriptionLink,
                                                                   link );
    const _topicMatchParams_t * pParam = ( _topicMatchParams_t * ) pMatch;

    /* Extract the relevant strings and lengths from parameters. */
    const char * pTopicName = pParam->pTopicName;
    const char * pTopicFilter = pSubscription->pTopicFilter;
    const uint16_t topicNameLength = pParam->topicNameLength;
    const uint16_t topicFilterLength = pSubscription->topicFilterLength;

    /* Check for an exact match. */
    if( topicNameLength == topicFilterLength )
    {
        status = ( strncmp( pTopicName, pTopicFilter, topicNameLength ) == 0 );
    }

    /* If  an exact match is required, return the result of the comparison above.
     * Otherwise, attempt to match with MQTT wildcards in topic filters. */
    if( pParam->exactMatchOnly == false )
    {
        status = _topicFilterMatch( pTopicName, topicNameLength, pTopicFilter, topicFilterLength );
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool _packetMatch( const IotLink_t * const pSubscriptionLink,
                          void * pMatch )
{
    bool match = false;

    /* Because this function is called from a container function, the given link
     * must never be NULL. */
    IotMqtt_Assert( pSubscriptionLink != NULL );

    /* Casting `pSubscriptionLink` to uint8_t * is done only to calculate the
     * starting address of the struct and does not modify the link it points to.
     * Adding parentheses to parameters of IotLink_Container is not applicable
     * because it uses type-casting and offsetof, and would cause compiling errors. */
    /* coverity[misra_c_2012_rule_11_8_violation] */
    /* coverity[misra_c_2012_rule_20_7_violation] */
    /* coverity[caretline] */
    _mqttSubscription_t * pSubscription = IotLink_Container( _mqttSubscription_t,
                                                             pSubscriptionLink,
                                                             link );
    const _packetMatchParams_t * pParam = ( _packetMatchParams_t * ) pMatch;

    /* Compare packet identifiers. */
    if( pParam->packetIdentifier == pSubscription->packetInfo.identifier )
    {
        /* Compare orders if order is not MQTT_REMOVE_ALL_SUBSCRIPTIONS. */
        if( pParam->order == MQTT_REMOVE_ALL_SUBSCRIPTIONS )
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
            /* Adding parentheses to parameters of IotLink_Container is not applicable
             * because it uses type-casting and offsetof, and would cause compiling errors. */
            /* coverity[misra_c_2012_rule_20_7_violation] */
            /* coverity[caretline] */
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

    IotMutex_Unlock( &( pMqttConnection->subscriptionMutex ) );

    /* If memory allocation failed, remove all previously added subscriptions. */
    if( status != IOT_MQTT_SUCCESS )
    {
        _IotMqtt_RemoveSubscriptionByTopicFilter( pMqttConnection,
                                                  pSubscriptionList,
                                                  i );
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

    void ( * callbackFunction )( void * pContext,
                                 IotMqttCallbackParam_t * pParam ) = NULL;
    _topicMatchParams_t topicMatchParams = { 0 };

    /* Set the members of the search parameter. */
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

        /* Subscription found. Calculate pointer to subscription object. */

        /* Adding parentheses to parameters of IotLink_Container is not applicable
         * because it uses type-casting and offsetof, and would cause compiling errors. */
        /* coverity[misra_c_2012_rule_20_7_violation] */
        /* coverity[caretline] */
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

    /* Set the members of the search parameter. */
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
            /* Adding parentheses to parameters of IotLink_Container is not applicable
             * because it uses type-casting and offsetof, and would cause compiling errors. */
            /* coverity[misra_c_2012_rule_20_7_violation] */
            /* coverity[caretline] */
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
    const _mqttSubscription_t * pSubscription = NULL;
    const IotLink_t * pSubscriptionLink = NULL;
    _topicMatchParams_t topicMatchParams = { 0 };

    /* Set the members of the search parameter. */
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
        /* Casting `pSubscriptionLink` to uint8_t * is done only to calculate the
         * starting address of the struct and does not modify the link it points to.
         * Adding parentheses to parameters of IotLink_Container is not applicable
         * because it uses type-casting and offsetof, and would cause compiling errors. */
        /* coverity[misra_c_2012_rule_11_8_violation] */
        /* coverity[misra_c_2012_rule_20_7_violation] */
        /* coverity[caretline] */
        pSubscription = IotLink_Container( _mqttSubscription_t, pSubscriptionLink, link );

        /* Copy the matching subscription to the output parameter. */
        if( pCurrentSubscription != NULL )
        {
            pCurrentSubscription->pTopicFilter = pTopicFilter;
            pCurrentSubscription->topicFilterLength = topicFilterLength;
            pCurrentSubscription->qos = IOT_MQTT_QOS_0;
            pCurrentSubscription->callback = pSubscription->callback;
        }

        status = true;
    }

    IotMutex_Unlock( &( mqttConnection->subscriptionMutex ) );

    return status;
}

/*-----------------------------------------------------------*/

/* Provide access to internal functions and variables if testing. */
/* IOT_BUILD_TESTS is defined outside the code base, e.g. passed in by build command. */
/* coverity[misra_c_2012_rule_20_9_violation] */
/* coverity[caretline] */
#if IOT_BUILD_TESTS == 1
    #include "iot_test_access_mqtt_subscription.c"
#endif
