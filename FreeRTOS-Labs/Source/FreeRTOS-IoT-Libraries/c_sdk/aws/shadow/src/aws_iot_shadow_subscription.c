/*
 * AWS IoT Shadow V2.1.0
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
 */

/**
 * @file aws_iot_shadow_subscription.c
 * @brief Implements functions for interacting with the Shadow library's
 * subscription list.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* Shadow internal include. */
#include "private/aws_iot_shadow_internal.h"

/* Error handling include. */
#include "iot_error.h"

/* Platform layer includes. */
#include "platform/iot_threads.h"

/* MQTT include. */
#include "iot_mqtt.h"

/*-----------------------------------------------------------*/

/**
 * @brief Match two #_shadowSubscription_t by Thing Name.
 *
 * @param[in] pSubscriptionLink Pointer to the link member of a #_shadowSubscription_t
 * containing the Thing Name to check.
 * @param[in] pMatch Pointer to an `AwsIotThingName_t`.
 *
 * @return `true` if the Thing Names match; `false` otherwise.
 */
static bool _shadowSubscription_match( const IotLink_t * pSubscriptionLink,
                                       void * pMatch );

/*-----------------------------------------------------------*/

/**
 * @brief List of active Shadow subscriptions objects.
 */
IotListDouble_t _AwsIotShadowSubscriptions = { 0 };

/**
 * @brief Protects #_AwsIotShadowSubscriptions from concurrent access.
 */
IotMutex_t _AwsIotShadowSubscriptionsMutex;

/*-----------------------------------------------------------*/

static bool _shadowSubscription_match( const IotLink_t * pSubscriptionLink,
                                       void * pMatch )
{
    bool match = false;

    /* Because this function is called from a container function, the given link
     * must never be NULL. */
    AwsIotShadow_Assert( pSubscriptionLink != NULL );

    const _shadowSubscription_t * pSubscription = IotLink_Container( _shadowSubscription_t,
                                                                     pSubscriptionLink,
                                                                     link );
    const AwsIotThingName_t * pThingName = ( AwsIotThingName_t * ) pMatch;

    if( pThingName->thingNameLength == pSubscription->thingNameLength )
    {
        /* Check for matching Thing Names. */
        match = ( strncmp( pThingName->pThingName,
                           pSubscription->pThingName,
                           pThingName->thingNameLength ) == 0 );
    }

    return match;
}

/*-----------------------------------------------------------*/

_shadowSubscription_t * _AwsIotShadow_FindSubscription( const char * pThingName,
                                                        size_t thingNameLength,
                                                        bool createIfNotFound )
{
    _shadowSubscription_t * pSubscription = NULL;
    IotLink_t * pSubscriptionLink = NULL;
    AwsIotThingName_t thingName = { 0 };

    thingName.pThingName = pThingName;
    thingName.thingNameLength = thingNameLength;

    /* Search the list for an existing subscription for Thing Name. */
    pSubscriptionLink = IotListDouble_FindFirstMatch( &( _AwsIotShadowSubscriptions ),
                                                      NULL,
                                                      _shadowSubscription_match,
                                                      &thingName );

    /* Check if a subscription was found. */
    if( pSubscriptionLink == NULL )
    {
        if( createIfNotFound == true )
        {
            /* No subscription found. Allocate a new subscription. */
            pSubscription = AwsIotShadow_MallocSubscription( sizeof( _shadowSubscription_t ) + thingNameLength );

            if( pSubscription != NULL )
            {
                /* Clear the new subscription. */
                ( void ) memset( pSubscription, 0x00, sizeof( _shadowSubscription_t ) + thingNameLength );

                /* Set the Thing Name length and copy the Thing Name into the new subscription. */
                pSubscription->thingNameLength = thingNameLength;
                ( void ) memcpy( pSubscription->pThingName, pThingName, thingNameLength );

                /* Add the new subscription to the subscription list. */
                IotListDouble_InsertHead( &( _AwsIotShadowSubscriptions ),
                                          &( pSubscription->link ) );

                IotLogDebug( "Created new Shadow subscriptions object for %.*s.",
                             thingNameLength,
                             pThingName );
            }
            else
            {
                IotLogError( "Failed to allocate memory for %.*s Shadow subscriptions.",
                             thingNameLength,
                             pThingName );
            }
        }
    }
    else
    {
        IotLogDebug( "Found existing Shadow subscriptions object for %.*s.",
                     thingNameLength,
                     pThingName );

        pSubscription = IotLink_Container( _shadowSubscription_t, pSubscriptionLink, link );
    }

    return pSubscription;
}

/*-----------------------------------------------------------*/

void _AwsIotShadow_RemoveSubscription( _shadowSubscription_t * pSubscription,
                                       _shadowSubscription_t ** pRemovedSubscription )
{
    int32_t i = 0;
    bool removeSubscription = true;

    IotLogDebug( "Checking if subscription object for %.*s can be removed.",
                 pSubscription->thingNameLength,
                 pSubscription->pThingName );

    /* Check for active operations. If any Shadow operation's subscription
     * reference count is not 0, then the subscription cannot be removed. */
    for( i = 0; i < SHADOW_OPERATION_COUNT; i++ )
    {
        if( pSubscription->references[ i ] > 0 )
        {
            IotLogDebug( "Reference count %ld for %.*s subscription object. "
                         "Subscription cannot be removed yet.",
                         ( long int ) pSubscription->references[ i ],
                         pSubscription->thingNameLength,
                         pSubscription->pThingName );

            removeSubscription = false;
        }
        else if( pSubscription->references[ i ] == AWS_IOT_PERSISTENT_SUBSCRIPTION )
        {
            IotLogDebug( "Subscription object for %.*s has persistent subscriptions. "
                         "Subscription will not be removed.",
                         pSubscription->thingNameLength,
                         pSubscription->pThingName );

            removeSubscription = false;
        }

        if( removeSubscription == false )
        {
            break;
        }
    }

    /* Check for active subscriptions. If any Shadow callbacks are active, then the
     * subscription cannot be removed. */
    if( removeSubscription == true )
    {
        for( i = 0; i < SHADOW_CALLBACK_COUNT; i++ )
        {
            if( pSubscription->callbacks[ i ].function != NULL )
            {
                IotLogDebug( "Found active Shadow %s callback for %.*s subscription object. "
                             "Subscription cannot be removed yet.",
                             _pAwsIotShadowCallbackNames[ i ],
                             pSubscription->thingNameLength,
                             pSubscription->pThingName );

                removeSubscription = false;
                break;
            }
        }
    }

    /* Remove the subscription if unused. */
    if( removeSubscription == true )
    {
        /* No Shadow operation subscription references or active Shadow callbacks.
         * Remove the subscription object. */
        IotListDouble_Remove( &( pSubscription->link ) );

        IotLogDebug( "Removed subscription object for %.*s.",
                     pSubscription->thingNameLength,
                     pSubscription->pThingName );

        /* If the caller requested the removed subscription, set the output parameter.
         * Otherwise, free the memory used by the subscription. */
        if( pRemovedSubscription != NULL )
        {
            *pRemovedSubscription = pSubscription;
        }
        else
        {
            _AwsIotShadow_DestroySubscription( pSubscription );
        }
    }
}

/*-----------------------------------------------------------*/

void _AwsIotShadow_DestroySubscription( void * pData )
{
    _shadowSubscription_t * pSubscription = ( _shadowSubscription_t * ) pData;

    /* Free the topic buffer if allocated. */
    if( pSubscription->pTopicBuffer != NULL )
    {
        AwsIotShadow_FreeString( pSubscription->pTopicBuffer );
    }

    /* Free memory used by subscription. */
    AwsIotShadow_FreeSubscription( pSubscription );
}

/*-----------------------------------------------------------*/

AwsIotShadowError_t _AwsIotShadow_IncrementReferences( _shadowOperation_t * pOperation,
                                                       char * pTopicBuffer,
                                                       uint16_t operationTopicLength,
                                                       AwsIotMqttCallbackFunction_t callback )
{
    IOT_FUNCTION_ENTRY( AwsIotShadowError_t, AWS_IOT_SHADOW_SUCCESS );
    const _shadowOperationType_t type = pOperation->type;
    _shadowSubscription_t * pSubscription = pOperation->pSubscription;
    IotMqttError_t subscriptionStatus = IOT_MQTT_STATUS_PENDING;
    AwsIotSubscriptionInfo_t subscriptionInfo = { 0 };

    /* Do nothing if this operation has persistent subscriptions. */
    if( pSubscription->references[ type ] == AWS_IOT_PERSISTENT_SUBSCRIPTION )
    {
        IotLogDebug( "Shadow %s for %.*s has persistent subscriptions. Reference "
                     "count will not be incremented.",
                     _pAwsIotShadowOperationNames[ type ],
                     pSubscription->thingNameLength,
                     pSubscription->pThingName );

        IOT_GOTO_CLEANUP();
    }

    /* When persistent subscriptions are not present, the reference count must
     * not be negative. */
    AwsIotShadow_Assert( pSubscription->references[ type ] >= 0 );

    /* Check if there are any existing references for this operation. */
    if( pSubscription->references[ type ] == 0 )
    {
        /* Set the parameters needed to add subscriptions. */
        subscriptionInfo.mqttConnection = pOperation->mqttConnection;
        subscriptionInfo.callbackFunction = callback;
        subscriptionInfo.timeout = _AwsIotShadowMqttTimeoutMs;
        subscriptionInfo.pTopicFilterBase = pTopicBuffer;
        subscriptionInfo.topicFilterBaseLength = operationTopicLength;

        subscriptionStatus = AwsIot_ModifySubscriptions( IotMqtt_SubscribeSync,
                                                         &subscriptionInfo );

        /* Convert MQTT return code to Shadow return code. */
        status = SHADOW_CONVERT_STATUS_CODE_MQTT_TO_SHADOW( subscriptionStatus );

        if( status != AWS_IOT_SHADOW_SUCCESS )
        {
            IOT_GOTO_CLEANUP();
        }
    }

    /* Increment the number of subscription references for this operation when
     * the keep subscriptions flag is not set. */
    if( ( pOperation->flags & AWS_IOT_SHADOW_FLAG_KEEP_SUBSCRIPTIONS ) == 0 )
    {
        ( pSubscription->references[ type ] )++;

        IotLogDebug( "Shadow %s subscriptions for %.*s now has count %d.",
                     _pAwsIotShadowOperationNames[ type ],
                     pSubscription->thingNameLength,
                     pSubscription->pThingName,
                     pSubscription->references[ type ] );
    }
    /* Otherwise, set the persistent subscriptions flag. */
    else
    {
        pSubscription->references[ type ] = AWS_IOT_PERSISTENT_SUBSCRIPTION;

        IotLogDebug( "Set persistent subscriptions flag for Shadow %s of %.*s.",
                     _pAwsIotShadowOperationNames[ type ],
                     pSubscription->thingNameLength,
                     pSubscription->pThingName );
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

void _AwsIotShadow_DecrementReferences( _shadowOperation_t * pOperation,
                                        char * pTopicBuffer,
                                        _shadowSubscription_t ** pRemovedSubscription )
{
    const _shadowOperationType_t type = pOperation->type;
    _shadowSubscription_t * pSubscription = pOperation->pSubscription;
    uint16_t operationTopicLength = 0;
    AwsIotSubscriptionInfo_t subscriptionInfo = { 0 };

    /* Do nothing if this Shadow operation has persistent subscriptions. */
    if( pSubscription->references[ type ] != AWS_IOT_PERSISTENT_SUBSCRIPTION )
    {
        /* Decrement the number of subscription references for this operation.
         * Ensure that it's positive. */
        ( pSubscription->references[ type ] )--;
        AwsIotShadow_Assert( pSubscription->references[ type ] >= 0 );

        /* Check if the number of references has reached 0. */
        if( pSubscription->references[ type ] == 0 )
        {
            IotLogDebug( "Reference count for %.*s %s is 0. Unsubscribing.",
                         pSubscription->thingNameLength,
                         pSubscription->pThingName,
                         _pAwsIotShadowOperationNames[ type ] );

            /* Subscription must have a topic buffer. */
            AwsIotShadow_Assert( pSubscription->pTopicBuffer != NULL );

            /* Generate the prefix of the Shadow topic. This function will not
             * fail when given a buffer. */
            ( void ) _AwsIotShadow_GenerateShadowTopic( ( _shadowOperationType_t ) type,
                                                        pSubscription->pThingName,
                                                        pSubscription->thingNameLength,
                                                        &( pSubscription->pTopicBuffer ),
                                                        &operationTopicLength );

            /* Set the parameters needed to remove subscriptions. */
            subscriptionInfo.mqttConnection = pOperation->mqttConnection;
            subscriptionInfo.timeout = _AwsIotShadowMqttTimeoutMs;
            subscriptionInfo.pTopicFilterBase = pTopicBuffer;
            subscriptionInfo.topicFilterBaseLength = operationTopicLength;

            ( void ) AwsIot_ModifySubscriptions( IotMqtt_UnsubscribeSync,
                                                 &subscriptionInfo );
        }

        /* Check if this subscription should be deleted. */
        _AwsIotShadow_RemoveSubscription( pSubscription,
                                          pRemovedSubscription );
    }
    else
    {
        IotLogDebug( "Shadow %s for %.*s has persistent subscriptions. Reference "
                     "count will not be decremented.",
                     _pAwsIotShadowOperationNames[ type ],
                     pSubscription->thingNameLength,
                     pSubscription->pThingName );
    }
}

/*-----------------------------------------------------------*/

AwsIotShadowError_t AwsIotShadow_RemovePersistentSubscriptions( IotMqttConnection_t mqttConnection,
                                                                const char * pThingName,
                                                                size_t thingNameLength,
                                                                uint32_t flags )
{
    int32_t i = 0;
    uint16_t operationTopicLength = 0;
    AwsIotShadowError_t status = AWS_IOT_SHADOW_STATUS_PENDING;
    IotMqttError_t unsubscribeStatus = IOT_MQTT_STATUS_PENDING;
    AwsIotSubscriptionInfo_t subscriptionInfo = { 0 };
    _shadowSubscription_t * pSubscription = NULL;
    IotLink_t * pSubscriptionLink = NULL;
    AwsIotThingName_t thingName = { 0 };

    thingName.pThingName = pThingName;
    thingName.thingNameLength = thingNameLength;

    IotLogInfo( "Removing persistent subscriptions for %.*s.",
                thingNameLength,
                pThingName );

    IotMutex_Lock( &( _AwsIotShadowSubscriptionsMutex ) );

    /* Search the list for an existing subscription for Thing Name. */
    pSubscriptionLink = IotListDouble_FindFirstMatch( &( _AwsIotShadowSubscriptions ),
                                                      NULL,
                                                      _shadowSubscription_match,
                                                      &thingName );

    /* Unsubscribe from operation subscriptions if found. */
    if( pSubscriptionLink != NULL )
    {
        IotLogDebug( "Found subscription object for %.*s. Checking for persistent "
                     "subscriptions to remove.",
                     thingNameLength,
                     pThingName );

        pSubscription = IotLink_Container( _shadowSubscription_t, pSubscriptionLink, link );

        for( i = 0; i < SHADOW_OPERATION_COUNT; i++ )
        {
            if( ( flags & ( 0x1UL << i ) ) != 0 )
            {
                IotLogDebug( "Removing %.*s %s persistent subscriptions.",
                             thingNameLength,
                             pThingName,
                             _pAwsIotShadowOperationNames[ i ] );

                /* Subscription must have a topic buffer. */
                AwsIotShadow_Assert( pSubscription->pTopicBuffer != NULL );

                if( pSubscription->references[ i ] == AWS_IOT_PERSISTENT_SUBSCRIPTION )
                {
                    /* Generate the prefix of the Shadow topic. This function will not
                     * fail when given a buffer. */
                    ( void ) _AwsIotShadow_GenerateShadowTopic( ( _shadowOperationType_t ) i,
                                                                pThingName,
                                                                thingNameLength,
                                                                &( pSubscription->pTopicBuffer ),
                                                                &operationTopicLength );

                    /* Set the parameters needed to remove subscriptions. */
                    subscriptionInfo.mqttConnection = mqttConnection;
                    subscriptionInfo.timeout = _AwsIotShadowMqttTimeoutMs;
                    subscriptionInfo.pTopicFilterBase = pSubscription->pTopicBuffer;
                    subscriptionInfo.topicFilterBaseLength = operationTopicLength;

                    unsubscribeStatus = AwsIot_ModifySubscriptions( IotMqtt_UnsubscribeSync,
                                                                    &subscriptionInfo );

                    /* Convert MQTT return code to Shadow return code. */
                    status = SHADOW_CONVERT_STATUS_CODE_MQTT_TO_SHADOW( unsubscribeStatus );

                    if( status != AWS_IOT_SHADOW_SUCCESS )
                    {
                        break;
                    }

                    /* Clear the persistent subscriptions flag and check if the
                     * subscription can be removed. */
                    pSubscription->references[ i ] = 0;
                    _AwsIotShadow_RemoveSubscription( pSubscription, NULL );
                }
                else
                {
                    IotLogDebug( "%.*s %s does not have persistent subscriptions.",
                                 thingNameLength,
                                 pThingName,
                                 _pAwsIotShadowOperationNames[ i ] );
                }
            }
        }
    }
    else
    {
        IotLogWarn( "No subscription object found for %.*s",
                    thingNameLength,
                    pThingName );
    }

    IotMutex_Unlock( &( _AwsIotShadowSubscriptionsMutex ) );

    return status;
}

/*-----------------------------------------------------------*/
