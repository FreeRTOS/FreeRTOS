/*
 * AWS IoT Jobs V1.0.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file aws_iot_jobs_subscription.c
 * @brief Implements functions for interacting with the Jobs library's
 * subscription list.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* Jobs internal include. */
#include "private/aws_iot_jobs_internal.h"

/* Error handling include. */
#include "iot_error.h"

/* Platform layer includes. */
#include "platform/iot_threads.h"

/* MQTT include. */
#include "iot_mqtt.h"

/*-----------------------------------------------------------*/

/**
 * @brief Match two #_jobsSubscription_t by Thing Name.
 *
 * @param[in] pSubscriptionLink Pointer to the link member of a #_jobsSubscription_t
 * containing the Thing Name to check.
 * @param[in] pMatch Pointer to a `AwsIotThingName_t`.
 *
 * @return `true` if the Thing Names match; `false` otherwise.
 */
static bool _jobsSubscription_match( const IotLink_t * pSubscriptionLink,
                                     void * pMatch );

/*-----------------------------------------------------------*/

/**
 * @brief List of active Jobs subscriptions objects.
 */
IotListDouble_t _AwsIotJobsSubscriptions = { 0 };

/**
 * @brief Protects #_AwsIotJobsSubscriptions from concurrent access.
 */
IotMutex_t _AwsIotJobsSubscriptionsMutex;

/*-----------------------------------------------------------*/

static bool _jobsSubscription_match( const IotLink_t * pSubscriptionLink,
                                     void * pMatch )
{
    bool match = false;

    /* Because this function is called from a container function, the given link
     * must never be NULL. */
    AwsIotJobs_Assert( pSubscriptionLink != NULL );

    const _jobsSubscription_t * pSubscription = IotLink_Container( _jobsSubscription_t,
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

_jobsSubscription_t * _AwsIotJobs_FindSubscription( const char * pThingName,
                                                    size_t thingNameLength,
                                                    bool createIfNotFound )
{
    _jobsSubscription_t * pSubscription = NULL;
    IotLink_t * pSubscriptionLink = NULL;
    AwsIotThingName_t thingName = { 0 };

    thingName.pThingName = pThingName;
    thingName.thingNameLength = thingNameLength;

    /* Search the list for an existing subscription for Thing Name. */
    pSubscriptionLink = IotListDouble_FindFirstMatch( &( _AwsIotJobsSubscriptions ),
                                                      NULL,
                                                      _jobsSubscription_match,
                                                      &thingName );

    /* Check if a subscription was found. */
    if( pSubscriptionLink == NULL )
    {
        if( createIfNotFound == true )
        {
            /* No subscription found. Allocate a new subscription. */
            pSubscription = AwsIotJobs_MallocSubscription( sizeof( _jobsSubscription_t ) + thingNameLength );

            if( pSubscription != NULL )
            {
                /* Clear the new subscription. */
                ( void ) memset( pSubscription, 0x00, sizeof( _jobsSubscription_t ) + thingNameLength );

                /* Set the Thing Name length and copy the Thing Name into the new subscription. */
                pSubscription->thingNameLength = thingNameLength;
                ( void ) memcpy( pSubscription->pThingName, pThingName, thingNameLength );

                /* Add the new subscription to the subscription list. */
                IotListDouble_InsertHead( &( _AwsIotJobsSubscriptions ),
                                          &( pSubscription->link ) );

                IotLogDebug( "Created new Jobs subscriptions object for %.*s.",
                             thingNameLength,
                             pThingName );
            }
            else
            {
                IotLogError( "Failed to allocate memory for %.*s Jobs subscriptions.",
                             thingNameLength,
                             pThingName );
            }
        }
    }
    else
    {
        IotLogDebug( "Found existing Jobs subscriptions object for %.*s.",
                     thingNameLength,
                     pThingName );

        pSubscription = IotLink_Container( _jobsSubscription_t, pSubscriptionLink, link );
    }

    return pSubscription;
}

/*-----------------------------------------------------------*/

void _AwsIotJobs_RemoveSubscription( _jobsSubscription_t * pSubscription,
                                     _jobsSubscription_t ** pRemovedSubscription )
{
    IOT_FUNCTION_ENTRY( bool, true );
    int32_t i = 0, callbackIndex = 0;

    IotLogDebug( "Checking if subscription object for %.*s can be removed.",
                 pSubscription->thingNameLength,
                 pSubscription->pThingName );

    /* Check for active operations. If any Jobs operation's subscription
     * reference count is not 0, then the subscription cannot be removed. */
    for( i = 0; i < JOBS_OPERATION_COUNT; i++ )
    {
        if( pSubscription->operationReferences[ i ] > 0 )
        {
            IotLogDebug( "Reference count %ld for %.*s subscription object. "
                         "Subscription cannot be removed yet.",
                         ( long int ) pSubscription->operationReferences[ i ],
                         pSubscription->thingNameLength,
                         pSubscription->pThingName );

            IOT_SET_AND_GOTO_CLEANUP( false );
        }
        else if( pSubscription->operationReferences[ i ] == AWS_IOT_PERSISTENT_SUBSCRIPTION )
        {
            IotLogDebug( "Subscription object for %.*s has persistent subscriptions. "
                         "Subscription will not be removed.",
                         pSubscription->thingNameLength,
                         pSubscription->pThingName );

            IOT_SET_AND_GOTO_CLEANUP( false );
        }
    }

    /* Check for active subscriptions. If any Jobs callbacks are active, then the
     * subscription cannot be removed. */
    if( pSubscription->callbackReferences > 0 )
    {
        IotLogDebug( "Notify callbacks are using %.*s subscription object. "
                     "Subscription cannot be removed yet.",
                     pSubscription->thingNameLength,
                     pSubscription->pThingName );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    for( i = 0; i < JOBS_CALLBACK_COUNT; i++ )
    {
        for( callbackIndex = 0; callbackIndex < AWS_IOT_JOBS_NOTIFY_CALLBACKS; callbackIndex++ )
        {
            if( pSubscription->callbacks[ i ][ callbackIndex ].function != NULL )
            {
                IotLogDebug( "Found active Jobs %s callback for %.*s subscription object. "
                             "Subscription cannot be removed yet.",
                             _pAwsIotJobsCallbackNames[ i ],
                             pSubscription->thingNameLength,
                             pSubscription->pThingName );

                IOT_SET_AND_GOTO_CLEANUP( false );
            }
        }
    }

    /* Remove the subscription if unused. */
    IOT_FUNCTION_CLEANUP_BEGIN();

    if( status == true )
    {
        /* No Jobs operation subscription references or active Jobs callbacks.
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
            _AwsIotJobs_DestroySubscription( pSubscription );
        }
    }
}

/*-----------------------------------------------------------*/

void _AwsIotJobs_DestroySubscription( void * pData )
{
    _jobsSubscription_t * pSubscription = ( _jobsSubscription_t * ) pData;

    /* Free the topic buffer if allocated. */
    if( pSubscription->pTopicBuffer != NULL )
    {
        AwsIotJobs_FreeString( pSubscription->pTopicBuffer );
    }

    /* Free memory used by subscription. */
    AwsIotJobs_FreeSubscription( pSubscription );
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t _AwsIotJobs_IncrementReferences( _jobsOperation_t * pOperation,
                                                   char * pTopicBuffer,
                                                   uint16_t operationTopicLength,
                                                   AwsIotMqttCallbackFunction_t callback )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_SUCCESS );
    const _jobsOperationType_t type = pOperation->type;
    _jobsSubscription_t * pSubscription = pOperation->pSubscription;
    IotMqttError_t subscriptionStatus = IOT_MQTT_STATUS_PENDING;
    AwsIotSubscriptionInfo_t subscriptionInfo = { 0 };

    /* Do nothing if this operation has persistent subscriptions. */
    if( pSubscription->operationReferences[ type ] == AWS_IOT_PERSISTENT_SUBSCRIPTION )
    {
        IotLogDebug( "Jobs %s for %.*s has persistent subscriptions. Reference "
                     "count will not be incremented.",
                     _pAwsIotJobsOperationNames[ type ],
                     pSubscription->thingNameLength,
                     pSubscription->pThingName );

        IOT_GOTO_CLEANUP();
    }

    /* When persistent subscriptions are not present, the reference count must
     * not be negative. */
    AwsIotJobs_Assert( pSubscription->operationReferences[ type ] >= 0 );

    /* Check if there are any existing references for this operation. */
    if( pSubscription->operationReferences[ type ] == 0 )
    {
        /* Set the parameters needed to add subscriptions. */
        subscriptionInfo.mqttConnection = pOperation->mqttConnection;
        subscriptionInfo.callbackFunction = callback;
        subscriptionInfo.timeout = _AwsIotJobsMqttTimeoutMs;
        subscriptionInfo.pTopicFilterBase = pTopicBuffer;
        subscriptionInfo.topicFilterBaseLength = operationTopicLength;

        subscriptionStatus = AwsIot_ModifySubscriptions( IotMqtt_SubscribeSync,
                                                         &subscriptionInfo );

        /* Convert MQTT return code to Jobs return code. */
        switch( subscriptionStatus )
        {
            case IOT_MQTT_SUCCESS:
                status = AWS_IOT_JOBS_SUCCESS;
                break;

            case IOT_MQTT_NO_MEMORY:
                status = AWS_IOT_JOBS_NO_MEMORY;
                break;

            default:
                status = AWS_IOT_JOBS_MQTT_ERROR;
                break;
        }

        if( status != AWS_IOT_JOBS_SUCCESS )
        {
            IOT_GOTO_CLEANUP();
        }
    }

    /* Increment the number of subscription references for this operation when
     * the keep subscriptions flag is not set. */
    if( ( pOperation->flags & AWS_IOT_JOBS_FLAG_KEEP_SUBSCRIPTIONS ) == 0 )
    {
        ( pSubscription->operationReferences[ type ] )++;

        IotLogDebug( "Jobs %s subscriptions for %.*s now has count %d.",
                     _pAwsIotJobsOperationNames[ type ],
                     pSubscription->thingNameLength,
                     pSubscription->pThingName,
                     pSubscription->operationReferences[ type ] );
    }
    /* Otherwise, set the persistent subscriptions flag. */
    else
    {
        pSubscription->operationReferences[ type ] = AWS_IOT_PERSISTENT_SUBSCRIPTION;

        IotLogDebug( "Set persistent subscriptions flag for Jobs %s of %.*s.",
                     _pAwsIotJobsOperationNames[ type ],
                     pSubscription->thingNameLength,
                     pSubscription->pThingName );
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

void _AwsIotJobs_DecrementReferences( _jobsOperation_t * pOperation,
                                      char * pTopicBuffer,
                                      _jobsSubscription_t ** pRemovedSubscription )
{
    const _jobsOperationType_t type = pOperation->type;
    _jobsSubscription_t * pSubscription = pOperation->pSubscription;
    uint16_t operationTopicLength = 0;
    AwsIotSubscriptionInfo_t subscriptionInfo = { 0 };
    AwsIotJobsRequestInfo_t requestInfo = AWS_IOT_JOBS_REQUEST_INFO_INITIALIZER;

    /* Do nothing if this Jobs operation has persistent subscriptions. */
    if( pSubscription->operationReferences[ type ] != AWS_IOT_PERSISTENT_SUBSCRIPTION )
    {
        /* Decrement the number of subscription references for this operation.
         * Ensure that it's positive. */
        ( pSubscription->operationReferences[ type ] )--;
        AwsIotJobs_Assert( pSubscription->operationReferences[ type ] >= 0 );

        /* Check if the number of references has reached 0. */
        if( pSubscription->operationReferences[ type ] == 0 )
        {
            IotLogDebug( "Reference count for %.*s %s is 0. Unsubscribing.",
                         pSubscription->thingNameLength,
                         pSubscription->pThingName,
                         _pAwsIotJobsOperationNames[ type ] );

            /* Subscription must have a topic buffer. */
            AwsIotJobs_Assert( pSubscription->pTopicBuffer != NULL );

            /* Set the parameters needed to generate a Jobs topic. */
            requestInfo.pThingName = pSubscription->pThingName;
            requestInfo.thingNameLength = pSubscription->thingNameLength;
            requestInfo.pJobId = pOperation->pJobId;
            requestInfo.jobIdLength = pOperation->jobIdLength;

            /* Generate the prefix of the Jobs topic. This function will not
             * fail when given a buffer. */
            ( void ) _AwsIotJobs_GenerateJobsTopic( ( _jobsOperationType_t ) type,
                                                    &requestInfo,
                                                    &( pSubscription->pTopicBuffer ),
                                                    &operationTopicLength );

            /* Set the parameters needed to remove subscriptions. */
            subscriptionInfo.mqttConnection = pOperation->mqttConnection;
            subscriptionInfo.timeout = _AwsIotJobsMqttTimeoutMs;
            subscriptionInfo.pTopicFilterBase = pTopicBuffer;
            subscriptionInfo.topicFilterBaseLength = operationTopicLength;

            ( void ) AwsIot_ModifySubscriptions( IotMqtt_UnsubscribeSync,
                                                 &subscriptionInfo );
        }

        /* Check if this subscription should be deleted. */
        _AwsIotJobs_RemoveSubscription( pSubscription,
                                        pRemovedSubscription );
    }
    else
    {
        IotLogDebug( "Jobs %s for %.*s has persistent subscriptions. Reference "
                     "count will not be decremented.",
                     _pAwsIotJobsOperationNames[ type ],
                     pSubscription->thingNameLength,
                     pSubscription->pThingName );
    }
}

/*-----------------------------------------------------------*/

AwsIotJobsError_t AwsIotJobs_RemovePersistentSubscriptions( const AwsIotJobsRequestInfo_t * pRequestInfo,
                                                            uint32_t flags )
{
    IOT_FUNCTION_ENTRY( AwsIotJobsError_t, AWS_IOT_JOBS_SUCCESS );
    int32_t i = 0;
    uint16_t operationTopicLength = 0;
    IotMqttError_t unsubscribeStatus = IOT_MQTT_STATUS_PENDING;
    AwsIotSubscriptionInfo_t subscriptionInfo = { 0 };
    _jobsSubscription_t * pSubscription = NULL;
    IotLink_t * pSubscriptionLink = NULL;
    AwsIotThingName_t thingName = { 0 };

    thingName.pThingName = pRequestInfo->pThingName;
    thingName.thingNameLength = pRequestInfo->thingNameLength;

    IotLogInfo( "Removing persistent subscriptions for %.*s.",
                pRequestInfo->thingNameLength,
                pRequestInfo->pThingName );

    /* Check parameters. */
    if( pRequestInfo->mqttConnection == IOT_MQTT_CONNECTION_INITIALIZER )
    {
        IotLogError( "MQTT connection is not initialized." );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
    }

    if( AwsIot_ValidateThingName( pRequestInfo->pThingName,
                                  pRequestInfo->thingNameLength ) == false )
    {
        IotLogError( "Thing Name is not valid." );

        IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
    }

    if( ( ( flags & AWS_IOT_JOBS_FLAG_REMOVE_DESCRIBE_SUBSCRIPTIONS ) != 0 ) ||
        ( ( flags & AWS_IOT_JOBS_FLAG_REMOVE_UPDATE_SUBSCRIPTIONS ) != 0 ) )
    {
        if( ( pRequestInfo->pJobId == NULL ) || ( pRequestInfo->jobIdLength == 0 ) )
        {
            IotLogError( "Job ID must be set." );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }

        if( pRequestInfo->jobIdLength > JOBS_MAX_ID_LENGTH )
        {
            IotLogError( "Job ID cannot be longer than %d.",
                         JOBS_MAX_ID_LENGTH );

            IOT_SET_AND_GOTO_CLEANUP( AWS_IOT_JOBS_BAD_PARAMETER );
        }
    }

    IotMutex_Lock( &( _AwsIotJobsSubscriptionsMutex ) );

    /* Search the list for an existing subscription for Thing Name. */
    pSubscriptionLink = IotListDouble_FindFirstMatch( &( _AwsIotJobsSubscriptions ),
                                                      NULL,
                                                      _jobsSubscription_match,
                                                      &thingName );

    if( pSubscriptionLink != NULL )
    {
        IotLogDebug( "Found subscription object for %.*s. Checking for persistent "
                     "subscriptions to remove.",
                     pRequestInfo->thingNameLength,
                     pRequestInfo->pThingName );

        pSubscription = IotLink_Container( _jobsSubscription_t, pSubscriptionLink, link );

        for( i = 0; i < JOBS_OPERATION_COUNT; i++ )
        {
            if( ( flags & ( 0x1UL << i ) ) != 0 )
            {
                IotLogDebug( "Removing %.*s %s persistent subscriptions.",
                             pRequestInfo->thingNameLength,
                             pRequestInfo->pThingName,
                             _pAwsIotJobsOperationNames[ i ] );

                /* Subscription must have a topic buffer. */
                AwsIotJobs_Assert( pSubscription->pTopicBuffer != NULL );

                if( pSubscription->operationReferences[ i ] == AWS_IOT_PERSISTENT_SUBSCRIPTION )
                {
                    /* Generate the prefix of the Jobs topic. This function will not
                     * fail when given a buffer. */
                    ( void ) _AwsIotJobs_GenerateJobsTopic( ( _jobsOperationType_t ) i,
                                                            pRequestInfo,
                                                            &( pSubscription->pTopicBuffer ),
                                                            &operationTopicLength );

                    /* Set the parameters needed to remove subscriptions. */
                    subscriptionInfo.mqttConnection = pRequestInfo->mqttConnection;
                    subscriptionInfo.timeout = _AwsIotJobsMqttTimeoutMs;
                    subscriptionInfo.pTopicFilterBase = pSubscription->pTopicBuffer;
                    subscriptionInfo.topicFilterBaseLength = operationTopicLength;

                    unsubscribeStatus = AwsIot_ModifySubscriptions( IotMqtt_UnsubscribeSync,
                                                                    &subscriptionInfo );

                    /* Convert MQTT return code to Shadow return code. */
                    switch( unsubscribeStatus )
                    {
                        case IOT_MQTT_SUCCESS:
                            status = AWS_IOT_JOBS_SUCCESS;
                            break;

                        case IOT_MQTT_NO_MEMORY:
                            status = AWS_IOT_JOBS_NO_MEMORY;
                            break;

                        default:
                            status = AWS_IOT_JOBS_MQTT_ERROR;
                            break;
                    }

                    if( status != AWS_IOT_JOBS_SUCCESS )
                    {
                        break;
                    }

                    /* Clear the persistent subscriptions flag and check if the
                     * subscription can be removed. */
                    pSubscription->operationReferences[ i ] = 0;
                    _AwsIotJobs_RemoveSubscription( pSubscription, NULL );
                }
                else
                {
                    IotLogDebug( "%.*s %s does not have persistent subscriptions.",
                                 pRequestInfo->thingNameLength,
                                 pRequestInfo->pThingName,
                                 _pAwsIotJobsOperationNames[ i ] );
                }
            }
        }
    }
    else
    {
        IotLogWarn( "No subscription object found for %.*s",
                    pRequestInfo->thingNameLength,
                    pRequestInfo->pThingName );
    }

    IotMutex_Unlock( &( _AwsIotJobsSubscriptionsMutex ) );

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/
