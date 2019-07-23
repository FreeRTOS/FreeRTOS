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
 * @file iot_mqtt_operation.c
 * @brief Implements functions that process MQTT operations.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* Error handling include. */
#include "private/iot_error.h"

/* MQTT internal include. */
#include "private/iot_mqtt_internal.h"

/* Platform layer includes. */
#include "platform/iot_clock.h"
#include "platform/iot_threads.h"

/*-----------------------------------------------------------*/

/**
 * @brief First parameter to #_mqttOperation_match.
 */
typedef struct _operationMatchParam
{
    IotMqttOperationType_t type;        /**< @brief The type of operation to look for. */
    const uint16_t * pPacketIdentifier; /**< @brief The packet identifier associated with the operation.
                                         * Set to `NULL` to ignore packet identifier. */
} _operationMatchParam_t;

/*-----------------------------------------------------------*/

/**
 * @brief Match an MQTT operation by type and packet identifier.
 *
 * @param[in] pOperationLink Pointer to the link member of an #_mqttOperation_t.
 * @param[in] pMatch Pointer to an #_operationMatchParam_t.
 *
 * @return `true` if the operation matches the parameters in `pArgument`; `false`
 * otherwise.
 */
static bool _mqttOperation_match( const IotLink_t * pOperationLink,
                                  void * pMatch );

/**
 * @brief Check if an operation with retry has exceeded its retry limit.
 *
 * If a PUBLISH operation is available for retry, this function also sets any
 * necessary DUP flags.
 *
 * @param[in] pOperation The operation to check.
 *
 * @return `true` if the operation may be retried; `false` otherwise.
 */
static bool _checkRetryLimit( _mqttOperation_t * pOperation );

/**
 * @brief Schedule the next send of an operation with retry.
 *
 * @param[in] pOperation The operation to schedule.
 *
 * @return `true` if the reschedule succeeded; `false` otherwise.
 */
static bool _scheduleNextRetry( _mqttOperation_t * pOperation );

/*-----------------------------------------------------------*/

static bool _mqttOperation_match( const IotLink_t * pOperationLink,
                                  void * pMatch )
{
    bool match = false;

    /* Because this function is called from a container function, the given link
     * must never be NULL. */
    IotMqtt_Assert( pOperationLink != NULL );

    _mqttOperation_t * pOperation = IotLink_Container( _mqttOperation_t,
                                                       pOperationLink,
                                                       link );
    _operationMatchParam_t * pParam = ( _operationMatchParam_t * ) pMatch;

    /* Check for matching operations. */
    if( pParam->type == pOperation->u.operation.type )
    {
        /* Check for matching packet identifiers. */
        if( pParam->pPacketIdentifier == NULL )
        {
            match = true;
        }
        else
        {
            match = ( *( pParam->pPacketIdentifier ) == pOperation->u.operation.packetIdentifier );
        }
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    return match;
}

/*-----------------------------------------------------------*/

static bool _checkRetryLimit( _mqttOperation_t * pOperation )
{
    _mqttConnection_t * pMqttConnection = pOperation->pMqttConnection;
    bool status = true;

    /* Choose a set DUP function. */
    void ( * publishSetDup )( uint8_t *,
                              uint8_t *,
                              uint16_t * ) = _IotMqtt_PublishSetDup;

    #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
        if( pMqttConnection->pSerializer != NULL )
        {
            if( pMqttConnection->pSerializer->serialize.publishSetDup != NULL )
            {
                publishSetDup = pMqttConnection->pSerializer->serialize.publishSetDup;
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
    #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

    /* Only PUBLISH may be retried. */
    IotMqtt_Assert( pOperation->u.operation.type == IOT_MQTT_PUBLISH_TO_SERVER );

    /* Check if the retry limit is exhausted. */
    if( pOperation->u.operation.retry.count > pOperation->u.operation.retry.limit )
    {
        /* The retry count may be at most one more than the retry limit, which
         * accounts for the final check for a PUBACK. */
        IotMqtt_Assert( pOperation->u.operation.retry.count == pOperation->u.operation.retry.limit + 1 );

        IotLogDebug( "(MQTT connection %p, PUBLISH operation %p) No response received after %lu retries.",
                     pMqttConnection,
                     pOperation,
                     pOperation->u.operation.retry.limit );

        status = false;
    }
    /* Check if this is the first retry. */
    else if( pOperation->u.operation.retry.count == 1 )
    {
        /* Always set the DUP flag on the first retry. */
        publishSetDup( pOperation->u.operation.pMqttPacket,
                       pOperation->u.operation.pPacketIdentifierHigh,
                       &( pOperation->u.operation.packetIdentifier ) );
    }
    else
    {
        /* In AWS IoT MQTT mode, the DUP flag (really a change to the packet
         * identifier) must be reset on every retry. */
        if( pMqttConnection->awsIotMqttMode == true )
        {
            publishSetDup( pOperation->u.operation.pMqttPacket,
                           pOperation->u.operation.pPacketIdentifierHigh,
                           &( pOperation->u.operation.packetIdentifier ) );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool _scheduleNextRetry( _mqttOperation_t * pOperation )
{
    bool firstRetry = false;
    uint32_t scheduleDelay = 0;
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    _mqttConnection_t * pMqttConnection = pOperation->pMqttConnection;

    /* This function should never be called with retry count greater than
     * retry limit. */
    IotMqtt_Assert( pOperation->u.operation.retry.count <= pOperation->u.operation.retry.limit );

    /* Increment the retry count. */
    ( pOperation->u.operation.retry.count )++;

    /* Check for a response shortly for the final retry. Otherwise, calculate the
     * next retry period. */
    if( pOperation->u.operation.retry.count > pOperation->u.operation.retry.limit )
    {
        scheduleDelay = IOT_MQTT_RESPONSE_WAIT_MS;

        IotLogDebug( "(MQTT connection %p, PUBLISH operation %p) Final retry was sent. Will check "
                     "for response in %d ms.",
                     pMqttConnection,
                     pOperation,
                     IOT_MQTT_RESPONSE_WAIT_MS );
    }
    else
    {
        scheduleDelay = pOperation->u.operation.retry.nextPeriod;

        /* Double the retry period, subject to a ceiling value. */
        pOperation->u.operation.retry.nextPeriod *= 2;

        if( pOperation->u.operation.retry.nextPeriod > IOT_MQTT_RETRY_MS_CEILING )
        {
            pOperation->u.operation.retry.nextPeriod = IOT_MQTT_RETRY_MS_CEILING;
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }

        IotLogDebug( "(MQTT connection %p, PUBLISH operation %p) Scheduling retry %lu of %lu in %lu ms.",
                     pMqttConnection,
                     pOperation,
                     ( unsigned long ) pOperation->u.operation.retry.count,
                     ( unsigned long ) pOperation->u.operation.retry.limit,
                     ( unsigned long ) scheduleDelay );

        /* Check if this is the first retry. */
        firstRetry = ( pOperation->u.operation.retry.count == 1 );

        /* On the first retry, the PUBLISH will be moved from the pending processing
         * list to the pending responses list. Lock the connection references mutex
         * to manipulate the lists. */
        if( firstRetry == true )
        {
            IotMutex_Lock( &( pMqttConnection->referencesMutex ) );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }

    /* Reschedule the PUBLISH for another send. */
    status = _IotMqtt_ScheduleOperation( pOperation,
                                         _IotMqtt_ProcessSend,
                                         scheduleDelay );

    /* Check for successful reschedule. */
    if( status == IOT_MQTT_SUCCESS )
    {
        /* Move a successfully rescheduled PUBLISH from the pending processing
         * list to the pending responses list on the first retry. */
        if( firstRetry == true )
        {
            /* Operation must be linked. */
            IotMqtt_Assert( IotLink_IsLinked( &( pOperation->link ) ) == true );

            /* Transfer to pending response list. */
            IotListDouble_Remove( &( pOperation->link ) );
            IotListDouble_InsertHead( &( pMqttConnection->pendingResponse ),
                                      &( pOperation->link ) );
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

    /* The references mutex only needs to be unlocked on the first retry, since
     * only the first retry manipulates the connection lists. */
    if( firstRetry == true )
    {
        IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    return( status == IOT_MQTT_SUCCESS );
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_CreateOperation( _mqttConnection_t * pMqttConnection,
                                         uint32_t flags,
                                         const IotMqttCallbackInfo_t * pCallbackInfo,
                                         _mqttOperation_t ** pNewOperation )
{
    IOT_FUNCTION_ENTRY( IotMqttError_t, IOT_MQTT_SUCCESS );
    bool decrementOnError = false;
    _mqttOperation_t * pOperation = NULL;
    bool waitable = ( ( flags & IOT_MQTT_FLAG_WAITABLE ) == IOT_MQTT_FLAG_WAITABLE );

    /* If the waitable flag is set, make sure that there's no callback. */
    if( waitable == true )
    {
        if( pCallbackInfo != NULL )
        {
            IotLogError( "Callback should not be set for a waitable operation." );

            return IOT_MQTT_BAD_PARAMETER;
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

    IotLogDebug( "(MQTT connection %p) Creating new operation record.",
                 pMqttConnection );

    /* Increment the reference count for the MQTT connection when creating a new
     * operation. */
    if( _IotMqtt_IncrementConnectionReferences( pMqttConnection ) == false )
    {
        IotLogError( "(MQTT connection %p) New operation record cannot be created"
                     " for a closed connection",
                     pMqttConnection );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_NETWORK_ERROR );
    }
    else
    {
        /* Reference count will need to be decremented on error. */
        decrementOnError = true;
    }

    /* Allocate memory for a new operation. */
    pOperation = IotMqtt_MallocOperation( sizeof( _mqttOperation_t ) );

    if( pOperation == NULL )
    {
        IotLogError( "(MQTT connection %p) Failed to allocate memory for new "
                     "operation record.",
                     pMqttConnection );

        IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_NO_MEMORY );
    }
    else
    {
        /* Clear the operation data. */
        ( void ) memset( pOperation, 0x00, sizeof( _mqttOperation_t ) );

        /* Initialize some members of the new operation. */
        pOperation->pMqttConnection = pMqttConnection;
        pOperation->u.operation.jobReference = 1;
        pOperation->u.operation.flags = flags;
        pOperation->u.operation.status = IOT_MQTT_STATUS_PENDING;
    }

    /* Check if the waitable flag is set. If it is, create a semaphore to
     * wait on. */
    if( waitable == true )
    {
        /* Create a semaphore to wait on for a waitable operation. */
        if( IotSemaphore_Create( &( pOperation->u.operation.notify.waitSemaphore ), 0, 1 ) == false )
        {
            IotLogError( "(MQTT connection %p) Failed to create semaphore for "
                         "waitable operation.",
                         pMqttConnection );

            IOT_SET_AND_GOTO_CLEANUP( IOT_MQTT_NO_MEMORY );
        }
        else
        {
            /* A waitable operation is created with an additional reference for the
             * Wait function. */
            ( pOperation->u.operation.jobReference )++;
        }
    }
    else
    {
        /* If the waitable flag isn't set but a callback is, copy the callback
         * information. */
        if( pCallbackInfo != NULL )
        {
            pOperation->u.operation.notify.callback = *pCallbackInfo;
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }

    /* Add this operation to the MQTT connection's operation list. */
    IotMutex_Lock( &( pMqttConnection->referencesMutex ) );
    IotListDouble_InsertHead( &( pMqttConnection->pendingProcessing ),
                              &( pOperation->link ) );
    IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

    /* Set the output parameter. */
    *pNewOperation = pOperation;

    /* Clean up operation and decrement reference count if this function failed. */
    IOT_FUNCTION_CLEANUP_BEGIN();

    if( status != IOT_MQTT_SUCCESS )
    {
        if( decrementOnError == true )
        {
            _IotMqtt_DecrementConnectionReferences( pMqttConnection );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }

        if( pOperation != NULL )
        {
            IotMqtt_FreeOperation( pOperation );
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

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

bool _IotMqtt_DecrementOperationReferences( _mqttOperation_t * pOperation,
                                            bool cancelJob )
{
    bool destroyOperation = false;
    IotTaskPoolError_t taskPoolStatus = IOT_TASKPOOL_SUCCESS;
    _mqttConnection_t * pMqttConnection = pOperation->pMqttConnection;

    /* Attempt to cancel the operation's job. */
    if( cancelJob == true )
    {
        taskPoolStatus = IotTaskPool_TryCancel( IOT_SYSTEM_TASKPOOL,
                                                pOperation->job,
                                                NULL );

        /* If the operation's job was not canceled, it must be already executing.
         * Any other return value is invalid. */
        IotMqtt_Assert( ( taskPoolStatus == IOT_TASKPOOL_SUCCESS ) ||
                        ( taskPoolStatus == IOT_TASKPOOL_CANCEL_FAILED ) );

        if( taskPoolStatus == IOT_TASKPOOL_SUCCESS )
        {
            IotLogDebug( "(MQTT connection %p, %s operation %p) Job canceled.",
                         pMqttConnection,
                         IotMqtt_OperationType( pOperation->u.operation.type ),
                         pOperation );
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

    /* Decrement job reference count. */
    if( taskPoolStatus == IOT_TASKPOOL_SUCCESS )
    {
        IotMutex_Lock( &( pMqttConnection->referencesMutex ) );
        pOperation->u.operation.jobReference--;

        IotLogDebug( "(MQTT connection %p, %s operation %p) Job reference changed"
                     " from %ld to %ld.",
                     pMqttConnection,
                     IotMqtt_OperationType( pOperation->u.operation.type ),
                     pOperation,
                     pOperation->u.operation.jobReference + 1,
                     pOperation->u.operation.jobReference );

        /* The job reference count must be 0 or 1 after the decrement. */
        IotMqtt_Assert( ( pOperation->u.operation.jobReference == 0 ) ||
                        ( pOperation->u.operation.jobReference == 1 ) );

        /* This operation may be destroyed if its reference count is 0. */
        if( pOperation->u.operation.jobReference == 0 )
        {
            destroyOperation = true;
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }

        IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    return destroyOperation;
}

/*-----------------------------------------------------------*/

void _IotMqtt_DestroyOperation( _mqttOperation_t * pOperation )
{
    _mqttConnection_t * pMqttConnection = pOperation->pMqttConnection;

    /* Default free packet function. */
    void ( * freePacket )( uint8_t * ) = _IotMqtt_FreePacket;

    IotLogDebug( "(MQTT connection %p, %s operation %p) Destroying operation.",
                 pMqttConnection,
                 IotMqtt_OperationType( pOperation->u.operation.type ),
                 pOperation );

    /* The job reference count must be between 0 and 2. */
    IotMqtt_Assert( ( pOperation->u.operation.jobReference >= 0 ) &&
                    ( pOperation->u.operation.jobReference <= 2 ) );

    /* Jobs to be destroyed should be removed from the MQTT connection's
     * lists. */
    IotMutex_Lock( &( pMqttConnection->referencesMutex ) );

    if( IotLink_IsLinked( &( pOperation->link ) ) == true )
    {
        IotLogDebug( "(MQTT connection %p, %s operation %p) Removed operation from connection lists.",
                     pMqttConnection,
                     IotMqtt_OperationType( pOperation->u.operation.type ),
                     pOperation,
                     pMqttConnection );

        IotListDouble_Remove( &( pOperation->link ) );
    }
    else
    {
        IotLogDebug( "(MQTT connection %p, %s operation %p) Operation was not present in connection lists.",
                     pMqttConnection,
                     IotMqtt_OperationType( pOperation->u.operation.type ),
                     pOperation );
    }

    IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

    /* Free any allocated MQTT packet. */
    if( pOperation->u.operation.pMqttPacket != NULL )
    {
        #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
            if( pMqttConnection->pSerializer != NULL )
            {
                if( pMqttConnection->pSerializer->freePacket != NULL )
                {
                    freePacket = pMqttConnection->pSerializer->freePacket;
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
        #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

        freePacket( pOperation->u.operation.pMqttPacket );

        IotLogDebug( "(MQTT connection %p, %s operation %p) MQTT packet freed.",
                     pMqttConnection,
                     IotMqtt_OperationType( pOperation->u.operation.type ),
                     pOperation );
    }
    else
    {
        IotLogDebug( "(MQTT connection %p, %s operation %p) Operation has no allocated MQTT packet.",
                     pMqttConnection,
                     IotMqtt_OperationType( pOperation->u.operation.type ),
                     pOperation );
    }

    /* Check if a wait semaphore was created for this operation. */
    if( ( pOperation->u.operation.flags & IOT_MQTT_FLAG_WAITABLE ) == IOT_MQTT_FLAG_WAITABLE )
    {
        IotSemaphore_Destroy( &( pOperation->u.operation.notify.waitSemaphore ) );

        IotLogDebug( "(MQTT connection %p, %s operation %p) Wait semaphore destroyed.",
                     pMqttConnection,
                     IotMqtt_OperationType( pOperation->u.operation.type ),
                     pOperation );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    IotLogDebug( "(MQTT connection %p, %s operation %p) Operation record destroyed.",
                 pMqttConnection,
                 IotMqtt_OperationType( pOperation->u.operation.type ),
                 pOperation );

    /* Free the memory used to hold operation data. */
    IotMqtt_FreeOperation( pOperation );

    /* Decrement the MQTT connection's reference count after destroying an
     * operation. */
    _IotMqtt_DecrementConnectionReferences( pMqttConnection );
}

/*-----------------------------------------------------------*/

void _IotMqtt_ProcessKeepAlive( IotTaskPool_t pTaskPool,
                                IotTaskPoolJob_t pKeepAliveJob,
                                void * pContext )
{
    bool status = true;
    IotTaskPoolError_t taskPoolStatus = IOT_TASKPOOL_SUCCESS;
    size_t bytesSent = 0;

    /* Retrieve the MQTT connection from the context. */
    _mqttConnection_t * pMqttConnection = ( _mqttConnection_t * ) pContext;

    /* Check parameters. */
    /* IotMqtt_Assert( pTaskPool == IOT_SYSTEM_TASKPOOL ); */
    IotMqtt_Assert( pKeepAliveJob == pMqttConnection->keepAliveJob );

    /* Check that keep-alive interval is valid. The MQTT spec states its maximum
     * value is 65,535 seconds. */
    IotMqtt_Assert( pMqttConnection->keepAliveMs <= 65535000 );

    /* Only two values are valid for the next keep alive job delay. */
    IotMqtt_Assert( ( pMqttConnection->nextKeepAliveMs == pMqttConnection->keepAliveMs ) ||
                    ( pMqttConnection->nextKeepAliveMs == IOT_MQTT_RESPONSE_WAIT_MS ) );

    IotLogDebug( "(MQTT connection %p) Keep-alive job started.", pMqttConnection );

    /* Re-create the keep-alive job for rescheduling. This should never fail. */
    taskPoolStatus = IotTaskPool_CreateJob( _IotMqtt_ProcessKeepAlive,
                                            pContext,
                                            IotTaskPool_GetJobStorageFromHandle( pKeepAliveJob ),
                                            &pKeepAliveJob );
    IotMqtt_Assert( taskPoolStatus == IOT_TASKPOOL_SUCCESS );

    IotMutex_Lock( &( pMqttConnection->referencesMutex ) );

    /* Determine whether to send a PINGREQ or check for PINGRESP. */
    if( pMqttConnection->nextKeepAliveMs == pMqttConnection->keepAliveMs )
    {
        IotLogDebug( "(MQTT connection %p) Sending PINGREQ.", pMqttConnection );

        /* Because PINGREQ may be used to keep the MQTT connection alive, it is
         * more important than other operations. Bypass the queue of jobs for
         * operations by directly sending the PINGREQ in this job. */
        bytesSent = pMqttConnection->pNetworkInterface->send( pMqttConnection->pNetworkConnection,
                                                              pMqttConnection->pPingreqPacket,
                                                              pMqttConnection->pingreqPacketSize );

        if( bytesSent != pMqttConnection->pingreqPacketSize )
        {
            IotLogError( "(MQTT connection %p) Failed to send PINGREQ.", pMqttConnection );
            status = false;
        }
        else
        {
            /* Assume the keep-alive will fail. The network receive callback will
             * clear the failure flag upon receiving a PINGRESP. */
            pMqttConnection->keepAliveFailure = true;

            /* Schedule a check for PINGRESP. */
            pMqttConnection->nextKeepAliveMs = IOT_MQTT_RESPONSE_WAIT_MS;

            IotLogDebug( "(MQTT connection %p) PINGREQ sent. Scheduling check for PINGRESP in %d ms.",
                         pMqttConnection,
                         IOT_MQTT_RESPONSE_WAIT_MS );
        }
    }
    else
    {
        IotLogDebug( "(MQTT connection %p) Checking for PINGRESP.", pMqttConnection );

        if( pMqttConnection->keepAliveFailure == false )
        {
            IotLogDebug( "(MQTT connection %p) PINGRESP was received.", pMqttConnection );

            /* PINGRESP was received. Schedule the next PINGREQ transmission. */
            pMqttConnection->nextKeepAliveMs = pMqttConnection->keepAliveMs;
        }
        else
        {
            IotLogError( "(MQTT connection %p) Failed to receive PINGRESP within %d ms.",
                         pMqttConnection,
                         IOT_MQTT_RESPONSE_WAIT_MS );

            /* The network receive callback did not clear the failure flag. */
            status = false;
        }
    }

    /* When a PINGREQ is successfully sent, reschedule this job to check for a
     * response shortly. */
    if( status == true )
    {
        taskPoolStatus = IotTaskPool_ScheduleDeferred( pTaskPool,
                                                       pKeepAliveJob,
                                                       pMqttConnection->nextKeepAliveMs );

        if( taskPoolStatus == IOT_TASKPOOL_SUCCESS )
        {
            IotLogDebug( "(MQTT connection %p) Next keep-alive job in %d ms.",
                         pMqttConnection,
                         IOT_MQTT_RESPONSE_WAIT_MS );
        }
        else
        {
            IotLogError( "(MQTT connection %p) Failed to reschedule keep-alive job, error %s.",
                         pMqttConnection,
                         IotTaskPool_strerror( taskPoolStatus ) );

            status = false;
        }
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Close the connection on failures. */
    if( status == false )
    {
        _IotMqtt_CloseNetworkConnection( IOT_MQTT_KEEP_ALIVE_TIMEOUT,
                                         pMqttConnection );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );
}

/*-----------------------------------------------------------*/

void _IotMqtt_ProcessIncomingPublish( IotTaskPool_t pTaskPool,
                                      IotTaskPoolJob_t pPublishJob,
                                      void * pContext )
{
    _mqttOperation_t * pOperation = pContext;
    IotMqttCallbackParam_t callbackParam = { .mqttConnection = NULL };

    /* Check parameters. The task pool and job parameter is not used when asserts
     * are disabled. */
    ( void ) pTaskPool;
    ( void ) pPublishJob;
    /* IotMqtt_Assert( pTaskPool == IOT_SYSTEM_TASKPOOL ); */
    IotMqtt_Assert( pOperation->incomingPublish == true );
    IotMqtt_Assert( pPublishJob == pOperation->job );

    /* Remove the operation from the pending processing list. */
    IotMutex_Lock( &( pOperation->pMqttConnection->referencesMutex ) );

    if( IotLink_IsLinked( &( pOperation->link ) ) == true )
    {
        IotListDouble_Remove( &( pOperation->link ) );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    IotMutex_Unlock( &( pOperation->pMqttConnection->referencesMutex ) );

    /* Process the current PUBLISH. */
    callbackParam.u.message.info = pOperation->u.publish.publishInfo;

    _IotMqtt_InvokeSubscriptionCallback( pOperation->pMqttConnection,
                                         &callbackParam );

    /* Free any buffers associated with the current PUBLISH message. */
    if( pOperation->u.publish.pReceivedData != NULL )
    {
        IotMqtt_FreeMessage( ( void * ) pOperation->u.publish.pReceivedData );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Free the incoming PUBLISH operation. */
    IotMqtt_FreeOperation( pOperation );
}

/*-----------------------------------------------------------*/

void _IotMqtt_ProcessSend( IotTaskPool_t pTaskPool,
                           IotTaskPoolJob_t pSendJob,
                           void * pContext )
{
    size_t bytesSent = 0;
    bool destroyOperation = false, waitable = false, networkPending = false;
    _mqttOperation_t * pOperation = ( _mqttOperation_t * ) pContext;
    _mqttConnection_t * pMqttConnection = pOperation->pMqttConnection;

    /* Check parameters. The task pool and job parameter is not used when asserts
     * are disabled. */
    ( void ) pTaskPool;
    ( void ) pSendJob;
    /* IotMqtt_Assert( pTaskPool == IOT_SYSTEM_TASKPOOL ); */
    IotMqtt_Assert( pSendJob == pOperation->job );

    /* The given operation must have an allocated packet and be waiting for a status. */
    IotMqtt_Assert( pOperation->u.operation.pMqttPacket != NULL );
    IotMqtt_Assert( pOperation->u.operation.packetSize != 0 );
    IotMqtt_Assert( pOperation->u.operation.status == IOT_MQTT_STATUS_PENDING );

    /* Check if this operation is waitable. */
    waitable = ( pOperation->u.operation.flags & IOT_MQTT_FLAG_WAITABLE ) == IOT_MQTT_FLAG_WAITABLE;

    /* Check PUBLISH retry counts and limits. */
    if( pOperation->u.operation.retry.limit > 0 )
    {
        if( _checkRetryLimit( pOperation ) == false )
        {
            pOperation->u.operation.status = IOT_MQTT_RETRY_NO_RESPONSE;
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

    /* Send an operation that is waiting for a response. */
    if( pOperation->u.operation.status == IOT_MQTT_STATUS_PENDING )
    {
        IotLogDebug( "(MQTT connection %p, %s operation %p) Sending MQTT packet.",
                     pMqttConnection,
                     IotMqtt_OperationType( pOperation->u.operation.type ),
                     pOperation );

        /* Transmit the MQTT packet from the operation over the network. */
        bytesSent = pMqttConnection->pNetworkInterface->send( pMqttConnection->pNetworkConnection,
                                                              pOperation->u.operation.pMqttPacket,
                                                              pOperation->u.operation.packetSize );

        /* Check transmission status. */
        if( bytesSent != pOperation->u.operation.packetSize )
        {
            pOperation->u.operation.status = IOT_MQTT_NETWORK_ERROR;
        }
        else
        {
            /* DISCONNECT operations are considered successful upon successful
             * transmission. In addition, non-waitable operations with no callback
             * may also be considered successful. */
            if( pOperation->u.operation.type == IOT_MQTT_DISCONNECT )
            {
                /* DISCONNECT operations are always waitable. */
                IotMqtt_Assert( waitable == true );

                pOperation->u.operation.status = IOT_MQTT_SUCCESS;
            }
            else if( waitable == false )
            {
                if( pOperation->u.operation.notify.callback.function == NULL )
                {
                    pOperation->u.operation.status = IOT_MQTT_SUCCESS;
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
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Check if this operation requires further processing. */
    if( pOperation->u.operation.status == IOT_MQTT_STATUS_PENDING )
    {
        /* Check if this operation should be scheduled for retransmission. */
        if( pOperation->u.operation.retry.limit > 0 )
        {
            if( _scheduleNextRetry( pOperation ) == false )
            {
                pOperation->u.operation.status = IOT_MQTT_SCHEDULING_ERROR;
            }
            else
            {
                /* A successfully scheduled PUBLISH retry is awaiting a response
                 * from the network. */
                networkPending = true;
            }
        }
        else
        {
            /* Decrement reference count to signal completion of send job. Check
             * if the operation should be destroyed. */
            if( waitable == true )
            {
                destroyOperation = _IotMqtt_DecrementOperationReferences( pOperation, false );
            }
            else
            {
                EMPTY_ELSE_MARKER;
            }

            /* If the operation should not be destroyed, transfer it from the
             * pending processing to the pending response list. */
            if( destroyOperation == false )
            {
                IotMutex_Lock( &( pMqttConnection->referencesMutex ) );

                /* Operation must be linked. */
                IotMqtt_Assert( IotLink_IsLinked( &( pOperation->link ) ) );

                /* Transfer to pending response list. */
                IotListDouble_Remove( &( pOperation->link ) );
                IotListDouble_InsertHead( &( pMqttConnection->pendingResponse ),
                                          &( pOperation->link ) );

                IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

                /* This operation is now awaiting a response from the network. */
                networkPending = true;
            }
            else
            {
                EMPTY_ELSE_MARKER;
            }
        }
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Destroy the operation or notify of completion if necessary. */
    if( destroyOperation == true )
    {
        _IotMqtt_DestroyOperation( pOperation );
    }
    else
    {
        /* Do not check the operation status if a network response is pending,
         * since a network response could modify the status. */
        if( networkPending == false )
        {
            /* Notify of operation completion if this job set a status. */
            if( pOperation->u.operation.status != IOT_MQTT_STATUS_PENDING )
            {
                _IotMqtt_Notify( pOperation );
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
}

/*-----------------------------------------------------------*/

void _IotMqtt_ProcessCompletedOperation( IotTaskPool_t pTaskPool,
                                         IotTaskPoolJob_t pOperationJob,
                                         void * pContext )
{
    _mqttOperation_t * pOperation = ( _mqttOperation_t * ) pContext;
    IotMqttCallbackParam_t callbackParam = { 0 };

    /* Check parameters. The task pool and job parameter is not used when asserts
     * are disabled. */
    ( void ) pTaskPool;
    ( void ) pOperationJob;
    /* IotMqtt_Assert( pTaskPool == IOT_SYSTEM_TASKPOOL ); */
    IotMqtt_Assert( pOperationJob == pOperation->job );

    /* The operation's callback function and status must be set. */
    IotMqtt_Assert( pOperation->u.operation.notify.callback.function != NULL );
    IotMqtt_Assert( pOperation->u.operation.status != IOT_MQTT_STATUS_PENDING );

    callbackParam.mqttConnection = pOperation->pMqttConnection;
    callbackParam.u.operation.type = pOperation->u.operation.type;
    callbackParam.u.operation.reference = pOperation;
    callbackParam.u.operation.result = pOperation->u.operation.status;

    /* Invoke the user callback function. */
    pOperation->u.operation.notify.callback.function( pOperation->u.operation.notify.callback.pCallbackContext,
                                                      &callbackParam );

    /* Attempt to destroy the operation once the user callback returns. */
    if( _IotMqtt_DecrementOperationReferences( pOperation, false ) == true )
    {
        _IotMqtt_DestroyOperation( pOperation );
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }
}

/*-----------------------------------------------------------*/

IotMqttError_t _IotMqtt_ScheduleOperation( _mqttOperation_t * pOperation,
                                           IotTaskPoolRoutine_t jobRoutine,
                                           uint32_t delay )
{
    IotMqttError_t status = IOT_MQTT_SUCCESS;
    IotTaskPoolError_t taskPoolStatus = IOT_TASKPOOL_SUCCESS;

    /* Check that job routine is valid. */
    IotMqtt_Assert( ( jobRoutine == _IotMqtt_ProcessSend ) ||
                    ( jobRoutine == _IotMqtt_ProcessCompletedOperation ) ||
                    ( jobRoutine == _IotMqtt_ProcessIncomingPublish ) );

    /* Creating a new job should never fail when parameters are valid. */
    taskPoolStatus = IotTaskPool_CreateJob( jobRoutine,
                                            pOperation,
                                            &( pOperation->jobStorage ),
                                            &( pOperation->job ) );
    IotMqtt_Assert( taskPoolStatus == IOT_TASKPOOL_SUCCESS );

    /* Schedule the new job with a delay. */
    taskPoolStatus = IotTaskPool_ScheduleDeferred( IOT_SYSTEM_TASKPOOL,
                                                   pOperation->job,
                                                   delay );

    if( taskPoolStatus != IOT_TASKPOOL_SUCCESS )
    {
        /* Scheduling a newly-created job should never be invalid or illegal. */
        IotMqtt_Assert( taskPoolStatus != IOT_TASKPOOL_BAD_PARAMETER );
        IotMqtt_Assert( taskPoolStatus != IOT_TASKPOOL_ILLEGAL_OPERATION );

        IotLogWarn( "(MQTT connection %p, %s operation %p) Failed to schedule operation job, error %s.",
                    pOperation->pMqttConnection,
                    IotMqtt_OperationType( pOperation->u.operation.type ),
                    pOperation,
                    IotTaskPool_strerror( taskPoolStatus ) );

        status = IOT_MQTT_SCHEDULING_ERROR;
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    return status;
}

/*-----------------------------------------------------------*/

_mqttOperation_t * _IotMqtt_FindOperation( _mqttConnection_t * pMqttConnection,
                                           IotMqttOperationType_t type,
                                           const uint16_t * pPacketIdentifier )
{
    bool waitable = false;
    IotTaskPoolError_t taskPoolStatus = IOT_TASKPOOL_SUCCESS;
    _mqttOperation_t * pResult = NULL;
    IotLink_t * pResultLink = NULL;
    _operationMatchParam_t param = { 0 };

    param.type = type;
    param.pPacketIdentifier = pPacketIdentifier;

    if( pPacketIdentifier != NULL )
    {
        IotLogDebug( "(MQTT connection %p) Searching for operation %s pending response "
                     "with packet identifier %hu.",
                     pMqttConnection,
                     IotMqtt_OperationType( type ),
                     *pPacketIdentifier );
    }
    else
    {
        IotLogDebug( "(MQTT connection %p) Searching for operation %s pending response.",
                     pMqttConnection,
                     IotMqtt_OperationType( type ) );
    }

    /* Find and remove the first matching element in the list. */
    IotMutex_Lock( &( pMqttConnection->referencesMutex ) );
    pResultLink = IotListDouble_FindFirstMatch( &( pMqttConnection->pendingResponse ),
                                                NULL,
                                                _mqttOperation_match,
                                                &param );

    /* Check if a match was found. */
    if( pResultLink != NULL )
    {
        /* Get operation pointer and check if it is waitable. */
        pResult = IotLink_Container( _mqttOperation_t, pResultLink, link );
        waitable = ( pResult->u.operation.flags & IOT_MQTT_FLAG_WAITABLE ) == IOT_MQTT_FLAG_WAITABLE;

        /* Check if the matched operation is a PUBLISH with retry. If it is, cancel
         * the retry job. */
        if( pResult->u.operation.retry.limit > 0 )
        {
            taskPoolStatus = IotTaskPool_TryCancel( IOT_SYSTEM_TASKPOOL,
                                                    pResult->job,
                                                    NULL );

            /* If the retry job could not be canceled, then it is currently
             * executing. Ignore the operation. */
            if( taskPoolStatus != IOT_TASKPOOL_SUCCESS )
            {
                pResult = NULL;
            }
            else
            {
                /* Check job reference counts. A waitable operation should have a
                 * count of 2; a non-waitable operation should have a count of 1. */
                IotMqtt_Assert( pResult->u.operation.jobReference == ( 1 + ( waitable == true ) ) );
            }
        }
        else
        {
            /* An operation with no retry in the pending responses list should
             * always have a job reference of 1. */
            IotMqtt_Assert( pResult->u.operation.jobReference == 1 );

            /* Increment job references of a waitable operation to prevent Wait from
             * destroying this operation if it times out. */
            if( waitable == true )
            {
                ( pResult->u.operation.jobReference )++;

                IotLogDebug( "(MQTT connection %p, %s operation %p) Job reference changed from %ld to %ld.",
                             pMqttConnection,
                             IotMqtt_OperationType( type ),
                             pResult,
                             ( long int ) ( pResult->u.operation.jobReference - 1 ),
                             ( long int ) ( pResult->u.operation.jobReference ) );
            }
        }
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    if( pResult != NULL )
    {
        IotLogDebug( "(MQTT connection %p) Found operation %s." ,
                     pMqttConnection,
                     IotMqtt_OperationType( type ) );

        /* Remove the matched operation from the list. */
        IotListDouble_Remove( &( pResult->link ) );
    }
    else
    {
        IotLogDebug( "(MQTT connection %p) Operation %s not found.",
                     pMqttConnection,
                     IotMqtt_OperationType( type ) );
    }

    IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

    return pResult;
}

/*-----------------------------------------------------------*/

void _IotMqtt_Notify( _mqttOperation_t * pOperation )
{
    IotMqttError_t status = IOT_MQTT_SCHEDULING_ERROR;
    _mqttConnection_t * pMqttConnection = pOperation->pMqttConnection;

    /* Check if operation is waitable. */
    bool waitable = ( pOperation->u.operation.flags & IOT_MQTT_FLAG_WAITABLE ) == IOT_MQTT_FLAG_WAITABLE;

    /* Remove any lingering subscriptions if a SUBSCRIBE failed. Rejected
     * subscriptions are removed by the deserializer, so not removed here. */
    if( pOperation->u.operation.type == IOT_MQTT_SUBSCRIBE )
    {
        switch( pOperation->u.operation.status )
        {
            case IOT_MQTT_SUCCESS:
                break;

            case IOT_MQTT_SERVER_REFUSED:
                break;

            default:
                _IotMqtt_RemoveSubscriptionByPacket( pOperation->pMqttConnection,
                                                     pOperation->u.operation.packetIdentifier,
                                                     -1 );
                break;
        }
    }
    else
    {
        EMPTY_ELSE_MARKER;
    }

    /* Schedule callback invocation for non-waitable operation. */
    if( waitable == false )
    {
        /* Non-waitable operation should have job reference of 1. */
        IotMqtt_Assert( pOperation->u.operation.jobReference == 1 );

        /* Schedule an invocation of the callback. */
        if( pOperation->u.operation.notify.callback.function != NULL )
        {
            IotMutex_Lock( &( pMqttConnection->referencesMutex ) );

            status = _IotMqtt_ScheduleOperation( pOperation,
                                                 _IotMqtt_ProcessCompletedOperation,
                                                 0 );

            if( status == IOT_MQTT_SUCCESS )
            {
                IotLogDebug( "(MQTT connection %p, %s operation %p) Callback scheduled.",
                             pOperation->pMqttConnection,
                             IotMqtt_OperationType( pOperation->u.operation.type ),
                             pOperation );

                /* Place the scheduled operation back in the list of operations pending
                 * processing. */
                if( IotLink_IsLinked( &( pOperation->link ) ) == true )
                {
                    IotListDouble_Remove( &( pOperation->link ) );
                }
                else
                {
                    EMPTY_ELSE_MARKER;
                }

                IotListDouble_InsertHead( &( pMqttConnection->pendingProcessing ),
                                          &( pOperation->link ) );
            }
            else
            {
                IotLogWarn( "(MQTT connection %p, %s operation %p) Failed to schedule callback.",
                            pOperation->pMqttConnection,
                            IotMqtt_OperationType( pOperation->u.operation.type ),
                            pOperation );
            }

            IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );
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

    /* Operations that weren't scheduled may be destroyed. */
    if( status == IOT_MQTT_SCHEDULING_ERROR )
    {
        /* Decrement reference count of operations not scheduled. */
        if( _IotMqtt_DecrementOperationReferences( pOperation, false ) == true )
        {
            _IotMqtt_DestroyOperation( pOperation );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }

        /* Post to a waitable operation's semaphore. */
        if( waitable == true )
        {
            IotLogDebug( "(MQTT connection %p, %s operation %p) Waitable operation "
                         "notified of completion.",
                         pOperation->pMqttConnection,
                         IotMqtt_OperationType( pOperation->u.operation.type ),
                         pOperation );

            IotSemaphore_Post( &( pOperation->u.operation.notify.waitSemaphore ) );
        }
        else
        {
            EMPTY_ELSE_MARKER;
        }
    }
    else
    {
        IotMqtt_Assert( status == IOT_MQTT_SUCCESS );
    }
}

/*-----------------------------------------------------------*/
