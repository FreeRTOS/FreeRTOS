/*
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

#include <assert.h>
#include <string.h>
#include "mqtt_state.h"

/*-----------------------------------------------------------*/

/**
 * @brief Create a 16-bit bitmap with bit set at specified position.
 *
 * @param[in] position The position at which the bit need to be set.
 */
#define UINT16_BITMAP_BIT_SET_AT( position )    ( ( uint16_t ) 0x01U << ( ( uint16_t ) position ) )

/**
 * @brief Set a bit in an 16-bit unsigned integer.
 *
 * @param[in] x The 16-bit unsigned integer to set a bit.
 * @param[in] position The position at which the bit need to be set.
 */
#define UINT16_SET_BIT( x, position )           ( ( x ) = ( uint16_t ) ( ( x ) | ( UINT16_BITMAP_BIT_SET_AT( position ) ) ) )

/**
 * @brief Macro for checking if a bit is set in a 16-bit unsigned integer.
 *
 * @param[in] x The unsigned 16-bit integer to check.
 * @param[in] position Which bit to check.
 */
#define UINT16_CHECK_BIT( x, position )         ( ( ( x ) & ( UINT16_BITMAP_BIT_SET_AT( position ) ) ) == ( UINT16_BITMAP_BIT_SET_AT( position ) ) )

/*-----------------------------------------------------------*/

/**
 * @brief Test if a transition to new state is possible, when dealing with PUBLISHes.
 *
 * @param[in] currentState The current state.
 * @param[in] newState State to transition to.
 * @param[in] opType Reserve, Send, or Receive.
 * @param[in] qos 0, 1, or 2.
 *
 * @note This function does not validate the current state, or the new state
 * based on either the operation type or QoS. It assumes the new state is valid
 * given the opType and QoS, which will be the case if calculated by
 * MQTT_CalculateStatePublish().
 *
 * @return `true` if transition is possible, else `false`
 */
static bool validateTransitionPublish( MQTTPublishState_t currentState,
                                       MQTTPublishState_t newState,
                                       MQTTStateOperation_t opType,
                                       MQTTQoS_t qos );

/**
 * @brief Test if a transition to a new state is possible, when dealing with acks.
 *
 * @param[in] currentState The current state.
 * @param[in] newState State to transition to.
 *
 * @return `true` if transition is possible, else `false`.
 */
static bool validateTransitionAck( MQTTPublishState_t currentState,
                                   MQTTPublishState_t newState );

/**
 * @brief Test if the publish corresponding to an ack is outgoing or incoming.
 *
 * @param[in] packetType PUBACK, PUBREC, PUBREL, or PUBCOMP.
 * @param[in] opType Send, or Receive.
 *
 * @return `true` if corresponds to outgoing publish, else `false`.
 */
static bool isPublishOutgoing( MQTTPubAckType_t packetType,
                               MQTTStateOperation_t opType );

/**
 * @brief Find a packet ID in the state record.
 *
 * @param[in] records State record array.
 * @param[in] recordCount Length of record array.
 * @param[in] packetId packet ID to search for.
 * @param[out] pQos QoS retrieved from record.
 * @param[out] pCurrentState state retrieved from record.
 *
 * @return index of the packet id in the record if it exists, else the record length.
 */
static size_t findInRecord( const MQTTPubAckInfo_t * records,
                            size_t recordCount,
                            uint16_t packetId,
                            MQTTQoS_t * pQos,
                            MQTTPublishState_t * pCurrentState );

/**
 * @brief Compact records.
 *
 * Records are arranged in the relative order to maintain message ordering.
 * This will lead to fragmentation and this function will help in defragmenting
 * the records array.
 *
 * @param[in] records State record array.
 * @param[in] recordCount Length of record array.
 */
static void compactRecords( MQTTPubAckInfo_t * records,
                            size_t recordCount );

/**
 * @brief Store a new entry in the state record.
 *
 * @param[in] records State record array.
 * @param[in] recordCount Length of record array.
 * @param[in] packetId, packet ID of new entry.
 * @param[in] qos QoS of new entry.
 * @param[in] publishState state of new entry.
 *
 * @return MQTTSuccess, MQTTNoMemory, MQTTStateCollision.
 */
static MQTTStatus_t addRecord( MQTTPubAckInfo_t * records,
                               size_t recordCount,
                               uint16_t packetId,
                               MQTTQoS_t qos,
                               MQTTPublishState_t publishState );

/**
 * @brief Update and possibly delete an entry in the state record.
 *
 * @param[in] records State record array.
 * @param[in] recordIndex index of record to update.
 * @param[in] newState New state to update.
 * @param[in] shouldDelete Whether an existing entry should be deleted.
 */
static void updateRecord( MQTTPubAckInfo_t * records,
                          size_t recordIndex,
                          MQTTPublishState_t newState,
                          bool shouldDelete );

/**
 * @brief Get the packet ID and index of an outgoing publish in specified
 * states.
 *
 * @param[in] pMqttContext Initialized MQTT context.
 * @param[in] searchStates The states to search for in 2-byte bit map.
 * @param[in,out] pCursor Index at which to start searching.
 */
static uint16_t stateSelect( const MQTTContext_t * pMqttContext,
                             uint16_t searchStates,
                             MQTTStateCursor_t * pCursor );

/**
 * @brief Update the state records for an ACK after state transition
 * validations.
 *
 * @param[in] records State records pointer.
 * @param[in] recordIndex Index at which the record is stored.
 * @param[in] packetId Packet id of the packet.
 * @param[in] currentState Current state of the publish record.
 * @param[in] newState New state of the publish.
 *
 * @return #MQTTIllegalState, or #MQTTSuccess.
 */
static MQTTStatus_t updateStateAck( MQTTPubAckInfo_t * records,
                                    size_t recordIndex,
                                    uint16_t packetId,
                                    MQTTPublishState_t currentState,
                                    MQTTPublishState_t newState );

/**
 * @brief Update the state record for a PUBLISH packet after validating
 * the state transitions.
 *
 * @param[in] pMqttContext Initialized MQTT context.
 * @param[in] recordIndex Index in state records at which publish record exists.
 * @param[in] packetId ID of the PUBLISH packet.
 * @param[in] opType Send or Receive.
 * @param[in] qos 0, 1, or 2.
 * @param[in] currentState Current state of the publish record.
 * @param[in] newState New state of the publish record.
 *
 * @return #MQTTIllegalState, #MQTTStateCollision or #MQTTSuccess.
 */
static MQTTStatus_t updateStatePublish( MQTTContext_t * pMqttContext,
                                        size_t recordIndex,
                                        uint16_t packetId,
                                        MQTTStateOperation_t opType,
                                        MQTTQoS_t qos,
                                        MQTTPublishState_t currentState,
                                        MQTTPublishState_t newState );

/*-----------------------------------------------------------*/

static bool validateTransitionPublish( MQTTPublishState_t currentState,
                                       MQTTPublishState_t newState,
                                       MQTTStateOperation_t opType,
                                       MQTTQoS_t qos )
{
    bool isValid = false;

    switch( currentState )
    {
        case MQTTStateNull:

            /* Transitions from null occur when storing a new entry into the record. */
            if( opType == MQTT_RECEIVE )
            {
                isValid = ( ( newState == MQTTPubAckSend ) || ( newState == MQTTPubRecSend ) ) ? true : false;
            }

            break;

        case MQTTPublishSend:

            /* Outgoing publish. All such publishes start in this state due to
             * the reserve operation. */
            switch( qos )
            {
                case MQTTQoS1:
                    isValid = ( newState == MQTTPubAckPending ) ? true : false;
                    break;

                case MQTTQoS2:
                    isValid = ( newState == MQTTPubRecPending ) ? true : false;
                    break;

                default:
                    /* QoS 0 is checked before calling this function. */
                    break;
            }

            break;

        /* Below cases are for validating the resends of publish when a session is
         * reestablished. */
        case MQTTPubAckPending:

            /* When a session is reestablished, outgoing QoS1 publishes in state
             * #MQTTPubAckPending can be resent. The state remains the same. */
            isValid = ( newState == MQTTPubAckPending ) ? true : false;

            break;

        case MQTTPubRecPending:

            /* When a session is reestablished, outgoing QoS2 publishes in state
             * #MQTTPubRecPending can be resent. The state remains the same. */
            isValid = ( newState == MQTTPubRecPending ) ? true : false;

            break;

        default:
            /* For a PUBLISH, we should not start from any other state. */
            break;
    }

    return isValid;
}

/*-----------------------------------------------------------*/

static bool validateTransitionAck( MQTTPublishState_t currentState,
                                   MQTTPublishState_t newState )
{
    bool isValid = false;

    switch( currentState )
    {
        case MQTTPubAckSend:
        /* Incoming publish, QoS 1. */
        case MQTTPubAckPending:
            /* Outgoing publish, QoS 1. */
            isValid = ( newState == MQTTPublishDone ) ? true : false;
            break;

        case MQTTPubRecSend:
            /* Incoming publish, QoS 2. */
            isValid = ( newState == MQTTPubRelPending ) ? true : false;
            break;

        case MQTTPubRelPending:

            /* Incoming publish, QoS 2.
             * There are 2 valid transitions possible.
             * 1. MQTTPubRelPending -> MQTTPubCompSend : A PUBREL ack is received
             *    when publish record state is MQTTPubRelPending. This is the
             *    normal state transition without any connection interruptions.
             * 2. MQTTPubRelPending -> MQTTPubRelPending : Receiving a duplicate
             *    QoS2 publish can result in a transition to the same state.
             *    This can happen in the below state transition.
             *    1. Incoming publish received.
             *    2. PUBREC ack sent and state is now MQTTPubRelPending.
             *    3. TCP connection failure and broker didn't receive the PUBREC.
             *    4. Reestablished MQTT session.
             *    5. MQTT broker resent the un-acked publish.
             *    6. Publish is received when publish record state is in
             *       MQTTPubRelPending.
             *    7. Sending out a PUBREC will result in this transition
             *       to the same state. */
            isValid = ( ( newState == MQTTPubCompSend ) ||
                        ( newState == MQTTPubRelPending ) ) ? true : false;
            break;

        case MQTTPubCompSend:

            /* Incoming publish, QoS 2.
             * There are 2 valid transitions possible.
             * 1. MQTTPubCompSend -> MQTTPublishDone : A PUBCOMP ack is sent
             *    after receiving a PUBREL from broker. This is the
             *    normal state transition without any connection interruptions.
             * 2. MQTTPubCompSend -> MQTTPubCompSend : Receiving a duplicate PUBREL
             *    can result in a transition to the same state.
             *    This can happen in the below state transition.
             *    1. A TCP connection failure happened before sending a PUBCOMP
             *       for an incoming PUBREL.
             *    2. Reestablished an MQTT session.
             *    3. MQTT broker resent the un-acked PUBREL.
             *    4. Receiving the PUBREL again will result in this transition
             *       to the same state. */
            isValid = ( ( newState == MQTTPublishDone ) ||
                        ( newState == MQTTPubCompSend ) ) ? true : false;
            break;

        case MQTTPubRecPending:
            /* Outgoing publish, Qos 2. */
            isValid = ( newState == MQTTPubRelSend ) ? true : false;
            break;

        case MQTTPubRelSend:
            /* Outgoing publish, Qos 2. */
            isValid = ( newState == MQTTPubCompPending ) ? true : false;
            break;

        case MQTTPubCompPending:

            /* Outgoing publish, Qos 2.
             * There are 2 valid transitions possible.
             * 1. MQTTPubCompPending -> MQTTPublishDone : A PUBCOMP is received.
             *    This marks the complete state transition for the publish packet.
             *    This is the normal state transition without any connection
             *    interruptions.
             * 2. MQTTPubCompPending -> MQTTPubCompPending : Resending a PUBREL for
             *    packets in state #MQTTPubCompPending can result in this
             *    transition to the same state.
             *    This can happen in the below state transition.
             *    1. A TCP connection failure happened before receiving a PUBCOMP
             *       for an outgoing PUBREL.
             *    2. An MQTT session is reestablished.
             *    3. Resending the un-acked PUBREL results in this transition
             *       to the same state. */
            isValid = ( ( newState == MQTTPublishDone ) ||
                        ( newState == MQTTPubCompPending ) ) ? true : false;
            break;

        case MQTTPublishDone:
        /* Done state should transition to invalid since it will be removed from the record. */
        case MQTTPublishSend:
        /* If an ack was sent/received we shouldn't have been in this state. */
        case MQTTStateNull:
        /* If an ack was sent/received the record should exist. */
        default:
            /* Invalid. */
            break;
    }

    return isValid;
}

/*-----------------------------------------------------------*/

static bool isPublishOutgoing( MQTTPubAckType_t packetType,
                               MQTTStateOperation_t opType )
{
    bool isOutgoing = false;

    switch( packetType )
    {
        case MQTTPuback:
        case MQTTPubrec:
        case MQTTPubcomp:
            isOutgoing = ( opType == MQTT_RECEIVE ) ? true : false;
            break;

        case MQTTPubrel:
            isOutgoing = ( opType == MQTT_SEND ) ? true : false;
            break;

        default:
            /* No other ack type. */
            break;
    }

    return isOutgoing;
}

/*-----------------------------------------------------------*/

static size_t findInRecord( const MQTTPubAckInfo_t * records,
                            size_t recordCount,
                            uint16_t packetId,
                            MQTTQoS_t * pQos,
                            MQTTPublishState_t * pCurrentState )
{
    size_t index = 0;

    *pCurrentState = MQTTStateNull;

    if( packetId == MQTT_PACKET_ID_INVALID )
    {
        index = recordCount;
    }
    else
    {
        for( index = 0; index < recordCount; index++ )
        {
            if( records[ index ].packetId == packetId )
            {
                *pQos = records[ index ].qos;
                *pCurrentState = records[ index ].publishState;
                break;
            }
        }
    }

    return index;
}

/*-----------------------------------------------------------*/

static void compactRecords( MQTTPubAckInfo_t * records,
                            size_t recordCount )
{
    size_t index = 0;
    size_t emptyIndex = MQTT_STATE_ARRAY_MAX_COUNT;

    assert( records != NULL );

    /* Find the empty spots and fill those with non empty values. */
    for( ; index < recordCount; index++ )
    {
        /* Find the first empty spot. */
        if( records[ index ].packetId == MQTT_PACKET_ID_INVALID )
        {
            if( emptyIndex == MQTT_STATE_ARRAY_MAX_COUNT )
            {
                emptyIndex = index;
            }
        }
        else
        {
            if( emptyIndex != MQTT_STATE_ARRAY_MAX_COUNT )
            {
                /* Copy over the contents at non empty index to empty index. */
                records[ emptyIndex ].packetId = records[ index ].packetId;
                records[ emptyIndex ].qos = records[ index ].qos;
                records[ emptyIndex ].publishState = records[ index ].publishState;

                /* Mark the record at current non empty index as invalid. */
                records[ index ].packetId = MQTT_PACKET_ID_INVALID;

                /* Advance the emptyIndex. */
                emptyIndex++;
            }
        }
    }
}

/*-----------------------------------------------------------*/

static MQTTStatus_t addRecord( MQTTPubAckInfo_t * records,
                               size_t recordCount,
                               uint16_t packetId,
                               MQTTQoS_t qos,
                               MQTTPublishState_t publishState )
{
    MQTTStatus_t status = MQTTNoMemory;
    int32_t index = 0;
    size_t availableIndex = recordCount;
    bool validEntryFound = false;

    assert( packetId != MQTT_PACKET_ID_INVALID );
    assert( qos != MQTTQoS0 );

    /* Check if we have to compact the records. This is known by checking if
     * the last spot in the array is filled. */
    if( records[ recordCount - 1U ].packetId != MQTT_PACKET_ID_INVALID )
    {
        compactRecords( records, recordCount );
    }

    /* Start from end so first available index will be populated.
     * Available index is always found after the last element in the records.
     * This is to make sure the relative order of the records in order to meet
     * the message ordering requirement of MQTT spec 3.1.1. */
    for( index = ( ( int32_t ) recordCount - 1 ); index >= 0; index-- )
    {
        /* Available index is only found after packet at the highest index. */
        if( records[ index ].packetId == MQTT_PACKET_ID_INVALID )
        {
            if( validEntryFound == false )
            {
                availableIndex = ( size_t ) index;
            }
        }
        else
        {
            /* A non-empty spot found in the records. */
            validEntryFound = true;

            if( records[ index ].packetId == packetId )
            {
                /* Collision. */
                LogError( ( "Collision when adding PacketID=%u at index=%u",
                            packetId,
                            index ) );

                status = MQTTStateCollision;
                availableIndex = recordCount;
                break;
            }
        }
    }

    if( availableIndex < recordCount )
    {
        records[ availableIndex ].packetId = packetId;
        records[ availableIndex ].qos = qos;
        records[ availableIndex ].publishState = publishState;
        status = MQTTSuccess;
    }

    return status;
}

/*-----------------------------------------------------------*/

static void updateRecord( MQTTPubAckInfo_t * records,
                          size_t recordIndex,
                          MQTTPublishState_t newState,
                          bool shouldDelete )
{
    assert( records != NULL );

    if( shouldDelete == true )
    {
        /* Mark the record as invalid. */
        records[ recordIndex ].packetId = MQTT_PACKET_ID_INVALID;
    }
    else
    {
        records[ recordIndex ].publishState = newState;
    }
}

/*-----------------------------------------------------------*/

static uint16_t stateSelect( const MQTTContext_t * pMqttContext,
                             uint16_t searchStates,
                             MQTTStateCursor_t * pCursor )
{
    uint16_t packetId = MQTT_PACKET_ID_INVALID;
    uint16_t outgoingStates = 0U;
    const MQTTPubAckInfo_t * records = NULL;
    bool stateCheck = false;

    assert( pMqttContext != NULL );
    assert( searchStates != 0U );
    assert( pCursor != NULL );

    /* Create a bit map with all the outgoing publish states. */
    UINT16_SET_BIT( outgoingStates, MQTTPublishSend );
    UINT16_SET_BIT( outgoingStates, MQTTPubAckPending );
    UINT16_SET_BIT( outgoingStates, MQTTPubRecPending );
    UINT16_SET_BIT( outgoingStates, MQTTPubRelSend );
    UINT16_SET_BIT( outgoingStates, MQTTPubCompPending );

    /* Only outgoing publish records need to be searched. */
    assert( ( outgoingStates & searchStates ) > 0U );
    assert( ( ~outgoingStates & searchStates ) == 0 );

    records = pMqttContext->outgoingPublishRecords;

    while( *pCursor < MQTT_STATE_ARRAY_MAX_COUNT )
    {
        /* Check if any of the search states are present. */
        stateCheck = UINT16_CHECK_BIT( searchStates, records[ *pCursor ].publishState ) ? true : false;

        if( stateCheck == true )
        {
            packetId = records[ *pCursor ].packetId;
            ( *pCursor )++;
            break;
        }

        ( *pCursor )++;
    }

    return packetId;
}

/*-----------------------------------------------------------*/

MQTTPublishState_t MQTT_CalculateStateAck( MQTTPubAckType_t packetType,
                                           MQTTStateOperation_t opType,
                                           MQTTQoS_t qos )
{
    MQTTPublishState_t calculatedState = MQTTStateNull;
    /* There are more QoS2 cases than QoS1, so initialize to that. */
    bool qosValid = ( qos == MQTTQoS2 ) ? true : false;

    switch( packetType )
    {
        case MQTTPuback:
            qosValid = ( qos == MQTTQoS1 ) ? true : false;
            calculatedState = MQTTPublishDone;
            break;

        case MQTTPubrec:

            /* Incoming publish: send PUBREC, PUBREL pending.
             * Outgoing publish: receive PUBREC, send PUBREL. */
            calculatedState = ( opType == MQTT_SEND ) ? MQTTPubRelPending : MQTTPubRelSend;
            break;

        case MQTTPubrel:

            /* Incoming publish: receive PUBREL, send PUBCOMP.
             * Outgoing publish: send PUBREL, PUBCOMP pending. */
            calculatedState = ( opType == MQTT_SEND ) ? MQTTPubCompPending : MQTTPubCompSend;
            break;

        case MQTTPubcomp:
            calculatedState = MQTTPublishDone;
            break;

        default:
            /* No other ack type. */
            break;
    }

    /* Sanity check, make sure ack and QoS agree. */
    if( qosValid == false )
    {
        calculatedState = MQTTStateNull;
    }

    return calculatedState;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t updateStateAck( MQTTPubAckInfo_t * records,
                                    size_t recordIndex,
                                    uint16_t packetId,
                                    MQTTPublishState_t currentState,
                                    MQTTPublishState_t newState )
{
    MQTTStatus_t status = MQTTIllegalState;
    bool shouldDeleteRecord = false;
    bool isTransitionValid = false;

    assert( records != NULL );

    /* Record to be deleted if the state transition is completed or if a PUBREC
     * is received for an outgoing QoS2 publish. When a PUBREC is received,
     * record is deleted and added back to the end of the records to maintain
     * ordering for PUBRELs. */
    shouldDeleteRecord = ( ( newState == MQTTPublishDone ) || ( newState == MQTTPubRelSend ) ) ? true : false;
    isTransitionValid = validateTransitionAck( currentState, newState );

    if( isTransitionValid == true )
    {
        status = MQTTSuccess;

        /* Update record for acks. When sending or receiving acks for packets that
         * are resent during a session reestablishment, the new state and
         * current state can be the same. No update of record required in that case. */
        if( currentState != newState )
        {
            updateRecord( records,
                          recordIndex,
                          newState,
                          shouldDeleteRecord );

            /* For QoS2 messages, in order to preserve the message ordering, when
             * a PUBREC is received for an outgoing publish, the record should be
             * moved to the last. This move will help preserve the order in which
             * a PUBREL needs to be resent in case of a session reestablishment. */
            if( newState == MQTTPubRelSend )
            {
                status = addRecord( records,
                                    MQTT_STATE_ARRAY_MAX_COUNT,
                                    packetId,
                                    MQTTQoS2,
                                    MQTTPubRelSend );
            }
        }
    }
    else
    {
        /* Invalid state transition. */
        LogError( ( "Invalid transition from state %s to state %s.",
                    MQTT_State_strerror( currentState ),
                    MQTT_State_strerror( newState ) ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

static MQTTStatus_t updateStatePublish( MQTTContext_t * pMqttContext,
                                        size_t recordIndex,
                                        uint16_t packetId,
                                        MQTTStateOperation_t opType,
                                        MQTTQoS_t qos,
                                        MQTTPublishState_t currentState,
                                        MQTTPublishState_t newState )
{
    MQTTStatus_t status = MQTTSuccess;
    bool isTransitionValid = false;

    assert( pMqttContext != NULL );
    assert( packetId != MQTT_PACKET_ID_INVALID );
    assert( qos != MQTTQoS0 );

    /* This will always succeed for an incoming publish. This is due to the fact
     * that the passed in currentState must be MQTTStateNull, since
     * #MQTT_UpdateStatePublish does not perform a lookup for receives. */
    isTransitionValid = validateTransitionPublish( currentState, newState, opType, qos );

    if( isTransitionValid == true )
    {
        /* addRecord will check for collisions. */
        if( opType == MQTT_RECEIVE )
        {
            status = addRecord( pMqttContext->incomingPublishRecords,
                                MQTT_STATE_ARRAY_MAX_COUNT,
                                packetId,
                                qos,
                                newState );
        }
        /* Send operation. */
        else
        {
            /* Skip updating record when publish is resend and no state
             * update is required. */
            if( currentState != newState )
            {
                updateRecord( pMqttContext->outgoingPublishRecords, recordIndex, newState, false );
            }
        }
    }
    else
    {
        status = MQTTIllegalState;
        LogError( ( "Invalid transition from state %s to state %s.",
                    MQTT_State_strerror( currentState ),
                    MQTT_State_strerror( newState ) ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_ReserveState( MQTTContext_t * pMqttContext,
                                uint16_t packetId,
                                MQTTQoS_t qos )
{
    MQTTStatus_t status = MQTTSuccess;

    if( qos == MQTTQoS0 )
    {
        status = MQTTSuccess;
    }
    else if( ( packetId == MQTT_PACKET_ID_INVALID ) || ( pMqttContext == NULL ) )
    {
        status = MQTTBadParameter;
    }
    else
    {
        /* Collisions are detected when adding the record. */
        status = addRecord( pMqttContext->outgoingPublishRecords,
                            MQTT_STATE_ARRAY_MAX_COUNT,
                            packetId,
                            qos,
                            MQTTPublishSend );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTPublishState_t MQTT_CalculateStatePublish( MQTTStateOperation_t opType,
                                               MQTTQoS_t qos )
{
    MQTTPublishState_t calculatedState = MQTTStateNull;

    switch( qos )
    {
        case MQTTQoS0:
            calculatedState = MQTTPublishDone;
            break;

        case MQTTQoS1:
            calculatedState = ( opType == MQTT_SEND ) ? MQTTPubAckPending : MQTTPubAckSend;
            break;

        case MQTTQoS2:
            calculatedState = ( opType == MQTT_SEND ) ? MQTTPubRecPending : MQTTPubRecSend;
            break;

        default:
            /* No other QoS values. */
            break;
    }

    return calculatedState;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_UpdateStatePublish( MQTTContext_t * pMqttContext,
                                      uint16_t packetId,
                                      MQTTStateOperation_t opType,
                                      MQTTQoS_t qos,
                                      MQTTPublishState_t * pNewState )
{
    MQTTPublishState_t newState = MQTTStateNull;
    MQTTPublishState_t currentState = MQTTStateNull;
    MQTTStatus_t mqttStatus = MQTTSuccess;
    size_t recordIndex = MQTT_STATE_ARRAY_MAX_COUNT;
    MQTTQoS_t foundQoS = MQTTQoS0;

    if( ( pMqttContext == NULL ) || ( pNewState == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pMqttContext=%p, pNewState=%p",
                    pMqttContext,
                    pNewState ) );

        mqttStatus = MQTTBadParameter;
    }
    else if( qos == MQTTQoS0 )
    {
        /* QoS 0 publish. Do nothing. */
        *pNewState = MQTTPublishDone;
    }
    else if( packetId == MQTT_PACKET_ID_INVALID )
    {
        /* Publishes > QoS 0 need a valid packet ID. */
        mqttStatus = MQTTBadParameter;
    }
    else if( opType == MQTT_SEND )
    {
        /* Search record for entry so we can check QoS. */
        recordIndex = findInRecord( pMqttContext->outgoingPublishRecords,
                                    MQTT_STATE_ARRAY_MAX_COUNT,
                                    packetId,
                                    &foundQoS,
                                    &currentState );

        if( ( recordIndex == MQTT_STATE_ARRAY_MAX_COUNT ) || ( foundQoS != qos ) )
        {
            /* Entry should match with supplied QoS. */
            mqttStatus = MQTTBadParameter;
        }
    }
    else
    {
        /* QoS 1 or 2 receive. Nothing to be done. */
    }

    if( ( qos != MQTTQoS0 ) && ( mqttStatus == MQTTSuccess ) )
    {
        newState = MQTT_CalculateStatePublish( opType, qos );
        /* Validate state transition and update state records. */
        mqttStatus = updateStatePublish( pMqttContext,
                                         recordIndex,
                                         packetId,
                                         opType,
                                         qos,
                                         currentState,
                                         newState );

        /* Update output parameter on success. */
        if( mqttStatus == MQTTSuccess )
        {
            *pNewState = newState;
        }
    }

    return mqttStatus;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_UpdateStateAck( MQTTContext_t * pMqttContext,
                                  uint16_t packetId,
                                  MQTTPubAckType_t packetType,
                                  MQTTStateOperation_t opType,
                                  MQTTPublishState_t * pNewState )
{
    MQTTPublishState_t newState = MQTTStateNull;
    MQTTPublishState_t currentState = MQTTStateNull;
    bool isOutgoingPublish = isPublishOutgoing( packetType, opType );
    MQTTQoS_t qos = MQTTQoS0;
    size_t recordIndex = MQTT_STATE_ARRAY_MAX_COUNT;
    MQTTPubAckInfo_t * records = NULL;
    MQTTStatus_t status = MQTTBadParameter;

    if( ( pMqttContext == NULL ) || ( pNewState == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pMqttContext=%p, pNewState=%p.",
                    pMqttContext,
                    pNewState ) );
    }
    else
    {
        if( isOutgoingPublish == true )
        {
            records = pMqttContext->outgoingPublishRecords;
        }
        else
        {
            records = pMqttContext->incomingPublishRecords;
        }

        recordIndex = findInRecord( records,
                                    MQTT_STATE_ARRAY_MAX_COUNT,
                                    packetId,
                                    &qos,
                                    &currentState );
    }

    if( recordIndex < MQTT_STATE_ARRAY_MAX_COUNT )
    {
        newState = MQTT_CalculateStateAck( packetType, opType, qos );

        /* Validate state transition and update state record. */
        status = updateStateAck( records, recordIndex, packetId, currentState, newState );

        /* Update the output parameter. */
        if( status == MQTTSuccess )
        {
            *pNewState = newState;
        }
    }
    else
    {
        LogError( ( "No matching record found for publish %u.", packetId ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

uint16_t MQTT_PubrelToResend( const MQTTContext_t * pMqttContext,
                              MQTTStateCursor_t * pCursor,
                              MQTTPublishState_t * pState )
{
    uint16_t packetId = MQTT_PACKET_ID_INVALID;
    uint16_t searchStates = 0U;

    /* Validate arguments. */
    if( ( pMqttContext == NULL ) || ( pCursor == NULL ) || ( pState == NULL ) )
    {
        LogError( ( "Arguments cannot be NULL pMqttContext =%p, pCursor=%p"
                    " pState=%p.",
                    pMqttContext,
                    pCursor,
                    pState ) );
    }
    else
    {
        /* PUBREL for packets in state #MQTTPubCompPending and #MQTTPubRelSend
         * would need to be resent when a session is reestablished.*/
        UINT16_SET_BIT( searchStates, MQTTPubCompPending );
        UINT16_SET_BIT( searchStates, MQTTPubRelSend );
        packetId = stateSelect( pMqttContext, searchStates, pCursor );

        /* The state needs to be in #MQTTPubRelSend for sending PUBREL. */
        if( packetId != MQTT_PACKET_ID_INVALID )
        {
            *pState = MQTTPubRelSend;
        }
    }

    return packetId;
}

/*-----------------------------------------------------------*/

uint16_t MQTT_PublishToResend( const MQTTContext_t * pMqttContext,
                               MQTTStateCursor_t * pCursor )
{
    uint16_t packetId = MQTT_PACKET_ID_INVALID;
    uint16_t searchStates = 0U;

    /* Validate arguments. */
    if( ( pMqttContext == NULL ) || ( pCursor == NULL ) )
    {
        LogError( ( "Arguments cannot be NULL pMqttContext =%p, pCursor=%p",
                    pMqttContext,
                    pCursor ) );
    }
    else
    {
        /* Packets in state #MQTTPublishSend, #MQTTPubAckPending and
         * #MQTTPubRecPending would need to be resent when a session is
         * reestablished. */
        UINT16_SET_BIT( searchStates, MQTTPublishSend );
        UINT16_SET_BIT( searchStates, MQTTPubAckPending );
        UINT16_SET_BIT( searchStates, MQTTPubRecPending );

        packetId = stateSelect( pMqttContext, searchStates, pCursor );
    }

    return packetId;
}

/*-----------------------------------------------------------*/

const char * MQTT_State_strerror( MQTTPublishState_t state )
{
    const char * str = NULL;

    switch( state )
    {
        case MQTTStateNull:
            str = "MQTTStateNull";
            break;

        case MQTTPublishSend:
            str = "MQTTPublishSend";
            break;

        case MQTTPubAckSend:
            str = "MQTTPubAckSend";
            break;

        case MQTTPubRecSend:
            str = "MQTTPubRecSend";
            break;

        case MQTTPubRelSend:
            str = "MQTTPubRelSend";
            break;

        case MQTTPubCompSend:
            str = "MQTTPubCompSend";
            break;

        case MQTTPubAckPending:
            str = "MQTTPubAckPending";
            break;

        case MQTTPubRecPending:
            str = "MQTTPubRecPending";
            break;

        case MQTTPubRelPending:
            str = "MQTTPubRelPending";
            break;

        case MQTTPubCompPending:
            str = "MQTTPubCompPending";
            break;

        case MQTTPublishDone:
            str = "MQTTPublishDone";
            break;

        default:
            /* Invalid state received. */
            str = "Invalid MQTT State";
            break;
    }

    return str;
}

/*-----------------------------------------------------------*/
