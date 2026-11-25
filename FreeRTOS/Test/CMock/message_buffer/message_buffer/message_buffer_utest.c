/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
/*! @file message_buffer_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>

/* Message Buffer includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "message_buffer.h"

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "CException.h"

/* Mock includes. */
#include "mock_task.h"
#include "mock_fake_assert.h"
#include "mock_fake_port.h"

/**
 * @brief Sample size in bytes of the message buffer used for test.
 * Keep it short enough so that they can be allocated on stack.
 */
#define TEST_MESSAGE_BUFFER_SIZE             ( 64U )

/**
 * @brief Minimum size required to store the length of the message.
 */
#define TEST_MESSAGE_METADATA_SIZE           ( sizeof( configMESSAGE_BUFFER_LENGTH_TYPE ) )

/**
 * @brief Maximum size of a message that can be sent to a message buffer.
 * Each message stores an associated length of the message as metadata. So maximum message
 * size at any time is total length - size of the variable used to store length.
 */
#define TEST_MAX_MESSAGE_SIZE                ( TEST_MESSAGE_BUFFER_SIZE - TEST_MESSAGE_METADATA_SIZE )

/**
 * @brief Maximum unsigned long value so as to trigger an integer overflow.
 */
#define TEST_MESSAGE_BUFFER_MAX_UINT_SIZE    ( ~( size_t ) ( 0UL ) )

/**
 * @brief Ticks to wait from tests if the message buffer is full while sending data or
 * below trigger level while receiving data.
 */
#define TEST_MESSAGE_BUFFER_WAIT_TICKS       ( 1000U )

/**
 * @brief CException code for when a configASSERT should be intercepted.
 */
#define configASSERT_E                       0xAA101

/**
 * @brief Expect a configASSERT from the function called.
 *  Break out of the called function when this occurs.
 * @details Use this macro when the call passed in as a parameter is expected
 * to cause invalid memory access.
 */
#define EXPECT_ASSERT_BREAK( call )                 \
    do                                              \
    {                                               \
        shouldAbortOnAssertion = true;              \
        CEXCEPTION_T e = CEXCEPTION_NONE;           \
        Try                                         \
        {                                           \
            call;                                   \
            TEST_FAIL();                            \
        }                                           \
        Catch( e )                                  \
        {                                           \
            TEST_ASSERT_EQUAL( configASSERT_E, e ); \
        }                                           \
    } while( 0 )

/* ============================  GLOBAL VARIABLES =========================== */

/**
 * @brief Global counter for the number of assertions in code.
 */
static int assertionFailed = 0;

/**
 * @brief Global counter to keep track of how many times a sender task was woken up by a task receiving from the stream buffer.
 */
static int senderTaskWoken = 0;

/**
 * @brief Global counter to keep track of how many times a receiver task was woken up by a task sending to the buffer.
 */
static int receiverTaskWoken = 0;

/**
 * @brief Dummy sender task handle to which the stream buffer receive APIs will send notification.
 */
static TaskHandle_t senderTask = ( TaskHandle_t ) ( 0xAABBCCDD );

/**
 * @brief Dummy receiver task handle to which the stream buffer send APIs will send notifications.
 */
static TaskHandle_t receiverTask = ( TaskHandle_t ) ( 0xABCDEEFF );

/**
 * @brief Global message buffer handle used for tests.
 */
static MessageBufferHandle_t xMessageBuffer;

/**
 * @brief Flag which denotes if test need to abort on assertion.
 */
static BaseType_t shouldAbortOnAssertion;

/* ==========================  CALLBACK FUNCTIONS =========================== */

void * pvPortMalloc( size_t xSize )
{
    return unity_malloc( xSize );
}
void vPortFree( void * pv )
{
    return unity_free( pv );
}

static void vFakeAssertStub( bool x,
                             char * file,
                             int line,
                             int cmock_num_calls )
{
    if( !x )
    {
        assertionFailed++;

        if( shouldAbortOnAssertion == pdTRUE )
        {
            Throw( configASSERT_E );
        }
    }
}

static BaseType_t senderTaskNotificationCallback( TaskHandle_t xTaskToNotify,
                                                  UBaseType_t uxIndexToNotify,
                                                  uint32_t ulValue,
                                                  eNotifyAction eAction,
                                                  uint32_t * pulPreviousNotificationValue,
                                                  int cmock_num_calls )
{
    TEST_ASSERT_EQUAL( senderTask, xTaskToNotify );
    senderTaskWoken++;
    return pdTRUE;
}

static BaseType_t messageBufferReceiveFromISRCallback( UBaseType_t uxIndexToWaitOn,
                                                       uint32_t ulBitsToClearOnEntry,
                                                       uint32_t ulBitsToClearOnExit,
                                                       uint32_t * pulNotificationValue,
                                                       TickType_t xTicksToWait,
                                                       int cmock_num_calls )
{
    uint8_t data[ TEST_MAX_MESSAGE_SIZE ] = { 0 };
    size_t dataReceived = 0;
    BaseType_t senderTaskWokenFromISR = pdFALSE;

    dataReceived = xMessageBufferReceiveFromISR( xMessageBuffer, data, TEST_MAX_MESSAGE_SIZE, &senderTaskWokenFromISR );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, dataReceived );
    return pdTRUE;
}

static BaseType_t messageBufferReceiveCallback( UBaseType_t uxIndexToWaitOn,
                                                uint32_t ulBitsToClearOnEntry,
                                                uint32_t ulBitsToClearOnExit,
                                                uint32_t * pulNotificationValue,
                                                TickType_t xTicksToWait,
                                                int cmock_num_calls )
{
    uint8_t data[ TEST_MAX_MESSAGE_SIZE ] = { 0 };
    size_t dataReceived = 0;

    /* Read next message from message buffer to wake up sender task. */
    dataReceived = xMessageBufferReceive( xMessageBuffer, data, TEST_MAX_MESSAGE_SIZE, 0 );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, dataReceived );
    return pdTRUE;
}

static BaseType_t messageBufferSendFromISRCallback( UBaseType_t uxIndexToWaitOn,
                                                    uint32_t ulBitsToClearOnEntry,
                                                    uint32_t ulBitsToClearOnExit,
                                                    uint32_t * pulNotificationValue,
                                                    TickType_t xTicksToWait,
                                                    int cmock_num_calls )
{
    BaseType_t receiverTaskWokenFromISR = pdFALSE;
    uint8_t data[ TEST_MAX_MESSAGE_SIZE ] = { 0 };
    size_t dataSent = 0;

    dataSent = xMessageBufferSendFromISR( xMessageBuffer, data, TEST_MAX_MESSAGE_SIZE, &receiverTaskWokenFromISR );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, dataSent );
    return pdTRUE;
}

static BaseType_t messageBufferSendCallback( UBaseType_t uxIndexToWaitOn,
                                             uint32_t ulBitsToClearOnEntry,
                                             uint32_t ulBitsToClearOnExit,
                                             uint32_t * pulNotificationValue,
                                             TickType_t xTicksToWait,
                                             int cmock_num_calls )
{
    uint8_t data[ TEST_MAX_MESSAGE_SIZE ] = { 0 };
    size_t dataSent = 0;

    /* Send a single message of max message size to message buffer to wake up receiver Task. */
    dataSent = xMessageBufferSend( xMessageBuffer, data, TEST_MAX_MESSAGE_SIZE, 0 );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, dataSent );
    return pdTRUE;
}

static BaseType_t receiverTaskNotificationCallback( TaskHandle_t xTaskToNotify,
                                                    UBaseType_t uxIndexToNotify,
                                                    uint32_t ulValue,
                                                    eNotifyAction eAction,
                                                    uint32_t * pulPreviousNotificationValue,
                                                    int cmock_num_calls )
{
    TEST_ASSERT_EQUAL( receiverTask, xTaskToNotify );
    receiverTaskWoken++;
    return pdTRUE;
}

/*******************************************************************************
 * Unity fixtures
 ******************************************************************************/
/*! called before each test case */
void setUp( void )
{
    assertionFailed = 0;
    xMessageBuffer = NULL;
    senderTaskWoken = 0;
    receiverTaskWoken = 0;
    shouldAbortOnAssertion = pdTRUE;

    mock_task_Init();
    mock_fake_assert_Init();
    mock_fake_port_Init();

    vFakePortEnterCriticalSection_Ignore();
    vFakePortExitCriticalSection_Ignore();
    ulFakePortSetInterruptMaskFromISR_IgnoreAndReturn( 0U );
    vFakePortClearInterruptMaskFromISR_Ignore();
    vFakeAssert_StubWithCallback( vFakeAssertStub );
    /* Track calls to malloc / free */
    UnityMalloc_StartTest();
}

/*! called after each test case */
void tearDown( void )
{
    TEST_ASSERT_EQUAL_MESSAGE( 0, assertionFailed, "Assertion check failed in code." );
    UnityMalloc_EndTest();

    mock_task_Verify();
    mock_task_Destroy();

    mock_fake_assert_Verify();
    mock_fake_assert_Destroy();

    mock_fake_port_Verify();
    mock_fake_port_Destroy();
}

/*! called at the beginning of the whole suite */
void suiteSetUp()
{
}

/*! called at the end of the whole suite */
int suiteTearDown( int numFailures )
{
    return numFailures;
}

static void validate_message_buffer_init_state( MessageBufferHandle_t xMessageBuffer,
                                                size_t bufferSize )
{
    TEST_ASSERT_TRUE( xMessageBufferIsEmpty( xMessageBuffer ) );
    TEST_ASSERT_FALSE( xMessageBufferIsFull( xMessageBuffer ) );
    TEST_ASSERT_EQUAL( bufferSize, xMessageBufferSpacesAvailable( xMessageBuffer ) );
    TEST_ASSERT_EQUAL( 0, xStreamBufferNextMessageLengthBytes( xMessageBuffer ) );
    TEST_ASSERT_EQUAL( 1, ucStreamBufferGetStreamBufferType( xMessageBuffer ) );
}

static void validate_and_clear_assertions( void )
{
    TEST_ASSERT_EQUAL( 1, assertionFailed );
    assertionFailed = 0;
}

/**
 * @brief Discard the full message while a sender is waiting for space.
 */
static BaseType_t messageBufferDiscardCallback( UBaseType_t uxIndexToWaitOn,
                                                uint32_t ulBitsToClearOnEntry,
                                                uint32_t ulBitsToClearOnExit,
                                                uint32_t * pulNotificationValue,
                                                TickType_t xTicksToWait,
                                                int cmock_num_calls )
{
    TEST_ASSERT_EQUAL( 2U, uxIndexToWaitOn );
    TEST_ASSERT_EQUAL( TEST_MESSAGE_BUFFER_WAIT_TICKS, xTicksToWait );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, xMessageBufferDiscard( xMessageBuffer ) );
    return pdTRUE;
}

/**
 * @brief Move the ring using public APIs, then discard across a selected boundary.
 */
static void validate_message_buffer_discard_wrap( size_t xInitialOffset,
                                                  size_t xDiscardLength )
{
    StaticMessageBuffer_t xStaticMessageBuffer;
    uint8_t ucStorage[ TEST_MESSAGE_BUFFER_SIZE + 1U ] = { 0 };
    uint8_t ucData[ TEST_MESSAGE_BUFFER_SIZE ] = { 0xA5 };
    const uint8_t ucFollowingMessage[] = { 0x11, 0x00, 0xFF };
    uint8_t ucReceived[ TEST_MESSAGE_BUFFER_SIZE ] = { 0 };
    size_t xPaddingLength = xInitialOffset - TEST_MESSAGE_METADATA_SIZE;

    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );
    xMessageBuffer = xMessageBufferCreateStatic( sizeof( ucStorage ), ucStorage, &xStaticMessageBuffer );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );

    /* After sending and receiving padding, both ring positions are at the
     * requested offset. No private stream buffer fields are modified. */
    TEST_ASSERT_EQUAL( xPaddingLength, xMessageBufferSend( xMessageBuffer, ucData, xPaddingLength, 0 ) );
    TEST_ASSERT_EQUAL( xPaddingLength, xMessageBufferReceive( xMessageBuffer, ucReceived, sizeof( ucReceived ), 0 ) );
    TEST_ASSERT_EQUAL( xDiscardLength, xMessageBufferSend( xMessageBuffer, ucData, xDiscardLength, 0 ) );
    TEST_ASSERT_EQUAL( sizeof( ucFollowingMessage ), xMessageBufferSend( xMessageBuffer, ucFollowingMessage, sizeof( ucFollowingMessage ), 0 ) );

    TEST_ASSERT_EQUAL( xDiscardLength, xMessageBufferDiscard( xMessageBuffer ) );
    TEST_ASSERT_EQUAL( sizeof( ucFollowingMessage ), xStreamBufferNextMessageLengthBytes( xMessageBuffer ) );
    TEST_ASSERT_EQUAL( sizeof( ucFollowingMessage ), xMessageBufferReceive( xMessageBuffer, ucReceived, sizeof( ucReceived ), 0 ) );
    TEST_ASSERT_EQUAL_MEMORY( ucFollowingMessage, ucReceived, sizeof( ucFollowingMessage ) );
    TEST_ASSERT_EQUAL( TEST_MESSAGE_BUFFER_SIZE, xMessageBufferSpacesAvailable( xMessageBuffer ) );
    vMessageBufferDelete( xMessageBuffer );
}

/**
 * @brief The discard receive tuple must not consume stream or batching data.
 */
static void validate_message_buffer_discard_non_message( StreamBufferHandle_t xBuffer )
{
    const uint8_t ucData[] = { 0x12, 0x00, 0x34, 0xFF };
    uint8_t ucReceived[ sizeof( ucData ) ] = { 0 };

    TEST_ASSERT_NOT_NULL( xBuffer );
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );
    TEST_ASSERT_EQUAL( sizeof( ucData ), xStreamBufferSend( xBuffer, ucData, sizeof( ucData ), 0 ) );
    TEST_ASSERT_EQUAL( 0, xMessageBufferDiscard( xBuffer ) );
    TEST_ASSERT_EQUAL( sizeof( ucData ), xStreamBufferBytesAvailable( xBuffer ) );
    TEST_ASSERT_EQUAL( sizeof( ucData ), xStreamBufferReceive( xBuffer, ucReceived, sizeof( ucReceived ), 0 ) );
    TEST_ASSERT_EQUAL_MEMORY( ucData, ucReceived, sizeof( ucData ) );
    vStreamBufferDelete( xBuffer );
}

/* ==============================  Test Cases  ============================== */

/**
 * @brief An empty discard returns immediately, without task notification calls.
 * @coverage xStreamBufferReceive
 */
void test_xMessageBufferDiscard_empty( void )
{
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );
    TEST_ASSERT_EQUAL( 0, xMessageBufferDiscard( xMessageBuffer ) );
    TEST_ASSERT_EQUAL( TEST_MESSAGE_BUFFER_SIZE, xMessageBufferSpacesAvailable( xMessageBuffer ) );
    vMessageBufferDelete( xMessageBuffer );
}

/**
 * @brief Discard the first message only after a too-small receive leaves it queued.
 * @coverage xStreamBufferReceive
 */
void test_xMessageBufferDiscard_preserves_following_message( void )
{
    const uint8_t ucFirst[] = { 0x11, 0x22, 0x33, 0x44 };
    const uint8_t ucSecond[] = { 0x00, 0xFF, 0x55 };
    uint8_t ucReceived[ sizeof( ucFirst ) ] = { 0xA5, 0xA5, 0xA5, 0xA5 };
    const uint8_t ucUnchanged[] = { 0xA5, 0xA5, 0xA5, 0xA5 };
    size_t xSpaceBeforeDiscard;

    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );
    TEST_ASSERT_EQUAL( sizeof( ucFirst ), xMessageBufferSend( xMessageBuffer, ucFirst, sizeof( ucFirst ), 0 ) );
    TEST_ASSERT_EQUAL( sizeof( ucSecond ), xMessageBufferSend( xMessageBuffer, ucSecond, sizeof( ucSecond ), 0 ) );

    TEST_ASSERT_EQUAL( 0, xMessageBufferReceive( xMessageBuffer, ucReceived, sizeof( ucFirst ) - 1U, 0 ) );
    TEST_ASSERT_EQUAL_MEMORY( ucUnchanged, ucReceived, sizeof( ucReceived ) );
    TEST_ASSERT_EQUAL( sizeof( ucFirst ), xStreamBufferNextMessageLengthBytes( xMessageBuffer ) );
    xSpaceBeforeDiscard = xMessageBufferSpacesAvailable( xMessageBuffer );
    TEST_ASSERT_EQUAL( sizeof( ucFirst ), xMessageBufferDiscard( xMessageBuffer ) );
    TEST_ASSERT_EQUAL( xSpaceBeforeDiscard + sizeof( ucFirst ) + TEST_MESSAGE_METADATA_SIZE, xMessageBufferSpacesAvailable( xMessageBuffer ) );
    TEST_ASSERT_EQUAL( sizeof( ucSecond ), xStreamBufferNextMessageLengthBytes( xMessageBuffer ) );
    TEST_ASSERT_EQUAL( sizeof( ucSecond ), xMessageBufferReceive( xMessageBuffer, ucReceived, sizeof( ucReceived ), 0 ) );
    TEST_ASSERT_EQUAL_MEMORY( ucSecond, ucReceived, sizeof( ucSecond ) );
    TEST_ASSERT_EQUAL( 0, xMessageBufferDiscard( xMessageBuffer ) );
    vMessageBufferDelete( xMessageBuffer );
}

/**
 * @brief Discarding the smallest message restores all space.
 * @coverage xStreamBufferReceive
 */
void test_xMessageBufferDiscard_one_byte( void )
{
    uint8_t ucData = 0xA5;

    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );
    TEST_ASSERT_EQUAL( sizeof( ucData ), xMessageBufferSend( xMessageBuffer, &ucData, sizeof( ucData ), 0 ) );
    TEST_ASSERT_EQUAL( sizeof( ucData ), xMessageBufferDiscard( xMessageBuffer ) );
    TEST_ASSERT_EQUAL( pdTRUE, xMessageBufferIsEmpty( xMessageBuffer ) );
    TEST_ASSERT_EQUAL( TEST_MESSAGE_BUFFER_SIZE, xMessageBufferSpacesAvailable( xMessageBuffer ) );
    vMessageBufferDelete( xMessageBuffer );
}

/**
 * @brief Discarding a full buffer permits another maximum-size send.
 * @coverage xStreamBufferReceive
 */
void test_xMessageBufferDiscard_full( void )
{
    uint8_t ucData[ TEST_MAX_MESSAGE_SIZE ] = { 0xA5 };
    uint8_t ucReceived[ TEST_MAX_MESSAGE_SIZE ] = { 0 };

    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );
    TEST_ASSERT_EQUAL( sizeof( ucData ), xMessageBufferSend( xMessageBuffer, ucData, sizeof( ucData ), 0 ) );
    TEST_ASSERT_EQUAL( 0, xMessageBufferSpacesAvailable( xMessageBuffer ) );
    TEST_ASSERT_EQUAL( sizeof( ucData ), xMessageBufferDiscard( xMessageBuffer ) );
    TEST_ASSERT_EQUAL( sizeof( ucData ), xMessageBufferSend( xMessageBuffer, ucData, sizeof( ucData ), 0 ) );
    TEST_ASSERT_EQUAL( sizeof( ucData ), xMessageBufferReceive( xMessageBuffer, ucReceived, sizeof( ucReceived ), 0 ) );
    TEST_ASSERT_EQUAL_MEMORY( ucData, ucReceived, sizeof( ucData ) );
    vMessageBufferDelete( xMessageBuffer );
}

/**
 * @brief The first message length header straddles the ring boundary.
 * @coverage xStreamBufferReceive
 */
void test_xMessageBufferDiscard_wrapped_length_header( void )
{
    validate_message_buffer_discard_wrap( TEST_MESSAGE_BUFFER_SIZE, 5U );
}

/**
 * @brief The first message payload straddles the ring boundary.
 * @coverage xStreamBufferReceive
 */
void test_xMessageBufferDiscard_wrapped_payload( void )
{
    validate_message_buffer_discard_wrap( TEST_MESSAGE_BUFFER_SIZE - TEST_MESSAGE_METADATA_SIZE, 5U );
}

/**
 * @brief The discarded payload ends exactly at the ring boundary.
 * @coverage xStreamBufferReceive
 */
void test_xMessageBufferDiscard_payload_ends_at_boundary( void )
{
    validate_message_buffer_discard_wrap( TEST_MESSAGE_BUFFER_SIZE - TEST_MESSAGE_METADATA_SIZE - 4U, 5U );
}

/**
 * @brief The reserved discard tuple must leave a normal stream unchanged.
 * @coverage xStreamBufferReceive
 */
void test_xMessageBufferDiscard_stream_unchanged( void )
{
    validate_message_buffer_discard_non_message( xStreamBufferCreate( TEST_MESSAGE_BUFFER_SIZE, 1U ) );
}

/**
 * @brief The reserved discard tuple must leave a batching stream unchanged.
 * @coverage xStreamBufferReceive
 */
void test_xMessageBufferDiscard_batching_stream_unchanged( void )
{
    validate_message_buffer_discard_non_message( xStreamBatchingBufferCreate( TEST_MESSAGE_BUFFER_SIZE, 1U ) );
}

/**
 * @brief Discard notifies the blocked writer through its configured index.
 * @coverage xStreamBufferReceive
 */
void test_xMessageBufferDiscard_unblocks_sender( void )
{
    uint8_t ucFirst[ TEST_MAX_MESSAGE_SIZE ] = { 0xA5 };
    const uint8_t ucSecond[] = { 0x00, 0x12, 0xFF };
    uint8_t ucReceived[ sizeof( ucSecond ) ] = { 0 };

    vTaskSetTimeOutState_Ignore();
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( senderTask );
    xTaskGenericNotifyWait_StubWithCallback( messageBufferDiscardCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );
    vStreamBufferSetStreamBufferNotificationIndex( xMessageBuffer, 2U );
    TEST_ASSERT_EQUAL( sizeof( ucFirst ), xMessageBufferSend( xMessageBuffer, ucFirst, sizeof( ucFirst ), 0 ) );
    xTaskGenericNotify_ExpectAndReturn( senderTask, 2U, 0, eNoAction, NULL, pdPASS );
    TEST_ASSERT_EQUAL( sizeof( ucSecond ), xMessageBufferSend( xMessageBuffer, ucSecond, sizeof( ucSecond ), TEST_MESSAGE_BUFFER_WAIT_TICKS ) );
    TEST_ASSERT_EQUAL( sizeof( ucSecond ), xMessageBufferReceive( xMessageBuffer, ucReceived, sizeof( ucReceived ), 0 ) );
    TEST_ASSERT_EQUAL_MEMORY( ucSecond, ucReceived, sizeof( ucSecond ) );
    vMessageBufferDelete( xMessageBuffer );
}

/**
 * @brief A zero-sized receive with a real destination retains the head message.
 * @coverage xStreamBufferReceive
 */
void test_xMessageBufferDiscard_preserves_zero_sized_receive( void )
{
    const uint8_t ucData[] = { 0x00, 0xA5 };
    uint8_t ucReceived[ sizeof( ucData ) ] = { 0 };

    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );
    TEST_ASSERT_EQUAL( sizeof( ucData ), xMessageBufferSend( xMessageBuffer, ucData, sizeof( ucData ), 0 ) );
    TEST_ASSERT_EQUAL( 0, xMessageBufferReceive( xMessageBuffer, ucReceived, 0, 0 ) );
    TEST_ASSERT_EQUAL( sizeof( ucData ), xStreamBufferNextMessageLengthBytes( xMessageBuffer ) );
    TEST_ASSERT_EQUAL( sizeof( ucData ), xMessageBufferReceive( xMessageBuffer, ucReceived, sizeof( ucReceived ), 0 ) );
    TEST_ASSERT_EQUAL_MEMORY( ucData, ucReceived, sizeof( ucData ) );
    vMessageBufferDelete( xMessageBuffer );
}

/**
 * @brief Only the nonblocking NULL/zero combination is a discard request.
 * @coverage xStreamBufferReceive
 */
void test_xMessageBufferDiscard_preserves_invalid_receive_assertions( void )
{
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );
    EXPECT_ASSERT_BREAK( ( void ) xMessageBufferReceive( xMessageBuffer, NULL, 1U, 0 ) );
    validate_and_clear_assertions();
    EXPECT_ASSERT_BREAK( ( void ) xMessageBufferReceive( xMessageBuffer, NULL, 0, 1U ) );
    validate_and_clear_assertions();
    EXPECT_ASSERT_BREAK( ( void ) xMessageBufferDiscard( NULL ) );
    validate_and_clear_assertions();
    vMessageBufferDelete( xMessageBuffer );
}

/**
 * @brief Validates that message buffer of sample test size is created successfully.
 */
void test_xMessageBufferCreate_success( void )
{
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_EQUAL( NULL, xMessageBuffer );
    validate_message_buffer_init_state( xMessageBuffer, TEST_MESSAGE_BUFFER_SIZE );
    vMessageBufferDelete( xMessageBuffer );
}

/**
 * @brief API should fail and return null if there is an integer overflow in message buffer size passed.
 */
void test_xMessageBufferCreate_integer_overflow( void )
{
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_MAX_UINT_SIZE );
    TEST_ASSERT_EQUAL( NULL, xMessageBuffer );
}

/**
 * @brief API should fail and return null if the malloc fails.
 */
void test_xMessageBufferCreate_malloc_fail( void )
{
    UnityMalloc_MakeMallocFailAfterCount( 0 );
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NULL( xMessageBuffer );
}

/**
 * @brief Should assert if a zero size is passed to create API.
 */
void test_xMessageBufferCreate_zero_size( void )
{
    EXPECT_ASSERT_BREAK( ( void ) xMessageBufferCreate( 0 ) );

    validate_and_clear_assertions();
}

/**
 * @brief Should assert if the size passed is less than the minimum size required to store metadata size.
 */
void test_xMessageBufferCreate_invalid_size( void )
{
    EXPECT_ASSERT_BREAK( ( void ) xMessageBufferCreate( TEST_MESSAGE_METADATA_SIZE ) );

    validate_and_clear_assertions();
}

/**
 * @brief Validates message buffer creation through a static buffer allocated by the user.
 */
void test_xMessageBufferCreateStatic_success( void )
{
    StaticMessageBuffer_t messageBufferStruct;
    /* The size of message buffer array should be one greater than the required size of message buffer. */
    uint8_t messageBufferArray[ TEST_MESSAGE_BUFFER_SIZE + 1 ] = { 0 };

    xMessageBuffer = xMessageBufferCreateStatic( sizeof( messageBufferArray ), messageBufferArray, &messageBufferStruct );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );

    validate_message_buffer_init_state( xMessageBuffer, TEST_MESSAGE_BUFFER_SIZE );

    vStreamBufferDelete( xMessageBuffer );
}

/**
 * @brief Validates message buffer creation fails if null array is passed.
 */
void test_xMessageBufferCreateStatic_null_array( void )
{
    StaticMessageBuffer_t messageBufferStruct;

    /* Tests should abort if assertion is enabled or return NULL. */
    shouldAbortOnAssertion = pdFALSE;

    /* Returns NULL when NULL storage area is passed as a parameter. */
    xMessageBuffer = xMessageBufferCreateStatic( TEST_MESSAGE_BUFFER_SIZE, NULL, &messageBufferStruct );
    TEST_ASSERT_NULL( xMessageBuffer );

    validate_and_clear_assertions();
}

/**
 * @brief Validates message buffer creation fails if NULL struct is passed.
 */
void test_xMessageBufferCreateStatic_null_struct( void )
{
    /* The size of message buffer array should be one greater than the required size of message buffer. */
    uint8_t messageBufferArray[ TEST_MESSAGE_BUFFER_SIZE + 1 ] = { 0 };

    /* Tests should abort if assertion is enabled or return NULL. */
    shouldAbortOnAssertion = pdFALSE;

    /* Returns NULL when NULL message buffer struct is passed as a parameter. */
    xMessageBuffer = xMessageBufferCreateStatic( sizeof( messageBufferArray ), messageBufferArray, NULL );
    TEST_ASSERT_NULL( xMessageBuffer );

    validate_and_clear_assertions();
}

/**
 * @brief Validates message buffer create assert if the size passed is less than the minimum size required to store metadata size.
 */
void test_xMessageBufferCreateStatic_invalid_size( void )
{
    StaticMessageBuffer_t messageBufferStruct;
    /* The size of message buffer array should be one greater than the required size of message buffer. */
    uint8_t messageBufferArray[ TEST_MESSAGE_BUFFER_SIZE + 1 ] = { 0 };

    EXPECT_ASSERT_BREAK( ( void ) xMessageBufferCreateStatic( TEST_MESSAGE_METADATA_SIZE, messageBufferArray, &messageBufferStruct ) );

    validate_and_clear_assertions();
}

/**
 * @brief Validate message buffer creation asserts if the size passed is zero.
 */
void test_xMessageBufferCreateStatic_zero_size( void )
{
    StaticMessageBuffer_t messageBufferStruct;
    /* The size of message buffer array should be one greater than the required size of message buffer. */
    uint8_t messageBufferArray[ TEST_MESSAGE_BUFFER_SIZE + 1 ] = { 0 };

    EXPECT_ASSERT_BREAK( ( void ) xMessageBufferCreateStatic( 0, messageBufferArray, &messageBufferStruct ) );

    validate_and_clear_assertions();
}

/**
 * @brief Validates a task is able to send upto maximum message size allowed, without blocking.
 */
void test_xMessageBufferSend_success( void )
{
    uint8_t data[ TEST_MAX_MESSAGE_SIZE ] = { 0 };
    size_t dataSent = 0;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a message buffer of the default test sample size. */
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );
    TEST_ASSERT_EQUAL( TEST_MESSAGE_BUFFER_SIZE, xMessageBufferSpacesAvailable( xMessageBuffer ) );

    /* Sending bytes of size  upto to available size should succeed. Sender task should not be in blocked state. */
    dataSent = xMessageBufferSend( xMessageBuffer, data, TEST_MAX_MESSAGE_SIZE, TEST_MESSAGE_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, dataSent );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, xStreamBufferNextMessageLengthBytes( xMessageBuffer ) );
    TEST_ASSERT_EQUAL( pdFALSE, xMessageBufferIsEmpty( xMessageBuffer ) );

    vStreamBufferDelete( xMessageBuffer );
}

/**
 * @brief An integer overflow in message size to be sent should result in an
 * assertion failure
 */
void test_xMessageBufferSend_message_size_integer_overflow( void )
{
    uint8_t data[ TEST_MAX_MESSAGE_SIZE ] = { 0 };

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a message buffer of the default test sample size. */
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );

    EXPECT_ASSERT_BREAK( ( void ) xMessageBufferSend( xMessageBuffer, data, TEST_MESSAGE_BUFFER_MAX_UINT_SIZE, TEST_MESSAGE_BUFFER_WAIT_TICKS ) );

    validate_and_clear_assertions();

    vStreamBufferDelete( xMessageBuffer );
}

/**
 * Sending a message of size greater than available size should return zero bytes sent.
 */
void test_xMessageBufferSend_message_larger_than_available_size( void )
{
    uint8_t message[ TEST_MAX_MESSAGE_SIZE + 1 ] = { 0 };
    size_t sentBytes = 0;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a message buffer of sample size. */
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );
    TEST_ASSERT_EQUAL( TEST_MESSAGE_BUFFER_SIZE, xMessageBufferSpacesAvailable( xMessageBuffer ) );

    sentBytes = xMessageBufferSend( xMessageBuffer, message, TEST_MAX_MESSAGE_SIZE + 1, TEST_MESSAGE_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 0, sentBytes );
    TEST_ASSERT_EQUAL( TEST_MESSAGE_BUFFER_SIZE, xMessageBufferSpacesAvailable( xMessageBuffer ) );

    vStreamBufferDelete( xMessageBuffer );
}

/**
 * @brief Sending null message should trigger an assert.
 */
void test_xMessageBufferSend_null_message( void )
{
    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a message buffer of sample size. */
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );

    EXPECT_ASSERT_BREAK( ( void ) xMessageBufferSend( xMessageBuffer, NULL, TEST_MAX_MESSAGE_SIZE + 1, TEST_MESSAGE_BUFFER_WAIT_TICKS ) );

    validate_and_clear_assertions();

    vStreamBufferDelete( xMessageBuffer );
}

/**
 * @brief Sending to a null message buffer should trigger an assert.
 */
void test_xMessageBufferSend_null_message_buffer( void )
{
    uint8_t message[ TEST_MAX_MESSAGE_SIZE + 1 ] = { 0 };

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a message buffer of sample size. */
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );

    EXPECT_ASSERT_BREAK( ( void ) xMessageBufferSend( NULL, message, TEST_MAX_MESSAGE_SIZE + 1, TEST_MESSAGE_BUFFER_WAIT_TICKS ) );

    validate_and_clear_assertions();

    vStreamBufferDelete( xMessageBuffer );
}

/**
 * @brief Validates that a task blocks if there is insufficient space in message buffer for a valid message to be sent.
 * Task then succeeds once enough space is available by reading from the message buffer.
 */
void test_xMessageBufferSend_blocking( void )
{
    uint8_t message[ TEST_MAX_MESSAGE_SIZE ] = { 0 };
    size_t sentBytes = 0;

    vTaskSetTimeOutState_Ignore();
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( senderTask );
    xTaskGenericNotifyWait_StubWithCallback( messageBufferReceiveCallback );
    xTaskGenericNotify_StubWithCallback( senderTaskNotificationCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a message buffer of sample size. */
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );
    TEST_ASSERT_EQUAL( TEST_MESSAGE_BUFFER_SIZE, xMessageBufferSpacesAvailable( xMessageBuffer ) );

    /* Sending max message size so that message buffer is full. */
    sentBytes = xMessageBufferSend( xMessageBuffer, message, TEST_MAX_MESSAGE_SIZE, TEST_MESSAGE_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, sentBytes );
    TEST_ASSERT_EQUAL( 0, xMessageBufferSpacesAvailable( xMessageBuffer ) );

    /* Sending max message size again blocks the task. API succeeds after reading the current message from the buffer. */
    sentBytes = xMessageBufferSend( xMessageBuffer, message, TEST_MAX_MESSAGE_SIZE, TEST_MESSAGE_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, sentBytes );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, xStreamBufferNextMessageLengthBytes( xMessageBuffer ) );
    TEST_ASSERT_EQUAL( 1, senderTaskWoken );

    vStreamBufferDelete( xMessageBuffer );
}

/**
 * @brief Validates a task is able to receive upto maximum message size allowed, without blocking.
 */
void test_xMessageBufferReceive_success( void )
{
    uint8_t data[ TEST_MAX_MESSAGE_SIZE ] = { 0xAA };
    size_t sent = 0;
    uint8_t dataReceived[ TEST_MAX_MESSAGE_SIZE + 1 ] = { 0x00 };
    size_t received = 0;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a message buffer of the default test sample size. */
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );
    TEST_ASSERT_EQUAL( TEST_MESSAGE_BUFFER_SIZE, xMessageBufferSpacesAvailable( xMessageBuffer ) );

    sent = xMessageBufferSend( xMessageBuffer, data, TEST_MAX_MESSAGE_SIZE, TEST_MESSAGE_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, sent );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, xStreamBufferNextMessageLengthBytes( xMessageBuffer ) );

    /* Receiving bytes of size less than the message length will return 0 bytes. */
    received = xMessageBufferReceive( xMessageBuffer, dataReceived, TEST_MAX_MESSAGE_SIZE - 1, TEST_MESSAGE_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 0, received );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, xStreamBufferNextMessageLengthBytes( xMessageBuffer ) );

    /* Receiving bytes of size greater than the message length will return message length bytes. */
    received = xMessageBufferReceive( xMessageBuffer, dataReceived, TEST_MAX_MESSAGE_SIZE + 1, TEST_MESSAGE_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, received );
    TEST_ASSERT_EQUAL( 0, xStreamBufferNextMessageLengthBytes( xMessageBuffer ) );

    vStreamBufferDelete( xMessageBuffer );
}

/**
 * @brief Validates xMessageBufferReceive API with null input message.
 */
void test_xMessageBufferReceive_null_input_message( void )
{
    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a message buffer of sample size. */
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );

    /* Should assert if a null input message is passed. */
    EXPECT_ASSERT_BREAK( ( void ) xMessageBufferReceive( xMessageBuffer, NULL, TEST_MAX_MESSAGE_SIZE, TEST_MESSAGE_BUFFER_WAIT_TICKS ) );

    validate_and_clear_assertions();

    vStreamBufferDelete( xMessageBuffer );
}


/**
 * @brief Validates xMessageBufferReceive API with null message buffer handle.
 */
void test_xMessageBufferReceive_invalid_params( void )
{
    uint8_t message[ TEST_MAX_MESSAGE_SIZE ] = { 0 };

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a message buffer of sample size. */
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );

    /* Should assert if a null message buffer handle is passed. */
    EXPECT_ASSERT_BREAK( ( void ) xMessageBufferReceive( NULL, message, TEST_MAX_MESSAGE_SIZE, TEST_MESSAGE_BUFFER_WAIT_TICKS ) );

    validate_and_clear_assertions();

    vStreamBufferDelete( xMessageBuffer );
}

/**
 * @brief Validates that a task blocks if trying to read from an empty buffer.
 * Task  succeeds once a message is sent to message buffer.
 */
void test_xMessageBufferReceive_blocking( void )
{
    uint8_t message[ TEST_MAX_MESSAGE_SIZE ] = { 0 };
    size_t received = 0;

    vTaskSetTimeOutState_Ignore();
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( receiverTask );
    xTaskGenericNotifyWait_StubWithCallback( messageBufferSendCallback );
    xTaskGenericNotify_StubWithCallback( receiverTaskNotificationCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a message buffer of sample size. */
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );
    TEST_ASSERT_EQUAL( TEST_MESSAGE_BUFFER_SIZE, xMessageBufferSpacesAvailable( xMessageBuffer ) );

    /* Receive from an empty buffer causes task to block. API succeeds after a message is sent to buffer. */
    received = xMessageBufferReceive( xMessageBuffer, message, TEST_MAX_MESSAGE_SIZE, TEST_MESSAGE_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, received );
    TEST_ASSERT_EQUAL( 0, xStreamBufferNextMessageLengthBytes( xMessageBuffer ) );
    TEST_ASSERT_EQUAL( 1, receiverTaskWoken );

    vStreamBufferDelete( xMessageBuffer );
}

/**
 * @brief Validates that xMessageBufferSendFromISR API is successful and unblocks a receive task.
 */
void test_xMessageBufferSendFromISR_success( void )
{
    uint8_t message[ TEST_MAX_MESSAGE_SIZE ] = { 0 };
    size_t received = 0, sent = 0;
    BaseType_t highPriorityTaskWoken = pdFALSE;

    vTaskSetTimeOutState_Ignore();
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( receiverTask );
    xTaskGenericNotifyWait_StubWithCallback( messageBufferSendFromISRCallback );
    xTaskGenericNotifyFromISR_IgnoreAndReturn( pdTRUE );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a message buffer of sample size. */
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );
    TEST_ASSERT_EQUAL( TEST_MESSAGE_BUFFER_SIZE, xMessageBufferSpacesAvailable( xMessageBuffer ) );

    /* Receiving from empty message buffer should block. But the task be woken up from a send from ISR. */
    received = xMessageBufferReceive( xMessageBuffer, message, TEST_MAX_MESSAGE_SIZE, TEST_MESSAGE_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, received );


    /* Sending message of max size from ISR should succeed. */
    sent = xMessageBufferSendFromISR( xMessageBuffer, message, TEST_MAX_MESSAGE_SIZE, &highPriorityTaskWoken );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, received );

    /* Sending message of max size again from ISR should return zero instead of blocking. */
    sent = xMessageBufferSendFromISR( xMessageBuffer, message, TEST_MAX_MESSAGE_SIZE, &highPriorityTaskWoken );
    TEST_ASSERT_EQUAL( 0, sent );

    vStreamBufferDelete( xMessageBuffer );
}

/**
 * @brief Validates that xMessageBufferSendFromISR API is successful and unblocks a receive task.
 */
void test_xMessageBufferReceiveFromISR_success( void )
{
    uint8_t message[ TEST_MAX_MESSAGE_SIZE ] = { 0 };
    size_t sent = 0, received = 0;
    BaseType_t xHighPriorityTaskWoken = pdFALSE;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a message buffer of sample size. */
    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xMessageBuffer );
    TEST_ASSERT_EQUAL( pdTRUE, xMessageBufferIsEmpty( xMessageBuffer ) );

    /* Receiving from an empty message buffer from ISR should not block but return 0 bytes. */
    received = xMessageBufferReceiveFromISR( xMessageBuffer, message, TEST_MESSAGE_BUFFER_SIZE, &xHighPriorityTaskWoken );
    TEST_ASSERT_EQUAL( 0, received );

    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( senderTask );
    xTaskGenericNotifyWait_StubWithCallback( messageBufferReceiveFromISRCallback );
    xTaskGenericNotifyFromISR_IgnoreAndReturn( pdTRUE );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );

    /* Sending max message size so that message buffer is full. */
    sent = xMessageBufferSend( xMessageBuffer, message, TEST_MAX_MESSAGE_SIZE, TEST_MESSAGE_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, sent );
    TEST_ASSERT_EQUAL( 0, xMessageBufferSpacesAvailable( xMessageBuffer ) );

    /* Receiving using a smaller buffer size from ISR should not block and return 0 bytes. */
    received = xMessageBufferReceiveFromISR( xMessageBuffer, message, TEST_MAX_MESSAGE_SIZE - 1, &xHighPriorityTaskWoken );
    TEST_ASSERT_EQUAL( 0, received );

    /* Sending max message size again should block, but task should be woken up after receiving message from ISR. */
    sent = xMessageBufferSend( xMessageBuffer, message, TEST_MAX_MESSAGE_SIZE, TEST_MESSAGE_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_MAX_MESSAGE_SIZE, sent );

    vStreamBufferDelete( xMessageBuffer );
}

/**
 * @brief validate xMessageBufferGetStaticBuffers with a null xMessageBuffer argument
 * @details Test that xMessageBufferGetStaticBuffers asserts when a null MessageBufferHandle_t is given.
 */
void test_xMessageBufferGetStaticBuffers_null_xMessageBuffer( void )
{
    uint8_t * pucMessageBufferStorageAreaRet = NULL;
    StaticMessageBuffer_t * pxStaticMessageBuffer = NULL;

    EXPECT_ASSERT_BREAK( xMessageBufferGetStaticBuffers( NULL, &pucMessageBufferStorageAreaRet, &pxStaticMessageBuffer ) );

    validate_and_clear_assertions();

    /* Check that pucMessageBufferStorageAreaRet and pxStaticMessageBuffer have not been modified */
    TEST_ASSERT_EQUAL( NULL, pucMessageBufferStorageAreaRet );
    TEST_ASSERT_EQUAL( NULL, pxStaticMessageBuffer );
}

/**
 * @brief validate xMessageBufferGetStaticBuffers with a null ppxStaticMessageBuffer argument
 * @details Test that xMessageBufferGetStaticBuffers asserts when a null ppxStaticMessageBuffer is given.
 */
void test_xMessageBufferGetStaticBuffers_null_ppxStaticMessageBuffer( void )
{
    MessageBufferHandle_t xMessageBuffer = NULL;
    StaticMessageBuffer_t messageBufferStruct;
    uint8_t messageBufferArray[ TEST_MESSAGE_BUFFER_SIZE + 1 ] = { 0 };

    uint8_t * pucMessageBufferStorageAreaRet = NULL;

    xMessageBuffer = xMessageBufferCreateStatic( sizeof( messageBufferArray ), messageBufferArray, &messageBufferStruct );

    EXPECT_ASSERT_BREAK( xMessageBufferGetStaticBuffers( xMessageBuffer, &pucMessageBufferStorageAreaRet, NULL ) );

    validate_and_clear_assertions();

    /* Check that pucMessageBufferStorageAreaRet has not been modified */
    TEST_ASSERT_EQUAL( NULL, pucMessageBufferStorageAreaRet );

    vMessageBufferDelete( xMessageBuffer );
}

/**
 * @brief validate xMessageBufferGetStaticBuffers with a null ppucMessageBufferStorageArea argument
 * @details Test that xMessageBufferGetStaticBuffers asserts when a null ppucMessageBufferStorageArea is given.
 */
void test_xMessageBufferGetStaticBuffers_null_ppucMessageBufferStorageArea( void )
{
    MessageBufferHandle_t xMessageBuffer = NULL;
    StaticMessageBuffer_t messageBufferStruct;
    uint8_t messageBufferArray[ TEST_MESSAGE_BUFFER_SIZE + 1 ] = { 0 };

    StaticMessageBuffer_t * pxStaticMessageBuffer = NULL;

    xMessageBuffer = xMessageBufferCreateStatic( sizeof( messageBufferArray ), messageBufferArray, &messageBufferStruct );

    EXPECT_ASSERT_BREAK( xMessageBufferGetStaticBuffers( xMessageBuffer, NULL, &pxStaticMessageBuffer ) );

    validate_and_clear_assertions();

    /* Check that pxStaticMessageBuffer has not been modified */
    TEST_ASSERT_EQUAL( NULL, pxStaticMessageBuffer );

    vMessageBufferDelete( xMessageBuffer );
}

/**
 * @brief validate xMessageBufferGetStaticBuffers on a statically created message buffer
 * @details Test xMessageBufferGetStaticBuffers returns the buffers of a statically created message buffer
 */
void test_xMessageBufferGetStaticBuffers_static( void )
{
    MessageBufferHandle_t xMessageBuffer = NULL;
    StaticMessageBuffer_t messageBufferStruct;
    uint8_t messageBufferArray[ TEST_MESSAGE_BUFFER_SIZE + 1 ] = { 0 };

    uint8_t * pucMessageBufferStorageAreaRet = NULL;
    StaticMessageBuffer_t * pxStaticMessageBuffer = NULL;

    xMessageBuffer = xMessageBufferCreateStatic( sizeof( messageBufferArray ), messageBufferArray, &messageBufferStruct );

    TEST_ASSERT_EQUAL( pdTRUE, xMessageBufferGetStaticBuffers( xMessageBuffer, &pucMessageBufferStorageAreaRet, &pxStaticMessageBuffer ) );
    TEST_ASSERT_EQUAL( messageBufferArray, pucMessageBufferStorageAreaRet );
    TEST_ASSERT_EQUAL( &messageBufferStruct, pxStaticMessageBuffer );

    vMessageBufferDelete( xMessageBuffer );
}

/**
 * @brief validate xMessageBufferGetStaticBuffers on a dynamically created message buffer
 * @details Test xMessageBufferGetStaticBuffers returns an error when called on a dynamically created message buffer
 */
void test_xMessageBufferGetStaticBuffers_dynamic( void )
{
    MessageBufferHandle_t xMessageBuffer = NULL;
    uint8_t * pucMessageBufferStorageAreaRet = NULL;
    StaticMessageBuffer_t * pxStaticMessageBuffer = NULL;

    xMessageBuffer = xMessageBufferCreate( TEST_MESSAGE_BUFFER_SIZE );

    TEST_ASSERT_EQUAL( pdFALSE, xMessageBufferGetStaticBuffers( xMessageBuffer, &pucMessageBufferStorageAreaRet, &pxStaticMessageBuffer ) );
    TEST_ASSERT_EQUAL( NULL, pucMessageBufferStorageAreaRet );
    TEST_ASSERT_EQUAL( NULL, pxStaticMessageBuffer );

    vMessageBufferDelete( xMessageBuffer );
}
