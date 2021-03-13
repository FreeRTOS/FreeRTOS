/*
 * FreeRTOS V202012.00
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
/*! @file queue_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>

/* Queue includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "stream_buffer.h"

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"

/* Mock includes. */
#include "mock_task.h"
#include "mock_fake_assert.h"

/**
 * @brief Sample size in bytes of the stream buffer used for test.
 * The size is kept short enough so that the buffer can be allocated on stack.
 */
#define TEST_STREAM_BUFFER_SIZE             ( 64U )

/**
 * @brief Sample trigger level in bytes used for stream buffer tests.
 * When a receiver task is blocked waiting for data, trigger level determines how much bytes should
 * be available before which receiver task can be unblocked.
 */
#define TEST_STREAM_BUFFER_TRIGGER_LEVEL    ( 32U )

/**
 * @brief Maximum unsigned long value that can be passed as a stream buffer size so as to
 * trigger an integer overflow.
 */
#define TEST_STREAM_BUFFER_MAX_UINT_SIZE    ( ~( size_t ) ( 0UL ) )

/**
 * @brief A value used to test setting and getting stream buffer number.
 */
#define TEST_STREAM_BUFFER_NUMBER           ( 0xFFU )

/**
 * @brief Wait ticks passed into from tests if the stream buffer is full while sending data or
 * empty while receiveing data.
 */
#define TEST_STREAM_BUFFER_WAIT_TICKS       ( 1000U )

/* ============================  GLOBAL VARIABLES =========================== */

/**
 * @brief Global counter for the number of assertions in code.
 */
static int assertionFailed = 0;

/**
 * @brief Global counter to keep track of how many times a sender task was woken up by a receiver task reading from the buffer.
 */
static int senderTaskWoken = 0;

/**
 * @brief Global counter to keep track of how many times a receiver task was woken up by a sender task writing to the buffer.
 */
static int receiverTaskWoken = 0;

static TaskHandle_t senderTask = ( TaskHandle_t ) ( 0xAABBCCDD );

static TaskHandle_t receiverTask = ( TaskHandle_t ) ( 0xABCDEEFF );

static StreamBufferHandle_t xStreamBuffer;

static BaseType_t fromISR;

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
        TEST_ABORT();
    }
}

static BaseType_t streamBufferReceiveCallback( UBaseType_t uxIndexToWaitOn,
                                               uint32_t ulBitsToClearOnEntry,
                                               uint32_t ulBitsToClearOnExit,
                                               uint32_t * pulNotificationValue,
                                               TickType_t xTicksToWait,
                                               int cmock_num_calls )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0 };
    size_t dataReceived = 0;

    /* Receive enough bytes (full size) from stream buffer to wake up sender task. */
    dataReceived = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, 0 );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, dataReceived );
    return pdTRUE;
}

static BaseType_t streamBufferReceiveFromISRCallback( UBaseType_t uxIndexToWaitOn,
                                                      uint32_t ulBitsToClearOnEntry,
                                                      uint32_t ulBitsToClearOnExit,
                                                      uint32_t * pulNotificationValue,
                                                      TickType_t xTicksToWait,
                                                      int cmock_num_calls )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0 };
    size_t dataReceived = 0;
    BaseType_t senderTaskWokenFromISR = pdFALSE;

    /* Receive enough bytes (full size) from stream buffer to wake up sender task. */
    dataReceived = xStreamBufferReceiveFromISR( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, &senderTaskWokenFromISR );
    TEST_ASSERT_EQUAL( pdTRUE, senderTaskWokenFromISR );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, dataReceived );
    return pdTRUE;
}

static BaseType_t resetWhenBlockedCallback( UBaseType_t uxIndexToWaitOn,
                                            uint32_t ulBitsToClearOnEntry,
                                            uint32_t ulBitsToClearOnExit,
                                            uint32_t * pulNotificationValue,
                                            TickType_t xTicksToWait,
                                            int cmock_num_calls )
{
    BaseType_t status;

    status = xStreamBufferReset( xStreamBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, status );
    return pdTRUE;
}

static BaseType_t sendCompletedFromISRCallback( UBaseType_t uxIndexToWaitOn,
                                                uint32_t ulBitsToClearOnEntry,
                                                uint32_t ulBitsToClearOnExit,
                                                uint32_t * pulNotificationValue,
                                                TickType_t xTicksToWait,
                                                int cmock_num_calls )
{
    BaseType_t status = pdFALSE, highPriorityTaskWoken = pdFALSE;

    status = xStreamBufferSendCompletedFromISR( xStreamBuffer, &highPriorityTaskWoken );
    TEST_ASSERT_EQUAL( pdTRUE, status );
    TEST_ASSERT_EQUAL( pdTRUE, highPriorityTaskWoken );
    return pdTRUE;
}

static BaseType_t receiveCompletedFromISRCallback( UBaseType_t uxIndexToWaitOn,
                                                   uint32_t ulBitsToClearOnEntry,
                                                   uint32_t ulBitsToClearOnExit,
                                                   uint32_t * pulNotificationValue,
                                                   TickType_t xTicksToWait,
                                                   int cmock_num_calls )
{
    BaseType_t status = pdFALSE, highPriorityTaskWoken = pdFALSE;

    status = xStreamBufferReceiveCompletedFromISR( xStreamBuffer, &highPriorityTaskWoken );
    TEST_ASSERT_EQUAL( pdTRUE, status );
    TEST_ASSERT_EQUAL( pdTRUE, highPriorityTaskWoken );
    return pdTRUE;
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

static BaseType_t senderTaskNotificationFromISRCallback( TaskHandle_t xTaskToNotify,
                                                         UBaseType_t uxIndexToNotify,
                                                         uint32_t ulValue,
                                                         eNotifyAction eAction,
                                                         uint32_t * pulPreviousNotificationValue,
                                                         BaseType_t * pxHigherPriorityTaskWoken,
                                                         int cmock_num_calls )
{
    TEST_ASSERT_EQUAL( senderTask, xTaskToNotify );
    senderTaskWoken++;
    *pxHigherPriorityTaskWoken = pdTRUE;

    return pdTRUE;
}

static BaseType_t streamBufferSendCallback( UBaseType_t uxIndexToWaitOn,
                                            uint32_t ulBitsToClearOnEntry,
                                            uint32_t ulBitsToClearOnExit,
                                            uint32_t * pulNotificationValue,
                                            TickType_t xTicksToWait,
                                            int cmock_num_calls )
{
    uint8_t data[ TEST_STREAM_BUFFER_TRIGGER_LEVEL ] = { 0 };
    size_t dataSent = 0;

    /* Send enough (trigger level) bytes to stream buffer to wake up receiver Task. */
    dataSent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL, 0 );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, dataSent );
    return pdTRUE;
}

static BaseType_t streamBufferSendFromISRCallback( UBaseType_t uxIndexToWaitOn,
                                                   uint32_t ulBitsToClearOnEntry,
                                                   uint32_t ulBitsToClearOnExit,
                                                   uint32_t * pulNotificationValue,
                                                   TickType_t xTicksToWait,
                                                   int cmock_num_calls )
{
    uint8_t data[ TEST_STREAM_BUFFER_TRIGGER_LEVEL ] = { 0 };
    size_t dataSent = 0;
    BaseType_t receiverTaskWokenFromISR = pdFALSE;

    /* Send enough (trigger level) bytes to stream buffer to wake up receiver Task. */
    dataSent = xStreamBufferSendFromISR( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL, &receiverTaskWokenFromISR );
    TEST_ASSERT_EQUAL( pdTRUE, receiverTaskWokenFromISR );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, dataSent );
    return pdTRUE;
}

static BaseType_t sendLessThanTriggerLevelBytesFromISRCallback( UBaseType_t uxIndexToWaitOn,
                                                                uint32_t ulBitsToClearOnEntry,
                                                                uint32_t ulBitsToClearOnExit,
                                                                uint32_t * pulNotificationValue,
                                                                TickType_t xTicksToWait,
                                                                int cmock_num_calls )
{
    uint8_t data[ TEST_STREAM_BUFFER_TRIGGER_LEVEL ] = { 0 };
    size_t dataSent = 0;
    BaseType_t receiverTaskWokenFromISR = pdFALSE;

    /* Send enough (trigger level) bytes to stream buffer to wake up receiver Task. */
    dataSent = xStreamBufferSendFromISR( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL - 1, &receiverTaskWokenFromISR );
    TEST_ASSERT_EQUAL( pdFALSE, receiverTaskWokenFromISR );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL - 1, dataSent );
    return pdTRUE;
}

static BaseType_t receiverTaskNotificationFromISRCallback( TaskHandle_t xTaskToNotify,
                                                           UBaseType_t uxIndexToNotify,
                                                           uint32_t ulValue,
                                                           eNotifyAction eAction,
                                                           uint32_t * pulPreviousNotificationValue,
                                                           BaseType_t * pxHigherPriorityTaskWoken,
                                                           int cmock_num_calls )
{
    TEST_ASSERT_EQUAL( receiverTask, xTaskToNotify );
    receiverTaskWoken++;
    *pxHigherPriorityTaskWoken = pdTRUE;

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
void setUp( void )
{
    assertionFailed = 0;
    xStreamBuffer = NULL;
    senderTaskWoken = 0;
    receiverTaskWoken = 0;
    fromISR = pdFALSE;

    vFakeAssert_StubWithCallback( vFakeAssertStub );
    /* Track calls to malloc / free */
    UnityMalloc_StartTest();
}

/*! called before each testcase */
void tearDown( void )
{
    TEST_ASSERT_EQUAL_MESSAGE( 0, assertionFailed, "Assertion check failed in code." );
    UnityMalloc_EndTest();
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

static void validate_stream_buffer_init_state( StreamBufferHandle_t xStreamBuffer,
                                               size_t bufferSize )
{
    TEST_ASSERT_TRUE( xStreamBufferIsEmpty( xStreamBuffer ) );
    TEST_ASSERT_FALSE( xStreamBufferIsFull( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( bufferSize, xStreamBufferSpacesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 0U, xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 0U, xStreamBufferNextMessageLengthBytes( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 0, ucStreamBufferGetStreamBufferType( xStreamBuffer ) );
}

static void validate_and_clear_assertitions( void )
{
    TEST_ASSERT_EQUAL( 1, assertionFailed );
    assertionFailed = 0;
}

/* ==============================  Test Cases  ============================== */

/**
 * @brief Validates that stream buffer of sample size is created succesfully.
 */
void test_xStreamBufferCreate_success( void )
{
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_EQUAL( NULL, xStreamBuffer );
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    /* Set a stream buffer number and get it. */
    vStreamBufferSetStreamBufferNumber( xStreamBuffer, TEST_STREAM_BUFFER_NUMBER );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_NUMBER, uxStreamBufferGetStreamBufferNumber( xStreamBuffer ) );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates stream buffer create fails on passing invalid parameters.
 */
void test_xStreamBufferCreate_invalid_params( void )
{
    /* Returns NULL if there is an integer overflow in the buffer size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_MAX_UINT_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_EQUAL( NULL, xStreamBuffer );

    /* Returns NULL if internal memory allocation of the stream buffer fails. */
    UnityMalloc_MakeMallocFailAfterCount( 0 );

    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_EQUAL( NULL, xStreamBuffer );

    /* Assertion fails if a zero buffer size is passed as  the parameter. */
    if( TEST_PROTECT() )
    {
        ( void ) xStreamBufferCreate( 0, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    }

    validate_and_clear_assertitions();

    /* Assertion fails if trigger level is greater than the stream buffer size. */
    if( TEST_PROTECT() )
    {
        ( void ) xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, ( TEST_STREAM_BUFFER_SIZE + 1 ) );
    }

    validate_and_clear_assertitions();
}

/**
 * @brief Validates stream buffer create using a static buffer is successful.
 */
void test_xStreamBufferCreateStatic_success( void )
{
    StaticStreamBuffer_t streamBufferStruct = { 0 };

    /* The size of stream buffer array should be one greater than the required size of stream buffer. */
    uint8_t streamBufferArray[ TEST_STREAM_BUFFER_SIZE + 1 ] = { 0 };

    xStreamBuffer = xStreamBufferCreateStatic( sizeof( streamBufferArray ), TEST_STREAM_BUFFER_TRIGGER_LEVEL, streamBufferArray, &streamBufferStruct );

    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates stream buffer static create fails on passing invalid parameters.
 */
void test_xStreamBufferCreateStatic_invalid_params( void )
{
    StaticStreamBuffer_t streamBufferStruct = { 0 };
    /* The size of stream buffer array should be one greater than the required size of stream buffer. */
    uint8_t streamBufferArray[ TEST_STREAM_BUFFER_SIZE + 1 ] = { 0 };

    /* Returns NULL if a NULL pointer is passed as the stream buffer storage area. */
    xStreamBuffer = xStreamBufferCreateStatic( sizeof( streamBufferArray ), TEST_STREAM_BUFFER_TRIGGER_LEVEL, NULL, &streamBufferStruct );
    TEST_ASSERT_NULL( xStreamBuffer );

    /* Returns NULL if a NULL struct is passed as a parameter. */
    xStreamBuffer = xStreamBufferCreateStatic( sizeof( streamBufferArray ), TEST_STREAM_BUFFER_TRIGGER_LEVEL, streamBufferArray, NULL );
    TEST_ASSERT_NULL( xStreamBuffer );

    /* Assertion fails if the trigger level is invalid. */
    if( TEST_PROTECT() )
    {
        ( void ) xStreamBufferCreateStatic( sizeof( streamBufferArray ), TEST_STREAM_BUFFER_SIZE + 2, streamBufferArray, &streamBufferStruct );
    }

    validate_and_clear_assertitions();
}

/**
 * @brief Validates a task is able to send upto buffer space available without blocking.
 */
void test_xStreamBufferSend_success( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0 };
    size_t sent = 0;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of the default test sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Sending bytes of size upto to available size should succeed without blocking. */
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sent );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( pdFALSE, xStreamBufferIsEmpty( xStreamBuffer ) );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates that sending data more than stream buffer size will cap the data to the total size without blocking.
 */
void test_xStreamBufferSend_more_than_buffer_size( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE + 1 ] = { 0 };
    size_t sent = 0;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of the default test sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Sending bytes beyond the total size caps the length to total size. */
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE + 1, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sent );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferBytesAvailable( xStreamBuffer ) );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates cases where stream buffer has insufficient space to send the data and sender has to block.
 */
void test_xStreamBufferSend_blocking( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0 };
    size_t sent = 0;

    vTaskSetTimeOutState_Ignore();
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( senderTask );
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of test sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Fill the stream buffer without blocking. */
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE - 1, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE - 1, sent );
    TEST_ASSERT_EQUAL( 1, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /*
     * Sending bytes more than available size should make the task block. Task
     * should timeout after TEST_STREAM_BUFFER_WAIT_TICKS and then return partial data sent.
     */
    xTaskGenericNotifyWait_ExpectAndReturn( 0, 0, 0, NULL, TEST_STREAM_BUFFER_WAIT_TICKS, pdTRUE );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 1, sent );
    TEST_ASSERT_EQUAL( pdTRUE, xStreamBufferIsFull( xStreamBuffer ) );

    /*
     * A sender task blocked on stream buffer shoud be woken up by receiving from the stream buffer.
     */
    xTaskGenericNotifyWait_StubWithCallback( streamBufferReceiveCallback );
    xTaskGenericNotify_StubWithCallback( senderTaskNotificationCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sent );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 1, senderTaskWoken );

    /*
     * A sender task blocked on stream buffer shoud be woken up by receiving from the stream buffer through an ISR.
     */
    xTaskGenericNotifyWait_StubWithCallback( streamBufferReceiveFromISRCallback );
    xTaskGenericNotifyFromISR_StubWithCallback( senderTaskNotificationFromISRCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sent );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 2, senderTaskWoken );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates that stream buffer does not block if zero wait time is passed.
 */
void test_xStreamBufferSend_zero_wait_ticks( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0 };
    size_t dataSent = 0;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Sending data of sample space should not block the task */
    dataSent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, dataSent );
    TEST_ASSERT_EQUAL( 0, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /*  Sending data to a full stream buffer with zero wait ticks should not block and return zero bytes sent. */
    dataSent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, 0 );
    TEST_ASSERT_EQUAL( 0, dataSent );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates that a task is able to receive available data from stream buffer without blocking.
 */
void test_xStreamBufferReceive_success( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0xAA };
    uint8_t dataReceived[ TEST_STREAM_BUFFER_SIZE ] = { 0x00 };
    size_t sentBytes = 0, receivedBytes = 0;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Send TEST_STREAM_BUFFER_SIZE data to the stream buffer. */
    sentBytes = xStreamBufferSend( xStreamBuffer, &data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sentBytes );

    /* Receive the half the data from stream Buffer without blocking. */
    receivedBytes = xStreamBufferReceive( xStreamBuffer, &dataReceived, ( TEST_STREAM_BUFFER_SIZE / 2 ), TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( ( TEST_STREAM_BUFFER_SIZE / 2 ), receivedBytes );
    TEST_ASSERT_EQUAL_HEX8_ARRAY( data, dataReceived, receivedBytes );
    TEST_ASSERT_EQUAL( ( TEST_STREAM_BUFFER_SIZE / 2 ), xStreamBufferBytesAvailable( xStreamBuffer ) );

    /* Request for full TEST_STREAM_BUFFER_SIZE bytes, but only receive whats available without blocking.  */
    receivedBytes = xStreamBufferReceive( xStreamBuffer, &dataReceived, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( ( TEST_STREAM_BUFFER_SIZE / 2 ), receivedBytes );
    TEST_ASSERT_EQUAL( 0, xStreamBufferBytesAvailable( xStreamBuffer ) );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates that receiving from an empty stream buffer will block untill atleast trigger level bytes are
 * added into the buffer.
 */
void test_xStreamBufferReceive_blocking( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0xAA };
    size_t receivedBytes = 0;

    vTaskSetTimeOutState_Ignore();
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( receiverTask );
    xTaskGenericNotify_StubWithCallback( receiverTaskNotificationCallback );

    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /*
     * Task blocks receiving from an empty stream buffer. From the callback trigger level bytes are
     * sent to the stream buffer which wakes up the receiver task.
     */
    xTaskGenericNotifyWait_StubWithCallback( streamBufferSendCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    receivedBytes = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( receivedBytes, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_EQUAL( 0, xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 1, receiverTaskWoken );

    /*
     * Task blocks receiving from an empty stream buffer. From the ISR trigger level bytes are
     * sent to the stream buffer which wakes up the receiver task.
     */
    xTaskGenericNotifyWait_StubWithCallback( streamBufferSendFromISRCallback );
    xTaskGenericNotifyFromISR_StubWithCallback( receiverTaskNotificationFromISRCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    receivedBytes = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, receivedBytes );
    TEST_ASSERT_EQUAL( 2, receiverTaskWoken );

    /* Sending less than trigger level bytes should not wake up the task. */
    xTaskGenericNotifyWait_StubWithCallback( sendLessThanTriggerLevelBytesFromISRCallback );
    xTaskGenericNotifyFromISR_StubWithCallback( receiverTaskNotificationFromISRCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );
    receivedBytes = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 2, receiverTaskWoken );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates that task does not block for receive if zero wait ticks are passed.
 */
void test_xStreamBufferReceive_zero_wait_ticks( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0xAA };
    size_t receivedBytes = 0;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Task does not block on an empty stream buffer if zero wait ticks are passed. */
    receivedBytes = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, 0 );
    TEST_ASSERT_EQUAL( 0, receivedBytes );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates that an interrupt service routine is able to read data from stream
 * buffer without blocking.
 */
void test_xStreamBufferReceiveFromISR_success( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0xAA };
    uint8_t dataReceived[ TEST_STREAM_BUFFER_SIZE ] = { 0x00 };
    size_t receivedBytes = 0, sentBytes = 0;
    BaseType_t xHighPriorityTaskWoken = pdFALSE;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Send full size data to the stream buffer. */
    sentBytes = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sentBytes );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferBytesAvailable( xStreamBuffer ) );

    /* Receive half the data from stream buffer without blocking. */
    receivedBytes = xStreamBufferReceiveFromISR( xStreamBuffer, &dataReceived, ( TEST_STREAM_BUFFER_SIZE / 2 ), &xHighPriorityTaskWoken );
    TEST_ASSERT_EQUAL( ( TEST_STREAM_BUFFER_SIZE / 2 ), receivedBytes );
    TEST_ASSERT_EQUAL_HEX8_ARRAY( data, dataReceived, receivedBytes );
    TEST_ASSERT_EQUAL( pdFALSE, xHighPriorityTaskWoken );

    /*
     * Read full stream buffer size but receive only half the data without blocking.
     */
    receivedBytes = xStreamBufferReceiveFromISR( xStreamBuffer, &dataReceived, TEST_STREAM_BUFFER_SIZE, &xHighPriorityTaskWoken );
    TEST_ASSERT_EQUAL( ( TEST_STREAM_BUFFER_SIZE / 2 ), receivedBytes );
    TEST_ASSERT_EQUAL( 0, xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( pdFALSE, xHighPriorityTaskWoken );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates that an interrupt service routine is able to send data upto the size of stream buffer without blocking.
 */
void test_xStreamBufferSendFromISR_success( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0xAA };
    size_t sentBytes = 0;
    BaseType_t xHighPriorityTaskWoken = pdFALSE;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Send data to an empty buffer should succeed without blocking. */
    sentBytes = xStreamBufferSendFromISR( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE - 1U, &xHighPriorityTaskWoken );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE - 1U, sentBytes );
    TEST_ASSERT_EQUAL( 1U, xStreamBufferSpacesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( pdFALSE, xHighPriorityTaskWoken );

    /* Send full bytes from ISR again should send partial bytes without blocking. */
    sentBytes = xStreamBufferSendFromISR( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, &xHighPriorityTaskWoken );
    TEST_ASSERT_EQUAL( 1U, sentBytes );
    TEST_ASSERT_EQUAL( 0, xStreamBufferSpacesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( pdFALSE, xHighPriorityTaskWoken );

    /* Sending to full buffer should return 0 bytes sent without blocking. */
    sentBytes = xStreamBufferSendFromISR( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, &xHighPriorityTaskWoken );
    TEST_ASSERT_EQUAL( 0U, sentBytes );
    TEST_ASSERT_EQUAL( pdFALSE, xHighPriorityTaskWoken );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates user is able to reset the stream buffer back to empty state.
 */
void test_xStreamBufferReset_success( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0 };
    size_t dataSent = 0;
    BaseType_t status = pdFALSE;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of the default test sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );

    /* Validate stream buffer is empty initially. */
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    /* Send maximum size of data to stream buffer. */
    dataSent = xStreamBufferSend( xStreamBuffer, data, sizeof( data ), TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, dataSent );

    /* Verify that all bytes are available. */
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferBytesAvailable( xStreamBuffer ) );

    /* Reset the stream buffer back to empty state. */
    status = xStreamBufferReset( xStreamBuffer );
    TEST_ASSERT_EQUAL( pdTRUE, status );

    /* Validate that stream buffer is empty. */
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates that stream buffer reset fails if a sender or receiver task is blocked on it.
 */
void test_xStreamBufferReset_while_blocked( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0xAA };
    size_t sentBytes = 0, receivedBytes = 0;

    vTaskSetTimeOutState_Ignore();
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( senderTask );
    xTaskGenericNotifyWait_StubWithCallback( resetWhenBlockedCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /*
     * Perform a blocking operation to receive from an empty stream buffer. Reset stream buffer within receiver task notify
     * wait callback should fail.
     */
    receivedBytes = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 0, receivedBytes );

    /*
     * Send full size data to stream buffer.
     */
    sentBytes = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sentBytes );
    TEST_ASSERT_EQUAL( pdTRUE, xStreamBufferIsFull( xStreamBuffer ) );

    /*
     * Sending data to full stream buffer causes task to be blocked. Reset stream buffer within sender task notify
     * wait callback should fail.
     */
    sentBytes = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 0, sentBytes );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates that a receiver task is able to receive data after lowering the stream buffer trigger level.
 */
void test_xStreamBufferSetTrigerLevel_success( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0xAA };
    BaseType_t status;

    vTaskSetTimeOutState_Ignore();
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( receiverTask );
    xTaskGenericNotify_StubWithCallback( receiverTaskNotificationCallback );
    xTaskGenericNotifyWait_StubWithCallback( streamBufferSendCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create stream buffer with trigger level equal to maximum stream buffer size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );

    /* Set the trigger level to TEST_STREAM_BUFFER_TRIGGER_LEVEL. */
    status = xStreamBufferSetTriggerLevel( xStreamBuffer, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_EQUAL( pdTRUE, status );

    /*
     * Receive data from empty stream buffer, with trigger level bytes send from the callback. This should unblock
     * the task.
     */
    ( void ) xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 1, receiverTaskWoken );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validate setting trigger level with invalid parameters fails.
 */
void test_xStreamBufferSetTrigerLevel_invalid_params( void )
{
    BaseType_t status;

    /* Create stream buffer. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );

    /* Set the trigger level to ( TEST_STREAM_BUFFER_SIZE + 1) should fail. */
    status = xStreamBufferSetTriggerLevel( xStreamBuffer, ( TEST_STREAM_BUFFER_SIZE + 1 ) );
    TEST_ASSERT_EQUAL( pdFALSE, status );

    /* Set the trigger level to 0 should pass but internally set trigger level to 1. */
    status = xStreamBufferSetTriggerLevel( xStreamBuffer, 0 );
    TEST_ASSERT_EQUAL( pdTRUE, status );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates xStreamBufferSendCompletedFromISR function unblocks a receive task.
 */
void test_xStreamBufferSendCompletedFromISR_success( void )
{
    BaseType_t status = pdFALSE;
    BaseType_t highPriorityTaskWoken = pdFALSE;
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ];
    size_t receiveBytes = 0;

    /* Create a stream buffer of the default test sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );

    /* Send completed without receiver task blocked on it. */
    status = xStreamBufferSendCompletedFromISR( xStreamBuffer, &highPriorityTaskWoken );
    TEST_ASSERT_EQUAL( pdFALSE, status );
    TEST_ASSERT_EQUAL( pdFALSE, highPriorityTaskWoken );

    /* Send completed with a receiver task blocked on it. */

    vTaskSetTimeOutState_Ignore();
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( receiverTask );
    xTaskGenericNotifyWait_StubWithCallback( sendCompletedFromISRCallback );
    xTaskGenericNotifyFromISR_StubWithCallback( receiverTaskNotificationFromISRCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    receiveBytes = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 0, receiveBytes );
    TEST_ASSERT_EQUAL( 1, receiverTaskWoken );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates xStreamBufferReceiveCompletedFromISR unblocks a sender task.
 */
void test_xStreamBufferReceiveCompletedFromISR_success( void )
{
    BaseType_t status = pdFALSE;
    BaseType_t highPriorityTaskWoken = pdFALSE;

    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0xAA };
    size_t sentBytes = 0;

    /* Create a stream buffer of the default test sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );

    /* Receive completed without a sender task blocked on it. */
    status = xStreamBufferReceiveCompletedFromISR( xStreamBuffer, &highPriorityTaskWoken );
    TEST_ASSERT_EQUAL( pdFALSE, status );
    TEST_ASSERT_EQUAL( pdFALSE, highPriorityTaskWoken );

    vTaskSetTimeOutState_Ignore();
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( senderTask );
    xTaskGenericNotifyWait_StubWithCallback( receiveCompletedFromISRCallback );
    xTaskGenericNotifyFromISR_StubWithCallback( senderTaskNotificationFromISRCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Send full data to an empty stream buffer. */
    sentBytes = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sentBytes );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferBytesAvailable( xStreamBuffer ) );

    sentBytes = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 0, sentBytes );
    TEST_ASSERT_EQUAL( 1, senderTaskWoken );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates a task is able to send upto buffer space available without blocking.
 */
void test_xStreamBufferSend_WrapOver( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0xAA };
    size_t sent = 0, received = 0;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of the default test sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Sending bytes upto max stream buffer size*/
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sent );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 0, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Read upto max buffer size - 1 */
    received = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE - 1, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE - 1, received );
    TEST_ASSERT_EQUAL( 1, xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE - 1, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Send upto max buffer size - 1 so that head wraps over. */
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE - 1, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE - 1, sent );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 0U, xStreamBufferSpacesAvailable( xStreamBuffer ) );


    /* Read all bytes and verify that tail wraps over as well. */
    received = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, received );
    TEST_ASSERT_EQUAL( 0, xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    vStreamBufferDelete( xStreamBuffer );
}
