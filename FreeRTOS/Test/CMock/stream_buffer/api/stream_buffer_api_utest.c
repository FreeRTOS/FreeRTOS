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
/*! @file stream_buffer_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>

/* Stream Buffer includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "stream_buffer.h"

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "CException.h"

/* Mock includes. */
#include "mock_task.h"
#include "mock_fake_assert.h"
#include "mock_fake_port.h"

/**
 * @brief Sample size in bytes of the stream buffer used for test.
 * The size is kept short enough so that the buffer can be allocated on stack.
 */
#define TEST_STREAM_BUFFER_SIZE                  ( 64U )

/**
 * @brief Sample trigger level in bytes used for stream buffer tests.
 * When a receiver task is blocked waiting for data, trigger level determines how much bytes should
 * be available before which receiver task can be unblocked.
 */
#define TEST_STREAM_BUFFER_TRIGGER_LEVEL         ( 32U )

/**
 * @brief Maximum unsigned long value that can be passed as a stream buffer size so as to
 * trigger an integer overflow.
 */
#define TEST_STREAM_BUFFER_MAX_UINT_SIZE         ( ~( size_t ) ( 0UL ) )

/**
 * @brief A value used to test setting and getting stream buffer number.
 */
#define TEST_STREAM_BUFFER_NUMBER                ( 0xFFU )

/**
 * @brief A value used to test setting and getting stream buffer notification index.
 */
#define TEST_STREAM_BUFFER_NOTIFICATION_INDEX    ( 0x2 )

/**
 * @brief Wait ticks passed into from tests if the stream buffer is full while sending data or
 * empty while receiving data.
 */
#define TEST_STREAM_BUFFER_WAIT_TICKS            ( 1000U )

/**
 * @brief CException code for when a configASSERT should be intercepted.
 */
#define configASSERT_E                           0xAA101

/**
 * @brief Expect a configASSERT from the function called.
 *  Break out of the called function when this occurs.
 * @details Use this macro when the call passed in as a parameter is expected
 * to cause invalid memory access.
 */
#define EXPECT_ASSERT_BREAK( call )                  \
    do                                               \
    {                                                \
        shouldAbortOnAssertion = true;               \
        CEXCEPTION_T e = CEXCEPTION_NONE;            \
        Try                                          \
        {                                            \
            call;                                    \
            TEST_FAIL_MESSAGE( "Expected Assert!" ); \
        }                                            \
        Catch( e )                                   \
        {                                            \
            TEST_ASSERT_EQUAL( configASSERT_E, e );  \
        }                                            \
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
 * @brief Global variable to keep track of the last notification index we are waiting on
 */
static UBaseType_t notificationIndex = -1;

/**
 * @brief Dummy sender task handle to which the stream buffer receive APIs will send notification.
 */
static TaskHandle_t senderTask = ( TaskHandle_t ) ( 0xAABBCCDD );

/**
 * @brief Dummy receiver task handle to which the stream buffer send APIs will send notifications.
 */
static TaskHandle_t receiverTask = ( TaskHandle_t ) ( 0xABCDEEFF );

/**
 * @brief Global Stream buffer handle used for tests.
 */
static StreamBufferHandle_t xStreamBuffer;

/**
 * @brief Flag which denotes if test need to abort on assertion.
 */
static BaseType_t shouldAbortOnAssertion;

/**
 * @brief Variable used to record the total dynamic size allocated in a test.
 */
static size_t dynamicMemoryAllocated = 0;

/* ==========================  CALLBACK FUNCTIONS =========================== */

void * pvPortMalloc( size_t xSize )
{
    dynamicMemoryAllocated += xSize;
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

static BaseType_t streamBufferReceiveCallback( UBaseType_t uxIndexToWaitOn,
                                               uint32_t ulBitsToClearOnEntry,
                                               uint32_t ulBitsToClearOnExit,
                                               uint32_t * pulNotificationValue,
                                               TickType_t xTicksToWait,
                                               int cmock_num_calls )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0 };
    size_t dataReceived = 0;

    notificationIndex = uxIndexToWaitOn;
    /* Receive enough bytes (full size) from stream buffer to wake up sender task. */
    dataReceived = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
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

    notificationIndex = uxIndexToWaitOn;
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

    notificationIndex = uxIndexToWaitOn;
    /* Reset when the task is blocked on stream buffer, should fail and return pdFAIL. */
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

    notificationIndex = uxIndexToWaitOn;
    /* Executing the send completed API from ISR should unblock a high priority task waiting to receive from stream buffer. */
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

    notificationIndex = uxIndexToWaitOn;
    /* Executing the receive completed API from ISR should unblock a high priority task waiting to send to stream buffer. */
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

    if( uxIndexToNotify == notificationIndex )
    {
        senderTaskWoken++;
    }

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

    if( uxIndexToNotify == notificationIndex )
    {
        senderTaskWoken++;
    }

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

    notificationIndex = uxIndexToWaitOn;
    /* Send enough (trigger level) bytes to stream buffer to wake up the receiver Task. */
    dataSent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL, TEST_STREAM_BUFFER_WAIT_TICKS );
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

    notificationIndex = uxIndexToWaitOn;
    /* Send enough (trigger level) bytes to stream buffer to wake up the receiver Task. */
    dataSent = xStreamBufferSendFromISR( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL, &receiverTaskWokenFromISR );
    TEST_ASSERT_EQUAL( pdTRUE, receiverTaskWokenFromISR );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, dataSent );
    return pdTRUE;
}

static BaseType_t sendLessThanTriggerLevelBytesCallback( UBaseType_t uxIndexToWaitOn,
                                                         uint32_t ulBitsToClearOnEntry,
                                                         uint32_t ulBitsToClearOnExit,
                                                         uint32_t * pulNotificationValue,
                                                         TickType_t xTicksToWait,
                                                         int cmock_num_calls )
{
    uint8_t data[ TEST_STREAM_BUFFER_TRIGGER_LEVEL ] = { 0 };
    size_t dataSent = 0;

    notificationIndex = uxIndexToWaitOn;
    /* Sending less than trigger level bytes should not wake up the receiver Task. */
    dataSent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL - 1, 0 );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL - 1, dataSent );
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

    notificationIndex = uxIndexToWaitOn;
    /* Sending less than trigger level bytes should not wake up the receiver Task. */
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

    if( uxIndexToNotify == notificationIndex )
    {
        receiverTaskWoken++;
    }

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

    if( uxIndexToNotify == notificationIndex )
    {
        receiverTaskWoken++;
    }

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
    notificationIndex = -1;
    shouldAbortOnAssertion = pdTRUE;
    dynamicMemoryAllocated = 0;


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

/*! called before each test case */
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

static void validate_stream_buffer_init_state( StreamBufferHandle_t xStreamBuffer,
                                               size_t bufferSize )
{
    TEST_ASSERT_TRUE( xStreamBufferIsEmpty( xStreamBuffer ) );
    TEST_ASSERT_FALSE( xStreamBufferIsFull( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( bufferSize, xStreamBufferSpacesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 0U, xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 0U, xStreamBufferNextMessageLengthBytes( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 0, ucStreamBufferGetStreamBufferType( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( tskDEFAULT_INDEX_TO_NOTIFY, uxStreamBufferGetStreamBufferNotificationIndex( xStreamBuffer ) );
}

static void validate_and_clear_assertions( void )
{
    TEST_ASSERT_EQUAL( 1, assertionFailed );
    assertionFailed = 0;
}

/* ==============================  Test Cases  ============================== */

/**
 * @brief Validates that stream buffer of sample size is created successfully.
 */
void test_xStreamBufferCreate_success( void )
{
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_EQUAL( NULL, xStreamBuffer );
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    /* Verify internal memory allocated is equal to size of the struct + buffer size + 1. */
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE + 1U + sizeof( StaticStreamBuffer_t ), dynamicMemoryAllocated );

    /* Set a stream buffer number and get it. */
    vStreamBufferSetStreamBufferNumber( xStreamBuffer, TEST_STREAM_BUFFER_NUMBER );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_NUMBER, uxStreamBufferGetStreamBufferNumber( xStreamBuffer ) );

    /* Set a notification index and get it. */
    vStreamBufferSetStreamBufferNotificationIndex( xStreamBuffer, TEST_STREAM_BUFFER_NOTIFICATION_INDEX );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_NOTIFICATION_INDEX, uxStreamBufferGetStreamBufferNotificationIndex( xStreamBuffer ) );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * Returns NULL if there is an integer overflow in the buffer size.
 */
void test_xStreamBufferCreate_integer_overflow( void )
{
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_MAX_UINT_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_EQUAL( NULL, xStreamBuffer );
}

/**
 * @brief Returns NULL if internal memory allocation of the stream buffer fails.
 */
void test_xStreamBufferCreate_malloc_fail( void )
{
    UnityMalloc_MakeMallocFailAfterCount( 0 );

    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_EQUAL( NULL, xStreamBuffer );
}

/**
 * @brief Assertion fails if a zero buffer size is passed as  the parameter.
 */
void test_xStreamBufferCreate_zero_buffer_size( void )
{
    EXPECT_ASSERT_BREAK( ( void ) xStreamBufferCreate( 0, TEST_STREAM_BUFFER_TRIGGER_LEVEL ) );
    validate_and_clear_assertions();
}

/**
 * @brief Assertion fails if trigger level is greater than the stream buffer size.
 */
void test_xStreamBufferCreate_invalid_trigger_level( void )
{
    EXPECT_ASSERT_BREAK( ( void ) xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, ( TEST_STREAM_BUFFER_SIZE + 1 ) ) );
    validate_and_clear_assertions();
}

/**
 * @brief Assertion fails while trying to delete a null stream buffer.
 */
void test_xStreamBufferDelete_null_stream_buffer( void )
{
    EXPECT_ASSERT_BREAK( vStreamBufferDelete( NULL ) );
    validate_and_clear_assertions();
}

/**
 * @brief Validates stream buffer create using a static buffer is successful.
 */
void test_xStreamBufferCreateStatic_success( void )
{
    StaticStreamBuffer_t streamBufferStruct;

    /* The size of stream buffer array should be one greater than the required size of stream buffer. */
    uint8_t streamBufferArray[ TEST_STREAM_BUFFER_SIZE + 1 ] = { 0 };

    xStreamBuffer = xStreamBufferCreateStatic( sizeof( streamBufferArray ), TEST_STREAM_BUFFER_TRIGGER_LEVEL, streamBufferArray, &streamBufferStruct );

    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates stream buffer static create fails if NULL array is passed.
 */
void test_xStreamBufferCreateStatic_null_array( void )
{
    StaticStreamBuffer_t streamBufferStruct;

    /* The size of stream buffer array should be one greater than the required size of stream buffer. */
    uint8_t streamBufferArray[ TEST_STREAM_BUFFER_SIZE + 1 ] = { 0 };

    /* Tests should abort if assertion is enabled or return NULL. */
    shouldAbortOnAssertion = pdFALSE;

    /* Returns NULL if a NULL pointer is passed as the stream buffer storage area. */
    xStreamBuffer = xStreamBufferCreateStatic( sizeof( streamBufferArray ), TEST_STREAM_BUFFER_TRIGGER_LEVEL, NULL, &streamBufferStruct );
    TEST_ASSERT_NULL( xStreamBuffer );
    validate_and_clear_assertions();
}

/**
 * @brief Validates stream buffer static create fails if NULL struct is passed.
 */
void test_xStreamBufferCreateStatic_invalid_null_struct( void )
{
    /* The size of stream buffer array should be one greater than the required size of stream buffer. */
    uint8_t streamBufferArray[ TEST_STREAM_BUFFER_SIZE + 1 ] = { 0 };

    /* Tests should abort if assertion is enabled or return NULL. */
    shouldAbortOnAssertion = pdFALSE;

    /* Returns NULL if a NULL struct is passed as a parameter. */
    xStreamBuffer = xStreamBufferCreateStatic( sizeof( streamBufferArray ), TEST_STREAM_BUFFER_TRIGGER_LEVEL, streamBufferArray, NULL );
    TEST_ASSERT_NULL( xStreamBuffer );
    validate_and_clear_assertions();
}

/**
 * @brief Validates stream buffer static create fails on passing invalid trigger level
 */
void test_xStreamBufferCreateStatic_invalid_trigger_level( void )
{
    StaticStreamBuffer_t streamBufferStruct;
    /* The size of stream buffer array should be one greater than the required size of stream buffer. */
    uint8_t streamBufferArray[ TEST_STREAM_BUFFER_SIZE + 1 ] = { 0 };

    EXPECT_ASSERT_BREAK( ( void ) xStreamBufferCreateStatic( sizeof( streamBufferArray ), TEST_STREAM_BUFFER_SIZE + 2, streamBufferArray, &streamBufferStruct ) );

    validate_and_clear_assertions();
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
 * @brief Validates that sending data more than stream buffer size will cap it to the size of stream buffer without blocking.
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

    /* Sending bytes more than stream buffer size caps its to the size of stream buffer. */
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE + 1, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sent );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferBytesAvailable( xStreamBuffer ) );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Sending zero bytes to stream buffer should return write nothing to the
 * buffer and return 0.
 */
void test_xStreamBufferSend_zero_bytes( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE + 1 ] = { 0 };

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of the default test sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    TEST_ASSERT_EQUAL( pdFALSE, xStreamBufferSend( xStreamBuffer, data, 0U, TEST_STREAM_BUFFER_WAIT_TICKS ) );

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
    TEST_ASSERT_EQUAL( tskDEFAULT_INDEX_TO_NOTIFY, uxStreamBufferGetStreamBufferNotificationIndex( xStreamBuffer ) );

    /* Sending upto size of stream buffer should not block. */
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE - 1, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE - 1, sent );
    TEST_ASSERT_EQUAL( 1, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /*
     * Sending beyond the stream buffer size should make task wait for upto TEST_STREAM_BUFFER_WAIT_TICKS. After the timeout
     * elapses, task should return with partial bytes sent.
     */
    xTaskGenericNotifyWait_ExpectAndReturn( 0, 0, 0, NULL, TEST_STREAM_BUFFER_WAIT_TICKS, pdTRUE );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 1, sent );
    TEST_ASSERT_EQUAL( pdTRUE, xStreamBufferIsFull( xStreamBuffer ) );

    /*
     * A task trying to send to a stream buffer without any space available should block for upto TEST_STREAM_BUFFER_WAIT_TICKS.
     * Sender task should be notified and woken up when bytes are consumed by a receiver task during the wait period.
     */
    xTaskGenericNotifyWait_StubWithCallback( streamBufferReceiveCallback );
    xTaskGenericNotify_StubWithCallback( senderTaskNotificationCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sent );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 1, senderTaskWoken );

    /*
     * A task trying to send to a stream buffer without any space available should block for upto TEST_STREAM_BUFFER_WAIT_TICKS.
     * Sender task should be notified and woken up when bytes are consumed by an ISR during the wait period.
     */
    xTaskGenericNotifyWait_StubWithCallback( streamBufferReceiveFromISRCallback );
    xTaskGenericNotifyFromISR_StubWithCallback( senderTaskNotificationFromISRCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sent );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 2, senderTaskWoken );


    /*
     * A task trying to send to a stream buffer without any space available should block for upto TEST_STREAM_BUFFER_WAIT_TICKS.
     * Sender task should be notified and woken up when bytes are consumed by a receiver task during the wait period,
     * also with different notification index.
     */
    vStreamBufferSetStreamBufferNotificationIndex( xStreamBuffer, TEST_STREAM_BUFFER_NOTIFICATION_INDEX );
    xTaskGenericNotifyWait_AddCallback( streamBufferReceiveCallback );
    xTaskGenericNotify_StubWithCallback( senderTaskNotificationCallback );
    xTaskGenericNotifyWait_ExpectAndReturn( TEST_STREAM_BUFFER_NOTIFICATION_INDEX, 0, 0, NULL, TEST_STREAM_BUFFER_WAIT_TICKS, pdTRUE );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_NOTIFICATION_INDEX, uxStreamBufferGetStreamBufferNotificationIndex( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sent );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 3, senderTaskWoken );

    /*
     * A task trying to send to a stream buffer without any space available should block for upto TEST_STREAM_BUFFER_WAIT_TICKS.
     * Sender task should be notified and woken up when bytes are consumed by an ISR during the wait period,
     * also with different notification index. (restore default index after this run)
     */
    vStreamBufferSetStreamBufferNotificationIndex( xStreamBuffer, TEST_STREAM_BUFFER_NOTIFICATION_INDEX );
    xTaskGenericNotifyWait_AddCallback( streamBufferReceiveFromISRCallback );
    xTaskGenericNotifyWait_ExpectAndReturn( TEST_STREAM_BUFFER_NOTIFICATION_INDEX, 0, 0, NULL, TEST_STREAM_BUFFER_WAIT_TICKS, pdTRUE );
    xTaskGenericNotifyFromISR_StubWithCallback( senderTaskNotificationFromISRCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_NOTIFICATION_INDEX, uxStreamBufferGetStreamBufferNotificationIndex( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sent );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 4, senderTaskWoken );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief This test case validates that multiple concurrent writers are not allowed on a stream buffer.
 * The API should cause an assert fail, if a second task tries to write to the stream buffer
 * while first task is blocked writing onto it.
 */
void test_xStreamBufferSend_concurrent_writers( void )
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

    /* Sending upto full size of stream buffer should not block. */
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sent );
    TEST_ASSERT_EQUAL( 0, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /*
     * Sending data to a stream buffer now should cause the sender task to block by calling xTaskGenericNotifyWait callback.
     * Withing the callback a second sender tries to send data to same stream buffer which will
     * cause the assert to fail.
     */
    xTaskGenericNotifyWait_StubWithCallback( streamBufferSendCallback );
    xTaskGenericNotify_StubWithCallback( senderTaskNotificationCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    EXPECT_ASSERT_BREAK( ( void ) xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS ) );
    validate_and_clear_assertions();

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

    /* Sending data of upto stream buffer size should not block. */
    dataSent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, dataSent );
    TEST_ASSERT_EQUAL( 0, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /*  Sending data beyond stream buffer size but with zero wait ticks should not block and return zero bytes sent. */
    dataSent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, 0 );
    TEST_ASSERT_EQUAL( 0, dataSent );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates that a task is able to receive from a non empty stream buffer without blocking.
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

    /* Receive the partial data from stream Buffer without blocking. */
    receivedBytes = xStreamBufferReceive( xStreamBuffer, &dataReceived, TEST_STREAM_BUFFER_SIZE - 1, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE - 1, receivedBytes );
    TEST_ASSERT_EQUAL_HEX8_ARRAY( data, dataReceived, receivedBytes );
    TEST_ASSERT_EQUAL( 1, xStreamBufferBytesAvailable( xStreamBuffer ) );

    /* Request for full TEST_STREAM_BUFFER_SIZE bytes, but only receive what's available without blocking.  */
    receivedBytes = xStreamBufferReceive( xStreamBuffer, &dataReceived, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 1, receivedBytes );
    TEST_ASSERT_EQUAL( 0, xStreamBufferBytesAvailable( xStreamBuffer ) );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates receiving from an empty stream buffer will block until at least trigger level bytes are
 * sent to the buffer.
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
    TEST_ASSERT_EQUAL( 0, xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( tskDEFAULT_INDEX_TO_NOTIFY, uxStreamBufferGetStreamBufferNotificationIndex( xStreamBuffer ) );

    /*
     * Receiving from an empty buffer causes the task to wait for TEST_STREAM_BUFFER_WAIT_TICKS period.
     * After the timeout elapses, task returns with zero bytes received.
     */
    xTaskGenericNotifyWait_ExpectAndReturn( 0, 0, 0, NULL, TEST_STREAM_BUFFER_WAIT_TICKS, pdTRUE );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );
    receivedBytes = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 0, receivedBytes );

    /*
     * Sending at least trigger level bytes, should notify and wake up the receiver task.
     */
    xTaskGenericNotifyWait_StubWithCallback( streamBufferSendCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    receivedBytes = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, receivedBytes );
    TEST_ASSERT_EQUAL( 1, receiverTaskWoken );
    TEST_ASSERT_EQUAL( 0, xStreamBufferBytesAvailable( xStreamBuffer ) );

    /*
     * Sending at least trigger level bytes from ISR, should notify and wake up the receiver task.
     */
    xTaskGenericNotifyWait_StubWithCallback( streamBufferSendFromISRCallback );
    xTaskGenericNotifyFromISR_StubWithCallback( receiverTaskNotificationFromISRCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    receivedBytes = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, receivedBytes );
    TEST_ASSERT_EQUAL( 2, receiverTaskWoken );
    TEST_ASSERT_EQUAL( 0, xStreamBufferBytesAvailable( xStreamBuffer ) );


    /* Sending less than trigger level bytes should not wake up the task. */
    xTaskGenericNotifyWait_StubWithCallback( sendLessThanTriggerLevelBytesCallback );
    xTaskGenericNotifyFromISR_StubWithCallback( receiverTaskNotificationFromISRCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );
    receivedBytes = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 2, receiverTaskWoken );

    /* Sending less than trigger level bytes from ISR should not wake up the task. */
    xTaskGenericNotifyWait_StubWithCallback( sendLessThanTriggerLevelBytesFromISRCallback );
    xTaskGenericNotifyFromISR_StubWithCallback( receiverTaskNotificationFromISRCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );
    receivedBytes = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 2, receiverTaskWoken );


    /*
     * Sending at least trigger level bytes, should notify and wake up the receiver task,
     * also with different notification index.
     */
    vStreamBufferSetStreamBufferNotificationIndex( xStreamBuffer, TEST_STREAM_BUFFER_NOTIFICATION_INDEX );
    xTaskGenericNotifyWait_AddCallback( streamBufferSendCallback );
    xTaskGenericNotifyWait_ExpectAndReturn( TEST_STREAM_BUFFER_NOTIFICATION_INDEX, 0, 0, NULL, TEST_STREAM_BUFFER_WAIT_TICKS, pdTRUE );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    receivedBytes = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_NOTIFICATION_INDEX, uxStreamBufferGetStreamBufferNotificationIndex( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, receivedBytes );
    TEST_ASSERT_EQUAL( 3, receiverTaskWoken );
    TEST_ASSERT_EQUAL( 0, xStreamBufferBytesAvailable( xStreamBuffer ) );

    /*
     * Sending at least trigger level bytes from ISR, should notify and wake up the receiver task,
     * also with different notification index. (restore default index after this run)
     */
    xTaskGenericNotifyWait_AddCallback( streamBufferSendFromISRCallback );
    xTaskGenericNotifyWait_ExpectAndReturn( TEST_STREAM_BUFFER_NOTIFICATION_INDEX, 0, 0, NULL, TEST_STREAM_BUFFER_WAIT_TICKS, pdTRUE );
    xTaskGenericNotifyFromISR_StubWithCallback( receiverTaskNotificationFromISRCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    receivedBytes = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_NOTIFICATION_INDEX, uxStreamBufferGetStreamBufferNotificationIndex( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, receivedBytes );
    TEST_ASSERT_EQUAL( 4, receiverTaskWoken );
    TEST_ASSERT_EQUAL( 0, xStreamBufferBytesAvailable( xStreamBuffer ) );
    vStreamBufferSetStreamBufferNotificationIndex( xStreamBuffer, tskDEFAULT_INDEX_TO_NOTIFY );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief This test case validates that multiple concurrent readers are not allowed on a stream buffer.
 * The API should cause an assert  fail if a second task tries to read from the stream buffer
 * while the first task is blocked reading from it.
 */
void test_xStreamBufferReceive_concurrent_readers( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0xAA };

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
    TEST_ASSERT_EQUAL( 0, xStreamBufferBytesAvailable( xStreamBuffer ) );

    /*
     * Receiving from an empty buffer causes the task to wait by calling xTaskGenericNotifyWait callback.
     * A second reader trying to read concurrently from stream buffer will cause  assert statement
     * to fail.
     */
    xTaskGenericNotifyWait_StubWithCallback( streamBufferReceiveCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    EXPECT_ASSERT_BREAK( ( void ) xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS ) );
    validate_and_clear_assertions();

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates that receiver task does not block if zero wait ticks are passed.
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

    /* Send data to fill the stream buffer to maximum capacity. */
    sentBytes = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sentBytes );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferBytesAvailable( xStreamBuffer ) );

    /* Receive partial data from stream buffer without blocking. */
    receivedBytes = xStreamBufferReceiveFromISR( xStreamBuffer, &dataReceived, ( TEST_STREAM_BUFFER_SIZE - 1U ), &xHighPriorityTaskWoken );
    TEST_ASSERT_EQUAL( ( TEST_STREAM_BUFFER_SIZE - 1U ), receivedBytes );
    TEST_ASSERT_EQUAL_HEX8_ARRAY( data, dataReceived, receivedBytes );
    TEST_ASSERT_EQUAL( pdFALSE, xHighPriorityTaskWoken );

    /* Try to receive full capacity from stream buffer but only remaining data is received. */
    receivedBytes = xStreamBufferReceiveFromISR( xStreamBuffer, &dataReceived, TEST_STREAM_BUFFER_SIZE, &xHighPriorityTaskWoken );
    TEST_ASSERT_EQUAL( 1U, receivedBytes );
    TEST_ASSERT_EQUAL( 0, xStreamBufferBytesAvailable( xStreamBuffer ) );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Assertion fails if a null stream buffer is passed.
 */
void test_xStreamBufferReceiveFromISR_null_stream_buffer( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0xAA };
    BaseType_t xHighPriorityTaskWoken = pdFALSE;

    EXPECT_ASSERT_BREAK( ( void ) xStreamBufferReceiveFromISR( NULL, data, TEST_STREAM_BUFFER_SIZE, &xHighPriorityTaskWoken ) );

    validate_and_clear_assertions();
}

/**
 * @brief Assertion fails if a null message is passed.
 */
void test_xStreamBufferReceiveFromISR_null_buffer( void )
{
    BaseType_t xHighPriorityTaskWoken = pdFALSE;

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    EXPECT_ASSERT_BREAK( ( void ) xStreamBufferReceiveFromISR( xStreamBuffer, NULL, TEST_STREAM_BUFFER_SIZE, &xHighPriorityTaskWoken ) );

    validate_and_clear_assertions();

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

    /* Send full capacity from ISR again should send partial bytes without blocking. */
    sentBytes = xStreamBufferSendFromISR( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, &xHighPriorityTaskWoken );
    TEST_ASSERT_EQUAL( 1U, sentBytes );
    TEST_ASSERT_EQUAL( 0, xStreamBufferSpacesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( pdFALSE, xHighPriorityTaskWoken );

    /* Send to full stream buffer should return 0 bytes sent without blocking. */
    sentBytes = xStreamBufferSendFromISR( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, &xHighPriorityTaskWoken );
    TEST_ASSERT_EQUAL( 0U, sentBytes );
    TEST_ASSERT_EQUAL( pdFALSE, xHighPriorityTaskWoken );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Assertion fails if a null stream buffer is passed.
 */
void test_xStreamBufferSendFromISR_null_stream_buffer( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0xAA };
    BaseType_t xHighPriorityTaskWoken = pdFALSE;

    EXPECT_ASSERT_BREAK( ( void ) xStreamBufferSendFromISR( NULL, data, TEST_STREAM_BUFFER_SIZE, &xHighPriorityTaskWoken ) );

    validate_and_clear_assertions();
}

/**
 * @brief Assertion fails if a null message is passed.
 */
void test_xStreamBufferSendFromISR_null_message( void )
{
    BaseType_t xHighPriorityTaskWoken = pdFALSE;

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    EXPECT_ASSERT_BREAK( ( void ) xStreamBufferSendFromISR( xStreamBuffer, NULL, TEST_STREAM_BUFFER_SIZE, &xHighPriorityTaskWoken ) );

    validate_and_clear_assertions();

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

    /* Send full capacity to stream buffer. */
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
 * @brief Resetting a null stream buffer should fail assertion.
 */
void test_xStreamBufferReset_null_stream_buffer( void )
{
    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    EXPECT_ASSERT_BREAK( ( void ) xStreamBufferReset( NULL ) );
    validate_and_clear_assertions();
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
void test_xStreamBufferSetTriggerLevel_success( void )
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
void test_xStreamBufferSetTriggerLevel_larger_than_buffer_size( void )
{
    BaseType_t status;

    /* Create stream buffer. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );

    /* Set the trigger level to ( TEST_STREAM_BUFFER_SIZE + 1) should fail. */
    status = xStreamBufferSetTriggerLevel( xStreamBuffer, ( TEST_STREAM_BUFFER_SIZE + 1 ) );
    TEST_ASSERT_EQUAL( pdFALSE, status );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Set the trigger level to 0 should pass but internally set trigger level to 1.
 */
void test_xStreamBufferSetTriggerLevel_zero( void )
{
    BaseType_t status;

    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );

    status = xStreamBufferSetTriggerLevel( xStreamBuffer, 0 );
    TEST_ASSERT_EQUAL( pdTRUE, status );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Setting trigger level for  a null stream buffer should fail assertion.
 */
void test_xStreamBufferSetTriggerLevel_null_stream_buffer( void )
{
    EXPECT_ASSERT_BREAK( ( void ) xStreamBufferSetTriggerLevel( NULL, TEST_STREAM_BUFFER_TRIGGER_LEVEL ) );
    validate_and_clear_assertions();
}

/**
 * @brief Checking bytes available for a null stream buffer should fail assertion.
 */
void test_xStreamBufferBytesAvailable_null_stream_buffer( void )
{
    EXPECT_ASSERT_BREAK( ( void ) xStreamBufferBytesAvailable( NULL ) );
    validate_and_clear_assertions();
}

/**
 * @brief Checking if stream buffer is full for a null stream buffer should fail assertion.
 */
void test_xStreamBufferIsFull_null_stream_buffer( void )
{
    EXPECT_ASSERT_BREAK( ( void ) xStreamBufferIsFull( NULL ) );
    validate_and_clear_assertions();
}

/**
 * @brief Checking if stream buffer is empty for a null stream buffer should fail assertion.
 */
void test_xStreamBufferIsEmpty_null_stream_buffer( void )
{
    EXPECT_ASSERT_BREAK( ( void ) xStreamBufferIsEmpty( NULL ) );
    validate_and_clear_assertions();
}

/**
 * @brief Checking buffer size for a null stream buffer should fail assertion.
 */
void test_xStreamBufferSpacesAvailable_null_stream_buffer( void )
{
    EXPECT_ASSERT_BREAK( ( void ) xStreamBufferSpacesAvailable( NULL ) );
    validate_and_clear_assertions();
}

/**
 * @brief Checking Next message length available for a null stream buffer fails
 * assertion.
 */
void test_xStreamBufferNextMessageLengthBytes_null_stream_buffer( void )
{
    EXPECT_ASSERT_BREAK( ( void ) xStreamBufferNextMessageLengthBytes( NULL ) );
    validate_and_clear_assertions();
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

    /* Send completed from ISR without receiver task waiting. */
    status = xStreamBufferSendCompletedFromISR( xStreamBuffer, &highPriorityTaskWoken );
    TEST_ASSERT_EQUAL( pdFALSE, status );
    TEST_ASSERT_EQUAL( pdFALSE, highPriorityTaskWoken );

    /* Send completed from ISR with receiver task waiting. */
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
 * @brief Validates xStreamBufferSendCompletedFromISR fails assertion if a null stream buffer is passed.
 */
void test_xStreamBufferSendCompletedFromISR_null_stream_buffer( void )
{
    BaseType_t highPriorityTaskWoken = pdFALSE;

    /* Send completed from ISR without receiver task waiting. */
    EXPECT_ASSERT_BREAK( ( void ) xStreamBufferSendCompletedFromISR( NULL, &highPriorityTaskWoken ) );
    validate_and_clear_assertions();
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

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of the default test sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );

    /* Receive completed from ISR without a sender task waiting. */
    status = xStreamBufferReceiveCompletedFromISR( xStreamBuffer, &highPriorityTaskWoken );
    TEST_ASSERT_EQUAL( pdFALSE, status );
    TEST_ASSERT_EQUAL( pdFALSE, highPriorityTaskWoken );


    /* Send full capacity to a stream buffer so that sender task blocks. */
    sentBytes = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sentBytes );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferBytesAvailable( xStreamBuffer ) );

    /* Receive completed from ISR when a sender task is waiting. */
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( senderTask );
    xTaskGenericNotifyWait_StubWithCallback( receiveCompletedFromISRCallback );
    xTaskGenericNotifyFromISR_StubWithCallback( senderTaskNotificationFromISRCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );
    sentBytes = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 0, sentBytes );
    TEST_ASSERT_EQUAL( 1, senderTaskWoken );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Validates xStreamBufferReceiveCompletedFromISR fails assertion if a null stream buffer is passed.
 */
void test_xStreamBufferReceiveCompletedFromISR_null_stream_buffer( void )
{
    BaseType_t highPriorityTaskWoken = pdFALSE;

    /* Send completed from ISR without receiver task waiting. */
    EXPECT_ASSERT_BREAK( ( void ) xStreamBufferReceiveCompletedFromISR( NULL, &highPriorityTaskWoken ) );
    validate_and_clear_assertions();
}

/**
 * @brief Validates scenario where stream buffer head and tail pointer wraps over.
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

    /* Sending bytes upto max stream buffer size. */
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

/**
 * @brief validate xStreamBufferGetStaticBuffers with a null xStreamBuffer argument
 * @details Test that xStreamBufferGetStaticBuffers asserts when a null StreamBufferHandle_t is given.
 */
void test_xStreamBufferGetStaticBuffers_null_xStreamBuffer( void )
{
    uint8_t * pucStreamBufferStorageAreaRet = NULL;
    StaticStreamBuffer_t * pxStaticStreamBufferRet = NULL;

    EXPECT_ASSERT_BREAK( xStreamBufferGetStaticBuffers( NULL, &pucStreamBufferStorageAreaRet, &pxStaticStreamBufferRet ) );

    validate_and_clear_assertions();

    /* Assert that pucStreamBufferStorageAreaRet and pxStaticStreamBufferRet were not modified */
    TEST_ASSERT_EQUAL( NULL, pucStreamBufferStorageAreaRet );
    TEST_ASSERT_EQUAL( NULL, pxStaticStreamBufferRet );
}

/**
 * @brief Test xStreamBufferGetStaticBuffers with a null ppxStaticStreamBuffer argument
 * @details Test that xStreamBufferGetStaticBuffers asserts when a null ppxStaticStreamBuffer is given.
 */
void test_xStreamBufferGetStaticBuffers_null_ppxStaticStreamBuffer( void )
{
    StreamBufferHandle_t xStreamBuffer = NULL;
    StaticStreamBuffer_t streamBufferStruct;

    /* The size of stream buffer array should be one greater than the required size of stream buffer. */
    uint8_t streamBufferArray[ TEST_STREAM_BUFFER_SIZE + 1 ] = { 0 };

    uint8_t * pucStreamBufferStorageAreaRet = NULL;

    xStreamBuffer = xStreamBufferCreateStatic( sizeof( streamBufferArray ), TEST_STREAM_BUFFER_TRIGGER_LEVEL, streamBufferArray, &streamBufferStruct );

    EXPECT_ASSERT_BREAK( xStreamBufferGetStaticBuffers( xStreamBuffer, &pucStreamBufferStorageAreaRet, NULL ) );

    validate_and_clear_assertions();

    /* Assert that pucStreamBufferStorageAreaRet was not modified */
    TEST_ASSERT_EQUAL( NULL, pucStreamBufferStorageAreaRet );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Test xStreamBufferGetStaticBuffers with a null ppucStreamBufferStorageArea argument
 * @details Test that xStreamBufferGetStaticBuffers asserts when a null ppucStreamBufferStorageArea is given.
 */
void test_xStreamBufferGetStaticBuffers_null_ppucStreamBufferStorageArea( void )
{
    StreamBufferHandle_t xStreamBuffer = NULL;
    StaticStreamBuffer_t streamBufferStruct;

    /* The size of stream buffer array should be one greater than the required size of stream buffer. */
    uint8_t streamBufferArray[ TEST_STREAM_BUFFER_SIZE + 1 ] = { 0 };
    StaticStreamBuffer_t * pxStaticStreamBufferRet = NULL;

    xStreamBuffer = xStreamBufferCreateStatic( sizeof( streamBufferArray ), TEST_STREAM_BUFFER_TRIGGER_LEVEL, streamBufferArray, &streamBufferStruct );

    EXPECT_ASSERT_BREAK( xStreamBufferGetStaticBuffers( xStreamBuffer, NULL, &pxStaticStreamBufferRet ) );

    validate_and_clear_assertions();

    /* Assert that pxStaticStreamBufferRet was not modified */
    TEST_ASSERT_EQUAL( NULL, pxStaticStreamBufferRet );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief validate xStreamBufferGetStaticBuffers on a statically created stream buffer
 * @details Test xStreamBufferGetStaticBuffers returns the buffers of a statically created stream buffer
 */
void test_xStreamBufferGetStaticBuffers_static( void )
{
    StreamBufferHandle_t xStreamBuffer = NULL;
    StaticStreamBuffer_t streamBufferStruct;

    /* The size of stream buffer array should be one greater than the required size of stream buffer. */
    uint8_t streamBufferArray[ TEST_STREAM_BUFFER_SIZE + 1 ] = { 0 };
    uint8_t * pucStreamBufferStorageAreaRet = NULL;
    StaticStreamBuffer_t * pxStaticStreamBufferRet = NULL;

    xStreamBuffer = xStreamBufferCreateStatic( sizeof( streamBufferArray ), TEST_STREAM_BUFFER_TRIGGER_LEVEL, streamBufferArray, &streamBufferStruct );

    TEST_ASSERT_EQUAL( pdTRUE, xStreamBufferGetStaticBuffers( xStreamBuffer, &pucStreamBufferStorageAreaRet, &pxStaticStreamBufferRet ) );
    TEST_ASSERT_EQUAL( streamBufferArray, pucStreamBufferStorageAreaRet );
    TEST_ASSERT_EQUAL( &streamBufferStruct, pxStaticStreamBufferRet );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief validate xStreamBufferGetStaticBuffers on a dynamically created stream buffer
 * @details Test xStreamBufferGetStaticBuffers returns an error when called on a dynamically created stream buffer
 */
void test_xStreamBufferGetStaticBuffers_dynamic( void )
{
    StreamBufferHandle_t xStreamBuffer = NULL;
    uint8_t * pucStreamBufferStorageAreaRet = NULL;
    StaticStreamBuffer_t * pxStaticStreamBufferRet = NULL;

    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_EQUAL( NULL, xStreamBuffer );

    TEST_ASSERT_EQUAL( pdFALSE, xStreamBufferGetStaticBuffers( xStreamBuffer, &pucStreamBufferStorageAreaRet, &pxStaticStreamBufferRet ) );
    TEST_ASSERT_EQUAL( NULL, pucStreamBufferStorageAreaRet );
    TEST_ASSERT_EQUAL( NULL, pxStaticStreamBufferRet );

    vStreamBufferDelete( xStreamBuffer );
}
