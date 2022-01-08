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

/* ==============================  Test Cases  ============================== */

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
