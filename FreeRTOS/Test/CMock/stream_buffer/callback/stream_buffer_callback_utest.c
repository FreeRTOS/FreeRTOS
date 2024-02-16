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
/*! @file stream_buffer_callback_utest.c */

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
 * empty while receiving data.
 */
#define TEST_STREAM_BUFFER_WAIT_TICKS       ( 1000U )

/**
 * @brief CException code for when a configASSERT should be intercepted.
 */
#define configASSERT_E                      0xAA101

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
 * @brief Global counter to keep track of how many times a send callback was invoked from a stream buffer.
 */
static int sendCallbackInvoked = 0;

/**
 * @brief Global counter to keep track of how many times a send callback was invoked from a stream buffer in ISR.
 */
static int sendCallbackInvokedFromISR = 0;

/**
 * @brief Global counter to keep track of how many times a receiver callback was invoked from a stream buffer.
 */
static int receiveCallbackInvoked = 0;

/**
 * @brief Global counter to keep track of how many times a receiver callback was invoked from a stream buffer in ISR.
 */
static int receiveCallbackInvokedFromISR = 0;

/**
 * @brief Global counter to keep track of how many times a default  callback was invoked.
 */
static int defaultCallbackInvoked = 0;

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

static void sendCompletedStub( StreamBufferHandle_t xCallingStreamBuffer,
                               BaseType_t xInsideISR,
                               BaseType_t * const pxHigherPriorityTaskWoken )
{
    size_t dataAvailable = 0;

    TEST_ASSERT_NOT_NULL( xCallingStreamBuffer );
    TEST_ASSERT_TRUE( ( xInsideISR == pdFALSE ) || ( pxHigherPriorityTaskWoken != NULL ) );
    TEST_ASSERT_FALSE( ( xInsideISR == pdFALSE ) && ( pxHigherPriorityTaskWoken != NULL ) );

    /* Validate that atleast trigger level bytes are available from stream buffer. */
    dataAvailable = xStreamBufferBytesAvailable( xCallingStreamBuffer );
    TEST_ASSERT_GREATER_OR_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, dataAvailable );

    if( xInsideISR )
    {
        sendCallbackInvokedFromISR++;
        ( *pxHigherPriorityTaskWoken ) = pdTRUE;
    }
    else
    {
        sendCallbackInvoked++;
    }
}

void vDefaultSendCompletedStub( void * xStreamBuffer )
{
    size_t dataAvailable = 0;

    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    /* Validate that atleast trigger level bytes are available from stream buffer. */
    dataAvailable = xStreamBufferBytesAvailable( xStreamBuffer );
    TEST_ASSERT_GREATER_OR_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, dataAvailable );
    defaultCallbackInvoked++;
    sendCallbackInvoked++;
}

void vDefaultSendCompletedFromISRStub( void * xStreamBuffer,
                                       BaseType_t * const pxTaskWoken )
{
    size_t dataAvailable = 0;

    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    /* Validate that atleast trigger level bytes are available from stream buffer. */
    dataAvailable = xStreamBufferBytesAvailable( xStreamBuffer );
    TEST_ASSERT_GREATER_OR_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, dataAvailable );

    defaultCallbackInvoked++;
    sendCallbackInvokedFromISR++;
    ( *pxTaskWoken ) = pdTRUE;
}

static void receiveCompletedStub( StreamBufferHandle_t xCallingStreamBuffer,
                                  BaseType_t xInsideISR,
                                  BaseType_t * const pxHigherPriorityTaskWoken )
{
    TEST_ASSERT_NOT_NULL( xCallingStreamBuffer );
    TEST_ASSERT_TRUE( ( xInsideISR == pdFALSE ) || ( pxHigherPriorityTaskWoken != NULL ) );
    TEST_ASSERT_FALSE( ( xInsideISR == pdFALSE ) && ( pxHigherPriorityTaskWoken != NULL ) );

    /* Validates that stream buffer has some free space to send data */
    TEST_ASSERT_EQUAL( pdFALSE, xStreamBufferIsFull( xCallingStreamBuffer ) );

    if( xInsideISR )
    {
        receiveCallbackInvokedFromISR++;
        ( *pxHigherPriorityTaskWoken ) = pdTRUE;
    }
    else
    {
        receiveCallbackInvoked++;
    }
}

void vDefaultReceiveCompletedStub( void * xStreamBuffer )
{
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    /* Validates that stream buffer has some free space to send data */
    TEST_ASSERT_EQUAL( pdFALSE, xStreamBufferIsFull( xStreamBuffer ) );
    receiveCallbackInvoked++;
    defaultCallbackInvoked++;
}

void vDefaultReceiveCompletedFromISRStub( void * xStreamBuffer,
                                          BaseType_t * const pxTaskWoken )
{
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    /* Validates that stream buffer has some free space to send data */
    TEST_ASSERT_EQUAL( pdFALSE, xStreamBufferIsFull( xStreamBuffer ) );
    receiveCallbackInvokedFromISR++;
    defaultCallbackInvoked++;
    ( *pxTaskWoken ) = pdTRUE;
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

/*******************************************************************************
 * Unity fixtures
 ******************************************************************************/
void setUp( void )
{
    assertionFailed = 0;
    xStreamBuffer = NULL;
    sendCallbackInvoked = 0;
    sendCallbackInvokedFromISR = 0;
    receiveCallbackInvoked = 0;
    receiveCallbackInvokedFromISR = 0;
    defaultCallbackInvoked = 0;
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


/* ==============================  Test Cases  ============================== */

/**
 * @brief Tests backwards compatibility with the existing API. Calling StreamBufferCreate() should
 * create a stream buffer successfully with per instance callbacks set to NULL.
 */
void test_xStreamBufferCreate_NoCallback( void )
{
    StaticStreamBuffer_t * pxStreamBufferStruct;

    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_EQUAL( NULL, xStreamBuffer );

    /* Verify internal memory allocated is equal to size of the struct + buffer size + 1. */
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE + 1U + sizeof( StaticStreamBuffer_t ), dynamicMemoryAllocated );

    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    /* Set a stream buffer number and get it. */
    vStreamBufferSetStreamBufferNumber( xStreamBuffer, TEST_STREAM_BUFFER_NUMBER );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_NUMBER, uxStreamBufferGetStreamBufferNumber( xStreamBuffer ) );

    pxStreamBufferStruct = ( StaticStreamBuffer_t * ) ( xStreamBuffer );
    TEST_ASSERT_NULL( pxStreamBufferStruct->pvDummy5[ 0 ] );
    TEST_ASSERT_NULL( pxStreamBufferStruct->pvDummy5[ 1 ] );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Tests successful creation of dynamic stream buffer with callbacks.
 */
void test_xStreamBufferCreate_WithCallback( void )
{
    StaticStreamBuffer_t * pxStreamBufferStruct;

    xStreamBuffer = xStreamBufferCreateWithCallback( TEST_STREAM_BUFFER_SIZE,
                                                     TEST_STREAM_BUFFER_TRIGGER_LEVEL,
                                                     sendCompletedStub,
                                                     receiveCompletedStub );
    TEST_ASSERT_NOT_EQUAL( NULL, xStreamBuffer );

    /* Verify internal memory allocated is equal to size of the struct + buffer size + 1. */
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE + 1U + sizeof( StaticStreamBuffer_t ), dynamicMemoryAllocated );

    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    /* Set a stream buffer number and get it. */
    vStreamBufferSetStreamBufferNumber( xStreamBuffer, TEST_STREAM_BUFFER_NUMBER );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_NUMBER, uxStreamBufferGetStreamBufferNumber( xStreamBuffer ) );

    pxStreamBufferStruct = ( StaticStreamBuffer_t * ) ( xStreamBuffer );
    TEST_ASSERT_EQUAL( sendCompletedStub, pxStreamBufferStruct->pvDummy5[ 0 ] );
    TEST_ASSERT_EQUAL( receiveCompletedStub, pxStreamBufferStruct->pvDummy5[ 1 ] );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Tests backwards compatibility with the existing API. Calling StreamBufferCreateStatic() should
 * create a stream buffer successfully with per instance callbacks set to NULL.
 */
void test_xStreamBufferCreateStatic_NoCallback( void )
{
    StaticStreamBuffer_t streamBufferStruct;

    /* The size of stream buffer array should be one greater than the required size of stream buffer. */
    uint8_t streamBufferArray[ TEST_STREAM_BUFFER_SIZE + 1 ] = { 0 };

    xStreamBuffer = xStreamBufferCreateStatic( sizeof( streamBufferArray ), TEST_STREAM_BUFFER_TRIGGER_LEVEL, streamBufferArray, &streamBufferStruct );

    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    TEST_ASSERT_NULL( streamBufferStruct.pvDummy5[ 0 ] );
    TEST_ASSERT_NULL( streamBufferStruct.pvDummy5[ 1 ] );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Tests successful creation of static stream buffer with callbacks.
 */
void test_xStreamBufferCreateStatic_WithCallback( void )
{
    StaticStreamBuffer_t streamBufferStruct;

    /* The size of stream buffer array should be one greater than the required size of stream buffer. */
    uint8_t streamBufferArray[ TEST_STREAM_BUFFER_SIZE + 1 ] = { 0 };

    xStreamBuffer = xStreamBufferCreateStaticWithCallback( sizeof( streamBufferArray ),
                                                           TEST_STREAM_BUFFER_TRIGGER_LEVEL,
                                                           streamBufferArray,
                                                           &streamBufferStruct,
                                                           sendCompletedStub,
                                                           receiveCompletedStub );

    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    TEST_ASSERT_EQUAL( sendCompletedStub, streamBufferStruct.pvDummy5[ 0 ] );
    TEST_ASSERT_EQUAL( receiveCompletedStub, streamBufferStruct.pvDummy5[ 1 ] );

    vStreamBufferDelete( xStreamBuffer );
}


/**
 * @brief Tests send completed callback is invoked by a sender task sending atleast bytes
 * equal to trigger level into the streambuffer.
 */
void test_xStreamBufferSend_CallbackInvoked( void )
{
    size_t sent = 0;
    uint8_t data[ TEST_STREAM_BUFFER_TRIGGER_LEVEL ] = { 0xFF };

    xStreamBuffer = xStreamBufferCreateWithCallback( TEST_STREAM_BUFFER_SIZE,
                                                     TEST_STREAM_BUFFER_TRIGGER_LEVEL,
                                                     sendCompletedStub,
                                                     NULL );

    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Send data equal to trigger level bytes should invoke the send completed callback. */
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, sent );
    TEST_ASSERT_EQUAL( 1, sendCallbackInvoked );
    TEST_ASSERT_EQUAL( 0, sendCallbackInvokedFromISR );
    TEST_ASSERT_EQUAL( 0, defaultCallbackInvoked );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Tests send completed callback is not invoked if less than
 * trigger level bytes are sent to the streambuffer.
 */
void test_xStreamBufferSend_CallbackNotInvoked( void )
{
    size_t sent = 0;
    uint8_t data[ TEST_STREAM_BUFFER_TRIGGER_LEVEL ] = { 0xFF };

    xStreamBuffer = xStreamBufferCreateWithCallback( TEST_STREAM_BUFFER_SIZE,
                                                     TEST_STREAM_BUFFER_TRIGGER_LEVEL,
                                                     sendCompletedStub,
                                                     NULL );

    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Send data less than trigger level bytes should not invoke the send completed callback. */
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL - 1U, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL - 1U, sent );
    TEST_ASSERT_EQUAL( 0, sendCallbackInvoked );
    TEST_ASSERT_EQUAL( 0, sendCallbackInvokedFromISR );
    TEST_ASSERT_EQUAL( 0, defaultCallbackInvoked );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Tests default callback is invoked if the user provided send callback is NULL
 */
void test_xStreamBufferSend_DefaultCallbackInvoked( void )
{
    size_t sent = 0;
    uint8_t data[ TEST_STREAM_BUFFER_TRIGGER_LEVEL ] = { 0xFF };

    xStreamBuffer = xStreamBufferCreateWithCallback( TEST_STREAM_BUFFER_SIZE,
                                                     TEST_STREAM_BUFFER_TRIGGER_LEVEL,
                                                     NULL,
                                                     NULL );

    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Send data equal to trigger level bytes should invoke the default send completed callback. */
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, sent );
    TEST_ASSERT_EQUAL( 1, sendCallbackInvoked );
    TEST_ASSERT_EQUAL( 0, sendCallbackInvokedFromISR );
    TEST_ASSERT_EQUAL( 1, defaultCallbackInvoked );

    vStreamBufferDelete( xStreamBuffer );
}


/**
 * @brief Tests send completed callback is invoked by sending atleast bytes
 * equal to trigger level from an ISR.
 */
void test_xStreamBufferSendFromISR_CallbackInvoked( void )
{
    size_t sent = 0;
    uint8_t data[ TEST_STREAM_BUFFER_TRIGGER_LEVEL ] = { 0xFF };
    BaseType_t highPriorityTaskWoken = pdFALSE;

    xStreamBuffer = xStreamBufferCreateWithCallback( TEST_STREAM_BUFFER_SIZE,
                                                     TEST_STREAM_BUFFER_TRIGGER_LEVEL,
                                                     sendCompletedStub,
                                                     NULL );

    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Send data equal to trigger level bytes from should invoke the send completed callback with ISR flag. */
    sent = xStreamBufferSendFromISR( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL, &highPriorityTaskWoken );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, sent );
    TEST_ASSERT_EQUAL( 1, sendCallbackInvokedFromISR );
    TEST_ASSERT_EQUAL( 0, sendCallbackInvoked );
    TEST_ASSERT_EQUAL( 0, defaultCallbackInvoked );
    TEST_ASSERT_EQUAL( pdTRUE, highPriorityTaskWoken );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Tests send completed callback is not invoked by sending less than trigger bytes
 * from an ISR.
 */
void test_xStreamBufferSendFromISR_CallbackNotInvoked( void )
{
    size_t sent = 0;
    uint8_t data[ TEST_STREAM_BUFFER_TRIGGER_LEVEL ] = { 0xFF };
    BaseType_t highPriorityTaskWoken = pdFALSE;

    xStreamBuffer = xStreamBufferCreateWithCallback( TEST_STREAM_BUFFER_SIZE,
                                                     TEST_STREAM_BUFFER_TRIGGER_LEVEL,
                                                     sendCompletedStub,
                                                     NULL );

    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Send data less than trigger level bytes from should not invoke the send completed callback with ISR flag. */
    sent = xStreamBufferSendFromISR( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL - 1, &highPriorityTaskWoken );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL - 1, sent );
    TEST_ASSERT_EQUAL( 0, sendCallbackInvokedFromISR );
    TEST_ASSERT_EQUAL( 0, sendCallbackInvoked );
    TEST_ASSERT_EQUAL( 0, defaultCallbackInvoked );
    TEST_ASSERT_EQUAL( pdFALSE, highPriorityTaskWoken );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Tests default send completed callback is invoked by sending atleast bytes
 * equal to trigger level from an ISR and send callback set to NULL.
 */
void test_xStreamBufferSendFromISR_DefaultCallbackInvoked( void )
{
    size_t sent = 0;
    uint8_t data[ TEST_STREAM_BUFFER_TRIGGER_LEVEL ] = { 0xFF };
    BaseType_t highPriorityTaskWoken = pdFALSE;

    xStreamBuffer = xStreamBufferCreateWithCallback( TEST_STREAM_BUFFER_SIZE,
                                                     TEST_STREAM_BUFFER_TRIGGER_LEVEL,
                                                     NULL,
                                                     NULL );

    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Send data equal to trigger level bytes from should invoke the send completed callback with ISR flag. */
    sent = xStreamBufferSendFromISR( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL, &highPriorityTaskWoken );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, sent );
    TEST_ASSERT_EQUAL( 1, sendCallbackInvokedFromISR );
    TEST_ASSERT_EQUAL( 0, sendCallbackInvoked );
    TEST_ASSERT_EQUAL( 1, defaultCallbackInvoked );
    TEST_ASSERT_EQUAL( pdTRUE, highPriorityTaskWoken );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Tests receive completed callback is invoked by a task receiving atleast 1 bytes
 * from the streambuffer.
 */
void test_xStreamBufferReceive_CallbackInvoked( void )
{
    size_t sent = 0, received = 0;
    uint8_t data[ TEST_STREAM_BUFFER_TRIGGER_LEVEL ] = { 0xFF };

    xStreamBuffer = xStreamBufferCreateWithCallback( TEST_STREAM_BUFFER_SIZE,
                                                     TEST_STREAM_BUFFER_TRIGGER_LEVEL,
                                                     NULL,
                                                     receiveCompletedStub );

    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( NULL );

    /* Send upto trigger level bytes in stream buffer. */
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, sent );

    /* Receive one byte of data should invoke the receive completed callback. */
    received = xStreamBufferReceive( xStreamBuffer, data, 1U, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 1U, received );
    TEST_ASSERT_EQUAL( 1, receiveCallbackInvoked );
    TEST_ASSERT_EQUAL( 0, receiveCallbackInvokedFromISR );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Tests receive completed callback is not invoked zero bytes are received from stream buffer.
 */
void test_xStreamBufferReceive_CallbackNotInvoked( void )
{
    size_t received = 0;
    uint8_t data[ TEST_STREAM_BUFFER_TRIGGER_LEVEL ] = { 0xFF };

    xStreamBuffer = xStreamBufferCreateWithCallback( TEST_STREAM_BUFFER_SIZE,
                                                     TEST_STREAM_BUFFER_TRIGGER_LEVEL,
                                                     NULL,
                                                     receiveCompletedStub );

    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( NULL );
    xTaskGenericNotifyWait_ExpectAndReturn( 0, 0, 0, NULL, TEST_STREAM_BUFFER_WAIT_TICKS, pdTRUE );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );

    /* Receive zero bytes should not invoke the receive completed callback. */
    received = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 0U, received );
    TEST_ASSERT_EQUAL( 0, receiveCallbackInvoked );
    TEST_ASSERT_EQUAL( 0, receiveCallbackInvokedFromISR );
    TEST_ASSERT_EQUAL( 0, defaultCallbackInvoked );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Tests default receive completed callback is invoked by a task receiving atleast 1 bytes
 * from the streambuffer and receive callback set to NULL.
 */
void test_xStreamBufferReceive_DefaultCallbackInvoked( void )
{
    size_t sent = 0, received = 0;
    uint8_t data[ TEST_STREAM_BUFFER_TRIGGER_LEVEL ] = { 0xFF };

    xStreamBuffer = xStreamBufferCreateWithCallback( TEST_STREAM_BUFFER_SIZE,
                                                     TEST_STREAM_BUFFER_TRIGGER_LEVEL,
                                                     NULL,
                                                     NULL );

    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( NULL );

    /* Send upto trigger level bytes in stream buffer. */
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, sent );
    TEST_ASSERT_EQUAL( 1, sendCallbackInvoked );
    TEST_ASSERT_EQUAL( 1, defaultCallbackInvoked );

    /* Receive one byte of data should invoke the receive completed callback. */
    received = xStreamBufferReceive( xStreamBuffer, data, 1U, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 1U, received );
    TEST_ASSERT_EQUAL( 1, receiveCallbackInvoked );
    TEST_ASSERT_EQUAL( 0, receiveCallbackInvokedFromISR );
    TEST_ASSERT_EQUAL( 2, defaultCallbackInvoked );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Tests receive completed callback is invoked from an ISR receiving atleast 1 bytes
 * from the streambuffer.
 */
void test_xStreamBufferReceiveFromISR_CallbackInvoked( void )
{
    size_t sent = 0, received = 0;
    uint8_t data[ TEST_STREAM_BUFFER_TRIGGER_LEVEL ] = { 0xFF };
    BaseType_t highPriorityTaskWoken = pdFALSE;

    xStreamBuffer = xStreamBufferCreateWithCallback( TEST_STREAM_BUFFER_SIZE,
                                                     TEST_STREAM_BUFFER_TRIGGER_LEVEL,
                                                     NULL,
                                                     receiveCompletedStub );

    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( NULL );

    /* Send upto trigger level bytes in stream buffer. */
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, sent );

    /* Receive one byte of data from ISR should invoke the receive completed callback. */
    received = xStreamBufferReceiveFromISR( xStreamBuffer, data, 1U, &highPriorityTaskWoken );
    TEST_ASSERT_EQUAL( 1U, received );
    TEST_ASSERT_EQUAL( 0, receiveCallbackInvoked );
    TEST_ASSERT_EQUAL( 1, receiveCallbackInvokedFromISR );
    TEST_ASSERT_EQUAL( pdTRUE, highPriorityTaskWoken );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Tests receive completed callback is not invoked if zero bytes are received from an ISR.
 */
void test_xStreamBufferReceiveFromISR_CallbackNotInvoked( void )
{
    size_t received = 0;
    uint8_t data[ TEST_STREAM_BUFFER_TRIGGER_LEVEL ] = { 0xFF };
    BaseType_t highPriorityTaskWoken = pdFALSE;

    xStreamBuffer = xStreamBufferCreateWithCallback( TEST_STREAM_BUFFER_SIZE,
                                                     TEST_STREAM_BUFFER_TRIGGER_LEVEL,
                                                     NULL,
                                                     receiveCompletedStub );

    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    /* Receive zero bytes should not invoke the receive completed callback. */
    received = xStreamBufferReceiveFromISR( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL, &highPriorityTaskWoken );
    TEST_ASSERT_EQUAL( 0U, received );
    TEST_ASSERT_EQUAL( 0, receiveCallbackInvoked );
    TEST_ASSERT_EQUAL( 0, receiveCallbackInvokedFromISR );
    TEST_ASSERT_EQUAL( 0, defaultCallbackInvoked );
    TEST_ASSERT_EQUAL( pdFALSE, highPriorityTaskWoken );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Tests default completed callback is invoked from an ISR receiving atleast 1 bytes
 * from the streambuffer and user receive callback is NULL.
 */
void test_xStreamBufferReceiveFromISR_DefaultCallbackInvoked( void )
{
    size_t sent = 0, received = 0;
    uint8_t data[ TEST_STREAM_BUFFER_TRIGGER_LEVEL ] = { 0xFF };
    BaseType_t highPriorityTaskWoken = pdFALSE;

    xStreamBuffer = xStreamBufferCreateWithCallback( TEST_STREAM_BUFFER_SIZE,
                                                     TEST_STREAM_BUFFER_TRIGGER_LEVEL,
                                                     NULL,
                                                     NULL );

    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    validate_stream_buffer_init_state( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( NULL );

    /* Send upto trigger level bytes in stream buffer. */
    sent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, sent );
    TEST_ASSERT_EQUAL( 1, sendCallbackInvoked );
    TEST_ASSERT_EQUAL( 1, defaultCallbackInvoked );

    /* Receive one byte of data from ISR should invoke the receive completed callback. */
    received = xStreamBufferReceiveFromISR( xStreamBuffer, data, 1U, &highPriorityTaskWoken );
    TEST_ASSERT_EQUAL( 1U, received );
    TEST_ASSERT_EQUAL( 0, receiveCallbackInvoked );
    TEST_ASSERT_EQUAL( 1, receiveCallbackInvokedFromISR );
    TEST_ASSERT_EQUAL( 2, defaultCallbackInvoked );
    TEST_ASSERT_EQUAL( pdTRUE, highPriorityTaskWoken );

    vStreamBufferDelete( xStreamBuffer );
}

/**
 * @brief Tests both send and receive callbacks are retained after a streambuffer
 * reset.
 */
void test_xStreamBufferReset_CallbackRetained( void )
{
    StaticStreamBuffer_t * pxStreamBufferStruct;
    BaseType_t xStatus = pdFAIL;

    xStreamBuffer = xStreamBufferCreateWithCallback( TEST_STREAM_BUFFER_SIZE,
                                                     TEST_STREAM_BUFFER_TRIGGER_LEVEL,
                                                     sendCompletedStub,
                                                     receiveCompletedStub );
    TEST_ASSERT_NOT_EQUAL( NULL, xStreamBuffer );

    /* Verify internal memory allocated is equal to size of the struct + buffer size + 1. */
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE + 1U + sizeof( StaticStreamBuffer_t ), dynamicMemoryAllocated );

    /* Verify the fields within stream buffer struct for send and receive completed stubs */
    pxStreamBufferStruct = ( StaticStreamBuffer_t * ) ( xStreamBuffer );
    TEST_ASSERT_EQUAL( sendCompletedStub, pxStreamBufferStruct->pvDummy5[ 0 ] );
    TEST_ASSERT_EQUAL( receiveCompletedStub, pxStreamBufferStruct->pvDummy5[ 1 ] );

    /* Reset Stream buffer */
    xStatus = xStreamBufferReset( xStreamBuffer );
    TEST_ASSERT_EQUAL( pdPASS, xStatus );

    /* Verify that the send and receive completed callbacks are retained after reset. */
    TEST_ASSERT_EQUAL( sendCompletedStub, pxStreamBufferStruct->pvDummy5[ 0 ] );
    TEST_ASSERT_EQUAL( receiveCompletedStub, pxStreamBufferStruct->pvDummy5[ 1 ] );

    vStreamBufferDelete( xStreamBuffer );
}
