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
 * Keep it short enough so that they can be allocated on stack for static stream buffer tests.
 */
#define TEST_STREAM_BUFFER_SIZE     ( 64U )

/**
 * @brief Sample trigger level in bytes used for stream buffer tests.
 */
#define TEST_STREAM_BUFFER_TRIGGER_LEVEL   ( 32U )

/**
 * @brief Maximum unsigned long value so as to trigger an integer overflow.
 */
#define TEST_STREAM_BUFFER_MAX_UINT_SIZE    (  ~ ( size_t ) ( 0UL ) )


/**
 * @brief Ticks to wait from tests if the stream buffer is full while sending data or
 * below trigger level while receiveing data.
 */
#define TEST_STREAM_BUFFER_WAIT_TICKS       (   1000U )

/* ============================  GLOBAL VARIABLES =========================== */

static int assertionFailed = 0;

TaskHandle_t senderTask;

StreamBufferHandle_t xStreamBuffer;

/* ==========================  CALLBACK FUNCTIONS =========================== */

void * pvPortMalloc( size_t xSize )
{
    return unity_malloc( xSize );
}
void vPortFree( void * pv )
{
    return unity_free( pv );
}

static void vFakeAssertStub( bool x, char* file, int line, int cmock_num_calls )
{
    if( !x )
    {
        assertionFailed++;
        TEST_ABORT();
    }
}

static BaseType_t senderTaskNotifyWaitCallback( UBaseType_t uxIndexToWaitOn,
                     uint32_t ulBitsToClearOnEntry,
                     uint32_t ulBitsToClearOnExit,
                     uint32_t* pulNotificationValue,
                     TickType_t xTicksToWait,
                     int cmock_num_calls )
{

    uint8_t data[ TEST_STREAM_BUFFER_SIZE ] = { 0 };
    size_t dataReceived = 0;

    /* Consume the bytes from stream buffer for sender task to proceed. */
    dataReceived = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, 0 );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, dataReceived );

    return pdTRUE;
}

/*******************************************************************************
 * Unity fixtures
 ******************************************************************************/
void setUp( void )
{
    assertionFailed = 0;
    xStreamBuffer = NULL;
    vFakeAssert_StubWithCallback(vFakeAssertStub);
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

static void validate_stream_buffer_empty( StreamBufferHandle_t xStreamBuffer, size_t bufferSize )
{
    TEST_ASSERT_TRUE( xStreamBufferIsEmpty( xStreamBuffer ) );
    TEST_ASSERT_FALSE( xStreamBufferIsFull( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( bufferSize, xStreamBufferSpacesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 0U, xStreamBufferBytesAvailable( xStreamBuffer ) );
}

static void validate_and_clear_assertitions( int numExpectedAssertions )
{
    TEST_ASSERT_EQUAL( numExpectedAssertions, assertionFailed );
    assertionFailed = 0;
}

/* ==============================  Test Cases  ============================== */

/**
 * @brief Validates that stream buffer of sane size is created.
 */
void test_xStreamBufferCreate_success( void )
{
    StreamBufferHandle_t xStreamBuffer = NULL;

    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_EQUAL( NULL, xStreamBuffer );
    validate_stream_buffer_empty( xStreamBuffer,  TEST_STREAM_BUFFER_SIZE );
    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Asserts stream buffer creation fails if buffer size integer overflows.
 */
void test_xStreamBufferCreate_integer_overflow( void )
{
    StreamBufferHandle_t xStreamBuffer = NULL;

    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_MAX_UINT_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_EQUAL( NULL, xStreamBuffer );
}

/**
 * @brief Asserts stream buffer creation fails if malloc fails.
 */
void test_xStreamBufferCreate_malloc_failure( void )
{
    StreamBufferHandle_t xStreamBuffer = NULL;

    UnityMalloc_MakeMallocFailAfterCount(0);

    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_EQUAL( NULL, xStreamBuffer );
}

/**
 * @brief Asserts stream buffer creation fails with an assertion failure if zero length size is passed.
 */
void test_xStreamBufferCreate_zero_length_buffer( void )
{ 
    if( TEST_PROTECT() )
    {
        ( void ) xStreamBufferCreate( 0, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    }

    validate_and_clear_assertitions( 1 );
}

/**
 * @brief Asserts stream buffer creation fails with an assertion failure if trigger level is greater than buffer size.
 */
void test_xStreamBufferCreate_triggerlevel_greater_than_buffersize( void )
{ 
    if( TEST_PROTECT() )
    {
        ( void ) xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, ( TEST_STREAM_BUFFER_SIZE + 1 ) );
    }
    
    validate_and_clear_assertitions( 1 );
}

/**
 * @brief Validates stream buffer creation through a static buffer allocated by the user.
 */
void test_xStreamBufferCreateStatic_success( void )
{
    StaticStreamBuffer_t streamBufferStruct = { 0 };
    /* The size of stream buffer array should be one greater than the required size of stream buffer. */
    uint8_t streamBufferArray[ TEST_STREAM_BUFFER_SIZE + 1 ] = { 0 };
    StreamBufferHandle_t streamBuffer = NULL;

    streamBuffer = xStreamBufferCreateStatic( sizeof( streamBufferArray ), TEST_STREAM_BUFFER_TRIGGER_LEVEL, streamBufferArray, &streamBufferStruct );
 
    TEST_ASSERT_NOT_NULL( streamBuffer );
    validate_stream_buffer_empty( streamBuffer, TEST_STREAM_BUFFER_SIZE );

    vStreamBufferDelete( streamBuffer );
}

/**
 * @brief Validates stream buffer creation fails and returns a null pointer if a null array is passed.
 */
void test_xStreamBufferCreateStatic_null_array( void )
{
    StaticStreamBuffer_t streamBufferStruct = { 0 };
    /* The size of stream buffer array should be one greater than the required size of stream buffer. */
    uint8_t streamBufferArray[ TEST_STREAM_BUFFER_SIZE + 1 ] = { 0 };
    StreamBufferHandle_t streamBuffer = NULL;
    
    streamBuffer = xStreamBufferCreateStatic( sizeof( streamBufferArray ), TEST_STREAM_BUFFER_TRIGGER_LEVEL, NULL, &streamBufferStruct );

    TEST_ASSERT_NULL( streamBuffer );
}

/**
 * @brief Validates stream buffer creation fails and returns a null pointer if a null struct is passed.
 */
void test_xStreamBufferCreateStatic_null_struct( void )
{
    /* The size of stream buffer array should be one greater than the required size of stream buffer. */
    uint8_t streamBufferArray[ TEST_STREAM_BUFFER_SIZE + 1 ] = { 0 };
    StreamBufferHandle_t streamBuffer = NULL;
    
    streamBuffer = xStreamBufferCreateStatic( sizeof( streamBufferArray ), TEST_STREAM_BUFFER_TRIGGER_LEVEL, streamBufferArray, NULL );
 
    TEST_ASSERT_NULL( streamBuffer );
}

/**
 * @brief Validates stream buffer creation fails with assertition if trigger level is higher than buffer size
 */
void test_xStreamBufferCreateStatic_triggerlevel_greater_than_buffersize( void )
{
    StaticStreamBuffer_t streamBufferStruct = { 0 };

    /* The size of stream buffer array should be one greater than the required size of stream buffer. */
    uint8_t streamBufferArray[ TEST_STREAM_BUFFER_SIZE + 1 ] = { 0 };

    if( TEST_PROTECT() )
    {
        ( void ) xStreamBufferCreateStatic( sizeof( streamBufferArray ), TEST_STREAM_BUFFER_SIZE + 2, streamBufferArray, &streamBufferStruct );
    }
 
    validate_and_clear_assertitions( 1 );
}

/**
 * @brief Validates a task is able to send upto buffer space available without blocking.
 */
void test_xStreamBufferSend_send_without_blocking( void )
{
    StreamBufferHandle_t xStreamBuffer = NULL;
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ]  = { 0 };
    size_t dataSent = 0;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of the default test sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Sending bytes of size  upto to available size should succeed. Sender task should not be in blocked state. */
    dataSent = xStreamBufferSend( xStreamBuffer, data, sizeof(data), TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( sizeof(data), dataSent );
    TEST_ASSERT_EQUAL( sizeof(data), xStreamBufferBytesAvailable(xStreamBuffer));

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that sending more than total size will cap the data to total size without blocking.
 */
void test_xStreamBufferSend_send_more_than_total_size( void )
{
    StreamBufferHandle_t xStreamBuffer = NULL;
    uint8_t data[ TEST_STREAM_BUFFER_SIZE + 1 ]  = { 0 };
    size_t dataSent = 0;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of the default test sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Sending bytes beyond the total size caps the length to total size. */
    dataSent = xStreamBufferSend( xStreamBuffer, data, sizeof(data), TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, dataSent );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE,  xStreamBufferBytesAvailable( xStreamBuffer ) );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that sending more than available size, will return by sending upto available size,
 *  after timeout, blocking for a given wait period.
 */
void test_xStreamBufferSend_send_partial_data_after_timeout( void )
{
    StreamBufferHandle_t xStreamBuffer = NULL;
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ]  = { 0 };
    size_t dataSent = 0;

    vTaskSetTimeOutState_Ignore();
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( senderTask );
    xTaskGenericNotifyWait_ExpectAndReturn( 0, 0, 0, NULL, TEST_STREAM_BUFFER_WAIT_TICKS, pdTRUE );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of test sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Sending data upto available space should not block the task */
    dataSent = xStreamBufferSend( xStreamBuffer,  data, TEST_STREAM_BUFFER_SIZE - 1 , TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE - 1, dataSent );
    TEST_ASSERT_EQUAL( 1,  xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Sending bytes beyond the available size should cause the task to block by calling xTaskGenericNotifyWait() API and 
     * then return with partial data after timeout.
     */
    dataSent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 1, dataSent );
    TEST_ASSERT_EQUAL( pdTRUE, xStreamBufferIsFull( xStreamBuffer ));
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE,  xStreamBufferBytesAvailable( xStreamBuffer ) );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that stream buffer blocks and then sends the remaining data only when bytes are read from the buffer.
 */
void test_xStreamBufferSend_send_data_with_blocking( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ]  = { 0 };
    size_t dataSent = 0;

    vTaskSetTimeOutState_Ignore();
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( senderTask );
    xTaskGenericNotifyWait_StubWithCallback( senderTaskNotifyWaitCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of the test sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Sending data of sample space should not block the task */
    dataSent = xStreamBufferSend( xStreamBuffer,  data, TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, dataSent );
    TEST_ASSERT_EQUAL( 0,  xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* 
     * Sending data of sample size again should block the task and then send the data once the sample size is consumed
     * from the buffer.
     */
    dataSent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, dataSent );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE,  xStreamBufferBytesAvailable( xStreamBuffer ) );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that stream buffer is able to receive upto available data without blocking.
 */
void test_xStreamBufferReceive_receive_data_without_blocking( void )
{
    uint32_t dataToSend = 0xFF, dataReceived = 0x00;
    size_t sentBytes = 0, receivedBytes = 0;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of the test sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Send uint32_t data to the stream buffer. */
    sentBytes = xStreamBufferSend( xStreamBuffer,  &dataToSend, sizeof(dataToSend), TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( sizeof(dataToSend), sentBytes );
    TEST_ASSERT_EQUAL( sizeof(dataToSend),  xStreamBufferBytesAvailable( xStreamBuffer ) );

    /* Receive the same data from stream Buffer without blocking. */
    receivedBytes = xStreamBufferReceive( xStreamBuffer,  &dataReceived, sizeof(dataReceived) , TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( sizeof(dataToSend), receivedBytes );
    TEST_ASSERT_EQUAL( dataToSend, dataReceived );
    TEST_ASSERT_EQUAL( 0,  xStreamBufferBytesAvailable( xStreamBuffer ) );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that stream buffer with not enough data blocks and returns with partial data after timeout.
 */
void test_xStreamBufferReceive_receive_data_blocking( void )
{
    uint32_t dataToSend = 0xFF, dataReceived = 0x00;
    size_t sentBytes = 0, receivedBytes = 0;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of the test sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Send uint32_t data to the stream buffer. */
    sentBytes = xStreamBufferSend( xStreamBuffer,  &dataToSend, sizeof(dataToSend), TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( sizeof(dataToSend), sentBytes );
    TEST_ASSERT_EQUAL( sizeof(dataToSend),  xStreamBufferBytesAvailable( xStreamBuffer ) );

    /* Receive the same data from stream Buffer without blocking. */
    receivedBytes = xStreamBufferReceive( xStreamBuffer,  &dataReceived, sizeof(dataReceived) , TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( sizeof(dataToSend), receivedBytes );
    TEST_ASSERT_EQUAL( dataToSend, dataReceived );
    TEST_ASSERT_EQUAL( 0,  xStreamBufferBytesAvailable( xStreamBuffer ) );

    vStreamBufferDelete(xStreamBuffer);
}