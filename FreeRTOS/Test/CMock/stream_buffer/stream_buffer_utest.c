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

static int senderTaskWoken = 0;

static int receiverTaskWoken = 0;

static TaskHandle_t senderTask = ( TaskHandle_t ) ( 0xDEADBEEF );

static TaskHandle_t receiverTask = ( TaskHandle_t ) ( 0xDEADC0DE );

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
    BaseType_t senderTaskWokenFromISR = pdFALSE;

    /* Receive enough bytes (full size) from stream buffer to wake up sender task. */
    if( fromISR == pdTRUE )
    {
        dataReceived = xStreamBufferReceiveFromISR( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, &senderTaskWokenFromISR );
        TEST_ASSERT_EQUAL( pdTRUE, senderTaskWokenFromISR );
    }
    else
    {
        dataReceived = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, 0 );
    }
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, dataReceived );
    return pdTRUE;
}

static BaseType_t resetWhenBlockedCallback( UBaseType_t uxIndexToWaitOn,
                     uint32_t ulBitsToClearOnEntry,
                     uint32_t ulBitsToClearOnExit,
                     uint32_t* pulNotificationValue,
                     TickType_t xTicksToWait,
                     int cmock_num_calls )
{
    BaseType_t status;
    status = xStreamBufferReset( xStreamBuffer );
    TEST_ASSERT_EQUAL( pdFAIL, status );
    return pdTRUE;
}

static BaseType_t sendCompleteWhenBlockedCallback( UBaseType_t uxIndexToWaitOn,
                     uint32_t ulBitsToClearOnEntry,
                     uint32_t ulBitsToClearOnExit,
                     uint32_t* pulNotificationValue,
                     TickType_t xTicksToWait,
                     int cmock_num_calls )
{
    BaseType_t status = pdFALSE, highPriorityTaskWoken = pdFALSE;
    status = xStreamBufferSendCompletedFromISR( xStreamBuffer, &highPriorityTaskWoken );
    TEST_ASSERT_EQUAL( pdTRUE, status );
    TEST_ASSERT_EQUAL( pdTRUE, highPriorityTaskWoken );
    return pdTRUE;
}

static BaseType_t receiveCompleteWhenBlockedCallback( UBaseType_t uxIndexToWaitOn,
                     uint32_t ulBitsToClearOnEntry,
                     uint32_t ulBitsToClearOnExit,
                     uint32_t* pulNotificationValue,
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
                            uint32_t* pulPreviousNotificationValue,
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
                    uint32_t* pulPreviousNotificationValue,
                    BaseType_t* pxHigherPriorityTaskWoken,
                    int cmock_num_calls)
{
    TEST_ASSERT_EQUAL( senderTask, xTaskToNotify );
    senderTaskWoken++;
    *pxHigherPriorityTaskWoken = pdTRUE;
     
    return pdTRUE;
}

static BaseType_t receiverTaskNotifyWaitCallback( UBaseType_t uxIndexToWaitOn,
                     uint32_t ulBitsToClearOnEntry,
                     uint32_t ulBitsToClearOnExit,
                     uint32_t* pulNotificationValue,
                     TickType_t xTicksToWait,
                     int cmock_num_calls )
{

    uint8_t data[ TEST_STREAM_BUFFER_TRIGGER_LEVEL ] = { 0 };
    size_t dataSent = 0;
    BaseType_t receiverTaskWokenFromISR = pdFALSE;

    /* Send enough (trigger level) bytes to stream buffer to wake up receiver Task. */
    if( fromISR == pdTRUE )
    {
        dataSent = xStreamBufferSendFromISR( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL, &receiverTaskWokenFromISR );
        TEST_ASSERT_EQUAL( pdTRUE, receiverTaskWokenFromISR );
    }
    else
    {
        dataSent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_TRIGGER_LEVEL, 0 );
    }
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, dataSent );

    return pdTRUE;
}

static BaseType_t receiverTaskNotificationFromISRCallback( TaskHandle_t xTaskToNotify,
                    UBaseType_t uxIndexToNotify,
                    uint32_t ulValue,
                    eNotifyAction eAction,
                    uint32_t* pulPreviousNotificationValue,
                    BaseType_t* pxHigherPriorityTaskWoken,
                    int cmock_num_calls)
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
                            uint32_t* pulPreviousNotificationValue,
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
void test_xStreamBufferCreate_invalid_triggerlevel( void )
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

    xStreamBuffer = xStreamBufferCreateStatic( sizeof( streamBufferArray ), TEST_STREAM_BUFFER_TRIGGER_LEVEL, streamBufferArray, &streamBufferStruct );
 
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    validate_stream_buffer_empty( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    vStreamBufferDelete( xStreamBuffer );
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
void test_xStreamBufferCreateStatic_invalid_triggerlevel( void )
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
void test_xStreamBufferSend_success( void )
{
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
    TEST_ASSERT_EQUAL( pdFALSE, xStreamBufferIsEmpty(xStreamBuffer) );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that sending more than total size will cap the data to total size without blocking.
 */
void test_xStreamBufferSend_max_size_non_blocking( void )
{
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
void test_xStreamBufferSend_partial( void )
{
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
void test_xStreamBufferSend_blocking( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ]  = { 0 };
    size_t dataSent = 0;

    vTaskSetTimeOutState_Ignore();
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( senderTask );
    xTaskGenericNotifyWait_StubWithCallback( senderTaskNotifyWaitCallback );
    xTaskGenericNotify_StubWithCallback( senderTaskNotificationCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Sending data of sample space should not block the task */
    dataSent = xStreamBufferSend( xStreamBuffer,  data, TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, dataSent );
    TEST_ASSERT_EQUAL( 0,  xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* 
     * Sending data of sample size again should block the task and then send the data once the sample size is consumed
     * from the buffer and a notification sent from the receiver.
     */
    dataSent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, dataSent );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE,  xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 1, senderTaskWoken );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that stream buffer does not block for send if zero wait tick is passed.
 */
void test_xStreamBufferSend_zero_wait_ticks( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ]  = { 0 };
    size_t dataSent = 0;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Sending data of sample space should not block the task */
    dataSent = xStreamBufferSend( xStreamBuffer,  data, TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, dataSent );
    TEST_ASSERT_EQUAL( 0,  xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* 
     * Sending data of sample size again with zero wait ticks should not block but return no bytes sent.
     */
    dataSent = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE, 0 );
    TEST_ASSERT_EQUAL( 0, dataSent );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that stream buffer is able to receive upto available data without blocking.
 */
void test_xStreamBufferReceive_success( void )
{
    uint32_t dataToSend = 0xFF, dataReceived = 0x00;
    size_t sentBytes = 0, receivedBytes = 0;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
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
 * @brief Validates that stream buffer with not enough data requested will return upto data available without blocking.
 */
void test_xStreamBufferReceive_partial( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ]  = { 0xAA };
    uint8_t dataReceived[ TEST_STREAM_BUFFER_SIZE ]  = { 0x00 };
    size_t sentBytes = 0, receivedBytes  = 0;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Send one less than max stream size to the stream buffer. */
    sentBytes = xStreamBufferSend( xStreamBuffer,  data, TEST_STREAM_BUFFER_SIZE - 1, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE - 1, sentBytes );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE - 1,  xStreamBufferBytesAvailable( xStreamBuffer ) );

    /* Try to receive maximum stream size from the stream buffer */
    receivedBytes = xStreamBufferReceive( xStreamBuffer,  dataReceived, TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( receivedBytes, TEST_STREAM_BUFFER_SIZE - 1 );
    TEST_ASSERT_EQUAL_HEX8_ARRAY( data, dataReceived, receivedBytes );
    TEST_ASSERT_EQUAL( 0,  xStreamBufferBytesAvailable( xStreamBuffer ) );

    vStreamBufferDelete(xStreamBuffer);
}


/**
 * @brief Validates that stream buffer with no data will block untill bytes upto trigger level
 * bytes is available and then returns the available bytes.
 */
void test_xStreamBufferReceive_blocking( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ]  = { 0xAA };
    size_t receivedBytes  = 0;

    vTaskSetTimeOutState_Ignore();
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( receiverTask );
    xTaskGenericNotifyWait_StubWithCallback( receiverTaskNotifyWaitCallback );
    xTaskGenericNotify_StubWithCallback( receiverTaskNotificationCallback );

    xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* 
     * Try to receive from an empty buffer. Task will block until trigger level bytes are added to the buffer
     *  and a notification is sent to the receiver.
     */
    receivedBytes = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( receivedBytes, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_EQUAL( 0,  xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 1, receiverTaskWoken );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that stream buffer does not block for receive if zero wait tick is passed.
 */
void test_xStreamBufferReceive_zero_wait_ticks( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ]  = { 0xAA };
    size_t receivedBytes  = 0;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Passing zero wait ticks causes a non-blocking receive. */
    receivedBytes = xStreamBufferReceive( xStreamBuffer,  data, TEST_STREAM_BUFFER_SIZE , 0 );
    TEST_ASSERT_EQUAL( 0, receivedBytes );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that an interrupt service routine is able to read upto requested data from stream
 * buffer without blocking.
 */
void test_xStreamBufferReceiveFromISR_success( void )
{
    uint8_t dataToSend[ TEST_STREAM_BUFFER_SIZE ]  = { 0xAA };
    uint8_t dataReceived[ TEST_STREAM_BUFFER_SIZE ] = { 0x00 };
    size_t receivedBytes  = 0, sentBytes = 0;
    BaseType_t xHighPriorityTaskWoken = pdFALSE;

     vTaskSetTimeOutState_Ignore();
     vTaskSuspendAll_Ignore();
     xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Send data to the stream buffer. */
    sentBytes = xStreamBufferSend( xStreamBuffer,  dataToSend, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sentBytes );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE,  xStreamBufferBytesAvailable( xStreamBuffer ) );

    /* Receive the same data from stream Buffer from an interrupt service routine. No tasks should be woken up. */
    receivedBytes = xStreamBufferReceiveFromISR( xStreamBuffer,  &dataReceived, TEST_STREAM_BUFFER_SIZE , &xHighPriorityTaskWoken );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, receivedBytes );
    TEST_ASSERT_EQUAL_HEX8_ARRAY( dataToSend, dataReceived, TEST_STREAM_BUFFER_SIZE );
    TEST_ASSERT_EQUAL( 0,  xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( pdFALSE, xHighPriorityTaskWoken );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that an interrupt service routine receives only partial data what is available
 * without blocking.
 */
void test_xStreamBufferReceiveFromISR_partial( void )
{
    uint8_t dataToSend[ TEST_STREAM_BUFFER_SIZE - 1U ]  = { 0xAA };
    uint8_t dataReceived[ TEST_STREAM_BUFFER_SIZE ] = { 0x00 };
    size_t receivedBytes  = 0, sentBytes = 0;
    BaseType_t xHighPriorityTaskWoken = pdFALSE;

     vTaskSetTimeOutState_Ignore();
     vTaskSuspendAll_Ignore();
     xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Send partial data to the stream buffer. */
    sentBytes = xStreamBufferSend( xStreamBuffer,  dataToSend, TEST_STREAM_BUFFER_SIZE - 1U, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE - 1U, sentBytes );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE - 1U,  xStreamBufferBytesAvailable( xStreamBuffer ) );

    /* 
     * Try to read full data from stream Buffer from an interrupt service routine.
     * Only partial data what is available should be returned. No tasks should be woken up.
     */
    receivedBytes = xStreamBufferReceiveFromISR( xStreamBuffer,  &dataReceived, TEST_STREAM_BUFFER_SIZE , &xHighPriorityTaskWoken );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE - 1U, receivedBytes );
    TEST_ASSERT_EQUAL_HEX8_ARRAY( dataToSend, dataReceived, TEST_STREAM_BUFFER_SIZE - 1U );
    TEST_ASSERT_EQUAL( 0,  xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( pdFALSE, xHighPriorityTaskWoken );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that an receiving data from an interrupt service routine wakes up a higher priority sender task which is
 * blocked on writing to stream buffer.
 */
void test_xStreamBufferReceiveFromISR_sender_task_wakeup( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ]  = { 0xAA };
    size_t sentBytes = 0;

    fromISR = pdTRUE;

     vTaskSetTimeOutState_Ignore();
     xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
     xTaskGetCurrentTaskHandle_IgnoreAndReturn( senderTask );
     xTaskGenericNotifyWait_StubWithCallback( senderTaskNotifyWaitCallback );
     xTaskGenericNotifyFromISR_StubWithCallback( senderTaskNotificationFromISRCallback );
     xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
     vTaskSuspendAll_Ignore();
     xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Send full data to an empty stream buffer should succeed without blocking. */
    sentBytes = xStreamBufferSend( xStreamBuffer,  data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sentBytes );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE,  xStreamBufferBytesAvailable( xStreamBuffer ) );

    /* Sending full data again to the stream buffer should block untill the existing data is read from an interrupt service routine. */
    sentBytes = xStreamBufferSend( xStreamBuffer,  data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sentBytes );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE,  xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 1, senderTaskWoken );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that an interrupt service routine is able to send data upto the size of stream buffer without blocking.
 */
void test_xStreamBufferSendFromISR_success( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ]  = { 0xAA };
    size_t sentBytes = 0;
    BaseType_t xHighPriorityTaskWoken = pdFALSE;

     vTaskSetTimeOutState_Ignore();
     vTaskSuspendAll_Ignore();
     xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Send full data to the empty stream buffer. This should not block and should not wake up any receiver tasks. */
    sentBytes = xStreamBufferSendFromISR( xStreamBuffer,  data, TEST_STREAM_BUFFER_SIZE, &xHighPriorityTaskWoken );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sentBytes );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE,  xStreamBufferBytesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( pdFALSE, xHighPriorityTaskWoken );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that an interrupt service routine receives only partial data what is available
 * without blocking.
 */
void test_xStreamBufferSendFromISR_partial( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ]  = { 0xAA };
    size_t sentBytes = 0;
    BaseType_t xHighPriorityTaskWoken = pdFALSE;

     vTaskSetTimeOutState_Ignore();
     vTaskSuspendAll_Ignore();
     xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Send partial data to the stream buffer. */
    sentBytes = xStreamBufferSendFromISR( xStreamBuffer,  data, TEST_STREAM_BUFFER_SIZE - 1U, &xHighPriorityTaskWoken );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE - 1U, sentBytes );
    TEST_ASSERT_EQUAL( 1U,  xStreamBufferSpacesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( pdFALSE, xHighPriorityTaskWoken );


    /* Try to send full data again to the stream buffer. Streambuffer should only accept size equal to buffer space available. */
    sentBytes = xStreamBufferSendFromISR( xStreamBuffer,  data, TEST_STREAM_BUFFER_SIZE, &xHighPriorityTaskWoken );
    TEST_ASSERT_EQUAL(  1U, sentBytes );
    TEST_ASSERT_EQUAL( 0,  xStreamBufferSpacesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( pdFALSE, xHighPriorityTaskWoken );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that task waiting to receiving data from stream buffer is woken up by an interrupt service routine which
 * sends trigger level bytes to stream buffer.
 */
void test_xStreamBufferSendFromISR_receiver_task_wakeup( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ]  = { 0x00 };
    size_t receiveBytes = 0;

    fromISR = pdTRUE;

     vTaskSetTimeOutState_Ignore();
     xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
     xTaskGetCurrentTaskHandle_IgnoreAndReturn( receiverTask );
     xTaskGenericNotifyWait_StubWithCallback( receiverTaskNotifyWaitCallback );
     xTaskGenericNotifyFromISR_StubWithCallback( receiverTaskNotificationFromISRCallback );
     xTaskCheckForTimeOut_IgnoreAndReturn( pdFALSE );
     vTaskSuspendAll_Ignore();
     xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Send full data to an empty stream buffer should succeed without blocking. */
    receiveBytes = xStreamBufferReceive( xStreamBuffer,  data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_TRIGGER_LEVEL, receiveBytes );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE,  xStreamBufferSpacesAvailable( xStreamBuffer ) );
    TEST_ASSERT_EQUAL( 1, receiverTaskWoken );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates user is able to reset the stream buffer back to empty state.
 */
void test_xStreamBufferReset_success( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ]  = { 0 };
    size_t dataSent = 0;
    BaseType_t status = pdFALSE;

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of the default test sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );

    /* Validate stream buffer is empty initially. */
    validate_stream_buffer_empty( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    /* Send maximum size of data to stream buffer. */
    dataSent = xStreamBufferSend( xStreamBuffer, data, sizeof(data), TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, dataSent );

    /* Verify that all bytes are available. */
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferBytesAvailable(xStreamBuffer));

    /* Reset the stream buffer back to empty state. */
    status = xStreamBufferReset( xStreamBuffer );
    TEST_ASSERT_EQUAL( pdTRUE, status );


     /* Validate that stream buffer is empty. */
    validate_stream_buffer_empty( xStreamBuffer, TEST_STREAM_BUFFER_SIZE );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that stream buffer reset fails if a sender or receiver task is blocked on it.
 */
void test_xStreamBufferReset_while_blocked( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ]  = { 0xAA };
    size_t sentBytes = 0, receivedBytes  = 0;

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
    receivedBytes = xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 0, receivedBytes );

    /* 
     * Send full size data to stream buffer.
     */
    sentBytes = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sentBytes );
    TEST_ASSERT_EQUAL( pdTRUE, xStreamBufferIsFull( xStreamBuffer ));
    
    /* 
     * Sending data again to a full stream buffer should cause task to be blocked. Reset stream buffer within sender task notify
     * wait callback should fail.
     */
    sentBytes = xStreamBufferSend( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 0, sentBytes );


    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that a receiver task is able to receive data after lowering the stream buffer trigger level.
 */
void test_xStreamBufferSetTrigerLevel_change_triggerlevel( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ]  = { 0xAA };
    BaseType_t status;

    vTaskSetTimeOutState_Ignore();
    xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
    xTaskGetCurrentTaskHandle_IgnoreAndReturn( receiverTask );
    xTaskGenericNotify_StubWithCallback( receiverTaskNotificationCallback );
    xTaskGenericNotifyWait_StubWithCallback( receiverTaskNotifyWaitCallback );
    xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Initially create stream buffer with trigger level equal to maximum stream buffer size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_SIZE );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );

    /* 
     * Perform receive operation on the empty stream buffer. Even if TEST_STREAM_BUFFER_TRIGGER_LEVEL bytes are sent to
     * stream buffer in notify wait operation, receiver task should not be waken up.
     */
     ( void ) xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 0, receiverTaskWoken  );

    /* 
     * Lower the trigger level to TEST_STREAM_BUFFER_TRIGGER_LEVEL.
     */
    status = xStreamBufferSetTriggerLevel( xStreamBuffer, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_EQUAL( pdTRUE, status  );
    
    /* 
     * Perform receive operation  again on the empty stream buffer. Since TEST_STREAM_BUFFER_TRIGGER_LEVEL bytes are sent to
     * stream buffer in notify wait operation, receiver task should be waken up.
     */
     ( void ) xStreamBufferReceive( xStreamBuffer, data, TEST_STREAM_BUFFER_SIZE , TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 1, receiverTaskWoken  );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that setting trigger level larger than stream buffer size fails.
 */
void test_xStreamBufferSetTrigerLevel_larger_than_buffer_size( void )
{
    BaseType_t status;

    /* Initially create stream buffer with trigger level equal to maximum stream buffer size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );

    /* Set the trigger level to TEST_STREAM_BUFFER_SIZE + 1. */
    status = xStreamBufferSetTriggerLevel( xStreamBuffer, TEST_STREAM_BUFFER_SIZE + 1 );
    TEST_ASSERT_EQUAL( pdFALSE, status );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates xStreamBufferSendCompletedFromISR returns false if no task is waiting to be unblocked.
 */
void test_xStreamBufferSendCompletedFromISR_no_task_waiting( void )
{
    BaseType_t status = pdFALSE;
    BaseType_t highPriorityTaskWoken = pdFALSE;

    /* Create a stream buffer of the default test sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );

    /* Send maximum size of data to stream buffer. */
    status = xStreamBufferSendCompletedFromISR( xStreamBuffer,  &highPriorityTaskWoken );
    TEST_ASSERT_EQUAL( pdFALSE, status );
    TEST_ASSERT_EQUAL( pdFALSE, highPriorityTaskWoken );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that invoking xStreamBufferSendCompletedFromISR wakes up a receiver task waiting to receive data from
 * an empty stream buffer.
 */
void test_xStreamBufferSendCompletedFromISR_receiver_task_wakeup( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ]  = { 0x00 };
    size_t receiveBytes = 0;

     vTaskSetTimeOutState_Ignore();
     xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
     xTaskGetCurrentTaskHandle_IgnoreAndReturn( receiverTask );
     xTaskGenericNotifyWait_StubWithCallback( sendCompleteWhenBlockedCallback );
     xTaskGenericNotifyFromISR_StubWithCallback( receiverTaskNotificationFromISRCallback );
     xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );
     vTaskSuspendAll_Ignore();
     xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    receiveBytes = xStreamBufferReceive( xStreamBuffer,  data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 0, receiveBytes );
    TEST_ASSERT_EQUAL( 1, receiverTaskWoken );

    vStreamBufferDelete(xStreamBuffer);
}
/**
 * @brief Validates xStreamBufferReceiveCompletedFromISR returns false if no task is waiting to be unblocked.
 */
void test_xStreamBufferReceiveCompletedFromISR_no_task_waiting( void )
{
    BaseType_t status = pdFALSE;
    BaseType_t highPriorityTaskWoken = pdFALSE;

    /* Create a stream buffer of the default test sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );

    /* Send maximum size of data to stream buffer. */
    status = xStreamBufferReceiveCompletedFromISR( xStreamBuffer,  &highPriorityTaskWoken );
    TEST_ASSERT_EQUAL( pdFALSE, status );
    TEST_ASSERT_EQUAL( pdFALSE, highPriorityTaskWoken );

    vStreamBufferDelete(xStreamBuffer);
}

/**
 * @brief Validates that calling  xStreamBufferReceiveCompletedFromISR wakes up a higher priority sender task which is
 * blocked on writing to stream buffer.
 */
void test_xStreamBufferReceiveCompletedFromISR_sender_task_wakeup( void )
{
    uint8_t data[ TEST_STREAM_BUFFER_SIZE ]  = { 0xAA };
    size_t sentBytes = 0;

     vTaskSetTimeOutState_Ignore();
     xTaskGenericNotifyStateClear_IgnoreAndReturn( pdTRUE );
     xTaskGetCurrentTaskHandle_IgnoreAndReturn( senderTask );
     xTaskGenericNotifyWait_StubWithCallback( receiveCompleteWhenBlockedCallback );
     xTaskGenericNotifyFromISR_StubWithCallback( senderTaskNotificationFromISRCallback );
     xTaskCheckForTimeOut_IgnoreAndReturn( pdTRUE );
     vTaskSuspendAll_Ignore();
     xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    /* Create a stream buffer of sample size. */
    xStreamBuffer = xStreamBufferCreate( TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_TRIGGER_LEVEL );
    TEST_ASSERT_NOT_NULL( xStreamBuffer );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, xStreamBufferSpacesAvailable( xStreamBuffer ) );

    /* Send full data to an empty stream buffer should succeed without blocking. */
    sentBytes = xStreamBufferSend( xStreamBuffer,  data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE, sentBytes );
    TEST_ASSERT_EQUAL( TEST_STREAM_BUFFER_SIZE,  xStreamBufferBytesAvailable( xStreamBuffer ) );

    sentBytes = xStreamBufferSend( xStreamBuffer,  data, TEST_STREAM_BUFFER_SIZE, TEST_STREAM_BUFFER_WAIT_TICKS );
    TEST_ASSERT_EQUAL( 0, sentBytes );
    TEST_ASSERT_EQUAL( 1, senderTaskWoken );

    vStreamBufferDelete(xStreamBuffer);
}

