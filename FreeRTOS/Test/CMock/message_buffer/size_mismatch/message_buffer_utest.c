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
 * @brief CException code for when a configASSERT should be intercepted.
 */
#define configASSERT_E    0xAA101

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
/*static TaskHandle_t senderTask = ( TaskHandle_t ) ( 0xAABBCCDD ); */

/**
 * @brief Dummy receiver task handle to which the stream buffer send APIs will send notifications.
 */
/*static TaskHandle_t receiverTask = ( TaskHandle_t ) ( 0xABCDEEFF ); */

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


static void validate_and_clear_assertions( void )
{
    TEST_ASSERT_EQUAL( 1, assertionFailed );
    assertionFailed = 0;
}

/* ==============================  Test Cases  ============================== */


/**
 * @brief assert if xDataLengthBytes does not fit in
 *        configMESSAGE_BUFFER_LENGTH_TYPE.
 *
 */
void test_xMessageBufferSend_size_mismatch( void )
{
    uint8_t message[ UINT8_MAX + 5 + 1 ] = { 0 };

    vTaskSetTimeOutState_Ignore();
    vTaskSuspendAll_Ignore();
    xTaskResumeAll_IgnoreAndReturn( pdTRUE );

    xMessageBuffer = xMessageBufferCreate( UINT8_MAX + 5 );
    /* Create a message buffer of sample size. */
    TEST_ASSERT_NOT_NULL( xMessageBuffer );

    EXPECT_ASSERT_BREAK( ( void ) xMessageBufferSend( xMessageBuffer,
                                                      message,
                                                      UINT8_MAX + 5,
                                                      0 ) );
    vStreamBufferDelete( xMessageBuffer );

    validate_and_clear_assertions();
}
