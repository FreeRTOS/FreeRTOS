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
/*! @file queue_utest_common.h */

#ifndef QUEUE_UTEST_COMMON_H
#define QUEUE_UTEST_COMMON_H

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "CException.h"

/* FreeRTOS includes */
#include "FreeRTOS.h"
#include "queue.h"

/* Mock includes. */
#include "mock_task.h"
#include "mock_fake_assert.h"

/* ================================  CONSTANTS ===============================*/

#define MAX_MULTI_LEN             16
#define MAX_QUEUE_ITEMS           500
#define QUEUE_T_SIZE              sizeof( StaticQueue_t )

#define B_SEMPHR_AVAILABLE        1
#define B_SEMPHR_TAKEN            0

#define INVALID_UINT32            0xFFFFFFFF
#define INVALID_PTR               ( ( void * ) INVALID_UINT32 )

#define configASSERT_E            0xAA101

#define queueUNLOCKED             ( ( int8_t ) -1 )
#define queueLOCKED_UNMODIFIED    ( ( int8_t ) 0 )

#define DEFAULT_PRIORITY          5

#define TICKS_TO_WAIT             10
#define NUM_CALLS_TO_INTERCEPT    TICKS_TO_WAIT / 2

/* ===========================  FUNCTION PROTOTYPES  ======================== */
void setxMaskAssertAndAbort( bool mask );
bool getxMaskAssertAndAbort();
/* ============================  GLOBAL VARIABLES =========================== */

/* =================================  MACROS ================================ */

/**
 * @brief Expect a configASSERT from the function called.
 *  Break out of the called function when this occurs.
 * @details Use this macro when the call passsed in as a parameter is expected
 * to cause invalid memory access.
 */
#define EXPECT_ASSERT_BREAK( call )             \
    do                                          \
    {                                           \
        setxMaskAssertAndAbort( true );         \
        CEXCEPTION_T e = CEXCEPTION_NONE;       \
        Try                                     \
        {                                       \
            call;                               \
            TEST_FAIL();                        \
        }                                       \
        Catch( e )                              \
        TEST_ASSERT_EQUAL( configASSERT_E, e ); \
    } while( 0 )

/* ==========================  CALLBACK FUNCTIONS =========================== */

/**
 * @brief defines malloc() for this test and redirects it to unity_malloc
 * @param xSize size of memory block to be allocated
 * @return pointer to the allocated memory on success.
 * @return NULL if the memory could not be allocated.
 */
void * pvPortMalloc( size_t xSize );

/**
 * @brief defines free() for this test and redirects it to unity_free
 * @param pv pointer to the block to be freed
 */
void vPortFree( void * pv );

/**
 * @brief Callback function for calls to configASSERT
 * @details This callback function will cause a unit test to fail if the
 *          provided assertion is false and the fakeAssertExpectFail()
 *          function was not called prior to the assertion.
 * @param assertion Boolean assertion passed into the configASSERT() macro
 * @param file Name of the file in which the assert occurred
 * @param line Line number of the assertion
 * @param num_calls Number of times configASSERT() was called
 */
void fakeAssertCallback( bool assertion,
                         char * file,
                         int line,
                         int num_calls );

/* ==========================  Unity fixtures =========================== */

/**
 * @brief Setup function called before each test case.
 */
void setUp( void );

/**
 * @brief Teardown function called after each test case.
 */
void tearDown( void );

/**
 * @brief Setup function called before this test suite (file).
 */
void suiteSetUp();

/**
 * @brief Setup function called afer this test suite (file) has completed.
 */
int suiteTearDown( int numFailures );

/* ==========================  Helper functions =========================== */

/**
 * @brief Common test case setup function for queue tests.
 */
void commonSetUp( void );

/**
 * @brief Common test case teardown function for queue tests.
 */
void commonTearDown( void );

/**
 * @brief Common test suite setup function for queue test suites.
 */
void commonSuiteSetUp();

/**
 * @brief Common test suite teardown function for queue test suites.
 */
int commonSuiteTearDown( int numFailures );

/**
 * @brief Get a monotonically increasing test value (somewhat random).
 */
uint32_t getNextMonotonicTestValue();

/**
 * @brief Get the test value provided by the last call to getNextMonotonicTestValue().
 */
uint32_t getLastMonotonicTestValue();

/**
 * @brief Mask subsquent failing assertions until next test case.
 */
void fakeAssertExpectFail( void );

/**
 * @brief Determine if a configASSERT occurred and clear the assertion flag.
 * @return true if an assert occurred since the start of the test suite or
 *  the last call to fakeAssertGetFlagAndClear.
 * @return false if no assert was triggered.
 */
bool fakeAssertGetFlagAndClear( void );

/**
 * @brief get the size of the last heap memory allocation via pvPortMalloc()
 * @return The parameter given during the last call to pvPortMalloc()
 */
size_t getLastMallocSize( void );

/**
 * @brief get the address of the last heap memory deallocation via pvPortFree()
 * @return The parameter given during the last call to pvPortFree()
 */
void * getLastFreedAddress( void );

/**
 * @brief get the number of malloc calls made in the current test case.
 * @return number of malloc calls made since the start of the test case.
 */
size_t getNumberMallocCalls( void );

/**
 * @return A pointer to the given queue's xTasksWaitingToSend event list.
 */
List_t * pxGetTasksWaitingToSendToQueue( QueueHandle_t xQueue );

/**
 * @return A pointer to the given queue's xTasksWaitingToReceive event list.
 */
List_t * pxGetTasksWaitingToReceiveFromQueue( QueueHandle_t xQueue );

/**
 * @return The value of a given queue's cRxLock.
 */
int8_t cGetQueueRxLock( QueueHandle_t xQueue );

/**
 * @return The value of a given queue's cTxLock.
 */
int8_t cGetQueueTxLock( QueueHandle_t xQueue );

/**
 * @brief Set the value of a given queue's cRxLock to the specified value.
 */
void vSetQueueRxLock( QueueHandle_t xQueue,
                      int8_t value );

/**
 * @brief Set the value of a given queue's cTxLock to the specified value.
 */
void vSetQueueTxLock( QueueHandle_t xQueue,
                      int8_t value );

/**
 * @brief Get the number of asserts that have occurred since the last call to this function in a given test case.
 */
BaseType_t fakeAssertGetNumAssertsAndClear( void );

/**
 * @brief Check that the number of failed configASSERTs that have occurred in this test case equals the given number.
 */
void fakeAssertVerifyNumAssertsAndClear( uint32_t ulNumAssertsExpected );

/**
 * @brief Receives a given number of items from the given queue and verifies that the items contain sequential values.
 */
void queue_common_receive_sequential_from_queue( QueueHandle_t xQueue,
                                                 uint32_t maxItems,
                                                 uint32_t numberOfItems,
                                                 uint32_t expectedFirstValue );

/**
 * @brief Adds a given number of itesm to the given queue with sequential values in each item.
 */
void queue_common_add_sequential_to_queue( QueueHandle_t xQueue,
                                           uint32_t numberOfItems );


/**
 * @brief Register the stubs contained in td_port.c using the relevant CMock _Stub calls.
 * @details This function should be called before every test case.
 */
void td_port_register_stubs( void );

/**
 * @brief Validate ending state of td_port related variables.
 * @details This function should be called after every test case.
 * It verifies the state of the variables used by td_port functions and
 * frees resources used by CMock.
 */
void td_port_teardown_check( void );

/**
 * @return pdTRUE if the simulated "port" a critical section/.
 */
BaseType_t td_port_isInCriticalSection( void );

/**
 * @brief Register the stubs contained in td_task.c using the relevant CMock _Stub calls.
 * @details This function should be called before every test case.
 */
void td_task_register_stubs( void );

/**
 * @brief Validate ending state of td_task related variables.
 * @details This function should be called after every test case.
 * It verifies the state of the variables used by td_task functions and
 * frees resources used by CMock.
 */
void td_task_teardown_check( void );

/**
 * @brief Sets the scheduler state used by the task test double.
 */
void td_task_setSchedulerState( BaseType_t state );

/**
 * @brief Sets the priority of the fake / simulated task used by td_task.c.
 */
void td_task_setFakeTaskPriority( TickType_t priority );

/**
 * @brief Sets the priority of the fake / simulated task used by td_task.c.
 */
TickType_t td_task_getFakeTaskPriority( void );

/**
 * @brief Adds the td_task.c fake task to the given queue's WaitingToSend event list.
 */
void td_task_addFakeTaskWaitingToSendToQueue( QueueHandle_t xQueue );

/**
 * @brief Adds the td_task.c fake task to the given queue's WaitingToReceive event list.
 */
void td_task_addFakeTaskWaitingToReceiveFromQueue( QueueHandle_t xQueue );

/**
 * @brief Test double for xTaskCheckForTimeOut
 */
BaseType_t td_task_xTaskCheckForTimeOutStub( TimeOut_t * const pxTimeOut,
                                             TickType_t * const pxTicksToWait,
                                             int cmock_num_calls );

/**
 * @brief Test double for xTaskResumeAll
 */
BaseType_t td_task_xTaskResumeAllStub( int cmock_num_calls );

/**
 * @brief Test double for vTaskSuspendAll which does not check the scheduler state when called.
 */
void td_task_vTaskSuspendAllStubNoCheck( int cmock_num_calls );

/**
 * @brief Test double for vPortYieldWithinAPI
 */
void td_task_vPortYieldWithinAPIStub( int cmock_num_calls );

/**
 * @brief Get the number of calls to all yield related functions.
 */
BaseType_t td_task_getYieldCount( void );

/**
 * @brief Get the number of times vPortYield was called and clear the counter.
 * @return number of times vPortYield was called during the current test case.
 */
BaseType_t td_task_getCount_vPortYield( void );

/**
 * @brief Get the number of times vPortYieldFromISR was called and clear the counter.
 * @return number of times vPortYieldFromISR was called during the current test case.
 */
BaseType_t td_task_getCount_vPortYieldFromISR( void );

/**
 * @brief Get the number of times vPortYieldWithinAPI was called and clear the counter.
 * @return number of times vPortYieldWithinAPI was called during the current test case.
 */
BaseType_t td_task_getCount_vPortYieldWithinAPI( void );

/**
 * @brief Get the number of times vTaskMissedYield was called and clear the counter.
 * @return number of times vTaskMissedYield was called during the current test case.
 */
BaseType_t td_task_getCount_vTaskMissedYield( void );

/**
 * @brief Get the number of times xTaskResumeAll and resulted in a yield.
 * @return number of times xTaskResumeAll was called and resulted in a yield
 * during the current test case. Also clears the counter before returning
 * the previous value.
 */
BaseType_t td_task_getCount_YieldFromTaskResumeAll( void );

/**
 * @brief Get the current state of the xYieldPending variable.
 * @return pdTRUE when a yield is pending due to a call to vTaskMissedYield
 * or xTaskRemoveFromEventList
 */
BaseType_t td_task_getYieldPending( void );


#endif /* QUEUE_UTEST_COMMON_H */
