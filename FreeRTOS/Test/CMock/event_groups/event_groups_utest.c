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
/*! @file list_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>

/* List includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "event_groups.h"

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"

/* Mock includes. */
#include "mock_task.h"
#include "mock_timers.h"
#include "mock_list.h"
#include "mock_list_macros.h"
#include "mock_fake_assert.h"
#include "mock_fake_port.h"


/* ===========================  DEFINES CONSTANTS  ========================== */
#define BIT_0            ( 1 << 0 )
#define BIT_2            ( 1 << 2 )
#define BIT_4            ( 1 << 4 )
#define ALL_SYNC_BITS    ( BIT_0 | BIT_2 | BIT_4 )

/* ===========================  GLOBAL VARIABLES  =========================== */

/**
 * @brief Global message buffer handle used for tests.
 */
static EventGroupHandle_t xEventGroupHandle;
static List_t xListTemp = { 0 };
static List_t * pxListTemp = &xListTemp;
static ListItem_t xListItemDummy = { 0 };
static ListItem_t * pxListItem_HasTaskBlockOnBit0 = &xListItemDummy;

/* ===========================  EXTERN VARIABLES  =========================== */

/* ==========================  CALLBACK FUNCTIONS =========================== */

void * pvPortMalloc( size_t xSize )
{
    return unity_malloc( xSize );
}
void vPortFree( void * pv )
{
    return unity_free( pv );
}

/* ============================  Unity Fixtures  ============================ */
/*! called before each testcase */
void setUp( void )
{
    xEventGroupHandle = NULL;

    pxListTemp->pxIndex = ( ListItem_t * ) &( pxListTemp->xListEnd );
    pxListTemp->xListEnd.xItemValue = portMAX_DELAY;
    pxListTemp->xListEnd.pxNext = ( ListItem_t * ) &( pxListTemp->xListEnd );
    pxListTemp->xListEnd.pxPrevious = ( ListItem_t * ) &( pxListTemp->xListEnd );
    pxListTemp->uxNumberOfItems = ( UBaseType_t ) 0U;

    pxListItem_HasTaskBlockOnBit0->xItemValue = BIT_0;

    vFakeAssert_Ignore();
    vFakePortEnterCriticalSection_Ignore();
    vFakePortExitCriticalSection_Ignore();
    ulFakePortSetInterruptMaskFromISR_IgnoreAndReturn( 0U );
    vFakePortClearInterruptMaskFromISR_Ignore();

    /* Track calls to malloc / free */
    UnityMalloc_StartTest();
}

/*! called after each testcase */
void tearDown( void )
{
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

/* ===========================  Static Functions  =========================== */


/* ==============================  Test Cases  ============================== */

/*!
 * @brief validate dynamically creating and deleting a new RTOS event group,
 * @coverage xEventGroupCreate vEventGroupDelete
 */
void test_xEventGroupDynamicCreateAndDelete_Success( void )
{
    /* Expectation of Function: xEventGroupCreate */
    vListInitialise_Expect( 0 );
    vListInitialise_IgnoreArg_pxList();
    vListInitialise_ReturnThruPtr_pxList( pxListTemp );
    /* Expectation of Function: vEventGroupDelete */
    vTaskSuspendAll_Ignore();
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 1 );
    vTaskRemoveFromUnorderedEventList_Ignore();
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );
    xTaskResumeAll_IgnoreAndReturn( 1 );

    /* API to Test */
    xEventGroupHandle = xEventGroupCreate();
    TEST_ASSERT_NOT_EQUAL( NULL, xEventGroupHandle );

    vEventGroupDelete( xEventGroupHandle );
}


/*!
 * @brief validate dynamically creating a event group failed when malloc failed
 * @coverage xEventGroupCreate
 */
void test_xEventGroupDynamicCreate_FailMalloc( void )
{
    /* Expectation of Function: xEventGroupCreate */
    vListInitialise_Ignore();
    UnityMalloc_MakeMallocFailAfterCount( 0 );

    /* API to Test */
    xEventGroupHandle = xEventGroupCreate();

    /* Validate */
    TEST_ASSERT_EQUAL( NULL, xEventGroupHandle );
}

/*!
 * @brief validate statically creating and deleting a new RTOS event group,
 * @coverage xEventGroupCreateStatic vEventGroupDelete
 */
void test_xEventGroupStaticCreate_Success( void )
{
    /* Expectation of Function: xEventGroupCreateStatic */
    vListInitialise_Ignore();

    /* Expectation of Function: vEventGroupDelete */
    vTaskSuspendAll_Ignore();
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 1 );
    vTaskRemoveFromUnorderedEventList_Ignore();
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );
    xTaskResumeAll_IgnoreAndReturn( 1 );

    /* API to Test */
    StaticEventGroup_t xCreatedEventGroup = { 0 };
    xEventGroupHandle = xEventGroupCreateStatic( &xCreatedEventGroup );

    /* Validate */
    TEST_ASSERT_NOT_EQUAL( NULL, xEventGroupHandle );

    /* Clean */
    vEventGroupDelete( xEventGroupHandle );
}

/*!
 * @brief validate statically creating and deleting a new RTOS event group,
 *
 */
void test_xEventGroupStaticCreate_InvalidInput_Failed( void )
{
    /* Expectation of Function: xEventGroupCreateStatic */
    vListInitialise_Ignore();

    /* API to Test */
    xEventGroupHandle = xEventGroupCreateStatic( NULL );

    /* Validate */
    TEST_ASSERT_EQUAL( NULL, xEventGroupHandle );
}

/*!
 * @brief validate setting event bits when not tasked is blocked by that event bits
 * @coverage xEventGroupSetBits
 */
void test_xEventGroupSetBits_NoTaskBlockedOnBits_Success( void )
{
    /* Expectation of Function: xEventGroupCreate */
    vListInitialise_Expect( 0 );
    vListInitialise_IgnoreArg_pxList();
    vListInitialise_ReturnThruPtr_pxList( pxListTemp );

    /* Expectation of Function: xEventGroupSetBits */
    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    vTaskSuspendAll_Ignore();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    listGET_LIST_ITEM_VALUE_IgnoreAndReturn( 0 );
    xTaskResumeAll_IgnoreAndReturn( 1 );

    /* Set-up */
    EventBits_t uxBits;
    StaticEventGroup_t xCreatedEventGroup = { 0 };
    xEventGroupHandle = xEventGroupCreateStatic( &xCreatedEventGroup );

    /* API to Test */
    uxBits = xEventGroupSetBits( xEventGroupHandle, BIT_0 | BIT_4 );

    /* Validate */
    TEST_ASSERT_EQUAL( ( BIT_0 | BIT_4 ), uxBits & ( BIT_0 | BIT_4 ) );
}

/*!
 * @brief validate setting event bits when some tasks are blocked by that event bits
 * @coverage xEventGroupSetBits
 */
void test_xEventGroupSetBits_WithTaskBlockedOnBits_Success( void )
{
    /* Expectation of Function: xEventGroupCreate */
    vListInitialise_Expect( 0 );
    vListInitialise_IgnoreArg_pxList();
    vListInitialise_ReturnThruPtr_pxList( pxListTemp );

    /* Expectation of Function: xEventGroupSetBits */
    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    vTaskSuspendAll_Ignore();
    listGET_NEXT_ExpectAnyArgsAndReturn( pxListItem_HasTaskBlockOnBit0 );
    listGET_LIST_ITEM_VALUE_IgnoreAndReturn( BIT_0 );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    vTaskRemoveFromUnorderedEventList_Ignore();
    xTaskResumeAll_IgnoreAndReturn( 1 );

    /* Set-up */
    EventBits_t uxBits;
    StaticEventGroup_t xCreatedEventGroup = { 0 };
    xEventGroupHandle = xEventGroupCreateStatic( &xCreatedEventGroup );

    /* API to Test */
    uxBits = xEventGroupSetBits( xEventGroupHandle, BIT_0 );

    /* Validate */
    TEST_ASSERT_EQUAL( ( BIT_0 ), uxBits & ( BIT_0 ) );
}

/*!
 * @brief validate the callback function of setting event bits
 * @coverage vEventGroupSetBitsCallback
 */
void test_vEventGroupSetBitsCallback_Success( void )
{
    /* Expectation of Function: xEventGroupCreate */
    vListInitialise_Expect( 0 );
    vListInitialise_IgnoreArg_pxList();
    vListInitialise_ReturnThruPtr_pxList( pxListTemp );

    /* Expectation of Function: xEventGroupSetBits */
    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    vTaskSuspendAll_Ignore();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    listGET_LIST_ITEM_VALUE_IgnoreAndReturn( 0 );
    xTaskResumeAll_IgnoreAndReturn( 1 );

    /* Set-up */
    EventBits_t uxReturn;
    StaticEventGroup_t xCreatedEventGroup = { 0 };
    xEventGroupHandle = xEventGroupCreateStatic( &xCreatedEventGroup );

    /* API to Test */
    vEventGroupSetBitsCallback( xEventGroupHandle, BIT_0 );
    uxReturn = xEventGroupGetBits( xEventGroupHandle );

    /* Validate: Expect to return and BIT_0 and BIT_2 was set */
    TEST_ASSERT_EQUAL( BIT_0, uxReturn & BIT_0 );
}

/*!
 * @brief validate getting current event bits
 * @coverage xEventGroupGetBits xEventGroupSetBits
 */
void test_xEventGroupGetBits_Success( void )
{
    /* Expectation of Function: xEventGroupCreate */
    vListInitialise_Expect( 0 );
    vListInitialise_IgnoreArg_pxList();
    vListInitialise_ReturnThruPtr_pxList( pxListTemp );

    /* Expectation of Function: xEventGroupSetBits */
    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    vTaskSuspendAll_Ignore();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    listGET_LIST_ITEM_VALUE_IgnoreAndReturn( 0 );
    xTaskResumeAll_IgnoreAndReturn( 1 );

    /* Expectation of Function: "xEventGroupGetBits" --> xEventGroupSetBits( xEventGroup, 0 ) */
    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );

    /* Set-up */
    EventBits_t uxBitsSetVal, uxBitsGetVal;
    StaticEventGroup_t xCreatedEventGroup = { 0 };
    xEventGroupHandle = xEventGroupCreateStatic( &xCreatedEventGroup );

    /* API to Test */
    uxBitsSetVal = xEventGroupSetBits( xEventGroupHandle, BIT_0 | BIT_4 );
    uxBitsGetVal = xEventGroupSetBits( xEventGroupHandle, 0 ); /* See event_groups.h: #define xEventGroupGetBits( xEventGroup ) xEventGroupClearBits( xEventGroup, 0 ) */

    /* Validate */
    TEST_ASSERT_EQUAL( uxBitsSetVal, uxBitsGetVal );
}

/*!
 * @brief validate getting current event bits from ISR
 * @coverage xEventGroupGetBitsFromISR
 */
void test_xEventGroupGetBitsFromISR_Success( void )
{
    /* Expectation of Function: xEventGroupCreate */
    vListInitialise_Expect( 0 );
    vListInitialise_IgnoreArg_pxList();
    vListInitialise_ReturnThruPtr_pxList( pxListTemp );

    /* Set-up */
    EventBits_t uxReturn;
    StaticEventGroup_t xCreatedEventGroup = { 0 };
    xEventGroupHandle = xEventGroupCreateStatic( &xCreatedEventGroup );

    /* API to Test */
    uxReturn = xEventGroupGetBitsFromISR( xEventGroupHandle );

    /* Validate */
    TEST_ASSERT_EQUAL( 0, uxReturn );
}

/*!
 * @brief validate clearing event bits
 * @coverage xEventGroupClearBits
 */
void test_xEventGroupClearBits_Success( void )
{
    /* Expectation of Function: xEventGroupCreate */
    vListInitialise_Expect( 0 );
    vListInitialise_IgnoreArg_pxList();
    vListInitialise_ReturnThruPtr_pxList( pxListTemp );

    /* Expectation of Function: xEventGroupSetBits */
    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    vTaskSuspendAll_Ignore();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    listGET_LIST_ITEM_VALUE_IgnoreAndReturn( 0 );
    xTaskResumeAll_IgnoreAndReturn( 1 );

    /* Set-up */
    EventBits_t uxBitsSetVal, uxBitsGetVal;
    StaticEventGroup_t xCreatedEventGroup = { 0 };
    xEventGroupHandle = xEventGroupCreateStatic( &xCreatedEventGroup );

    /* API to Test */
    uxBitsSetVal = xEventGroupSetBits( xEventGroupHandle, BIT_0 | BIT_4 );
    TEST_ASSERT_EQUAL( ( BIT_0 | BIT_4 ), uxBitsSetVal & ( BIT_0 | BIT_4 ) );
    uxBitsSetVal = xEventGroupClearBits( xEventGroupHandle, BIT_4 );
    uxBitsGetVal = xEventGroupGetBits( xEventGroupHandle );

    /* Validate */
    TEST_ASSERT_EQUAL( uxBitsSetVal, uxBitsGetVal | BIT_4 );
    TEST_ASSERT_EQUAL( 0, uxBitsGetVal & BIT_4 );
}

/*!
 * @brief validate the callback function of clearing event bits
 * @coverage vEventGroupClearBitsCallback
 */
void test_vEventGroupClearBitsCallback_Success( void )
{
    /* Expectation of Function: xEventGroupCreate */
    vListInitialise_Expect( 0 );
    vListInitialise_IgnoreArg_pxList();
    vListInitialise_ReturnThruPtr_pxList( pxListTemp );

    /* Expectation of Function: xEventGroupSetBits */
    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    vTaskSuspendAll_Ignore();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    listGET_LIST_ITEM_VALUE_IgnoreAndReturn( 0 );
    xTaskResumeAll_IgnoreAndReturn( 1 );

    /* Set-up */
    EventBits_t uxReturn;
    StaticEventGroup_t xCreatedEventGroup = { 0 };
    xEventGroupHandle = xEventGroupCreateStatic( &xCreatedEventGroup );
    uxReturn = xEventGroupSetBits( xEventGroupHandle, BIT_0 );

    /* API to Test */
    vEventGroupClearBitsCallback( xEventGroupHandle, BIT_0 );
    uxReturn = xEventGroupGetBits( xEventGroupHandle );

    /* Validate: Expect to return and BIT_0 and BIT_2 was set */
    TEST_ASSERT_EQUAL( 0, uxReturn & BIT_0 );
}

/*!
 * @brief validate waiting on for all bits are set when currently no bits are set. Clear the bit before return.
 * @coverage xEventGroupWaitBits
 */
void test_xEventGroupWaitBits_WhenNoBitWasSet_WaitForBoth_ClearBit_Success( void )
{
    /* Expectation of Function: xEventGroupCreate */
    vListInitialise_Expect( 0 );
    vListInitialise_IgnoreArg_pxList();
    vListInitialise_ReturnThruPtr_pxList( pxListTemp );

    /* Expectation of Function: xEventGroupWaitBits */
    vTaskSuspendAll_Ignore();
    xTaskGetSchedulerState_IgnoreAndReturn( taskSCHEDULER_SUSPENDED );
    vTaskPlaceOnUnorderedEventList_Ignore();
    xTaskResumeAll_IgnoreAndReturn( 1 );
    uxTaskResetEventItemValue_IgnoreAndReturn( 0 );

    /* Set-up */
    EventBits_t uxBitsSetVal, uxBitsGetVal;
    const TickType_t xTicksToWait = 100 / portTICK_PERIOD_MS;
    StaticEventGroup_t xCreatedEventGroup = { 0 };
    xEventGroupHandle = xEventGroupCreateStatic( &xCreatedEventGroup );
    uxBitsSetVal = xEventGroupGetBits( xEventGroupHandle );

    /* API to Test */
    uxBitsGetVal = xEventGroupWaitBits(
        xEventGroupHandle, /* The event group being tested. */
        BIT_0 | BIT_4,     /* The bits within the event group to wait for. */
        pdTRUE,            /* BIT_0 & BIT_4 should be cleared before returning. */
        pdTRUE,            /* Wait for both bits. */
        xTicksToWait );    /* Wait a maximum of 100ms for either bit to be set. */

    /* Validate: Expect to time-out and BitValue unchanged */
    TEST_ASSERT_EQUAL( uxBitsSetVal, uxBitsGetVal );
}

/*!
 * @brief validate non-block waiting on for either one bits is set when currently no bits are set.
 *        Don't clear the bit before return.
 * @coverage xEventGroupWaitBits
 */
void test_xEventGroupWaitBits_WhenNoBitWasSet_NonBlock_WaitForEither_NoClear_Success( void )
{
    /* Expectation of Function: xEventGroupCreate */
    vListInitialise_Expect( 0 );
    vListInitialise_IgnoreArg_pxList();
    vListInitialise_ReturnThruPtr_pxList( pxListTemp );

    /* Expectation of Function: xEventGroupWaitBits */
    vTaskSuspendAll_Ignore();
    xTaskGetSchedulerState_IgnoreAndReturn( taskSCHEDULER_SUSPENDED );
    vTaskPlaceOnUnorderedEventList_Ignore();
    xTaskResumeAll_IgnoreAndReturn( 1 );
    uxTaskResetEventItemValue_IgnoreAndReturn( 0 );

    /* Set-up */
    EventBits_t uxBitsSetVal, uxBitsGetVal;
    StaticEventGroup_t xCreatedEventGroup = { 0 };
    xEventGroupHandle = xEventGroupCreateStatic( &xCreatedEventGroup );
    uxBitsSetVal = xEventGroupGetBits( xEventGroupHandle );

    /* API to Test */
    uxBitsGetVal = xEventGroupWaitBits(
        xEventGroupHandle, /* The event group being tested. */
        BIT_0 | BIT_4,     /* The bits within the event group to wait for. */
        pdFALSE,           /* BIT_0 & BIT_4 should not be cleared before returning. */
        pdFALSE,           /* Don't wait for both bits, either bit will do. */
        0 );               /* Don't block and wait */

    /* Validate: Expect return and BitValue unchanged */
    TEST_ASSERT_EQUAL( uxBitsSetVal, uxBitsGetVal );
}

/*!
 * @brief validate waiting on for either one bits. The function should return when one bits are set.
 *        Don't clear the bit before return.
 * @coverage xEventGroupWaitBits
 */
void test_xEventGroupWaitBits_WhenBitWasSet_WaitForEither_NoClear_Success( void )
{
    /* Expectation of Function: xEventGroupCreate */
    vListInitialise_Expect( 0 );
    vListInitialise_IgnoreArg_pxList();
    vListInitialise_ReturnThruPtr_pxList( pxListTemp );

    /* Expectation of Function: xEventGroupSetBits */
    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    vTaskSuspendAll_Ignore();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    listGET_LIST_ITEM_VALUE_IgnoreAndReturn( 0 );
    xTaskResumeAll_IgnoreAndReturn( 1 );

    /* Expectation of Function: xEventGroupWaitBits */
    xTaskGetSchedulerState_IgnoreAndReturn( taskSCHEDULER_SUSPENDED );
    vTaskPlaceOnUnorderedEventList_Ignore();
    uxTaskResetEventItemValue_IgnoreAndReturn( 0 );

    /* Set-up */
    EventBits_t uxBitsSetVal, uxBitsGetVal;
    const TickType_t xTicksToWait = 100 / portTICK_PERIOD_MS;
    StaticEventGroup_t xCreatedEventGroup = { 0 };
    xEventGroupHandle = xEventGroupCreateStatic( &xCreatedEventGroup );
    uxBitsSetVal = xEventGroupSetBits( xEventGroupHandle, BIT_0 ); /* BIT_0 was set */

    /* API to Test */
    uxBitsSetVal = xEventGroupWaitBits(
        xEventGroupHandle, /* The event group being tested. */
        BIT_0 | BIT_4,     /* The bits within the event group to wait for. */
        pdFALSE,           /* BIT_0 & BIT_4 should not be cleared before returning. */
        pdFALSE,           /* Don't wait for both bits, either bit will do. */
        xTicksToWait );    /* Wait a maximum of 100ms for either bit to be set. */
    uxBitsGetVal = xEventGroupGetBits( xEventGroupHandle );

    /* Validate: Expect to return because BIT_0 was set */
    TEST_ASSERT_EQUAL( BIT_0, uxBitsSetVal );
    TEST_ASSERT_EQUAL( BIT_0, uxBitsGetVal & BIT_0 );
}

/*!
 * @brief validate waiting on for all bits are set. Don't clear the bit before return.
 * @coverage xEventGroupWaitBits
 */
void test_xEventGroupWaitBits_WhenBitWasSet_WaitForBoth_WithClear_Success( void )
{
    /* Expectation of Function: xEventGroupCreate */
    vListInitialise_Expect( 0 );
    vListInitialise_IgnoreArg_pxList();
    vListInitialise_ReturnThruPtr_pxList( pxListTemp );

    /* Expectation of Function: xEventGroupSetBits x2 */
    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    vTaskSuspendAll_Ignore();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    listGET_LIST_ITEM_VALUE_IgnoreAndReturn( 0 );
    xTaskResumeAll_IgnoreAndReturn( 1 );
    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );

    /* Expectation of Function: xEventGroupWaitBits */
    xTaskGetSchedulerState_IgnoreAndReturn( taskSCHEDULER_SUSPENDED );
    vTaskPlaceOnUnorderedEventList_Ignore();
    uxTaskResetEventItemValue_IgnoreAndReturn( 0 );

    /* Set-up */
    EventBits_t uxBitsSetVal, uxBitsGetVal;
    const TickType_t xTicksToWait = 100 / portTICK_PERIOD_MS;
    StaticEventGroup_t xCreatedEventGroup = { 0 };
    xEventGroupHandle = xEventGroupCreateStatic( &xCreatedEventGroup );
    uxBitsSetVal = xEventGroupSetBits( xEventGroupHandle, BIT_0 ); /* BIT_0 was set */
    uxBitsSetVal = xEventGroupSetBits( xEventGroupHandle, BIT_4 ); /* BIT_4 was set */
    TEST_ASSERT_EQUAL( BIT_0 | BIT_4, uxBitsSetVal );

    /* API to Test */
    uxBitsSetVal = xEventGroupWaitBits(
        xEventGroupHandle, /* The event group being tested. */
        BIT_0 | BIT_4,     /* The bits within the event group to wait for. */
        pdTRUE,            /* BIT_0 & BIT_4 should be cleared before returning. */
        pdTRUE,            /* Wait for both bits. */
        xTicksToWait );    /* Wait a maximum of 100ms for either bit to be set. */
    uxBitsGetVal = xEventGroupGetBits( xEventGroupHandle );

    /* Validate: Expect to return because both BIT_0 and BIT_4 was set and then cleared */
    TEST_ASSERT_EQUAL( BIT_0 | BIT_4, uxBitsSetVal & ( BIT_0 | BIT_4 ) );
    TEST_ASSERT_EQUAL( 0, uxBitsGetVal & ( BIT_0 | BIT_4 ) );
}

/*!
 * @brief validate tasks sync on event bits:
 *        Set BIT_0 before reach the sync point and wait for all sync bits are set.
 *        Should return due to timeout.
 * @coverage xEventGroupSync
 */
void test_xEventGroupSync_SetBits_BlockWait_NotSynced_Success( void )
{
    /* Expectation of Function: xEventGroupCreate */
    vListInitialise_Expect( 0 );
    vListInitialise_IgnoreArg_pxList();
    vListInitialise_ReturnThruPtr_pxList( pxListTemp );

    /* Expectation of Function: xEventGroupSetBits */
    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    vTaskSuspendAll_Ignore();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    xTaskResumeAll_IgnoreAndReturn( 1 );
    listGET_LIST_ITEM_VALUE_IgnoreAndReturn( 0 );

    /* Expectation of Function: xEventGroupSync */
    xTaskGetSchedulerState_IgnoreAndReturn( taskSCHEDULER_SUSPENDED );
    vTaskPlaceOnUnorderedEventList_Ignore();
    uxTaskResetEventItemValue_IgnoreAndReturn( 0 );

    /* Set-up */
    EventBits_t uxReturn;
    StaticEventGroup_t xCreatedEventGroup = { 0 };
    xEventGroupHandle = xEventGroupCreateStatic( &xCreatedEventGroup );

    /* API to Test */
    uxReturn = xEventGroupSync( xEventGroupHandle, BIT_0, ALL_SYNC_BITS, portMAX_DELAY );

    /* Validate: Expect to timeout and BIT_0 was set */
    TEST_ASSERT_EQUAL( BIT_0, uxReturn );
}

/*!
 * @brief validate tasks sync on event bits:
 *        Non-Block wait for all sync bits are set.
 *        Should return due to timeout.
 * @coverage xEventGroupSync
 */
void test_xEventGroupSync_NoSetBit_NonBlockWait_NotSynced_Success( void )
{
    /* Expectation of Function: xEventGroupCreate */
    vListInitialise_Expect( 0 );
    vListInitialise_IgnoreArg_pxList();
    vListInitialise_ReturnThruPtr_pxList( pxListTemp );

    /* Expectation of Function: xEventGroupSetBits x2 */
    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    vTaskSuspendAll_Ignore();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    xTaskResumeAll_IgnoreAndReturn( 1 );
    listGET_LIST_ITEM_VALUE_IgnoreAndReturn( 0 );
    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );

    /* Expectation of Function: xEventGroupSync */
    xTaskGetSchedulerState_IgnoreAndReturn( taskSCHEDULER_SUSPENDED );
    vTaskPlaceOnUnorderedEventList_Ignore();
    uxTaskResetEventItemValue_IgnoreAndReturn( 0 );

    /* Set-up */
    EventBits_t uxReturn;
    StaticEventGroup_t xCreatedEventGroup = { 0 };
    xEventGroupHandle = xEventGroupCreateStatic( &xCreatedEventGroup );
    uxReturn = xEventGroupSetBits( xEventGroupHandle, ( BIT_0 | BIT_2 ) );
    TEST_ASSERT_EQUAL( ( BIT_0 | BIT_2 ), uxReturn );

    /* API to Test */
    uxReturn = xEventGroupSync( xEventGroupHandle, 0, ALL_SYNC_BITS, 0 );

    /* Validate: Expect to return and BIT_0 and BIT_2 was set */
    TEST_ASSERT_EQUAL( ( BIT_0 | BIT_2 ), uxReturn );
}

/*!
 * @brief validate tasks sync on event bits:
 *        Set BIT_0 before reach the sync point and wait for all sync bits are set.
 *        Should return due to reach the sync point.
 * @coverage xEventGroupSync
 */
void test_xEventGroupSync_SetBits_BlockWait_Synced_Success( void )
{
    /* Expectation of Function: xEventGroupCreate */
    vListInitialise_Expect( 0 );
    vListInitialise_IgnoreArg_pxList();
    vListInitialise_ReturnThruPtr_pxList( pxListTemp );

    /* Expectation of Function: xEventGroupSetBits x2 */
    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    vTaskSuspendAll_Ignore();
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    xTaskResumeAll_IgnoreAndReturn( 1 );
    listGET_LIST_ITEM_VALUE_IgnoreAndReturn( 0 );
    listGET_END_MARKER_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );
    listGET_NEXT_ExpectAnyArgsAndReturn( ( ListItem_t * ) NULL );

    /* Expectation of Function: xEventGroupSync */
    xTaskGetSchedulerState_IgnoreAndReturn( taskSCHEDULER_SUSPENDED );
    vTaskPlaceOnUnorderedEventList_Ignore();
    uxTaskResetEventItemValue_IgnoreAndReturn( 0 );

    /* Set-up */
    EventBits_t uxReturn;
    StaticEventGroup_t xCreatedEventGroup = { 0 };
    xEventGroupHandle = xEventGroupCreateStatic( &xCreatedEventGroup );

    /* API to Test */
    uxReturn = xEventGroupSetBits( xEventGroupHandle, ALL_SYNC_BITS );
    uxReturn = xEventGroupSync( xEventGroupHandle, 0, ALL_SYNC_BITS, portMAX_DELAY );

    /* Validate: Expect to return and BIT_0 and BIT_2 was set */
    TEST_ASSERT_EQUAL( ALL_SYNC_BITS, uxReturn );
}

/*!
 * @brief validate getting event group number
 * @coverage uxEventGroupGetNumber
 */
void test_uxEventGroupGetNumber_Success( void )
{
    /* Expectation of Function: xEventGroupCreate */
    vListInitialise_Expect( 0 );
    vListInitialise_IgnoreArg_pxList();
    vListInitialise_ReturnThruPtr_pxList( pxListTemp );

    /* Set-up */
    UBaseType_t xReturn;
    StaticEventGroup_t xCreatedEventGroup = { 0 };
    xEventGroupHandle = xEventGroupCreateStatic( &xCreatedEventGroup );

    /* API to Test */
    xReturn = uxEventGroupGetNumber( NULL );
    TEST_ASSERT_EQUAL( 0, xReturn );
    xReturn = uxEventGroupGetNumber( xEventGroupHandle );
    TEST_ASSERT_EQUAL( 0, xReturn );
}

/*!
 * @brief validate setting event bits.
 * @coverage vEventGroupSetNumber
 */
void test_vEventGroupSetNumber_Success( void )
{
    /* Expectation of Function: xEventGroupCreate */
    vListInitialise_Expect( 0 );
    vListInitialise_IgnoreArg_pxList();
    vListInitialise_ReturnThruPtr_pxList( pxListTemp );

    /* Set-up */
    UBaseType_t xReturn;
    StaticEventGroup_t xCreatedEventGroup = { 0 };
    xEventGroupHandle = xEventGroupCreateStatic( &xCreatedEventGroup );

    /* API to Test */
    vEventGroupSetNumber( xEventGroupHandle, 3 );
    xReturn = uxEventGroupGetNumber( xEventGroupHandle );

    /* Validate */
    TEST_ASSERT_EQUAL( 3, xReturn );
}

/*!
 * @brief validate clearing event bits from ISR.
 * @coverage xEventGroupClearBitsFromISR
 */
void test_xEventGroupClearBitsFromISR_Success( void )
{
    /* Expectation of Function: xEventGroupClearBitsFromISR */
    xTimerPendFunctionCallFromISR_ExpectAndReturn( vEventGroupClearBitsCallback, NULL, 1, NULL, pdPASS );
    xTimerPendFunctionCallFromISR_IgnoreArg_pvParameter1();
    xTimerPendFunctionCallFromISR_IgnoreArg_ulParameter2();
    xTimerPendFunctionCallFromISR_IgnoreArg_pxHigherPriorityTaskWoken();

    /* API to Test */
    ( void ) xEventGroupClearBitsFromISR( NULL, BIT_0 );
}

/*!
 * @brief validate setting event bits from ISR.
 * @coverage xEventGroupClearBitsFromISR
 */
void test_xEventGroupSetBitsFromISR_Success( void )
{
    /* Expectation of Function: xEventGroupSetBitsFromISR */
    xTimerPendFunctionCallFromISR_ExpectAndReturn( vEventGroupSetBitsCallback, NULL, 1, pdFALSE, pdPASS );
    xTimerPendFunctionCallFromISR_IgnoreArg_pvParameter1();
    xTimerPendFunctionCallFromISR_IgnoreArg_ulParameter2();
    xTimerPendFunctionCallFromISR_IgnoreArg_pxHigherPriorityTaskWoken();

    /* Set-up */
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    /* API to Test */
    ( void ) xEventGroupSetBitsFromISR( NULL, BIT_0, &xHigherPriorityTaskWoken );
}
