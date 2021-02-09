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
/*! @file list_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>

/* List includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "list.h"

/* Test includes. */
#include "unity.h"

/* ===========================  DEFINES CONSTANTS  ========================== */
#define MAX_ITEMS    5000 /*!< number of items for a few testcases*/

/* ===========================  GLOBAL VARIABLES  =========================== */


/* ============================  Unity Fixtures  ============================ */
/*! called before each testcase */
void setUp( void )
{
}

/*! called after each testcase */
void tearDown( void )
{
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

/*!
 * @brief initilize a preallocated list of ListItems_t
 * @param listItems list to initilize
 * @param count the number of listItems in the list
 */
static void initialize_list_items( ListItem_t * listItems,
                                   int count )
{
    for( int i = 0; i < count; i++ )
    {
        vListInitialiseItem( &listItems[ i ] );
    }
}

/*!
 * @brief initilize a preallocated list of ListItems_t initializing each ones
 *        value to its position value
 * @param listItems list to initilize
 * @param count the number of listItems in the list
 */
static void initialize_list_items_with_position( ListItem_t * listItems,
                                                 int count )
{
    for( int i = 0; i < count; i++ )
    {
        listItems[ i ].xItemValue = i;
        vListInitialiseItem( &listItems[ i ] );
    }
}

/*!
 * @brief validate a list when it is empty
 * @param pxList a list object
 */
static void validate_empty_list( const List_t * const pxList )
{
    TEST_ASSERT_EQUAL( 0U, pxList->uxNumberOfItems );
    TEST_ASSERT_EQUAL_PTR( &pxList->xListEnd, pxList->pxIndex );
    TEST_ASSERT_EQUAL( portMAX_DELAY, pxList->xListEnd.xItemValue );
    TEST_ASSERT_EQUAL( &pxList->xListEnd, pxList->xListEnd.pxNext );
    TEST_ASSERT_EQUAL( &pxList->xListEnd, pxList->xListEnd.pxPrevious );
}

/* ==============================  Test Cases  ============================== */

/*!
 * @brief validate the initilization function of a list
 */
void test_vListInitialisee_Success( void )
{
    List_t pxList;

    vListInitialise( &pxList );
    validate_empty_list( &pxList );
}

/*!
 * @brief ivalidate the initializatiom function of a list item
 */
void test_vListInitialiseItem_Sucess( void )
{
    ListItem_t pxItem;

    vListInitialiseItem( &pxItem );
    TEST_ASSERT_EQUAL( NULL, pxItem.pxContainer );
}

/*!
 * @brief test vListIntertEnd successful case with only 1 item
 * @details This test ensures the list is sane when 1 item is inserted
 */
void test_vListInsertEnd_Success_1_item( void )
{
    List_t pxList;
    ListItem_t pxNewListItem;
    MiniListItem_t * miniListEnd;

    vListInitialise( &pxList );
    vListInitialiseItem( &pxNewListItem );
    miniListEnd = ( MiniListItem_t * ) pxList.pxIndex;

    vListInsertEnd( &pxList, &pxNewListItem );
    /* List contains 1 item */
    TEST_ASSERT_EQUAL( 1U, pxList.uxNumberOfItems );
    TEST_ASSERT_EQUAL_PTR( &pxList.xListEnd, miniListEnd );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem.pxNext, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem.pxPrevious, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem.pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxNext, &pxNewListItem );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxPrevious, &pxNewListItem );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->xItemValue, portMAX_DELAY );
}

/*!
 * @brief test vListIntertEnd successful case with only 2 items
 * @details This test ensures the list is sane when 2 items are inserted
 */
void test_vListInsertEnd_Success_2_items( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 2 ];
    MiniListItem_t * miniListEnd;

    vListInitialise( &pxList );
    vListInitialiseItem( &pxNewListItem[ 0 ] );
    vListInitialiseItem( &pxNewListItem[ 1 ] );
    miniListEnd = ( MiniListItem_t * ) pxList.pxIndex;

    vListInsertEnd( &pxList, &pxNewListItem[ 0 ] );
    vListInsertEnd( &pxList, &pxNewListItem[ 1 ] );
    /* List contains 2 items */
    TEST_ASSERT_EQUAL( 2U, pxList.uxNumberOfItems );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxNext, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxPrevious, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxNext, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxPrevious, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxNext, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxPrevious, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->xItemValue, portMAX_DELAY );
}

/*!
 * @brief test vListIntertEnd successful case with only 3 items
 * @details This test ensures the list is sane when 3 items are inserted
 */
void test_vListInsertEnd_Success_3_items( void )
{
    List_t pxList;

    ListItem_t pxNewListItem[ 3 ];
    MiniListItem_t * miniListEnd;

    vListInitialise( &pxList );
    initialize_list_items( pxNewListItem, 3 );

    miniListEnd = ( MiniListItem_t * ) pxList.pxIndex;

    vListInsertEnd( &pxList, &pxNewListItem[ 0 ] );
    vListInsertEnd( &pxList, &pxNewListItem[ 1 ] );
    vListInsertEnd( &pxList, &pxNewListItem[ 2 ] );
    /* List contains 3 items */
    TEST_ASSERT_EQUAL( 3U, pxList.uxNumberOfItems );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxNext, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxPrevious, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxNext, &pxNewListItem[ 2 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxPrevious, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 2 ].pxNext, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 2 ].pxPrevious, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 2 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxNext, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxPrevious, &pxNewListItem[ 2 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->xItemValue, portMAX_DELAY );
}

/*!
 * @brief test vListIntertEnd successful case with multiple items 5000
 * @details This test ensures the list is sane when 5000 items are inserted
 */
void test_vListInsertEnd_success_multiple_items( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ MAX_ITEMS ];
    MiniListItem_t * miniListEnd;

    vListInitialise( &pxList );
    initialize_list_items( pxNewListItem, MAX_ITEMS );
    miniListEnd = ( MiniListItem_t * ) pxList.pxIndex;

    for( int i = 0; i < MAX_ITEMS; i++ )
    {
        vListInsertEnd( &pxList, &pxNewListItem[ i ] );
    }

    /* List contains 5000 items */
    TEST_ASSERT_EQUAL( MAX_ITEMS, pxList.uxNumberOfItems );

    for( int i = 1; i < MAX_ITEMS - 1; i++ )
    {
        TEST_ASSERT_EQUAL_PTR( pxNewListItem[ i ].pxNext, &pxNewListItem[ i + 1 ] );
        TEST_ASSERT_EQUAL_PTR( pxNewListItem[ i ].pxPrevious, &pxNewListItem[ i - 1 ] );
        TEST_ASSERT_EQUAL_PTR( pxNewListItem[ i ].pxContainer, &pxList );
    }

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxNext, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxPrevious, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ MAX_ITEMS - 1 ].pxNext, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ MAX_ITEMS - 1 ].pxPrevious, &pxNewListItem[ MAX_ITEMS - 2 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ MAX_ITEMS - 1 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxNext, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxPrevious, &pxNewListItem[ MAX_ITEMS - 1 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->xItemValue, portMAX_DELAY );
}

/*!
 * @brief test vListIntert successful case with 1 item
 * @details This test ensures the list is sane when 1 item is inserted
 */
void test_vListInsert_sucess_1_item( void )
{
    List_t pxList;
    ListItem_t pxNewListItem;
    MiniListItem_t * miniListEnd;

    vListInitialise( &pxList );
    vListInitialiseItem( &pxNewListItem );
    miniListEnd = ( MiniListItem_t * ) pxList.pxIndex;
    vListInsert( &pxList, &pxNewListItem );

    TEST_ASSERT_EQUAL( 1U, pxList.uxNumberOfItems );
    TEST_ASSERT_EQUAL_PTR( &pxList.xListEnd, miniListEnd );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem.pxNext, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem.pxPrevious, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem.pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxNext, &pxNewListItem );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxPrevious, &pxNewListItem );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->xItemValue, portMAX_DELAY );
}

/*!
 * @brief test vListIntert successful case with 2 items
 * @details This test ensures the list is sane when 2 items are inserted
 */
void test_vListInsert_sucess_2_items( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 2 ];
    MiniListItem_t * miniListEnd;

    vListInitialise( &pxList );
    initialize_list_items( pxNewListItem, 2 );
    miniListEnd = ( MiniListItem_t * ) pxList.pxIndex;

    pxNewListItem[ 0 ].xItemValue = 0;
    pxNewListItem[ 1 ].xItemValue = 1;
    vListInsert( &pxList, &pxNewListItem[ 0 ] );
    vListInsert( &pxList, &pxNewListItem[ 1 ] );

    TEST_ASSERT_EQUAL( 2U, pxList.uxNumberOfItems );
    TEST_ASSERT_EQUAL_PTR( &pxList.xListEnd, miniListEnd );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxNext, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxPrevious, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxNext, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxPrevious, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxNext, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxPrevious, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->xItemValue, portMAX_DELAY );
}

/*!
 * @brief test vListIntert successful case with 3 items
 * @details This test ensures the list is sane when 3 items are inserted
 */
void test_vListInsert_sucess_3_items( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 3 ];
    MiniListItem_t * miniListEnd;

    vListInitialise( &pxList );
    initialize_list_items( pxNewListItem, 2 );
    miniListEnd = ( MiniListItem_t * ) pxList.pxIndex;

    pxNewListItem[ 0 ].xItemValue = 0;
    pxNewListItem[ 1 ].xItemValue = 1;
    pxNewListItem[ 2 ].xItemValue = 2;

    vListInsert( &pxList, &pxNewListItem[ 0 ] );
    vListInsert( &pxList, &pxNewListItem[ 1 ] );
    vListInsert( &pxList, &pxNewListItem[ 2 ] );


    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxNext, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxPrevious, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxNext, &pxNewListItem[ 2 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxPrevious, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 2 ].pxNext, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 2 ].pxPrevious, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 2 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxNext, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxPrevious, &pxNewListItem[ 2 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->xItemValue, portMAX_DELAY );
}

/*!
 * @brief test vListIntert successful case with multiple items
 * @details This test ensures the list is sane when multiple items are inserted
 */
void test_vListInsert_success_multiple_items( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ MAX_ITEMS ];
    MiniListItem_t * miniListEnd;

    vListInitialise( &pxList );
    initialize_list_items_with_position( pxNewListItem, MAX_ITEMS );
    miniListEnd = ( MiniListItem_t * ) pxList.pxIndex;

    for( int i = 0; i < MAX_ITEMS; i++ )
    {
        vListInsert( &pxList, &pxNewListItem[ i ] );
    }

    /* List contains 5000 items */
    TEST_ASSERT_EQUAL( MAX_ITEMS, pxList.uxNumberOfItems );

    for( int i = 1; i < MAX_ITEMS - 1; i++ )
    {
        TEST_ASSERT_EQUAL_PTR( pxNewListItem[ i ].pxNext, &pxNewListItem[ i + 1 ] );
        TEST_ASSERT_EQUAL_PTR( pxNewListItem[ i ].pxPrevious, &pxNewListItem[ i - 1 ] );
        TEST_ASSERT_EQUAL_PTR( pxNewListItem[ i ].pxContainer, &pxList );
    }

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxNext, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxPrevious, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ MAX_ITEMS - 1 ].pxNext, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ MAX_ITEMS - 1 ].pxPrevious,
                           &pxNewListItem[ MAX_ITEMS - 2 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ MAX_ITEMS - 1 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxNext, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxPrevious, &pxNewListItem[ MAX_ITEMS - 1 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->xItemValue, portMAX_DELAY );
}

/*!
 * @brief test uxListRemove successful case with 1 item
 * @details This test ensures the list is sane when 1 item is removed
 */
void test_vListInsert_success_vportMAXDELAY( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 2 ];
    MiniListItem_t * miniListEnd;

    vListInitialise( &pxList );
    initialize_list_items( pxNewListItem, 2 );
    miniListEnd = ( MiniListItem_t * ) pxList.pxIndex;

    pxNewListItem[ 0 ].xItemValue = 1;
    pxNewListItem[ 1 ].xItemValue = portMAX_DELAY;
    vListInsert( &pxList, &pxNewListItem[ 0 ] );
    vListInsert( &pxList, &pxNewListItem[ 1 ] );

    TEST_ASSERT_EQUAL( 2U, pxList.uxNumberOfItems );
    TEST_ASSERT_EQUAL_PTR( &pxList.xListEnd, miniListEnd );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxNext, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxPrevious, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxNext, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxPrevious, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxNext, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxPrevious, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->xItemValue, portMAX_DELAY );
}

/*!
 * @brief test uxListRemove successful case with 1 item
 * @details This test ensures the list is sane when 1 item is removed
 */
void test_uxListRemove_sucesss( void )
{
    List_t pxList;
    ListItem_t pxNewListItem;
    MiniListItem_t * miniListEnd;

    vListInitialise( &pxList );
    vListInitialiseItem( &pxNewListItem );
    miniListEnd = ( MiniListItem_t * ) pxList.pxIndex;
    vListInsert( &pxList, &pxNewListItem );

    TEST_ASSERT_EQUAL( 1U, pxList.uxNumberOfItems );
    TEST_ASSERT_EQUAL_PTR( &pxList.xListEnd, miniListEnd );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem.pxNext, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem.pxPrevious, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem.pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxNext, &pxNewListItem );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxPrevious, &pxNewListItem );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->xItemValue, portMAX_DELAY );

    uxListRemove( &pxNewListItem );

    validate_empty_list( &pxList );

    TEST_ASSERT_EQUAL( 0U, pxList.uxNumberOfItems );
    TEST_ASSERT_EQUAL_PTR( &pxList.xListEnd, pxList.pxIndex );
    TEST_ASSERT_EQUAL( portMAX_DELAY, pxList.xListEnd.xItemValue );
    TEST_ASSERT_EQUAL( &pxList.xListEnd, pxList.xListEnd.pxNext );
    TEST_ASSERT_EQUAL( &pxList.xListEnd, pxList.xListEnd.pxPrevious );
}

/*!
 * @brief test uxListRemove successful case with 2 items
 * @details This test ensures the list is sane when 2 items are removed
 */
void test_uxListRemove_multiple( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 3 ];
    MiniListItem_t * miniListEnd;

    vListInitialise( &pxList );
    initialize_list_items( pxNewListItem, 2 );
    miniListEnd = ( MiniListItem_t * ) pxList.pxIndex;

    pxNewListItem[ 0 ].xItemValue = 0;
    pxNewListItem[ 1 ].xItemValue = 1;
    pxNewListItem[ 2 ].xItemValue = portMAX_DELAY;

    vListInsert( &pxList, &pxNewListItem[ 0 ] );
    vListInsert( &pxList, &pxNewListItem[ 1 ] );
    vListInsert( &pxList, &pxNewListItem[ 2 ] );

    uxListRemove( &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL( 2U, pxList.uxNumberOfItems );
    vListInsert( &pxList, &pxNewListItem[ 1 ] );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxNext, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxPrevious, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxNext, &pxNewListItem[ 2 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxPrevious, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 2 ].pxNext, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 2 ].pxPrevious, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 2 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxNext, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxPrevious, &pxNewListItem[ 2 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->xItemValue, portMAX_DELAY );

    uxListRemove( &pxNewListItem[ 2 ] );
    TEST_ASSERT_EQUAL( 2U, pxList.uxNumberOfItems );
    vListInsert( &pxList, &pxNewListItem[ 2 ] );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxNext, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxPrevious, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxNext, &pxNewListItem[ 2 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxPrevious, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 2 ].pxNext, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 2 ].pxPrevious, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 2 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxNext, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxPrevious, &pxNewListItem[ 2 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->xItemValue, portMAX_DELAY );

    uxListRemove( &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL( 2U, pxList.uxNumberOfItems );
    vListInsert( &pxList, &pxNewListItem[ 0 ] );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxNext, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxPrevious, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxNext, &pxNewListItem[ 2 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxPrevious, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 1 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 2 ].pxNext, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 2 ].pxPrevious, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 2 ].pxContainer, &pxList );

    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxNext, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxPrevious, &pxNewListItem[ 2 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->xItemValue, portMAX_DELAY );
}
