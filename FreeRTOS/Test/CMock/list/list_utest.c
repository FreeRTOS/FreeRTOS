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
 * @brief initialize a preallocated list of ListItems_t
 * @param listItems list to initialize
 * @param count the number of listItems in the list
 */
static void initialise_list_items( ListItem_t * listItems,
                                   int count )
{
    for( int i = 0; i < count; i++ )
    {
        vListInitialiseItem( &listItems[ i ] );
    }
}

/*!
 * @brief initialize a preallocated list of ListItems_t initializing each ones
 *        value to its position value
 * @param listItems list to initialize
 * @param count the number of listItems in the list
 */
static void initialise_list_items_with_position( ListItem_t * listItems,
                                                 int count )
{
    for( int i = 0; i < count; i++ )
    {
        /*listItems[ i ].xItemValue = i; */
        listSET_LIST_ITEM_VALUE( &listItems[ i ], i );
        vListInitialiseItem( &listItems[ i ] );
    }
}

/*!
 * @brief validate a list when it is empty
 * @param pxList a list object
 */
static void validate_empty_list( const List_t * const pxList )
{
    TEST_ASSERT_EQUAL( 0U, listCURRENT_LIST_LENGTH( pxList ) );
    TEST_ASSERT_EQUAL_PTR( &pxList->xListEnd, pxList->pxIndex );
    TEST_ASSERT_EQUAL( portMAX_DELAY, pxList->xListEnd.xItemValue );
    TEST_ASSERT_EQUAL( &pxList->xListEnd, pxList->xListEnd.pxNext );
    TEST_ASSERT_EQUAL( &pxList->xListEnd, pxList->xListEnd.pxPrevious );
}

/* ==============================  Test Cases  ============================== */

/*!
 * @brief validate the initialization function of a list
 * @coverage vListInitialise
 */
void test_vListInitialise_Success( void )
{
    List_t pxList;

    vListInitialise( &pxList );
    validate_empty_list( &pxList );
}

/*!
 * @brief validate the initialization function of a list item
 * @coverage vListInitialiseItem
 */
void test_vListInitialiseItem_Success( void )
{
    ListItem_t pxItem;

    vListInitialiseItem( &pxItem );
    TEST_ASSERT_EQUAL( NULL, pxItem.pxContainer );
}

/*!
 * @brief test vListIntertEnd successful case with only 1 item
 * @details This test ensures the list is sane when 1 item is inserted
 * @coverage vListInsertEnd
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
 * @coverage vListInsertEnd
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
 * @coverage vListInsertEnd
 */
void test_vListInsertEnd_Success_3_items( void )
{
    List_t pxList;

    ListItem_t pxNewListItem[ 3 ];
    MiniListItem_t * miniListEnd;

    vListInitialise( &pxList );
    initialise_list_items( pxNewListItem, 3 );

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
 * @brief test vListIntertEnd successful case with multiple items (5000)
 * @details This test ensures the list is sane when 5000 items are inserted
 * @coverage vListInsertEnd
 */
void test_vListInsertEnd_success_multiple_items( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ MAX_ITEMS ];
    MiniListItem_t * miniListEnd;

    vListInitialise( &pxList );
    initialise_list_items( pxNewListItem, MAX_ITEMS );
    miniListEnd = ( MiniListItem_t * ) pxList.pxIndex;

    for( int i = 0; i < MAX_ITEMS; i++ )
    {
        vListInsertEnd( &pxList, &pxNewListItem[ i ] );
    }

    /* List contains 5000 items */
    TEST_ASSERT_EQUAL( MAX_ITEMS, pxList.uxNumberOfItems );

    /* Validate all elements except first and last */
    for( int i = 1; i < MAX_ITEMS - 1; i++ )
    {
        TEST_ASSERT_EQUAL_PTR( pxNewListItem[ i ].pxNext, &pxNewListItem[ i + 1 ] );
        TEST_ASSERT_EQUAL_PTR( pxNewListItem[ i ].pxPrevious, &pxNewListItem[ i - 1 ] );
        TEST_ASSERT_EQUAL_PTR( pxNewListItem[ i ].pxContainer, &pxList );
    }

    /* Validate first element */
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxNext, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxPrevious, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxContainer, &pxList );

    /* Validate last element */
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ MAX_ITEMS - 1 ].pxNext, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ MAX_ITEMS - 1 ].pxPrevious, &pxNewListItem[ MAX_ITEMS - 2 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ MAX_ITEMS - 1 ].pxContainer, &pxList );

    /* Validate end marker */
    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxNext, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxPrevious, &pxNewListItem[ MAX_ITEMS - 1 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->xItemValue, portMAX_DELAY );
}

/*!
 * @brief test vListIntert successful case with 1 item
 * @details This test ensures the list is sane when 1 item is inserted
 * @coverage vListInsert
 */
void test_vListInsert_success_1_item( void )
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
 * @coverage vListInsert
 */
void test_vListInsert_success_2_items( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 2 ];
    MiniListItem_t * miniListEnd;

    vListInitialise( &pxList );
    initialise_list_items( pxNewListItem, 2 );
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
 * @coverage vListInsert
 */
void test_vListInsert_success_3_items( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 3 ];
    MiniListItem_t * miniListEnd;

    vListInitialise( &pxList );
    initialise_list_items( pxNewListItem, 2 );
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
 * @brief test vListIntert successful case with multiple items (5000)
 * @details This test ensures the list is sane when multiple items are inserted
 * @coverage vListInsert
 */
void test_vListInsert_success_multiple_items( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ MAX_ITEMS ];
    MiniListItem_t * miniListEnd;

    vListInitialise( &pxList );
    initialise_list_items_with_position( pxNewListItem, MAX_ITEMS );
    miniListEnd = ( MiniListItem_t * ) pxList.pxIndex;

    for( int i = 0; i < MAX_ITEMS; i++ )
    {
        vListInsert( &pxList, &pxNewListItem[ i ] );
    }

    /* List contains 5000 items */
    TEST_ASSERT_EQUAL( MAX_ITEMS, pxList.uxNumberOfItems );

    /* Validate all elements except first and last */
    for( int i = 1; i < MAX_ITEMS - 1; i++ )
    {
        TEST_ASSERT_EQUAL_PTR( pxNewListItem[ i ].pxNext, &pxNewListItem[ i + 1 ] );
        TEST_ASSERT_EQUAL_PTR( pxNewListItem[ i ].pxPrevious, &pxNewListItem[ i - 1 ] );
        TEST_ASSERT_EQUAL_PTR( pxNewListItem[ i ].pxContainer, &pxList );
    }

    /* Validate first element */
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxNext, &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxPrevious, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ 0 ].pxContainer, &pxList );

    /* Validate last element */
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ MAX_ITEMS - 1 ].pxNext, miniListEnd );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ MAX_ITEMS - 1 ].pxPrevious,
                           &pxNewListItem[ MAX_ITEMS - 2 ] );
    TEST_ASSERT_EQUAL_PTR( pxNewListItem[ MAX_ITEMS - 1 ].pxContainer, &pxList );

    /* Validate end marker */
    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxNext, &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->pxPrevious, &pxNewListItem[ MAX_ITEMS - 1 ] );
    TEST_ASSERT_EQUAL_PTR( miniListEnd->xItemValue, portMAX_DELAY );
}

/*!
 * @brief test uxListRemove successful case with 1 item
 * @details This test ensures the list is sane when 1 item is removed
 * @coverage vListInsert
 */
void test_vListInsert_success_vportMAXDELAY( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 2 ];
    MiniListItem_t * miniListEnd;

    vListInitialise( &pxList );
    initialise_list_items( pxNewListItem, 2 );
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
 * @coverage uxListRemove
 */
void test_uxListRemove_success( void )
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
 * @coverage uxListRemove
 */
void test_uxListRemove_multiple( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 3 ];
    MiniListItem_t * miniListEnd;

    vListInitialise( &pxList );
    initialise_list_items( pxNewListItem, 3 );
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
    TEST_ASSERT_EQUAL( 2U, listCURRENT_LIST_LENGTH( &pxList ) );
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

/*!
 * @brief test uxListRemove when the index pointed to by pxList->pxIndex is
 *        being removed
 * @details This test ensures that the function uxListRemove reassigns the
 *          index to the previous element of the one being removed
 * @coverage uxListRemove
 */
void test_uxListRemove_index_item( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 2 ];
    void * owner1 = ( void * ) 0;
    void * owner2 = ( void * ) 8;
    void * nextOwner;

    vListInitialise( &pxList );
    initialise_list_items_with_position( pxNewListItem, 2 );

    vListInsert( &pxList, &pxNewListItem[ 0 ] );
    vListInsert( &pxList, &pxNewListItem[ 1 ] );
    listSET_LIST_ITEM_OWNER( &pxNewListItem[ 0 ], owner1 );
    listSET_LIST_ITEM_OWNER( &pxNewListItem[ 1 ], owner2 );

    TEST_ASSERT_EQUAL_PTR( &pxList.xListEnd, pxList.pxIndex );

    listGET_OWNER_OF_NEXT_ENTRY( nextOwner, ( List_t * const ) &pxList );
    TEST_ASSERT_EQUAL_PTR( nextOwner, owner1 );
    listGET_OWNER_OF_NEXT_ENTRY( nextOwner, ( List_t * const ) &pxList );
    TEST_ASSERT_EQUAL_PTR( nextOwner, owner2 );

    uxListRemove( &pxNewListItem[ 1 ] );
    TEST_ASSERT_EQUAL( &pxNewListItem[ 0 ], pxList.pxIndex );
    uxListRemove( &pxNewListItem[ 0 ] );
    validate_empty_list( &pxList );
}

/*!
 * @brief test macros listSET_LIST_ITEM_VALUE and   listGET_LIST_ITEM_VALUE
 * @details This test ensures  that the macros are setting and getting the exact
 *          values stored in the list items
 */
void test_macro_listSET_GET_LIST_ITEM_VALUE( void )
{
    ListItem_t pxNewListItem;
    int initial_value = 10;
    int get_value;

    listSET_LIST_ITEM_VALUE( &pxNewListItem, initial_value );
    get_value = listGET_LIST_ITEM_VALUE( &pxNewListItem );
    TEST_ASSERT_EQUAL( get_value, initial_value );
}

/*!
 * @brief test macro listCURRENT_LIST_LENGTH
 * @details This test ensures  that the macro  is returning the actual number
 *          of items in the list
 */
void test_macro_listCURRENT_LIST_LENGTH( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 3 ];

    vListInitialise( &pxList );
    initialise_list_items( pxNewListItem, 3 );

    vListInsert( &pxList, &pxNewListItem[ 0 ] );
    vListInsert( &pxList, &pxNewListItem[ 1 ] );
    vListInsert( &pxList, &pxNewListItem[ 2 ] );

    TEST_ASSERT_EQUAL( 3U, pxList.uxNumberOfItems );
    TEST_ASSERT_EQUAL( 3U, listCURRENT_LIST_LENGTH( &pxList ) );
}

/*!
 * @brief test macro listGET_LIST_ITEM_OWNER and listSET_LIST_ITEM_OWNER
 * @details This test ensures that the macros set and get the same owner from
 *          the ListItem_t
 */
void test_macros_list_SET_GET_LIST_ITEM_OWNER( void )
{
    ListItem_t pxNewListItem;
    void * owner = ( void * ) 0;
    void * saved_owner;

    listSET_LIST_ITEM_OWNER( &pxNewListItem, owner );
    saved_owner = listGET_LIST_ITEM_OWNER( &pxNewListItem );
    TEST_ASSERT_EQUAL_PTR( saved_owner, owner );
}

/*!
 * @brief test macro  listGET_OWNER_OF_NEXT_ENTRY
 * @details This test ensures  that the macro is circling correctly through the list
 */
void test_macro_listGET_OWNER_OF_NEXT_ENTRY( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 3 ];
    void * owner1 = ( void * ) 0;
    void * owner2 = ( void * ) 8;
    void * owner3 = ( void * ) 16;
    void * nextOwner;

    vListInitialise( &pxList );
    initialise_list_items( pxNewListItem, 3 );

    pxNewListItem[ 0 ].xItemValue = 0;
    pxNewListItem[ 1 ].xItemValue = 1;
    pxNewListItem[ 2 ].xItemValue = portMAX_DELAY;

    vListInsert( &pxList, &pxNewListItem[ 0 ] );
    vListInsert( &pxList, &pxNewListItem[ 1 ] );
    vListInsert( &pxList, &pxNewListItem[ 2 ] );

    listSET_LIST_ITEM_OWNER( &pxNewListItem[ 0 ], owner1 );
    listSET_LIST_ITEM_OWNER( &pxNewListItem[ 1 ], owner2 );
    listSET_LIST_ITEM_OWNER( &pxNewListItem[ 2 ], owner3 );

    TEST_ASSERT_EQUAL_PTR( &pxList.xListEnd, pxList.pxIndex );

    listGET_OWNER_OF_NEXT_ENTRY( nextOwner, ( List_t * const ) &pxList );
    TEST_ASSERT_NOT_EQUAL_UINT64( &pxList.xListEnd, pxList.pxIndex );
    TEST_ASSERT_EQUAL( pxList.pxIndex->pvOwner, owner1 );
    TEST_ASSERT_EQUAL_PTR( nextOwner, owner1 );

    listGET_OWNER_OF_NEXT_ENTRY( nextOwner, ( List_t * const ) &pxList );
    TEST_ASSERT_NOT_EQUAL_UINT64( &pxList.xListEnd, pxList.pxIndex );
    TEST_ASSERT_EQUAL( pxList.pxIndex->pvOwner, owner2 );
    TEST_ASSERT_EQUAL_PTR( nextOwner, owner2 );

    listGET_OWNER_OF_NEXT_ENTRY( nextOwner, ( List_t * const ) &pxList );
    TEST_ASSERT_NOT_EQUAL_UINT64( &pxList.xListEnd, pxList.pxIndex );
    TEST_ASSERT_EQUAL( pxList.pxIndex->pvOwner, owner3 );
    TEST_ASSERT_EQUAL_PTR( nextOwner, owner3 );

    /* back to the first owner */
    listGET_OWNER_OF_NEXT_ENTRY( nextOwner, ( List_t * const ) &pxList );
    TEST_ASSERT_NOT_EQUAL_UINT64( &pxList.xListEnd, pxList.pxIndex );
    TEST_ASSERT_EQUAL( pxList.pxIndex->pvOwner, owner1 );
    TEST_ASSERT_EQUAL_PTR( nextOwner, owner1 );
}

/*!
 * @brief test macro listGET_ITEM_VALUE_OF_HEAD_ENTRY normal case
 * @details This test ensures  that the macro is returning the correct value of
 *          the head entry from pxList
 */
void test_macro_listGET_ITEM_VALUE_OF_HEAD_ENTRY( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 2 ];
    TickType_t saved_item_value;

    vListInitialise( &pxList );
    initialise_list_items( pxNewListItem, 2 );

    pxNewListItem[ 0 ].xItemValue = 0;
    pxNewListItem[ 1 ].xItemValue = 1;

    vListInsert( &pxList, &pxNewListItem[ 0 ] );
    vListInsert( &pxList, &pxNewListItem[ 1 ] );
    saved_item_value = listGET_ITEM_VALUE_OF_HEAD_ENTRY( &pxList );
    TEST_ASSERT_EQUAL( saved_item_value, pxNewListItem[ 0 ].xItemValue );
}

/*!
 * @brief test macro listGET_HEAD_ENTRY normal case
 * @details This test ensures  that the macro is returning the head entry
 */
void test_macro_listGET_HEAD_ENTRY( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 2 ];
    ListItem_t * saved_head_entry;

    vListInitialise( &pxList );
    initialise_list_items( pxNewListItem, 2 );

    pxNewListItem[ 0 ].xItemValue = 0;
    pxNewListItem[ 1 ].xItemValue = 1;

    vListInsert( &pxList, &pxNewListItem[ 0 ] );
    vListInsert( &pxList, &pxNewListItem[ 1 ] );
    saved_head_entry = listGET_HEAD_ENTRY( &pxList );
    TEST_ASSERT_EQUAL_PTR( saved_head_entry, &pxNewListItem[ 0 ] );
}

/*!
 * @brief test macro listGET_NEXT normal case
 * @details This test ensures that the macro is returning the next list item
 */
void test_macro_listGET_NEXT( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 2 ];
    ListItem_t * pxNextListItem;

    vListInitialise( &pxList );
    initialise_list_items( pxNewListItem, 2 );

    pxNewListItem[ 0 ].xItemValue = 0;
    pxNewListItem[ 1 ].xItemValue = 1;

    vListInsert( &pxList, &pxNewListItem[ 0 ] );
    vListInsert( &pxList, &pxNewListItem[ 1 ] );

    pxNextListItem = listGET_NEXT( &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( &pxNewListItem[ 1 ], pxNextListItem );
}

/*!
 * @brief test macro listGET_END_MARKER normal case
 * @details This test ensures that the macro is returning the last item
 *          (MiniListItem_t)
 */
void test_macro_listGET_END_MARKER( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 2 ];
    MiniListItem_t * endList;

    vListInitialise( &pxList );
    initialise_list_items( pxNewListItem, 2 );

    pxNewListItem[ 0 ].xItemValue = 0;
    pxNewListItem[ 1 ].xItemValue = 1;

    vListInsert( &pxList, &pxNewListItem[ 0 ] );
    vListInsert( &pxList, &pxNewListItem[ 1 ] );

    endList = ( MiniListItem_t * ) listGET_END_MARKER( &pxList );
    TEST_ASSERT_EQUAL_PTR( &pxList.xListEnd, endList );
}

/*!
 * @brief test macro listLIST_IS_EMPTY normal case
 * @details This test ensures that the macro is returning if the list is empty
 *          or not
 */
void test_macro_listLIST_IS_EMPTY( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 2 ];
    bool is_list_empty;

    vListInitialise( &pxList );
    initialise_list_items( pxNewListItem, 2 );
    is_list_empty = listLIST_IS_EMPTY( &pxList );
    TEST_ASSERT_TRUE( is_list_empty );

    vListInsert( &pxList, &pxNewListItem[ 0 ] );
    is_list_empty = listLIST_IS_EMPTY( &pxList );
    TEST_ASSERT_FALSE( is_list_empty );
    vListInsert( &pxList, &pxNewListItem[ 1 ] );
    is_list_empty = listLIST_IS_EMPTY( &pxList );
    TEST_ASSERT_FALSE( is_list_empty );
}

/*!
 * @brief test macro listGET_OWNER_OF_HEAD_ENTRY normal case
 * @details This test ensures that the macro is returning  the owner of he head
 *          entry
 */
void test_macro_listGET_OWNER_OF_HEAD_ENTRY( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 2 ];
    void * owner1 = ( void * ) 0;
    void * owner2 = ( void * ) 8;
    void * saved_owner;

    vListInitialise( &pxList );
    initialise_list_items( pxNewListItem, 2 );

    pxNewListItem[ 0 ].xItemValue = 0;
    pxNewListItem[ 1 ].xItemValue = 1;

    listSET_LIST_ITEM_OWNER( &pxNewListItem[ 0 ], owner1 );
    listSET_LIST_ITEM_OWNER( &pxNewListItem[ 1 ], owner2 );

    vListInsert( &pxList, &pxNewListItem[ 0 ] );
    vListInsert( &pxList, &pxNewListItem[ 1 ] );

    saved_owner = listGET_OWNER_OF_HEAD_ENTRY( &pxList );
    TEST_ASSERT_EQUAL_PTR( saved_owner, owner1 );
}

/*!
 * @brief test macro listIS_CONTAINED_WITHIN normal case
 * @details This test ensures that the macro is returning whether the list item
 *          is contained within the list
 */
void test_macro_listIS_CONTAINED_WITHIN( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 2 ];
    bool is_contained;

    vListInitialise( &pxList );
    initialise_list_items( pxNewListItem, 2 );


    vListInsertEnd( &pxList, &pxNewListItem[ 0 ] );
    is_contained = listIS_CONTAINED_WITHIN( &pxList, &pxNewListItem[ 1 ] );
    TEST_ASSERT_FALSE( is_contained );

    vListInsertEnd( &pxList, &pxNewListItem[ 1 ] );
    /* List contains 2 items */
    TEST_ASSERT_EQUAL( 2U, pxList.uxNumberOfItems );
    is_contained = listIS_CONTAINED_WITHIN( &pxList, &pxNewListItem[ 1 ] );
    TEST_ASSERT_TRUE( is_contained );
    uxListRemove( &pxNewListItem[ 1 ] );
    is_contained = listIS_CONTAINED_WITHIN( &pxList, &pxNewListItem[ 1 ] );
    TEST_ASSERT_FALSE( is_contained );
}

/*!
 * @brief test macro listLIST_ITEM_CONTAINER normal case
 * @details This test ensures that the macro is returning the item container
 *          list
 */
void test_macro_listLIST_ITEM_CONTAINER( void )
{
    List_t pxList;
    ListItem_t pxNewListItem[ 2 ];
    List_t * pxListContainer;

    vListInitialise( &pxList );
    initialise_list_items( pxNewListItem, 2 );


    vListInsertEnd( &pxList, &pxNewListItem[ 0 ] );
    vListInsertEnd( &pxList, &pxNewListItem[ 1 ] );
    /* List contains 2 items */
    TEST_ASSERT_EQUAL( 2U, pxList.uxNumberOfItems );
    pxListContainer = listLIST_ITEM_CONTAINER( &pxNewListItem[ 0 ] );
    TEST_ASSERT_EQUAL_PTR( pxListContainer, &pxList );
}

/*!
 * @brief test macro listLIST_IS_INITIALISED normal case
 * @details This test ensures that the macro is returning true when the list is
 *          initialised
 */
void test_macro_listLIST_IS_INITIALISED_success( void )
{
    List_t pxList;
    bool is_initialised;

    vListInitialise( &pxList );

    is_initialised = listLIST_IS_INITIALISED( &pxList );
    TEST_ASSERT_TRUE( is_initialised );
}

/*!
 * @brief test macro listLIST_ITEM_CONTAINER normal case
 * @details This test ensures that the macro is returning false when the list is
 *          not initialised
 */
void test_macro_listLIST_IS_INITIALISED_fail( void )
{
    List_t pxList = { 0 };
    bool is_initialised;

    is_initialised = listLIST_IS_INITIALISED( &pxList );
    TEST_ASSERT_FALSE( is_initialised );
}
