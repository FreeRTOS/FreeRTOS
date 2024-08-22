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

#ifndef LIST_MACRO_H
#define LIST_MACRO_H

#include <FreeRTOS.h>
#include <task.h>
#include <portmacro.h>
#include <list.h>

struct tskTaskControlBlock;

#undef  listLIST_IS_EMPTY
BaseType_t listLIST_IS_EMPTY( const List_t * pxList );

#undef  listGET_OWNER_OF_HEAD_ENTRY
struct tskTaskControlBlock * listGET_OWNER_OF_HEAD_ENTRY( const List_t * pxList );

#undef listIS_CONTAINED_WITHIN
BaseType_t listIS_CONTAINED_WITHIN( List_t * list,
                                    const ListItem_t * listItem );

#undef listGET_LIST_ITEM_VALUE
TickType_t listGET_LIST_ITEM_VALUE( ListItem_t * listItem );

#undef listSET_LIST_ITEM_VALUE
void listSET_LIST_ITEM_VALUE( ListItem_t * listItem,
                              TickType_t itemValue );


#undef listLIST_ITEM_CONTAINER
List_t * listLIST_ITEM_CONTAINER( const ListItem_t * listItem );

#undef listCURRENT_LIST_LENGTH
UBaseType_t listCURRENT_LIST_LENGTH( List_t * list );

#undef listGET_ITEM_VALUE_OF_HEAD_ENTRY
TickType_t listGET_ITEM_VALUE_OF_HEAD_ENTRY( List_t * list );

#undef listGET_LIST_ITEM_OWNER
struct tskTaskControlBlock * listGET_LIST_ITEM_OWNER( ListItem_t * listItem );

#undef listINSERT_END
void listINSERT_END( List_t * pxList,
                     ListItem_t * listItem );

#undef listREMOVE_ITEM
void listREMOVE_ITEM( ListItem_t * listItem );

#endif /* ifndef LIST_MACRO_H */
