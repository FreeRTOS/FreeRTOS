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

#include <stdint.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"
#include "old_list.h"
#include "cbmc.h"

void harness()
{
    // Initialize the lists
    List_t arrayList;
    vListInitialise(&arrayList);
    old_List_t linkedList;
    vold_ListInitialise(&linkedList);

    // Set a non-deterministic list size
    UBaseType_t numItems;
    __CPROVER_assume(numItems <= configLIST_SIZE - 1);

    // Allocate the same elements for the array-list and linked-list
    ListItem_t arrayListItems[configLIST_SIZE - 1];
    old_ListItem_t linkedListItems[configLIST_SIZE - 1];
    for (UBaseType_t i = 0 ; i < configLIST_SIZE - 1 ; i++){
        __CPROVER_assume(arrayListItems[i].xItemValue == linkedListItems[i].xItemValue);
    }

    // Insert elements into the array-list
    for (UBaseType_t i = 0 ; i < numItems ; i++){
        vListInsertEnd(&arrayList,&arrayListItems[i]);
    }
    
    // Insert elements into the linked-list
    for (UBaseType_t i = 0 ; i < numItems ; i++){
        vold_ListInsertEnd(&linkedList,&linkedListItems[i]);
    }
    
    // Perform insertion on each list
    ListItem_t newArrayListItem;
    old_ListItem_t newLinkedListItem;
    __CPROVER_assume(newArrayListItem.xItemValue == newLinkedListItem.xItemValue);
    vListInsertEnd(&arrayList, &newArrayListItem);
    vold_ListInsertEnd(&linkedList, &newLinkedListItem);
   
    /* Assert equivalence:
     * 1) Same number of elements
     * 2) Same pxIndex value
     * 3) Same item-value for corresponding elements.
     */
    __CPROVER_assert(arrayList.uxNumberOfItems == linkedList.uxNumberOfItems,"Same number of elements");
    
    // Find the right number for the linked-list's pxIndex pointer
    // and compare it to the array-lists's pxIndex.
    UBaseType_t linkedListPxIndexNumber = 0;
    old_ListItem_t * temp = linkedList.xold_ListEnd.pxNext;  // set to head element.
    while (temp != linkedList.pxIndex){
        temp = temp->pxNext;
        linkedListPxIndexNumber++;
    }
    // special case where we are the end-marker item
    if (linkedList.uxNumberOfItems > 0 && temp == &linkedList.xold_ListEnd){     
        linkedListPxIndexNumber--;
    }
    __CPROVER_assert(arrayList.pxIndex == linkedListPxIndexNumber,"Same pxIndex value");
    

    // Compare the item-values of the two lists
    
    old_ListItem_t * linkedListPointer = linkedList.xold_ListEnd.pxNext;  // set to head element.
    UBaseType_t arrayListIndex = 0;
    while (arrayListIndex < arrayList.uxNumberOfItems){
        __CPROVER_assert(arrayList.xListData[arrayListIndex]->xItemValue == linkedListPointer->xItemValue,"Elements should be equal.");
        linkedListPointer = linkedListPointer->pxNext;
        arrayListIndex++;
    }
    
}