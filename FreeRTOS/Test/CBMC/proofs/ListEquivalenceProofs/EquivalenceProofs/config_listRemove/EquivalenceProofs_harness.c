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


ListItem_t arrayListItems[configLIST_SIZE - 1];
old_ListItem_t linkedListItems[configLIST_SIZE - 1];

void setupLists(List_t* aList, old_List_t* lList)
{
    // Initialize the lists
    vListInitialise(aList);
    vold_ListInitialise(lList);

    // Set a non-deterministic list size
    UBaseType_t numItems;
    __CPROVER_assume(numItems <= configLIST_SIZE - 1);
    aList->uxNumberOfItems = numItems;
    lList->uxNumberOfItems = numItems;

    // Set the same elements for the array-list and linked-list
    for (UBaseType_t i = 0 ; i < configLIST_SIZE - 1 ; i++){
        __CPROVER_assume(arrayListItems[i].xItemValue == linkedListItems[i].xItemValue);
    }

    // Insert elements into the array-list.
    for (UBaseType_t i = 0 ; i < aList->uxNumberOfItems ; i++){
        aList->xListData[i] = &(arrayListItems[i]);
        aList->xListData[i]->pxContainer = aList;
    }
    
    // Insert elements into the linked-list
    old_ListItem_t * temp  = &(lList->xold_ListEnd);
    for (UBaseType_t i = 0 ; i < lList->uxNumberOfItems ; i++){
        temp->pxNext = &(linkedListItems[i]);
        linkedListItems[i].pxPrevious = temp;
        linkedListItems[i].pxContainer = lList;
        temp = temp->pxNext;
    }
    temp->pxNext = &(lList->xold_ListEnd);  // complete the final links.
    lList->xold_ListEnd.pxPrevious = temp;
    
    // Set the pxIndex for both lists as some non-deterministic element.
    UBaseType_t pxIndexValue;
    __CPROVER_assume(pxIndexValue < aList->uxNumberOfItems);
    lList->pxIndex = &(linkedListItems[pxIndexValue]);
    aList->pxIndex = pxIndexValue;
}


/* Linked list and array-list are equivalent if:
 * 1) Same number of elements
 * 2) Same pxIndex value
 * 3) Same item-value for corresponding elements.
 * [ These are the properties visible to outside functions]
 */
void assertEquivalence(List_t* aList, old_List_t* lList)
{
    // same number of elements for both lists.
    __CPROVER_assert(aList->uxNumberOfItems == lList->uxNumberOfItems,"Same number of elements");
    
    // Find the right number for the linked-list's pxIndex pointer
    // and compare it to the array-lists's pxIndex.
    UBaseType_t linkedListPxIndexNumber = 0;
    old_ListItem_t * temp = lList->xold_ListEnd.pxNext;  // set to head element.
    while (temp != lList->pxIndex){
        temp = temp->pxNext;
        linkedListPxIndexNumber++;
    }
    // special case where we are the end-marker item
    if (lList->uxNumberOfItems > 0 && temp == &(lList->xold_ListEnd)){     
        linkedListPxIndexNumber--;
    }
    __CPROVER_assert(aList->pxIndex == linkedListPxIndexNumber,"Same pxIndex value");
    

    // Compare the item-values of the two lists
    old_ListItem_t * linkedListPointer = lList->xold_ListEnd.pxNext;  // set to head element.
    UBaseType_t arrayListIndex = 0;
    while (arrayListIndex < aList->uxNumberOfItems){
        __CPROVER_assert(aList->xListData[arrayListIndex]->xItemValue == linkedListPointer->xItemValue,"Elements should be equal.");
        linkedListPointer = linkedListPointer->pxNext;
        arrayListIndex++;
    }
    
}

void harness()
{
    /* PART 1: INITIALIZE AN EQUIVALENT ARRAY AND LINKED LIST */
    List_t arrayList;
    old_List_t linkedList;
    setupLists(&arrayList, &linkedList);

    /* PART 2: PERFORM THE OPERATION ON EACH LIST */
    ListItem_t newArrayListItem;
    old_ListItem_t newLinkedListItem;
    __CPROVER_assume(newArrayListItem.xItemValue == newLinkedListItem.xItemValue);
#ifdef USE_LIST_INSERT
    vListInsert(&arrayList, &newArrayListItem);
    vold_ListInsert(&linkedList, &newLinkedListItem);
#endif
#ifdef USE_LIST_INSERT_END
    vListInsertEnd(&arrayList, &newArrayListItem);
    vold_ListInsertEnd(&linkedList, &newLinkedListItem);
#endif
#ifdef USE_LIST_REMOVE
    UBaseType_t removalIndex;
    __CPROVER_assume(removalIndex < arrayList.uxNumberOfItems);
    uxListRemove(&(arrayListItems[removalIndex]));
    uxold_ListRemove(&(linkedListItems[removalIndex]));
#endif

    /* PART 3: ASSERT EQUILVALENCE */
    assertEquivalence(&arrayList, &linkedList);
}