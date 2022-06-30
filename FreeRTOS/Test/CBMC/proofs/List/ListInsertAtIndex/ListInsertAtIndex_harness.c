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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "list.h"
#include "cbmc.h"

void harness()
{
    List_t pxList;
    vListInitialise(&pxList);
    
    // Non-deterministically add 0 to (maxElements-1) elements to the
    // list. (The -1 ensures that there is space to insert 1 more element)
    ListItem_t items[configLIST_SIZE-1];
    UBaseType_t numListElements = nondet_uint32();
    __CPROVER_assume( numListElements <= configLIST_SIZE - 1 );
    for (UBaseType_t i = 0; i < numListElements; i++)
    __CPROVER_assigns (i,__CPROVER_POINTER_OBJECT(pxList.xListData))
    __CPROVER_loop_invariant (i >= 0 && i <= numListElements)
    __CPROVER_decreases (numListElements - i)
    {
        pxList.xListData[i] = &items[i];
    }
    __CPROVER_assume( pxList.uxNumberOfItems == numListElements );

    // Finally add 1 item.
    ListItem_t newItem;
    UBaseType_t insertIndex;
    __CPROVER_assume( insertIndex < pxList.uxNumberOfItems );
    vListinsertAtIndex(&pxList, insertIndex, &newItem);
}

/*
 UBaseType_t numListElements;
    _CPROVER_assume( numListElements <= configLIST_SIZE - 1 );
    ListItem_t items[numListElements];
    for (UBaseType_t i = 0; i < numListElements ; i++){
        pxList.xListData[i] = &items[i];
    }
    _CPROVER_assume( pxList.uxNumberOfItems == numListElements );
*/