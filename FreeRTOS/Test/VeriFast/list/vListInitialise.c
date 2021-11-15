/*
 * FreeRTOS V202111.00
 * Copyright (C) Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#include "proof/list.h"

/*@
 * predicate xLIST_uninitialised(struct xLIST *l) =
 *  l->uxNumberOfItems |-> _ &*&
 *  l->pxIndex |-> _ &*&
 *  l->xListEnd.xItemValue |-> _ &*&
 *  l->xListEnd.pxNext |-> _ &*&
 *  l->xListEnd.pxPrevious |-> _ &*&
 *  l->xListEnd.pvOwner |-> _ &*&
 *  l->xListEnd.pxContainer |-> _ &*&
 *  struct_xLIST_ITEM_padding(&l->xListEnd);
 * @*/

void vListInitialise( List_t * const pxList )
/*@requires xLIST_uninitialised(pxList);@*/
/*@ensures xLIST(pxList, 0, ?end, end, singleton(end), singleton(portMAX_DELAY));@*/
{
    /*@open xLIST_uninitialised(pxList);@*/

    /* The list structure contains a list item which is used to mark the
     * end of the list.  To initialise the list the list end is inserted
     * as the only list entry. */
    pxList->pxIndex = ( ListItem_t * ) &( pxList->xListEnd ); /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. */

    /* The list end value is the highest possible value in the list to
     * ensure it remains at the end of the list. */
    pxList->xListEnd.xItemValue = portMAX_DELAY;

    /* The list end next and previous pointers point to itself so we know
     * when the list is empty. */
    pxList->xListEnd.pxNext = ( ListItem_t * ) &( pxList->xListEnd );     /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. */
    pxList->xListEnd.pxPrevious = ( ListItem_t * ) &( pxList->xListEnd ); /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. */

    pxList->uxNumberOfItems = ( UBaseType_t ) 0U;

    /* Write known values into the list if
     * configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES is set to 1. */
    listSET_LIST_INTEGRITY_CHECK_1_VALUE( pxList );
    listSET_LIST_INTEGRITY_CHECK_2_VALUE( pxList );

    #ifdef VERIFAST /*< ***change MiniList_t to ListItem_t*** */
        pxList->xListEnd.pxContainer = pxList;
    #endif
    /*@ListItem_t *end = &(pxList->xListEnd);@*/
    /*@close xLIST_ITEM(end, portMAX_DELAY, _, _, pxList);@*/
    /*@close DLS(end, end, end, end, singleton(end), singleton(portMAX_DELAY), pxList);@*/
    /*@close xLIST(pxList, 0, end, end, singleton(end), singleton(portMAX_DELAY));@*/
}
