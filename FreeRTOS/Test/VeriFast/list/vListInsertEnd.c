/*
 * FreeRTOS V202012.00
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
 */

#include "proof/list.h"

void vListInsertEnd( List_t * const pxList,
                     ListItem_t * const pxNewListItem )
/*@requires xLIST(pxList, ?len, ?idx, ?end, ?cells, ?vals) &*&
    xLIST_ITEM(pxNewListItem, ?val, _, _, _);@*/
/*@ensures xLIST(pxList, len+1, idx, end, ?new_cells, ?new_vals) &*&
    idx == end
        ? (new_cells == append(cells, singleton(pxNewListItem)) &*&
            new_vals == append(vals, singleton(val)))
        : (new_cells == append(take(index_of(idx, cells), cells), append(singleton(pxNewListItem), drop(index_of(idx, cells), cells))) &*&
            new_vals == append(take(index_of(idx, cells), vals), append(singleton(val), drop(index_of(idx, cells), vals))));@*/
{
    /*@xLIST_star_item(pxList, pxNewListItem);@*/
    /*@assert mem(pxNewListItem, cells) == false;@*/
    /*@open xLIST(pxList, len, idx, end, cells, vals);@*/
#ifdef VERIFAST /*< const pointer declaration */
    ListItem_t * pxIndex = pxList->pxIndex;
#else
    ListItem_t * const pxIndex = pxList->pxIndex;

    /* Only effective when configASSERT() is also defined, these tests may catch
     * the list data structures being overwritten in memory.  They will not catch
     * data errors caused by incorrect configuration or use of FreeRTOS. */
    listTEST_LIST_INTEGRITY( pxList );
    listTEST_LIST_ITEM_INTEGRITY( pxNewListItem );
#endif

    /*@open xLIST_ITEM(pxNewListItem, _, _, _, _);@*/
    /*@assert DLS(end, ?endprev, end, _, cells, vals, pxList);@*/
    /*@dls_first_mem(end, endprev, end, endprev, cells);@*/
    /*@dls_last_mem(end, endprev, end, endprev, cells);@*/
    /*@
    if (end == idx)
    {
        open DLS(end, endprev, end, endprev, cells, vals, pxList);
        open xLIST_ITEM(end, portMAX_DELAY, ?endnext, endprev, pxList);
        if (end == endprev)
        {
            // Case A (singleton): idx==end==endprev
        }
        else
        {
            assert DLS(endnext, end, end, endprev, tail(cells), tail(vals), pxList);
            if (endnext == endprev)
            {
                // Case B (two): idx==end and endnext==endprev
                open DLS(endnext, end, end, endnext, _, _, _);
                open xLIST_ITEM(endnext, _, _, _, _);
            }
            else
            {
                // Case C: idx==end and DLS:endnext...endprev
                split(endnext, end, end, endprev, tail(cells), tail(vals), endprev, index_of(endprev, tail(cells)));
                open DLS(endprev, _, _, _, _, _, _);
                open xLIST_ITEM(endprev, _, _, _, _);
            }
        }
    }
    else
    {
        int i = index_of(idx, cells);
        split(end, endprev, end, endprev, cells, vals, idx, i);
        assert DLS(end, endprev, idx, ?idxprev, take(i, cells), take(i, vals), pxList);
        assert DLS(idx, idxprev, end, endprev, drop(i, cells), drop(i, vals), pxList);
        open DLS(idx, idxprev, end, endprev, _, _, _);
        open xLIST_ITEM(idx, _, _, _, _);
        if (end == idxprev)
        {
            // Case D: end==idxprev and DLS:idx...endprev
            take_take(1, i, vals);
            take_head(vals);
            open DLS(end, endprev, idx, idxprev, take(i, cells), take(i, vals), pxList);
            open xLIST_ITEM(end, portMAX_DELAY, _, _, _);
            assert length(take(i, cells)) == 1;
        }
        else
        {
            // Case E: DLS:end...idxprev and DLS:idx...endprev
            dls_last_mem(end, endprev, idx, idxprev, take(i, cells));
            split(end, endprev, idx, idxprev, take(i, cells), take(i, vals), idxprev, index_of(idxprev, take(i, cells)));
            open DLS(idxprev, _, _, idxprev, _, _, _);
            length_take(i, cells);
            drop_take_singleton(i, vals);
            open xLIST_ITEM(idxprev, nth(i-1, vals), _, _, _);
        }
    }
    @*/

    /* Insert a new list item into pxList, but rather than sort the list,
     * makes the new list item the last item to be removed by a call to
     * listGET_OWNER_OF_NEXT_ENTRY(). */
    pxNewListItem->pxNext = pxIndex;
    pxNewListItem->pxPrevious = pxIndex->pxPrevious;

    /* Only used during decision coverage testing. */
    mtCOVERAGE_TEST_DELAY();

    pxIndex->pxPrevious->pxNext = pxNewListItem;
    pxIndex->pxPrevious = pxNewListItem;

    /* Remember which list the item is in. */
    pxNewListItem->pxContainer = pxList;

    ( pxList->uxNumberOfItems )++;

    /*@
    if (end == idx)
    {
        close xLIST_ITEM(pxNewListItem, val, end, endprev, pxList);
        close DLS(pxNewListItem, endprev, end, pxNewListItem, singleton(pxNewListItem), singleton(val), pxList);
        close xLIST_ITEM(end, portMAX_DELAY, ?endnext, pxNewListItem, pxList);
        if (end == endprev)
        {
            // Case A (singleton): idx==end==endprev
            close DLS(end, pxNewListItem, endnext, end, cells, vals, pxList);
            join(end, pxNewListItem, endnext, end, cells, vals,
                pxNewListItem, endprev, end, pxNewListItem, singleton(pxNewListItem), singleton(val));
            close xLIST(pxList, len+1, idx, end, append(cells, singleton(pxNewListItem)), append(vals, singleton(val)));
        }
        else
        {
            close xLIST_ITEM(endprev, ?endprevval, pxNewListItem, ?endprevprev, _);
            if (endnext == endprev)
            {
                // Case B (two): idx==end and endnext==endprev
                close DLS(endprev, end, pxNewListItem, endprev, singleton(endprev), singleton(endprevval), pxList);
                close DLS(end, pxNewListItem, pxNewListItem, endprev, cells, vals, pxList);
                join(end, pxNewListItem, pxNewListItem, endprev, cells, vals,
                    pxNewListItem, endprev, end, pxNewListItem, singleton(pxNewListItem), singleton(val));
                close xLIST(pxList, len+1, idx, end, append(cells, singleton(pxNewListItem)), append(vals, singleton(val)));
            }
            else
            {
                // Case C: idx==end and DLS:endnext...endprev
                close DLS(endprev, endprevprev, pxNewListItem, endprev, singleton(endprev), singleton(endprevval), pxList);
                assert DLS(endnext, end, endprev, endprevprev, ?cells_endnext_to_endprevprev, ?vals_endnext_to_endprevprev, pxList);
                join(endnext, end, endprev, endprevprev, cells_endnext_to_endprevprev, vals_endnext_to_endprevprev,
                     endprev, endprevprev, pxNewListItem, endprev, singleton(endprev), singleton(endprevval));
                close DLS(end, pxNewListItem, pxNewListItem, endprev, cells, vals, pxList);
                join(end, pxNewListItem, pxNewListItem, endprev, cells, vals,
                     pxNewListItem, endprev, end, pxNewListItem, singleton(pxNewListItem), singleton(val));
                close xLIST(pxList, len+1, idx, end, append(cells, singleton(pxNewListItem)), append(vals, singleton(val)));
            }
        }
    }
    else
    {
        // Case D: end==idxprev and DLS:idx...endprev
        // Case E: DLS:end...idxprev and DLS:idx...endprev
        int i = index_of(idx, cells);
        close xLIST_ITEM(pxNewListItem, val, idx, ?idxprev, pxList);
        close xLIST_ITEM(idx, ?idxval, ?idxnext, pxNewListItem, pxList);
        nth_drop2(vals, i);
        assert idxval == nth(i, vals);
        close xLIST_ITEM(idxprev, ?idxprevval, pxNewListItem, ?idxprevprev, pxList);

        if (end == idxprev)
        {
            close DLS(end, endprev, pxNewListItem, end, singleton(end), singleton(portMAX_DELAY), pxList);
        }
        else
        {
            length_take(i, cells);
            take_take(i-1, i, vals);
            take_singleton(i-1, vals);
            take_singleton(i, vals);
            assert DLS(end, endprev, idxprev, idxprevprev, ?cells_end_to_idxprevprev, take(i-1, vals), pxList);
            close DLS(idxprev, idxprevprev, pxNewListItem, idxprev, singleton(idxprev), singleton(idxprevval), pxList);
            join(end, endprev, idxprev, idxprevprev, cells_end_to_idxprevprev, take(i-1, vals),
                 idxprev, idxprevprev, pxNewListItem, idxprev, singleton(idxprev), singleton(idxprevval));
        }

        if (idx == endprev)
        {
            close DLS(idx, pxNewListItem, end, idx, singleton(idx), singleton(idxval), pxList);
        }
        else
        {
            assert DLS(end, endprev, pxNewListItem, idxprev, ?cells_end_to_idxprev, ?vals_end_to_idxprev, pxList);
            close DLS(idx, pxNewListItem, end, endprev, drop(i, cells), drop(i, vals), pxList);
        }

        assert DLS(end, endprev, pxNewListItem, idxprev, take(i, cells), take(i, vals), pxList);
        assert DLS(idx, pxNewListItem, end, endprev, drop(i, cells), drop(i, vals), pxList);
        assert xLIST_ITEM(pxNewListItem, val, idx, idxprev, pxList);
        dls_star_item(idx, endprev, pxNewListItem);
        close DLS(pxNewListItem, idxprev, end, endprev, cons(pxNewListItem, drop(i, cells)), cons(val, drop(i, vals)), pxList);
        join(end, endprev, pxNewListItem, idxprev, take(i, cells), take(i, vals),
             pxNewListItem, idxprev, end, endprev, cons(pxNewListItem, drop(i, cells)), cons(val, drop(i, vals)));
        assert DLS(end, endprev, end, endprev, ?cells_new, ?vals_new, pxList);
        assert cells_new == append(take(i, cells), append(singleton(pxNewListItem), drop(i, cells)));
        assert vals_new == append(take(i, vals) , append(singleton(val), drop(i, vals)));
        head_append(take(i, cells), append(singleton(pxNewListItem), drop(i, cells)));
        take_take(1, i, cells);
        head_append(take(i, vals), append(singleton(val), drop(i, vals)));
        take_take(1, i, vals);
        close xLIST(pxList, len+1, idx, end, cells_new, vals_new);
    }
    @*/
}

void client_example1( List_t * const l, ListItem_t * const pxNewListItem )
/*@requires
    xLIST(l, ?len, ?idx, ?end, ?cells, ?vals) &*&
    xLIST_ITEM(pxNewListItem, ?val, _, _, _) &*&
    idx == end;@*/
/*@ensures
    xLIST(l, len + 1, idx, end, _, append(vals, singleton(val)));@*/
{
    vListInsertEnd(l, pxNewListItem);
}
