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

UBaseType_t uxListRemove( ListItem_t * const pxItemToRemove )
/*@requires
    exists<struct xLIST * >(?l) &*&
    xLIST(l, ?len, ?idx, ?end, ?cells, ?vals) &*&
    end != pxItemToRemove &*&
    mem(pxItemToRemove, cells) == true;@*/
/*@ensures
    result == len-1 &*&
    xLIST_ITEM(pxItemToRemove, nth(index_of(pxItemToRemove, cells), vals), _, ?pxItemToRemovePrevious, NULL) &*&
    pxItemToRemovePrevious == nth(index_of(pxItemToRemove, cells)-1, cells) &*&
    xLIST(l, result, idx == pxItemToRemove ? pxItemToRemovePrevious : idx,  end, remove(pxItemToRemove, cells), remove_nth(index_of(pxItemToRemove, cells), vals));@*/
{
    /* For brevity we alias x to pxItemToRemove */
    /*@struct xLIST_ITEM *x = pxItemToRemove;@*/

    /* Start by establishing that the list must be non-empty since x != end */
    /*@open xLIST(l, len, idx, end, cells, vals);@*/
    /*@assert DLS(end, ?endprev, end, _, cells, vals, l);@*/
    /*@assert vals == cons(portMAX_DELAY, _);@*/
    /*@dls_not_empty(end, endprev, cells, x);@*/

    /* We know the xLIST is a DLS: end...endprev
    Split this into DLS1:end...xprev and DLS2:x...endprev */
    /*@int i = index_of(x, cells);@*/
    /*@split(end, endprev, end, endprev, cells, vals, x, i);@*/
    /*@list<struct xLIST_ITEM *> ys = take(i, cells);@*/
    /*@list<struct xLIST_ITEM *> zs = drop(i, cells);@*/
    /*@list<TickType_t> vs = take(i, vals);@*/
    /*@list<TickType_t> ws = drop(i, vals);@*/
    /*@assert length(ys) == length(vs);@*/
    /*@assert length(zs) == length(ws);@*/
    /*@assert DLS(end, endprev, x, ?xprev, ys, vs, l);@*/ /*< DLS1 (ys, vs) */
    /*@assert DLS(x, xprev, end, endprev, zs, ws, l);@*/  /*< DLS2 (zs, ws) */

    /* Now case split to open DLS1 and DLS2 appropriately */
    /*@
    if (end == xprev)
    {
        if (x == endprev)
        {
            //Case A
            //DLS1: extract end=prev=next
            open DLS(end, endprev, x, xprev, ys, vs, l);
            open xLIST_ITEM(end, portMAX_DELAY, x, endprev, l);
            //DLS2: extract x
            open DLS(x, xprev, end, endprev, zs, ws, l);
            //Lengths
            assert length(ys) == 1;
            assert length(zs) == 1;
        }
        else
        {
            //Case B
            //DLS1: extract end=prev
            open DLS(end, endprev, x, xprev, ys, vs, l);
            open xLIST_ITEM(end, portMAX_DELAY, x, endprev, l);
            //DLS2: extract next and x
            open DLS(x, end, end, endprev, zs, ws, l);
            assert DLS(?xnext, x, end, endprev, tail(zs), tail(ws), l);
            open DLS(xnext, x, end, endprev, tail(zs), tail(ws), l);
            open xLIST_ITEM(xnext, _, _, x, l);
            //Lengths
            assert length(ys) == 1;
        }
    }
    else
    {
        if (x == endprev)
        {
            //Case C
            //DLS1: extract end=next and prev
            dls_last_mem(end, endprev, x, xprev, ys);
            assert mem(xprev, ys) == true;
            open DLS(end, endprev, x, xprev, ys, vs, l);
            open xLIST_ITEM(end, portMAX_DELAY, ?endnext, endprev, l);
            if (endnext == xprev)
            {
                open DLS(endnext, end, x, xprev, tail(ys), tail(vs), l);
                open xLIST_ITEM(xprev, _, x, _, l);
            }
            else
            {
                assert DLS(endnext, end, x, xprev, tail(ys), tail(vs), l);
                int k = index_of(xprev, tail(ys));
                dls_last_mem(endnext, end, x, xprev, tail(ys));
                split(endnext, end, x, xprev, tail(ys), tail(vs), xprev, k);
                open DLS(xprev, _, x, xprev, _, _, l);
                open xLIST_ITEM(xprev, _, x, _, l);
            }
            //DLS2: extract x
            open DLS(x, xprev, end, endprev, zs, ws, l);
            //Lengths
            assert length(zs) == 1;
        }
        else
        {
            //Case D
            //DLS1: extract prev
            dls_last_mem(end, endprev, x, xprev, ys);
            int j = index_of(xprev, ys);
            open DLS(end, endprev, x, xprev, ys, vs, l);
            open xLIST_ITEM(end, portMAX_DELAY, ?endnext, endprev, l);
            if (endnext == xprev)
            {
                open DLS(endnext, end, x, xprev, tail(ys), tail(vs), l);
                assert tail(ys) == singleton(xprev);
                open xLIST_ITEM(xprev, _, x, _, l);
            }
            else
            {
                assert DLS(endnext, end, x, xprev, tail(ys), tail(vs), l);
                int k = index_of(xprev, tail(ys));
                dls_last_mem(endnext, end, x, xprev, tail(ys));
                split(endnext, end, x, xprev, tail(ys), tail(vs), xprev, k);
                open DLS(xprev, _, x, xprev, _, _, l);
                open xLIST_ITEM(xprev, _, x, _, l);
            }
            //DLS2: extract next and x
            open DLS(x, xprev, end, endprev, zs, ws, l);
            assert xLIST_ITEM(x, _, ?xnext, _, l);
            open DLS(xnext, x, end, endprev, tail(zs), tail(ws), l);
            open xLIST_ITEM(xnext, _, _, x, l);
        }
    }
    @*/
    /*@drop_nth_index_of(vals, i);@*/
    /*@open xLIST_ITEM(x, nth(i, vals), ?xnext, xprev, l);@*/

/* The list item knows which list it is in.  Obtain the list from the list
 * item. */
#ifdef VERIFAST /*< const pointer declaration */
    List_t * pxList = pxItemToRemove->pxContainer;
#else
    List_t * const pxList = pxItemToRemove->pxContainer;
#endif

    pxItemToRemove->pxNext->pxPrevious = pxItemToRemove->pxPrevious;
    pxItemToRemove->pxPrevious->pxNext = pxItemToRemove->pxNext;

    /* Only used during decision coverage testing. */
    mtCOVERAGE_TEST_DELAY();

    /* Make sure the index is left pointing to a valid item. */
    if( pxList->pxIndex == pxItemToRemove )
    {
        pxList->pxIndex = pxItemToRemove->pxPrevious;
    }
    else
    {
        mtCOVERAGE_TEST_MARKER();
    }

    pxItemToRemove->pxContainer = NULL;
    ( pxList->uxNumberOfItems )--;

    return pxList->uxNumberOfItems;

    /*@
    // Reassemble DLS1 and a modified DLS2, which no longer includes x
    if (end == xprev)
    {
        if (x == endprev)
        {
            //Case A
            close xLIST_ITEM(end, portMAX_DELAY, _, _, _);
            close DLS(end, end, end, end, singleton(end), singleton(portMAX_DELAY), l);
        }
        else
        {
            //Case B
            close xLIST_ITEM(xprev, _, xnext, endprev, l);
            close DLS(end, endprev, xnext, xprev, singleton(end), singleton(portMAX_DELAY), l);
            close xLIST_ITEM(xnext, _, _, xprev, l);
            close DLS(xnext, xprev, end, endprev, tail(zs), tail(ws), l);
            join(end, endprev, xnext, xprev, singleton(end), singleton(portMAX_DELAY),
                 xnext, xprev, end, endprev, tail(zs), tail(ws));
        }
    }
    else
    {
        if (x == endprev)
        {
            //Case C
            close xLIST_ITEM(end, _, ?endnext, xprev, l);
            close xLIST_ITEM(xprev, ?xprev_val, end, _, l);
            if (endnext == xprev)
            {
                close DLS(xprev, end, end, xprev, singleton(xprev), singleton(xprev_val), l);
                close DLS(end, xprev, end, xprev, cons(end, singleton(xprev)), cons(portMAX_DELAY, singleton(xprev_val)), l);
            }
            else
            {
                close DLS(xprev, ?xprevprev, xnext, xprev, singleton(xprev), singleton(xprev_val), l);
                assert DLS(endnext, end, xprev, xprevprev, ?cells_endnext_to_xprevprev, ?vals_endnext_to_xprevprev, l);
                join(endnext, end, xprev, xprevprev, cells_endnext_to_xprevprev, vals_endnext_to_xprevprev,
                     xprev, xprevprev, xnext, xprev, singleton(xprev), singleton(xprev_val));
                close DLS(end, xprev, end, xprev, ys, vs, l);
            }
        }
        else
        {
            //Case D
            close xLIST_ITEM(xnext, _, ?xnextnext, xprev, l);
            close DLS(xnext, xprev, end, endprev, tail(zs), tail(ws), l);
            close xLIST_ITEM(end, _, ?endnext, endprev, l);
            close xLIST_ITEM(xprev, ?xprev_val, xnext, _, l);
            if (endnext == xprev)
            {
                close DLS(xprev, _, xnext, xprev, singleton(xprev), singleton(xprev_val), l);
                close DLS(end, endprev, xnext, xprev, ys, vs, l);
                join(end, endprev, xnext, xprev, ys, vs,
                     xnext, xprev, end, endprev, tail(zs), tail(ws));
            }
            else
            {
                close DLS(xprev, ?xprevprev, xnext, xprev, singleton(xprev), singleton(xprev_val), l);
                assert DLS(endnext, end, xprev, xprevprev, ?cells_endnext_to_xprevprev, ?vals_endnext_to_xprevprev, l);
                join(endnext, end, xprev, xprevprev, cells_endnext_to_xprevprev, vals_endnext_to_xprevprev,
                     xprev, xprevprev, xnext, xprev, singleton(xprev), singleton(xprev_val));
                close DLS(end, endprev, xnext, xprev, ys, vs, l);
                join(end, endprev, xnext, xprev, ys, vs,
                     xnext, xprev, end, endprev, tail(zs), tail(ws));
            }
        }
    }
    @*/
    /*@remove_remove_nth(cells, x);@*/
    /*@
    if (idx == x)
    {
        close xLIST(l, len-1, xprev, end, append(ys, tail(zs)), append(vs, tail(ws)));
    }
    else
    {
        idx_remains_in_list(cells, idx, x, i);
        close xLIST(l, len-1, idx, end, append(ys, tail(zs)), append(vs, tail(ws)));
    }
    @*/
    /*@close xLIST_ITEM(x, nth(i, vals), xnext, xprev, NULL);@*/
}

ListItem_t * client_example( List_t * l )
/*@requires
    xLIST(l, ?len, ?idx, ?end, ?cells, ?vals) &*&
    idx != end &*&
    cells == cons(end, cons(idx, ?cells_tl)) &*&
    vals == cons(portMAX_DELAY, cons(42, ?vals_tl));@*/
/*@ensures
    xLIST(l, len - 1, _, end, cons(end, cells_tl), cons(portMAX_DELAY, vals_tl)) &*&
    xLIST_ITEM(result, 42, _, _, NULL);@*/
{
    /*@open xLIST(l, len, idx, end, cells, vals);@*/
    ListItem_t *index = l->pxIndex;
    /*@close xLIST(l, len, idx, end, cells, vals);@*/
    /*@close exists(l);@*/
    uxListRemove( index );
    return index;
}

void client_example2( List_t * l )
/*@requires
    xLIST(l, ?len, ?idx, ?end, ?cells, ?vals) &*&
    cells == cons(end, cons(?x1, cons(?x2, ?cells_tl))) &*&
    idx == x2 &*&
    vals == cons(portMAX_DELAY, cons(1, cons(2, ?vals_tl)));@*/
/*@ensures
    xLIST(l, len-2, end, end, cons(end, cells_tl), cons(portMAX_DELAY, vals_tl)) &*&
    xLIST_ITEM(_, 1, _, _, NULL) &*&
    xLIST_ITEM(_, 2, _, _, NULL);@*/
{
    /*@xLIST_distinct_cells(l);@*/
    /*@open xLIST(l, len, idx, end, cells, vals);@*/
    ListItem_t *index = l->pxIndex;
    /*@close xLIST(l, len, idx, end, cells, vals);@*/
    /*@close exists(l);@*/
    uxListRemove( index );
    /*@open xLIST(l, len-1, x1, end, cons(end, cons(x1, cells_tl)), cons(portMAX_DELAY, cons(1, vals_tl)));@*/
    index = l->pxIndex;
    /*@close xLIST(l, len-1, x1, end, cons(end, cons(x1, cells_tl)), cons(portMAX_DELAY, cons(1, vals_tl)));@*/
    /*@close exists(l);@*/
    uxListRemove( index );
}
