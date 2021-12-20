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


ListItem_t * choose( List_t * list );
/*@ requires DLS(&(list->xListEnd), ?endprev, &(list->xListEnd), endprev, ?cells, ?vals, ?container);@*/

/*@ ensures DLS(&(list->xListEnd), endprev, &(list->xListEnd), endprev, cells, vals, container) &*&
 *  mem(result, cells) == true;@*/

void vListInsert( List_t * const pxList,
                  ListItem_t * const pxNewListItem )

/*@requires xLIST(pxList, ?len, ?idx, ?end, ?cells, ?vals) &*&
 *  xLIST_ITEM(pxNewListItem, ?val, _, _, _);@*/

/*@ensures xLIST(pxList, len+1, idx, end, ?new_cells, ?new_vals) &*&
 *  remove(pxNewListItem, new_cells) == cells
 * ;@*/
{
    /*@xLIST_star_item(pxList, pxNewListItem);@*/
    /*@open xLIST_ITEM(pxNewListItem, _, _, _, _);@*/
    /*@open xLIST(pxList, len, idx, end, cells, vals);@*/
    /*@assert DLS(end, ?endprev, end, endprev, cells, vals, pxList);@*/
    ListItem_t * pxIterator;
    const TickType_t xValueOfInsertion = pxNewListItem->xItemValue;

    /* Only effective when configASSERT() is also defined, these tests may catch
     * the list data structures being overwritten in memory.  They will not catch
     * data errors caused by incorrect configuration or use of FreeRTOS. */
    listTEST_LIST_INTEGRITY( pxList );
    listTEST_LIST_ITEM_INTEGRITY( pxNewListItem );

    /* Insert the new list item into the list, sorted in xItemValue order.
     *
     * If the list already contains a list item with the same item value then the
     * new list item should be placed after it.  This ensures that TCBs which are
     * stored in ready lists (all of which have the same xItemValue value) get a
     * share of the CPU.  However, if the xItemValue is the same as the back marker
     * the iteration loop below will not end.  Therefore the value is checked
     * first, and the algorithm slightly modified if necessary. */
    if( xValueOfInsertion == portMAX_DELAY )
    {
        /*@open DLS(end, endprev, end, endprev, cells, vals, pxList);@*/
        /*@open xLIST_ITEM(end, portMAX_DELAY, ?endnext, endprev, pxList);@*/

        /*@
         * if (end != endprev)
         * {
         *  assert DLS(endnext, end, end, endprev, tail(cells), tail(vals), pxList);
         *  if (endnext == endprev)
         *  {
         *      // done
         *  }
         *  else
         *  {
         *      dls_last_mem(endnext, end, end, endprev, tail(cells));
         *      split(endnext, end, end, endprev, tail(cells), tail(vals), endprev, index_of(endprev, tail(cells)));
         *  }
         *  open DLS(endprev, _, _, _, _, _, _);
         *  open xLIST_ITEM(endprev, _, _, _, _);
         * }
         * @*/
        pxIterator = pxList->xListEnd.pxPrevious;
    }
    else
    {
        /* *** NOTE ***********************************************************
        *  If you find your application is crashing here then likely causes are
        *  listed below.  In addition see https://www.FreeRTOS.org/FAQHelp.html for
        *  more tips, and ensure configASSERT() is defined!
        *  https://www.FreeRTOS.org/a00110.html#configASSERT
        *
        *   1) Stack overflow -
        *      see https://www.FreeRTOS.org/Stacks-and-stack-overflow-checking.html
        *   2) Incorrect interrupt priority assignment, especially on Cortex-M
        *      parts where numerically high priority values denote low actual
        *      interrupt priorities, which can seem counter intuitive.  See
        *      https://www.FreeRTOS.org/RTOS-Cortex-M3-M4.html and the definition
        *      of configMAX_SYSCALL_INTERRUPT_PRIORITY on
        *      https://www.FreeRTOS.org/a00110.html
        *   3) Calling an API function from within a critical section or when
        *      the scheduler is suspended, or calling an API function that does
        *      not end in "FromISR" from an interrupt.
        *   4) Using a queue or semaphore before it has been initialised or
        *      before the scheduler has been started (are interrupts firing
        *      before vTaskStartScheduler() has been called?).
        **********************************************************************/

        #ifdef VERIFAST /*< ***over-approximate list insert loop*** */
            pxIterator = choose( pxList );
        #else
            for( pxIterator = ( ListItem_t * ) &( pxList->xListEnd ); pxIterator->pxNext->xItemValue <= xValueOfInsertion; pxIterator = pxIterator->pxNext ) /*lint !e826 !e740 !e9087 The mini list structure is used as the list end to save RAM.  This is checked and valid. *//*lint !e440 The iterator moves to a different value, not xValueOfInsertion. */
            {
                /* There is nothing to do here, just iterating to the wanted
                 * insertion position. */
            }
        #endif
        /*@int i = index_of(pxIterator, cells);@*/

        /*@
         * if (pxIterator == end)
         * {
         *  open DLS(end, endprev, end, endprev, cells, vals, pxList);
         *  open xLIST_ITEM(end, portMAX_DELAY, ?endnext, endprev, pxList);
         *  if (end != endprev)
         *  {
         *      assert DLS(endnext, end, end, endprev, tail(cells), tail(vals), pxList);
         *      open DLS(endnext, _, _, _, _, _, _);
         *      open xLIST_ITEM(endnext, _, _, _, _);
         *  }
         * }
         * else
         * {
         *  assert DLS(end, endprev, end, endprev, cells, vals, pxList);
         *  dls_first_mem(end, endprev, end, endprev, cells);
         *  assert pxIterator != end;
         *  assert index_of(end, cells) == 0;
         *  split(end, endprev, end, endprev, cells, vals, pxIterator, i);
         *  assert DLS(end, endprev, pxIterator, ?iterprev, take(i, cells), take(i, vals), pxList);
         *  assert DLS(pxIterator, iterprev, end, endprev, drop(i, cells), drop(i, vals), pxList);
         *  open DLS(pxIterator, iterprev, end, endprev, drop(i, cells), drop(i, vals), pxList);
         *  open xLIST_ITEM(pxIterator, _, ?iternext, iterprev, pxList);
         *  if (pxIterator == endprev)
         *  {
         *      open DLS(end, endprev, pxIterator, iterprev, take(i, cells), take(i, vals), pxList);
         *      take_take(1, i, vals);
         *      assert xLIST_ITEM(end, portMAX_DELAY, _, _, _);
         *      open xLIST_ITEM(iternext, _, _, pxIterator, _);
         *  }
         *  else
         *  {
         *      open DLS(iternext, pxIterator, end, endprev, _, _, _);
         *      open xLIST_ITEM(iternext, _, _, pxIterator, _);
         *  }
         * }@*/
    }

    pxNewListItem->pxNext = pxIterator->pxNext;
    pxNewListItem->pxNext->pxPrevious = pxNewListItem;
    pxNewListItem->pxPrevious = pxIterator;
    pxIterator->pxNext = pxNewListItem;

    /* Remember which list the item is in.  This allows fast removal of the
     * item later. */
    pxNewListItem->pxContainer = pxList;

    ( pxList->uxNumberOfItems )++;

    /*@close xLIST_ITEM(pxNewListItem, val, ?iternext, pxIterator, pxList);@*/
    /*@close xLIST_ITEM(pxIterator, ?iterval, pxNewListItem, ?iterprev, pxList);@*/

    /*@
     * if( xValueOfInsertion == portMAX_DELAY )
     * {
     *  assert iternext == end;
     *  assert pxIterator == endprev;
     *  if (end == endprev)
     *  {
     *      close DLS(end, pxNewListItem, pxNewListItem, end, cells, vals, pxList);
     *      close DLS(pxNewListItem, end, end, pxNewListItem, singleton(pxNewListItem), singleton(val), pxList);
     *      join(end, pxNewListItem, pxNewListItem, end, cells, vals,
     *          pxNewListItem, end, end, pxNewListItem, singleton(pxNewListItem), singleton(val));
     *      close xLIST(pxList, len+1, idx, end, append(cells, singleton(pxNewListItem)), append(vals, singleton(val)));
     *  }
     *  else
     *  {
     *      close xLIST_ITEM(end, portMAX_DELAY, ?endnext, pxNewListItem, pxList);
     *      close DLS(pxNewListItem, endprev, end, pxNewListItem, singleton(pxNewListItem), singleton(val), pxList);
     *      if (endnext == endprev)
     *      {
     *          assert xLIST_ITEM(endnext, ?endnextval, pxNewListItem, end, pxList);
     *          close DLS(end, pxNewListItem, endnext, end, singleton(end), singleton(portMAX_DELAY), pxList);
     *          close DLS(endnext, end, pxNewListItem, endnext, singleton(endnext), singleton(endnextval), pxList);
     *          join(end, pxNewListItem, endnext, end, singleton(end), singleton(portMAX_DELAY),
     *              endnext, end, pxNewListItem, endnext, singleton(endnext), singleton(endnextval));
     *          assert DLS(end, pxNewListItem, pxNewListItem, endnext, cells, vals, pxList);
     *      }
     *      else
     *      {
     *          assert DLS(endnext, end, endprev, ?endprevprev, ?cells_endnext_to_endprevprev, ?vals_endnext_to_endprevprev, pxList);
     *          assert cells_endnext_to_endprevprev == take(index_of(endprev, tail(cells)), tail(cells));
     *          assert index_of(endprev, tail(cells)) == length(tail(cells)) - 1;
     *          assert cells_endnext_to_endprevprev == take(length(tail(cells)) - 1, tail(cells));
     *          assert xLIST_ITEM(endprev, ?endprevval, pxNewListItem, endprevprev, pxList);
     *          close DLS(endprev, endprevprev, pxNewListItem, endprev, singleton(endprev), singleton(endprevval), pxList);
     *          dls_last_mem(endnext, end, endprev, endprevprev, cells_endnext_to_endprevprev);
     *          dls_star_item(endnext, endprevprev, end);
     *          close DLS(end, pxNewListItem, endprev, endprevprev, cons(end, cells_endnext_to_endprevprev), cons(portMAX_DELAY, vals_endnext_to_endprevprev), pxList);
     *          join(end, pxNewListItem, endprev, endprevprev, cons(end, cells_endnext_to_endprevprev), cons(portMAX_DELAY, vals_endnext_to_endprevprev),
     *              endprev, endprevprev, pxNewListItem, endprev, singleton(endprev), singleton(endprevval));
     *          assert DLS(end, pxNewListItem, pxNewListItem, endprev, cells, vals, pxList);
     *
     *      }
     *      join(end, pxNewListItem, pxNewListItem, endprev, cells, vals,
     *          pxNewListItem, endprev, end, pxNewListItem, singleton(pxNewListItem), singleton(val));
     *      remove_append(pxNewListItem, cells, singleton(pxNewListItem));
     *      close xLIST(pxList, len+1, idx, end, append(cells, singleton(pxNewListItem)), append(vals, singleton(val)));
     *  }
     * }
     * else
     * {
     *  if (pxIterator == end)
     *  {
     *      if (iternext == end)
     *      {
     *          close DLS(end, pxNewListItem, pxNewListItem, end, cells, vals, pxList);
     *          close DLS(pxNewListItem, pxIterator, end, pxNewListItem, singleton(pxNewListItem), singleton(val), pxList);
     *          join(end, pxNewListItem, pxNewListItem, end, cells, vals,
     *              pxNewListItem, pxIterator, end, pxNewListItem, singleton(pxNewListItem), singleton(val));
     *          close xLIST(pxList, len+1, idx, end, append(cells, singleton(pxNewListItem)), append(vals, singleton(val)));
     *      }
     *      else
     *      {
     *          close xLIST_ITEM(iternext, ?iternextval, _, pxNewListItem, pxList);
     *          if (iternext == endprev)
     *          {
     *              close DLS(iternext, pxNewListItem, end, endprev, singleton(iternext), singleton(iternextval), pxList);
     *              dls_last_mem(iternext, pxNewListItem, end, endprev, singleton(iternext));
     *          }
     *          else
     *          {
     *              assert DLS(?iternextnext, iternext, end, endprev, ?cells_iternextnext_to_endprev, ?vals_iternextnext_to_endprev, pxList);
     *              close DLS(iternext, pxNewListItem, end, endprev, cons(iternext, cells_iternextnext_to_endprev), cons(iternextval, vals_iternextnext_to_endprev), pxList);
     *              dls_last_mem(iternext, pxNewListItem, end, endprev, cons(iternext, cells_iternextnext_to_endprev));
     *          }
     *          close DLS(end, endprev, pxNewListItem, end, singleton(end), singleton(portMAX_DELAY), pxList);
     *          assert DLS(iternext, pxNewListItem, end, endprev, ?cells_iternext_to_endprev, ?vals_iternext_to_endprev, pxList);
     *          dls_star_item(iternext, endprev, pxNewListItem);
     *          close DLS(pxNewListItem, pxIterator, end, endprev, cons(pxNewListItem, cells_iternext_to_endprev), cons(val, vals_iternext_to_endprev), pxList);
     *          join(end, endprev, pxNewListItem, end, singleton(end), singleton(portMAX_DELAY),
     *              pxNewListItem, pxIterator, end, endprev, cons(pxNewListItem, cells_iternext_to_endprev), cons(val, vals_iternext_to_endprev));
     *          close xLIST(pxList, len+1, idx, end, cons(end, cons(pxNewListItem, cells_iternext_to_endprev)), cons(portMAX_DELAY, cons(val, vals_iternext_to_endprev)));
     *      }
     *  }
     *  else
     *  {
     *      close xLIST_ITEM(iternext, ?iternextval, _, pxNewListItem, pxList);
     *      if (pxIterator == endprev)
     *      {
     *          if (iterprev == end)
     *          {
     *              close DLS(end, pxNewListItem, pxIterator, end, singleton(end), singleton(portMAX_DELAY), pxList);
     *          }
     *          else
     *          {
     *              assert DLS(_, iternext, pxIterator, iterprev, ?cells1, ?vals1, _);
     *              close DLS(end, pxNewListItem, pxIterator, iterprev, cons(end, cells1), cons(portMAX_DELAY, vals1), pxList);
     *          }
     *          int i = index_of(pxIterator, cells);
     *          assert DLS(end, pxNewListItem, pxIterator, iterprev, take(i, cells), take(i, vals), pxList);
     *          close DLS(pxIterator, iterprev, pxNewListItem, pxIterator, drop(i, cells), drop(i, vals), pxList);
     *          close DLS(pxNewListItem, pxIterator, end, pxNewListItem, singleton(pxNewListItem), singleton(val), pxList);
     *          join(end, pxNewListItem, pxIterator, iterprev, take(i, cells), take(i, vals),
     *              pxIterator, iterprev, pxNewListItem, pxIterator, drop(i, cells), drop(i, vals));
     *          join(end, pxNewListItem, pxNewListItem, pxIterator, cells, vals,
     *              pxNewListItem, pxIterator, end, pxNewListItem, singleton(pxNewListItem), singleton(val));
     *          close xLIST(pxList, len+1, idx, end, append(cells, singleton(pxNewListItem)), append(vals, singleton(val)));
     *          remove_append(pxNewListItem, cells, singleton(pxNewListItem));
     *      }
     *      else
     *      {
     *          int i = index_of(pxIterator, cells);
     *          if (iternext == endprev)
     *          {
     *              close DLS(iternext, pxNewListItem, end, endprev, singleton(iternext), singleton(iternextval), pxList);
     *          }
     *          else
     *          {
     *              assert DLS(_, iternext, end, endprev, ?cells0, ?vals0, pxList);
     *              dls_star_item(end, iterprev, iternext);
     *              close DLS(iternext, pxNewListItem, end, endprev, tail(drop(i, cells)), tail(drop(i, vals)), pxList);
     *          }
     *          drop_drop(1, i, cells);
     *          drop_drop(1, i, vals);
     *          assert DLS(iternext, pxNewListItem, end, endprev, drop(i+1, cells), drop(i+1, vals), pxList);
     *          assert DLS(end, endprev, pxIterator, iterprev, take(i, cells), take(i, vals), pxList);
     *          dls_star_item(iternext, endprev, pxNewListItem);
     *          dls_last_mem(iternext, pxNewListItem, end, endprev, drop(i+1, cells));
     *          close DLS(pxNewListItem, pxIterator, end, endprev, cons(pxNewListItem, drop(i+1, cells)), cons(val, drop(i+1, vals)), pxList);
     *          close DLS(pxIterator, iterprev, end, endprev, cons(pxIterator, cons(pxNewListItem, drop(i+1, cells))), cons(iterval, cons(val, drop(i+1, vals))), pxList);
     *          join(end, endprev, pxIterator, iterprev, take(i, cells), take(i, vals),
     *              pxIterator, iterprev, end, endprev, cons(pxIterator, cons(pxNewListItem, drop(i+1, cells))), cons(iterval, cons(val, drop(i+1, vals))));
     *          list<struct xLIST_ITEM * >new_cells = append(take(i, cells), cons(pxIterator, cons(pxNewListItem, drop(i+1, cells))));
     *          list<TickType_t >new_vals = append(take(i, vals), cons(iterval, cons(val, drop(i+1, vals))));
     *          head_append(take(i, cells), cons(pxIterator, cons(pxNewListItem, drop(i+1, cells))));
     *          take_head(take(i, cells));
     *          take_take(1, i, cells);
     *          assert( end == head(new_cells) );
     *          head_append(take(i, vals), cons(iterval, cons(val, drop(i+1, vals))));
     *          take_head(take(i, vals));
     *          take_take(1, i, vals);
     *          assert( portMAX_DELAY == head(new_vals) );
     *          append_take_drop_n(cells, index_of(pxIterator, cells));
     *          close xLIST(pxList, len+1, idx, end, append(take(i, cells), cons(pxIterator, cons(pxNewListItem, drop(i+1, cells)))), append(take(i, vals), cons(iterval, cons(val, drop(i+1, vals)))));
     *          mem_take_false(pxNewListItem, i, cells);
     *          remove_append(pxNewListItem, take(i, cells), cons(pxIterator, cons(pxNewListItem, drop(i+1, cells))));
     *      }
     *  }
     * }@*/
}
