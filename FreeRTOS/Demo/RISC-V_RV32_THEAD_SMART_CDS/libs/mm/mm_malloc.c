/****************************************************************************
 * mm/mm_heap/mm_malloc.c
 *
 *   Copyright (C) 2007, 2009, 2013-2014  Gregory Nutt. All rights reserved.
 *   Author: Gregory Nutt <gnutt@nuttx.org>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 * 3. Neither the name NuttX nor the names of its contributors may be
 *    used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS
 * OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED
 * AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 ****************************************************************************/

/****************************************************************************
 * Included Files
 ****************************************************************************/

#include <csi_config.h>

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include "mm.h"

/****************************************************************************
 * Pre-processor Definitions
 ****************************************************************************/
#define THIS_MODULE MODULE_MEM_HEAP

#ifndef NULL
#  define NULL ((void *)0)
#endif

/****************************************************************************
 * Public Function Prototypes
 ****************************************************************************/

extern void mm_leak_dump(void);
void mm_record_minfree(void);

/****************************************************************************
 * Type Definitions
 ****************************************************************************/

/****************************************************************************
 * Private Data
 ****************************************************************************/

/****************************************************************************
 * Public Data
 ****************************************************************************/

/****************************************************************************
 * Private Functions
 ****************************************************************************/

/****************************************************************************
 * Public Functions
 ****************************************************************************/
/****************************************************************************
 * Name: mm_malloc
 *
 * Description:
 *  Find the smallest chunk that satisfies the request. Take the memory from
 *  that chunk, save the remaining, smaller chunk (if any).
 *
 *  8-byte alignment of the allocated data is assured.
 *
 ****************************************************************************/

void *mm_malloc(struct mm_heap_s *heap, size_t size, void *caller)
{
  struct mm_freenode_s *node;
  void *ret = NULL;
  int ndx;
#if defined(CONFIG_MM_DETECT_ERROR)
  size_t real_size;
#endif

  /* Handle bad sizes */

  if (size < 1)
    {
      return NULL;
    }

#if defined(CONFIG_MM_DETECT_ERROR)
  size = (size + 3) & ~3;
  real_size = size;
  size += MDBG_SZ_HEAD + MDBG_SZ_TAIL;
#endif

  /* Adjust the size to account for (1) the size of the allocated node and
   * (2) to make sure that it is an even multiple of our granule size.
   */

  size = MM_ALIGN_UP(size + SIZEOF_MM_ALLOCNODE);

  /* We need to hold the MM semaphore while we muck with the nodelist. */

  mm_takesemaphore(heap);

  /* Get the location in the node list to start the search. Special case
   * really big allocations
   */

  if (size >= MM_MAX_CHUNK)
    {
      ndx = MM_NNODES-1;
    }
  else
    {
      /* Convert the request size into a nodelist index */

      ndx = mm_size2ndx(size);
    }

  /* Search for a large enough chunk in the list of nodes. This list is
   * ordered by size, but will have occasional zero sized nodes as we visit
   * other mm_nodelist[] entries.
   */

  for (node = heap->mm_nodelist[ndx].flink;
       node && node->size < size;
       node = node->flink);

  /* If we found a node with non-zero size, then this is one to use. Since
   * the list is ordered, we know that is must be best fitting chunk
   * available.
   */

  if (node)
    {
      struct mm_freenode_s *remainder;
      struct mm_freenode_s *next;
      size_t remaining;

      /* Remove the node.  There must be a predecessor, but there may not be
       * a successor node.
       */

      //DEBUGASSERT(node->blink);
      node->blink->flink = node->flink;
      if (node->flink)
        {
          node->flink->blink = node->blink;
        }

      /* Check if we have to split the free node into one of the allocated
       * size and another smaller freenode.  In some cases, the remaining
       * bytes can be smaller (they may be SIZEOF_MM_ALLOCNODE).  In that
       * case, we will just carry the few wasted bytes at the end of the
       * allocation.
       */

      remaining = node->size - size;
      if (remaining >= SIZEOF_MM_FREENODE)
        {
          /* Get a pointer to the next node in physical memory */

          next = (struct mm_freenode_s *)(((char *)node) + node->size);

          /* Create the remainder node */

          remainder = (struct mm_freenode_s *)(((char *)node) + size);
          remainder->size = remaining;
          remainder->preceding = size;

          /* Adjust the size of the node under consideration */

          node->size = size;

          /* Adjust the 'preceding' size of the (old) next node, preserving
           * the allocated flag.
           */

          next->preceding = remaining | (next->preceding & MM_ALLOC_BIT);

          /* Add the remainder back into the nodelist */

          mm_addfreechunk(heap, remainder);
        }

      /* Handle the case of an exact size match */

      node->preceding |= MM_ALLOC_BIT;
      ret = (void *)((char *)node + SIZEOF_MM_ALLOCNODE);
    }

#if defined(CONFIG_MM_DETECT_ERROR)
  struct m_dbg_hdr *hdr = ret;
  if (hdr) {
    hdr->caller = caller;
    hdr->size = real_size;
    hdr->pid = 0;//getpid();
    ret = hdr + 1;
    mdbg_set_magic_hdr(hdr);
    mdbg_set_magic_end(hdr);
    mm_leak_add_chunk(hdr);
    mm_record_minfree();
  }
#endif
  mm_givesemaphore(heap);
  if (!ret) {
    printf("Allocation failed, size %d\n", size);
#if defined(CONFIG_MM_DETECT_ERROR)
    mm_leak_dump();
#endif
  }

#if (CONFIG_MM_MAX_USED)
  mm_max_usedsize_update(heap);
#endif
  return ret;
}
