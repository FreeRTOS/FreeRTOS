/****************************************************************************
 * mm/mm_heap/mm_free.c
 *
 *   Copyright (C) 2007, 2009, 2013-2014 Gregory Nutt. All rights reserved.
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

#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <errno.h>
#include "mm.h"

/****************************************************************************
 * Pre-processor Definitions
 ****************************************************************************/
#define THIS_MODULE MODULE_NONE

/****************************************************************************
 * Private Functions
 ****************************************************************************/

/****************************************************************************
 * Public Functions
 ****************************************************************************/

/****************************************************************************
 * Name: mm_free
 *
 * Description:
 *   Returns a chunk of memory to the list of free nodes,  merging with
 *   adjacent free chunks if possible.
 *
 ****************************************************************************/

void mm_free(struct mm_heap_s *heap, void *mem, void *caller)
{
  struct mm_freenode_s *node;
  struct mm_freenode_s *prev;
  struct mm_freenode_s *next;

  (void)caller;
  //mvdbg("Freeing %p\n", mem);

  /* Protect against attempts to free a NULL reference */

  if (!mem)
    {
      return;
    }

#if defined(CONFIG_MM_DETECT_ERROR)
  struct m_dbg_hdr *hdr = (struct m_dbg_hdr *)((uint8_t *)mem - MDBG_SZ_HEAD);
  if (!mdbg_check_magic_hdr(hdr)) {
    printf("mm magic hdr err %p,%p\n", hdr->caller, caller);
    mm_leak_search_chunk(hdr);
    /* force trapping */
    *(volatile void **)0 = 0;
  }
  if (!mdbg_check_magic_end(hdr)) {
    printf("mm magic end err %p,%p", hdr->caller, caller);
    mm_leak_search_chunk(hdr+1);
    /* force trapping */
    *(volatile void **)0 = 0;
  }
  mem = hdr;
  hdr->magic = MAGIC_FREE;
  mm_leak_del_chunk(hdr);
#endif

  /* We need to hold the MM semaphore while we muck with the
   * nodelist.
   */

  mm_takesemaphore(heap);

  /* Map the memory chunk into a free node */

  node = (struct mm_freenode_s *)((uint32_t)mem - SIZEOF_MM_ALLOCNODE);
  node->preceding &= ~MM_ALLOC_BIT;

  /* Check if the following node is free and, if so, merge it */

  next = (struct mm_freenode_s *)((uint32_t)node + node->size);
  if ((next->preceding & MM_ALLOC_BIT) == 0)
    {
      struct mm_allocnode_s *andbeyond;

      /* Get the node following the next node (which will
       * become the new next node). We know that we can never
       * index past the tail chunk because it is always allocated.
       */

      andbeyond = (struct mm_allocnode_s *)((uint32_t)next + next->size);

      /* Remove the next node.  There must be a predecessor,
       * but there may not be a successor node.
       */

      //DEBUGASSERT(next->blink);
      next->blink->flink = next->flink;
      if (next->flink)
        {
          next->flink->blink = next->blink;
        }

      /* Then merge the two chunks */

      node->size          += next->size;
      andbeyond->preceding =  node->size | (andbeyond->preceding & MM_ALLOC_BIT);
      next                 = (struct mm_freenode_s *)andbeyond;
    }

  /* Check if the preceding node is also free and, if so, merge
   * it with this node
   */

  prev = (struct mm_freenode_s *)((uint32_t)node - node->preceding);
  if ((prev->preceding & MM_ALLOC_BIT) == 0)
    {
      /* Remove the node.  There must be a predecessor, but there may
       * not be a successor node.
       */

      //DEBUGASSERT(prev->blink);
      prev->blink->flink = prev->flink;
      if (prev->flink)
        {
          prev->flink->blink = prev->blink;
        }

      /* Then merge the two chunks */

      prev->size     += node->size;
      next->preceding = prev->size | (next->preceding & MM_ALLOC_BIT);
      node            = prev;
    }

  /* Add the merged node to the nodelist */

  mm_addfreechunk(heap, node);
  mm_givesemaphore(heap);
}
