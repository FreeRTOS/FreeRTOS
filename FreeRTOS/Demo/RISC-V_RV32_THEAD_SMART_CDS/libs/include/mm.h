/****************************************************************************
 *
 *   Copyright (C) 2007-2009, 2013-2014 Gregory Nutt. All rights reserved.
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

#ifndef __INCLUDE_NUTTX_MM_MM_H
#define __INCLUDE_NUTTX_MM_MM_H

/****************************************************************************
 * Included Files
 ****************************************************************************/
#include <csi_config.h>

#include <sys/types.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdint.h>

/****************************************************************************
 * Pre-processor Definitions
 ****************************************************************************/
#ifndef CONFIG_MM_MAX_USED
#define CONFIG_MM_MAX_USED 1
#endif 

#define true  1
#define false 0
#define OK  0
/* Configuration ************************************************************/
/* If the MCU has a small (16-bit) address capability, then we will use
 * a smaller chunk header that contains 16-bit size/offset information.
 * We will also use the smaller header on MCUs with wider addresses if
 * CONFIG_MM_SMALL is selected.  This configuration is common with MCUs
 * that have a large FLASH space, but only a tiny internal SRAM.
 */

#ifdef CONFIG_SMALL_MEMORY
  /* If the MCU has a small addressing capability, then for the smaller
   * chunk header.
   */

#  undef  CONFIG_MM_SMALL
#  define CONFIG_MM_SMALL 1
#endif

/* Terminology:
 *
 * - Flat Build: In the flat build (CONFIG_BUILD_FLAT=y), there is only a
 *   single heap access with the standard allocations (malloc/free).  This
 *   heap is referred to as the user heap.  The kernel logic must
 *   initialize this single heap at boot time.
 * - Protected build: In the protected build (CONFIG_BUILD_PROTECTED=y)
 *   where an MPU is used to protect a region of otherwise flat memory,
 *   there will be two allocators:  One that allocates protected (kernel)
 *   memory and one that allocates unprotected (user) memory.  These are
 *   referred to as the kernel and user heaps, respectively.  Both must be
 *   initialized by the kernel logic at boot time.
 * - Kernel Build: If the architecture has an MMU, then it may support the
 *   kernel build (CONFIG_BUILD_KERNEL=y).  In this configuration, there
 *   is one kernel heap but multiple user heaps:  One per task group.
 *   However, in this case, the kernel need only be concerned about
 *   initializing the single kernel heap here.  User heaps will be created
 *   as tasks are created.
 *
 * These special definitions are provided:
 *
 *   MM_KERNEL_USRHEAP_INIT
 *     Special kernel interfaces to the kernel user-heap are required
 *     for heap initialization.
 *   CONFIG_MM_KERNEL_HEAP
 *     The configuration requires a kernel heap that must initialized
 *     at boot-up.
 */

#undef MM_KERNEL_USRHEAP_INIT
#if defined(CONFIG_BUILD_PROTECTED) && defined(__KERNEL__)
#  define MM_KERNEL_USRHEAP_INIT 1
#elif !defined(CONFIG_BUILD_KERNEL)
#  define MM_KERNEL_USRHEAP_INIT 1
#endif

/* The kernel heap is never accessible from user code */

#ifndef __KERNEL__
#  undef CONFIG_MM_KERNEL_HEAP
#endif

/* Chunk Header Definitions *************************************************/
/* These definitions define the characteristics of allocator
 *
 * MM_MIN_SHIFT is used to define MM_MIN_CHUNK.
 * MM_MIN_CHUNK - is the smallest physical chunk that can be allocated.  It
 *   must be at least a large as sizeof(struct mm_freenode_s).  Larger values
 *   may improve performance slightly, but will waste memory due to
 *   quantization losses.
 *
 * MM_MAX_SHIFT is used to define MM_MAX_CHUNK
 * MM_MAX_CHUNK is the largest, contiguous chunk of memory that can be
 *   allocated.  It can range from 16-bytes to 4Gb.  Larger values of
 *   MM_MAX_SHIFT can cause larger data structure sizes and, perhaps,
 *   minor performance losses.
 */

#if defined(CONFIG_MM_SMALL) && UINTPTR_MAX <= UINT32_MAX
/* Two byte offsets; Pointers may be 2 or 4 bytes;
 * sizeof(struct mm_freenode_s) is 8 or 12 bytes.
 * REVISIT: We could do better on machines with 16-bit addressing.
 */

#  define MM_MIN_SHIFT    4  /* 16 bytes */
#  define MM_MAX_SHIFT   15  /* 32 Kb */

#elif defined(CONFIG_HAVE_LONG_LONG)
/* Four byte offsets; Pointers may be 4 or 8 bytes
 * sizeof(struct mm_freenode_s) is 16 or 24 bytes.
 */
  
#  if UINTPTR_MAX <= UINT32_MAX
#    define MM_MIN_SHIFT  4  /* 16 bytes */
#  elif UINTPTR_MAX <= UINT64_MAX
#    define MM_MIN_SHIFT  5  /* 32 bytes */
#  endif
#  define MM_MAX_SHIFT   22  /*  4 Mb */

#else
/* Four byte offsets; Pointers must be 4 bytes.
 * sizeof(struct mm_freenode_s) is 16 bytes.
 */

#  define MM_MIN_SHIFT    4  /* 16 bytes */
#  define MM_MAX_SHIFT   22  /*  4 Mb */
#endif

/* All other definitions derive from these two */

#define MM_MIN_CHUNK     (1 << MM_MIN_SHIFT)
#define MM_MAX_CHUNK     (1 << MM_MAX_SHIFT)
#define MM_NNODES        (MM_MAX_SHIFT - MM_MIN_SHIFT + 1)

#define MM_GRAN_MASK     (MM_MIN_CHUNK-1)
#define MM_ALIGN_UP(a)   (((a) + MM_GRAN_MASK) & ~MM_GRAN_MASK)
#define MM_ALIGN_DOWN(a) ((a) & ~MM_GRAN_MASK)

/* An allocated chunk is distinguished from a free chunk by bit 31 (or 15)
 * of the 'preceding' chunk size.  If set, then this is an allocated chunk.
 */

#ifdef CONFIG_MM_SMALL
# define MM_ALLOC_BIT    0x8000
#else
# define MM_ALLOC_BIT    0x80000000
#endif
#define MM_IS_ALLOCATED(n) \
  ((int)((struct mm_allocnode_s*)(n)->preceding) < 0))

/****************************************************************************
 * Public Types
 ****************************************************************************/

struct mallinfo
{
  int arena;    /* This is the total size of memory allocated
                 * for use by malloc in bytes. */
  int ordblks;  /* This is the number of free (not in use) chunks */
  int mxordblk; /* Size of the largest free (not in use) chunk */
  int uordblks; /* This is the total size of memory occupied by
                 * chunks handed out by malloc. */
  int fordblks; /* This is the total size of memory occupied
                 * by free (not in use) chunks.*/
};

/* Determines the size of the chunk size/offset type */

#ifdef CONFIG_MM_SMALL
   typedef uint16_t mmsize_t;
#  define MMSIZE_MAX 0xffff
#else
   typedef size_t mmsize_t;
#  define MMSIZE_MAX SIZE_MAX
#endif

/* This describes an allocated chunk.  An allocated chunk is
 * distinguished from a free chunk by bit 15/31 of the 'preceding' chunk
 * size.  If set, then this is an allocated chunk.
 */

struct mm_allocnode_s
{
  mmsize_t size;           /* Size of this chunk */
  mmsize_t preceding;      /* Size of the preceding chunk */
};

/* What is the size of the allocnode? */

#ifdef CONFIG_MM_SMALL
# define SIZEOF_MM_ALLOCNODE   4
#else
# define SIZEOF_MM_ALLOCNODE   8
#endif

#define CHECK_ALLOCNODE_SIZE \
  DEBUGASSERT(sizeof(struct mm_allocnode_s) == SIZEOF_MM_ALLOCNODE)

/* This describes a free chunk */

struct mm_freenode_s
{
  mmsize_t size;                   /* Size of this chunk */
  mmsize_t preceding;              /* Size of the preceding chunk */
  struct mm_freenode_s *flink; /* Supports a doubly linked list */
  struct mm_freenode_s *blink;
};

/* What is the size of the freenode? */

#define MM_PTR_SIZE sizeof(struct mm_freenode_s *)
#define SIZEOF_MM_FREENODE (SIZEOF_MM_ALLOCNODE + 2*MM_PTR_SIZE)

#define CHECK_FREENODE_SIZE \
  DEBUGASSERT(sizeof(struct mm_freenode_s) == SIZEOF_MM_FREENODE)

#ifndef CONFIG_MM_REGIONS
#define CONFIG_MM_REGIONS 1
#endif

/* This describes one heap (possibly with multiple regions) */

typedef void* sem_t;
struct mm_heap_s
{
  /* Mutually exclusive access to this data set is enforced with
   * the following un-named semaphore.
   */

  sem_t mm_semaphore;
  uint16_t mm_holder;
  int   mm_counts_held;

  /* This is the size of the heap provided to mm */

  size_t  mm_heapsize;

  /* This is the first and last nodes of the heap */

  struct mm_allocnode_s *mm_heapstart[CONFIG_MM_REGIONS];
  struct mm_allocnode_s *mm_heapend[CONFIG_MM_REGIONS];

#if CONFIG_MM_REGIONS > 1
  int mm_nregions;
#endif

  /* All free nodes are maintained in a doubly linked list.  This
   * array provides some hooks into the list at various points to
   * speed searches for free nodes.
   */

  struct mm_freenode_s mm_nodelist[MM_NNODES];
};

/****************************************************************************
 * Public Data
 ****************************************************************************/

#undef EXTERN
#if defined(__cplusplus)
#define EXTERN extern "C"
extern "C"
{
#else
#define EXTERN extern
#endif

/* User heap structure:
 *
 * - Flat build:  In the FLAT build, the user heap structure is a globally
 *   accessible variable.
 * - Protected build:  The user heap structure is directly available only
 *   in user space.
 * - Kernel build: There are multiple heaps, one per process.  The heap
 *   structure is associated with the address environment and there is
 *   no global user heap structure.
 */

#if defined(CONFIG_ARCH_ADDRENV) && defined(CONFIG_BUILD_KERNEL)
/* In the kernel build, there a multiple user heaps; one for each task
 * group.  In this build configuration, the user heap structure lies
 * in a reserved region at the beginning of the .bss/.data address
 * space (CONFIG_ARCH_DATA_VBASE).  The size of that region is given by
 * ARCH_DATA_RESERVE_SIZE
 */

#elif defined(CONFIG_BUILD_PROTECTED) && defined(__KERNEL__)
/* In the protected mode, there are two heaps:  A kernel heap and a single
 * user heap.  In that case the user heap structure lies in the user space
 * (with a reference in the userspace interface).
 */

#else
/* Otherwise, the user heap data structures are in common .bss */

EXTERN struct mm_heap_s g_mmheap;
#endif

#ifdef CONFIG_MM_KERNEL_HEAP
/* This is the kernel heap */

EXTERN struct mm_heap_s g_kmmheap;
#endif

/****************************************************************************
 * Public Function Prototypes
 ****************************************************************************/

/* Functions contained in mm_initialize.c ***********************************/

void mm_initialize(struct mm_heap_s *heap, void *heap_start,
                   size_t heap_size);
void mm_addregion(struct mm_heap_s *heap, void *heapstart,
                  size_t heapsize);

/* Functions contained in umm_initialize.c **********************************/

void umm_initialize(void *heap_start, size_t heap_size);

/* Functions contained in kmm_initialize.c **********************************/

#ifdef CONFIG_MM_KERNEL_HEAP
void kmm_initialize(void *heap_start, size_t heap_size);
#endif

/* Functions contained in umm_addregion.c ***********************************/

void umm_addregion(void *heapstart, size_t heapsize);

/* Functions contained in kmm_addregion.c ***********************************/

#ifdef CONFIG_MM_KERNEL_HEAP
void kmm_addregion(void *heapstart, size_t heapsize);
#endif

/* Functions contained in mm_sem.c ******************************************/

#define mm_seminitialize(heap)
#define mm_takesemaphore(heap)
#define mm_trysemaphore(heap)
#define mm_givesemaphore(heap)

/* Functions contained in umm_sem.c ****************************************/

int  umm_trysemaphore(void);
void umm_givesemaphore(void);

/* Functions contained in kmm_sem.c ****************************************/

#ifdef CONFIG_MM_KERNEL_HEAP
int  kmm_trysemaphore(void);
void kmm_givesemaphore(void);
#endif

/* Functions contained in mm_malloc.c ***************************************/

#include "mm_queue.h"

struct m_dbg_hdr {
    dq_entry_t node;
    void *caller;
    uint32_t size:23;
    uint32_t referenced:1;
    uint32_t pid:8;
#define MAGIC_INUSE 0x65657575
#define MAGIC_FREE 0x3f3f3f3f
#define MAGIC_END 0xe5e5e5e5
    uint32_t magic;
};

#define MDBG_SZ_HEAD sizeof(struct m_dbg_hdr)
#define MDBG_SZ_TAIL 16

static inline bool mdbg_calc_magic(struct m_dbg_hdr *hdr)
{
    uint32_t magic = (uint32_t)hdr->caller;
    magic ^= hdr->size;
    magic ^= hdr->pid;
    magic ^= MAGIC_INUSE;
    return magic;
}

static inline bool mdbg_check_magic_hdr(struct m_dbg_hdr *hdr)
{
    return mdbg_calc_magic(hdr) == hdr->magic;
}

static inline bool mdbg_check_magic_end(struct m_dbg_hdr *hdr)
{
    void *p = hdr + 1;
    uint32_t *m = (uint32_t *)((uint32_t)p + hdr->size);
    uint32_t magic = MAGIC_END ^ hdr->magic;
    int i;

    for (i=0;i<MDBG_SZ_TAIL/4;i++) {
        if (m[i] != magic)
            return false;
    }

    return true;
}

static inline void mdbg_set_magic_hdr(struct m_dbg_hdr *hdr)
{
    hdr->magic = mdbg_calc_magic(hdr);
}

static inline void mdbg_set_magic_end(struct m_dbg_hdr *hdr)
{
    void *p = hdr + 1;
    uint32_t *m = (uint32_t *)((uint32_t)p + hdr->size);
    int i;

    for (i=0;i<MDBG_SZ_TAIL/4;i++) {
        m[i] = MAGIC_END ^ hdr->magic;
    }
}


void *mm_malloc(struct mm_heap_s *heap, size_t size, void *caller);

#if (CONFIG_MM_MAX_USED)
int mm_get_max_usedsize(void);
int mm_max_usedsize_update(struct mm_heap_s *heap);
#endif

/* Functions contained in kmm_malloc.c **************************************/

#ifdef CONFIG_MM_KERNEL_HEAP
void *kmm_malloc(size_t size);
#endif

/* Functions contained in mm_free.c *****************************************/

void mm_free(struct mm_heap_s *heap, void *mem, void *caller);

/* Functions contained in kmm_free.c ****************************************/

#ifdef CONFIG_MM_KERNEL_HEAP
void kmm_free(void *mem);
#endif

/* Functions contained in mm_realloc.c **************************************/

void *mm_realloc(struct mm_heap_s *heap, void *oldmem,
                     size_t size);

/* Functions contained in kmm_realloc.c *************************************/

#ifdef CONFIG_MM_KERNEL_HEAP
void *kmm_realloc(void *oldmem, size_t newsize);
#endif

/* Functions contained in mm_calloc.c ***************************************/

void *mm_calloc(struct mm_heap_s *heap, size_t n, size_t elem_size);

/* Functions contained in kmm_calloc.c **************************************/

#ifdef CONFIG_MM_KERNEL_HEAP
void *kmm_calloc(size_t n, size_t elem_size);
#endif

/* Functions contained in mm_zalloc.c ***************************************/

void *mm_zalloc(struct mm_heap_s *heap, size_t size);

/* Functions contained in kmm_zalloc.c **************************************/

#ifdef CONFIG_MM_KERNEL_HEAP
void *kmm_zalloc(size_t size);
#endif

/* Functions contained in mm_memalign.c *************************************/

void *mm_memalign(struct mm_heap_s *heap, size_t alignment,
                      size_t size);

/* Functions contained in kmm_memalign.c ************************************/

#ifdef CONFIG_MM_KERNEL_HEAP
void *kmm_memalign(size_t alignment, size_t size);
#endif

/* Functions contained in kmm_heapmember.c **********************************/

#if defined(CONFIG_MM_KERNEL_HEAP)
bool kmm_heapmember(void *mem);
#endif

/* Functions contained in mm_brkaddr.c **************************************/

void *mm_brkaddr(struct mm_heap_s *heap, int region);

/* Functions contained in umm_brkaddr.c *************************************/

#if !defined(CONFIG_BUILD_PROTECTED) || !defined(__KERNEL__)
void *umm_brkaddr(int region);
#endif

/* Functions contained in kmm_brkaddr.c *************************************/

#ifdef CONFIG_MM_KERNEL_HEAP
void *kmm_brkaddr(int region);
#endif

/* Functions contained in mm_sbrk.c *****************************************/

#if defined(CONFIG_ARCH_ADDRENV) && defined(CONFIG_MM_PGALLOC) && \
    defined(CONFIG_ARCH_USE_MMU)
void *mm_sbrk(struct mm_heap_s *heap, intptr_t incr,
                  uintptr_t maxbreak);
#endif

/* Functions contained in kmm_sbrk.c ****************************************/

#if defined(CONFIG_MM_KERNEL_HEAP) && defined(CONFIG_ARCH_ADDRENV) && \
    defined(CONFIG_MM_PGALLOC) && defined(CONFIG_ARCH_USE_MMU)
void *kmm_sbrk(intptr_t incr);
#endif

/* Functions contained in mm_extend.c ***************************************/

void mm_extend(struct mm_heap_s *heap, void *mem, size_t size,
               int region);

/* Functions contained in umm_extend.c **************************************/

#if !defined(CONFIG_BUILD_PROTECTED) || !defined(__KERNEL__)
void umm_extend(void *mem, size_t size, int region);
#endif

/* Functions contained in kmm_extend.c **************************************/

#ifdef CONFIG_MM_KERNEL_HEAP
void kmm_extend(void *mem, size_t size, int region);
#endif

/* Functions contained in mm_mallinfo.c *************************************/

struct mallinfo; /* Forward reference */
int mm_mallinfo(struct mm_heap_s *heap, struct mallinfo *info);

/* Functions contained in kmm_mallinfo.c ************************************/

#ifdef CONFIG_MM_KERNEL_HEAP
#ifdef CONFIG_CAN_PASS_STRUCTS
struct mallinfo kmm_mallinfo(void);
#else
int kmm_mallinfo(struct mallinfo *info);
#endif
#endif /* CONFIG_CAN_PASS_STRUCTS */

/* Functions contained in mm_shrinkchunk.c **********************************/

void mm_shrinkchunk(struct mm_heap_s *heap,
                    struct mm_allocnode_s *node, size_t size);

/* Functions contained in mm_addfreechunk.c *********************************/

void mm_addfreechunk(struct mm_heap_s *heap,
                     struct mm_freenode_s *node);

/* Functions contained in mm_size2ndx.c.c ***********************************/

int mm_size2ndx(size_t size);

#if defined(CONFIG_MM_DETECT_ERROR)
void mm_leak_add_chunk(struct m_dbg_hdr *chunk);
void mm_leak_del_chunk(struct m_dbg_hdr *chunk);
void mm_leak_dump(void);
void mm_leak_search_chunk(void *mem);
#else
//static inline void mm_leak_add_chunk(struct m_dbg_hdr *chunk){}
//static inline void mm_leak_del_chunk(struct m_dbg_hdr *chunk){}
//static inline void mm_leak_dump(void){}
//static inline void mm_leak_search_chunk(void *mem){}
#endif

#undef EXTERN
#ifdef __cplusplus
}
#endif

#endif /* __INCLUDE_NUTTX_MM_MM_H */
