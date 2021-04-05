/****************************************************************************
 *
 *   Copyright (C) 2015 Gregory Nutt. All rights reserved.
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

#ifndef __MM_UMM_HEAP_UMM_HEAP_H
#define __MM_UMM_HEAP_UMM_HEAP_H

/****************************************************************************
 * Included Files
 ****************************************************************************/
#include <stdint.h>
#include "mm.h"

#ifdef __cplusplus
extern "C" {
#endif

/****************************************************************************
 * Pre-processor Definitions
 ****************************************************************************/

#if defined(CONFIG_ARCH_ADDRENV) && defined(CONFIG_BUILD_KERNEL)
/* In the kernel build, there a multiple user heaps; one for each task
 * group.  In this build configuration, the user heap structure lies
 * in a reserved region at the beginning of the .bss/.data address
 * space (CONFIG_ARCH_DATA_VBASE).  The size of that region is given by
 * ARCH_DATA_RESERVE_SIZE
 */

#  include <nuttx/addrenv.h>
#  define USR_HEAP (&ARCH_DATA_RESERVE->ar_usrheap)

#elif defined(CONFIG_BUILD_PROTECTED) && defined(__KERNEL__)
/* In the protected mode, there are two heaps:  A kernel heap and a single
 * user heap.  Kernel code must obtain the address of the user heap data
 * structure from the userspace interface.
 */

#  include <nuttx/userspace.h>
#  define USR_HEAP (USERSPACE->us_heap)

#else
/* Otherwise, the user heap data structures are in common .bss */

#  define USR_HEAP &g_mmheap
#endif

/****************************************************************************
 * Public Functions
 ****************************************************************************/
void mm_heap_initialize(void);
int32_t mm_get_mallinfo(int32_t *total, int32_t *used, int32_t *free, int32_t *peak);
void mm_leak_dump(void);

#ifdef __cplusplus
}
#endif

#endif /* __MM_UMM_HEAP_UMM_HEAP_H */
