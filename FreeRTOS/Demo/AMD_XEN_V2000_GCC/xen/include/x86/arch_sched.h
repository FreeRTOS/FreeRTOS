/* arch_sched 
 * 
 * Copyright (C) 2025 Advanced Micro Devices, Inc. or its affiliates. All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
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
 *
 */



#ifndef __ARCH_SCHED_H__
#define __ARCH_SCHED_H__

#include "arch_limits.h"

static inline struct thread* get_current(void)
{
    struct thread **current;
#ifdef __i386__    
    register unsigned long sp asm("esp");
#else
    register unsigned long sp asm("rsp");
#endif 
    current = (void *)(unsigned long)(sp & ~(__STACK_SIZE-1));
    return *current;
}

extern void __arch_switch_threads(unsigned long *prevctx, unsigned long *nextctx);

#define arch_switch_threads(prev,next) __arch_switch_threads(&(prev)->sp, &(next)->sp)


          
#endif /* __ARCH_SCHED_H__ */
