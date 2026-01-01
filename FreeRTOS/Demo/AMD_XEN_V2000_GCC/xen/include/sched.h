/* sched
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


#ifndef __SCHED_H__
#define __SCHED_H__

#ifdef HAVE_LIBC
#include <sys/reent.h>
#endif

#include <time.h>
#include <xenfreertos-queue.h>
#include <arch_sched.h>

struct thread
{
    char *name;
    char *stack;
    /* keep in that order */
    unsigned long sp;  /* Stack pointer */
    unsigned long ip;  /* Instruction pointer */
    TAILQ_ENTRY(thread) thread_list;
    uint32_t flags;
    s_time_t wakeup_time;
#ifdef HAVE_LIBC
    struct _reent reent;
#endif
};

extern struct thread *idle_thread;
void idle_thread_fn(void *unused);

#define RUNNABLE_FLAG   0x00000001

#define is_runnable(_thread)    (_thread->flags & RUNNABLE_FLAG)
#define set_runnable(_thread)   (_thread->flags |= RUNNABLE_FLAG)
#define clear_runnable(_thread) (_thread->flags &= ~RUNNABLE_FLAG)

#define switch_threads(prev, next) arch_switch_threads(prev, next)
 
    /* Architecture specific setup of thread creation. */
struct thread* arch_create_thread(char *name, void (*function)(void *),
                                  void *data);

void init_sched(void);
void run_idle_thread(void);
struct thread* create_thread(char *name, void (*function)(void *), void *data);
void exit_thread(void) __attribute__((noreturn));
void schedule(void);

#ifdef __INSIDE_MINIOS__
#define current get_current()
#endif

void wake(struct thread *thread);
void block(struct thread *thread);
void msleep(uint32_t millisecs);

#endif /* __SCHED_H__ */
