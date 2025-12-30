/* wait 
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


#ifndef __WAIT_H__
#define __WAIT_H__

#include <sched.h>
#include <os.h>
#include <waittypes.h>
#include <xenfreertos-queue.h>

#define DEFINE_WAIT(name)                          \
struct wait_queue name = {                         \
    .thread       = get_current(),                 \
    .waiting      = 0,                             \
}


static inline void init_waitqueue_head(struct wait_queue_head *h)
{
    STAILQ_INIT(h);
}

static inline void init_waitqueue_entry(struct wait_queue *q, struct thread *thread)
{
    q->thread = thread;
    q->waiting = 0;
}

static inline void add_wait_queue(struct wait_queue_head *h, struct wait_queue *q)
{
    if (!q->waiting) {
        STAILQ_INSERT_HEAD(h, q, thread_list);
        q->waiting = 1;
    }
}

static inline void remove_wait_queue(struct wait_queue_head *h, struct wait_queue *q)
{
    if (q->waiting) {
        STAILQ_REMOVE(h, q, wait_queue, thread_list);
        q->waiting = 0;
    }
}

static inline void wake_up(struct wait_queue_head *head)
{
    unsigned long flags;
    struct wait_queue *curr, *tmp;
    local_irq_save(flags);
    STAILQ_FOREACH_SAFE(curr, head, thread_list, tmp)
         wake(curr->thread);
    local_irq_restore(flags);
}

#define add_waiter(w, wq) do {  \
    unsigned long flags;        \
    local_irq_save(flags);      \
    add_wait_queue(&wq, &w);    \
    block(get_current());       \
    local_irq_restore(flags);   \
} while (0)

#define remove_waiter(w, wq) do {  \
    unsigned long flags;           \
    local_irq_save(flags);         \
    remove_wait_queue(&wq, &w);    \
    local_irq_restore(flags);      \
} while (0)

#define wait_event_deadline(wq, condition, deadline) do {       \
    unsigned long flags;                                        \
    DEFINE_WAIT(__wait);                                        \
    if(condition)                                               \
        break;                                                  \
    for(;;)                                                     \
    {                                                           \
        /* protect the list */                                  \
        local_irq_save(flags);                                  \
        add_wait_queue(&wq, &__wait);                           \
        get_current()->wakeup_time = deadline;                  \
        clear_runnable(get_current());                          \
        local_irq_restore(flags);                               \
        if((condition) || (deadline && NOW() >= deadline))      \
            break;                                              \
        schedule();                                             \
    }                                                           \
    local_irq_save(flags);                                      \
    /* need to wake up */                                       \
    wake(get_current());                                        \
    remove_wait_queue(&wq, &__wait);                            \
    local_irq_restore(flags);                                   \
} while(0) 

#define wait_event(wq, condition) wait_event_deadline(wq, condition, 0) 



#endif /* __WAIT_H__ */

/*
 * Local variables:
 * mode: C
 * c-file-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
