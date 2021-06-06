/*
 * Copyright (C) 2016 YunOS Project. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <csi_config.h>
#include <stdio.h>
#include <stdlib.h>

#include "mm.h"
#include "umm_heap.h"

#define MAX_HASH 16

extern char __sdata, __edata, __sbss, __ebss;

static struct mm_status mm_status;
static struct mm_status mm_status_snapshoot;
static int min_free = 0xFFFFFFFF;
static bool start_statistics = false;
static struct m_dbg_hdr *caddr;
static struct m_dbg_hdr *caddr_l;

static inline int addr2hash(void *p)
{
    uint32_t addr = (uint32_t)p;
    addr >>= 3;
    addr ^= addr >> 11;
    return addr & (MAX_HASH - 1);
}

struct mm_status {
    dq_queue_t  list[MAX_HASH];
};

void mm_dbg_clone(struct m_dbg_hdr * src , struct m_dbg_hdr * dst)
{
    dst->caller  = src->caller;
    dst->size = src->size;
    dst->referenced = src->referenced;
    dst->pid = src->pid;
    dst->magic = src->magic;
}
void mm_statistics_save(void)
{
    start_statistics = false;
}

void mm_statistics_restore(void)
{
    start_statistics = true;
}

void mm_do_snapshoot(struct mm_status * src, struct mm_status * dst)
{
    int item = 0;
    dq_queue_t * queue = NULL;
    dq_entry_t * entry = NULL;

    struct m_dbg_hdr *node = NULL;
    struct m_dbg_hdr *chunk = NULL;

    for(; item < MAX_HASH; item++) {
        queue = &(src->list[item]);
        entry = queue->head;

        for(; entry != NULL; ) {
            chunk = (struct m_dbg_hdr *)malloc (sizeof (struct m_dbg_hdr));
            node = (struct m_dbg_hdr *)entry;
            mm_dbg_clone(node, chunk);
            dq_addlast(&chunk->node, &(dst->list[item]));
            entry = dq_next(entry);
        }
    }
}

void mm_release_snapshoot(void)
{
    int item = 0;
    dq_queue_t * queue = NULL;
    dq_entry_t * entry = NULL;
    struct m_dbg_hdr * node = NULL;

    for(; item < MAX_HASH ; item ++) {
        queue = &(mm_status_snapshoot.list[item]);
        entry = queue->head;

        for(; entry != NULL; ) {
            dq_rem(entry, queue);
            node = (struct m_dbg_hdr *)entry;
            free(node);
            entry = dq_peek(queue);
        }
    }
}

void mm_leak_add_chunk(struct m_dbg_hdr *chunk)
{
    dq_addlast(&chunk->node, &mm_status.list[addr2hash(chunk)]);
}

void mm_leak_del_chunk(struct m_dbg_hdr *chunk)
{
    dq_rem(&chunk->node, &mm_status.list[addr2hash(chunk)]);
}

static bool is_valid_address(void *p)
{
    int i;

    for (i = 0; i < CONFIG_MM_REGIONS; i++) {
        void *s = (USR_HEAP)->mm_heapstart[0];
        void *e = (USR_HEAP)->mm_heapend[0];
        if (p >= s && p < e) {
            return true;
        }
    }

    return false;
}

typedef int (*scan_cb)(struct m_dbg_hdr *, void *);
static void traverse_one_list(struct m_dbg_hdr *cur, scan_cb cb, void *cookie)
{
    void *prev = cur;

    while (cur) {
        if (!is_valid_address(cur)) {
            cur = prev;
            printf("!!!already corrupted after, stop traversaling!!!ptr=%x size=%d pid=%d caller=%x leak=%c\n",
                   (uint32_t)(cur + 1), cur->size, cur->pid, (uint32_t)cur->caller, cur->referenced ? 'N' : 'Y');
            break;
        }

        int done = cb(cur, cookie);
        if (done) {
            break;
        }
        prev = cur;
        cur = (struct m_dbg_hdr *)cur->node.flink;
    }
}

static bool is_corrupted(struct m_dbg_hdr *cur)
{
    bool corrupted = !mdbg_check_magic_hdr(cur);

    corrupted = corrupted || !mdbg_check_magic_end(cur);

    return corrupted;
}

static int show_chunk_snapshot(struct m_dbg_hdr *cur, void *unused)
{
    (void)unused;
    printf("ptr=%x size=%d pid=%d caller=%x\n",
           (uint32_t)cur + 1, cur->size, cur->pid, (uint32_t)cur->caller);

    return 0;
}

static void mm_snapshoot_dump(void)
{
    int i;
    for(i = 0; i < MAX_HASH; i++) {
        printf("-----------------------------\n");
        traverse_one_list((struct m_dbg_hdr *)(mm_status_snapshoot.list[i].head), show_chunk_snapshot, NULL);
    }
}

void mm_do_statistics(void)
{
    if(start_statistics) {
        start_statistics = false;
        printf("------------min_free:%d,show max mem use statistic-----------------\n", min_free);
        mm_snapshoot_dump();
    } else {
        printf("------------start max mem use statistic-----------------\n");
        start_statistics = true;
    }
}

void mm_record_minfree(void)
{
    if(!start_statistics) {
        return;
    }

#ifdef CONFIG_CAN_PASS_STRUCTS
    struct mallinfo mem;
    mem = mallinfo();
    int free_now = mem.fordblks;
    //printf("mm_record_minfree free_now %d,min_free %d!\n", free_now, min_free);
    if (min_free > free_now) {
        mm_statistics_save();
        min_free = free_now;
        mm_release_snapshoot();
        mm_do_snapshoot(&mm_status, &mm_status_snapshoot);
        mm_statistics_restore();
    }
#else
//    (void)mallinfo(&mem);
#endif
    return;
}


#if defined(CONFIG_MM_DETECT_ERROR)
static int show_one_chunk(struct m_dbg_hdr *cur, void *unused)
{
    printf("caller=[<%x>] ptr=%x size=%d\t pid=%d leak=%c corrupted=%c\n",
           (uint32_t)cur->caller, (uint32_t)(cur + 1), cur->size, cur->pid,
           cur->referenced ? 'N' : 'Y', is_corrupted(cur) ? 'Y' : 'N');

    return 0;
}

static void dump_one_list(struct m_dbg_hdr *cur)
{
    printf("-----------------------------\n");
    traverse_one_list(cur, show_one_chunk, NULL);
}

static int mark_as_referenced(struct m_dbg_hdr *cur, void *p)
{
    if (p == cur + 1) {
        cur->referenced = 1;
        return 1;
    }

    return 0;
}

static void scan_area(void *start, void *end)
{
    void **p = (void **)((uint32_t)start & ~3);

    while ((void *)p < end) {
        struct m_dbg_hdr *cur;
        cur = (struct m_dbg_hdr *)mm_status.list[addr2hash((uint8_t *)(*p) - MDBG_SZ_HEAD)].head;
        traverse_one_list(cur, mark_as_referenced, *p);
        p ++;
    }
}

static int mark_as_leaked(struct m_dbg_hdr *cur, void *p)
{
    *(int *)p += cur->size;
    cur->referenced = 0;

    return 0;
}
#endif

static int show_corrupted_chunk(struct m_dbg_hdr *cur, void *unused)
{
    (void)unused;
    if (!is_corrupted(cur)) {
        return 0;
    }

    printf("caller=%x ptr=%x size=%d  pid=%d leak=%c corrupted=%c\n",
           (uint32_t)cur->caller, (uint32_t)(cur + 1), cur->size, cur->pid,
           cur->referenced ? 'N' : 'Y', is_corrupted(cur) ? 'Y' : 'N');

    return 0;
}

static void dump_corrupted_list(struct m_dbg_hdr *cur)
{
    traverse_one_list(cur, show_corrupted_chunk, NULL);
}

void mm_leak_dump(void)
{
    struct mallinfo info;

#if defined(CONFIG_MM_DETECT_ERROR)
    int i;
    int size = 0;
    for(i = 0; i < MAX_HASH; i++) {
        traverse_one_list((struct m_dbg_hdr *)(mm_status.list[i].head), mark_as_leaked, &size);
    }

    scan_area(&__sdata, &__edata);
    scan_area(&__sbss, &__ebss);
    for (i = 0; i < CONFIG_MM_REGIONS; i++) {
        scan_area((USR_HEAP)->mm_heapstart[i], (USR_HEAP)->mm_heapend[i]);
#ifdef CONFIG_MM_KERNEL_HEAP
        scan_area((&g_kmmheap)->mm_heapstart[i], (&g_kmmheap)->mm_heapend[i]);
#endif
    }

    printf("malloced size=%d(except for mem used for debugging)\n", size);
    for(i = 0; i < MAX_HASH; i++) {
        dump_one_list((struct m_dbg_hdr *)(mm_status.list[i].head));
    }
#endif

    mm_mallinfo(USR_HEAP, &info);
}

static int search_nearest(struct m_dbg_hdr *cur, void *p)
{
    if ((void *)cur < p && cur > caddr) {
        caddr = cur;
    }

    if ((void *)cur > p && cur < caddr_l) {
        caddr_l = cur;
    }

    return 0;
}

void mm_leak_search_chunk(void *p)
{
    int i;
    caddr = NULL;
    caddr_l = (void *) - 1UL;

    for(i = 0; i < MAX_HASH; i++) {
        dump_corrupted_list((struct m_dbg_hdr *)(mm_status.list[i].head));
        traverse_one_list((struct m_dbg_hdr *)(mm_status.list[i].head), search_nearest, p);
    }

    if (caddr) {
        printf("%s before : addr=%x caller=%x\n", __func__, (uint32_t)caddr, (uint32_t)caddr->caller);
    }

    if (caddr_l != (void *) - 1UL) {
        printf("%s after : addr=%x caller=%x\n", __func__, (uint32_t)caddr_l, (uint32_t)caddr_l->caller);
    }
}

void mm_show_corrupted(void)
{
    int i;

    for(i = 0; i < MAX_HASH; i++) {
        dump_corrupted_list((struct m_dbg_hdr *)(mm_status.list[i].head));
    }
}

