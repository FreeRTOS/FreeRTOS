/* freertos_mm
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

#include <os.h>
#include <mm.h>

#define MAX_1GB_SLOTS       512

#if defined (__x86_64__)
#define ONDEMAND_VIRT_BASE  0xFFFFC00000000000ULL
extern uint64_t pml4;
extern uint64_t pud;
static uint8_t ondemand_bitmap[MAX_1GB_SLOTS] = {0};

uint64_t allocate_virt_addr(int n, int alignment) {
    int start = -1;

    for (int i = 0; i <= MAX_1GB_SLOTS - n; i++) {
        if (i % alignment != 0) continue;

        int j;
        for (j = 0; j < n; j++) {
            if (ondemand_bitmap[i + j]) break;
        }

        if (j == n) {
            start = i;
            for (int k = 0; k < n; k++)
                ondemand_bitmap[start + k] = 1;
            return ONDEMAND_VIRT_BASE + (uint64_t)start * 0x40000000ULL;
        }
    }

    return 0;
}

int map_single_frame(uint64_t *pml4, uint64_t *pud,
                        uint64_t virt_addr, uint64_t mfn) {
    uint64_t pml4_index = (virt_addr >> 39) & 0x1FF;
    uint64_t pud_index  = (virt_addr >> 30) & 0x1FF;

    if (!(pml4[pml4_index] & 0x1)) {
        return -1;
    }

    uint64_t *pud_table = (uint64_t *)(pml4[pml4_index] & ~0xFFFULL);
    pud_table[pud_index] = (mfn << 12) | 0x83;
    return 0;
}

#endif

void *map_frames_ex(const unsigned long *mfns, unsigned long n,
                    unsigned long stride, unsigned long incr,
                    unsigned long alignment,
                    domid_t id, int *err, unsigned long prot)
{
#if defined (__x86_64__)
    unsigned long va = allocate_virt_addr(n, alignment);
    if (!va)
        return NULL;

    for (int i = 0; i < n; i++) {
        map_single_frame(&pml4, &pud, va + i * 0x40000000ULL, mfns[i]);
    }
    
    return (void *)va;
#else
    return (void *)(*mfns<< 12);
#endif
}
