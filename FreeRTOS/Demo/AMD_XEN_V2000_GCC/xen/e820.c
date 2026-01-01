/* e820 
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



#include <types.h>
#include <lib.h>
#include <console.h>
#include <os.h>
//#include <xenfreertos/posix/limits.h>
#include <e820.h>
#include <xen/memory.h>

//struct e820entry e820_map[E820_MAX];
//unsigned e820_entries;

static char *e820_types[E820_TYPES] = {
    [E820_RAM]      = "RAM",
    [E820_RESERVED] = "Reserved",
    [E820_ACPI]     = "ACPI",
    [E820_NVS]      = "NVS",
    [E820_UNUSABLE] = "Unusable",
    [E820_DISABLED] = "Disabled",
    [E820_PMEM]     = "PMEM"
};


static void e820_insert_entry_at(int idx, unsigned long addr,
                                 unsigned long size, unsigned int type)
{
    int i;

    if ( e820_entries == E820_MAX )
    {
        xprintk("E820 memory map overflow\n");
        do_exit();
    }

    e820_entries++;
    for ( i = e820_entries - 1; i > idx; i-- )
        e820_map[i] = e820_map[i - 1];

    e820_map[idx].addr = addr;
    e820_map[idx].size = size;
    e820_map[idx].type = type;
}

unsigned long e820_get_reserved_pfns(int pages)
{
    int i;
    unsigned long last = 0, needed = (long)pages << PAGE_SHIFT;

    for ( i = 0; i < e820_entries && e820_map[i].addr < last + needed; i++ )
        last = e820_map[i].addr + e820_map[i].size;

    if ( i == 0 || e820_map[i - 1].type != E820_RESERVED )
        e820_insert_entry_at(i, last, needed, E820_RESERVED);
    else
        e820_map[i - 1].size += needed;

    return last >> PAGE_SHIFT;
}

void arch_print_memmap(void)
{
    int i;
    unsigned long from, to;
    char *type;
    char buf[12];

    printk("Memory map:\n");
    for ( i = 0; i < e820_entries; i++ )
    {
        if ( e820_map[i].type >= E820_TYPES || !e820_types[e820_map[i].type] )
        {
            snprintf(buf, sizeof(buf), "%8x", e820_map[i].type);
            type = buf;
        }
        else
        {
            type = e820_types[e820_map[i].type];
        }
        from = e820_map[i].addr;
        to = from + e820_map[i].size - 1;
        printk("%012lx-%012lx: %s\n", from, to, type);
    }
}

