/* -*-  Mode:C; c-basic-offset:4; tab-width:4 -*-
 *
 * (C) 2016 - Juergen Gross, SUSE Linux GmbH
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to
 * deal in the Software without restriction, including without limitation the
 * rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

#ifndef __E820_HEADER
#define __E820_HEADER

#if defined(__arm__) || defined(__aarch64__) || defined(CONFIG_PARAVIRT)
#define CONFIG_E820_TRIVIAL
#else
#include <xen/arch-x86/hvm/start_info.h>
#endif

/* PC BIOS standard E820 types and structure. */
#define E820_RAM          1
#define E820_RESERVED     2
#define E820_ACPI         3
#define E820_NVS          4
#define E820_UNUSABLE     5
#define E820_DISABLED     6
#define E820_PMEM         7
#define E820_TYPES        8

struct __attribute__((packed)) e820entry {
    uint64_t addr;
    uint64_t size;
    uint32_t type;
};

/* Maximum number of entries. */
#define E820_MAX          128

extern struct e820entry e820_map[];
extern unsigned e820_entries;

unsigned long e820_get_current_pages(void);
unsigned long e820_get_max_pages(void);
unsigned long e820_get_maxpfn(unsigned long pages);
unsigned long e820_get_max_contig_pages(unsigned long pfn, unsigned long pages);
#ifndef CONFIG_E820_TRIVIAL
unsigned long e820_get_reserved_pfns(int pages);
void e820_put_reserved_pfns(unsigned long start_pfn, int pages);
void e820_init_memmap(struct hvm_memmap_table_entry *entry, unsigned int num);
#endif

#endif /*__E820_HEADER*/
