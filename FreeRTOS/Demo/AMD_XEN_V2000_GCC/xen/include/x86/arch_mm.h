/* -*-  Mode:C; c-basic-offset:4; tab-width:4 -*-
 *
 * (C) 2003 - Rolf Neugebauer - Intel Research Cambridge
 * Copyright (c) 2005, Keir A Fraser
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

#ifndef _ARCH_MM_H_
#define _ARCH_MM_H_

#ifndef __ASSEMBLY__
#include <xen/xen.h>
#if defined(__i386__)
#include <xen/arch-x86_32.h>
#define __CONST(x) x ## ULL
#elif defined(__x86_64__)
#include <xen/arch-x86_64.h>
#define __CONST(x) x ## UL
#else
#error "Unsupported architecture"
#endif
#define CONST(x) __CONST(x)
#else
#define CONST(x) x
#endif

/*
 * Physical address space usage:
 *
 * 0..._edata: kernel text/data
 * *stack    : kernel stack (thread 0)
 * hypervisor allocated data: p2m_list, start_info page, xenstore page,
 *                            console page, initial page tables
 * bitmap of allocated pages
 * pages controlled by the page allocator
 *
 *
 * Virtual address space usage:
 *
 *  area                           x86-64               x86-32
 *  ------------------------------------------------------------
 *  mapped physical memory       00000000             00000000
 *  kernel virtual mappings    8000000000             3f000000
 *  demand mappings          100000000000             40000000
 *  heap (with libc only)    200000000000             b0000000
 *
 */

#define L1_FRAME                1
#define L2_FRAME                2
#define L3_FRAME                3

#define L1_PAGETABLE_SHIFT      12

#if defined(__i386__)

#define L2_PAGETABLE_SHIFT      21
#define L3_PAGETABLE_SHIFT      30

#define L1_PAGETABLE_ENTRIES    512
#define L2_PAGETABLE_ENTRIES    512
#define L3_PAGETABLE_ENTRIES    4

#define PAGETABLE_LEVELS        3

#define PADDR_BITS              44
#define PADDR_MASK              ((1ULL << PADDR_BITS)-1)

#define L2_MASK  ((1UL << L3_PAGETABLE_SHIFT) - 1)

#define PRIpte "016llx"
#ifndef __ASSEMBLY__
typedef uint64_t pgentry_t;
#else
#define PTE(val) .long val; .long 0
#endif

#define MAX_MEM_SIZE            CONST(0x3f000000)
#define VIRT_KERNEL_AREA        CONST(0x3f000000)
#define VIRT_DEMAND_AREA        CONST(0x40000000)
#define VIRT_HEAP_AREA          CONST(0xb0000000)

#define DEMAND_MAP_PAGES        CONST(0x6ffff)
#define HEAP_PAGES_MAX          ((HYPERVISOR_VIRT_START - VIRT_HEAP_AREA) / \
                                 PAGE_SIZE - 1)

#elif defined(__x86_64__)

#define L2_PAGETABLE_SHIFT      21
#define L3_PAGETABLE_SHIFT      30
#define L4_PAGETABLE_SHIFT      39

#define L1_PAGETABLE_ENTRIES    512
#define L2_PAGETABLE_ENTRIES    512
#define L3_PAGETABLE_ENTRIES    512
#define L4_PAGETABLE_ENTRIES    512

#define PAGETABLE_LEVELS        4

/* These are page-table limitations. Current CPUs support only 40-bit phys. */
#define PADDR_BITS              52
#define VADDR_BITS              48
#define PADDR_MASK              ((1UL << PADDR_BITS)-1)
#define VADDR_MASK              ((1UL << VADDR_BITS)-1)

#define L2_MASK  ((1UL << L3_PAGETABLE_SHIFT) - 1)
#define L3_MASK  ((1UL << L4_PAGETABLE_SHIFT) - 1)

#define PRIpte "016lx"
#ifndef __ASSEMBLY__
typedef unsigned long pgentry_t;
#else
#define PTE(val) .quad val
#endif

#define MAX_MEM_SIZE            (CONST(512) << 30)
#define VIRT_KERNEL_AREA        CONST(0x0000008000000000)
#define VIRT_DEMAND_AREA        CONST(0x0000100000000000)
#define VIRT_HEAP_AREA          CONST(0x0000200000000000)

#define DEMAND_MAP_PAGES        CONST(0x8000000)
#define HEAP_PAGES_MAX          CONST(0x8000000)

#endif

#ifndef HAVE_LIBC
#define HEAP_PAGES 0
#else
#define HEAP_PAGES   HEAP_PAGES_MAX
#endif

#define L1_MASK  ((1UL << L2_PAGETABLE_SHIFT) - 1)

/* Given a virtual address, get an entry offset into a page table. */
#define l1_table_offset(_a) \
  (((_a) >> L1_PAGETABLE_SHIFT) & (L1_PAGETABLE_ENTRIES - 1))
#define l2_table_offset(_a) \
  (((_a) >> L2_PAGETABLE_SHIFT) & (L2_PAGETABLE_ENTRIES - 1))
#define l3_table_offset(_a) \
  (((_a) >> L3_PAGETABLE_SHIFT) & (L3_PAGETABLE_ENTRIES - 1))
#if defined(__x86_64__)
#define l4_table_offset(_a) \
  (((_a) >> L4_PAGETABLE_SHIFT) & (L4_PAGETABLE_ENTRIES - 1))
#endif

#define _PAGE_PRESENT  CONST(0x001)
#define _PAGE_RW       CONST(0x002)
#define _PAGE_USER     CONST(0x004)
#define _PAGE_PWT      CONST(0x008)
#define _PAGE_PCD      CONST(0x010)
#define _PAGE_ACCESSED CONST(0x020)
#define _PAGE_DIRTY    CONST(0x040)
#define _PAGE_PAT      CONST(0x080)
#define _PAGE_PSE      CONST(0x080)
#define _PAGE_GLOBAL   CONST(0x100)

#ifdef CONFIG_PARAVIRT
#define PAGE_USER _PAGE_USER
#else
#define PAGE_USER CONST(0)
#endif

#if defined(__i386__)
#define L1_PROT (_PAGE_PRESENT|_PAGE_RW|_PAGE_ACCESSED)
#define L1_PROT_RO (_PAGE_PRESENT|_PAGE_ACCESSED)
#define L2_PROT (_PAGE_PRESENT|_PAGE_RW|_PAGE_ACCESSED|_PAGE_DIRTY |PAGE_USER)
#define L3_PROT (_PAGE_PRESENT)
#elif defined(__x86_64__)
#define L1_PROT (_PAGE_PRESENT|_PAGE_RW|_PAGE_ACCESSED|PAGE_USER)
#define L1_PROT_RO (_PAGE_PRESENT|_PAGE_ACCESSED|PAGE_USER)
#define L2_PROT (_PAGE_PRESENT|_PAGE_RW|_PAGE_ACCESSED|_PAGE_DIRTY|PAGE_USER)
#define L3_PROT (_PAGE_PRESENT|_PAGE_RW|_PAGE_ACCESSED|_PAGE_DIRTY|PAGE_USER)
#define L4_PROT (_PAGE_PRESENT|_PAGE_RW|_PAGE_ACCESSED|_PAGE_DIRTY|PAGE_USER)
#endif /* __i386__ || __x86_64__ */

/* flags for ioremap */
#define IO_PROT (L1_PROT)
#define IO_PROT_NOCACHE (L1_PROT | _PAGE_PCD)

#include "arch_limits.h"
#define PAGE_SIZE       __PAGE_SIZE
#define PAGE_SHIFT      __PAGE_SHIFT
#define PAGE_MASK       (~(PAGE_SIZE-1))

#define PFN_UP(x)	(((x) + PAGE_SIZE-1) >> L1_PAGETABLE_SHIFT)
#define PFN_DOWN(x)	((x) >> L1_PAGETABLE_SHIFT)
#define PFN_PHYS(x)	((uint64_t)(x) << L1_PAGETABLE_SHIFT)
#define PHYS_PFN(x)	((x) >> L1_PAGETABLE_SHIFT)

/* to align the pointer to the (next) page boundary */
#define PAGE_ALIGN(addr)        (((addr)+PAGE_SIZE-1)&PAGE_MASK)

#define LAPIC_ADDRESS	CONST(0xfee00000)

#ifndef __ASSEMBLY__
/* Definitions for machine and pseudophysical addresses. */
#ifdef __i386__
typedef unsigned long long paddr_t;
typedef unsigned long long maddr_t;
#else
typedef unsigned long paddr_t;
typedef unsigned long maddr_t;
#endif

extern pgentry_t *pt_base;
#ifdef CONFIG_PARAVIRT
extern unsigned long *phys_to_machine_mapping;
#else
extern pgentry_t page_table_base[];
#endif
/* FIXME: _end -> end(variable def), defined end as _end, _erodata -> __rodata_end, defined it later. */
extern char _text, _etext, __rodata_end, _edata;
extern uint8_t end;
#define _erodata	__rodata_end
#define _end		end
extern unsigned long mfn_zero;
static __inline__ maddr_t phys_to_machine(paddr_t phys)
{
	maddr_t machine = pfn_to_mfn(phys >> PAGE_SHIFT);
	machine = (machine << PAGE_SHIFT) | (phys & ~PAGE_MASK);
	return machine;
}

static __inline__ paddr_t machine_to_phys(maddr_t machine)
{
	paddr_t phys = mfn_to_pfn(machine >> PAGE_SHIFT);
	phys = (phys << PAGE_SHIFT) | (machine & ~PAGE_MASK);
	return phys;
}

#define VIRT_START                 ((unsigned long)&_text)

#define to_phys(x)                 ((unsigned long)(x)-VIRT_START)
#define to_virt(x)                 ((void *)((unsigned long)(x)+VIRT_START))

#define virt_to_pfn(_virt)         (PFN_DOWN(to_phys(_virt)))
#define virt_to_mfn(_virt)         (pfn_to_mfn(virt_to_pfn(_virt)))
#define mach_to_virt(_mach)        (to_virt(machine_to_phys(_mach)))
#define virt_to_mach(_virt)        (phys_to_machine(to_phys(_virt)))
#define mfn_to_virt(_mfn)          (to_virt(mfn_to_pfn(_mfn) << PAGE_SHIFT))
#define pfn_to_virt(_pfn)          (to_virt((_pfn) << PAGE_SHIFT))

/* Pagetable walking. */
#define pte_to_mfn(_pte)           (((_pte) & (PADDR_MASK&PAGE_MASK)) >> L1_PAGETABLE_SHIFT)
#define pte_to_virt(_pte)          to_virt(mfn_to_pfn(pte_to_mfn(_pte)) << PAGE_SHIFT)

#ifdef __x86_64__
#define virtual_to_l3(_virt)	   ((pgentry_t *)pte_to_virt(pt_base[l4_table_offset(_virt)]))
#else
#define virtual_to_l3(_virt)	   pt_base
#endif

#define virtual_to_l2(_virt)	   ({ \
	unsigned long __virt2 = (_virt); \
	(pgentry_t *) pte_to_virt(virtual_to_l3(__virt2)[l3_table_offset(__virt2)]); \
})

#define virtual_to_l1(_virt)	   ({ \
	unsigned long __virt1 = (_virt); \
	(pgentry_t *) pte_to_virt(virtual_to_l2(__virt1)[l2_table_offset(__virt1)]); \
})

#define virtual_to_pte(_virt)	   ({ \
	unsigned long __virt0 = (unsigned long) (_virt); \
	virtual_to_l1(__virt0)[l1_table_offset(__virt0)]; \
})
#define virtual_to_mfn(_virt)	   pte_to_mfn(virtual_to_pte(_virt))

#define map_frames(f, n) map_frames_ex(f, n, 1, 0, 1, DOMID_SELF, NULL, L1_PROT)
#define map_zero(n, a) map_frames_ex(&mfn_zero, n, 0, 0, a, DOMID_SELF, NULL, L1_PROT_RO)
#define do_map_zero(start, n) do_map_frames(start, &mfn_zero, n, 0, 0, DOMID_SELF, NULL, L1_PROT_RO)

pgentry_t *need_pgt(unsigned long addr);
void arch_mm_preinit(void *p);
unsigned long alloc_virt_kernel(unsigned n_pages);

void arch_mm_pre_suspend(void);
void arch_mm_post_suspend(int canceled);

#ifndef CONFIG_PARAVIRT
void arch_print_memmap(void);
#endif

#endif

#endif /* _ARCH_MM_H_ */
