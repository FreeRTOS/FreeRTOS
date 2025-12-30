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

#ifndef _PARAVIRT_H
#define _PARAVIRT_H

#if defined(CONFIG_PARAVIRT)

#define mfn_to_pfn(_mfn) (machine_to_phys_mapping[(_mfn)])
#define pfn_to_mfn(_pfn) (phys_to_machine_mapping[(_pfn)])

/* for P2M */
#ifdef __x86_64__
#define P2M_SHIFT       9
#else
#define P2M_SHIFT       10
#endif
#define P2M_ENTRIES     (1UL << P2M_SHIFT)
#define P2M_MASK        (P2M_ENTRIES - 1)
#define L1_P2M_SHIFT    P2M_SHIFT
#define L2_P2M_SHIFT    (2 * P2M_SHIFT)
#define L3_P2M_SHIFT    (3 * P2M_SHIFT)
#define L1_P2M_IDX(pfn) ((pfn) & P2M_MASK)
#define L2_P2M_IDX(pfn) (((pfn) >> L1_P2M_SHIFT) & P2M_MASK)
#define L3_P2M_IDX(pfn) (((pfn) >> L2_P2M_SHIFT) & P2M_MASK)
#define INVALID_P2M_ENTRY (~0UL)

void p2m_chk_pfn(unsigned long pfn);

static inline unsigned long p2m_pages(unsigned long pages)
{
    return (pages + P2M_ENTRIES - 1) >> L1_P2M_SHIFT;
}

void arch_init_p2m(unsigned long max_pfn_p);

#else

#define mfn_to_pfn(_mfn) ((unsigned long)(_mfn))
#define pfn_to_mfn(_pfn) ((unsigned long)(_pfn))

static inline void arch_init_p2m(unsigned long max_pfn_p) { }

#endif

#if defined(CONFIG_PARAVIRT) && defined(CONFIG_BALLOON)

void arch_remap_p2m(unsigned long max_pfn);
int arch_expand_p2m(unsigned long max_pfn);

#else

static inline void arch_remap_p2m(unsigned long max_pfn) { }
static inline int arch_expand_p2m(unsigned long max_pfn)
{
    return 0;
}

#endif

#endif /* _PARAVIRT_H */
