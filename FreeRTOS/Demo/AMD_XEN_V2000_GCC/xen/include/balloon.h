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

#ifndef _BALLOON_H_
#define _BALLOON_H_

#ifdef CONFIG_BALLOON

/*
 * Always keep some pages free for allocations while ballooning or
 * interrupts disabled.
 */
#define BALLOON_EMERGENCY_PAGES   64

extern unsigned long nr_max_pfn;

void get_max_pages(void);
int balloon_up(unsigned long n_pages);
void balloon_set_nr_pages(unsigned long pages, unsigned long pfn);

void mm_alloc_bitmap_remap(void);
void arch_pfn_add(unsigned long pfn, unsigned long mfn);
int chk_free_pages(unsigned long needed);

#else /* CONFIG_BALLOON */

static inline void get_max_pages(void) { }
static inline void mm_alloc_bitmap_remap(void) { }
static inline int chk_free_pages(unsigned long needed)
{
    return needed <= nr_free_pages;
}
static inline void balloon_set_nr_pages(unsigned long pages, unsigned long pfn) { }

#endif /* CONFIG_BALLOON */
#endif /* _BALLOON_H_ */
