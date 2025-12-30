/* gnttab
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

#ifndef __GNTTAB_H__
#define __GNTTAB_H__

#include <xen/grant_table.h>

void init_gnttab(void);
grant_ref_t gnttab_alloc_and_grant(void **map);
grant_ref_t gnttab_grant_access(domid_t domid, unsigned long frame,
				int readonly);
grant_ref_t gnttab_grant_transfer(domid_t domid, unsigned long pfn);
unsigned long gnttab_end_transfer(grant_ref_t gref);
int gnttab_end_access(grant_ref_t ref);
const char *gnttabop_error(int16_t status);
void fini_gnttab(void);
void suspend_gnttab(void);
void resume_gnttab(void);
grant_entry_v1_t *arch_init_gnttab(int nr_grant_frames);
void arch_suspend_gnttab(grant_entry_v1_t *gnttab_table, int nr_grant_frames);
void arch_resume_gnttab(grant_entry_v1_t *gnttab_table, int nr_grant_frames);

#endif /* !__GNTTAB_H__ */
