/* -*-  Mode:C; c-basic-offset:4; tab-width:4 -*-
 *
 * (C) 2021 - Juergen Gross, SUSE Software Solutions Germany GmbH
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

#include <os.h>
#include <console.h>
#include <e820.h>
#include <hypervisor.h>
#include <gnttab.h>
#include <mm.h>
#include <types.h>
#include <xen/memory.h>

extern uint8_t grant_table;

#ifdef CONFIG_PARAVIRT
grant_entry_v1_t *arch_init_gnttab(int nr_grant_frames)
{
    struct gnttab_setup_table setup;
    unsigned long frames[nr_grant_frames];

    setup.dom = DOMID_SELF;
    setup.nr_frames = nr_grant_frames;
    set_xen_guest_handle(setup.frame_list, frames);

    HYPERVISOR_grant_table_op(GNTTABOP_setup_table, &setup, 1);
    return map_frames(frames, nr_grant_frames);
}
#else
grant_entry_v1_t *arch_init_gnttab(int nr_grant_frames)
{
    int i, rc;
    struct xen_add_to_physmap xatp;
    unsigned long pfn;
    
    for ( i = 0; i < nr_grant_frames; i++ )
    {
        xatp.domid = DOMID_SELF;
        xatp.idx = i;
        xatp.space = XENMAPSPACE_grant_table;
        xatp.gpfn = (unsigned long)(&grant_table + (4096 * i)) >> 12;
        rc = HYPERVISOR_memory_op(XENMEM_add_to_physmap, &xatp);
        if ( rc )
        {
            xprintk("could not init grant table\n");
            do_exit();
        }
    }

    return (grant_entry_v1_t *)&grant_table;
}
#endif

void arch_suspend_gnttab(grant_entry_v1_t *gnttab_table, int nr_grant_frames)
{
#ifdef CONFIG_PARAVIRT
    int i;

    for ( i = 0; i < nr_grant_frames; i++ )
    {
        HYPERVISOR_update_va_mapping((unsigned long)gnttab_table + PAGE_SIZE * i,
                __pte(0x0 << PAGE_SHIFT), UVMF_INVLPG);
    }
#endif
    return;
}

void arch_resume_gnttab(grant_entry_v1_t *gnttab_table, int nr_grant_frames)
{
    struct gnttab_setup_table setup;
    unsigned long frames[nr_grant_frames];
#ifdef CONFIG_PARAVIRT
    int i;
#endif

    setup.dom = DOMID_SELF;
    setup.nr_frames = nr_grant_frames;
    set_xen_guest_handle(setup.frame_list, frames);

    HYPERVISOR_grant_table_op(GNTTABOP_setup_table, &setup, 1);

#ifdef CONFIG_PARAVIRT
    for ( i = 0; i < nr_grant_frames; i++ )
    {
        HYPERVISOR_update_va_mapping((unsigned long)gnttab_table + PAGE_SIZE * i,
                __pte((frames[i] << PAGE_SHIFT) | L1_PROT), UVMF_INVLPG);
    }
#endif
}
