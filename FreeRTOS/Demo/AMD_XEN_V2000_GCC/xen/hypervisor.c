/******************************************************************************
 * hypervisor.c
 *
 * Communication to/from hypervisor.
 *
 * Copyright (c) 2002-2003, K A Fraser
 * Copyright (c) 2005, Grzegorz Milos, gm281@cam.ac.uk,Intel Research Cambridge
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
#include <lib.h>
#include <hypervisor.h>
#include <events.h>
#include <xen/memory.h>

#define active_evtchns(sh, idx)                           \
    ((sh)->evtchn_pending[idx] & ~(sh)->evtchn_mask[idx])

#ifndef CONFIG_PARAVIRT
extern shared_info_t shared_info;

int hvm_get_parameter(int idx, uint64_t *value)
{
    struct xen_hvm_param xhv;
    int ret;

    xhv.domid = DOMID_SELF;
    xhv.index = idx;
    ret = HYPERVISOR_hvm_op(HVMOP_get_param, &xhv);
    BUG_ON(ret < 0);

    *value = xhv.value;

    return ret;
}

int hvm_set_parameter(int idx, uint64_t value)
{
    struct xen_hvm_param xhv;

    xhv.domid = DOMID_SELF;
    xhv.index = idx;
    xhv.value = value;

    printk("Making hypercall to set console input IRQ 0x%zx\n", value);
    return HYPERVISOR_hvm_op(HVMOP_set_param, &xhv);
}

shared_info_t *map_shared_info(void *p)
{
    struct xen_add_to_physmap xatp;

    xatp.domid = DOMID_SELF;
    xatp.idx = 0;
    xatp.space = XENMAPSPACE_shared_info;
    xatp.gpfn = (((uint64_t)&shared_info) >> 12);

    if ( HYPERVISOR_memory_op(XENMEM_add_to_physmap, &xatp) != 0 )
        BUG();

    return &shared_info;
}

void unmap_shared_info(void)
{
    struct xen_remove_from_physmap xrtp;

    xrtp.domid = DOMID_SELF;
    xrtp.gpfn = (((uint64_t)&shared_info) >> 12);
    if ( HYPERVISOR_memory_op(XENMEM_remove_from_physmap, &xrtp) != 0 )
        BUG();
}
#endif

void do_hypervisor_callback( void *regs)
{
    unsigned long l1, l2, l1i, l2i;
    unsigned int port;
    shared_info_t *s = HYPERVISOR_shared_info;
    vcpu_info_t *vcpu_info = &s->vcpu_info[smp_processor_id()];

    BUG_ON(!irqs_disabled());

    vcpu_info->evtchn_upcall_pending = 0;
    /* NB x86. No need for a barrier here -- XCHG is a barrier on x86. */
#if !defined(__i386__) && !defined(__x86_64__)
    /* Clear master flag /before/ clearing selector flag. */
    wmb();
#endif
    l1 = xchg(&vcpu_info->evtchn_pending_sel, 0);
    while ( l1 != 0 )
    {
        l1i = __ffs(l1);
        l1 &= ~(1UL << l1i);

        while ( (l2 = active_evtchns(s, l1i)) != 0 )
        {
            l2i = __ffs(l2);
            l2 &= ~(1UL << l2i);

            port = l1i * sizeof(unsigned long) * 8 + l2i;
            do_event(port, regs);
        }
    }
}

void force_evtchn_callback(void)
{
    vcpu_info_t *vcpu;
    unsigned long flags;

    local_irq_save(flags);

    vcpu = &HYPERVISOR_shared_info->vcpu_info[smp_processor_id()];

    while ( vcpu->evtchn_upcall_pending )
    {
        do_hypervisor_callback(NULL);
        barrier();
    };

    local_irq_restore(flags);
}

void mask_evtchn(uint32_t port)
{
    shared_info_t *s = HYPERVISOR_shared_info;

    synch_set_bit(port, &s->evtchn_mask[0]);
}

void unmask_evtchn(uint32_t port)
{
    shared_info_t *s = HYPERVISOR_shared_info;
    vcpu_info_t *vcpu_info = &s->vcpu_info[smp_processor_id()];

    synch_clear_bit(port, &s->evtchn_mask[0]);

    /*
     * The following is basically the equivalent of 'hw_resend_irq'. Just like
     * a real IO-APIC we 'lose the interrupt edge' if the channel is masked.
     */
    if ( synch_test_bit(port, &s->evtchn_pending[0]) &&
         !synch_test_and_set_bit(port / (sizeof(unsigned long) * 8),
                                 &vcpu_info->evtchn_pending_sel) )
    {
        vcpu_info->evtchn_upcall_pending = 1;
        if ( !irqs_disabled() )
            force_evtchn_callback();
    }
}

void clear_evtchn(uint32_t port)
{
    shared_info_t *s = HYPERVISOR_shared_info;

    synch_clear_bit(port, &s->evtchn_pending[0]);
}
