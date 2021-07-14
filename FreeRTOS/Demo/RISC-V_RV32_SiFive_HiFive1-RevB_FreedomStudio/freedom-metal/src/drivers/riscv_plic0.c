/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_RISCV_PLIC0

#define PLIC0_MAX_INTERRUPTS 1024

#include <metal/drivers/riscv_plic0.h>
#include <metal/interrupt.h>
#include <metal/io.h>
#include <metal/machine.h>
#include <metal/shutdown.h>

unsigned int
__metal_plic0_claim_interrupt(struct __metal_driver_riscv_plic0 *plic,
                              int context_id) {
    unsigned long control_base = __metal_driver_sifive_plic0_control_base(
        (struct metal_interrupt *)plic);
    return __METAL_ACCESS_ONCE(
        (__metal_io_u32 *)(control_base + METAL_RISCV_PLIC0_CONTEXT_BASE +
                           (context_id * METAL_RISCV_PLIC0_CONTEXT_PER_HART) +
                           METAL_RISCV_PLIC0_CONTEXT_CLAIM));
}

void __metal_plic0_complete_interrupt(struct __metal_driver_riscv_plic0 *plic,
                                      int context_id, unsigned int id) {
    unsigned long control_base = __metal_driver_sifive_plic0_control_base(
        (struct metal_interrupt *)plic);
    __METAL_ACCESS_ONCE(
        (__metal_io_u32 *)(control_base + METAL_RISCV_PLIC0_CONTEXT_BASE +
                           (context_id * METAL_RISCV_PLIC0_CONTEXT_PER_HART) +
                           METAL_RISCV_PLIC0_CONTEXT_CLAIM)) = id;
}

int __metal_plic0_set_threshold(struct metal_interrupt *controller,
                                int context_id, unsigned int threshold) {
    unsigned long control_base =
        __metal_driver_sifive_plic0_control_base(controller);
    __METAL_ACCESS_ONCE(
        (__metal_io_u32 *)(control_base + METAL_RISCV_PLIC0_CONTEXT_BASE +
                           (context_id * METAL_RISCV_PLIC0_CONTEXT_PER_HART) +
                           METAL_RISCV_PLIC0_CONTEXT_THRESHOLD)) = threshold;
    return 0;
}

unsigned int __metal_plic0_get_threshold(struct metal_interrupt *controller,
                                         int context_id) {
    unsigned long control_base =
        __metal_driver_sifive_plic0_control_base(controller);
    return __METAL_ACCESS_ONCE(
        (__metal_io_u32 *)(control_base + METAL_RISCV_PLIC0_CONTEXT_BASE +
                           (context_id * METAL_RISCV_PLIC0_CONTEXT_PER_HART) +
                           METAL_RISCV_PLIC0_CONTEXT_THRESHOLD));
}

int __metal_driver_riscv_plic0_set_priority(struct metal_interrupt *controller,
                                            int id, unsigned int priority) {
    unsigned long control_base = __metal_driver_sifive_plic0_control_base(
        (struct metal_interrupt *)controller);
    unsigned int max_priority = __metal_driver_sifive_plic0_max_priority(
        (struct metal_interrupt *)controller);
    if ((max_priority) && (priority < max_priority)) {
        __METAL_ACCESS_ONCE(
            (__metal_io_u32 *)(control_base + METAL_RISCV_PLIC0_PRIORITY_BASE +
                               (id << METAL_PLIC_SOURCE_PRIORITY_SHIFT))) =
            priority;
        return 0;
    }
    return -1;
}

unsigned int
__metal_driver_riscv_plic0_get_priority(struct metal_interrupt *controller,
                                        int id) {
    unsigned long control_base =
        __metal_driver_sifive_plic0_control_base(controller);

    return __METAL_ACCESS_ONCE(
        (__metal_io_u32 *)(control_base + METAL_RISCV_PLIC0_PRIORITY_BASE +
                           (id << METAL_PLIC_SOURCE_PRIORITY_SHIFT)));
}

int __metal_plic0_enable(struct __metal_driver_riscv_plic0 *plic,
                         int context_id, int id, int enable) {
    unsigned int current;
    unsigned long control_base = __metal_driver_sifive_plic0_control_base(
        (struct metal_interrupt *)plic);

    current = __METAL_ACCESS_ONCE(
        (__metal_io_u32 *)(control_base + METAL_RISCV_PLIC0_ENABLE_BASE +
                           (context_id * METAL_RISCV_PLIC0_ENABLE_PER_HART) +
                           (id >> METAL_PLIC_SOURCE_SHIFT) * 4));
    __METAL_ACCESS_ONCE(
        (__metal_io_u32 *)(control_base + METAL_RISCV_PLIC0_ENABLE_BASE +
                           (context_id * METAL_RISCV_PLIC0_ENABLE_PER_HART) +
                           ((id >> METAL_PLIC_SOURCE_SHIFT) * 4))) =
        enable ? (current | (1 << (id & METAL_PLIC_SOURCE_MASK)))
               : (current & ~(1 << (id & METAL_PLIC_SOURCE_MASK)));

    return 0;
}

void __metal_plic0_default_handler(int id, void *priv) { metal_shutdown(300); }

void __metal_plic0_handler(int id, void *priv) {
    struct __metal_driver_riscv_plic0 *plic = priv;
    int contextid =
        __metal_driver_sifive_plic0_context_ids(__metal_myhart_id());
    unsigned int idx = __metal_plic0_claim_interrupt(plic, contextid);
    unsigned int num_interrupts = __metal_driver_sifive_plic0_num_interrupts(
        (struct metal_interrupt *)plic);

    if ((idx < num_interrupts) && (plic->metal_exint_table[idx])) {
        plic->metal_exint_table[idx](idx,
                                     plic->metal_exdata_table[idx].exint_data);
    }

    __metal_plic0_complete_interrupt(plic, contextid, idx);
}

void __metal_driver_riscv_plic0_init(struct metal_interrupt *controller) {
    struct __metal_driver_riscv_plic0 *plic = (void *)(controller);

    if (!plic->init_done) {
        int num_interrupts, line;
        struct metal_interrupt *intc;

        for (int parent = 0; parent < __METAL_PLIC_NUM_PARENTS; parent++) {
            num_interrupts =
                __metal_driver_sifive_plic0_num_interrupts(controller);
            intc = __metal_driver_sifive_plic0_interrupt_parents(controller,
                                                                 parent);
            line =
                __metal_driver_sifive_plic0_interrupt_lines(controller, parent);

            /* Initialize ist parent controller, aka cpu_intc. */
            intc->vtable->interrupt_init(intc);

            for (int i = 0; i < PLIC0_MAX_INTERRUPTS; i++) {
                __metal_plic0_enable(plic, parent, i, METAL_DISABLE);
                if (i < num_interrupts) {
                    __metal_driver_riscv_plic0_set_priority(controller, i, 0);
                    plic->metal_exint_table[i] = NULL;
                    plic->metal_exdata_table[i].sub_int = NULL;
                    plic->metal_exdata_table[i].exint_data = NULL;
                }
            }

            __metal_plic0_set_threshold(controller, parent, 0);

            /* Register plic (ext) interrupt with with parent controller */
            intc->vtable->interrupt_register(intc, line, NULL, plic);
            /* Register plic handler for dispatching its device interrupts */
            intc->vtable->interrupt_register(intc, line, __metal_plic0_handler,
                                             plic);
            /* Enable plic (ext) interrupt with with parent controller */
            intc->vtable->interrupt_enable(intc, line);
        }
        plic->init_done = 1;
    }
}

int __metal_driver_riscv_plic0_register(struct metal_interrupt *controller,
                                        int id, metal_interrupt_handler_t isr,
                                        void *priv) {
    struct __metal_driver_riscv_plic0 *plic = (void *)(controller);

    if (id >= __metal_driver_sifive_plic0_num_interrupts(controller)) {
        return -1;
    }

    if (isr) {
        __metal_driver_riscv_plic0_set_priority(controller, id, 2);
        plic->metal_exint_table[id] = isr;
        plic->metal_exdata_table[id].exint_data = priv;
    } else {
        __metal_driver_riscv_plic0_set_priority(controller, id, 1);
        plic->metal_exint_table[id] = __metal_plic0_default_handler;
        plic->metal_exdata_table[id].sub_int = priv;
    }

    return 0;
}

int __metal_driver_riscv_plic0_enable(struct metal_interrupt *controller,
                                      int id) {
    struct __metal_driver_riscv_plic0 *plic = (void *)(controller);

    if (id >= __metal_driver_sifive_plic0_num_interrupts(controller)) {
        return -1;
    }

    __metal_plic0_enable(plic, __metal_myhart_id(), id, METAL_ENABLE);
    return 0;
}

int __metal_driver_riscv_plic0_disable(struct metal_interrupt *controller,
                                       int id) {
    struct __metal_driver_riscv_plic0 *plic = (void *)(controller);

    if (id >= __metal_driver_sifive_plic0_num_interrupts(controller)) {
        return -1;
    }
    __metal_plic0_enable(plic, __metal_myhart_id(), id, METAL_DISABLE);
    return 0;
}

int __metal_driver_riscv_plic0_set_threshold(struct metal_interrupt *controller,
                                             unsigned int threshold) {
    return __metal_plic0_set_threshold(controller, __metal_myhart_id(),
                                       threshold);
}

unsigned int
__metal_driver_riscv_plic0_get_threshold(struct metal_interrupt *controller) {
    return __metal_plic0_get_threshold(controller, __metal_myhart_id());
}

metal_affinity
__metal_driver_riscv_plic0_affinity_enable(struct metal_interrupt *controller,
                                           metal_affinity bitmask, int id) {
    metal_affinity ret = {0};
    int context;

    struct __metal_driver_riscv_plic0 *plic = (void *)(controller);

    if (id >= __metal_driver_sifive_plic0_num_interrupts(controller)) {
        metal_affinity_set_val(ret, -1);
        return ret;
    }

    for_each_metal_affinity(context, bitmask) {
        if (context != 0)
            metal_affinity_set_bit(
                ret, context,
                __metal_plic0_enable(plic, context, id, METAL_ENABLE));
    }

    return ret;
}

metal_affinity
__metal_driver_riscv_plic0_affinity_disable(struct metal_interrupt *controller,
                                            metal_affinity bitmask, int id) {
    metal_affinity ret = {0};
    int context;

    struct __metal_driver_riscv_plic0 *plic = (void *)(controller);

    if (id >= __metal_driver_sifive_plic0_num_interrupts(controller)) {
        metal_affinity_set_val(ret, -1);
        return ret;
    }

    for_each_metal_affinity(context, bitmask) {
        if (context != 0)
            metal_affinity_set_bit(
                ret, context,
                __metal_plic0_enable(plic, context, id, METAL_DISABLE));
    }

    return ret;
}

metal_affinity __metal_driver_riscv_plic0_affinity_set_threshold(
    struct metal_interrupt *controller, metal_affinity bitmask,
    unsigned int threshold) {
    metal_affinity ret = {0};
    int context;

    for_each_metal_affinity(context, bitmask) {
        if (context != 0)
            metal_affinity_set_bit(
                ret, context,
                __metal_plic0_set_threshold(controller, context, threshold));
    }

    return ret;
}

unsigned int __metal_driver_riscv_plic0_affinity_get_threshold(
    struct metal_interrupt *controller, int context_id) {
    __metal_plic0_get_threshold(controller, context_id);
    return 0;
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_riscv_plic0) = {
    .plic_vtable.interrupt_init = __metal_driver_riscv_plic0_init,
    .plic_vtable.interrupt_register = __metal_driver_riscv_plic0_register,
    .plic_vtable.interrupt_enable = __metal_driver_riscv_plic0_enable,
    .plic_vtable.interrupt_disable = __metal_driver_riscv_plic0_disable,
    .plic_vtable.interrupt_get_threshold =
        __metal_driver_riscv_plic0_get_threshold,
    .plic_vtable.interrupt_set_threshold =
        __metal_driver_riscv_plic0_set_threshold,
    .plic_vtable.interrupt_get_priority =
        __metal_driver_riscv_plic0_get_priority,
    .plic_vtable.interrupt_set_priority =
        __metal_driver_riscv_plic0_set_priority,
    .plic_vtable.interrupt_affinity_enable =
        __metal_driver_riscv_plic0_affinity_enable,
    .plic_vtable.interrupt_affinity_disable =
        __metal_driver_riscv_plic0_affinity_disable,
    .plic_vtable.interrupt_affinity_get_threshold =
        __metal_driver_riscv_plic0_affinity_get_threshold,
    .plic_vtable.interrupt_affinity_set_threshold =
        __metal_driver_riscv_plic0_affinity_set_threshold,
};

#endif /* METAL_RISCV_PLIC0 */

typedef int no_empty_translation_units;
