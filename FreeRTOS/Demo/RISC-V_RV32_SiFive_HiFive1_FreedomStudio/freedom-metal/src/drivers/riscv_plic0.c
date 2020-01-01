/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_RISCV_PLIC0

#include <metal/io.h>
#include <metal/shutdown.h>
#include <metal/drivers/riscv_plic0.h>
#include <metal/machine.h>

unsigned int __metal_plic0_claim_interrupt (struct __metal_driver_riscv_plic0 *plic)
{
    unsigned long control_base = __metal_driver_sifive_plic0_control_base((struct metal_interrupt *)plic);
    return __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base +
					      METAL_RISCV_PLIC0_CLAIM));
}

void __metal_plic0_complete_interrupt(struct __metal_driver_riscv_plic0 *plic,
				    unsigned int id)
{
    unsigned long control_base = __metal_driver_sifive_plic0_control_base((struct metal_interrupt *)plic);
    __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base +
				       METAL_RISCV_PLIC0_CLAIM)) = id;
}

int __metal_plic0_set_threshold(struct metal_interrupt *controller, unsigned int threshold)
{
    unsigned long control_base = __metal_driver_sifive_plic0_control_base(controller);
    __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base +
				       METAL_RISCV_PLIC0_THRESHOLD)) = threshold;
    return 0;
}

unsigned int __metal_plic0_get_threshold(struct metal_interrupt *controller)
{
    unsigned long control_base = __metal_driver_sifive_plic0_control_base(controller);

    return __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base +
				       METAL_RISCV_PLIC0_THRESHOLD));
}

int __metal_plic0_set_priority(struct metal_interrupt *controller, int id, unsigned int priority)
{
    unsigned long control_base = __metal_driver_sifive_plic0_control_base((struct metal_interrupt *)controller);
    unsigned int max_priority = __metal_driver_sifive_plic0_max_priority((struct metal_interrupt *)controller);
    if ( (max_priority) && (priority < max_priority) ) {
        __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base +
					   METAL_RISCV_PLIC0_PRIORITY_BASE +
					   (id << METAL_PLIC_SOURCE_PRIORITY_SHIFT))) = priority;
        return 0;
    }
    return -1;
}

unsigned int __metal_plic0_get_priority(struct metal_interrupt *controller, int id)
{
    unsigned long control_base = __metal_driver_sifive_plic0_control_base(controller);

    return __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base +
					   METAL_RISCV_PLIC0_PRIORITY_BASE +
					   (id << METAL_PLIC_SOURCE_PRIORITY_SHIFT)));
}

void __metal_plic0_enable(struct __metal_driver_riscv_plic0 *plic, int id, int enable)
{
    unsigned int current;
    unsigned long control_base = __metal_driver_sifive_plic0_control_base((struct metal_interrupt *)plic);

    current = __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base +
						METAL_RISCV_PLIC0_ENABLE_BASE +
						(id >> METAL_PLIC_SOURCE_SHIFT) * 4));
    __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base +
					METAL_RISCV_PLIC0_ENABLE_BASE +
					((id >> METAL_PLIC_SOURCE_SHIFT) * 4))) =
              enable ? (current | (1 << (id & METAL_PLIC_SOURCE_MASK)))
                     : (current & ~(1 << (id & METAL_PLIC_SOURCE_MASK)));
}

void __metal_plic0_default_handler (int id, void *priv) {
    metal_shutdown(300);
}

void __metal_plic0_handler (int id, void *priv)
{
    struct __metal_driver_riscv_plic0 *plic = priv;
    unsigned int idx = __metal_plic0_claim_interrupt(plic);
    unsigned int num_interrupts = __metal_driver_sifive_plic0_num_interrupts((struct metal_interrupt *)plic);

    if ( (idx < num_interrupts) && (plic->metal_exint_table[idx]) ) {
	plic->metal_exint_table[idx](idx,
				  plic->metal_exdata_table[idx].exint_data);
    }

    __metal_plic0_complete_interrupt(plic, idx);
}

void __metal_driver_riscv_plic0_init (struct metal_interrupt *controller)
{
    struct __metal_driver_riscv_plic0 *plic = (void *)(controller);

    if ( !plic->init_done ) {
        int num_interrupts, line;
        struct metal_interrupt *intc;

	for(int parent = 0; parent < __METAL_PLIC_NUM_PARENTS; parent++) {
	    num_interrupts = __metal_driver_sifive_plic0_num_interrupts(controller);
	    intc = __metal_driver_sifive_plic0_interrupt_parents(controller, parent);
	    line = __metal_driver_sifive_plic0_interrupt_lines(controller, parent);

	    /* Initialize ist parent controller, aka cpu_intc. */
	    intc->vtable->interrupt_init(intc);

	    for (int i = 0; i < num_interrupts; i++) {
		__metal_plic0_enable(plic, i, METAL_DISABLE);
		__metal_plic0_set_priority(controller, i, 0);
		plic->metal_exint_table[i] = NULL;
		plic->metal_exdata_table[i].sub_int = NULL;
		plic->metal_exdata_table[i].exint_data = NULL;
	    }

	    __metal_plic0_set_threshold(controller, 0);

	    /* Register plic (ext) interrupt with with parent controller */
	    intc->vtable->interrupt_register(intc, line, NULL, plic);
	    /* Register plic handler for dispatching its device interrupts */
	    intc->vtable->interrupt_register(intc, line, __metal_plic0_handler, plic);
	    /* Enable plic (ext) interrupt with with parent controller */
	    intc->vtable->interrupt_enable(intc, line);
	}
        plic->init_done = 1;
    }
}

int __metal_driver_riscv_plic0_register (struct metal_interrupt *controller,
			               int id, metal_interrupt_handler_t isr,
			               void *priv)
{
    struct __metal_driver_riscv_plic0 *plic = (void *)(controller);

    if (id >= __metal_driver_sifive_plic0_num_interrupts(controller)) {
        return -1;
    }
 
    if (isr) {
        __metal_plic0_set_priority(controller, id, 2);
	plic->metal_exint_table[id] = isr;
	plic->metal_exdata_table[id].exint_data = priv;
    } else {
        __metal_plic0_set_priority(controller, id, 1);
	plic->metal_exint_table[id] = __metal_plic0_default_handler;
	plic->metal_exdata_table[id].sub_int = priv;
    }

    return 0;
}

int __metal_driver_riscv_plic0_enable (struct metal_interrupt *controller, int id)
{
    struct __metal_driver_riscv_plic0 *plic = (void *)(controller);

    if (id >= __metal_driver_sifive_plic0_num_interrupts(controller)) {
        return -1;
    }

    __metal_plic0_enable(plic, id, METAL_ENABLE);
    return 0;
}

int __metal_driver_riscv_plic0_disable (struct metal_interrupt *controller, int id)
{
    struct __metal_driver_riscv_plic0 *plic = (void *)(controller);

    if (id >= __metal_driver_sifive_plic0_num_interrupts(controller)) {
        return -1;
    }
    __metal_plic0_enable(plic, id, METAL_DISABLE);
    return 0;
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_riscv_plic0) = {
    .plic_vtable.interrupt_init = __metal_driver_riscv_plic0_init,
    .plic_vtable.interrupt_register = __metal_driver_riscv_plic0_register,
    .plic_vtable.interrupt_enable   = __metal_driver_riscv_plic0_enable,
    .plic_vtable.interrupt_disable  = __metal_driver_riscv_plic0_disable,
    .plic_vtable.interrupt_get_threshold  = __metal_plic0_get_threshold,
    .plic_vtable.interrupt_set_threshold  = __metal_plic0_set_threshold,
    .plic_vtable.interrupt_get_priority  = __metal_plic0_get_priority,
    .plic_vtable.interrupt_set_priority  = __metal_plic0_set_priority,
};

#endif /* METAL_RISCV_PLIC0 */

typedef int no_empty_translation_units;
