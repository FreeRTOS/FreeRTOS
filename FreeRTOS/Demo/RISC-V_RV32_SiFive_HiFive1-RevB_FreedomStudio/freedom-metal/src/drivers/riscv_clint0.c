/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_RISCV_CLINT0

#include <metal/cpu.h>
#include <metal/drivers/riscv_clint0.h>
#include <metal/io.h>
#include <metal/machine.h>

unsigned long long
__metal_clint0_mtime_get(struct __metal_driver_riscv_clint0 *clint) {
    __metal_io_u32 lo, hi;
    unsigned long control_base =
        __metal_driver_sifive_clint0_control_base(&clint->controller);

    /* Guard against rollover when reading */
    do {
        hi = __METAL_ACCESS_ONCE(
            (__metal_io_u32 *)(control_base + METAL_RISCV_CLINT0_MTIME + 4));
        lo = __METAL_ACCESS_ONCE(
            (__metal_io_u32 *)(control_base + METAL_RISCV_CLINT0_MTIME));
    } while (__METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base +
                                                    METAL_RISCV_CLINT0_MTIME +
                                                    4)) != hi);

    return (((unsigned long long)hi) << 32) | lo;
}

int __metal_driver_riscv_clint0_mtimecmp_set(struct metal_interrupt *controller,
                                             int hartid,
                                             unsigned long long time) {
    struct __metal_driver_riscv_clint0 *clint =
        (struct __metal_driver_riscv_clint0 *)(controller);
    unsigned long control_base =
        __metal_driver_sifive_clint0_control_base(&clint->controller);
    /* Per spec, the RISC-V MTIME/MTIMECMP registers are 64 bit,
     * and are NOT internally latched for multiword transfers.
     * Need to be careful about sequencing to avoid triggering
     * spurious interrupts: For that set the high word to a max
     * value first.
     */
    __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base + (8 * hartid) +
                                           METAL_RISCV_CLINT0_MTIMECMP_BASE +
                                           4)) = 0xFFFFFFFF;
    __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base + (8 * hartid) +
                                           METAL_RISCV_CLINT0_MTIMECMP_BASE)) =
        (__metal_io_u32)time;
    __METAL_ACCESS_ONCE((__metal_io_u32 *)(control_base + (8 * hartid) +
                                           METAL_RISCV_CLINT0_MTIMECMP_BASE +
                                           4)) = (__metal_io_u32)(time >> 32);
    return 0;
}

static struct metal_interrupt *_get_cpu_intc() {
    int hartid = 0;
    __asm__ volatile("csrr %[hartid], mhartid"
                     : [hartid] "=r"(hartid)::"memory");

    struct metal_cpu *cpu = metal_cpu_get(hartid);

    return metal_cpu_interrupt_controller(cpu);
}

void __metal_driver_riscv_clint0_init(struct metal_interrupt *controller) {
    int num_interrupts =
        __metal_driver_sifive_clint0_num_interrupts(controller);
    struct __metal_driver_riscv_clint0 *clint =
        (struct __metal_driver_riscv_clint0 *)(controller);

    if (!clint->init_done) {
        /* Register its interrupts with with parent controller, aka sw and
         * timerto its default isr */
        for (int i = 0; i < num_interrupts; i++) {
            struct metal_interrupt *intc =
                __metal_driver_sifive_clint0_interrupt_parents(controller, i);
            int line =
                __metal_driver_sifive_clint0_interrupt_lines(controller, i);
            intc->vtable->interrupt_register(intc, line, NULL, controller);
        }
        clint->init_done = 1;
    }
}

int __metal_driver_riscv_clint0_register(struct metal_interrupt *controller,
                                         int id, metal_interrupt_handler_t isr,
                                         void *priv) {
    int rc = -1;
    metal_vector_mode mode = __metal_controller_interrupt_vector_mode();
    struct metal_interrupt *intc = NULL;
    struct metal_interrupt *cpu_intc = _get_cpu_intc();
    int num_interrupts =
        __metal_driver_sifive_clint0_num_interrupts(controller);

    if ((mode != METAL_VECTOR_MODE) && (mode != METAL_DIRECT_MODE)) {
        return rc;
    }

    for (int i = 0; i < num_interrupts; i++) {
        int line = __metal_driver_sifive_clint0_interrupt_lines(controller, i);
        intc = __metal_driver_sifive_clint0_interrupt_parents(controller, i);
        if (cpu_intc == intc && id == line) {
            break;
        }
        intc = NULL;
    }

    /* Register its interrupts with parent controller */
    if (intc) {
        rc = intc->vtable->interrupt_register(intc, id, isr, priv);
    }
    return rc;
}

int __metal_driver_riscv_clint0_vector_register(
    struct metal_interrupt *controller, int id,
    metal_interrupt_vector_handler_t isr, void *priv) {
    /* Not supported. User can override the 'weak' handler with their own */
    int rc = -1;
    return rc;
}

metal_vector_mode __metal_driver_riscv_clint0_get_vector_mode(
    struct metal_interrupt *controller) {
    return __metal_controller_interrupt_vector_mode();
}

int __metal_driver_riscv_clint0_set_vector_mode(
    struct metal_interrupt *controller, metal_vector_mode mode) {
    int rc = -1;
    struct metal_interrupt *intc = _get_cpu_intc();

    if (intc) {
        /* Valid vector modes are VECTOR and DIRECT, anything else is invalid
         * (-1) */
        switch (mode) {
        case METAL_VECTOR_MODE:
        case METAL_DIRECT_MODE:
            rc = intc->vtable->interrupt_set_vector_mode(intc, mode);
            break;
        default:
            break;
        }
    }
    return rc;
}

int __metal_driver_riscv_clint0_enable(struct metal_interrupt *controller,
                                       int id) {
    int rc = -1;

    if (id) {
        struct metal_interrupt *intc = NULL;
        struct metal_interrupt *cpu_intc = _get_cpu_intc();
        int num_interrupts =
            __metal_driver_sifive_clint0_num_interrupts(controller);

        for (int i = 0; i < num_interrupts; i++) {
            int line =
                __metal_driver_sifive_clint0_interrupt_lines(controller, i);
            intc =
                __metal_driver_sifive_clint0_interrupt_parents(controller, i);
            if (cpu_intc == intc && id == line) {
                break;
            }
            intc = NULL;
        }

        /* Enable its interrupts with parent controller */
        if (intc) {
            rc = intc->vtable->interrupt_enable(intc, id);
        }
    }

    return rc;
}

int __metal_driver_riscv_clint0_disable(struct metal_interrupt *controller,
                                        int id) {
    int rc = -1;

    if (id) {
        struct metal_interrupt *intc = NULL;
        struct metal_interrupt *cpu_intc = _get_cpu_intc();
        int num_interrupts =
            __metal_driver_sifive_clint0_num_interrupts(controller);

        for (int i = 0; i < num_interrupts; i++) {
            int line =
                __metal_driver_sifive_clint0_interrupt_lines(controller, i);
            intc =
                __metal_driver_sifive_clint0_interrupt_parents(controller, i);
            if (cpu_intc == intc && id == line) {
                break;
            }
            intc = NULL;
        }

        /* Disable its interrupts with parent controller */
        if (intc) {
            rc = intc->vtable->interrupt_disable(intc, id);
        }
    }

    return rc;
}

int __metal_driver_riscv_clint0_command_request(
    struct metal_interrupt *controller, int command, void *data) {
    int hartid;
    int rc = -1;
    struct __metal_driver_riscv_clint0 *clint =
        (struct __metal_driver_riscv_clint0 *)(controller);
    unsigned long control_base =
        __metal_driver_sifive_clint0_control_base(controller);

    switch (command) {
    case METAL_TIMER_MTIME_GET:
        if (data) {
            *(unsigned long long *)data = __metal_clint0_mtime_get(clint);
            rc = 0;
        }
        break;
    case METAL_SOFTWARE_IPI_CLEAR:
        if (data) {
            hartid = *(int *)data;
            __METAL_ACCESS_ONCE((
                __metal_io_u32 *)(control_base + (hartid * 4))) = METAL_DISABLE;
            rc = 0;
        }
        break;
    case METAL_SOFTWARE_IPI_SET:
        if (data) {
            hartid = *(int *)data;
            __METAL_ACCESS_ONCE(
                (__metal_io_u32 *)(control_base + (hartid * 4))) = METAL_ENABLE;
            /* Callers of this function assume it's blocking, in the sense that
             * the IPI is guarnteed to have been delivered before the function
             * returns.  We can't really guarnteed it's delivered, but we can
             * read back the control register after writing it in at least an
             * attempt to provide some semblence of ordering here.  The fence
             * ensures the read is order after the write -- it wouldn't be
             * necessary under RVWMO because this is the same address, but we
             * don't have an IO memory model so I'm being a bit overkill here.
             */
            __METAL_IO_FENCE(o, i);
            rc = __METAL_ACCESS_ONCE(
                (__metal_io_u32 *)(control_base + (hartid * 4)));
            rc = 0;
        }
        break;
    case METAL_SOFTWARE_MSIP_GET:
        rc = 0;
        if (data) {
            hartid = *(int *)data;
            rc = __METAL_ACCESS_ONCE(
                (__metal_io_u32 *)(control_base + (hartid * 4)));
        }
        break;
    default:
        break;
    }

    return rc;
}

int __metal_driver_riscv_clint0_clear_interrupt(
    struct metal_interrupt *controller, int id) {
    int hartid = metal_cpu_get_current_hartid();
    return __metal_driver_riscv_clint0_command_request(
        controller, METAL_SOFTWARE_IPI_CLEAR, &hartid);
}

int __metal_driver_riscv_clint0_set_interrupt(
    struct metal_interrupt *controller, int id) {
    int hartid = metal_cpu_get_current_hartid();
    return __metal_driver_riscv_clint0_command_request(
        controller, METAL_SOFTWARE_IPI_SET, &hartid);
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_riscv_clint0) = {
    .clint_vtable.interrupt_init = __metal_driver_riscv_clint0_init,
    .clint_vtable.interrupt_register = __metal_driver_riscv_clint0_register,
    .clint_vtable.interrupt_vector_register =
        __metal_driver_riscv_clint0_vector_register,
    .clint_vtable.interrupt_enable = __metal_driver_riscv_clint0_enable,
    .clint_vtable.interrupt_disable = __metal_driver_riscv_clint0_disable,
    .clint_vtable.interrupt_get_vector_mode =
        __metal_driver_riscv_clint0_get_vector_mode,
    .clint_vtable.interrupt_set_vector_mode =
        __metal_driver_riscv_clint0_set_vector_mode,
    .clint_vtable.interrupt_clear = __metal_driver_riscv_clint0_clear_interrupt,
    .clint_vtable.interrupt_set = __metal_driver_riscv_clint0_set_interrupt,
    .clint_vtable.command_request = __metal_driver_riscv_clint0_command_request,
    .clint_vtable.mtimecmp_set = __metal_driver_riscv_clint0_mtimecmp_set,
};

#endif /* METAL_RISCV_CLINT0 */

typedef int no_empty_translation_units;
