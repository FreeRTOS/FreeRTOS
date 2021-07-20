/* Copyright 2020 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/drivers/sifive_buserror0.h>
#include <metal/machine/platform.h>
#include <stddef.h>
#include <stdint.h>

#ifdef METAL_SIFIVE_BUSERROR0

#include <metal/cpu.h>
#include <metal/init.h>
#include <metal/io.h>
#include <metal/machine.h>

/* Enable all events on all hart bus error units */
METAL_CONSTRUCTOR(metal_driver_sifive_buserror_init) {
    for (int hart = 0; hart < metal_cpu_get_num_harts(); hart++) {
        struct metal_cpu *cpu = metal_cpu_get(hart);
        if (cpu != NULL) {
            struct metal_buserror *beu = metal_cpu_get_buserror(cpu);
            if (beu != NULL) {
                metal_buserror_set_event_enabled(beu, METAL_BUSERROR_EVENT_ALL,
                                                 true);
            }
        }
    }
}

int metal_buserror_set_event_enabled(struct metal_buserror *beu,
                                     metal_buserror_event_t events,
                                     bool enabled) {
    uintptr_t base = __metal_driver_sifive_buserror0_control_base(beu);
    if (base == (uintptr_t)NULL) {
        return 1;
    }
    if (!(events & METAL_BUSERROR_EVENT_ANY)) {
        return 2;
    }

    uintptr_t reg_enable = base + METAL_SIFIVE_BUSERROR0_ENABLE;

    if (enabled) {
        __METAL_ACCESS_ONCE((__metal_io_u8 *)reg_enable) |= events;
    } else {
        __METAL_ACCESS_ONCE((__metal_io_u8 *)reg_enable) &= ~events;
    }

    if (!(events & __METAL_ACCESS_ONCE((__metal_io_u8 *)reg_enable))) {
        return __METAL_ACCESS_ONCE((__metal_io_u8 *)reg_enable);
    }

    return 0;
}

metal_buserror_event_t
metal_buserror_get_event_enabled(struct metal_buserror *beu) {
    uintptr_t base = __metal_driver_sifive_buserror0_control_base(beu);
    if (base == (uintptr_t)NULL) {
        return 1;
    }

    uintptr_t reg_enable = base + METAL_SIFIVE_BUSERROR0_ENABLE;

    return __METAL_ACCESS_ONCE((__metal_io_u8 *)reg_enable);
}

int metal_buserror_set_platform_interrupt(struct metal_buserror *beu,
                                          metal_buserror_event_t events,
                                          bool enabled) {
    uintptr_t base = __metal_driver_sifive_buserror0_control_base(beu);
    if (base == (uintptr_t)NULL) {
        return 1;
    }
    if (!(events & METAL_BUSERROR_EVENT_ANY)) {
        return 2;
    }

    uintptr_t platform_interrupt =
        base + METAL_SIFIVE_BUSERROR0_PLATFORM_INTERRUPT;

    if (enabled) {
        __METAL_ACCESS_ONCE((__metal_io_u8 *)platform_interrupt) |= events;
    } else {
        __METAL_ACCESS_ONCE((__metal_io_u8 *)platform_interrupt) &= ~events;
    }

    return 0;
}

int metal_buserror_set_local_interrupt(struct metal_buserror *beu,
                                       metal_buserror_event_t events,
                                       bool enabled) {
    uintptr_t base = __metal_driver_sifive_buserror0_control_base(beu);
    if (base == (uintptr_t)NULL) {
        return 1;
    }
    if (!(events & METAL_BUSERROR_EVENT_ANY)) {
        return 2;
    }

    uintptr_t local_interrupt = base + METAL_SIFIVE_BUSERROR0_LOCAL_INTERRUPT;

    if (enabled) {
        __METAL_ACCESS_ONCE((__metal_io_u8 *)local_interrupt) |= events;
    } else {
        __METAL_ACCESS_ONCE((__metal_io_u8 *)local_interrupt) &= ~events;
    }

    return 0;
}

metal_buserror_event_t metal_buserror_get_cause(struct metal_buserror *beu) {
    uintptr_t base = __metal_driver_sifive_buserror0_control_base(beu);
    if (base == (uintptr_t)NULL) {
        return METAL_BUSERROR_EVENT_INVALID;
    }

    uintptr_t cause = base + METAL_SIFIVE_BUSERROR0_CAUSE;

    return (metal_buserror_event_t)(
        1 << __METAL_ACCESS_ONCE((__metal_io_u8 *)cause));
}

int metal_buserror_clear_cause(struct metal_buserror *beu) {
    uintptr_t base = __metal_driver_sifive_buserror0_control_base(beu);
    if (base == (uintptr_t)NULL) {
        /* We return (1 << 8) because the value of the cause register
         * can never equal that value */
        return (1 << 8);
    }

    uintptr_t cause = base + METAL_SIFIVE_BUSERROR0_CAUSE;
    __METAL_ACCESS_ONCE((__metal_io_u8 *)cause) = METAL_BUSERROR_EVENT_NONE;

    return __METAL_ACCESS_ONCE((__metal_io_u8 *)cause);
}

uintptr_t metal_buserror_get_event_address(struct metal_buserror *beu) {
    uintptr_t base = __metal_driver_sifive_buserror0_control_base(beu);
    if (base == (uintptr_t)NULL) {
        return 0;
    }

    uintptr_t value = base + METAL_SIFIVE_BUSERROR0_VALUE;

    return __METAL_ACCESS_ONCE((__metal_io_u8 *)value);
}

bool metal_buserror_is_event_accrued(struct metal_buserror *beu,
                                     metal_buserror_event_t events) {
    uintptr_t base = __metal_driver_sifive_buserror0_control_base(beu);
    if (base == (uintptr_t)NULL) {
        return false;
    }

    uintptr_t accrued = base + METAL_SIFIVE_BUSERROR0_ACCRUED;

    if (!(events & METAL_BUSERROR_EVENT_ANY)) {
        return false;
    }

    return !!(events & __METAL_ACCESS_ONCE((__metal_io_u8 *)accrued));
}

int metal_buserror_clear_event_accrued(struct metal_buserror *beu,
                                       metal_buserror_event_t events) {
    uintptr_t base = __metal_driver_sifive_buserror0_control_base(beu);
    if (base == (uintptr_t)NULL) {
        /* We return (1 << 8) because the value of the accrued register
         * can never equal that value */
        return (1 << 8);
    }

    uintptr_t accrued = base + METAL_SIFIVE_BUSERROR0_ACCRUED;

    if (!(events & METAL_BUSERROR_EVENT_ANY)) {
        /* We return (1 << 9) because the value of the accrued register
         * can never equal that value */
        return (1 << 9);
    } else {
        __METAL_ACCESS_ONCE((__metal_io_u8 *)accrued) &= ~events;
        if (events & __METAL_ACCESS_ONCE((__metal_io_u8 *)accrued)) {
            return __METAL_ACCESS_ONCE((__metal_io_u8 *)accrued);
        }
    }

    return 0;
}

struct metal_interrupt *
metal_buserror_get_platform_interrupt_parent(struct metal_buserror *beu) {
    return __metal_driver_sifive_buserror0_interrupt_parent(beu);
}

int metal_buserror_get_platform_interrupt_id(struct metal_buserror *beu) {
    return __metal_driver_sifive_buserror0_interrupt_id(beu);
}

int metal_buserror_get_local_interrupt_id(struct metal_buserror *beu) {
    return 128;
}

#else

int metal_buserror_set_event_enabled(struct metal_buserror *beu,
                                     metal_buserror_event_t event,
                                     bool enabled) {
    return 1;
}

int metal_buserror_set_platform_interrupt(struct metal_buserror *beu,
                                          metal_buserror_event_t event,
                                          bool enabled) {
    return 1;
}

int metal_buserror_set_local_interrupt(struct metal_buserror *beu,
                                       metal_buserror_event_t event,
                                       bool enabled) {
    return 1;
}

metal_buserror_event_t metal_buserror_get_cause(struct metal_buserror *beu) {
    return METAL_BUSERROR_EVENT_INVALID;
}

int metal_buserror_clear_cause(struct metal_buserror *beu) { return (1 << 9); }

uintptr_t metal_buserror_get_event_address(struct metal_buserror *beu) {
    return 0;
}

bool metal_buserror_is_event_accrued(struct metal_buserror *beu,
                                     metal_buserror_event_t event) {
    return false;
}

int metal_buserror_clear_event_accrued(struct metal_buserror *beu,
                                       metal_buserror_event_t event) {
    return (1 << 8);
}

struct metal_interrupt *
metal_buserror_get_platform_interrupt_parent(struct metal_buserror *beu) {
    return NULL;
}

int metal_buserror_get_platform_interrupt_id(struct metal_buserror *beu) {
    return 0;
}

int metal_buserror_get_local_interrupt_id(struct metal_buserror *beu) {
    return 0;
}

#endif
