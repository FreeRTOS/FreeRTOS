/* Copyright 2020 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/drivers/riscv_cpu.h>
#include <metal/hpm.h>
#include <stdint.h>

/* Macro to generate code within a switch case */
#define METAL_HPM_HANDLE_SWITCH(m)                                             \
    m(3) m(4) m(5) m(6) m(7) m(8) m(9) m(10) m(11) m(12) m(13) m(14) m(15)     \
        m(16) m(17) m(18) m(19) m(20) m(21) m(22) m(23) m(24) m(25) m(26)      \
            m(27) m(28) m(29) m(30) m(31)

/* Macro to set values into event selector register */
#define METAL_HPM_SET_EVENT_REG(x)                                             \
    case METAL_HPM_COUNTER_##x:                                                \
        __asm__ __volatile__("csrr %0, mhpmevent" #x : "=r"(val));             \
        val &= ~bitmask;                                                       \
        val |= bitmask;                                                        \
        __asm__ __volatile__("csrw mhpmevent" #x ", %0" : : "r"(val));         \
        break;

/* Macro to set values into event selector register */
#define METAL_HPM_CLR_EVENT_REG(x)                                             \
    case METAL_HPM_COUNTER_##x:                                                \
        __asm__ __volatile__("csrr %0, mhpmevent" #x : "=r"(val));             \
        val &= ~bitmask;                                                       \
        __asm__ __volatile__("csrw mhpmevent" #x ", %0" : : "r"(val));         \
        break;

/* Macro to get values from event selector register */
#define METAL_HPM_GET_EVENT_REG(x)                                             \
    case METAL_HPM_COUNTER_##x:                                                \
        __asm__ __volatile__("csrr %0, mhpmevent" #x : "=r"(val));             \
        break;

/* Macro to read HW performance monitor counter values */
#if __riscv_xlen == 32
#define METAL_HPM_GET_COUNT_REG(x)                                             \
    case METAL_HPM_COUNTER_##x:                                                \
        do {                                                                   \
            __asm__ __volatile__("csrr %0, mhpmcounter" #x "h" : "=r"(vh));    \
            __asm__ __volatile__("csrr %0, mhpmcounter" #x : "=r"(vl));        \
            __asm__ __volatile__("csrr %0, mhpmcounter" #x "h" : "=r"(vh1));   \
        } while (vh != vh1);                                                   \
        break;
#else
#define METAL_HPM_GET_COUNT_REG(x)                                             \
    case METAL_HPM_COUNTER_##x:                                                \
        __asm__ __volatile__("csrr %0, mhpmcounter" #x : "=r"(vl));            \
        break;
#endif

/* Macro to clear HW performance monitor counter values */
#if __riscv_xlen == 32
#define METAL_HPM_CLR_COUNT_REG(x)                                             \
    case METAL_HPM_COUNTER_##x:                                                \
        __asm__ __volatile__("csrw mhpmcounter" #x "h, zero");                 \
        __asm__ __volatile__("csrw mhpmcounter" #x ", zero");                  \
        __asm__ __volatile__("csrw mhpmcounter" #x "h, zero");                 \
        break;
#else
#define METAL_HPM_CLR_COUNT_REG(x)                                             \
    case METAL_HPM_COUNTER_##x:                                                \
        __asm__ __volatile__("csrw mhpmcounter" #x ", zero");                  \
        break;
#endif

/* Max available counters */
#define METAL_HPM_COUNT_MAX 32

/* Macro to check for instruction trap */
#define MCAUSE_ILLEGAL_INST 0x02

/* Return codes */
#define METAL_HPM_RET_OK 0
#define METAL_HPM_RET_NOK 1

int metal_hpm_init(struct metal_cpu *gcpu) {
    struct __metal_driver_cpu *cpu = (void *)gcpu;

    /* Check if counters are initialized or pointer is NULL */
    if ((gcpu) && (cpu->hpm_count == 0)) {
        metal_hpm_counter n;

        /* Count number of available hardware performance counters */
        cpu->hpm_count = METAL_HPM_COUNT_MAX;

        /* mcycle, mtime and minstret counters are always available */
        for (n = METAL_HPM_COUNTER_3; n < METAL_HPM_COUNTER_31; n++) {
            metal_hpm_set_event(gcpu, n, 0xFFFFFFFF);

            if (metal_hpm_get_event(gcpu, n) == 0) {
                break;
            }
        }
        cpu->hpm_count = n;

        /* TODO: mcountinhibit csr is not yet accessible.
         * As per latest RiscV privileged spec v1.11,
         * mcountinhibit controls which of the counters increment.
         * Unused counters can be disabled to reduce power consumption. */
        /* Keep all counters disabled, enable them later on as needed. */
        /* __asm__ __volatile__("csrw mcountinhibit, zero"); */

        /* Clear all counters */
        for (unsigned int i = 0; i < cpu->hpm_count; i++) {
            metal_hpm_clr_event(gcpu, i, 0xFFFFFFFF);
            metal_hpm_clear_counter(gcpu, i);
        }
    } else {
        return METAL_HPM_RET_NOK;
    }

    return METAL_HPM_RET_OK;
}

int metal_hpm_disable(struct metal_cpu *gcpu) {
    struct __metal_driver_cpu *cpu = (void *)gcpu;
    uintptr_t temp = 0, val = 0;

    /* Check if pointer is NULL */
    if (gcpu) {
        /* Disable counter access */
        __asm__ __volatile__("la %0, 1f \n\t"
                             "csrr %1, mtvec \n\t"
                             "csrw mtvec, %0 \n\t"
                             "csrw mcounteren, zero \n\t"
                             ".align 4 \n\t"
                             "1: \n\t"
                             "csrw mtvec, %1 \n\t"
                             : "+r"(val), "+r"(temp));

        /* TODO: Disable all counters */
        /* __asm__ __volatile__("csrw mcountinhibit, zero"); */

        cpu->hpm_count = 0;
    } else {
        return METAL_HPM_RET_NOK;
    }

    return METAL_HPM_RET_OK;
}

int metal_hpm_set_event(struct metal_cpu *gcpu, metal_hpm_counter counter,
                        unsigned int bitmask) {
    struct __metal_driver_cpu *cpu = (void *)gcpu;
    unsigned int val;

    /* Return error if counter is out of range or pointer is NULL */
    if ((gcpu) && (counter >= cpu->hpm_count))
        return METAL_HPM_RET_NOK;

    switch (counter) {
        /* Set event register bit mask as requested */
        METAL_HPM_HANDLE_SWITCH(METAL_HPM_SET_EVENT_REG)

    default:
        break;
    }

    return METAL_HPM_RET_OK;
}

unsigned int metal_hpm_get_event(struct metal_cpu *gcpu,
                                 metal_hpm_counter counter) {
    struct __metal_driver_cpu *cpu = (void *)gcpu;
    unsigned int val = 0;

    /* Return error if counter is out of range or pointer is NULL */
    if ((gcpu) && (counter >= cpu->hpm_count))
        return METAL_HPM_RET_NOK;

    switch (counter) {
        /* Read event registers */
        METAL_HPM_HANDLE_SWITCH(METAL_HPM_GET_EVENT_REG)

    default:
        break;
    }

    return val;
}

int metal_hpm_clr_event(struct metal_cpu *gcpu, metal_hpm_counter counter,
                        unsigned int bitmask) {
    struct __metal_driver_cpu *cpu = (void *)gcpu;
    unsigned int val;

    /* Return error if counter is out of range or pointer is NULL */
    if ((gcpu) && (counter >= cpu->hpm_count))
        return METAL_HPM_RET_NOK;

    switch (counter) {
        /* Clear event registers as requested */
        METAL_HPM_HANDLE_SWITCH(METAL_HPM_CLR_EVENT_REG)

    default:
        break;
    }

    return METAL_HPM_RET_OK;
}

int metal_hpm_enable_access(struct metal_cpu *gcpu, metal_hpm_counter counter) {
    struct __metal_driver_cpu *cpu = (void *)gcpu;
    uintptr_t temp = 0, val = 0;

    /* Return error if counter is out of range or pointer is NULL */
    if ((gcpu) && (counter >= cpu->hpm_count))
        return METAL_HPM_RET_NOK;

    /* Set trap exit, to handle illegal instruction trap. */
    __asm__ __volatile__("la %0, 1f \n\t"
                         "csrr %1, mtvec \n\t"
                         "csrw mtvec, %0 \n\t"
                         "csrr %0, mcounteren \n\t"
                         "or %0, %0, %2 \n\t"
                         "csrw mcounteren, %0 \n\t"
                         ".align 4 \n\t"
                         "1: \n\t"
                         "csrw mtvec, %1 \n\t"
                         : "+r"(val), "+r"(temp)
                         : "r"(1 << counter));

    return METAL_HPM_RET_OK;
}

int metal_hpm_disable_access(struct metal_cpu *gcpu,
                             metal_hpm_counter counter) {
    struct __metal_driver_cpu *cpu = (void *)gcpu;
    uintptr_t temp = 0, val = 0;

    /* Return error if counter is out of range or pointer is NULL */
    if ((gcpu) && (counter >= cpu->hpm_count))
        return METAL_HPM_RET_NOK;

    /* Set trap exit, to handle illegal instruction trap. */
    __asm__ __volatile__("la %0, 1f \n\t"
                         "csrr %1, mtvec \n\t"
                         "csrw mtvec, %0 \n\t"
                         "csrr %0, mcounteren \n\t"
                         "and %0, %0, %2 \n\t"
                         "csrw mcounteren, %0 \n\t"
                         ".align 4 \n\t"
                         "1: \n\t"
                         "csrw mtvec, %1 \n\t"
                         : "+r"(val), "+r"(temp)
                         : "r"(~(1 << counter)));

    return METAL_HPM_RET_OK;
}

unsigned long long metal_hpm_read_counter(struct metal_cpu *gcpu,
                                          metal_hpm_counter counter) {
    struct __metal_driver_cpu *cpu = (void *)gcpu;
#if __riscv_xlen == 32
    unsigned int vh = 0, vh1 = 0, vl = 0;
#else
    unsigned long long vl = 0;
#endif

    /* Return error if counter is out of range or pointer is NULL */
    if ((gcpu) && (counter >= cpu->hpm_count))
        return METAL_HPM_RET_NOK;

    switch (counter) {
    case METAL_HPM_CYCLE:
#if __riscv_xlen == 32
        do {
            __asm__ __volatile__("csrr %0, mcycleh" : "=r"(vh));
            __asm__ __volatile__("csrr %0, mcycle" : "=r"(vl));
            __asm__ __volatile__("csrr %0, mcycleh" : "=r"(vh1));
        } while (vh != vh1);
#else
        __asm__ __volatile__("csrr %0, mcycle" : "=r"(vl));
#endif
        break;
    case METAL_HPM_TIME:
        /* mtime is memory mapped within CLINT block,
         * Use CLINT APIs to access this register. */
        return METAL_HPM_RET_NOK;
        break;

    case METAL_HPM_INSTRET:
#if __riscv_xlen == 32
        do {
            __asm__ __volatile__("csrr %0, minstreth" : "=r"(vh));
            __asm__ __volatile__("csrr %0, minstret" : "=r"(vl));
            __asm__ __volatile__("csrr %0, minstreth" : "=r"(vh1));
        } while (vh != vh1);
#else
        __asm__ __volatile__("csrr %0, minstret" : "=r"(vl));
#endif
        break;
        METAL_HPM_HANDLE_SWITCH(METAL_HPM_GET_COUNT_REG)

    default:
        break;
    }

#if __riscv_xlen == 32
    return ((((unsigned long long)vh) << 32) | vl);
#else
    return vl;
#endif
}

int metal_hpm_clear_counter(struct metal_cpu *gcpu, metal_hpm_counter counter) {
    struct __metal_driver_cpu *cpu = (void *)gcpu;
    /* Return error if counter is out of range or pointer is NULL */
    if ((gcpu) && (counter >= cpu->hpm_count))
        return METAL_HPM_RET_NOK;

    switch (counter) {
    case METAL_HPM_CYCLE:
#if __riscv_xlen == 32
        __asm__ __volatile__("csrw mcycleh, zero");
        __asm__ __volatile__("csrw mcycle, zero");
        __asm__ __volatile__("csrw mcycleh, zero");
#else
        __asm__ __volatile__("csrw mcycle, zero");
#endif
        break;
    case METAL_HPM_TIME:
        /* mtime is memory mapped within CLINT block */
        return METAL_HPM_RET_NOK;
        break;
    case METAL_HPM_INSTRET:
#if __riscv_xlen == 32
        __asm__ __volatile__("csrw minstreth, zero");
        __asm__ __volatile__("csrw minstret, zero");
        __asm__ __volatile__("csrw minstreth, zero");
#else
        __asm__ __volatile__("csrw minstret, zero");
#endif
        break;
        METAL_HPM_HANDLE_SWITCH(METAL_HPM_CLR_COUNT_REG)

    default:
        break;
    }

    return METAL_HPM_RET_OK;
}
