/* Copyright 2020 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_SIFIVE_L2PF0

#include <metal/drivers/sifive_l2pf0.h>
#include <metal/machine.h>

/* Macros to access memory mapped registers */
#define REGW(x)                                                                \
    *(volatile uint32_t *)(METAL_SIFIVE_L2PF0_0_BASE_ADDRESS +                 \
                           hartid * 0x2000 + x)

/* Macros for register bit masks */
#define REG_MASK_BITWIDTH1 0x01
#define REG_MASK_BITWIDTH4 0x0F
#define REG_MASK_BITWIDTH5 0x1F
#define REG_MASK_BITWIDTH6 0x3F
#define REG_MASK_BITWIDTH7 0x7F

/* Macros to specify register bit shift */
#define REG_BITSHIFT_1 1
#define REG_BITSHIFT_2 2
#define REG_BITSHIFT_4 4
#define REG_BITSHIFT_8 8
#define REG_BITSHIFT_9 9
#define REG_BITSHIFT_13 13
#define REG_BITSHIFT_14 14
#define REG_BITSHIFT_20 20
#define REG_BITSHIFT_21 21
#define REG_BITSHIFT_28 28

/* Macros to capture trap, if L2PF does not exist for a hart id. */
#define SIFIVE_L2PF0_TRAP_CAPTURE(exit, mtvec)                                 \
    __asm__ __volatile__("la %0, 1f \n\t"                                      \
                         "csrr %1, mtvec \n\t"                                 \
                         "csrw mtvec, %0 \n\t"                                 \
                         : "+r"(exit), "+r"(mtvec))

#define SIFIVE_L2PF0_TRAP_RESTORE(mtvec)                                       \
    __asm__ __volatile__(".align 2 \n\t"                                       \
                         "1: \n\t"                                             \
                         "csrw mtvec, %0 \n\t"                                 \
                         : "+r"(mtvec))

void sifive_l2pf0_enable(void) {
    volatile uintptr_t exit = 0, mtvec = 0;
    int hartid;
    __asm__ volatile("csrr %0, mhartid" : "=r"(hartid));

    SIFIVE_L2PF0_TRAP_CAPTURE(exit, mtvec);

    uint32_t val = REGW(METAL_SIFIVE_L2PF0_BASIC_CONTROL);

    /* Enable L2 prefetch unit for current hart */
    val |= REG_MASK_BITWIDTH1;

    REGW(METAL_SIFIVE_L2PF0_BASIC_CONTROL) = val;

    SIFIVE_L2PF0_TRAP_RESTORE(mtvec);
}

void sifive_l2pf0_disable(void) {
    volatile uintptr_t exit = 0, mtvec = 0;
    int hartid;
    __asm__ volatile("csrr %0, mhartid" : "=r"(hartid));

    SIFIVE_L2PF0_TRAP_CAPTURE(exit, mtvec);

    uint32_t val = REGW(METAL_SIFIVE_L2PF0_BASIC_CONTROL);

    /* Disable L2 prefetch unit for current hart */
    val &= ~REG_MASK_BITWIDTH1;

    REGW(METAL_SIFIVE_L2PF0_BASIC_CONTROL) = val;

    SIFIVE_L2PF0_TRAP_RESTORE(mtvec);
}

void sifive_l2pf0_get_config(sifive_l2pf0_config *config) {
    volatile uintptr_t exit = 0, mtvec = 0;
    int hartid;
    __asm__ volatile("csrr %0, mhartid" : "=r"(hartid));
    uint32_t val;

    SIFIVE_L2PF0_TRAP_CAPTURE(exit, mtvec);

    if (config) /* Check for NULL */
    {
        /* Get currently active L2 prefetch configuration values */
        val = REGW(METAL_SIFIVE_L2PF0_BASIC_CONTROL);

        config->HwPrefetchEnable = (val & REG_MASK_BITWIDTH1);
        config->CrossPageOptmDisable =
            ((val >> REG_BITSHIFT_1) & REG_MASK_BITWIDTH1);
        config->PrefetchDistance =
            ((val >> REG_BITSHIFT_2) & REG_MASK_BITWIDTH6);
        config->MaxAllowedDistance =
            ((val >> REG_BITSHIFT_8) & REG_MASK_BITWIDTH6);
        config->LinToExpThreshold =
            ((val >> REG_BITSHIFT_14) & REG_MASK_BITWIDTH6);
        config->AgeOutEn = ((val >> REG_BITSHIFT_20) & REG_MASK_BITWIDTH1);
        config->NumLdsToAgeOut =
            ((val >> REG_BITSHIFT_21) & REG_MASK_BITWIDTH7);
        config->CrossPageEn = ((val >> REG_BITSHIFT_28) & REG_MASK_BITWIDTH1);

        val = REGW(METAL_SIFIVE_L2PF0_USER_CONTROL);

        config->QFullnessThreshold = (val & REG_MASK_BITWIDTH4);
        config->HitCacheThreshold =
            ((val >> REG_BITSHIFT_4) & REG_MASK_BITWIDTH5);
        config->hitMSHRThreshold =
            ((val >> REG_BITSHIFT_9) & REG_MASK_BITWIDTH4);
        config->Window = ((val >> REG_BITSHIFT_13) & REG_MASK_BITWIDTH6);
    }
    SIFIVE_L2PF0_TRAP_RESTORE(mtvec);
}

void sifive_l2pf0_set_config(sifive_l2pf0_config *config) {
    volatile uintptr_t exit = 0, mtvec = 0;
    int hartid;
    __asm__ volatile("csrr %0, mhartid" : "=r"(hartid));
    uint32_t val;

    SIFIVE_L2PF0_TRAP_CAPTURE(exit, mtvec);

    if (config) /* Check for NULL */
    {
        /* Get values from configuration to write into register */
        val = (uint32_t)(
            (config->HwPrefetchEnable & REG_MASK_BITWIDTH1) |
            ((config->CrossPageOptmDisable & REG_MASK_BITWIDTH1)
             << REG_BITSHIFT_1) |
            ((config->PrefetchDistance & REG_MASK_BITWIDTH6)
             << REG_BITSHIFT_2) |
            ((config->MaxAllowedDistance & REG_MASK_BITWIDTH6)
             << REG_BITSHIFT_8) |
            ((config->LinToExpThreshold & REG_MASK_BITWIDTH6)
             << REG_BITSHIFT_14) |
            ((config->AgeOutEn & REG_MASK_BITWIDTH1) << REG_BITSHIFT_20) |
            ((config->NumLdsToAgeOut & REG_MASK_BITWIDTH7) << REG_BITSHIFT_21) |
            ((config->CrossPageEn & REG_MASK_BITWIDTH1) << REG_BITSHIFT_28));

        /* Set user specified L2 prefetch configuration values */
        REGW(METAL_SIFIVE_L2PF0_BASIC_CONTROL) = val;

        val = (uint32_t)(
            (config->QFullnessThreshold & REG_MASK_BITWIDTH4) |
            ((config->HitCacheThreshold & REG_MASK_BITWIDTH5)
             << REG_BITSHIFT_4) |
            ((config->hitMSHRThreshold & REG_MASK_BITWIDTH4)
             << REG_BITSHIFT_9) |
            ((config->Window & REG_MASK_BITWIDTH6) << REG_BITSHIFT_13));

        REGW(METAL_SIFIVE_L2PF0_USER_CONTROL) = val;
    }
    SIFIVE_L2PF0_TRAP_RESTORE(mtvec);
}

#endif

typedef int no_empty_translation_units;
