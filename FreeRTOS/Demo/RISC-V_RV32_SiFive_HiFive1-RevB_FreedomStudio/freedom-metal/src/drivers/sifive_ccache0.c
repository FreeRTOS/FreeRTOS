/* Copyright 2020 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_SIFIVE_CCACHE0

#include <metal/drivers/sifive_ccache0.h>
#include <metal/init.h>
#include <metal/machine.h>
#include <stdint.h>

/* Macros to access memory mapped registers */
#define REGW(x) *(volatile uint32_t *)(METAL_SIFIVE_CCACHE0_0_BASE_ADDRESS + x)

#define REGD(x) *(volatile uint64_t *)(METAL_SIFIVE_CCACHE0_0_BASE_ADDRESS + x)

/* Macros to specify register bit shift */
#define REG_SHIFT_4 4
#define REG_SHIFT_8 8
#define REG_SHIFT_16 16
#define REG_SHIFT_24 24

#define SIFIVE_CCACHE0_BYTE_MASK 0xFFUL

static int sifive_ccache0_interrupts[] = METAL_SIFIVE_CCACHE0_INTERRUPTS;

/* Initialize cache at start-up via metal constructors */
METAL_CONSTRUCTOR(_sifive_ccache0_init) { sifive_ccache0_init(); }

/* Linker symbols to calculate LIM allocated size */
extern char metal_segment_lim_target_start, metal_segment_lim_target_end;

int sifive_ccache0_init(void) {
    int ret;

    sifive_ccache0_config config;

    /* Get cache configuration data */
    sifive_ccache0_get_config(&config);

    int lim_size =
        &metal_segment_lim_target_end - &metal_segment_lim_target_start;

    if (lim_size) { /* Do not enable cache ways, corresponding to LIM area in
                       use. */
        while (lim_size > 0) {
            lim_size -= (config.block_size * config.num_sets * config.num_bank);
            config.num_ways--;
        }
    }

    /* Enable ways */
    ret = sifive_ccache0_set_enabled_ways(config.num_ways);

    return ret;
}

void sifive_ccache0_get_config(sifive_ccache0_config *config) {
    uint32_t val;

    if (config) /* Check for NULL */
    {
        val = REGW(METAL_SIFIVE_CCACHE0_CONFIG);

        /* Populate cache configuration data */
        config->num_bank = (val & SIFIVE_CCACHE0_BYTE_MASK);
        config->num_ways = ((val >> REG_SHIFT_8) & SIFIVE_CCACHE0_BYTE_MASK);
        config->num_sets =
            2 << (((val >> REG_SHIFT_16) & SIFIVE_CCACHE0_BYTE_MASK) - 1);
        config->block_size =
            2 << (((val >> REG_SHIFT_24) & SIFIVE_CCACHE0_BYTE_MASK) - 1);
    }
}

uint32_t sifive_ccache0_get_enabled_ways(void) {

    uint32_t val = 0;

    val = SIFIVE_CCACHE0_BYTE_MASK & REGW(METAL_SIFIVE_CCACHE0_WAYENABLE);

    /* The stored number is the way index, so increment by 1 */
    val++;

    return val;
}

int sifive_ccache0_set_enabled_ways(uint32_t ways) {

    int ret = 0;

    /* We can't decrease the number of enabled ways */
    if (sifive_ccache0_get_enabled_ways() > ways) {
        ret = -1;
    } else {
        /* The stored value is the index, so subtract one */
        uint32_t value = 0xFF & (ways - 1);

        /* Set the number of enabled ways */
        REGW(METAL_SIFIVE_CCACHE0_WAYENABLE) = value;

        /* Make sure the number of ways was set correctly */
        if (sifive_ccache0_get_enabled_ways() != ways) {
            ret = -2;
        }
    }

    return ret;
}

void sifive_ccache0_inject_ecc_error(uint32_t bitindex,
                                     sifive_ccache0_ecc_errtype_t type) {
    /* Induce ECC error at given bit index and location */
    REGW(METAL_SIFIVE_CCACHE0_ECCINJECTERROR) =
        (uint32_t)(((type & 0x01) << REG_SHIFT_16) | (bitindex & 0xFF));
}

void sifive_ccache0_flush(uintptr_t flush_addr) {
    /* Block memory access until operation completed */
    __asm volatile("fence rw, io" : : : "memory");

#if __riscv_xlen == 32
    REGW(METAL_SIFIVE_CCACHE0_FLUSH32) = flush_addr >> REG_SHIFT_4;
#else
    REGD(METAL_SIFIVE_CCACHE0_FLUSH64) = flush_addr;
#endif

    __asm volatile("fence io, rw" : : : "memory");
}

uintptr_t sifive_ccache0_get_ecc_fix_addr(sifive_ccache0_ecc_errtype_t type) {
    uintptr_t addr = 0;

    switch (type) {
        /* Get most recently ECC corrected address */
    case SIFIVE_CCACHE0_DATA:
        addr = (uintptr_t)REGD(METAL_SIFIVE_CCACHE0_DATECCFIXLOW);
        break;

    case SIFIVE_CCACHE0_DIR:
        addr = (uintptr_t)REGD(METAL_SIFIVE_CCACHE0_DIRECCFIXLOW);
        break;
    }

    return addr;
}

uint32_t sifive_ccache0_get_ecc_fix_count(sifive_ccache0_ecc_errtype_t type) {
    uint32_t count = 0;

    switch (type) {
        /* Get number of times ECC errors were corrected */
    case SIFIVE_CCACHE0_DATA:
        count = REGW(METAL_SIFIVE_CCACHE0_DATECCFIXCOUNT);
        break;

    case SIFIVE_CCACHE0_DIR:
        count = REGW(METAL_SIFIVE_CCACHE0_DIRECCFIXCOUNT);
        break;
    }

    return count;
}

uintptr_t sifive_ccache0_get_ecc_fail_addr(sifive_ccache0_ecc_errtype_t type) {
    uintptr_t addr = 0;

    switch (type) {
        /*  Get address location of most recent uncorrected ECC error */
    case SIFIVE_CCACHE0_DATA:
        addr = (uintptr_t)REGD(METAL_SIFIVE_CCACHE0_DATECCFAILLOW);
        break;

    case SIFIVE_CCACHE0_DIR:
        addr = (uintptr_t)REGD(METAL_SIFIVE_CCACHE0_DIRECCFAILLOW);
        break;
    }

    return addr;
}

uint32_t sifive_ccache0_get_ecc_fail_count(sifive_ccache0_ecc_errtype_t type) {
    uint32_t count = 0;

    switch (type) {
        /* Get number of times ECC errors were not corrected */
    case SIFIVE_CCACHE0_DATA:
        count = REGW(METAL_SIFIVE_CCACHE0_DATECCFAILCOUNT);
        break;

    case SIFIVE_CCACHE0_DIR:
        count = REGW(METAL_SIFIVE_CCACHE0_DIRECCFAILCOUNT);
        break;
    }

    return count;
}

uint64_t sifive_ccache0_get_way_mask(uint32_t master_id) {
    uint64_t val = 0;

    /* Get way mask for given master ID */
    val = REGD(METAL_SIFIVE_CCACHE0_WAYMASK0 + master_id * 8);

    return val;
}

int sifive_ccache0_set_way_mask(uint32_t master_id, uint64_t waymask) {

    /* Set way mask for given master ID */
    REGD(METAL_SIFIVE_CCACHE0_WAYMASK0 + master_id * 8) = waymask;

    return 0;
}

void sifive_ccache0_set_pmevent_selector(uint32_t counter, uint64_t mask) {

#if METAL_SIFIVE_CCACHE0_PERFMON_COUNTERS > 0
    if (counter < METAL_SIFIVE_CCACHE0_PERFMON_COUNTERS) {

        /* Set event selector for specified L2 event counter */
        REGD(METAL_SIFIVE_CCACHE0_PMEVENTSELECT0 + counter * 8) = mask;
    }
#endif
    return;
}

uint64_t sifive_ccache0_get_pmevent_selector(uint32_t counter) {
    uint64_t val = 0;

#if METAL_SIFIVE_CCACHE0_PERFMON_COUNTERS > 0
    if (counter < METAL_SIFIVE_CCACHE0_PERFMON_COUNTERS) {

        /* Get event selector for specified L2 event counter */
        val = REGD(METAL_SIFIVE_CCACHE0_PMEVENTSELECT0 + counter * 8);
    }
#endif
    return val;
}

void sifive_ccache0_clr_pmevent_counter(uint32_t counter) {

#if METAL_SIFIVE_CCACHE0_PERFMON_COUNTERS > 0
    if (counter < METAL_SIFIVE_CCACHE0_PERFMON_COUNTERS) {
        /* Clear specified L2 event counter */
        REGD(METAL_SIFIVE_CCACHE0_PMEVENTCOUNTER0 + counter * 8) = 0;
    }
#endif
    return;
}

uint64_t sifive_ccache0_get_pmevent_counter(uint32_t counter) {
#if __riscv_xlen == 32
    uint32_t vh = 0, vh1 = 0, vl = 0;
#else
    uint64_t val = 0;
#endif
#if METAL_SIFIVE_CCACHE0_PERFMON_COUNTERS > 0
    if (counter < METAL_SIFIVE_CCACHE0_PERFMON_COUNTERS) {
        /* Set counter register offset */
        counter *= 8;

#if __riscv_xlen == 32
        do {
            vh = REGW(METAL_SIFIVE_CCACHE0_PMEVENTCOUNTER0 + counter + 4);
            vl = REGW(METAL_SIFIVE_CCACHE0_PMEVENTCOUNTER0 + counter);
            vh1 = REGW(METAL_SIFIVE_CCACHE0_PMEVENTCOUNTER0 + counter + 4);
        } while (vh != vh1);
#else
        val = REGD(METAL_SIFIVE_CCACHE0_PMEVENTCOUNTER0 + counter);
#endif
    }
#endif
#if __riscv_xlen == 32
    return ((((unsigned long long)vh) << 32) | vl);
#else
    return val;
#endif
}

void sifive_ccache0_set_client_filter(uint64_t mask) {

    /* Set clients to be excluded from performance monitoring */
    REGD(METAL_SIFIVE_CCACHE0_PMCLIENTFILTER) = mask;
}

uint64_t sifive_ccache0_get_client_filter(void) {
    uint64_t val = 0;

    /* Get currently active client filter mask */
    val = REGD(METAL_SIFIVE_CCACHE0_PMCLIENTFILTER);

    return val;
}

int sifive_ccache0_get_interrupt_id(uint32_t src) {
    int ret = 0;

    if (src < (uint32_t)sizeof(sifive_ccache0_interrupts) / sizeof(int)) {
        ret = sifive_ccache0_interrupts[src];
    }

    return ret;
}

struct metal_interrupt *sifive_ccache0_interrupt_controller(void) {
    return METAL_SIFIVE_CCACHE0_INTERRUPT_PARENT;
}

#endif

typedef int no_empty_translation_units;
