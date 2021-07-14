/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/cpu.h>
#include <metal/machine.h>
#include <metal/pmp.h>

#define CONFIG_TO_INT(_config) (*((char *)&(_config)))
#define INT_TO_CONFIG(_int) (*((struct metal_pmp_config *)(char *)&(_int)))

struct metal_pmp *metal_pmp_get_device(void) {
#ifdef __METAL_DT_PMP_HANDLE
    return __METAL_DT_PMP_HANDLE;
#else
    return NULL;
#endif
}

/* This function calculates the minimum granularity from the address
 * that pmpaddr takes on after writing all ones to pmpaddr when pmpcfg = 0.
 *
 * Detect the address granularity based on the position of the
 * least-significant 1 set in the address.
 *
 * For example, if the value read from pmpaddr is 0x3ffffc00, the
 * least-significant set bit is in bit 10 (counting from 0), resulting
 * in a detected granularity of 2^(10 + 2) = 4096.
 */
static uintptr_t _get_detected_granularity(uintptr_t address) {
    if (address == 0) {
        return (uintptr_t)-1;
    }

    /* Get the index of the least significant set bit */
    int index = 0;
    while (((address >> index) & 0x1) == 0) {
        index += 1;
    }

    /* The granularity is equal to 2^(index + 2) bytes */
    return (1 << (index + 2));
}

/* This function calculates the granularity requested by the user's provided
 * value for pmpaddr.
 *
 * Calculate the requested granularity based on the position of the
 * least-significant unset bit.
 *
 * For example, if the requested address is 0x20009ff, the least-significant
 * unset bit is at index 9 (counting from 0), resulting in a requested
 * granularity of 2^(9 + 3) = 4096.
 */
static uintptr_t _get_pmpaddr_granularity(uintptr_t address) {
    /* Get the index of the least significant unset bit */
    int index = 0;
    while (((address >> index) & 0x1) == 1) {
        index += 1;
    }

    /* The granularity is equal to 2^(index + 3) bytes */
    return (1 << (index + 3));
}

/* Get the number of pmp regions for the given hart */
int metal_pmp_num_regions(int hartid) {
    struct metal_cpu *cpu = metal_cpu_get(hartid);

    return __metal_driver_cpu_num_pmp_regions(cpu);
}

/* Get the number of pmp regions for the current hart */
static unsigned int _pmp_regions() {
    return metal_pmp_num_regions(metal_cpu_get_current_hartid());
}

void metal_pmp_init(struct metal_pmp *pmp) {
    if (!pmp) {
        return;
    }

    struct metal_pmp_config init_config = {
        .L = METAL_PMP_UNLOCKED,
        .A = METAL_PMP_OFF,
        .X = 0,
        .W = 0,
        .R = 0,
    };

    for (unsigned int i = 0; i < _pmp_regions(); i++) {
        metal_pmp_set_region(pmp, i, init_config, 0);
    }

    /* Detect the region granularity by writing all 1s to pmpaddr0 while
     * pmpcfg0 = 0. */
    if (metal_pmp_set_address(pmp, 0, -1) != 0) {
        /* Failed to detect granularity */
        return;
    }

    /* Calculate the granularity based on the value that pmpaddr0 takes on */
    pmp->_granularity[metal_cpu_get_current_hartid()] =
        _get_detected_granularity(metal_pmp_get_address(pmp, 0));

    /* Clear pmpaddr0 */
    metal_pmp_set_address(pmp, 0, 0);
}

int metal_pmp_set_region(struct metal_pmp *pmp, unsigned int region,
                         struct metal_pmp_config config, size_t address) {
    struct metal_pmp_config old_config;
    size_t old_address;
    size_t cfgmask;
    size_t pmpcfg;
    int rc = 0;

    if (!pmp) {
        /* Device handle cannot be NULL */
        return 1;
    }

    if (region > _pmp_regions()) {
        /* Region outside of supported range */
        return 2;
    }

    if (config.A == METAL_PMP_NA4 &&
        pmp->_granularity[metal_cpu_get_current_hartid()] > 4) {
        /* The requested granularity is too small */
        return 3;
    }

    if (config.A == METAL_PMP_NAPOT &&
        pmp->_granularity[metal_cpu_get_current_hartid()] >
            _get_pmpaddr_granularity(address)) {
        /* The requested granularity is too small */
        return 3;
    }

    rc = metal_pmp_get_region(pmp, region, &old_config, &old_address);
    if (rc) {
        /* Error reading region */
        return rc;
    }

    if (old_config.L == METAL_PMP_LOCKED) {
        /* Cannot modify locked region */
        return 4;
    }

    /* Update the address first, because if the region is being locked we won't
     * be able to modify it after we set the config */
    if (old_address != address) {
        switch (region) {
        case 0:
            __asm__("csrw pmpaddr0, %[addr]" ::[addr] "r"(address) :);
            break;
        case 1:
            __asm__("csrw pmpaddr1, %[addr]" ::[addr] "r"(address) :);
            break;
        case 2:
            __asm__("csrw pmpaddr2, %[addr]" ::[addr] "r"(address) :);
            break;
        case 3:
            __asm__("csrw pmpaddr3, %[addr]" ::[addr] "r"(address) :);
            break;
        case 4:
            __asm__("csrw pmpaddr4, %[addr]" ::[addr] "r"(address) :);
            break;
        case 5:
            __asm__("csrw pmpaddr5, %[addr]" ::[addr] "r"(address) :);
            break;
        case 6:
            __asm__("csrw pmpaddr6, %[addr]" ::[addr] "r"(address) :);
            break;
        case 7:
            __asm__("csrw pmpaddr7, %[addr]" ::[addr] "r"(address) :);
            break;
        case 8:
            __asm__("csrw pmpaddr8, %[addr]" ::[addr] "r"(address) :);
            break;
        case 9:
            __asm__("csrw pmpaddr9, %[addr]" ::[addr] "r"(address) :);
            break;
        case 10:
            __asm__("csrw pmpaddr10, %[addr]" ::[addr] "r"(address) :);
            break;
        case 11:
            __asm__("csrw pmpaddr11, %[addr]" ::[addr] "r"(address) :);
            break;
        case 12:
            __asm__("csrw pmpaddr12, %[addr]" ::[addr] "r"(address) :);
            break;
        case 13:
            __asm__("csrw pmpaddr13, %[addr]" ::[addr] "r"(address) :);
            break;
        case 14:
            __asm__("csrw pmpaddr14, %[addr]" ::[addr] "r"(address) :);
            break;
        case 15:
            __asm__("csrw pmpaddr15, %[addr]" ::[addr] "r"(address) :);
            break;
        }
    }

#if __riscv_xlen == 32
    if (CONFIG_TO_INT(old_config) != CONFIG_TO_INT(config)) {
        /* Mask to clear old pmpcfg */
        cfgmask = (0xFF << (8 * (region % 4)));
        pmpcfg = (CONFIG_TO_INT(config) << (8 * (region % 4)));

        switch (region / 4) {
        case 0:
            __asm__("csrc pmpcfg0, %[mask]" ::[mask] "r"(cfgmask) :);

            __asm__("csrs pmpcfg0, %[cfg]" ::[cfg] "r"(pmpcfg) :);
            break;
        case 1:
            __asm__("csrc pmpcfg1, %[mask]" ::[mask] "r"(cfgmask) :);

            __asm__("csrs pmpcfg1, %[cfg]" ::[cfg] "r"(pmpcfg) :);
            break;
        case 2:
            __asm__("csrc pmpcfg2, %[mask]" ::[mask] "r"(cfgmask) :);

            __asm__("csrs pmpcfg2, %[cfg]" ::[cfg] "r"(pmpcfg) :);
            break;
        case 3:
            __asm__("csrc pmpcfg3, %[mask]" ::[mask] "r"(cfgmask) :);

            __asm__("csrs pmpcfg3, %[cfg]" ::[cfg] "r"(pmpcfg) :);
            break;
        }
    }
#elif __riscv_xlen == 64
    if (CONFIG_TO_INT(old_config) != CONFIG_TO_INT(config)) {
        /* Mask to clear old pmpcfg */
        cfgmask = (0xFF << (8 * (region % 8)));
        pmpcfg = (CONFIG_TO_INT(config) << (8 * (region % 8)));

        switch (region / 8) {
        case 0:
            __asm__("csrc pmpcfg0, %[mask]" ::[mask] "r"(cfgmask) :);

            __asm__("csrs pmpcfg0, %[cfg]" ::[cfg] "r"(pmpcfg) :);
            break;
        case 1:
            __asm__("csrc pmpcfg2, %[mask]" ::[mask] "r"(cfgmask) :);

            __asm__("csrs pmpcfg2, %[cfg]" ::[cfg] "r"(pmpcfg) :);
            break;
        }
    }
#else
#error XLEN is not set to supported value for PMP driver
#endif

    return 0;
}

int metal_pmp_get_region(struct metal_pmp *pmp, unsigned int region,
                         struct metal_pmp_config *config, size_t *address) {
    size_t pmpcfg = 0;
    char *pmpcfg_convert = (char *)&pmpcfg;

    if (!pmp || !config || !address) {
        /* NULL pointers are invalid arguments */
        return 1;
    }

    if (region > _pmp_regions()) {
        /* Region outside of supported range */
        return 2;
    }

#if __riscv_xlen == 32
    switch (region / 4) {
    case 0:
        __asm__("csrr %[cfg], pmpcfg0" : [cfg] "=r"(pmpcfg)::);
        break;
    case 1:
        __asm__("csrr %[cfg], pmpcfg1" : [cfg] "=r"(pmpcfg)::);
        break;
    case 2:
        __asm__("csrr %[cfg], pmpcfg2" : [cfg] "=r"(pmpcfg)::);
        break;
    case 3:
        __asm__("csrr %[cfg], pmpcfg3" : [cfg] "=r"(pmpcfg)::);
        break;
    }

    pmpcfg = (0xFF & (pmpcfg >> (8 * (region % 4))));

#elif __riscv_xlen == 64
    switch (region / 8) {
    case 0:
        __asm__("csrr %[cfg], pmpcfg0" : [cfg] "=r"(pmpcfg)::);
        break;
    case 1:
        __asm__("csrr %[cfg], pmpcfg2" : [cfg] "=r"(pmpcfg)::);
        break;
    }

    pmpcfg = (0xFF & (pmpcfg >> (8 * (region % 8))));

#else
#error XLEN is not set to supported value for PMP driver
#endif

    *config = INT_TO_CONFIG(*pmpcfg_convert);

    switch (region) {
    case 0:
        __asm__("csrr %[addr], pmpaddr0" : [addr] "=r"(*address)::);
        break;
    case 1:
        __asm__("csrr %[addr], pmpaddr1" : [addr] "=r"(*address)::);
        break;
    case 2:
        __asm__("csrr %[addr], pmpaddr2" : [addr] "=r"(*address)::);
        break;
    case 3:
        __asm__("csrr %[addr], pmpaddr3" : [addr] "=r"(*address)::);
        break;
    case 4:
        __asm__("csrr %[addr], pmpaddr4" : [addr] "=r"(*address)::);
        break;
    case 5:
        __asm__("csrr %[addr], pmpaddr5" : [addr] "=r"(*address)::);
        break;
    case 6:
        __asm__("csrr %[addr], pmpaddr6" : [addr] "=r"(*address)::);
        break;
    case 7:
        __asm__("csrr %[addr], pmpaddr7" : [addr] "=r"(*address)::);
        break;
    case 8:
        __asm__("csrr %[addr], pmpaddr8" : [addr] "=r"(*address)::);
        break;
    case 9:
        __asm__("csrr %[addr], pmpaddr9" : [addr] "=r"(*address)::);
        break;
    case 10:
        __asm__("csrr %[addr], pmpaddr10" : [addr] "=r"(*address)::);
        break;
    case 11:
        __asm__("csrr %[addr], pmpaddr11" : [addr] "=r"(*address)::);
        break;
    case 12:
        __asm__("csrr %[addr], pmpaddr12" : [addr] "=r"(*address)::);
        break;
    case 13:
        __asm__("csrr %[addr], pmpaddr13" : [addr] "=r"(*address)::);
        break;
    case 14:
        __asm__("csrr %[addr], pmpaddr14" : [addr] "=r"(*address)::);
        break;
    case 15:
        __asm__("csrr %[addr], pmpaddr15" : [addr] "=r"(*address)::);
        break;
    }

    return 0;
}

int metal_pmp_lock(struct metal_pmp *pmp, unsigned int region) {
    struct metal_pmp_config config;
    size_t address;
    int rc = 0;

    rc = metal_pmp_get_region(pmp, region, &config, &address);
    if (rc) {
        return rc;
    }

    if (config.L == METAL_PMP_LOCKED) {
        return 0;
    }

    config.L = METAL_PMP_LOCKED;

    rc = metal_pmp_set_region(pmp, region, config, address);

    return rc;
}

int metal_pmp_set_address(struct metal_pmp *pmp, unsigned int region,
                          size_t address) {
    struct metal_pmp_config config;
    size_t old_address;
    int rc = 0;

    rc = metal_pmp_get_region(pmp, region, &config, &old_address);
    if (rc) {
        return rc;
    }

    rc = metal_pmp_set_region(pmp, region, config, address);

    return rc;
}

size_t metal_pmp_get_address(struct metal_pmp *pmp, unsigned int region) {
    struct metal_pmp_config config;
    size_t address = 0;

    metal_pmp_get_region(pmp, region, &config, &address);

    return address;
}

int metal_pmp_set_address_mode(struct metal_pmp *pmp, unsigned int region,
                               enum metal_pmp_address_mode mode) {
    struct metal_pmp_config config;
    size_t address;
    int rc = 0;

    rc = metal_pmp_get_region(pmp, region, &config, &address);
    if (rc) {
        return rc;
    }

    config.A = mode;

    rc = metal_pmp_set_region(pmp, region, config, address);

    return rc;
}

enum metal_pmp_address_mode metal_pmp_get_address_mode(struct metal_pmp *pmp,
                                                       unsigned int region) {
    struct metal_pmp_config config;
    size_t address = 0;

    metal_pmp_get_region(pmp, region, &config, &address);

    return config.A;
}

int metal_pmp_set_executable(struct metal_pmp *pmp, unsigned int region,
                             int X) {
    struct metal_pmp_config config;
    size_t address;
    int rc = 0;

    rc = metal_pmp_get_region(pmp, region, &config, &address);
    if (rc) {
        return rc;
    }

    config.X = X;

    rc = metal_pmp_set_region(pmp, region, config, address);

    return rc;
}

int metal_pmp_get_executable(struct metal_pmp *pmp, unsigned int region) {
    struct metal_pmp_config config;
    size_t address = 0;

    metal_pmp_get_region(pmp, region, &config, &address);

    return config.X;
}

int metal_pmp_set_writeable(struct metal_pmp *pmp, unsigned int region, int W) {
    struct metal_pmp_config config;
    size_t address;
    int rc = 0;

    rc = metal_pmp_get_region(pmp, region, &config, &address);
    if (rc) {
        return rc;
    }

    config.W = W;

    rc = metal_pmp_set_region(pmp, region, config, address);

    return rc;
}

int metal_pmp_get_writeable(struct metal_pmp *pmp, unsigned int region) {
    struct metal_pmp_config config;
    size_t address = 0;

    metal_pmp_get_region(pmp, region, &config, &address);

    return config.W;
}

int metal_pmp_set_readable(struct metal_pmp *pmp, unsigned int region, int R) {
    struct metal_pmp_config config;
    size_t address;
    int rc = 0;

    rc = metal_pmp_get_region(pmp, region, &config, &address);
    if (rc) {
        return rc;
    }

    config.R = R;

    rc = metal_pmp_set_region(pmp, region, config, address);

    return rc;
}

int metal_pmp_get_readable(struct metal_pmp *pmp, unsigned int region) {
    struct metal_pmp_config config;
    size_t address = 0;

    metal_pmp_get_region(pmp, region, &config, &address);

    return config.R;
}
