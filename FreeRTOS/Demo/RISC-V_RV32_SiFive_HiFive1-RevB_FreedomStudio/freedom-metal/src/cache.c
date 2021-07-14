/* Copyright 2020 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/cache.h>
#include <metal/machine.h>

/* Macros to generate driver prefix string */
#ifdef METAL_CACHE_DRIVER_PREFIX
#define METAL_FUNC_STR(a, b) a##_##b
#define METAL_FUNC_STR_(a, b) METAL_FUNC_STR(a, b)
#define METAL_FUNC(x) METAL_FUNC_STR_(METAL_CACHE_DRIVER_PREFIX, x)
#endif

extern __inline__ void metal_cache_init(struct metal_cache *cache, int ways);
extern __inline__ int metal_cache_get_enabled_ways(struct metal_cache *cache);
extern __inline__ int metal_cache_set_enabled_ways(struct metal_cache *cache,
                                                   int ways);

int metal_l2cache_init(void) {
#ifdef METAL_CACHE_DRIVER_PREFIX
    return METAL_FUNC(init)();
#else
    return -1;
#endif
}

int metal_l2cache_get_enabled_ways(void) {
#ifdef METAL_CACHE_DRIVER_PREFIX
    return METAL_FUNC(get_enabled_ways)();
#else
    return -1;
#endif
}

int metal_l2cache_set_enabled_ways(int ways) {
#ifdef METAL_CACHE_DRIVER_PREFIX
    return METAL_FUNC(set_enabled_ways)(ways);
#else
    return -1;
#endif
}

int metal_dcache_l1_available(int hartid) {
    switch (hartid) {
    case 0:
#ifdef __METAL_CPU_0_DCACHE_HANDLE
        return __METAL_CPU_0_DCACHE_HANDLE;
#endif
        break;
    case 1:
#ifdef __METAL_CPU_1_DCACHE_HANDLE
        return __METAL_CPU_1_DCACHE_HANDLE;
#endif
        break;
    case 2:
#ifdef __METAL_CPU_2_DCACHE_HANDLE
        return __METAL_CPU_2_DCACHE_HANDLE;
#endif
        break;
    case 3:
#ifdef __METAL_CPU_3_DCACHE_HANDLE
        return __METAL_CPU_3_DCACHE_HANDLE;
#endif
        break;
    case 4:
#ifdef __METAL_CPU_4_DCACHE_HANDLE
        return __METAL_CPU_4_DCACHE_HANDLE;
#endif
        break;
    case 5:
#ifdef __METAL_CPU_5_DCACHE_HANDLE
        return __METAL_CPU_5_DCACHE_HANDLE;
#endif
        break;
    case 6:
#ifdef __METAL_CPU_6_DCACHE_HANDLE
        return __METAL_CPU_6_DCACHE_HANDLE;
#endif
        break;
    case 7:
#ifdef __METAL_CPU_7_DCACHE_HANDLE
        return __METAL_CPU_7_DCACHE_HANDLE;
#endif
        break;
    case 8:
#ifdef __METAL_CPU_8_DCACHE_HANDLE
        return __METAL_CPU_8_DCACHE_HANDLE;
#endif
        break;
    }
    return 0;
}

int metal_icache_l1_available(int hartid) {
    switch (hartid) {
    case 0:
#ifdef __METAL_CPU_0_ICACHE_HANDLE
        return __METAL_CPU_0_ICACHE_HANDLE;
#endif
        break;
    case 1:
#ifdef __METAL_CPU_1_ICACHE_HANDLE
        return __METAL_CPU_1_ICACHE_HANDLE;
#endif
        break;
    case 2:
#ifdef __METAL_CPU_2_ICACHE_HANDLE
        return __METAL_CPU_2_ICACHE_HANDLE;
#endif
        break;
    case 3:
#ifdef __METAL_CPU_3_ICACHE_HANDLE
        return __METAL_CPU_3_ICACHE_HANDLE;
#endif
        break;
    case 4:
#ifdef __METAL_CPU_4_ICACHE_HANDLE
        return __METAL_CPU_4_ICACHE_HANDLE;
#endif
        break;
    case 5:
#ifdef __METAL_CPU_5_ICACHE_HANDLE
        return __METAL_CPU_5_ICACHE_HANDLE;
#endif
        break;
    case 6:
#ifdef __METAL_CPU_6_ICACHE_HANDLE
        return __METAL_CPU_6_ICACHE_HANDLE;
#endif
        break;
    case 7:
#ifdef __METAL_CPU_7_ICACHE_HANDLE
        return __METAL_CPU_7_ICACHE_HANDLE;
#endif
        break;
    case 8:
#ifdef __METAL_CPU_8_ICACHE_HANDLE
        return __METAL_CPU_8_ICACHE_HANDLE;
#endif
        break;
    }
    return 0;
}

/*!
 * @brief CFlush.D.L1 instruction is a custom instruction implemented as a
 * state machine in L1 Data Cache (D$) with funct3=0, (for core with data
 * caches) It is an I type: .insn i opcode, func3, rd, rs1, simm12(signed
 * immediate 12bs)
 *  31     28 27    24 23    20 19   16 15    12 11     8 7      4 3       0
 * |--------|--------|--------|--------|--------|--------|--------|--------|
 * +-------------+------------+----------+------+--------+-----------------+
 * |sign immediate12b (simm12)|   rs1    | func3|    rd  |      opcode     |
 * |-1-1-1-1 -1-1-0-0 -0-0-0-0|-x-x-x-x-x|0-0-0-|-0-0-0-0|-0-1-1-1 -0-0-1-1|
 * +--------------------------+----------+------+--------+-----------------+
 * 31     -0x40              20        15   0 12   x0     7      0x73      0
 * +--------+--------+--------+----------+------+--------+--------+--------+
 * where,
 * rs1 =  x0, CFLUSH.D.L1 writes back and invalidates all lines in the L1 D$
 * rs1 != x0, CFLUSH.D.L1 writes back and invalidates the L1 D$ line containing
 *            the virtual address in integer register rs1.
 */
void metal_dcache_l1_flush(int hartid, uintptr_t address) {
    if (metal_dcache_l1_available(hartid)) {
        if (address) {
            uintptr_t ms1 = 0, ms2 = 0;
            __asm__ __volatile__("csrr %0, mtvec \n\t"
                                 "la %1, 1f \n\t"
                                 "csrw mtvec, %1 \n\t"
                                 ".insn i 0x73, 0, x0, %2, -0x40 \n\t"
                                 ".align 2\n\t"
                                 "1: \n\t"
                                 "csrw mtvec, %0 \n\t"
                                 : "+r"(ms1), "+r"(ms2)
                                 : "r"(address));
            // Using ‘.insn’ pseudo directive:
            //       '.insn i opcode, func3, rd, rs1, simm12'
        } else {
            __asm__ __volatile__(".word 0xfc000073" : : : "memory");
        }
    }
}

/*!
 * @brief CDiscard.D.L1 instruction is a custom instruction implemented as a
 * state machine in L1 Data Cache (D$) with funct3=0, (for core with data
 * caches) It is an I type: .insn i opcode, func3, rd, rs1, simm12(signed
 * immediate 12bs)
 * 31     28 27    24 23    20 19    16 15    12 11     8 7      4 3       0
 * |--------|--------|--------|--------|--------|--------|--------|--------|
 * +-------------+------------+----------+------+--------+-----------------+
 * |sign immediate12b (simm12)|   rs1    | func3|    rd  |      opcode     |
 * |-1-1-1-1 -1-1-0-0 -0-0-1-0|-x-x-x-x-x|0-0-0-|-0-0-0-0|-0-1-1-1 -0-0-1-1|
 * +--------------------------+----------+------+--------+-----------------+
 * 31     -0x3E              20        15   0 12    x0    7      0x73      0
 * +--------+--------+--------+----------+------+--------+--------+--------+
 * where,
 * rs1 = x0, CDISCARD.D.L1 invalidates all lines in the L1 D$ with no writes
 * back. rs1 != x0, CDISCARD.D.L1 invalidates the L1 D$ line containing the
 * virtual address in integer register rs1, with no writes back.
 */
void metal_dcache_l1_discard(int hartid, uintptr_t address) {
    if (metal_dcache_l1_available(hartid)) {
        if (address) {
            uintptr_t ms1 = 0, ms2 = 0;
            __asm__ __volatile__("csrr %0, mtvec \n\t"
                                 "la %1, 1f \n\t"
                                 "csrw mtvec, %1 \n\t"
                                 ".insn i 0x73, 0, x0, %2, -0x3E \n\t"
                                 ".align 2\n\t"
                                 "1: \n\t"
                                 "csrw mtvec, %0 \n\t"
                                 : "+r"(ms1), "+r"(ms2)
                                 : "r"(address));
            // Using ‘.insn’ pseudo directive:
            //       '.insn i opcode, func3, rd, rs1, simm12'
        } else {
            __asm__ __volatile__(".word 0xfc200073" : : : "memory");
        }
    }
}
