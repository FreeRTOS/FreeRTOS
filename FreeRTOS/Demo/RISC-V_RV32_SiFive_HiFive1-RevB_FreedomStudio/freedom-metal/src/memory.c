/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine.h>
#include <metal/memory.h>

struct metal_memory *metal_get_memory_from_address(const uintptr_t address) {
    for (int i = 0; i < __METAL_DT_MAX_MEMORIES; i++) {
        struct metal_memory *mem = __metal_memory_table[i];

        uintptr_t lower_bound = metal_memory_get_base_address(mem);
        uintptr_t upper_bound = lower_bound + metal_memory_get_size(mem);

        if ((address >= lower_bound) && (address < upper_bound)) {
            return mem;
        }
    }

    return NULL;
}

extern __inline__ uintptr_t
metal_memory_get_base_address(const struct metal_memory *memory);
extern __inline__ size_t
metal_memory_get_size(const struct metal_memory *memory);
extern __inline__ int
metal_memory_supports_atomics(const struct metal_memory *memory);
extern __inline__ int
metal_memory_is_cachable(const struct metal_memory *memory);
