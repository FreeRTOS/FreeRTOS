/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__MEMORY_H
#define METAL__MEMORY_H

#include <stddef.h>
#include <stdint.h>

/*!
 * @file memory.h
 *
 * @brief API for enumerating memory blocks
 */

struct _metal_memory_attributes {
    unsigned int R : 1;
    unsigned int W : 1;
    unsigned int X : 1;
    unsigned int C : 1;
    unsigned int A : 1;
};

/*!
 * @brief A handle for a memory block
 */
struct metal_memory {
    const uintptr_t _base_address;
    const size_t _size;
    const struct _metal_memory_attributes _attrs;
};

/*!
 * @brief Get the memory block which services the given address
 *
 * Given a physical memory address, get a handle for the memory block to which
 * that address is mapped.
 *
 * @param address The address to query
 * @return The memory block handle, or NULL if the address is not mapped to a
 * memory block
 */
struct metal_memory *metal_get_memory_from_address(const uintptr_t address);

/*!
 * @brief Get the base address for a memory block
 * @param memory The handle for the memory block
 * @return The base address of the memory block
 */
__inline__ uintptr_t
metal_memory_get_base_address(const struct metal_memory *memory) {
    return memory->_base_address;
}

/*!
 * @brief Get the size of a memory block
 * @param memory The handle for the memory block
 * @return The size of the memory block
 */
__inline__ size_t metal_memory_get_size(const struct metal_memory *memory) {
    return memory->_size;
}

/*!
 * @brief Query if a memory block supports atomic operations
 * @param memory The handle for the memory block
 * @return nonzero if the memory block supports atomic operations
 */
__inline__ int
metal_memory_supports_atomics(const struct metal_memory *memory) {
    return memory->_attrs.A;
}

/*!
 * @brief Query if a memory block is cacheable
 * @param memory The handle for the memory block
 * @return nonzero if the memory block is cachable
 */
__inline__ int metal_memory_is_cachable(const struct metal_memory *memory) {
    return memory->_attrs.C;
}

#endif /* METAL__MEMORY_H */
