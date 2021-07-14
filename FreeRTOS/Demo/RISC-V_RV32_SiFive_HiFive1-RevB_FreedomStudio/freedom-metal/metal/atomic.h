/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__ATOMIC_H
#define METAL__ATOMIC_H

#include <stdint.h>

#include <metal/compiler.h>

typedef volatile int32_t metal_atomic_t;

#define METAL_ATOMIC_DECLARE(name)                                             \
    __attribute((section(".data.atomics"))) metal_atomic_t name

#define _METAL_STORE_AMO_ACCESS_FAULT 7

/* This macro stores the memory address in mtval like a normal store/amo access
 * fault, triggers a trap, and then if execution returns, returns 0 as an
 * arbitrary choice */
#define _METAL_TRAP_AMO_ACCESS(addr)                                           \
    __asm__("csrw mtval, %[atomic]" ::[atomic] "r"(a));                        \
    _metal_trap(_METAL_STORE_AMO_ACCESS_FAULT);                                \
    return 0;

/*!
 * @brief Check if the platform supports atomic operations
 *
 * @return 1 if atomic operations are supported, 0 if not
 */
__inline__ int32_t metal_atomic_available(void) {
#ifdef __riscv_atomic
    return 1;
#else
    return 0;
#endif
}

/*!
 * @brief Atomically increment a metal_atomic_t and return its old value
 *
 * If atomics are not supported on the platform, this function will trap with
 * a Store/AMO access fault.
 *
 * @param a The pointer to the value to increment
 * @param increment the amount to increment the value
 *
 * @return The previous value of the metal_atomic_t
 */
__inline__ int32_t metal_atomic_add(metal_atomic_t *a, int32_t increment) {
#ifdef __riscv_atomic
    int32_t old;
    __asm__ volatile("amoadd.w %[old], %[increment], (%[atomic])"
                     : [old] "=r"(old)
                     : [increment] "r"(increment), [atomic] "r"(a)
                     : "memory");
    return old;
#else
    _METAL_TRAP_AMO_ACCESS(a);
#endif
}

/*!
 * @brief Atomically bitwise-AND a metal_atomic_t and return its old value
 *
 * If atomics are not supported on the platform, this function will trap with
 * a Store/AMO access fault.
 *
 * @param a The pointer to the value to bitwise-AND
 * @param mask the bitmask to AND
 *
 * @return The previous value of the metal_atomic_t
 */
__inline__ int32_t metal_atomic_and(metal_atomic_t *a, int32_t mask) {
#ifdef __riscv_atomic
    int32_t old;
    __asm__ volatile("amoand.w %[old], %[mask], (%[atomic])"
                     : [old] "=r"(old)
                     : [mask] "r"(mask), [atomic] "r"(a)
                     : "memory");
    return old;
#else
    _METAL_TRAP_AMO_ACCESS(a);
#endif
}

/*!
 * @brief Atomically bitwise-OR a metal_atomic_t and return its old value
 *
 * If atomics are not supported on the platform, this function will trap with
 * a Store/AMO access fault.
 *
 * @param a The pointer to the value to bitwise-OR
 * @param mask the bitmask to OR
 *
 * @return The previous value of the metal_atomic_t
 */
__inline__ int32_t metal_atomic_or(metal_atomic_t *a, int32_t mask) {
#ifdef __riscv_atomic
    int32_t old;
    __asm__ volatile("amoor.w %[old], %[mask], (%[atomic])"
                     : [old] "=r"(old)
                     : [mask] "r"(mask), [atomic] "r"(a)
                     : "memory");
    return old;
#else
    _METAL_TRAP_AMO_ACCESS(a);
#endif
}

/*!
 * @brief Atomically swap a metal_atomic_t and return its old value
 *
 * If atomics are not supported on the platform, this function will trap with
 * a Store/AMO access fault.
 *
 * @param a The pointer to the value to swap
 * @param new_value the value to store in the metal_atomic_t
 *
 * @return The previous value of the metal_atomic_t
 */
__inline__ int32_t metal_atomic_swap(metal_atomic_t *a, int32_t new_value) {
#ifdef __riscv_atomic
    int32_t old;
    __asm__ volatile("amoswap.w %[old], %[newval], (%[atomic])"
                     : [old] "=r"(old)
                     : [newval] "r"(new_value), [atomic] "r"(a)
                     : "memory");
    return old;
#else
    _METAL_TRAP_AMO_ACCESS(a);
#endif
}

/*!
 * @brief Atomically bitwise-XOR a metal_atomic_t and return its old value
 *
 * If atomics are not supported on the platform, this function will trap with
 * a Store/AMO access fault.
 *
 * @param a The pointer to the value to bitwise-XOR
 * @param mask the bitmask to XOR
 *
 * @return The previous value of the metal_atomic_t
 */
__inline__ int32_t metal_atomic_xor(metal_atomic_t *a, int32_t mask) {
#ifdef __riscv_atomic
    int32_t old;
    __asm__ volatile("amoxor.w %[old], %[mask], (%[atomic])"
                     : [old] "=r"(old)
                     : [mask] "r"(mask), [atomic] "r"(a)
                     : "memory");
    return old;
#else
    _METAL_TRAP_AMO_ACCESS(a);
#endif
}

/*!
 * @brief Atomically set the value of a memory location to the greater of
 * its current value or a value to compare it with.
 *
 * If atomics are not supported on the platform, this function will trap with
 * a Store/AMO access fault.
 *
 * @param a The pointer to the value to swap
 * @param compare the value to compare with the value in memory
 *
 * @return The previous value of the metal_atomic_t
 */
__inline__ int32_t metal_atomic_max(metal_atomic_t *a, int32_t compare) {
#ifdef __riscv_atomic
    int32_t old;
    __asm__ volatile("amomax.w %[old], %[compare], (%[atomic])"
                     : [old] "=r"(old)
                     : [compare] "r"(compare), [atomic] "r"(a)
                     : "memory");
    return old;
#else
    _METAL_TRAP_AMO_ACCESS(a);
#endif
}

/*!
 * @brief Atomically set the value of a memory location to the (unsigned)
 * greater of its current value or a value to compare it with.
 *
 * If atomics are not supported on the platform, this function will trap with
 * a Store/AMO access fault.
 *
 * @param a The pointer to the value to swap
 * @param compare the value to compare with the value in memory
 *
 * @return The previous value of the metal_atomic_t
 */
__inline__ uint32_t metal_atomic_max_u(metal_atomic_t *a, uint32_t compare) {
#ifdef __riscv_atomic
    int32_t old;
    __asm__ volatile("amomaxu.w %[old], %[compare], (%[atomic])"
                     : [old] "=r"(old)
                     : [compare] "r"(compare), [atomic] "r"(a)
                     : "memory");
    return old;
#else
    _METAL_TRAP_AMO_ACCESS(a);
#endif
}

/*!
 * @brief Atomically set the value of a memory location to the lesser of
 * its current value or a value to compare it with.
 *
 * If atomics are not supported on the platform, this function will trap with
 * a Store/AMO access fault.
 *
 * @param a The pointer to the value to swap
 * @param compare the value to compare with the value in memory
 *
 * @return The previous value of the metal_atomic_t
 */
__inline__ int32_t metal_atomic_min(metal_atomic_t *a, int32_t compare) {
#ifdef __riscv_atomic
    int32_t old;
    __asm__ volatile("amomin.w %[old], %[compare], (%[atomic])"
                     : [old] "=r"(old)
                     : [compare] "r"(compare), [atomic] "r"(a)
                     : "memory");
    return old;
#else
    _METAL_TRAP_AMO_ACCESS(a);
#endif
}

/*!
 * @brief Atomically set the value of a memory location to the (unsigned) lesser
 * of its current value or a value to compare it with.
 *
 * If atomics are not supported on the platform, this function will trap with
 * a Store/AMO access fault.
 *
 * @param a The pointer to the value to swap
 * @param compare the value to compare with the value in memory
 *
 * @return The previous value of the metal_atomic_t
 */
__inline__ uint32_t metal_atomic_min_u(metal_atomic_t *a, uint32_t compare) {
#ifdef __riscv_atomic
    int32_t old;
    __asm__ volatile("amominu.w %[old], %[compare], (%[atomic])"
                     : [old] "=r"(old)
                     : [compare] "r"(compare), [atomic] "r"(a)
                     : "memory");
    return old;
#else
    _METAL_TRAP_AMO_ACCESS(a);
#endif
}

#endif /* METAL__ATOMIC_H */
