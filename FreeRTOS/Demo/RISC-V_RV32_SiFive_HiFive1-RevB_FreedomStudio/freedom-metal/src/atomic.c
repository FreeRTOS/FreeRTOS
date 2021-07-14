/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/atomic.h>

extern __inline__ int32_t metal_atomic_available(void);
extern __inline__ int32_t metal_atomic_add(metal_atomic_t *a,
                                           int32_t increment);
extern __inline__ int32_t metal_atomic_and(metal_atomic_t *a, int32_t mask);
extern __inline__ int32_t metal_atomic_or(metal_atomic_t *a, int32_t mask);
extern __inline__ int32_t metal_atomic_swap(metal_atomic_t *a,
                                            int32_t new_value);
extern __inline__ int32_t metal_atomic_xor(metal_atomic_t *a, int32_t mask);
extern __inline__ int32_t metal_atomic_max(metal_atomic_t *a, int32_t compare);
extern __inline__ uint32_t metal_atomic_max_u(metal_atomic_t *a,
                                              uint32_t compare);
extern __inline__ int32_t metal_atomic_min(metal_atomic_t *a, int32_t compare);
extern __inline__ uint32_t metal_atomic_min_u(metal_atomic_t *a,
                                              uint32_t compare);
