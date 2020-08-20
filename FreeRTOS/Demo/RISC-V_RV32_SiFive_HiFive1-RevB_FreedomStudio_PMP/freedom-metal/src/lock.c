/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/lock.h>

extern __inline__ int metal_lock_init(struct metal_lock *lock);
extern __inline__ int metal_lock_take(struct metal_lock *lock);
extern __inline__ int metal_lock_give(struct metal_lock *lock);
