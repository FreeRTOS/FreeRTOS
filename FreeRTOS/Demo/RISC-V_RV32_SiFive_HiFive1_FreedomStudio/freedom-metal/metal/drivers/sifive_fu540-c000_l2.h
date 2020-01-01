/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_FU540_C000_L2_H
#define METAL__DRIVERS__SIFIVE_FU540_C000_L2_H

#include <metal/cache.h>
#include <metal/compiler.h>

struct __metal_driver_vtable_sifive_fu540_c000_l2 {
	struct __metal_cache_vtable cache;
};

struct __metal_driver_sifive_fu540_c000_l2;

__METAL_DECLARE_VTABLE(__metal_driver_vtable_sifive_fu540_c000_l2)

struct __metal_driver_sifive_fu540_c000_l2 {
	struct metal_cache cache;
};

#endif

