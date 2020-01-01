/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__DRIVERS__SIFIVE_CCACHE0_H
#define METAL__DRIVERS__SIFIVE_CCACHE0_H

#include <metal/cache.h>
#include <metal/compiler.h>

struct __metal_driver_vtable_sifive_ccache0 {
	struct __metal_cache_vtable cache;
};

struct __metal_driver_sifive_ccache0;

__METAL_DECLARE_VTABLE(__metal_driver_vtable_sifive_ccache0)

struct __metal_driver_sifive_ccache0 {
	struct metal_cache cache;
};

#endif

