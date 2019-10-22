/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/cache.h>

extern inline void metal_cache_init(struct metal_cache *cache, int ways);
extern inline int metal_cache_get_enabled_ways(struct metal_cache *cache);
extern inline int metal_cache_set_enabled_ways(struct metal_cache *cache, int ways);
