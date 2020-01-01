/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__CACHE_H
#define METAL__CACHE_H

/*!
 * @file cache.h
 *
 * @brief API for configuring caches
 */
#include <stdint.h>

struct metal_cache;

struct __metal_cache_vtable {
	void (*init)(struct metal_cache *cache, int ways);
	int (*get_enabled_ways)(struct metal_cache *cache);
	int (*set_enabled_ways)(struct metal_cache *cache, int ways);
};

/*!
 * @brief a handle for a cache
 */
struct metal_cache {
	const struct __metal_cache_vtable *vtable;
};

/*!
 * @brief Initialize a cache
 * @param cache The handle for the cache to initialize
 * @param ways The number of ways to enable
 *
 * Initializes a cache with the requested number of ways enabled.
 */
__inline__ void metal_cache_init(struct metal_cache *cache, int ways) {
	cache->vtable->init(cache, ways);
}

/*!
 * @brief Get the current number of enabled cache ways
 * @param cache The handle for the cache
 * @return The current number of enabled cache ways
 */
__inline__ int metal_cache_get_enabled_ways(struct metal_cache *cache) {
	return cache->vtable->get_enabled_ways(cache);
}

/*!
 * @brief Enable the requested number of cache ways
 * @param cache The handle for the cache
 * @param ways The number of ways to enabled
 * @return 0 if the ways are successfully enabled
 */
__inline__ int metal_cache_set_enabled_ways(struct metal_cache *cache, int ways) {
	return cache->vtable->set_enabled_ways(cache, ways);
}

/*!
 * @brief Check if dcache is supported on the core
 * @param hartid The core to check
 * @return 1 if dcache is present
 */
int metal_dcache_l1_available(int hartid);

/*!
 * @brief Flush dcache for L1 on the requested core with write back
 * @param hartid  The core to flush
 * @param address The virtual address of cacheline to invalidate
 * @return None
 */
void metal_dcache_l1_flush(int hartid, uintptr_t address);

/*!
 * @brief Discard dcache for L1 on the requested core with no write back
 * @param hartid  The core to discard
 * @param address The virtual address of cacheline to invalidate
 * @return None
 */
void metal_dcache_l1_discard(int hartid, uintptr_t address);

/*!
 * @brief Check if icache is supported on the core
 * @param hartid The core to check
 * @return 1 if icache is present
 */
int metal_icache_l1_available(int hartid);

/*!
 * @brief Flush icache for L1 on the requested core
 * @param hartid  The core to flush
 * @return None
 */
void metal_icache_l1_flush(int hartid);

#endif
