/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__CACHE_H
#define METAL__CACHE_H

/*!
 * @file cache.h
 *
 * @brief API for configuring caches
 */

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
inline void metal_cache_init(struct metal_cache *cache, int ways) {
	return cache->vtable->init(cache, ways);
}

/*!
 * @brief Get the current number of enabled cache ways
 * @param cache The handle for the cache
 * @return The current number of enabled cache ways
 */
inline int metal_cache_get_enabled_ways(struct metal_cache *cache) {
	return cache->vtable->get_enabled_ways(cache);
}

/*!
 * @brief Enable the requested number of cache ways
 * @param cache The handle for the cache
 * @param ways The number of ways to enabled
 * @return 0 if the ways are successfully enabled
 */
inline int metal_cache_set_enabled_ways(struct metal_cache *cache, int ways) {
	return cache->vtable->set_enabled_ways(cache, ways);
}

#endif
