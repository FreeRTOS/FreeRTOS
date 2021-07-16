/* Copyright 2020 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__CACHE_H
#define METAL__CACHE_H

/*!
 * @file cache.h
 *
 * @brief API for configuring caches
 */
#include <stdint.h>

/*!
 * @brief a handle for a cache
 * Note: To be deprecated in next release.
 */
struct metal_cache {
    uint8_t __no_empty_structs;
};

/*!
 * @brief Initialize L2 cache controller.
 *        Enables all available cache ways.
 * @param None
 * @return 0 If no error
 */
int metal_l2cache_init(void);

/*!
 * @brief Get the current number of enabled L2 cache ways
 * @param None
 * @return The current number of enabled L2 cache ways
 */
int metal_l2cache_get_enabled_ways(void);

/*!
 * @brief Enable the requested number of L2 cache ways
 * @param ways Number of ways to enable
 * @return 0 if the ways are successfully enabled
 */
int metal_l2cache_set_enabled_ways(int ways);

/*!
 * @brief Initialize a cache
 * @param cache The handle for the cache to initialize
 * @param ways The number of ways to enable
 *
 * Initializes a cache with the requested number of ways enabled.
 * Note: API to be deprecated in next release.
 */
__inline__ void metal_cache_init(struct metal_cache *cache, int ways) {
    metal_l2cache_init();
}

/*!
 * @brief Get the current number of enabled cache ways
 * @param cache The handle for the cache
 * @return The current number of enabled cache ways
 * Note: API to be deprecated in next release.
 */
__inline__ int metal_cache_get_enabled_ways(struct metal_cache *cache) {
    return metal_l2cache_get_enabled_ways();
}

/*!
 * @brief Enable the requested number of cache ways
 * @param cache The handle for the cache
 * @param ways The number of ways to enabled
 * @return 0 if the ways are successfully enabled
 * Note: API to be deprecated in next release.
 */
__inline__ int metal_cache_set_enabled_ways(struct metal_cache *cache,
                                            int ways) {
    return metal_l2cache_set_enabled_ways(ways);
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

#endif
