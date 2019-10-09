/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>
#include <metal/drivers/sifive_fu540-c000_l2.h>

#define L2_CONFIG_WAYS_SHIFT    8
#define L2_CONFIG_WAYS_MASK     (0xFF << L2_CONFIG_WAYS_SHIFT)

#ifdef CONFIG_SIFIVE_FU540_C000_L2

static void metal_driver_sifive_fu540_c000_l2_init(void) __attribute__((constructor));
static void metal_driver_sifive_fu540_c000_l2_init(void)
{
#ifdef __METAL_DT_SIFIVE_FU540_C000_L2_HANDLE
    /* Get the handle for the L2 cache controller */
    struct __metal_driver_sifive_fu540_c000_l2 *l2 = __METAL_DT_SIFIVE_FU540_C000_L2_HANDLE;
    if(!l2) {
        return;
    }

    /* Get the number of available ways per bank */
    uint32_t ways = __METAL_ACCESS_ONCE((__metal_io_u32 *)(l2->control_base + SIFIVE_FU540_C000_L2_CONFIG));
    ways = ((ways & L2_CONFIG_WAYS_MASK) >> L2_CONFIG_WAYS_SHIFT);

    /* Enable all the ways */
    __metal_driver_sifive_fu540_c000_l2_init(l2, ways);
#endif
}

void __metal_driver_sifive_fu540_c000_l2_init(struct metal_cache *l2, int ways)
{
    metal_cache_set_enabled_ways(l2, ways);
}

int __metal_driver_sifive_fu540_c000_l2_get_enabled_ways(struct metal_cache *cache)
{
    struct __metal_driver_sifive_fu540_c000_l2 *l2 = (struct __metal_driver_sifive_fu540_c000_l2 *) cache;
    if(!l2) {
        return -1;
    }

    uint32_t way_enable = __METAL_ACCESS_ONCE((__metal_io_u32 *)(l2->control_base + SIFIVE_FU540_C000_L2_WAYENABLE));

    /* The stored number is the index, so add one */
    return (0xFF & way_enable) + 1;
}

int __metal_driver_sifive_fu540_c000_l2_set_enabled_ways(struct metal_cache *cache, int ways)
{
    struct __metal_driver_sifive_fu540_c000_l2 *l2 = (struct __metal_driver_sifive_fu540_c000_l2 *) cache;
    if(!l2) {
        return -1;
    }

    /* We can't decrease the number of enabled ways */
    if(metal_cache_get_enabled_ways(cache) > ways) {
        return -2;
    }

    /* The stored value is the index, so subtract one */
    uint32_t value = 0xFF & (ways - 1);

    /* Set the number of enabled ways */
    __METAL_ACCESS_ONCE((__metal_io_u32 *)(l2->control_base + SIFIVE_FU540_C000_L2_WAYENABLE)) = value;

    /* Make sure the number of ways was set correctly */
    if(metal_cache_get_enabled_ways(cache) != ways) {
        return -3;
    }

    return 0;
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_sifive_fu540_c000_l2) = {
	.cache.init = __metal_driver_sifive_fu540_c000_l2_init,
	.cache.get_enabled_ways = __metal_driver_sifive_fu540_c000_l2_get_enabled_ways,
	.cache.set_enabled_ways = __metal_driver_sifive_fu540_c000_l2_set_enabled_ways,
};

#endif
