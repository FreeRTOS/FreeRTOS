/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */
/*******************************************************************************
 * @file mss_l2_cache.c
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief The code in this file is executed before any code/data sections are
 * copied. This code must not rely sdata/data section content. Hence, global
 * variables should not be used unless they are constants.
 *
 */
/*==============================================================================
 *
 */

#include <stdio.h>
#include <string.h>
#include "mpfs_hal/mss_hal.h"
#include "mss_l2_cache.h"

/*==============================================================================
 * Local defines
 */
#if (LIBERO_SETTING_NUM_SCRATCH_PAD_WAYS != 0)
static const uint64_t g_init_marker = INIT_MARKER;
#endif

/*==============================================================================
 * Local functions.
 */
static void check_config_l2_scratchpad(void);


/*==============================================================================
 * This code should only be executed from E51 to be functional.
 * Configure the L2 cache memory:
 *  - Set the number of cache ways used as cache based on the MSS Configurator
 *    settings.
 *  - Configure some of the enabled ways as scratchpad based on linker
 *    configuration and space allocated by configurator.
 */
__attribute__((weak)) void config_l2_cache(void)
{
    ASSERT(LIBERO_SETTING_WAY_ENABLE < 16U);

    /*
     * Set the number of ways that will be shared between cache and scratchpad.
     */
    CACHE_CTRL->WAY_ENABLE = LIBERO_SETTING_WAY_ENABLE;

    /*
     * shutdown L2 as directed
     */
    SYSREG->L2_SHUTDOWN_CR = LIBERO_SETTING_L2_SHUTDOWN_CR;

    /* The scratchpad has already been set-up, first check enough space before copying */
    check_config_l2_scratchpad();

    /* If you are not using scratchpad, no need to include the following code */

    ASSERT(LIBERO_SETTING_WAY_ENABLE >= LIBERO_SETTING_NUM_SCRATCH_PAD_WAYS);



    /*
     * Compute the mask used to specify ways that will be used by the
     * scratchpad.
     */

    uint32_t scratchpad_ways_mask = 0U;
#if (LIBERO_SETTING_NUM_SCRATCH_PAD_WAYS != 0)
    uint32_t inc;
    uint32_t seed_ways_mask = 0x1U << LIBERO_SETTING_WAY_ENABLE;
    for(inc = 0; inc < LIBERO_SETTING_NUM_SCRATCH_PAD_WAYS; ++inc)
    {
        scratchpad_ways_mask |= (seed_ways_mask >> inc) ;
    }
#else
    (void)scratchpad_ways_mask;
#endif

    /*
     * Make sure ways are masked if being used as scratchpad
     */
    ASSERT((LIBERO_SETTING_WAY_MASK_DMA & scratchpad_ways_mask) == 0UL);
    ASSERT((LIBERO_SETTING_WAY_MASK_AXI4_PORT_0 & scratchpad_ways_mask) == 0UL);
    ASSERT((LIBERO_SETTING_WAY_MASK_AXI4_PORT_1 & scratchpad_ways_mask) == 0UL);
    ASSERT((LIBERO_SETTING_WAY_MASK_AXI4_PORT_2 & scratchpad_ways_mask) == 0UL);
    ASSERT((LIBERO_SETTING_WAY_MASK_AXI4_PORT_3 & scratchpad_ways_mask) == 0UL);
    ASSERT((LIBERO_SETTING_WAY_MASK_E51_DCACHE & scratchpad_ways_mask) == 0UL);
    ASSERT((LIBERO_SETTING_WAY_MASK_E51_ICACHE & scratchpad_ways_mask) == 0UL);
    ASSERT((LIBERO_SETTING_WAY_MASK_U54_1_DCACHE & scratchpad_ways_mask) == 0UL);
    ASSERT((LIBERO_SETTING_WAY_MASK_U54_2_DCACHE & scratchpad_ways_mask) == 0UL);
    ASSERT((LIBERO_SETTING_WAY_MASK_U54_3_DCACHE & scratchpad_ways_mask) == 0UL);
    ASSERT((LIBERO_SETTING_WAY_MASK_U54_4_DCACHE & scratchpad_ways_mask) == 0UL);
    ASSERT((LIBERO_SETTING_WAY_MASK_U54_1_ICACHE & scratchpad_ways_mask) == 0UL);
    ASSERT((LIBERO_SETTING_WAY_MASK_U54_2_ICACHE & scratchpad_ways_mask) == 0UL);
    ASSERT((LIBERO_SETTING_WAY_MASK_U54_3_ICACHE & scratchpad_ways_mask) == 0UL);
    ASSERT((LIBERO_SETTING_WAY_MASK_U54_4_ICACHE & scratchpad_ways_mask) == 0UL);

    /*
     * Setup all masters, apart from one we are using to setup scratch
     */
    CACHE_CTRL->WAY_MASK_DMA = LIBERO_SETTING_WAY_MASK_DMA;
    CACHE_CTRL->WAY_MASK_AXI4_SLAVE_PORT_0 = LIBERO_SETTING_WAY_MASK_AXI4_PORT_0;
    CACHE_CTRL->WAY_MASK_AXI4_SLAVE_PORT_1 = LIBERO_SETTING_WAY_MASK_AXI4_PORT_1;
    CACHE_CTRL->WAY_MASK_AXI4_SLAVE_PORT_2 = LIBERO_SETTING_WAY_MASK_AXI4_PORT_2;
    CACHE_CTRL->WAY_MASK_AXI4_SLAVE_PORT_3 = LIBERO_SETTING_WAY_MASK_AXI4_PORT_3;
    CACHE_CTRL->WAY_MASK_E51_ICACHE = LIBERO_SETTING_WAY_MASK_E51_ICACHE;
    CACHE_CTRL->WAY_MASK_U54_1_DCACHE = LIBERO_SETTING_WAY_MASK_U54_1_DCACHE;
    CACHE_CTRL->WAY_MASK_U54_1_ICACHE = LIBERO_SETTING_WAY_MASK_U54_1_ICACHE;
    CACHE_CTRL->WAY_MASK_U54_2_DCACHE = LIBERO_SETTING_WAY_MASK_U54_2_DCACHE;
    CACHE_CTRL->WAY_MASK_U54_2_ICACHE = LIBERO_SETTING_WAY_MASK_U54_2_ICACHE;
    CACHE_CTRL->WAY_MASK_U54_3_DCACHE = LIBERO_SETTING_WAY_MASK_U54_3_DCACHE;
    CACHE_CTRL->WAY_MASK_U54_3_ICACHE = LIBERO_SETTING_WAY_MASK_U54_3_ICACHE;
    CACHE_CTRL->WAY_MASK_U54_4_DCACHE = LIBERO_SETTING_WAY_MASK_U54_4_DCACHE;
    CACHE_CTRL->WAY_MASK_U54_4_ICACHE = LIBERO_SETTING_WAY_MASK_U54_4_ICACHE;

#if (LIBERO_SETTING_NUM_SCRATCH_PAD_WAYS != 0)
    /*
     * Assign ways to Zero Device
     */
    uint64_t * p_scratchpad = (uint64_t *)ZERO_DEVICE_BOTTOM;
    uint32_t ways_inc;
    uint64_t current_way = 0x1U << (((LIBERO_SETTING_WAY_ENABLE + 1U) - LIBERO_SETTING_NUM_SCRATCH_PAD_WAYS) );
    for(ways_inc = 0; ways_inc < LIBERO_SETTING_NUM_SCRATCH_PAD_WAYS; ++ways_inc)
    {
        /*
         * Populate the scratchpad memory one way at a time.
         */
        CACHE_CTRL->WAY_MASK_E51_DCACHE = current_way;
        mb();
        /*
         * Write to the first 64-bit location of each cache block.
         */
        for(inc = 0; inc < (WAY_BYTE_LENGTH / CACHE_BLOCK_BYTE_LENGTH); ++inc)
        {
            *p_scratchpad = g_init_marker + inc;
            p_scratchpad += CACHE_BLOCK_BYTE_LENGTH / UINT64_BYTE_LENGTH;
        }
        current_way = current_way << 1U;
        mb();
    }
#endif  /* (LIBERO_SETTING_NUM_SCRATCH_PAD_WAYS != 0) */
    /*
     * Prevent E51 from evicting from scratchpad ways.
     */
    CACHE_CTRL->WAY_MASK_E51_DCACHE = LIBERO_SETTING_WAY_MASK_E51_DCACHE;
    mb();

}


/*==============================================================================
 * Configure the L2 scratchpad based on linker symbols:
 *  __l2_scratchpad_vma_start
 *  __l2_scratchpad_vma_end
 *
 *  These linker symbols specify the start address and length of the scratchpad.
 *  The scratchpad must be located within the Zero Device memory range.
 */
static void check_config_l2_scratchpad(void)
{
    extern char __l2_scratchpad_vma_start;
    extern char __l2_scratchpad_vma_end;

    uint8_t n_scratchpad_ways;
    const uint64_t end = (const uint64_t)&__l2_scratchpad_vma_end;
    const uint64_t start = (const uint64_t)&__l2_scratchpad_vma_start;
    uint64_t modulo;

    ASSERT(start >= (uint64_t)ZERO_DEVICE_BOTTOM);
    ASSERT(end < (uint64_t)ZERO_DEVICE_TOP);
    ASSERT(end >= start);

    /*
     * Figure out how many cache ways will be required from linker script
     * symbols.
     */
    n_scratchpad_ways = (uint8_t)((end - start) / WAY_BYTE_LENGTH);
    modulo = (end - start) % WAY_BYTE_LENGTH;
    if(modulo > 0)
    {
        ++n_scratchpad_ways;
    }

    ASSERT(LIBERO_SETTING_NUM_SCRATCH_PAD_WAYS >= n_scratchpad_ways);
}

#if 0 // todo - remove, no longer used


/*==============================================================================
 * Reserve a number of cache ways to be used as scratchpad memory.
 *
 * @param nways
 *  Number of ways to be used as scratchpad. One way is 128Kbytes.
 *
 * @param scratchpad_start
 *  Start address within the Zero Device memory range in which the scratchpad
 *  will be located.
 */
static void reserve_scratchpad_ways(uint8_t nways, uint64_t * scratchpad_start)
{
    uint8_t way_enable;
    uint64_t available_ways = 1;
    uint64_t scratchpad_ways = 0;
    uint64_t non_scratchpad_ways;
    uint32_t inc;

    ASSERT(scratchpad_start >= (uint64_t *)ZERO_DEVICE_BOTTOM);
    ASSERT(scratchpad_start < (uint64_t *)ZERO_DEVICE_TOP);

    /*
     * Ensure at least one way remains available as cache.
     */
    way_enable = CACHE_CTRL->WAY_ENABLE;
    ASSERT(nways <= way_enable);
    if(nways <= way_enable)
    {
        /*
         * Compute the mask used to specify ways that will be used by the
         * scratchpad.
         */

        for(inc = 0; inc < way_enable; ++inc)
        {
            available_ways = (available_ways << 1) | (uint64_t)0x01;
            if(inc < nways)
            {
                scratchpad_ways = (scratchpad_ways << 1) | (uint64_t)0x01;
            }
        }

        /*
         * Prevent other masters from evicting cache lines from scratchpad ways.
         * Only allow E51 to evict from scratchpad ways.
         */
        non_scratchpad_ways = available_ways &  ~scratchpad_ways;

        CACHE_CTRL->WAY_MASK_DMA = non_scratchpad_ways;

        CACHE_CTRL->WAY_MASK_AXI4_SLAVE_PORT_0 = non_scratchpad_ways;
        CACHE_CTRL->WAY_MASK_AXI4_SLAVE_PORT_1 = non_scratchpad_ways;
        CACHE_CTRL->WAY_MASK_AXI4_SLAVE_PORT_2 = non_scratchpad_ways;
        CACHE_CTRL->WAY_MASK_AXI4_SLAVE_PORT_3 = non_scratchpad_ways;

        CACHE_CTRL->WAY_MASK_E51_ICACHE = non_scratchpad_ways;

        CACHE_CTRL->WAY_MASK_U54_1_DCACHE = non_scratchpad_ways;
        CACHE_CTRL->WAY_MASK_U54_1_ICACHE = non_scratchpad_ways;

        CACHE_CTRL->WAY_MASK_U54_2_DCACHE = non_scratchpad_ways;
        CACHE_CTRL->WAY_MASK_U54_2_ICACHE = non_scratchpad_ways;

        CACHE_CTRL->WAY_MASK_U54_3_DCACHE = non_scratchpad_ways;
        CACHE_CTRL->WAY_MASK_U54_3_ICACHE = non_scratchpad_ways;

        CACHE_CTRL->WAY_MASK_U54_4_DCACHE = non_scratchpad_ways;
        CACHE_CTRL->WAY_MASK_U54_4_ICACHE = non_scratchpad_ways;

        /*
         * Assign ways to Zero Device
         */
        uint64_t * p_scratchpad = scratchpad_start;
        int ways_inc;
        uint64_t current_way = 1;
        for(ways_inc = 0; ways_inc < nways; ++ways_inc)
        {
            /*
             * Populate the scratchpad memory one way at a time.
             */
            CACHE_CTRL->WAY_MASK_E51_DCACHE = current_way;
            /*
             * Write to the first 64-bit location of each cache block.
             */
            for(inc = 0; inc < (WAY_BYTE_LENGTH / CACHE_BLOCK_BYTE_LENGTH); ++inc)
            {
                *p_scratchpad = g_init_marker + inc;
                p_scratchpad += CACHE_BLOCK_BYTE_LENGTH / UINT64_BYTE_LENGTH;
            }
            current_way = current_way << 1U;
            mb();
        }

        /*
         * Prevent E51 from evicting from scratchpad ways.
         */
        CACHE_CTRL->WAY_MASK_E51_DCACHE = non_scratchpad_ways;
    }
}
#endif
