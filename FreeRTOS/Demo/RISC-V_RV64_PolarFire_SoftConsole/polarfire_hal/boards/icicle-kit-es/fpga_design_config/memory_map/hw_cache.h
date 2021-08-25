/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * @file hw_cache.h
 * @author Microchip-FPGA Embedded Systems Solutions
 *
 *
 * Note 1: This file should not be edited. If you need to modify a parameter
 * without going through regenerating using the MSS Configurator Libero flow 
 * or editing the associated xml file
 * the following method is recommended: 

 * 1. edit the following file 
 * boards/your_board/platform_config/mpfs_hal_config/mss_sw_config.h

 * 2. define the value you want to override there.
 * (Note: There is a commented example in the platform directory)

 * Note 2: The definition in mss_sw_config.h takes precedence, as
 * mss_sw_config.h is included prior to the generated header files located in
 * boards/your_board/fpga_design_config
 *
 */

#ifndef HW_CACHE_H_
#define HW_CACHE_H_


#ifdef __cplusplus
extern  "C" {
#endif

#if !defined (LIBERO_SETTING_WAY_ENABLE)
/*Way indexes less than or equal to this register value may be used by the
cache. E.g. set to 0x7, will allocate 8 cache ways, 0-7 to cache, and leave
8-15 as LIM. Note 1: Way 0 is always allocated as cache. Note 2: each way is
128KB. */
#define LIBERO_SETTING_WAY_ENABLE    0x0000000BUL
    /* WAY_ENABLE                        [0:8]   RW value= 0xB */
#endif
#if !defined (LIBERO_SETTING_WAY_MASK_DMA)
/*Way mask register master DMA. Set field to zero to disable way from this
master. The available cache ways are 0 to number set in WAY_ENABLE register. If
using scratch pad memory, the ways you want reserved for scrathpad are not
available for selection, you must set to 0. e.g. If three ways reserved for
scratchpad, WAY_MASK_0, WAY_MASK_1 and WAY_MASK_2 will be set to zero for all
masters, so they can not evict the way. */
#define LIBERO_SETTING_WAY_MASK_DMA    0x0000F0FFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x0 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x0 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x0 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x0 */
    /* WAY_MASK_12                       [12:1]  RW value= 0x1 */
    /* WAY_MASK_13                       [13:1]  RW value= 0x1 */
    /* WAY_MASK_14                       [14:1]  RW value= 0x1 */
    /* WAY_MASK_15                       [15:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_WAY_MASK_AXI4_PORT_0)
/*Way mask register master DMA. Set field to zero to disable way from this
master. The available cache ways are 0 to number set in WAY_ENABLE register. If
using scratch pad memory, the ways you want reserved for scrathpad are not
available for selection, you must set to 0. e.g. If three ways reserved for
scratchpad, WAY_MASK_0, WAY_MASK_1 and WAY_MASK_2 will be set to zero for all
masters, so they can not evict the way. */
#define LIBERO_SETTING_WAY_MASK_AXI4_PORT_0    0x0000F0FFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x0 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x0 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x0 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x0 */
    /* WAY_MASK_12                       [12:1]  RW value= 0x1 */
    /* WAY_MASK_13                       [13:1]  RW value= 0x1 */
    /* WAY_MASK_14                       [14:1]  RW value= 0x1 */
    /* WAY_MASK_15                       [15:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_WAY_MASK_AXI4_PORT_1)
/*Way mask register master DMA. Set field to zero to disable way from this
master. The available cache ways are 0 to number set in WAY_ENABLE register. If
using scratch pad memory, the ways you want reserved for scrathpad are not
available for selection, you must set to 0. e.g. If three ways reserved for
scratchpad, WAY_MASK_0, WAY_MASK_1 and WAY_MASK_2 will be set to zero for all
masters, so they can not evict the way. */
#define LIBERO_SETTING_WAY_MASK_AXI4_PORT_1    0x0000F0FFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x0 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x0 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x0 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x0 */
    /* WAY_MASK_12                       [12:1]  RW value= 0x1 */
    /* WAY_MASK_13                       [13:1]  RW value= 0x1 */
    /* WAY_MASK_14                       [14:1]  RW value= 0x1 */
    /* WAY_MASK_15                       [15:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_WAY_MASK_AXI4_PORT_2)
/*Way mask registerAXI slave port 2. Set field to zero to disable way from this
master. The available cache ways are 0 to number set in WAY_ENABLE register. If
using scratch pad memory, the ways you want reserved for scrathpad are not
available for selection, you must set to 0. e.g. If three ways reserved for
scratchpad, WAY_MASK_0, WAY_MASK_1 and WAY_MASK_2 will be set to zero for all
masters, so they can not evict the way. */
#define LIBERO_SETTING_WAY_MASK_AXI4_PORT_2    0x0000F0FFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x0 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x0 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x0 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x0 */
    /* WAY_MASK_12                       [12:1]  RW value= 0x1 */
    /* WAY_MASK_13                       [13:1]  RW value= 0x1 */
    /* WAY_MASK_14                       [14:1]  RW value= 0x1 */
    /* WAY_MASK_15                       [15:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_WAY_MASK_AXI4_PORT_3)
/*Way mask register AXI slave port 3. Set field to 1 to disable way from this
master. Set field to zero to disable way from this master. The available cache
ways are 0 to number set in WAY_ENABLE register. If using scratch pad memory,
the ways you want reserved for scrathpad are not available for selection, you
must set to 0. e.g. If three ways reserved for scratchpad, WAY_MASK_0,
WAY_MASK_1 and WAY_MASK_2 will be set to zero for all masters, so they can not
evict the way. */
#define LIBERO_SETTING_WAY_MASK_AXI4_PORT_3    0x0000F0FFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x0 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x0 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x0 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x0 */
    /* WAY_MASK_12                       [12:1]  RW value= 0x1 */
    /* WAY_MASK_13                       [13:1]  RW value= 0x1 */
    /* WAY_MASK_14                       [14:1]  RW value= 0x1 */
    /* WAY_MASK_15                       [15:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_WAY_MASK_E51_DCACHE)
/*Way mask register E51 data cache (hart0). Set field to zero to disable way
from this master. The available cache ways are 0 to number set in WAY_ENABLE
register. If using scratch pad memory, the ways you want reserved for scrathpad
are not available for selection, you must set to 0. e.g. If three ways reserved
for scratchpad, WAY_MASK_0, WAY_MASK_1 and WAY_MASK_2 will be set to zero for
all masters, so they can not evict the way. */
#define LIBERO_SETTING_WAY_MASK_E51_DCACHE    0x0000F0FFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x0 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x0 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x0 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x0 */
    /* WAY_MASK_12                       [12:1]  RW value= 0x1 */
    /* WAY_MASK_13                       [13:1]  RW value= 0x1 */
    /* WAY_MASK_14                       [14:1]  RW value= 0x1 */
    /* WAY_MASK_15                       [15:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_WAY_MASK_E51_ICACHE)
/*Way mask registerE52 instruction cache (hart0). Set field to zero to disable
way from this master. The available cache ways are 0 to number set in
WAY_ENABLE register. If using scratch pad memory, the ways you want reserved
for scrathpad are not available for selection, you must set to 0. e.g. If three
ways reserved for scratchpad, WAY_MASK_0, WAY_MASK_1 and WAY_MASK_2 will be set
to zero for all masters, so they can not evict the way. */
#define LIBERO_SETTING_WAY_MASK_E51_ICACHE    0x0000F0FFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x0 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x0 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x0 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x0 */
    /* WAY_MASK_12                       [12:1]  RW value= 0x1 */
    /* WAY_MASK_13                       [13:1]  RW value= 0x1 */
    /* WAY_MASK_14                       [14:1]  RW value= 0x1 */
    /* WAY_MASK_15                       [15:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_WAY_MASK_U54_1_DCACHE)
/*Way mask register data cache (hart1). Set field to zero to disable way from
this master. The available cache ways are 0 to number set in WAY_ENABLE
register. If using scratch pad memory, the ways you want reserved for scrathpad
are not available for selection, you must set to 0. e.g. If three ways reserved
for scratchpad, WAY_MASK_0, WAY_MASK_1 and WAY_MASK_2 will be set to zero for
all masters, so they can not evict the way. */
#define LIBERO_SETTING_WAY_MASK_U54_1_DCACHE    0x0000F0FFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x0 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x0 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x0 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x0 */
    /* WAY_MASK_12                       [12:1]  RW value= 0x1 */
    /* WAY_MASK_13                       [13:1]  RW value= 0x1 */
    /* WAY_MASK_14                       [14:1]  RW value= 0x1 */
    /* WAY_MASK_15                       [15:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_WAY_MASK_U54_1_ICACHE)
/*Way mask register instruction cache (hart1). Set field to zero to disable way
from this master. The available cache ways are 0 to number set in WAY_ENABLE
register. If using scratch pad memory, the ways you want reserved for scrathpad
are not available for selection, you must set to 0. e.g. If three ways reserved
for scratchpad, WAY_MASK_0, WAY_MASK_1 and WAY_MASK_2 will be set to zero for
all masters, so they can not evict the way. */
#define LIBERO_SETTING_WAY_MASK_U54_1_ICACHE    0x0000F0FFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x0 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x0 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x0 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x0 */
    /* WAY_MASK_12                       [12:1]  RW value= 0x1 */
    /* WAY_MASK_13                       [13:1]  RW value= 0x1 */
    /* WAY_MASK_14                       [14:1]  RW value= 0x1 */
    /* WAY_MASK_15                       [15:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_WAY_MASK_U54_2_DCACHE)
/*Way mask register data cache (hart2). Set field to 1 to disable way from this
master. Set field to zero to disable way from this master. The available cache
ways are 0 to number set in WAY_ENABLE register. If using scratch pad memory,
the ways you want reserved for scrathpad are not available for selection, you
must set to 0. e.g. If three ways reserved for scratchpad, WAY_MASK_0,
WAY_MASK_1 and WAY_MASK_2 will be set to zero for all masters, so they can not
evict the way. */
#define LIBERO_SETTING_WAY_MASK_U54_2_DCACHE    0x0000F0FFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x0 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x0 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x0 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x0 */
    /* WAY_MASK_12                       [12:1]  RW value= 0x1 */
    /* WAY_MASK_13                       [13:1]  RW value= 0x1 */
    /* WAY_MASK_14                       [14:1]  RW value= 0x1 */
    /* WAY_MASK_15                       [15:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_WAY_MASK_U54_2_ICACHE)
/*Way mask register instruction cache (hart2). Set field to zero to disable way
from this master. The available cache ways are 0 to number set in WAY_ENABLE
register. If using scratch pad memory, the ways you want reserved for scrathpad
are not available for selection, you must set to 0. e.g. If three ways reserved
for scratchpad, WAY_MASK_0, WAY_MASK_1 and WAY_MASK_2 will be set to zero for
all masters, so they can not evict the way. */
#define LIBERO_SETTING_WAY_MASK_U54_2_ICACHE    0x0000F0FFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x0 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x0 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x0 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x0 */
    /* WAY_MASK_12                       [12:1]  RW value= 0x1 */
    /* WAY_MASK_13                       [13:1]  RW value= 0x1 */
    /* WAY_MASK_14                       [14:1]  RW value= 0x1 */
    /* WAY_MASK_15                       [15:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_WAY_MASK_U54_3_DCACHE)
/*Way mask register data cache (hart3). Set field to 1 to disable way from this
master.Set field to zero to disable way from this master. The available cache
ways are 0 to number set in WAY_ENABLE register. If using scratch pad memory,
the ways you want reserved for scrathpad are not available for selection, you
must set to 0. e.g. If three ways reserved for scratchpad, WAY_MASK_0,
WAY_MASK_1 and WAY_MASK_2 will be set to zero for all masters, so they can not
evict the way. */
#define LIBERO_SETTING_WAY_MASK_U54_3_DCACHE    0x0000F0FFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x0 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x0 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x0 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x0 */
    /* WAY_MASK_12                       [12:1]  RW value= 0x1 */
    /* WAY_MASK_13                       [13:1]  RW value= 0x1 */
    /* WAY_MASK_14                       [14:1]  RW value= 0x1 */
    /* WAY_MASK_15                       [15:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_WAY_MASK_U54_3_ICACHE)
/*Way mask register instruction cache(hart3). Set field to zero to disable way
from this master. The available cache ways are 0 to number set in WAY_ENABLE
register. If using scratch pad memory, the ways you want reserved for scrathpad
are not available for selection, you must set to 0. e.g. If three ways reserved
for scratchpad, WAY_MASK_0, WAY_MASK_1 and WAY_MASK_2 will be set to zero for
all masters, so they can not evict the way. */
#define LIBERO_SETTING_WAY_MASK_U54_3_ICACHE    0x0000F0FFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x0 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x0 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x0 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x0 */
    /* WAY_MASK_12                       [12:1]  RW value= 0x1 */
    /* WAY_MASK_13                       [13:1]  RW value= 0x1 */
    /* WAY_MASK_14                       [14:1]  RW value= 0x1 */
    /* WAY_MASK_15                       [15:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_WAY_MASK_U54_4_DCACHE)
/*Way mask register data cache (hart4). Set field to 1 to disable way from this
master. Set field to zero to disable way from this master. The available cache
ways are 0 to number set in WAY_ENABLE register. If using scratch pad memory,
the ways you want reserved for scrathpad are not available for selection, you
must set to 0. e.g. If three ways reserved for scratchpad, WAY_MASK_0,
WAY_MASK_1 and WAY_MASK_2 will be set to zero for all masters, so they can not
evict the way. */
#define LIBERO_SETTING_WAY_MASK_U54_4_DCACHE    0x0000F0FFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x0 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x0 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x0 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x0 */
    /* WAY_MASK_12                       [12:1]  RW value= 0x1 */
    /* WAY_MASK_13                       [13:1]  RW value= 0x1 */
    /* WAY_MASK_14                       [14:1]  RW value= 0x1 */
    /* WAY_MASK_15                       [15:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_WAY_MASK_U54_4_ICACHE)
/*Way mask register instruction cache (hart4). Set field to zero to disable way
from this master. The available cache ways are 0 to number set in WAY_ENABLE
register. If using scratch pad memory, the ways you want reserved for scrathpad
are not available for selection, you must set to 0. e.g. If three ways reserved
for scratchpad, WAY_MASK_0, WAY_MASK_1 and WAY_MASK_2 will be set to zero for
all masters, so they can not evict the way. */
#define LIBERO_SETTING_WAY_MASK_U54_4_ICACHE    0x0000F0FFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x0 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x0 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x0 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x0 */
    /* WAY_MASK_12                       [12:1]  RW value= 0x1 */
    /* WAY_MASK_13                       [13:1]  RW value= 0x1 */
    /* WAY_MASK_14                       [14:1]  RW value= 0x1 */
    /* WAY_MASK_15                       [15:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_NUM_SCRATCH_PAD_WAYS)
/*Number of ways reserved for scratchpad. Note 1: This is not a register Note
2: each way is 128KB. Note 3: Embedded software expects cache ways allocated
for scratchpad start at way 0, and work up. */
#define LIBERO_SETTING_NUM_SCRATCH_PAD_WAYS    0x00000004UL
    /* NUM_OF_WAYS                       [0:8]   RW value= 0x4 */
#endif

#ifdef __cplusplus
}
#endif


#endif /* #ifdef HW_CACHE_H_ */

