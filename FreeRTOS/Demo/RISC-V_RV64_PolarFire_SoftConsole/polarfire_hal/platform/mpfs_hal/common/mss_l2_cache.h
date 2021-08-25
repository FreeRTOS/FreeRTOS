/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/***************************************************************************
 * @file mss_l2_cache.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief MACROs defines and prototypes associated with L2 Cache
 *
 */
#ifndef MSS_L2_CACHE_H
#define MSS_L2_CACHE_H

#include <stdint.h>
#include "encoding.h"

#ifdef __cplusplus
extern "C" {
#endif

/*
 * The following defines will be present in configurator generated xml Q1 2021
 * In the interim, you can manually edit if required.
 */
#if !defined (LIBERO_SETTING_WAY_ENABLE)
/*Way indexes less than or equal to this register value may be used by the
cache. E.g. set to 0x7, will allocate 8 cache ways, 0-7 to cache, and leave
8-15 as LIM. Note 1: Way 0 is always allocated as cache. Note 2: each way is
128KB. */
#define LIBERO_SETTING_WAY_ENABLE    0x00000007UL
    /* WAY_ENABLE                        [0:8]   RW value= 0x7 */
#endif
#if !defined (LIBERO_SETTING_WAY_MASK_DMA)
/*Way mask register master DMA. Set field to zero to disable way from this
master. The available cache ways are 0 to number set in WAY_ENABLE register. If
using scratch pad memory, the ways you want reserved for scrathpad are not
available for selection, you must set to 0. e.g. If three ways reserved for
scratchpad, WAY_MASK_0, WAY_MASK_1 and WAY_MASK_2 will be set to zero for all
masters, so they can not evict the way. */
#define LIBERO_SETTING_WAY_MASK_DMA    0x0000FFFFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x1 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x1 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x1 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x1 */
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
#define LIBERO_SETTING_WAY_MASK_AXI4_PORT_0    0x0000FFFFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x1 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x1 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x1 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x1 */
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
#define LIBERO_SETTING_WAY_MASK_AXI4_PORT_1    0x0000FFFFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x1 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x1 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x1 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x1 */
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
#define LIBERO_SETTING_WAY_MASK_AXI4_PORT_2    0x0000FFFFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x1 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x1 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x1 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x1 */
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
#define LIBERO_SETTING_WAY_MASK_AXI4_PORT_3    0x0000FFFFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x1 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x1 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x1 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x1 */
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
#define LIBERO_SETTING_WAY_MASK_E51_DCACHE    0x0000FFFFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x1 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x1 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x1 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x1 */
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
#define LIBERO_SETTING_WAY_MASK_E51_ICACHE    0x0000FFFFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x1 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x1 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x1 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x1 */
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
#define LIBERO_SETTING_WAY_MASK_U54_1_DCACHE    0x0000FFFFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x1 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x1 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x1 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x1 */
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
#define LIBERO_SETTING_WAY_MASK_U54_1_ICACHE    0x0000FFFFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x1 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x1 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x1 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x1 */
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
#define LIBERO_SETTING_WAY_MASK_U54_2_DCACHE    0x0000FFFFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x1 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x1 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x1 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x1 */
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
#define LIBERO_SETTING_WAY_MASK_U54_2_ICACHE    0x0000FFFFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x1 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x1 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x1 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x1 */
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
#define LIBERO_SETTING_WAY_MASK_U54_3_DCACHE    0x0000FFFFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x1 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x1 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x1 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x1 */
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
#define LIBERO_SETTING_WAY_MASK_U54_3_ICACHE    0x0000FFFFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x1 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x1 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x1 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x1 */
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
#define LIBERO_SETTING_WAY_MASK_U54_4_DCACHE    0x0000FFFFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x1 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x1 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x1 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x1 */
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
#define LIBERO_SETTING_WAY_MASK_U54_4_ICACHE    0x0000FFFFUL
    /* WAY_MASK_0                        [0:1]   RW value= 0x1 */
    /* WAY_MASK_1                        [1:1]   RW value= 0x1 */
    /* WAY_MASK_2                        [2:1]   RW value= 0x1 */
    /* WAY_MASK_3                        [3:1]   RW value= 0x1 */
    /* WAY_MASK_4                        [4:1]   RW value= 0x1 */
    /* WAY_MASK_5                        [5:1]   RW value= 0x1 */
    /* WAY_MASK_6                        [6:1]   RW value= 0x1 */
    /* WAY_MASK_7                        [7:1]   RW value= 0x1 */
    /* WAY_MASK_8                        [8:1]   RW value= 0x1 */
    /* WAY_MASK_9                        [9:1]   RW value= 0x1 */
    /* WAY_MASK_10                       [10:1]  RW value= 0x1 */
    /* WAY_MASK_11                       [11:1]  RW value= 0x1 */
    /* WAY_MASK_12                       [12:1]  RW value= 0x1 */
    /* WAY_MASK_13                       [13:1]  RW value= 0x1 */
    /* WAY_MASK_14                       [14:1]  RW value= 0x1 */
    /* WAY_MASK_15                       [15:1]  RW value= 0x1 */
#endif
#if !defined (LIBERO_SETTING_NUM_SCRATCH_PAD_WAYS)
/*Number of ways reserved for scratchpad. Note 1: This is not a register Note
2: each way is 128KB. Note 3: Embedded software expects cache ways allocated
for scratchpad start at way 0, and work up. */
#define LIBERO_SETTING_NUM_SCRATCH_PAD_WAYS    0x00000000UL
    /* NUM_OF_WAYS                       [0:8]   RW value= 0x0 */
#endif


#if !defined (LIBERO_SETTING_L2_SHUTDOWN_CR)
/*Number of ways reserved for scratchpad. Note 1: This is not a register Note
2: each way is 128KB. Note 3: Embedded software expects cache ways allocated
for scratchpad start at way 0, and work up. */
#define LIBERO_SETTING_L2_SHUTDOWN_CR    0x00000000UL
    /* NUM_OF_WAYS                       [0:8]   RW value= 0x0 */
#endif



/*==============================================================================
 * Define describing cache characteristics.
 */
#define MAX_WAY_ENABLE          15
#define NB_SETS                 512
#define NB_BANKS                4
#define CACHE_BLOCK_BYTE_LENGTH 64
#define UINT64_BYTE_LENGTH      8
#define WAY_BYTE_LENGTH         (CACHE_BLOCK_BYTE_LENGTH * NB_SETS * NB_BANKS)

#define ZERO_DEVICE_BOTTOM  0x0A000000ULL
#define ZERO_DEVICE_TOP     0x0C000000ULL

#define CACHE_CTRL_BASE     0x02010000ULL

#define INIT_MARKER         0xC0FFEEBEC0010000ULL

#define SHUTDOWN_CACHE_CC24_00_07_MASK     0x01
#define SHUTDOWN_CACHE_CC24_08_15_MASK     0x02
#define SHUTDOWN_CACHE_CC24_16_23_MASK     0x04
#define SHUTDOWN_CACHE_CC24_24_31_MASK     0x08


/*==============================================================================
 * Cache controller registers definitions
 */
#define RO  volatile const
#define RW  volatile
#define WO  volatile

typedef struct {
  RO uint8_t  BANKS;
  RO uint8_t  WAYS;
  RO uint8_t  SETS;
  RO uint8_t  BYTES;
} CACHE_CONFIG_typedef;

typedef struct {
  CACHE_CONFIG_typedef CONFIG;
  RO uint32_t RESERVED;
  RW uint8_t  WAY_ENABLE;
  RO uint8_t  RESERVED0[55];

  RW uint32_t ECC_INJECT_ERROR;
  RO uint32_t RESERVED1[47];

  RO uint64_t ECC_DIR_FIX_ADDR;
  RO uint32_t ECC_DIR_FIX_COUNT;
  RO uint32_t RESERVED2[13];

  RO uint64_t ECC_DATA_FIX_ADDR;
  RO uint32_t ECC_DATA_FIX_COUNT;
  RO uint32_t RESERVED3[5];

  RO uint64_t ECC_DATA_FAIL_ADDR;
  RO uint32_t ECC_DATA_FAIL_COUNT;
  RO uint32_t RESERVED4[37];

  WO uint64_t FLUSH64;
  RO uint64_t RESERVED5[7];

  WO uint32_t FLUSH32;
  RO uint32_t RESERVED6[367];

  RW uint64_t WAY_MASK_DMA;

  RW uint64_t WAY_MASK_AXI4_SLAVE_PORT_0;
  RW uint64_t WAY_MASK_AXI4_SLAVE_PORT_1;
  RW uint64_t WAY_MASK_AXI4_SLAVE_PORT_2;
  RW uint64_t WAY_MASK_AXI4_SLAVE_PORT_3;

  RW uint64_t WAY_MASK_E51_DCACHE;
  RW uint64_t WAY_MASK_E51_ICACHE;

  RW uint64_t WAY_MASK_U54_1_DCACHE;
  RW uint64_t WAY_MASK_U54_1_ICACHE;

  RW uint64_t WAY_MASK_U54_2_DCACHE;
  RW uint64_t WAY_MASK_U54_2_ICACHE;

  RW uint64_t WAY_MASK_U54_3_DCACHE;
  RW uint64_t WAY_MASK_U54_3_ICACHE;

  RW uint64_t WAY_MASK_U54_4_DCACHE;
  RW uint64_t WAY_MASK_U54_4_ICACHE;
} CACHE_CTRL_typedef;

#define CACHE_CTRL  ((volatile CACHE_CTRL_typedef *) CACHE_CTRL_BASE)

void config_l2_cache(void);
uint8_t check_num_scratch_ways(uint64_t *start, uint64_t *end);

#ifdef __cplusplus
}
#endif

#endif  /* MSS_L2_CACHE_H */
