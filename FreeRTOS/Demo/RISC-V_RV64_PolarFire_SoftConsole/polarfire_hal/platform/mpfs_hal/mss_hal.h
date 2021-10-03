/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 * @file mss_hal.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief MPFS HAL include file. This is the file intended for application to
 * include so that all the other MPFS files are then accessible to it.
 *
 */

#ifndef MSS_HAL_H
#define MSS_HAL_H

#ifndef CONFIG_OPENSBI
#  include <stddef.h>  // for size_t
#  include <stdbool.h> // for bool, true, false
#  include <stdint.h>
#ifndef ssize_t
typedef long            ssize_t;
#endif
#endif

#include "common/mss_assert.h"
#include "common/nwc/mss_ddr_defs.h"
#include "common/nwc/mss_ddr_sgmii_regs.h"
#include "common/nwc/mss_io_config.h"
#include "common/nwc/mss_pll.h"
#include "common/nwc/mss_scb_nwc_regs.h"
#include "common/nwc/mss_scb_nwc_regs.h"
/*
 * mss_sw_config.h may be edited as required and should be located outside the
 * mpfs_hal folder
 */
#include "mpfs_hal_config/mss_sw_config.h"
/*
 * The hw_platform.h is included here only. It must be included after
 * mss_sw_config.h. This allows defines in hw_platform.h be overload from
 * mss_sw_config.h if necessary.
 * */
#include "common/atomic.h"
#include "common/bits.h"
#include "common/encoding.h"
#include "fpga_design_config/fpga_design_config.h"
#include "common/nwc/mss_ddr.h"
#include "common/mss_clint.h"
#include "common/mss_h2f.h"
#include "common/mss_hart_ints.h"
#include "common/mss_mpu.h"
#include "common/mss_pmp.h"
#include "common/mss_plic.h"
#include "common/mss_seg.h"
#include "common/mss_sysreg.h"
#include "common/mss_util.h"
#include "common/mss_mtrap.h"
#include "common/mss_l2_cache.h"
#include "common/mss_axiswitch.h"
#include "common/mss_peripherals.h"
#include "common/nwc/mss_cfm.h"
#include "common/nwc/mss_ddr.h"
#include "common/nwc/mss_sgmii.h"
#include "startup_gcc/system_startup.h"
#include "common/nwc/mss_ddr_debug.h"
#ifdef SIMULATION_TEST_FEEDBACK
#include "nwc/simulation.h"
#endif

#ifdef __cplusplus
extern "C" {
#endif

#ifdef __cplusplus
}
#endif

#endif /* MSS_HAL_H */
