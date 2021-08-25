/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 * @file mss_ddr_defs.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief mss_ddr_debug related defines
 *
 */

#ifndef SRC_PLATFORM_MPFS_HAL_NWC_MSS_DDR_DEFS_H_
#define SRC_PLATFORM_MPFS_HAL_NWC_MSS_DDR_DEFS_H_

#define PATTERN_INCREMENTAL     (0x01U << 0U)
#define PATTERN_WALKING_ONE     (0x01U << 1U)
#define PATTERN_WALKING_ZERO    (0x01U << 2U)
#define PATTERN_RANDOM          (0x01U << 3U)
#define PATTERN_0xCCCCCCCC      (0x01U << 4U)
#define PATTERN_0x55555555      (0x01U << 5U)
#define PATTERN_ZEROS           (0x01U << 6U)
#define MAX_NO_PATTERNS         7U

/* Training types status offsets */
#define BCLK_SCLK_BIT            (0x1U<<0U)
#define ADDCMD_BIT               (0x1U<<1U)
#define WRLVL_BIT                (0x1U<<2U)
#define RDGATE_BIT               (0x1U<<3U)
#define DQ_DQS_BIT               (0x1U<<4U)

/*  The first five bits represent the currently supported training in the TIP */
/*  This value will not change unless more training possibilities are added to
 *  the TIP */
#define TRAINING_MASK             (BCLK_SCLK_BIT|\
                                       ADDCMD_BIT|\
                                       WRLVL_BIT|\
                                       RDGATE_BIT|\
                                       DQ_DQS_BIT)

#endif /* SRC_PLATFORM_MPFS_HAL_NWC_MSS_DDR_DEFS_H_ */
