/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

/*******************************************************************************
 *
 * @file mss_plic.c
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief PolarFire SoC MSS PLIC and PRCI access data structures and functions.
 *
 * PLIC related data which cannot be placed in mss_plic.h
 *
 */
#include "mpfs_hal/mss_hal.h"

#ifdef __cplusplus
extern "C" {
#endif

const unsigned long plic_hart_lookup[5U] = {0U, 1U, 3U, 5U, 7U};

#ifdef __cplusplus
}
#endif
