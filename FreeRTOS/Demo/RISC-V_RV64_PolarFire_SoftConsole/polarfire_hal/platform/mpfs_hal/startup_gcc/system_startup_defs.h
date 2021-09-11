/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
*/

/******************************************************************************
 * @file system_startup_defs.h
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief Defines for the system_startup_defs.c
 */

#ifndef SYSTEM_STARTUP_DEFS_H
#define SYSTEM_STARTUP_DESF_H

#ifdef __cplusplus
extern "C" {
#endif

/*------------------------------------------------------------------------------
 * Markers used to indicate startup status of hart
 */
#define HLS_MAIN_HART_STARTED               0x12344321U
#define HLS_MAIN_HART_FIN_INIT              0x55555555U
#define HLS_OTHER_HART_IN_WFI               0x12345678U
#define HLS_OTHER_HART_PASSED_WFI           0x87654321U

/*------------------------------------------------------------------------------
 * Define the size of the HLS used
 * In our HAL, we are using Hart Local storage for debug data storage only
 * as well as flags for wfi instruction management.
 * The TLS will take memory from top of the stack if allocated
 *
 */
#if !defined (HLS_DEBUG_AREA_SIZE)
#define HLS_DEBUG_AREA_SIZE     64
#endif

#ifdef __cplusplus
}
#endif

#endif /* SYSTEM_STARTUP_DESF_H */
