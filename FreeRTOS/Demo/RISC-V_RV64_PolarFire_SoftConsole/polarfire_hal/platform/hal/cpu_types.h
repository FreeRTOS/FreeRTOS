/*******************************************************************************
 * Copyright 2019-2020 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */

#ifndef CPU_TYPES_H
#define CPU_TYPES_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef unsigned long size_t;

/*------------------------------------------------------------------------------
 * addr_t: address type.
 * Used to specify the address of peripherals present in the processor's memory
 * map.
 */
typedef unsigned long addr_t;

/*------------------------------------------------------------------------------
 * psr_t: processor state register.
 * Used by HAL_disable_interrupts() and HAL_restore_interrupts() to store the
 * processor's state between disabling and restoring interrupts.
 */
typedef unsigned long psr_t;

#ifdef __cplusplus
}
#endif

#endif  /* CPU_TYPES_H */

