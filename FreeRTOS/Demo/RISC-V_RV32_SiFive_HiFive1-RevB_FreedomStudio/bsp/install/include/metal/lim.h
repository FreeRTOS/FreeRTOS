/* Copyright 2020 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__LIM_H
#define METAL__LIM_H

/*! @file lim.h
 *
 * API for manipulating LIM allocation
 */

/*! @def METAL_PLACE_IN_LIM
 * @brief Link a function into the LIM
 *
 * Link a function into the LIM (Loosely Integrated
 * Memory) if the LIM is present on the target device.
 */
#define METAL_PLACE_IN_LIM __attribute__((section(".lim")))

#endif
