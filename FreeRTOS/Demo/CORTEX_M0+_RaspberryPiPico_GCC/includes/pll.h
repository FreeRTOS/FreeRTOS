/*
 * Copyright (c) 2020 Raspberry Pi (Trading) Ltd.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef _HARDWARE_PLL_H_
#define _HARDWARE_PLL_H_

#include "types.h"
#include "address_mapped.h"
#include "regs/pll.h"

/// \tag::pll_hw[]
typedef struct {
    io_rw_32 cs;
    io_rw_32 pwr;
    io_rw_32 fbdiv_int;
    io_rw_32 prim;
} pll_hw_t;

#define pll_sys_hw ((pll_hw_t *const)PLL_SYS_BASE)
#define pll_usb_hw ((pll_hw_t *const)PLL_USB_BASE)
/// \end::pll_hw[]

/** \file hardware/pll.h
 *  \defgroup hardware_pll hardware_pll
 *
 * Phase Locked Loop control APIs
 *
 * There are two PLLs in RP2040. They are:
 *   - pll_sys - Used to generate up to a 133MHz system clock
 *   - pll_usb - Used to generate a 48MHz USB reference clock
 *
 * For details on how the PLL's are calculated, please refer to the RP2040 datasheet.
 */

typedef pll_hw_t *PLL;

#define pll_sys pll_sys_hw
#define pll_usb pll_usb_hw

/*! \brief Initialise specified PLL.
 *  \ingroup hardware_pll
 * \param pll pll_sys or pll_usb
 * \param ref_div Input clock divider.
 * \param vco_freq  Requested output from the VCO (voltage controlled oscillator)
 * \param post_div1 Post Divider 1 - range 1-7. Must be >= post_div2
 * \param post_div2 Post Divider 2 - range 1-7
 */
void pll_init(PLL pll, uint32_t ref_div, uint32_t vco_freq, uint32_t post_div1, uint8_t post_div2);

/*! \brief Release/uninitialise specified PLL.
 *  \ingroup hardware_pll
 *
 * This will turn off the power to the specified PLL. Note this function does not currently check if
 * the PLL is in use before powering it off so should be used with care.
 *
 * \param pll pll_sys or pll_usb
 */
void pll_deinit(PLL pll);


#endif
