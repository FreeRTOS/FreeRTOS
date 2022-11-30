/**
 * \file
 *
 * \brief Chip-specific generic clock management
 *
 * Copyright (c) 2012 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */
#ifndef CHIP_GENCLK_H_INCLUDED
#define CHIP_GENCLK_H_INCLUDED

#ifdef __cplusplus
extern "C" {
#endif

// dfll.h is not included to avoid a circular dependency.
extern void dfll_enable_config_defaults(uint32_t dfll_id);

/**
 * \weakgroup genclk_group
 * @{
 */

//! \name Chip-specific generic clock definitions
//@{

#define GENCLK_DIV_MAX          256

#ifndef __ASSEMBLY__

#include <compiler.h>
#include <osc.h>
#include <pll.h>

enum genclk_source {
	GENCLK_SRC_RCSYS        = 0,    //!< System RC oscillator
	GENCLK_SRC_OSC32K       = 1,    //!< 32 kHz oscillator
	GENCLK_SRC_DFLL         = 2,    //!< DFLL
	GENCLK_SRC_OSC0         = 3,    //!< Oscillator 0
	GENCLK_SRC_RC80M        = 4,    //!< 80 MHz RC oscillator
	GENCLK_SRC_RCFAST       = 5,    //!< 4-8-12 MHz RC oscillator
	GENCLK_SRC_RC1M         = 6,    //!< 1 MHz RC oscillator
	GENCLK_SRC_CLK_CPU      = 7,    //!< CPU clock
	GENCLK_SRC_CLK_HSB      = 8,    //!< High Speed Bus clock
	GENCLK_SRC_CLK_PBA      = 9,    //!< Peripheral Bus A clock
	GENCLK_SRC_CLK_PBB      = 10,   //!< Peripheral Bus B clock
	GENCLK_SRC_CLK_PBC      = 11,   //!< Peripheral Bus C clock
	GENCLK_SRC_CLK_PBD      = 12,   //!< Peripheral Bus D clock
	GENCLK_SRC_RC32K        = 13,   //!< 32 kHz RC oscillator
	GENCLK_SRC_CLK_1K       = 15,   //!< 1 kHz output from OSC32K
	GENCLK_SRC_PLL0         = 16,   //!< PLL0
	GENCLK_SRC_HRPCLK       = 17,   //!< High resolution prescaler
	GENCLK_SRC_FPCLK        = 18,   //!< Fractional prescaler
	GENCLK_SRC_GCLKIN0      = 19,   //!< GCLKIN0
	GENCLK_SRC_GCLKIN1      = 20,   //!< GCLKIN1
	GENCLK_SRC_GCLK11       = 21,   //!< GCLK11
};

//@}

struct genclk_config {
	uint32_t ctrl;
};

static inline void genclk_config_defaults(struct genclk_config *cfg,
		uint32_t id)
{
	UNUSED(id);
	cfg->ctrl = 0;
}

static inline void genclk_config_read(struct genclk_config *cfg,
		uint32_t id)
{
	cfg->ctrl = SCIF->SCIF_GCCTRL[id].SCIF_GCCTRL;
}

static inline void genclk_config_write(const struct genclk_config *cfg,
		uint32_t id)
{
	SCIF->SCIF_GCCTRL[id].SCIF_GCCTRL = cfg->ctrl;
}

static inline void genclk_config_set_source(struct genclk_config *cfg,
		enum genclk_source src)
{
	cfg->ctrl = (cfg->ctrl & ~SCIF_GCCTRL_OSCSEL_Msk)
			| SCIF_GCCTRL_OSCSEL(src);
}

static inline void genclk_config_set_divider(struct genclk_config *cfg,
		uint32_t divider)
{
	Assert(divider > 0 && divider <= GENCLK_DIV_MAX);

	/* Clear all the bits we're about to modify */
	cfg->ctrl &= ~(SCIF_GCCTRL_DIVEN
			| SCIF_GCCTRL_DIV_Msk);

	if (divider > 1) {
		cfg->ctrl |= SCIF_GCCTRL_DIVEN;
		cfg->ctrl |= SCIF_GCCTRL_DIV(((divider + 1) / 2) - 1);
	}
}

static inline void genclk_enable(const struct genclk_config *cfg,
		uint32_t id)
{
	 SCIF->SCIF_GCCTRL[id].SCIF_GCCTRL = cfg->ctrl | SCIF_GCCTRL_CEN;
}

static inline void genclk_disable(uint32_t id)
{
	SCIF->SCIF_GCCTRL[id].SCIF_GCCTRL = 0;
}

static inline void genclk_enable_source(enum genclk_source src)
{
	switch (src) {
	case GENCLK_SRC_RCSYS:
	case GENCLK_SRC_CLK_CPU:
	case GENCLK_SRC_CLK_HSB:
	case GENCLK_SRC_CLK_PBA:
	case GENCLK_SRC_CLK_PBB:
	case GENCLK_SRC_CLK_PBC:
	case GENCLK_SRC_CLK_PBD:
		// Nothing to do
		break;

#ifdef BOARD_OSC32_HZ
	case GENCLK_SRC_OSC32K:
	case GENCLK_SRC_CLK_1K: // The 1K linked on OSC32K
		if (!osc_is_ready(OSC_ID_OSC32)) {
			osc_enable(OSC_ID_OSC32);
			osc_wait_ready(OSC_ID_OSC32);
		}
		break;
#endif

	case GENCLK_SRC_RC80M:
		if (!osc_is_ready(OSC_ID_RC80M)) {
			osc_enable(OSC_ID_RC80M);
			osc_wait_ready(OSC_ID_RC80M);
		}
		break;

	case GENCLK_SRC_RCFAST:
		if (!osc_is_ready(OSC_ID_RCFAST)) {
			osc_enable(OSC_ID_RCFAST);
			osc_wait_ready(OSC_ID_RCFAST);
		}
		break;

	case GENCLK_SRC_RC1M:
		if (!osc_is_ready(OSC_ID_RC1M)) {
			osc_enable(OSC_ID_RC1M);
			osc_wait_ready(OSC_ID_RC1M);
		}
		break;

	case GENCLK_SRC_RC32K:
		if (!osc_is_ready(OSC_ID_RC32K)) {
			osc_enable(OSC_ID_RC32K);
			osc_wait_ready(OSC_ID_RC32K);
		}
		break;

#ifdef CONFIG_DFLL0_SOURCE
	case GENCLK_SRC_DFLL:
		dfll_enable_config_defaults(0);
		break;
#endif

#ifdef BOARD_OSC0_HZ
	case GENCLK_SRC_OSC0:
		if (!osc_is_ready(OSC_ID_OSC0)) {
			osc_enable(OSC_ID_OSC0);
			osc_wait_ready(OSC_ID_OSC0);
		}
		break;
#endif

# ifdef CONFIG_PLL0_SOURCE
	case GENCLK_SRC_PLL0: {
		pll_enable_config_defaults(0);
		break;
	}
# endif

	default:
		Assert(false);
		break;
	}
}

#endif /* __ASSEMBLY__ */

//! @}

#ifdef __cplusplus
}
#endif

#endif /* CHIP_GENCLK_H_INCLUDED */
