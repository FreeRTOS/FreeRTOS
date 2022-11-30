/**
 * \file
 *
 * \brief Chip-specific PLL definitions
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
#ifndef CHIP_PLL_H_INCLUDED
#define CHIP_PLL_H_INCLUDED

#ifdef __cplusplus
extern "C" {
#endif

#define SCIF0_PLL_VCO_RANGE1_MAX_FREQ   240000000
#define SCIF_PLL0_VCO_RANGE1_MIN_FREQ   160000000
#define SCIF_PLL0_VCO_RANGE0_MAX_FREQ   180000000
#define SCIF_PLL0_VCO_RANGE0_MIN_FREQ    80000000

/**
 * \weakgroup pll_group
 * @{
 */

#define PLL_MAX_STARTUP_CYCLES    (SCIF_PLL_PLLCOUNT_Msk >> SCIF_PLL_PLLCOUNT_Pos)
#define NR_PLLS                   1

/**
 * \brief Number of milliseconds to wait for PLL lock
 */
#define PLL_TIMEOUT_MS \
	div_ceil(1000 * (PLL_MAX_STARTUP_CYCLES * 2), OSC_RCSYS_MIN_HZ)

/**
 * \note The PLL must run at twice this frequency internally, but the
 * output frequency may be divided by two by setting the PLLOPT[1] bit.
 */
#define PLL_MIN_HZ                40000000
#define PLL_MAX_HZ                240000000

//! \name Chip-specific PLL options
//@{
//! VCO frequency range is 160-240 MHz (80-180 MHz if unset).
#define PLL_OPT_VCO_RANGE_HIGH    0
//! Divide output frequency by two
#define PLL_OPT_OUTPUT_DIV        1
//! Disable wide-bandwidth mode
#define PLL_OPT_WBM_DISABLE       2
//! Number of PLL options
#define PLL_NR_OPTIONS            3
//! The threshold above which to set the #PLL_OPT_VCO_RANGE_HIGH option
#define PLL_VCO_LOW_THRESHOLD     ((SCIF_PLL0_VCO_RANGE1_MIN_FREQ \
	+ SCIF_PLL0_VCO_RANGE0_MAX_FREQ) / 2)
//@}

#ifndef __ASSEMBLY__

#include <compiler.h>
#include <osc.h>

enum pll_source {
	PLL_SRC_OSC0            = 0,    //!< Oscillator 0
	PLL_SRC_GCLK9           = 1,    //!< Generic Clock 9
	PLL_NR_SOURCES,                 //!< Number of PLL sources
};

struct pll_config {
	uint32_t ctrl;
};

#define pll_get_default_rate(pll_id)                \
	((osc_get_rate(CONFIG_PLL ## pll_id ## _SOURCE) \
	* CONFIG_PLL ## pll_id ## _MUL)                 \
	/ CONFIG_PLL ## pll_id ## _DIV)

static inline void pll_config_set_option(struct pll_config *cfg,
		uint32_t option)
{
	Assert(option < PLL_NR_OPTIONS);

	cfg->ctrl |= 1U << (SCIF_PLL_PLLOPT_Pos + option);
}

static inline void pll_config_clear_option(struct pll_config *cfg,
		uint32_t option)
{
	Assert(option < PLL_NR_OPTIONS);

	cfg->ctrl &= ~(1U << (SCIF_PLL_PLLOPT_Pos + option));
}

/**
 * The PLL options #PLL_OPT_VCO_RANGE_HIGH and #PLL_OPT_OUTPUT_DIV will
 * be set automatically based on the calculated target frequency.
 */
static inline void pll_config_init(struct pll_config *cfg,
		enum pll_source src, uint32_t divide, uint32_t mul)
{
#define MUL_MIN    2
#define MUL_MAX    16
#define DIV_MIN    0
#define DIV_MAX    15

	uint32_t vco_hz;

	Assert(src < PLL_NR_SOURCES);
	Assert(divide != 0);

	/* Calculate internal VCO frequency */
	vco_hz = osc_get_rate(src) * mul;
	vco_hz /= divide;
	Assert(vco_hz >= PLL_MIN_HZ);
	Assert(vco_hz <= PLL_MAX_HZ);

	cfg->ctrl = 0;

	/* Bring the internal VCO frequency up to the minimum value */
	if ((vco_hz < PLL_MIN_HZ * 2) && (mul <= 8)) {
		mul *= 2;
		vco_hz *= 2;
		pll_config_set_option(cfg, PLL_OPT_OUTPUT_DIV);
	}

	/* Set VCO frequency range according to calculated value */
	if (vco_hz >= PLL_VCO_LOW_THRESHOLD) {
		pll_config_set_option(cfg, PLL_OPT_VCO_RANGE_HIGH);
	}

	Assert(mul > MUL_MIN && mul <= MUL_MAX);
	Assert(divide > DIV_MIN && divide <= DIV_MAX);

	cfg->ctrl |= ((mul - 1) << SCIF_PLL_PLLMUL_Pos)
			| (divide << SCIF_PLL_PLLDIV_Pos)
			| (PLL_MAX_STARTUP_CYCLES << SCIF_PLL_PLLCOUNT_Pos)
			| (src << SCIF_PLL_PLLOSC_Pos);
}

#define pll_config_defaults(cfg, pll_id) \
	pll_config_init(cfg,                 \
		CONFIG_PLL ## pll_id ## _SOURCE, \
		CONFIG_PLL ## pll_id ## _DIV,    \
		CONFIG_PLL ## pll_id ## _MUL)

static inline void pll_config_read(struct pll_config *cfg, uint32_t pll_id)
{
	Assert(pll_id < NR_PLLS);

	cfg->ctrl = SCIF->SCIF_PLL[pll_id].SCIF_PLL;
}

extern void pll_config_write(const struct pll_config *cfg, uint32_t pll_id);
extern void pll_enable(const struct pll_config *cfg, uint32_t pll_id);
extern void pll_disable(uint32_t pll_id);

static inline bool pll_is_locked(uint32_t pll_id)
{
	Assert(pll_id < NR_PLLS);
	return !!(SCIF->SCIF_PCLKSR & (1U << (6 + pll_id)));
}

static inline void pll_enable_source(enum pll_source src)
{
	switch (src) {
	case PLL_SRC_OSC0:
		if (!osc_is_ready(OSC_ID_OSC0)) {
			osc_enable(OSC_ID_OSC0);
			osc_wait_ready(OSC_ID_OSC0);
		}
		break;
#ifdef CONFIG_GCLK9_SOURCE
	case PLL_SRC_GCLK9:
		SCIF->SCIF_GCCTRL[9].SCIF_GCCTRL =
			SCIF_GCCTRL_OSCSEL(CONFIG_GCLK9_SOURCE) |
			SCIF_GCCTRL_CEN;
		break;
#endif
	default:
		Assert(false);
		break;
	}
}

static inline void pll_enable_config_defaults(uint32_t pll_id)
{
	struct pll_config pllcfg;

	if (pll_is_locked(pll_id)) {
		return; // Pll already running
	}

	switch (pll_id) {
#ifdef CONFIG_PLL0_SOURCE
	case 0:
		pll_enable_source(CONFIG_PLL0_SOURCE);
		pll_config_init(&pllcfg,
				CONFIG_PLL0_SOURCE,
				CONFIG_PLL0_DIV,
				CONFIG_PLL0_MUL);
		break;

#endif
	default:
		Assert(false);
		break;
	}
	pll_enable(&pllcfg, pll_id);
	while (!pll_is_locked(pll_id));
}

#endif /* __ASSEMBLY__ */

//! @}

#ifdef __cplusplus
}
#endif

#endif /* CHIP_PLL_H_INCLUDED */
