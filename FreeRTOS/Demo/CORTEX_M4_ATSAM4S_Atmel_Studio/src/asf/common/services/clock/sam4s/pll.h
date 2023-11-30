/**
 * \file
 *
 * \brief Chip-specific PLL definitions.
 *
 * Copyright (c) 2011-2012 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
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

#include <osc.h>

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/// @endcond

/**
 * \weakgroup pll_group
 * @{
 */

#define PLL_OUTPUT_MIN_HZ	80000000
#define PLL_OUTPUT_MAX_HZ	240000000

#define PLL_INPUT_MIN_HZ	3000000
#define PLL_INPUT_MAX_HZ	32000000

#define NR_PLLS				2
#define	PLLA_ID				0
#define	PLLB_ID				1

#define PLL_COUNT			0x3fU

enum pll_source {
	PLL_SRC_MAINCK_4M_RC		= OSC_MAINCK_4M_RC,		//!< Internal 4MHz RC oscillator.
	PLL_SRC_MAINCK_8M_RC		= OSC_MAINCK_8M_RC,		//!< Internal 8MHz RC oscillator.
	PLL_SRC_MAINCK_12M_RC		= OSC_MAINCK_12M_RC,	//!< Internal 12MHz RC oscillator.
	PLL_SRC_MAINCK_XTAL			= OSC_MAINCK_XTAL,		//!< External crystal oscillator.
	PLL_SRC_MAINCK_BYPASS		= OSC_MAINCK_BYPASS,	//!< External bypass oscillator.
	PLL_NR_SOURCES,										//!< Number of PLL sources.
};

struct pll_config {
	uint32_t ctrl;
};

#define pll_get_default_rate(pll_id)                                       \
	((osc_get_rate(CONFIG_PLL##pll_id##_SOURCE)                            \
			* CONFIG_PLL##pll_id##_MUL)                                    \
			/ CONFIG_PLL##pll_id##_DIV)

/**
 * \note The SAM3S PLL hardware interprets mul as mul+1. For readability the hardware mul+1
 * is hidden in this implementation. Use mul as mul effective value.
 */
static inline void pll_config_init(struct pll_config *p_cfg,
		enum pll_source e_src, uint32_t ul_div, uint32_t ul_mul)
{
	uint32_t vco_hz;

	Assert(e_src < PLL_NR_SOURCES);

	/* Calculate internal VCO frequency */
	vco_hz = osc_get_rate(e_src) / ul_div;
	Assert(vco_hz >= PLL_INPUT_MIN_HZ);
	Assert(vco_hz <= PLL_INPUT_MAX_HZ);
	
	vco_hz *= ul_mul;
	Assert(vco_hz >= PLL_OUTPUT_MIN_HZ);
	Assert(vco_hz <= PLL_OUTPUT_MAX_HZ);

	/* PMC hardware will automatically make it mul+1 */
	p_cfg->ctrl = CKGR_PLLAR_MULA(ul_mul - 1) | CKGR_PLLAR_DIVA(ul_div) | CKGR_PLLAR_PLLACOUNT(PLL_COUNT);
}

#define pll_config_defaults(cfg, pll_id)                                   \
	pll_config_init(cfg,                                                   \
			CONFIG_PLL##pll_id##_SOURCE,                                   \
			CONFIG_PLL##pll_id##_DIV,                                      \
			CONFIG_PLL##pll_id##_MUL)

static inline void pll_config_read(struct pll_config *p_cfg, uint32_t ul_pll_id)
{
	Assert(ul_pll_id < NR_PLLS);

	if (ul_pll_id == PLLA_ID)
		p_cfg->ctrl = PMC->CKGR_PLLAR;
	else
		p_cfg->ctrl = PMC->CKGR_PLLBR;
}

static inline void pll_config_write(const struct pll_config *p_cfg, uint32_t ul_pll_id)
{
	Assert(ul_pll_id < NR_PLLS);
	
	if (ul_pll_id == PLLA_ID) {
		pmc_disable_pllack(); // Always stop PLL first!
		PMC->CKGR_PLLAR = CKGR_PLLAR_ONE | p_cfg->ctrl;
	} else {
		pmc_disable_pllbck();
		PMC->CKGR_PLLBR = p_cfg->ctrl;
	}
}

static inline void pll_enable(const struct pll_config *p_cfg, uint32_t ul_pll_id)
{
	Assert(ul_pll_id < NR_PLLS);
	
	if (ul_pll_id == PLLA_ID) {
		pmc_disable_pllack(); // Always stop PLL first!
		PMC->CKGR_PLLAR = CKGR_PLLAR_ONE | p_cfg->ctrl;
	} else {
		pmc_disable_pllbck();
		PMC->CKGR_PLLBR = p_cfg->ctrl;
	}
}

/** 
 * \note This will only disable the selected PLL, not the underlying oscillator (mainck).
 */
static inline void pll_disable(uint32_t ul_pll_id)
{
	Assert(ul_pll_id < NR_PLLS);
	
	if (ul_pll_id == PLLA_ID)
		pmc_disable_pllack();
	else
		pmc_disable_pllbck();
}

static inline uint32_t pll_is_locked(uint32_t ul_pll_id)
{
	Assert(ul_pll_id < NR_PLLS);
	
	if (ul_pll_id == PLLA_ID)
		return pmc_is_locked_pllack();
	else
		return pmc_is_locked_pllbck();
}

static inline void pll_enable_source(enum pll_source e_src)
{
	switch (e_src) {
	case PLL_SRC_MAINCK_4M_RC:
	case PLL_SRC_MAINCK_8M_RC:
	case PLL_SRC_MAINCK_12M_RC:
	case PLL_SRC_MAINCK_XTAL:
	case PLL_SRC_MAINCK_BYPASS:
		osc_enable(e_src);
		osc_wait_ready(e_src);
		break;

	default:
		Assert(false);
		break;
	}
}

static inline void pll_enable_config_defaults(unsigned int ul_pll_id)
{
	struct pll_config pllcfg;

	if (pll_is_locked(ul_pll_id)) {
		return; // Pll already running
	}
	switch (ul_pll_id) {
#ifdef CONFIG_PLL0_SOURCE
	case 0:
		pll_enable_source(CONFIG_PLL0_SOURCE);
		pll_config_init(&pllcfg,
				CONFIG_PLL0_SOURCE,
				CONFIG_PLL0_DIV,
				CONFIG_PLL0_MUL);
		break;
#endif
#ifdef CONFIG_PLL1_SOURCE
	case 1:
		pll_enable_source(CONFIG_PLL1_SOURCE);
		pll_config_init(&pllcfg,
				CONFIG_PLL1_SOURCE,
				CONFIG_PLL1_DIV,
				CONFIG_PLL1_MUL);
		break;
#endif
	default:
		Assert(false);
		break;
	}
	pll_enable(&pllcfg, ul_pll_id);
	while (!pll_is_locked(ul_pll_id));
}

//! @}

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/// @endcond

#endif /* CHIP_PLL_H_INCLUDED */
