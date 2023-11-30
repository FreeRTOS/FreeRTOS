/**
 * \file
 *
 * \brief Chip-specific DFLL implementation
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
#include <compiler.h>
#include <dfll.h>

#define dfll_write_reg(reg, value) \
	do { \
		while (!(SCIF->SCIF_PCLKSR & SCIF_PCLKSR_DFLL0RDY));                 \
		irqflags_t ATPASTE2(dfll_flags, __LINE__) = cpu_irq_save();          \
		SCIF->SCIF_UNLOCK = SCIF_UNLOCK_KEY(0xAAUL)                          \
			| SCIF_UNLOCK_ADDR((uint32_t)&SCIF->SCIF_##reg - (uint32_t)SCIF);\
		SCIF->SCIF_##reg = (value);                                          \
		cpu_irq_restore(ATPASTE2(dfll_flags, __LINE__));                     \
	} while (0)



void dfll_enable_open_loop(const struct dfll_config *cfg, uint32_t dfll_id)
{
	irqflags_t flags;

	UNUSED(dfll_id);

	/* First, enable the DFLL, then configure it */
	flags = cpu_irq_save();
	SCIF->SCIF_UNLOCK = SCIF_UNLOCK_KEY(0xAAUL)
		| SCIF_UNLOCK_ADDR((uint32_t)&SCIF->SCIF_DFLL0CONF - (uint32_t)SCIF);
	SCIF->SCIF_DFLL0CONF = SCIF_DFLL0CONF_EN;
	cpu_irq_restore(flags);
	dfll_write_reg(DFLL0CONF, cfg->conf | SCIF_DFLL0CONF_EN);
	dfll_write_reg(DFLL0MUL, cfg->mul);
	dfll_write_reg(DFLL0VAL, cfg->val);
	dfll_write_reg(DFLL0SSG, cfg->ssg);
}

void dfll_disable_open_loop(uint32_t dfll_id)
{
	UNUSED(dfll_id);

	/* First, disable the DFLL. */
	// Do a sync before reading a dfll conf register
	SCIF->SCIF_DFLL0SYNC = SCIF_DFLL0SYNC_SYNC;
	while (!(SCIF->SCIF_PCLKSR & SCIF_PCLKSR_DFLL0RDY));

	uint32_t conf = SCIF->SCIF_DFLL0CONF;
	conf &= ~SCIF_DFLL0CONF_EN;
	dfll_write_reg(DFLL0CONF, conf);

	/* Finally, stop the reference clock */
	genclk_disable(0);
}

void dfll_enable_closed_loop(const struct dfll_config *cfg, uint32_t dfll_id)
{
	irqflags_t flags;

	UNUSED(dfll_id);

	/* Enable the reference clock */
	genclk_enable(&cfg->ref_cfg, 0);

	/*
	 * Enable the DFLL first, but don't wait for the DFLL0RDY bit
	 * because if the DFLL has been disabled before, the DFLL0RDY
	 * bit stays cleared until it is re-enabled.
	 */
	flags = cpu_irq_save();
	SCIF->SCIF_UNLOCK = SCIF_UNLOCK_KEY(0xAAUL)
		| SCIF_UNLOCK_ADDR((uint32_t)&SCIF->SCIF_DFLL0CONF - (uint32_t)SCIF);
	SCIF->SCIF_DFLL0CONF = SCIF_DFLL0CONF_EN;
	cpu_irq_restore(flags);

	/*
	 * Then, configure the DFLL, taking care to wait for the
	 * DFLL0RDY bit before every step.
	 */
	dfll_write_reg(DFLL0STEP, cfg->step);
	dfll_write_reg(DFLL0MUL, cfg->mul);
	dfll_write_reg(DFLL0SSG, cfg->ssg);
	dfll_write_reg(DFLL0CONF, cfg->conf | SCIF_DFLL0CONF_EN);
}

void dfll_disable_closed_loop(uint32_t dfll_id)
{
	UNUSED(dfll_id);

	/* First, disable the DFLL. */
	// Do a sync before reading a dfll conf register
	SCIF->SCIF_DFLL0SYNC = SCIF_DFLL0SYNC_SYNC;
	while (!(SCIF->SCIF_PCLKSR & SCIF_PCLKSR_DFLL0RDY));

	uint32_t conf = SCIF->SCIF_DFLL0CONF;
	conf &= ~SCIF_DFLL0CONF_EN;
	dfll_write_reg(DFLL0CONF, conf);

	/* Finally, stop the reference clock */
	genclk_disable(0);
}

void dfll_enable_config_defaults(uint32_t dfll_id)
{
#ifdef CONFIG_DFLL0_SOURCE
	struct dfll_config dfllcfg;
#endif
	static bool open_loop_done = false;

	if(SCIF->SCIF_DFLL0CONF & SCIF_DFLL0CONF_MODE) {
		// Closed-loop mode
		if (dfll_is_fine_locked(dfll_id)) {
			return; // DFLL already running
		}
	}
	if (open_loop_done == true) {
		return;
	}

	switch (dfll_id) {
#ifdef CONFIG_DFLL0_SOURCE
	case 0:
		dfll_enable_source(CONFIG_DFLL0_SOURCE);
		dfll_config_init_closed_loop_mode(&dfllcfg,
			CONFIG_DFLL0_SOURCE,
			CONFIG_DFLL0_DIV,
			CONFIG_DFLL0_MUL);

		dfll_enable_closed_loop(&dfllcfg, dfll_id);
		while (!dfll_is_fine_locked(dfll_id));
		break;
#endif

	default:
		Assert(false);
		break;
	}
}
