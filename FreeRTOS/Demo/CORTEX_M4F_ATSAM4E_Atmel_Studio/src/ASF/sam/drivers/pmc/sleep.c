/**
 * \file
 *
 * \brief Sleep mode access
 *
 * Copyright (c) 2013 Atmel Corporation. All rights reserved.
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
#include "sleep.h"

/* SAM3 and SAM4 series */
#if (SAM3S || SAM3N || SAM3XA || SAM3U || SAM4S || SAM4E || SAM4N)
# include "pmc.h"
# include "board.h"

/* Checking board configuration of main clock xtal statup time */
#if !defined(BOARD_OSC_STARTUP_US)
# warning The board main clock xtal statup time has not been defined. Using default settings.
# define BOARD_OSC_STARTUP_US    (15625UL)
#endif

/**
 * Save clock settings and shutdown PLLs
 */
__always_inline static void pmc_save_clock_settings(
		uint32_t *p_osc_setting,
		uint32_t *p_pll0_setting,
		uint32_t *p_pll1_setting,
		uint32_t *p_mck_setting)
{
	if (p_osc_setting) {
		*p_osc_setting = PMC->CKGR_MOR;
	}
	if (p_pll0_setting) {
		*p_pll0_setting = PMC->CKGR_PLLAR;
	}
	if (p_pll1_setting) {
#if (SAM3S || SAM4S)
		*p_pll1_setting = PMC->CKGR_PLLBR;
#elif (SAM3U || SAM3XA)
		*p_pll1_setting = PMC->CKGR_UCKR;
#else
		*p_pll1_setting = 0;
#endif
	}
	if (p_mck_setting) {
		*p_mck_setting  = PMC->PMC_MCKR;
	}

	/* Switch MCK to internal 4/8/12M RC for fast wakeup
	   and disable unused clock for power saving. */
	pmc_switch_mck_to_sclk(PMC_MCKR_PRES_CLK_1);
	pmc_switch_mainck_to_fastrc(CKGR_MOR_MOSCRCF_4_MHz);
	pmc_osc_disable_xtal(0);
	pmc_disable_pllack();
#if (SAM3S || SAM4S)
	pmc_disable_pllbck();
#elif (SAM3U || SAM3XA)
	pmc_disable_upll_clock();
#endif
	pmc_switch_mck_to_mainck(PMC_MCKR_PRES_CLK_1);
}

/**
 * Restore clock settings
 */
__always_inline static void pmc_restore_clock_setting(
		uint32_t osc_setting,
		uint32_t pll0_setting,
		uint32_t pll1_setting,
		uint32_t mck_setting)
{
	uint32_t mckr;
	uint32_t pll_sr = 0;

	/* Switch MCK to slow clock  */
	pmc_switch_mck_to_sclk(PMC_MCKR_PRES_CLK_1);
	/* Switch mainck to external xtal */
	if (CKGR_MOR_MOSCXTBY == (osc_setting & CKGR_MOR_MOSCXTBY)) {
		/* Bypass mode */
		pmc_switch_mainck_to_xtal(PMC_OSC_BYPASS,
			pmc_us_to_moscxtst(BOARD_OSC_STARTUP_US,
				CHIP_FREQ_SLCK_RC));
		pmc_osc_disable_fastrc();
	} else if (CKGR_MOR_MOSCXTEN == (osc_setting & CKGR_MOR_MOSCXTEN)) {
		/* External XTAL */
		pmc_switch_mainck_to_xtal(PMC_OSC_XTAL,
			pmc_us_to_moscxtst(BOARD_OSC_STARTUP_US,
				CHIP_FREQ_SLCK_RC));
		pmc_osc_disable_fastrc();
	}

	if (pll0_setting & CKGR_PLLAR_MULA_Msk) {
		PMC->CKGR_PLLAR = CKGR_PLLAR_ONE | pll0_setting;
		pll_sr |= PMC_SR_LOCKA;
	}
#if (SAM3S || SAM4S)
	if (pll1_setting & CKGR_PLLBR_MULB_Msk) {
		PMC->CKGR_PLLBR = pll1_setting;
		pll_sr |= PMC_SR_LOCKB;
	}
#elif (SAM3U || SAM3XA)
	if (pll1_setting & CKGR_UCKR_UPLLEN) {
		PMC->CKGR_UCKR = pll1_setting;
		pll_sr |= PMC_SR_LOCKU;
	}
#else
	UNUSED(pll1_setting);
#endif
	/* Wait MCK source ready */
	switch(mck_setting & PMC_MCKR_CSS_Msk) {
	case PMC_MCKR_CSS_PLLA_CLK:
		while (!(PMC->PMC_SR & PMC_SR_LOCKA));
		break;
#if (SAM3S || SAM4S)
	case PMC_MCKR_CSS_PLLB_CLK:
		while (!(PMC->PMC_SR & PMC_SR_LOCKB));
		break;
#elif (SAM3U || SAM3XA)
	case PMC_MCKR_CSS_UPLL_CLK:
		while (!(PMC->PMC_SR & PMC_SR_LOCKU));
		break;
#endif
	}

	/* Switch to faster clock */
	mckr = PMC->PMC_MCKR;
	/* Set PRES */
	PMC->PMC_MCKR = (mckr & ~PMC_MCKR_PRES_Msk)
		| (mck_setting & PMC_MCKR_PRES_Msk);
	while (!(PMC->PMC_SR & PMC_SR_MCKRDY));
	/* Set CSS and others */
	PMC->PMC_MCKR = mck_setting;
	while (!(PMC->PMC_SR & PMC_SR_MCKRDY));
	/* Waiting all restored PLLs ready */
	while (!(PMC->PMC_SR & pll_sr));
}

/** If clocks are switched to FASTRC for WAIT mode */
static volatile bool b_is_fastrc_used = false;
/** Callback invoked once when clocks are restored */
static pmc_callback_wakeup_clocks_restored_t callback_clocks_restored = NULL;

void pmc_sleep(int sleep_mode)
{
	switch (sleep_mode) {
	case SAM_PM_SMODE_SLEEP_WFI:
	case SAM_PM_SMODE_SLEEP_WFE:
#if (SAM4S || SAM4E || SAM4N)
		SCB->SCR &= (uint32_t)~SCR_SLEEPDEEP;
		cpu_irq_enable();
		__WFI();
		break;
#else
		PMC->PMC_FSMR &= (uint32_t)~PMC_FSMR_LPM;
		SCB->SCR &= (uint32_t)~SCR_SLEEPDEEP;
		cpu_irq_enable();
		if (sleep_mode == SAM_PM_SMODE_SLEEP_WFI)
			__WFI();
		else
			__WFE();
		break;
#endif
	case SAM_PM_SMODE_WAIT: {
		uint32_t mor, pllr0, pllr1, mckr;
		cpu_irq_disable();
		b_is_fastrc_used = true;
		pmc_save_clock_settings(&mor, &pllr0, &pllr1, &mckr);

		/* Enter wait mode */
		cpu_irq_enable();
		pmc_enable_waitmode();

		cpu_irq_disable();
		pmc_restore_clock_setting(mor, pllr0, pllr1, mckr);
		b_is_fastrc_used = false;
		if (callback_clocks_restored) {
			callback_clocks_restored();
			callback_clocks_restored = NULL;
		}
		cpu_irq_enable();
		break;
	}

	case SAM_PM_SMODE_BACKUP:
		SCB->SCR |= SCR_SLEEPDEEP;
#if (SAM4S || SAM4E || SAM4N)
		SUPC->SUPC_CR = SUPC_CR_KEY(0xA5u) | SUPC_CR_VROFF_STOP_VREG;
		cpu_irq_enable();
		__WFI() ;
#else
		cpu_irq_enable();
		__WFE() ;
#endif
		break;
	}
}

bool pmc_is_wakeup_clocks_restored(void)
{
	return !b_is_fastrc_used;
}

void pmc_wait_wakeup_clocks_restore(
		pmc_callback_wakeup_clocks_restored_t callback)
{
	if (b_is_fastrc_used) {
		cpu_irq_disable();
		callback_clocks_restored = callback;
	} else if (callback) {
		callback();
	}
}

#endif /* #if (SAM3S || SAM3N || SAM3XA || SAM3U || SAM4S || SAM4E || SAM4N) */
