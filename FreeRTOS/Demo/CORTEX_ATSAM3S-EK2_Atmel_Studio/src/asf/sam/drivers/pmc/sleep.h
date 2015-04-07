/**
 * \file
 *
 * \brief Sleep mode access
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

#ifndef SLEEP_H
#define SLEEP_H

#ifdef __cplusplus
extern "C" {
#endif

#include <compiler.h>

/**
 * \defgroup sleep_group Power Manager (PM)
 *
 * This is a stub on the SAM Power Manager Control (PMC) for the sleepmgr service.
 *
 * \note To minimize the code overhead, these functions do not feature
 * interrupt-protected access since they are likely to be called inside
 * interrupt handlers or in applications where such protection is not
 * necessary. If such protection is needed, it must be ensured by the calling
 * code.
 *
 * @{
 */

#if defined(__DOXYGEN__)
/**
 * \brief Sets the MCU in the specified sleep mode
 * \param sleep_mode Sleep mode to set.
 */
#endif

#if (SAM3S || SAM3N || SAM3XA || SAM3U || SAM4S) // SAM3 and SAM4 series
# include "pmc.h"

# define  SAM_PM_SMODE_ACTIVE     0
# define  SAM_PM_SMODE_SLEEP_WFE  1
# define  SAM_PM_SMODE_SLEEP_WFI  2
# define  SAM_PM_SMODE_WAIT       3
# define  SAM_PM_SMODE_BACKUP     4

/* (SCR) Sleep deep bit */
#define SCR_SLEEPDEEP   (0x1 <<  2)

/**
 * Save clock settings and shutdown PLLs
 */
static inline void pmc_save_clock_settings(
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
#if SAM3S||SAM4S
		*p_pll1_setting = PMC->CKGR_PLLBR;
#elif SAM3U||SAM3XA
		*p_pll1_setting = PMC->CKGR_UCKR;
#else
		*p_pll1_setting = 0;
#endif
	}
	if (p_mck_setting) {
		*p_mck_setting  = PMC->PMC_MCKR;
	}

	// Switch MCK to Main clock (internal or external 12MHz) for fast wakeup
	// If MAIN_CLK is already the source, just skip
	if ((PMC->PMC_MCKR & PMC_MCKR_CSS_Msk) == PMC_MCKR_CSS_MAIN_CLK) {
		return;
	}
	// If we have to enable the MAIN_CLK
	if ((PMC->PMC_SR & PMC_SR_MOSCXTS) == 0) {
		// Intend to use internal RC as source of MAIN_CLK
		pmc_osc_enable_fastrc(CKGR_MOR_MOSCRCF_12_MHz);
		pmc_switch_mainck_to_fastrc(CKGR_MOR_MOSCRCF_12_MHz);
	}
	pmc_switch_mck_to_mainck(PMC_MCKR_PRES_CLK_1);
}

/**
 * Restore clock settings
 */
static inline void pmc_restore_clock_setting(
		uint32_t osc_setting,
		uint32_t pll0_setting,
		uint32_t pll1_setting,
		uint32_t mck_setting)
{
	uint32_t mckr;
	if ((pll0_setting & CKGR_PLLAR_MULA_Msk) &&
		pll0_setting != PMC->CKGR_PLLAR) {
		PMC->CKGR_PLLAR = 0;
		PMC->CKGR_PLLAR = CKGR_PLLAR_ONE | pll0_setting;
		while (!(PMC->PMC_SR & PMC_SR_LOCKA));
	}
#if SAM3S||SAM4S
	if ((pll1_setting & CKGR_PLLBR_MULB_Msk) &&
		pll1_setting != PMC->CKGR_PLLBR) {
		PMC->CKGR_PLLBR = 0;
		PMC->CKGR_PLLBR = pll1_setting ;
		while (!(PMC->PMC_SR & PMC_SR_LOCKB));
	}
#elif SAM3U||SAM3XA
	if ((pll1_setting & CKGR_UCKR_UPLLEN) &&
		pll1_setting != PMC->CKGR_UCKR) {
		PMC->CKGR_UCKR = 0;
		PMC->CKGR_UCKR = pll1_setting;
		while (!(PMC->PMC_SR & PMC_SR_LOCKU));
	}
#else
	UNUSED(pll1_setting);
#endif
	/* Switch to faster clock */
	mckr = PMC->PMC_MCKR;
	// Set PRES
	PMC->PMC_MCKR = (mckr & ~PMC_MCKR_PRES_Msk)
		| (mck_setting & PMC_MCKR_PRES_Msk);
	while (!(PMC->PMC_SR & PMC_SR_MCKRDY));
	// Set CSS and others
	PMC->PMC_MCKR = mck_setting;
	while (!(PMC->PMC_SR & PMC_SR_MCKRDY));
	/* Shutdown fastrc */
	if (0 == (osc_setting & CKGR_MOR_MOSCRCEN)) {
		pmc_osc_disable_fastrc();
	}
}

static inline void pmc_sleep(int sleep_mode)
{
	switch (sleep_mode) {
	case SAM_PM_SMODE_SLEEP_WFI:
	case SAM_PM_SMODE_SLEEP_WFE:
		PMC->PMC_FSMR &= (uint32_t)~PMC_FSMR_LPM;
		SCB->SCR &= (uint32_t)~SCR_SLEEPDEEP;
		cpu_irq_enable();
		if (sleep_mode == SAM_PM_SMODE_SLEEP_WFI)
			__WFI();
		else
			__WFE();
		break;

	case SAM_PM_SMODE_WAIT: {
		uint32_t mor, pllr0, pllr1, mckr;
		pmc_save_clock_settings(&mor, &pllr0, &pllr1, &mckr);

		PMC->PMC_FSMR |= PMC_FSMR_LPM;
		SCB->SCR &= (uint32_t)~SCR_SLEEPDEEP ;
		cpu_irq_enable();
		__WFE();

		cpu_irq_disable();
		pmc_restore_clock_setting(mor, pllr0, pllr1, mckr);
		cpu_irq_enable();
		break;
	}

	case SAM_PM_SMODE_BACKUP:
		SCB->SCR |= SCR_SLEEPDEEP ;
		cpu_irq_enable();
		__WFE() ;
		break;
	}
}

#endif

//! @}

#ifdef __cplusplus
}
#endif

#endif /* SLEEP_H */
