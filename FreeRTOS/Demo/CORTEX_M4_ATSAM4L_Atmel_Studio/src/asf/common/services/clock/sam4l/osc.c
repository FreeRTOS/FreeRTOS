/**
 * \file
 *
 * \brief Chip-specific oscillator management functions
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
#include <osc.h>

#ifdef BOARD_OSC0_HZ
void osc_priv_enable_osc0(void)
{
	irqflags_t flags;

	flags = cpu_irq_save();
	SCIF->SCIF_UNLOCK = SCIF_UNLOCK_KEY(0xAAu)
		| SCIF_UNLOCK_ADDR((uint32_t)&SCIF->SCIF_OSCCTRL0 - (uint32_t)SCIF);
	SCIF->SCIF_OSCCTRL0 =
			OSC0_STARTUP_VALUE
# if BOARD_OSC0_IS_XTAL == true
			| OSC0_GAIN_VALUE
#endif
			| OSC0_MODE_VALUE
			| SCIF_OSCCTRL0_OSCEN;
	cpu_irq_restore(flags);
}

void osc_priv_disable_osc0(void)
{
	irqflags_t flags;

	flags = cpu_irq_save();
	SCIF->SCIF_UNLOCK = SCIF_UNLOCK_KEY(0xAAu)
		| SCIF_UNLOCK_ADDR((uint32_t)&SCIF->SCIF_OSCCTRL0 - (uint32_t)SCIF);
	SCIF->SCIF_OSCCTRL0 = 0;
	cpu_irq_restore(flags);
}
#endif /* BOARD_OSC0_HZ */

#ifdef BOARD_OSC32_HZ
void osc_priv_enable_osc32(void)
{
	irqflags_t flags;

	flags = cpu_irq_save();
	BSCIF->BSCIF_UNLOCK = BSCIF_UNLOCK_KEY(0xAAu)
		| BSCIF_UNLOCK_ADDR((uint32_t)&BSCIF->BSCIF_OSCCTRL32 - (uint32_t)BSCIF);
	BSCIF->BSCIF_OSCCTRL32 =
			OSC32_STARTUP_VALUE
			| BOARD_OSC32_SELCURR
			| OSC32_MODE_VALUE
			| BSCIF_OSCCTRL32_EN1K
			| BSCIF_OSCCTRL32_EN32K
			| BSCIF_OSCCTRL32_OSC32EN;
	cpu_irq_restore(flags);
}

void osc_priv_disable_osc32(void)
{
	irqflags_t flags;

	flags = cpu_irq_save();
	BSCIF->BSCIF_UNLOCK = BSCIF_UNLOCK_KEY(0xAAu)
		| BSCIF_UNLOCK_ADDR((uint32_t)&BSCIF->BSCIF_OSCCTRL32 - (uint32_t)BSCIF);
	BSCIF->BSCIF_OSCCTRL32 &= ~BSCIF_OSCCTRL32_OSC32EN;
	// Wait until OSC32 RDY flag is cleared.
	while (BSCIF->BSCIF_PCLKSR & BSCIF_PCLKSR_OSC32RDY);
	cpu_irq_restore(flags);
}
#endif /* BOARD_OSC32_HZ */

void osc_priv_enable_rc32k(void)
{
	irqflags_t flags;
	uint32_t temp;

	flags = cpu_irq_save();
	temp = BSCIF->BSCIF_RC32KCR;
	BSCIF->BSCIF_UNLOCK = BSCIF_UNLOCK_KEY(0xAAu)
		| BSCIF_UNLOCK_ADDR((uint32_t)&BSCIF->BSCIF_RC32KCR - (uint32_t)BSCIF);
	BSCIF->BSCIF_RC32KCR = temp | BSCIF_RC32KCR_EN32K | BSCIF_RC32KCR_EN;
	cpu_irq_restore(flags);
}

void osc_priv_disable_rc32k(void)
{
	irqflags_t flags;
	uint32_t temp;

	flags = cpu_irq_save();
	temp = BSCIF->BSCIF_RC32KCR;
	temp &= ~BSCIF_RC32KCR_EN;
	BSCIF->BSCIF_UNLOCK = BSCIF_UNLOCK_KEY(0xAAu)
		| BSCIF_UNLOCK_ADDR((uint32_t)&BSCIF->BSCIF_RC32KCR - (uint32_t)BSCIF);
	BSCIF->BSCIF_RC32KCR = temp;
	cpu_irq_restore(flags);
}

void osc_priv_enable_rc1m(void)
{
	irqflags_t flags;
	uint32_t temp;

	flags = cpu_irq_save();
	temp = BSCIF->BSCIF_RC1MCR;
	BSCIF->BSCIF_UNLOCK = BSCIF_UNLOCK_KEY(0xAAu)
		| BSCIF_UNLOCK_ADDR((uint32_t)&BSCIF->BSCIF_RC1MCR - (uint32_t)BSCIF);
	BSCIF->BSCIF_RC1MCR = temp | BSCIF_RC1MCR_CLKOE;
	cpu_irq_restore(flags);
}

void osc_priv_disable_rc1m(void)
{
	irqflags_t flags;
	uint32_t temp;

	flags = cpu_irq_save();
	temp = BSCIF->BSCIF_RC1MCR;
	temp &= ~BSCIF_RC1MCR_CLKOE;
	BSCIF->BSCIF_UNLOCK = BSCIF_UNLOCK_KEY(0xAAu)
		| BSCIF_UNLOCK_ADDR((uint32_t)&BSCIF->BSCIF_RC1MCR - (uint32_t)BSCIF);
	BSCIF->BSCIF_RC1MCR = temp;
	cpu_irq_restore(flags);
}

void osc_priv_enable_rc80m(void)
{
	irqflags_t flags;
	uint32_t temp;

	flags = cpu_irq_save();
	temp = SCIF->SCIF_RC80MCR;
	SCIF->SCIF_UNLOCK = SCIF_UNLOCK_KEY(0xAAu)
		| SCIF_UNLOCK_ADDR((uint32_t)&SCIF->SCIF_RC80MCR - (uint32_t)SCIF);
	SCIF->SCIF_RC80MCR = temp | SCIF_RC80MCR_EN;
	cpu_irq_restore(flags);
}

void osc_priv_disable_rc80m(void)
{
	irqflags_t flags;
	uint32_t temp;

	flags = cpu_irq_save();
	temp = SCIF->SCIF_RC80MCR;
	temp &= ~SCIF_RC80MCR_EN ;
	SCIF->SCIF_UNLOCK = SCIF_UNLOCK_KEY(0xAAu)
		| SCIF_UNLOCK_ADDR((uint32_t)&SCIF->SCIF_RC80MCR - (uint32_t)SCIF);
	SCIF->SCIF_RC80MCR = temp;
	cpu_irq_restore(flags);
}

void osc_priv_enable_rcfast(void)
{
	irqflags_t flags;
	uint32_t temp;

	flags = cpu_irq_save();
	// Let FCD and calibration value by default
	temp = SCIF->SCIF_RCFASTCFG;
	// Clear previous FRANGE value
	temp &= ~SCIF_RCFASTCFG_FRANGE_Msk;

	SCIF->SCIF_UNLOCK = SCIF_UNLOCK_KEY(0xAAu)
		| SCIF_UNLOCK_ADDR((uint32_t)&SCIF->SCIF_RCFASTCFG - (uint32_t)SCIF);
	SCIF->SCIF_RCFASTCFG = temp | SCIF_RCFASTCFG_EN
		| SCIF_RCFASTCFG_FRANGE(CONFIG_RCFAST_FRANGE);
	cpu_irq_restore(flags);
}

void osc_priv_disable_rcfast(void)
{
	irqflags_t flags;
	uint32_t temp;
	flags = cpu_irq_save();
	// Let FCD and calibration value by default
	temp = SCIF->SCIF_RCFASTCFG;
	// Clear previous FRANGE value
	temp &= ~SCIF_RCFASTCFG_FRANGE_Msk;
	// Disalbe RCFAST
	temp &= ~SCIF_RCFASTCFG_EN;
	SCIF->SCIF_UNLOCK = SCIF_UNLOCK_KEY(0xAAu)
		| SCIF_UNLOCK_ADDR((uint32_t)&SCIF->SCIF_RCFASTCFG - (uint32_t)SCIF);
	SCIF->SCIF_RCFASTCFG = temp;
	cpu_irq_restore(flags);
}

