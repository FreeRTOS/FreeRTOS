/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
 * \file
 *
 * Provides the low-level initialization function that called on chip startup.
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"
#include "board.h"
#include "compiler.h"
#include "timer.h"

#include "cortex-a/cpsr.h"

#include "peripherals/aic.h"
#include "peripherals/matrix.h"
#include "peripherals/pio.h"
#include "peripherals/pmc.h"

#include <stdio.h>

/*----------------------------------------------------------------------------
 *        Functions
 *----------------------------------------------------------------------------*/

extern void Undefined_Handler();
extern void Abort_Handler();
extern void FIQ_Handler();
extern void FreeRTOS_IRQ_Handler();

/**
 * \brief Performs the low-level initialization of the chip.
 * It also enable a low level on the pin NRST triggers a user reset.
 */
void low_level_init(void)
{
  uint32_t i;

	/* Setup default interrupt handlers */
	aic_initialize();

	/* Configure clocking if code is not in external mem */
	if ((uint32_t)low_level_init < DDR_CS_ADDR)
	{
		pmc_switch_mck_to_slck();
		pmc_set_mck_h32mxdiv(PMC_MCKR_H32MXDIV_H32MXDIV2);
		pmc_set_mck_plla_div(PMC_MCKR_PLLADIV2);
		pmc_set_mck_prescaler(PMC_MCKR_PRES_CLOCK);
		pmc_set_mck_divider(PMC_MCKR_MDIV_EQ_PCK);
		/* Disable PLLA */
		pmc_set_plla(0, PMC_PLLICPR_IPLL_PLLA(0x3));
		pmc_select_external_osc();
		/* Configure PLLA */
		pmc_set_plla(CKGR_PLLAR_ONE | CKGR_PLLAR_PLLACOUNT(0x3F) |
			CKGR_PLLAR_OUTA(0x0) | CKGR_PLLAR_MULA(82) |
			CKGR_PLLAR_DIVA_BYPASS, PMC_PLLICPR_IPLL_PLLA(0x3));
		pmc_set_mck_divider(PMC_MCKR_MDIV_PCK_DIV3);
		pmc_set_mck_prescaler(PMC_MCKR_PRES_CLOCK);
		pmc_switch_mck_to_pll();
	}

   /* select FIQ */
    AIC->AIC_SSR = 0;
    AIC->AIC_SVR = (unsigned int) FIQ_Handler;

    for (i = 1; i < 31; i++)
    {
        AIC->AIC_SSR = i;
        AIC->AIC_SVR =  (unsigned int) FreeRTOS_IRQ_Handler;
    }

    AIC->AIC_SPU =  (unsigned int) Undefined_Handler;

    /* Disable all interrupts */
    for (i = 1; i < 31; i++)
    {
        AIC->AIC_SSR  = i;
        AIC->AIC_IDCR = 1 ;
    }
    /* Clear All pending interrupts flags */
    for (i = 1; i < 31; i++)
    {
        AIC->AIC_SSR  = i;
        AIC->AIC_ICCR = 1 ;
    }
    /* Perform 8 IT acknoledge (write any value in EOICR) */
    for (i = 0; i < 8 ; i++)
    {
        AIC->AIC_EOICR = 0;
    }

	/* Remap */
	matrix_remap_ram();

	// timer_configure(BOARD_TIMER_RESOLUTION);
}

/**
 * \brief Restore all IOs to default state after power-on reset.
 */
void board_restore_pio_reset_state(void)
{
	unsigned int i;

	/* all pins, excluding JTAG and NTRST */
	struct _pin pins[] = {
		{ PIO_GROUP_A, 0xFFFFFFFF, PIO_INPUT, PIO_PULLUP },
		{ PIO_GROUP_B, 0xFFFFFFFF, PIO_INPUT, PIO_PULLUP },
		{ PIO_GROUP_C, 0xFFFFFFFF, PIO_INPUT, PIO_PULLUP },
		{ PIO_GROUP_D, 0xFFF83FFF, PIO_INPUT, PIO_PULLUP },
	};

	pio_configure(pins, ARRAY_SIZE(pins));
	for (i = 0; i < ARRAY_SIZE(pins); i++)
		pio_clear(&pins[i]);
}

void board_save_misc_power(void)
{
	int i;

	/* disable USB clock */
	pmc_disable_upll_clock();
	pmc_disable_upll_bias();

	/* Disable audio clock */
//	pmc_disable_audio();

	/* disable system clocks */
	pmc_disable_system_clock(PMC_SYSTEM_CLOCK_DDR);
	pmc_disable_system_clock(PMC_SYSTEM_CLOCK_LCD);
	pmc_disable_system_clock(PMC_SYSTEM_CLOCK_SMD);
	pmc_disable_system_clock(PMC_SYSTEM_CLOCK_UHP);
	pmc_disable_system_clock(PMC_SYSTEM_CLOCK_UDP);
	pmc_disable_system_clock(PMC_SYSTEM_CLOCK_PCK0);
	pmc_disable_system_clock(PMC_SYSTEM_CLOCK_PCK1);
	pmc_disable_system_clock(PMC_SYSTEM_CLOCK_PCK2);
	pmc_disable_system_clock(PMC_SYSTEM_CLOCK_ISC);

	/* disable all peripheral clocks except PIOA for JTAG, serial debug port */
	for (i = ID_PIT; i < ID_PERIPH_COUNT; i++) {
		if (i == ID_PIOA)
			continue;
		pmc_disable_peripheral(i);
	}
}

