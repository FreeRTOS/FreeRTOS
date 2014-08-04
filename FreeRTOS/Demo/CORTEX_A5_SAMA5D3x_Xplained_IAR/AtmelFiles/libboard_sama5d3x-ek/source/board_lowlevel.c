/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
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

#include "board.h"

/*----------------------------------------------------------------------------
 *        Internal functions
 *----------------------------------------------------------------------------*/
/**
 * \brief Default spurious interrupt handler. Infinite loop.
 */
void defaultSpuriousHandler( void )
{
    while (1);
}

/**
 * \brief Default handler for fast interrupt requests. Infinite loop.
 */
void defaultFiqHandler( void )
{
    while (1);
}

/**
 * \brief Default handler for standard interrupt requests. Infinite loop.
 */
void defaultIrqHandler( void )
{
    while (1);
}

/**
 * \brief Performs the low-level initialization of the chip.
 * This includes EFC and master clock configuration.
 * It also enable a low level on the pin NRST triggers a user reset.
 */
extern WEAK void LowLevelInit( void )
{
    uint32_t i;
    if ((uint32_t)LowLevelInit < DDR_CS_ADDR) /* Code not in external mem */ {
        PMC_SelectExt12M_Osc();
        PMC_SwitchMck2Main();
        PMC_SetPllA( CKGR_PLLAR_STUCKTO1 |
                     CKGR_PLLAR_PLLACOUNT(0x3F) |
                     CKGR_PLLAR_OUTA(0x0) |
                     CKGR_PLLAR_MULA(65) |
                     CKGR_PLLAR_DIVA(1),
                     0x3u << 8);
        PMC_SetMckPllaDiv(PMC_MCKR_PLLADIV2_DIV2);
        PMC_SetMckPrescaler(PMC_MCKR_PRES_CLOCK);
        PMC_SetMckDivider(PMC_MCKR_MDIV_PCK_DIV3);
        PMC_SwitchMck2Pll();
    }

#if 0
    uint32_t abcdsr;
    /* Configure PCK1 to measure MCK */
    PIOD->PIO_IDR = (1<<31);
    abcdsr = PIOD->PIO_ABCDSR[0];
    PIOD->PIO_ABCDSR[0] = ((1<<31) | abcdsr);
    abcdsr = PIOD->PIO_ABCDSR[1];
    PIOD->PIO_ABCDSR[1] &= (~(1<<31) & abcdsr);
    PIOD->PIO_PDR = (1<<31);

    /* Disable programmable clock 1 output */
    REG_PMC_SCDR = PMC_SCER_PCK1;
    /* Enable the DAC master clock */
    PMC->PMC_PCK[1] = PMC_PCK_CSS_MCK_CLK | PMC_PCK_PRES_CLOCK;
    /* Enable programmable clock 1 output */
    REG_PMC_SCER = PMC_SCER_PCK1;
    /* Wait for the PCKRDY1 bit to be set in the PMC_SR register*/
    while ((REG_PMC_SR & PMC_SR_PCKRDY1) == 0);
#endif

    /* select FIQ */
    AIC->AIC_SSR = 0;
    AIC->AIC_SVR = (unsigned int) defaultFiqHandler;

    for (i = 1; i < 31; i++)
    {
        AIC->AIC_SSR = i;
        AIC->AIC_SVR =  (unsigned int) defaultIrqHandler;
    }

    AIC->AIC_SPU =  (unsigned int) defaultSpuriousHandler;

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
    BOARD_RemapRam();
}

