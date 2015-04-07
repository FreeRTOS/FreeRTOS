/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
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

//------------------------------------------------------------------------------
/// \unit
///
/// !Purpose
///
/// Provides the low-level initialization function that gets called on chip
/// startup.
///
/// !Usage
///
/// LowLevelInit() is called in #board_cstartup_xxx.c#.
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include "board.h"
#include "board_memories.h"
#include "board_lowlevel.h"
#include <pio/pio.h>

//------------------------------------------------------------------------------
//         Local definitions
//------------------------------------------------------------------------------
// Settings at 48/48MHz
#define AT91C_CKGR_MUL_SHIFT         16
#define AT91C_CKGR_OUT_SHIFT         14
#define AT91C_CKGR_PLLCOUNT_SHIFT     8
#define AT91C_CKGR_DIV_SHIFT          0

#define BOARD_OSCOUNT         (AT91C_CKGR_MOSCXTST & (0x3F << 8))
#define BOARD_PLLR ((1 << 29) | (0x7 << AT91C_CKGR_MUL_SHIFT) \
        | (0x0 << AT91C_CKGR_OUT_SHIFT) |(0x3f << AT91C_CKGR_PLLCOUNT_SHIFT) \
        | (0x1 << AT91C_CKGR_DIV_SHIFT))
#define BOARD_MCKR ( AT91C_PMC_PRES_CLK_2 | AT91C_PMC_CSS_PLLA_CLK)

// Define clock timeout
#define CLOCK_TIMEOUT           0xFFFFFFFF

#define AT91C_SUPC_SR_OSCSEL_CRYST 0x80UL
#define AT91C_SUPC_CR_XTALSEL_CRYSTAL_SEL 0x08UL

void SetDefaultMaster(unsigned char enable);

//------------------------------------------------------------------------------
//         Local variables
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//         Local functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//         Exported functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// After POR, at91sam3u device is running on 4MHz internal RC
/// At the end of the LowLevelInit procedure MCK = 48MHz PLLA = 96 CPU=48MHz
/// Performs the low-level initialization of the chip. This includes EFC, master
/// clock, IRQ & watchdog configuration.
//------------------------------------------------------------------------------
void LowLevelInit(void)
{
    unsigned int timeout = 0;

    /* Set 2 WS for Embedded Flash Access
     ************************************/
    AT91C_BASE_EFC0->EFC_FMR = AT91C_EFC_FWS_2WS;
    AT91C_BASE_EFC1->EFC_FMR = AT91C_EFC_FWS_2WS;

    /* Watchdog initialization
     *************************/
    AT91C_BASE_WDTC->WDTC_WDMR = AT91C_WDTC_WDDIS;

    /* Select external slow clock
     ****************************/
    if ((AT91C_BASE_SUPC->SUPC_SR & AT91C_SUPC_SR_OSCSEL_CRYST) != AT91C_SUPC_SR_OSCSEL_CRYST) {
        AT91C_BASE_SUPC->SUPC_CR = AT91C_SUPC_CR_XTALSEL_CRYSTAL_SEL | (0xA5UL << 24UL);
        timeout = 0;
        while (!(AT91C_BASE_SUPC->SUPC_SR & AT91C_SUPC_SR_OSCSEL_CRYST) && (timeout++ < CLOCK_TIMEOUT));
    }

    /* Initialize main oscillator
     ****************************/

	if(!(AT91C_BASE_PMC->PMC_MOR & AT91C_CKGR_MOSCSEL))
	{
		AT91C_BASE_PMC->PMC_MOR = (0x37 << 16) | BOARD_OSCOUNT | AT91C_CKGR_MOSCRCEN | AT91C_CKGR_MOSCXTEN;
		timeout = 0;
		while (!(AT91C_BASE_PMC->PMC_SR & AT91C_PMC_MOSCXTS) && (timeout++ < CLOCK_TIMEOUT));
	}	
	else
    {
		AT91C_BASE_PMC->PMC_MOR = (0x37 << 16) | BOARD_OSCOUNT | AT91C_CKGR_MOSCRCEN | AT91C_CKGR_MOSCXTEN | AT91C_CKGR_MOSCSEL;
        timeout = 0;
        while (!(AT91C_BASE_PMC->PMC_SR & AT91C_PMC_MOSCRCS) && (timeout++ < CLOCK_TIMEOUT));
        AT91C_BASE_PMC->PMC_MOR = (0x37 << 16) | BOARD_OSCOUNT | AT91C_CKGR_MOSCRCEN | AT91C_CKGR_MOSCXTEN;
        timeout = 0;
        while (!(AT91C_BASE_PMC->PMC_SR & AT91C_PMC_MOSCSELS) && (timeout++ < CLOCK_TIMEOUT));
    }

    /* Switch to moscsel */
    AT91C_BASE_PMC->PMC_MOR = (0x37 << 16) | BOARD_OSCOUNT | AT91C_CKGR_MOSCRCEN | AT91C_CKGR_MOSCXTEN | AT91C_CKGR_MOSCSEL;
    timeout = 0;
    while (!(AT91C_BASE_PMC->PMC_SR & AT91C_PMC_MOSCSELS) && (timeout++ < CLOCK_TIMEOUT));
    AT91C_BASE_PMC->PMC_MCKR = (AT91C_BASE_PMC->PMC_MCKR & ~AT91C_PMC_CSS) | AT91C_PMC_CSS_MAIN_CLK;
    timeout = 0;
    while (!(AT91C_BASE_PMC->PMC_SR & AT91C_PMC_MCKRDY) && (timeout++ < CLOCK_TIMEOUT));

    /* Initialize PLLA */
    AT91C_BASE_PMC->PMC_PLLAR = BOARD_PLLR;
    timeout = 0;
    while (!(AT91C_BASE_PMC->PMC_SR & AT91C_PMC_LOCKA) && (timeout++ < CLOCK_TIMEOUT));

    /* Initialize UTMI for USB usage */
    AT91C_BASE_CKGR->CKGR_UCKR |= (AT91C_CKGR_UPLLCOUNT & (3 << 20)) | AT91C_CKGR_UPLLEN;
    timeout = 0;
    while (!(AT91C_BASE_PMC->PMC_SR & AT91C_PMC_LOCKU) && (timeout++ < CLOCK_TIMEOUT));

    /* Switch to fast clock
     **********************/
    AT91C_BASE_PMC->PMC_MCKR = (BOARD_MCKR & ~AT91C_PMC_CSS) | AT91C_PMC_CSS_MAIN_CLK;
    timeout = 0;
    while (!(AT91C_BASE_PMC->PMC_SR & AT91C_PMC_MCKRDY) && (timeout++ < CLOCK_TIMEOUT));

    AT91C_BASE_PMC->PMC_MCKR = BOARD_MCKR;
    timeout = 0;
    while (!(AT91C_BASE_PMC->PMC_SR & AT91C_PMC_MCKRDY) && (timeout++ < CLOCK_TIMEOUT));

    /* Enable clock for UART
     ************************/
    AT91C_BASE_PMC->PMC_PCER = (1 << AT91C_ID_DBGU);

    /* Optimize CPU setting for speed */
    SetDefaultMaster(1);

}

//------------------------------------------------------------------------------
/// Enable or disable default master access
/// \param enalbe 1 enable defaultMaster settings, 0 disable it.
//------------------------------------------------------------------------------
void SetDefaultMaster(unsigned char enable)
{
    AT91PS_HMATRIX2 pMatrix = AT91C_BASE_MATRIX;

    // Set default master
    if (enable == 1) {

        // Set default master: SRAM0 -> Cortex-M3 System
        pMatrix->HMATRIX2_SCFG0 |= AT91C_MATRIX_FIXED_DEFMSTR_SCFG0_ARMS |
                                   AT91C_MATRIX_DEFMSTR_TYPE_FIXED_DEFMSTR;

        // Set default master: SRAM1 -> Cortex-M3 System
        pMatrix->HMATRIX2_SCFG1 |= AT91C_MATRIX_FIXED_DEFMSTR_SCFG1_ARMS |
                                   AT91C_MATRIX_DEFMSTR_TYPE_FIXED_DEFMSTR;

        // Set default master: Internal flash0 -> Cortex-M3 Instruction/Data
        pMatrix->HMATRIX2_SCFG3 |= AT91C_MATRIX_FIXED_DEFMSTR_SCFG3_ARMC |
                                   AT91C_MATRIX_DEFMSTR_TYPE_FIXED_DEFMSTR;
    } else {

        // Clear default master: SRAM0 -> Cortex-M3 System
        pMatrix->HMATRIX2_SCFG0 &= (~AT91C_MATRIX_DEFMSTR_TYPE);

        // Clear default master: SRAM1 -> Cortex-M3 System
        pMatrix->HMATRIX2_SCFG1 &= (~AT91C_MATRIX_DEFMSTR_TYPE);

        // Clear default master: Internal flash0 -> Cortex-M3 Instruction/Data
        pMatrix->HMATRIX2_SCFG3 &= (~AT91C_MATRIX_DEFMSTR_TYPE);
    }
}

//------------------------------------------------------------------------------
/// Set flash wait state
/// \param ws    Value of flash wait state
//------------------------------------------------------------------------------
void SetFlashWaitState(unsigned char ws)
{
    // Set Wait State for Embedded Flash Access
	AT91C_BASE_EFC0->EFC_FMR = ((ws << 8) & AT91C_EFC_FWS);
	AT91C_BASE_EFC1->EFC_FMR = ((ws << 8) & AT91C_EFC_FWS);
}

