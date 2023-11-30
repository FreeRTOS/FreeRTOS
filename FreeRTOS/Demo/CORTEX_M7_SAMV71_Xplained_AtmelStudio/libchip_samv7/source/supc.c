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

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include <assert.h>

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Select external 32K Crystal.
 *
 */

void SUPC_SelectExtCrystal32K(void)
{
	PMC_EnableXT32KFME();
	/* Select XTAL 32k instead of internal slow RC 32k for slow clock */
	if ( (SUPC->SUPC_SR & SUPC_SR_OSCSEL) != SUPC_SR_OSCSEL_CRYST ) {
		SUPC->SUPC_CR = SUPC_CR_KEY_PASSWD | SUPC_CR_XTALSEL_CRYSTAL_SEL;
		while( !(SUPC->SUPC_SR & SUPC_SR_OSCSEL) );
	}
}

/**
 * \brief VROFF asserts the vddcore_nreset and stops the voltage regulator
 *
 */
void SUPC_DisableVoltageReg(void)
{
	SUPC->SUPC_CR |= SUPC_CR_KEY_PASSWD | SUPC_CR_VROFF;
}

/**
 * \brief Configures supply monitor
 *
 */
void SUPC_ConfigSupplyMonitor(uint32_t Config)
{
	SUPC->SUPC_SMMR = Config;
}


/**
 * \brief Disables supply monitor
 *
 */
void SUPC_DisableSupplyMonitor(void)
{
	SUPC->SUPC_SMMR = SUPC_SMMR_SMSMPL_SMD;
}


/**
 * \brief Enables/Disables Brownout detector
 *
 */
void SUPC_BrownoutDetectEnable(uint8_t enable)
{
	if(enable) {
		SUPC->SUPC_MR = ( SUPC_MR_BODDIS_ENABLE | SUPC_MR_KEY_PASSWD);
	} else {
		SUPC->SUPC_MR = ( SUPC_MR_BODDIS_DISABLE | SUPC_MR_KEY_PASSWD);
	}
}

/**
 * \brief Enables Brownout Detector Reset
 *
 */
void SUPC_BrownoutResetEnable(void)
{
	SUPC->SUPC_MR = ( SUPC_MR_BODRSTEN_ENABLE | SUPC_MR_KEY_PASSWD);
}


/**
 * \brief Enables/Disables Sram in backup mode
 *
 */
void SUPC_SramBackupMode(uint8_t enable)
{
	if(enable) {
		SUPC->SUPC_MR = ((1 << 17) | SUPC_MR_KEY_PASSWD);
	} else {
		SUPC->SUPC_MR = ( (0 << 17) | SUPC_MR_KEY_PASSWD);
	}
}

/**
 * \brief Bypass external 32.768KHz oscillator
 *
 */
void SUPC_BypassXtal32KOsc(void)
{
	SUPC->SUPC_MR = ( SUPC_MR_OSCBYPASS_BYPASS | SUPC_MR_KEY_PASSWD);    
}


/**
 * \brief Enables/Disables Wakeup mode
 *
 */
void SUPC_EnablesWakeupMode(uint32_t Regs, uint8_t enable)
{
	if(enable) {
		SUPC->SUPC_WUMR |= Regs;
	} else {
		SUPC->SUPC_WUMR &= ~(uint32_t)Regs;
	}
}

/**
 * \brief Configure Wakeup denounce period
 *
 */
void SUPC_SetWakeupDebounce(uint8_t period)
{
	SUPC->SUPC_WUMR |= ( (period << SUPC_WUMR_WKUPDBC_Pos) & SUPC_WUMR_WKUPDBC_Msk);
}

/**
 * \brief Configure Low-power denounce period
 *
 */
void SUPC_SetLowPowerDebounce(uint8_t period)
{
	SUPC->SUPC_WUMR |= ( (period << SUPC_WUMR_LPDBC_Pos) & SUPC_WUMR_LPDBC_Msk);
}


/**
 * \brief Enables/Disables Wakeup Inputs
 *
 */
void SUPC_EnablesWakeupInput(uint32_t Input, uint8_t enable)
{
	if(enable) {
		SUPC->SUPC_WUIR |= Input;
	} else {
		SUPC->SUPC_WUIR &= ~(uint32_t)Input;
	}
}

/**
 * \brief Checks if Crystal oscillator is selected as a slow clock
 */

uint8_t SUPC_IsSlowClkExtCrystal32K(void)
{
	return ((SUPC->SUPC_SR & SUPC_SR_OSCSEL) >> 7);
}

/**
 * \brief Checks if Crystal oscillator is selected as a slow clock
 */

uint8_t SUPC_Read_Status(uint32_t status)
{
	return (SUPC->SUPC_SR & status);
}


