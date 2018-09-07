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

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"
#include "peripherals/acc.h"

/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

#define ACC_MR_INV_Pos		12	/* ACC invert output (reg offset) */

#define ACC_ACR_HYST_0mv_max	0x00	/* Hysteresis levels  */
#define ACC_ACR_HYST_50mv_max	0x01
#define ACC_ACR_HYST_90mv_max	0x11

/*----------------------------------------------------------------------------
 *         Exported functions
 *----------------------------------------------------------------------------*/

void acc_init(Acc *p_acc, uint32_t select_plus, uint32_t select_minus,
              uint32_t edge_type, uint32_t invert)
{
	/* Reset the controller */
	p_acc->ACC_CR |= ACC_CR_SWRST;

	/* Write to the MR register */
	p_acc->ACC_MR = (((select_plus << ACC_MR_SELPLUS_Pos) & ACC_MR_SELPLUS_Msk) |
			((select_minus << ACC_MR_SELMINUS_Pos) & ACC_MR_SELMINUS_Msk) |
			((edge_type << ACC_MR_EDGETYP_Pos) & ACC_MR_EDGETYP_Msk) |
			((invert << ACC_MR_INV_Pos) & ACC_MR_INV));

	/* Set hysteresis and current selection (ISEL) */
	p_acc->ACC_ACR = (ACC_ACR_ISEL_HISP | ACC_ACR_HYST(ACC_ACR_HYST_50mv_max));

	/* Automatic Output Masking Period */
	while (p_acc->ACC_ISR & (uint32_t)ACC_ISR_MASK) ;
}

void acc_enable(Acc *p_acc)
{
	p_acc->ACC_MR |= ACC_MR_ACEN_EN;
}

void acc_disable(Acc *p_acc)
{
	p_acc->ACC_MR &= ~ACC_MR_ACEN_EN;
}

void acc_reset(Acc *p_acc)
{
	p_acc->ACC_CR = ACC_CR_SWRST;
}

void acc_set_input(Acc *p_acc, uint32_t select_minus, uint32_t select_plus)
{
	p_acc->ACC_MR &= ~(ACC_MR_SELMINUS_Msk & ACC_MR_SELPLUS_Msk);
	p_acc->ACC_MR |= select_plus | select_minus;
}

void acc_set_output(Acc *p_acc, uint32_t invert, uint32_t fault_enable,
                    uint32_t fault_source)
{
	p_acc->ACC_MR &= ~(ACC_MR_INV_EN & ACC_MR_FE_EN & ACC_MR_SELFS_OUTPUT);
	p_acc->ACC_MR |= invert | fault_source | fault_enable;
}

uint32_t acc_get_comparison_result(Acc *p_acc)
{
	uint32_t temp = p_acc->ACC_MR;
	uint32_t status = p_acc->ACC_ISR;

	if ((temp & ACC_MR_INV_EN) == ACC_MR_INV_EN)
		return status & ACC_ISR_SCO ? 0 : 1;
	else
		return status & ACC_ISR_SCO ? 1 : 0;
}

void acc_enable_interrupt(Acc *p_acc)
{
	p_acc->ACC_IER = ACC_IER_CE;
}

void acc_disable_interrupt(Acc *p_acc)
{
	p_acc->ACC_IDR = ACC_IDR_CE;
}

uint32_t acc_get_interrupt_status(Acc *p_acc)
{
	return p_acc->ACC_ISR;
}

void acc_set_write_protect(Acc *p_acc, uint32_t enable)
{
	if (enable)
		p_acc->ACC_WPMR = ACC_WPMR_WPKEY_PASSWD | ACC_WPMR_WPEN;
	else
		p_acc->ACC_WPMR = ACC_WPMR_WPKEY_PASSWD;
}

uint32_t acc_get_write_protect_status(Acc *p_acc)
{
	return p_acc->ACC_WPSR & ACC_WPSR_WPVS;
}
