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
#include "peripherals/shdwc.h"
#include <stdint.h>

/*----------------------------------------------------------------------------
 *        Local Defines
 *----------------------------------------------------------------------------*/

struct _bitfield_shdwc_cfgr {
	uint32_t
		lpdbcen0: 1,
		lpdbcen1: 1,
		rfu2_7:   6,
		lpdbc:    3,
		rfu10_15: 5,
		rttwken:  1,
		rtcwken:  1,
		accwken:  1,
		rxlpwken: 1,
		rfu20_23: 4,
		wkupdbc:  3,
		rfu26_31: 5;
};

union _shdwc_cfg {
	struct _bitfield_shdwc_cfgr bfield;
	uint32_t uint32_value;
};

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

void shdwc_configure_wakeup_mode(uint32_t config)
{
	union _shdwc_cfg cfg;

	cfg.uint32_value = SHDWC->SHDW_MR;

	cfg.bfield.lpdbcen0 = (config & SHDW_MR_LPDBCEN0_ENABLE) ? 1 : 0;
	cfg.bfield.lpdbcen1 = (config & SHDW_MR_LPDBCEN1_ENABLE) ? 1 : 0;
	cfg.bfield.lpdbc = (config & SHDW_MR_LPDBC_Msk) >> SHDW_MR_LPDBC_Pos;
	cfg.bfield.rttwken = (config & SHDW_MR_RTTWKEN) ? 1 : 0;
	cfg.bfield.rtcwken = (config & SHDW_MR_RTCWKEN) ? 1 : 0;
	cfg.bfield.accwken = (config & SHDW_MR_ACCWKEN) ? 1 : 0;
	cfg.bfield.rxlpwken = (config & SHDW_MR_RXLPWKEN) ? 1 : 0;
	cfg.bfield.wkupdbc = (config & SHDW_MR_WKUPDBC_Msk) >> SHDW_MR_WKUPDBC_Pos;

	SHDWC->SHDW_MR = cfg.uint32_value;
}

void shdwc_set_wakeup_input(uint32_t input_enable, uint32_t input_type)
{
	uint32_t wuir = (input_enable & 0x0000FFFF) | (input_type & 0xFFFF0000);

	SHDWC->SHDW_WUIR |= wuir;
}

void shdwc_do_shutdown(void)
{
	SHDWC->SHDW_CR = SHDW_CR_KEY_PASSWD | SHDW_CR_SHDW;
}

uint32_t shdwc_get_status(void)
{
	return SHDWC->SHDW_SR;
}
