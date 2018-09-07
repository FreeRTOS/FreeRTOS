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
#include "board.h"
#include "trace.h"

#include "peripherals/classd.h"
#include "peripherals/pmc.h"

#include <stdio.h>
#include <string.h>

/*----------------------------------------------------------------------------
 *        Local constants
 *----------------------------------------------------------------------------*/

static const struct {
	uint32_t rate;
	uint32_t sample_rate;
	uint32_t dsp_clk;
} audio_info[] = {
	{ 8000,  CLASSD_INTPMR_FRAME_FRAME_8K, CLASSD_INTPMR_DSPCLKFREQ_12M288 },
	{ 16000, CLASSD_INTPMR_FRAME_FRAME_16K, CLASSD_INTPMR_DSPCLKFREQ_12M288 },
	{ 32000, CLASSD_INTPMR_FRAME_FRAME_32K, CLASSD_INTPMR_DSPCLKFREQ_12M288 },
	{ 48000, CLASSD_INTPMR_FRAME_FRAME_48K, CLASSD_INTPMR_DSPCLKFREQ_12M288 },
	{ 96000, CLASSD_INTPMR_FRAME_FRAME_96K, CLASSD_INTPMR_DSPCLKFREQ_12M288 },
	{ 22050, CLASSD_INTPMR_FRAME_FRAME_22K, CLASSD_INTPMR_DSPCLKFREQ_11M2896 },
	{ 44100, CLASSD_INTPMR_FRAME_FRAME_44K, CLASSD_INTPMR_DSPCLKFREQ_11M2896 },
	{ 88200, CLASSD_INTPMR_FRAME_FRAME_88K, CLASSD_INTPMR_DSPCLKFREQ_11M2896 },
};

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

static bool _dspclk_configure(uint32_t dsp_clk)
{
	struct _pmc_audio_cfg cfg;

	/* Pad Clock: not used */
	cfg.div = 0;
	cfg.qdaudio = 0;

	/* PMC Clock: */
	/* 12Mhz * (ND + 1 + FRACR/2^22) / (QDPMC + 1) = 8 * DSPCLK */
	switch (dsp_clk) {
	case CLASSD_INTPMR_DSPCLKFREQ_12M288:
		/* 12Mhz * (56 + 1 + 1442841/2^22) / (6 + 1) = 8 * 12.288Mhz */
		cfg.nd = 56;
		cfg.fracr = 1442841;
		cfg.qdpmc = 6;
		break;
	case CLASSD_INTPMR_DSPCLKFREQ_11M2896:
		/* 12Mhz * (59 + 1 + 885837/2^22) / (7 + 1) = 8 * 11.2896Mhz */
		cfg.nd = 59;
		cfg.fracr = 885837;
		cfg.qdpmc = 7;
		break;
	default:
		return false;
	}

	pmc_configure_audio(&cfg);
	pmc_enable_audio(true, false);

#ifndef NDEBUG
	{
		uint32_t clk;
		clk = pmc_get_audio_pmc_clock();
		trace_debug("Configured Audio PLL PMC Clock: %u (= 8 * %u)\r\n",
				(unsigned)clk, (unsigned)(clk >> 3));
	}
#endif

	return true;
}

static bool _set_eqcfg_bits(enum _classd_eqcfg eqcfg, volatile uint32_t *intpmr)
{
	uint32_t mask = CLASSD_INTPMR_EQCFG_Msk;
	uint32_t bits = 0;

	switch (eqcfg) {
	case CLASSD_EQCFG_FLAT:
		bits = CLASSD_INTPMR_EQCFG_FLAT;
		break;
	case CLASSD_EQCFG_BBOOST12:
		bits = CLASSD_INTPMR_EQCFG_BBOOST12;
		break;
	case CLASSD_EQCFG_BBOOST6:
		bits = CLASSD_INTPMR_EQCFG_BBOOST6;
		break;
	case CLASSD_EQCFG_BCUT12:
		bits = CLASSD_INTPMR_EQCFG_BCUT12;
		break;
	case CLASSD_EQCFG_BCUT6:
		bits = CLASSD_INTPMR_EQCFG_BCUT6;
		break;
	case CLASSD_EQCFG_MBOOST3:
		bits = CLASSD_INTPMR_EQCFG_MBOOST3;
		break;
	case CLASSD_EQCFG_MBOOST8:
		bits = CLASSD_INTPMR_EQCFG_MBOOST8;
		break;
	case CLASSD_EQCFG_MCUT3:
		bits = CLASSD_INTPMR_EQCFG_MCUT3;
		break;
	case CLASSD_EQCFG_MCUT8:
		bits = CLASSD_INTPMR_EQCFG_MCUT8;
		break;
	case CLASSD_EQCFG_TBOOST12:
		bits = CLASSD_INTPMR_EQCFG_TBOOST12;
		break;
	case CLASSD_EQCFG_TBOOST6:
		bits = CLASSD_INTPMR_EQCFG_TBOOST6;
		break;
	case CLASSD_EQCFG_TCUT12:
		bits = CLASSD_INTPMR_EQCFG_TCUT12;
		break;
	case CLASSD_EQCFG_TCUT6:
		bits = CLASSD_INTPMR_EQCFG_TCUT6;
		break;
	default:
		trace_warning("classd: invalid equalizer config %u\r\n",
				(unsigned)eqcfg);
		return false;
	};

	*intpmr = (*intpmr & ~mask) | bits;
	return true;
}

static bool _set_mono_bits(bool mono, enum _classd_mono mono_mode, volatile uint32_t *intpmr)
{
	uint32_t mask = CLASSD_INTPMR_MONO_ENABLED | CLASSD_INTPMR_MONOMODE_Msk;
	uint32_t bits = 0;

	if (mono) {
		bits = CLASSD_INTPMR_MONO_ENABLED;
		switch (mono_mode) {
		case CLASSD_MONO_MIXED:
			bits |= CLASSD_INTPMR_MONOMODE_MONOMIX;
			break;
		case CLASSD_MONO_SAT:
			bits |= CLASSD_INTPMR_MONOMODE_MONOSAT;
			break;
		case CLASSD_MONO_LEFT:
			bits |= CLASSD_INTPMR_MONOMODE_MONOLEFT;
			break;
		case CLASSD_MONO_RIGHT:
			bits |= CLASSD_INTPMR_MONOMODE_MONORIGHT;
			break;
		default:
			trace_warning("classd: invalid mono mode %u\r\n",
					(unsigned)mono_mode);
			return false;
		}
	}

	*intpmr = (*intpmr & ~mask) | bits;
	return true;
}

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

bool classd_configure(struct _classd_desc *desc)
{
	uint8_t i;
	uint32_t mr, intpmr, dsp_clk_set, frame_set;

	for (i = 0; i < ARRAY_SIZE(audio_info); i++) {
		if (audio_info[i].rate == desc->sample_rate) {
			dsp_clk_set  = audio_info[i].dsp_clk;
			frame_set = audio_info[i].sample_rate;
			break;
		}
	}
	if(i == ARRAY_SIZE(audio_info))
		return false;

	if (!_dspclk_configure(dsp_clk_set))
		return false;

	/* enable peripheral clock, disable audio clock for now */
	pmc_enable_peripheral(ID_CLASSD);
	pmc_disable_gck(ID_CLASSD);
	pmc_configure_gck(ID_CLASSD, PMC_PCR_GCKCSS_AUDIO_CLK, 0);

	/* perform soft reset */
	CLASSD->CLASSD_CR  = CLASSD_CR_SWRST;
	CLASSD->CLASSD_IDR = CLASSD_IDR_DATRDY;

	/* initial MR/INTPMR values */
	mr = 0;
	intpmr = dsp_clk_set | frame_set;

	/* configure output mode */
	switch (desc->mode) {
	case CLASSD_OUTPUT_SINGLE_ENDED:
		break;
	case CLASSD_OUTPUT_DIFFERENTIAL:
		mr |= CLASSD_MR_PWMTYP;
		break;
	case CLASSD_OUTPUT_HALF_BRIDGE:
		mr |= CLASSD_MR_NON_OVERLAP;
		break;
	case CLASSD_OUTPUT_FULL_BRIDGE:
		mr |= CLASSD_MR_PWMTYP | CLASSD_MR_NON_OVERLAP;
		break;
	default:
		trace_warning("classd: invalid mode %u\n", (unsigned)desc->mode);
		return false;
	}

	/* configure non-overlapping time */
	if (mr & CLASSD_MR_NON_OVERLAP) {
		switch (desc->non_ovr) {
		case CLASSD_NONOVR_5NS:
			mr |= CLASSD_MR_NOVRVAL_5NS;
			break;
		case CLASSD_NONOVR_10NS:
			mr |= CLASSD_MR_NOVRVAL_10NS;
			break;
		case CLASSD_NONOVR_15NS:
			mr |= CLASSD_MR_NOVRVAL_15NS;
			break;
		case CLASSD_NONOVR_20NS:
			mr |= CLASSD_MR_NOVRVAL_20NS;
			break;
		default:
			trace_warning("classd: invalid non overlap value %u\r\n",
					(unsigned)desc->non_ovr);
			return false;
		}
	}

	/* configure mono/stereo */
	if (desc->swap_channels)
		intpmr |= CLASSD_INTPMR_SWAP;
	if (!_set_mono_bits(desc->mono, desc->mono_mode, &intpmr))
		return false;

	/* configure left channel (muted, max attn) */
	if (desc->left_enable)
		mr |= CLASSD_MR_LEN;
	mr |= CLASSD_MR_LMUTE;
	intpmr |= CLASSD_INTPMR_ATTL(CLASSD_INTPMR_ATTL_Msk);

	/* configure right channel (muted, max attn)  */
	if (desc->right_enable)
		mr |= CLASSD_MR_REN;
	mr |= CLASSD_MR_RMUTE;
	intpmr |= CLASSD_INTPMR_ATTR(CLASSD_INTPMR_ATTL_Msk);

	/* write configuration */
	CLASSD->CLASSD_MR = mr;
	CLASSD->CLASSD_INTPMR = intpmr;

	/* enable audio clock */
	pmc_enable_gck(ID_CLASSD);

	return (CLASSD->CLASSD_INTSR & CLASSD_INTSR_CFGERR) == 0;
}

void classd_disable(void)
{
	pmc_disable_audio();
	pmc_disable_gck(ID_CLASSD);
	pmc_disable_peripheral(ID_CLASSD);
}

void classd_swap_channels(bool swap)
{
	if (swap) {
		CLASSD->CLASSD_INTPMR |= CLASSD_INTPMR_SWAP;
	} else {
		CLASSD->CLASSD_INTPMR &= ~CLASSD_INTPMR_SWAP;
	}
}

void classd_enable_mono(enum _classd_mono mono_mode)
{
	_set_mono_bits(true, mono_mode, &CLASSD->CLASSD_INTPMR);
}

void classd_disable_mono(void)
{
	_set_mono_bits(false, CLASSD_MONO_MIXED, &CLASSD->CLASSD_INTPMR);
}

void classd_set_equalizer(enum _classd_eqcfg eqcfg)
{
	_set_eqcfg_bits(eqcfg, &CLASSD->CLASSD_INTPMR);
}

void classd_enable_channels(bool left, bool right)
{
	uint32_t bits = 0;
	if (left)
		bits |= CLASSD_MR_LEN;
	if (right)
		bits |= CLASSD_MR_REN;
	CLASSD->CLASSD_MR |= bits;
}

void classd_disable_channels(bool left, bool right)
{
	uint32_t bits = 0;
	if (left)
		bits |= CLASSD_MR_LEN;
	if (right)
		bits |= CLASSD_MR_REN;
	CLASSD->CLASSD_MR &= ~bits;
}

void classd_set_left_attenuation(uint8_t attn)
{
	if (attn < 1 || attn > 0x3f)
		return;

	uint32_t intpmr = CLASSD->CLASSD_INTPMR & ~CLASSD_INTPMR_ATTL_Msk;
	CLASSD->CLASSD_INTPMR = intpmr | CLASSD_INTPMR_ATTL(attn);
}

void classd_set_right_attenuation(uint8_t attn)
{
	if (attn < 1 || attn > 0x3f)
		return;

	uint32_t intpmr = CLASSD->CLASSD_INTPMR & ~CLASSD_INTPMR_ATTR_Msk;
	CLASSD->CLASSD_INTPMR = intpmr | CLASSD_INTPMR_ATTR(attn);
}

void classd_volume_mute(bool left, bool right)
{
	uint32_t bits = 0;
	if (left)
		bits |= CLASSD_MR_LMUTE;
	if (right)
		bits |= CLASSD_MR_RMUTE;
	CLASSD->CLASSD_MR |= bits;
}

void classd_volume_unmute(bool left, bool right)
{
	uint32_t bits = 0;
	if (left)
		bits |= CLASSD_MR_LMUTE;
	if (right)
		bits |= CLASSD_MR_RMUTE;
	CLASSD->CLASSD_MR &= ~bits;
}

