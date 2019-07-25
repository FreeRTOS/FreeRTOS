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

#ifndef _CLASSD_H
#define _CLASSD_H

/*---------------------------------------------------------------------------
 *         Includes
 *---------------------------------------------------------------------------*/

#include <stdbool.h>
#include <stdint.h>

/*---------------------------------------------------------------------------
 *         Types
 *---------------------------------------------------------------------------*/

enum _classd_mode
{
	CLASSD_OUTPUT_SINGLE_ENDED,
	CLASSD_OUTPUT_DIFFERENTIAL,
	CLASSD_OUTPUT_HALF_BRIDGE,
	CLASSD_OUTPUT_FULL_BRIDGE,
};

enum _classd_non_ovr
{
	CLASSD_NONOVR_5NS,
	CLASSD_NONOVR_10NS,
	CLASSD_NONOVR_15NS,
	CLASSD_NONOVR_20NS,
};

enum _classd_eqcfg
{
	CLASSD_EQCFG_FLAT,
	CLASSD_EQCFG_BBOOST12,
	CLASSD_EQCFG_BBOOST6,
	CLASSD_EQCFG_BCUT12,
	CLASSD_EQCFG_BCUT6,
	CLASSD_EQCFG_MBOOST3,
	CLASSD_EQCFG_MBOOST8,
	CLASSD_EQCFG_MCUT3,
	CLASSD_EQCFG_MCUT8,
	CLASSD_EQCFG_TBOOST12,
	CLASSD_EQCFG_TBOOST6,
	CLASSD_EQCFG_TCUT12,
	CLASSD_EQCFG_TCUT6,
};

enum _classd_mono
{
	CLASSD_MONO_MIXED,
	CLASSD_MONO_SAT,
	CLASSD_MONO_LEFT,
	CLASSD_MONO_RIGHT,
};

struct _classd_desc
{
	uint32_t             sample_rate;
	enum _classd_mode    mode;
	enum _classd_non_ovr non_ovr;
	bool                 swap_channels;
	bool                 mono;
	enum _classd_mono    mono_mode;
	bool                 left_enable;
	bool                 right_enable;
};

/*---------------------------------------------------------------------------
 *         Exported functions
 *---------------------------------------------------------------------------*/

extern bool classd_configure(struct _classd_desc *desc);

extern void classd_disable(void);

extern void classd_swap_channels(bool swap);

extern void classd_enable_mono(enum _classd_mono mono_mode);

extern void classd_disable_mono(void);

extern void classd_set_equalizer(enum _classd_eqcfg eqcfg);

extern void classd_enable_channels(bool left, bool right);

extern void classd_disable_channels(bool left, bool right);

extern void classd_set_left_attenuation(uint8_t attn);

extern void classd_set_right_attenuation(uint8_t attn);

extern void classd_volume_mute(bool left, bool right);

extern void classd_volume_unmute(bool left, bool right);

#endif /* _CLASSD_H */
