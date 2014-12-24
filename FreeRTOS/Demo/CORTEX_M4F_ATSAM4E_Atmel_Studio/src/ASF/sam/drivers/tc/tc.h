/**
 * \file
 *
 * \brief Timer Counter (TC) driver for SAM.
 *
 * Copyright (c) 2011-2013 Atmel Corporation. All rights reserved.
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

#ifndef TC_H_INCLUDED
#define TC_H_INCLUDED

#include "compiler.h"

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/// @endcond

void tc_init(Tc *p_tc, uint32_t ul_Channel, uint32_t ul_Mode);
void tc_sync_trigger(Tc *p_tc);
void tc_set_block_mode(Tc *p_tc, uint32_t ul_blockmode);

#if (!SAM3U)
uint32_t tc_init_2bit_gray(Tc *p_tc, uint32_t ul_channel,
		uint32_t ul_steppermode);
#endif

void tc_start(Tc *p_tc, uint32_t ul_channel);
void tc_stop(Tc *p_tc, uint32_t ul_channel);

uint32_t tc_read_cv(Tc *p_tc, uint32_t ul_channel);
uint32_t tc_read_ra(Tc *p_tc, uint32_t ul_channel);
uint32_t tc_read_rb(Tc *p_tc, uint32_t ul_channel);
uint32_t tc_read_rc(Tc *p_tc, uint32_t ul_channel);

void tc_write_ra(Tc *p_tc, uint32_t ul_channel,
		uint32_t ul_value);
void tc_write_rb(Tc *p_tc, uint32_t ul_channel,
		uint32_t ul_value);
void tc_write_rc(Tc *p_tc, uint32_t ul_channel,
		uint32_t ul_value);

uint32_t tc_find_mck_divisor(uint32_t ul_freq, uint32_t ul_mck,
		uint32_t *p_uldiv, uint32_t *ul_tcclks, uint32_t ul_boardmck);
void tc_enable_interrupt(Tc *p_tc, uint32_t ul_channel,
		uint32_t ul_sources);
void tc_disable_interrupt(Tc *p_tc, uint32_t ul_channel,
		uint32_t ul_sources);
uint32_t tc_get_interrupt_mask(Tc *p_tc, uint32_t ul_channel);
uint32_t tc_get_status(Tc *p_tc, uint32_t ul_channel);
#if (!SAM4L)
void tc_enable_qdec_interrupt(Tc *p_tc, uint32_t ul_sources);
void tc_disable_qdec_interrupt(Tc *p_tc, uint32_t ul_sources);
uint32_t tc_get_qdec_interrupt_mask(Tc *p_tc);
uint32_t tc_get_qdec_interrupt_status(Tc *p_tc);
#endif

#if (!SAM3U)
void tc_set_writeprotect(Tc *p_tc, uint32_t ul_enable);
#endif

#if SAM4L
uint32_t tc_get_feature(Tc *p_tc);
uint32_t tc_get_version(Tc *p_tc);

#endif

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/// @endcond

#endif /* TC_H_INCLUDED */
