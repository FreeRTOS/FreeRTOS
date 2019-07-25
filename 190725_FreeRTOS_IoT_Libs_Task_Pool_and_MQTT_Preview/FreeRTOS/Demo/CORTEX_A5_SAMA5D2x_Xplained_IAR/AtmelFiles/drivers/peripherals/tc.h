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
 *  \file
 *
 *  \section Purpose
 *
 *  Interface for configuring and using Timer Counter (TC) peripherals.
 *
 *  \section Usage
 *  -# Optionally, use tc_find_mck_divisor() to let the program find the best
 *     TCCLKS field value automatically.
 *  -# Configure a Timer Counter in the desired mode using tc_configure().
 *  -# Start or stop the timer clock using tc_start() and tc_stop().
 */

#ifndef _TC_
#define _TC_

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "chip.h"

#include <stdint.h>

/*------------------------------------------------------------------------------
 *         Global functions
 *------------------------------------------------------------------------------*/

#ifdef __cplusplus
extern "C" {
#endif

extern void tc_configure (Tc* pTc, uint32_t channel, uint32_t mode);
extern void tc_start (Tc * pTc, uint32_t channel);
extern void tc_stop (Tc * pTc, uint32_t channel);
extern void tc_enable_it(Tc* tc, uint32_t channel, uint32_t mask);
extern uint32_t tc_find_mck_divisor (uint32_t freq, uint32_t* div, uint32_t * tc_clks);
extern uint32_t tc_get_status(Tc* tc, uint32_t channel_num);
extern void tc_trigger_on_freq(Tc* tc, uint32_t channel_num, uint32_t freq);

#ifdef __cplusplus
}
#endif
#endif				/* #ifndef _TC_ */
