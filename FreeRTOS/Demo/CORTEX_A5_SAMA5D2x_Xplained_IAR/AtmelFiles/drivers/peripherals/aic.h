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
 *  Methods and definitions for configuring interrupts.
 *
 *  \section Usage
  *  -# Enable or disable interrupt generation of a particular source with
 *    IRQ_EnableIT and IRQ_DisableIT.
 */

#ifndef AIC_H
#define AIC_H

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "chip.h"

#include <stdint.h>

typedef void(*aic_handler_t)(void);

/*------------------------------------------------------------------------------
 *         Global functions
 *------------------------------------------------------------------------------*/

#ifdef __cplusplus
extern "C" {
#endif

extern void aic_initialize(void);
extern void aic_enable(uint32_t source);
extern void aic_disable(uint32_t source);
extern void aic_configure(uint32_t source, uint8_t mode);
extern void aic_set_source_vector(uint32_t source, void (*handler)(void));
extern void aic_set_spurious_vector(void (*handler)(void));
extern void aic_set_or_clear(uint32_t source, uint8_t set);
extern void aic_end_interrupt(Aic * aic);
extern uint32_t aic_debug_config(Aic * aic, uint8_t protect, uint8_t mask);
extern void aic_write_protection(Aic * aic, uint32_t enable);
extern uint32_t aic_violation_occured(Aic * aic, uint32_t * pViolationSource);

#ifdef __cplusplus
}
#endif

#endif //#ifndef AIC_H
