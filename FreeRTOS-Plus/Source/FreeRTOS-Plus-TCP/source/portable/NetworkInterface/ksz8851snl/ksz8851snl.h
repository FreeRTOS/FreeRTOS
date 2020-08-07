/**
 *
 * \file
 *
 * \brief KS8851SNL driver for SAM.
 *
 * Copyright (c) 2013-2015 Atmel Corporation. All rights reserved.
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
/*
 * Support and FAQ: visit <a href="http://www.atmel.com/design-support/">Atmel Support</a>
 */

#ifndef KSZ8851SNL_H_INCLUDED
#define KSZ8851SNL_H_INCLUDED

#include "gpio.h"

void configure_intn(void (*p_handler) (uint32_t, uint32_t));
void ksz8851_reg_setbits(uint16_t reg, uint16_t bits_to_set);
void ksz8851_reg_clrbits(uint16_t reg, uint16_t bits_to_clr);
void ksz8851_fifo_read(uint8_t *buf, uint32_t len);
void ksz8851_fifo_write(uint8_t *buf, uint32_t ulActualLength, uint32_t ulFIFOLength);
void ksz8851_fifo_dummy(uint32_t len);
void ksz8851_reg_write(uint16_t reg, uint16_t wrdata);
uint16_t ksz8851_reg_read(uint16_t reg);
uint32_t ksz8851snl_init(void);
uint32_t ksz8851snl_reinit(void);

uint32_t ksz8851snl_reset_rx( void );
uint32_t ksz8851snl_reset_tx( void );

#endif /* KSZ8851SNL_H_INCLUDED */
