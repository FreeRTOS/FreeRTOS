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
 * \file
 *
 * \par Purpose
 *
 * This module provides several definitions and methods for using an USART
 * peripheral in LIN mode.
 *
 */

#ifndef _USART_LIN_
#define _USART_LIN_

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "chip.h"

/*------------------------------------------------------------------------------
 *         Definitions
 *------------------------------------------------------------------------------*/

#ifdef __cplusplus
extern "C" {
#endif

/*------------------------------------------------------------------------------*/
/*         Exported functions                                                   */
/*------------------------------------------------------------------------------*/

extern void usart_lin_reset_status_bits(Usart *usart);
extern uint32_t usart_lin_get_status_register(Usart *usart);
extern void usart_lin_set_mode_master_or_slave (Usart* usart, uint32_t mode_master_or_slave);
extern void usart_lin_abort_tx(Usart *usart);
extern void usart_lin_send_wakeup_signal(Usart *usart);
extern void usart_lin_set_node_action(Usart *usart, uint8_t action);
extern void usart_lin_disable_parity(Usart *usart);
extern void usart_lin_enable_parity(Usart *usart);
extern void usart_lin_disable_checksum(Usart *usart);
extern void usart_lin_enable_checksum(Usart *usart);
extern void usart_lin_set_checksum_type(Usart *usart, uint8_t type);
extern void usart_lin_set_data_len_mode(Usart *usart, uint8_t mode);
extern void usart_lin_disable_frame_slot(Usart *usart);
extern void usart_lin_enable_frame_slot(Usart *usart);
extern void usart_lin_set_wakeup_signal_type(Usart *usart, uint8_t type);
extern void usart_lin_set_frame_data_len(Usart *usart, uint8_t len);
extern void usart_lin_disable_dmac_mode(Usart *usart);
extern void usart_lin_enable_dmac_mode(Usart *usart);
extern void usart_lin_set_tx_identifier(Usart *usart, uint8_t id);
extern uint8_t usart_lin_read_identifier(Usart *usart);
extern uint8_t usart_lin_get_data_length(Usart *usart);


#ifdef CONFIG_HAVE_USART_FIFO
extern uint32_t usart_lin_read_stream(Usart *usart, uint8_t *stream, uint32_t len);
extern uint32_t usart_lin_write_stream(Usart *usart, uint8_t *stream, uint32_t len);
#endif

#ifdef __cplusplus
}
#endif

#endif	/* #ifndef _USART_LIN_ */
