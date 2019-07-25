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

#ifndef _CONSOLE_H_
#define _CONSOLE_H_

/*-----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include <stdint.h>

#define DRV_UART     (1)
#define DRV_USART    (2)
#define DRV_DBGU     (3)
//#define DRV_FLEXCOM  (4)

struct _console {
	void* addr;
	void (*init)(void*, uint32_t, uint32_t);
	void (*put_char)(void*, uint8_t);
	uint32_t (*get_char)(void*);
	uint32_t (*is_rx_ready)(void*);
	void (*enable_interrupts)(void*, uint32_t);
};

/* ----------------------------------------------------------------------------
 *         Global function
 * ---------------------------------------------------------------------------*/

extern void console_configure(uint32_t baudrate);
extern void console_put_char(uint8_t uc);
extern uint32_t console_get_char(void);
extern uint32_t console_is_rx_ready(void);
extern void console_enable_interrupts(uint32_t mask);
extern void console_dump_frame(uint8_t * pframe, uint32_t size);
extern void console_dump_memory(uint8_t * pbuffer, uint32_t size,
				uint32_t address);
extern uint32_t console_get_integer(uint32_t * pvalue);
extern uint32_t console_get_integer_min_max(uint32_t * pvalue, uint32_t min,
					    uint32_t max);
extern uint32_t console_get_hexa_32(uint32_t * pvalue);

extern void console_echo(uint8_t c);
extern void console_clear_screen(void);
extern void console_reset_cursor(void);

#endif	/* _CONSOLE_H_ */
