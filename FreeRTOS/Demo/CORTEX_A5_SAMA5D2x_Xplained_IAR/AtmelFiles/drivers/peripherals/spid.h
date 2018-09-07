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


#ifndef SPID_HEADER__
#define SPID_HEADER__

/*------------------------------------------------------------------------------
 *        Header
 *----------------------------------------------------------------------------*/

#include <stdint.h>
#include "mutex.h"
#include "io.h"

/*------------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

#define SPID_SUCCESS         (0)
#define SPID_INVALID_ID      (1)
#define SPID_INVALID_BITRATE (2)
#define SPID_ERROR_LOCK      (3)

#define SPID_NO_CALLBACK     ((spid_callback_t)0)

struct _spi_desc;

typedef void (*spid_callback_t)(struct _spi_desc* spid, void* args);

enum _spid_trans_mode
{
	SPID_MODE_POLLING,
	SPID_MODE_FIFO,
	SPID_MODE_DMA
};

struct _spi_desc
{
	Spi*            addr;
	uint32_t        bitrate;
	uint32_t        attributes;
	uint8_t         dlybs;
	uint8_t         dlybct;
	uint8_t         chip_select;
	uint8_t         spi_mode;
	uint8_t         transfert_mode;
	/* implicit internal padding is mandatory here */
	spid_callback_t callback;
	void*           cb_args;
	mutex_t         mutex;
	uint32_t        region_start;
	uint32_t        region_end;
};

/*------------------------------------------------------------------------------
 *        Functions
 *----------------------------------------------------------------------------*/

extern void spid_configure(struct _spi_desc* desc);

extern void spid_begin_transfert(struct _spi_desc* desc);

extern uint32_t spid_transfert(struct _spi_desc* desc, struct _buffer* rx,
			       struct _buffer* tx, spid_callback_t cb,
			       void* user_args);
extern void spid_finish_transfert(struct _spi_desc* desc);
extern void spid_finish_transfert_callback(struct _spi_desc* desc,
					   void* user_arg);
extern void spid_close(const struct _spi_desc* desc);

extern uint32_t spid_is_busy(const struct _spi_desc* desc);
extern void spid_wait_transfert(const struct _spi_desc* desc);

#endif /* SPID_HEADER__ */
