/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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
 *  Implements DBG utility that uses DBGU and System tick to get byte or binary
 *  stream from DBGU console.
 */

#ifndef _DBG_UTIL_
#define _DBG_UTIL_

/*----------------------------------------------------------------------------
 *         Headers
 *----------------------------------------------------------------------------*/

#include <stdint.h>

/*----------------------------------------------------------------------------
 *         Definitions
 *----------------------------------------------------------------------------*/

/*----------------------------------------------------------------------------
 *         Global functions
 *----------------------------------------------------------------------------*/

extern uint8_t DbgReceiveByte(uint8_t * pByte, uint32_t timeOut);

extern uint32_t DbgReceiveBinary(uint8_t start,
				 uint32_t address, uint32_t maxSize);

extern uint32_t DbgReceive1KXModem(uint8_t * pktBuffer,
				   uint32_t address, uint32_t maxSize);

#endif				/* _DBG_UTIL_ */
