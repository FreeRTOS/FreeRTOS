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

/** \file */

/*------------------------------------------------------------------------------
 *         Header
 *------------------------------------------------------------------------------*/

#include "board.h"

#include "rand.h"

/*------------------------------------------------------------------------------
 *         Global Variables
 *------------------------------------------------------------------------------*/

static uint32_t _dwRandNext = 1;

/*------------------------------------------------------------------------------
 *         Exported Functions
 *------------------------------------------------------------------------------*/

/**
 *  Initialize the seed for rand generator.
 *
 *  \param dwSeed rand initiation seed
 */
void srand(uint32_t dwSeed)
{
	_dwRandNext = dwSeed;
}

/**
 *  Return a random number, maxinum assumed to be 65536
 */
uint32_t rand(void)
{
	_dwRandNext = _dwRandNext * 1103515245 + 12345;

	return (uint32_t) (_dwRandNext / 131072) % 65536;
}
