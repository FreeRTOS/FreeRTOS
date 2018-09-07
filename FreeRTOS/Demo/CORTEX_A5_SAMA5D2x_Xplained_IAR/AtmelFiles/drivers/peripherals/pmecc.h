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

#ifndef PMECC_H
#define PMECC_H

/*----------------------------------------------------------------------- */
/*         Definition                                                     */
/*----------------------------------------------------------------------- */

/** Start address of ECC cvalue in spare zone, this must not be 0 since Bad block tag are at 0. */
#define PMECC_ECC_DEFAULT_START_ADDR   0x02

/*------------------------------------------------------------------------------ */
/*         Exported functions                                                    */
/*------------------------------------------------------------------------------ */

extern uint8_t pmecc_initialize(uint8_t sector_size,
		uint8_t ecc_errors_per_sector,
		uint32_t page_data_size,
		uint32_t page_spare_size,
		uint16_t ecc_offset_in_spare,
		uint8_t spare_protected);

extern uint32_t pmecc_get_page_size(void);

extern uint32_t pmecc_get_ecc_bytes(void);

extern uint32_t pmecc_get_ecc_start_address(void);

extern uint32_t pmecc_get_ecc_end_address(void);

extern uint32_t pmecc_correction(uint32_t pmecc_status, uint32_t page_buffer);

extern void build_gf(uint32_t mm, int32_t *index_of, int32_t *alpha_to);

extern void pmecc_disable(void);

#endif

