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

#ifndef MATRIX_HEADER_
#define MATRIX_HEADER_

#include "chip.h"
#include <stdint.h>


/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

#define MATRIX_AREA_4K     (0x0u)  /* 0x1000 */
#define MATRIX_AREA_8K     (0x1u)  /* 0x2000 */
#define MATRIX_AREA_16K    (0x2u)  /* 0x4000 */
#define MATRIX_AREA_32K    (0x3u)  /* 0x8000 */
#define MATRIX_AREA_64K    (0x4u)  /* 0x10000 */
#define MATRIX_AREA_128K   (0x5u)  /* 0x20000 */
#define MATRIX_AREA_256K   (0x6u)  /* 0x40000 */
#define MATRIX_AREA_512K   (0x7u)  /* 0x80000 */
#define MATRIX_AREA_1M     (0x8u)  /* 0x100000 */
#define MATRIX_AREA_2M     (0x9u)  /* 0x200000 */
#define MATRIX_AREA_4M     (0xAu)  /* 0x400000 */
#define MATRIX_AREA_8M     (0xBu)  /* 0x800000 */
#define MATRIX_AREA_16M    (0xCu)  /* 0x1000000 */
#define MATRIX_AREA_32M    (0xDu)  /* 0x2000000 */
#define MATRIX_AREA_64M    (0xEu)  /* 0x4000000 */
#define MATRIX_AREA_128M   (0xFu)  /* 0x8000000 */

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

#ifdef __cplusplus
extern "C" {
#endif

extern void matrix_configure_slave_sec(Matrix* mtx, uint8_t slave_id,
				       uint8_t sel_mask, uint8_t read_mask,
				       uint8_t write_mask);

extern void matrix_set_slave_split_addr(Matrix* mtx, uint8_t slave_id,
					uint8_t area, uint8_t mask);

extern void matrix_set_slave_region_size(Matrix* mtx, uint8_t slave_id,
					 uint8_t area, uint8_t mask);

extern uint8_t matrix_is_peripheral_secured(Matrix* mtx, uint32_t periph_id);

extern void matrix_remove_write_protection(Matrix* mtx);

extern void matrix_remap_rom(void);

extern void matrix_remap_ram(void);

#ifdef __cplusplus
}
#endif

#endif /* MATRIX_HEADER_ */
