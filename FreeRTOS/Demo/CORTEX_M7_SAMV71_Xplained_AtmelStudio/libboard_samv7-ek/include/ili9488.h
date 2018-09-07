/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
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
 * Interface of ILI9488 driver.
 *
 */

#ifndef _ILI9488_H_
#define _ILI9488_H_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"

#include <stdint.h>


/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

#define ILI9488_SPIMODE        0
#define ILI9488_EBIMODE        1

/* ILI9325 ID code */
#define ILI9488_DEVICE_CODE    0x9488

#define ILI9488_LCD_WIDTH       320
#define ILI9488_LCD_HEIGHT      480
#define ILI9488_SELF_TEST_OK    0xC0

/* EBI chip select for LCD */
#define SMC_EBI_LCD_CS          3

/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/
typedef enum{
	 AccessInst = 0,
	 AccessRead,
	 AccessWrite
}AccessIli_t;

typedef union _union_type
{
	uint32_t value;
		struct{
			uint8_t byte_8;
			uint8_t byte_l6;
			uint8_t byte_24;
			uint8_t byte_32;
		}byte;
		struct{
			uint16_t half_word_l;
			uint16_t half_word_h;
			}half_word;
	}union_type;
typedef volatile uint8_t REG8;

typedef uint32_t LcdColor_t;

/*----------------------------------------------------------------------------
 *        Marcos
 *----------------------------------------------------------------------------*/
/* Pixel cache used to speed up communication */
#define LCD_DATA_CACHE_SIZE         BOARD_LCD_WIDTH

/*----------------------------------------------------------------------------
 *        Function Marcos
 *----------------------------------------------------------------------------*/
#define get_0b_to_8b(x)             (((union_type*)&(x))->byte.byte_8)
#define get_8b_to_16b(x)            (((union_type*)&(x))->byte.byte_l6)
#define get_16b_to_24b(x)           (((union_type*)&(x))->byte.byte_24)
#define get_24b_to_32b(x)           (((union_type*)&(x))->byte.byte_32)

#endif /* #ifndef ILI9488 */
