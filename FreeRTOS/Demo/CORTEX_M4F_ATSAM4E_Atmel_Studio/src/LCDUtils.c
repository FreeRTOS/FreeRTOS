/**
 * gfx_draw_bmpfile() is provided by and copyright to Atmel Corporation with the
 * following usage restrictions:
 *
 * Copyright (c) 2013 Atmel Corporation. All rights reserved.
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
 */

/* Standard includes. */
#include <stdint.h>

/* Library includes. */
#include <asf.h>

/* Bitmap. */
#include "logo_atmel.h"

/* Chip select number to be set for LCD. */
#define ILI93XX_LCD_CS  1

/*
 * Initialise the LCD and output a bitmap.
 */
void vInitialiseLCD( void );

/*
 * Output a bitmap to the LCD.
 */
static void gfx_draw_bmpfile( const uint8_t *bmpImage );

/*-----------------------------------------------------------*/

COMPILER_PACK_SET( 1 )
struct bmpfile_header {
	/** signature, must be 4D42 hex */
	uint16_t type;
	/** size of BMP file in bytes (unreliable) */
	uint32_t file_size;
	/** reserved, must be zero */
	uint16_t reserved1;
	/** reserved, must be zero */
	uint16_t reserved2;
	/** offset to start of image data in bytes */
	uint32_t offset;
	/** size of BITMAPINFOHEADER structure, must be 40 */
	uint32_t header_size;
	/** image width in pixels */
	uint32_t width;
	/** image height in pixels */
	uint32_t height;
	/** number of planes in the image, must be 1 */
	uint16_t planes;
	/** number of bits per pixel (1, 4, 8, 16, 24, 32) */
	uint16_t bits;
	/** compression type (0=none, 1=RLE-8, 2=RLE-4) */
	uint32_t compression;
	/** size of image data in bytes (including padding) */
	uint32_t inage_size;
	/** horizontal resolution in pixels per meter */
	uint32_t h_resolution;
	/** vertical resolution in pixels per meter */
	uint32_t v_resolution;
	/** number of colors in image, or zero */
	uint32_t colours;
	/** number of important colors, or zero */
	uint32_t important_colors;
};
COMPILER_PACK_RESET()

void vInitialiseLCD( void )
{
struct ili93xx_opt_t g_ili93xx_display_opt;

	/* Configure SMC interface for Lcd */
	smc_set_setup_timing( SMC, ILI93XX_LCD_CS, SMC_SETUP_NWE_SETUP( 2 ) | SMC_SETUP_NCS_WR_SETUP( 2 ) | SMC_SETUP_NRD_SETUP( 2 ) | SMC_SETUP_NCS_RD_SETUP( 2 ) );
	smc_set_pulse_timing( SMC, ILI93XX_LCD_CS, SMC_PULSE_NWE_PULSE( 4 )	| SMC_PULSE_NCS_WR_PULSE( 4 ) | SMC_PULSE_NRD_PULSE( 10 )| SMC_PULSE_NCS_RD_PULSE( 10 ) );
	smc_set_cycle_timing( SMC, ILI93XX_LCD_CS, SMC_CYCLE_NWE_CYCLE( 10 )| SMC_CYCLE_NRD_CYCLE( 22 ) );
	smc_set_mode( SMC, ILI93XX_LCD_CS, SMC_MODE_READ_MODE | SMC_MODE_WRITE_MODE );

	/* Initialise the LCD. */
	g_ili93xx_display_opt.ul_width = ILI93XX_LCD_WIDTH;
	g_ili93xx_display_opt.ul_height = ILI93XX_LCD_HEIGHT;
	g_ili93xx_display_opt.foreground_color = COLOR_BLACK;
	g_ili93xx_display_opt.background_color = COLOR_WHITE;
	ili93xx_init( &g_ili93xx_display_opt );

	/* Set backlight level */
	aat31xx_set_backlight(AAT31XX_AVG_BACKLIGHT_LEVEL);

	/* Turn on LCD */
	ili93xx_display_on();

	/* Clear. */
	ili93xx_set_foreground_color( COLOR_WHITE );
	ili93xx_draw_filled_rectangle( 0, 0, ILI93XX_LCD_WIDTH, ILI93XX_LCD_HEIGHT );

	/* Draw logos. */
	ili93xx_set_cursor_position( 0,0 );
	gfx_draw_bmpfile( logo_atmel_bmp );

	/* Set foreground colour ready to write text. */
	ili93xx_set_foreground_color( COLOR_BLACK );
}
/*-----------------------------------------------------------*/

static void gfx_draw_bmpfile( const uint8_t *bmpImage )
{
	struct bmpfile_header *bmp_header;
	uint32_t length;
	uint32_t i = 0;
	uint32_t offset;
	uint16_t j;

	bmp_header = (struct bmpfile_header*) bmpImage;
	length = bmp_header->height * bmp_header->width * 3;
	offset = sizeof(struct bmpfile_header);

	if (ili93xx_device_type() == DEVICE_TYPE_ILI9325) {

		ili93xx_set_cursor_position(0, 0);

		/** Prepare to write in GRAM */
		LCD_IR(0);
		LCD_IR(ILI9325_GRAM_DATA_REG);
		for (i = offset; i < length; i += 3) {
			/** Invert red and blue. */
			LCD_WD(bmpImage[i + 2]);
			LCD_WD(bmpImage[i + 1]);
			LCD_WD(bmpImage[i]);
		}
		} else if (ili93xx_device_type() == DEVICE_TYPE_ILI9341) {
		ili93xx_set_window(0, 0, bmp_header->width - 15, bmp_header->height);
		/** memory write command (R2Ch)*/
		LCD_IR(ILI9341_CMD_MEMORY_WRITE);
		LCD_IR(ILI9341_CMD_WRITE_MEMORY_CONTINUE);

		/** the original image is mirrored */
		for (i= bmp_header->height - 1; i * bmp_header->width * 3 > offset;
		i -=1) {
			for (j = 45; j < bmp_header->width * 3; j += 3) {
				LCD_WD(bmpImage[i * bmp_header->width * 3 + j + 2]);
				LCD_WD(bmpImage[i * bmp_header->width * 3 + j + 1]);
				LCD_WD(bmpImage[i * bmp_header->width * 3 + j]);
			}
		}
	}
}
