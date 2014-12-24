/**
 * \file
 *
 * \brief API driver for ILI93XX TFT display component.
 *
 * Copyright (c) 2013 Atmel Corporation. All rights reserved.
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

/**
 * \defgroup ili93xx_display_group Display - ILI93XX Controller
 *
 * Low-level driver for the ILI93XX LCD controller. This driver provides access
 * to the main features of the ILI93XX controller.
 * Now ILI9325 and ILI9341 are supported.
 *
 * \{
 */

#include <string.h>
#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include "ili93xx.h"
#include "ili9341_regs.h"
#include "ili9325_regs.h"

/** Device type*/
static uint8_t g_uc_device_type = 0;

/** Pixel cache used to speed up communication */
#define LCD_DATA_CACHE_SIZE ILI93XX_LCD_WIDTH

/** LCD X-axis and Y-axis length */
static uint32_t g_ul_lcd_x_length = ILI93XX_LCD_WIDTH;
static uint32_t g_ul_lcd_y_length = ILI93XX_LCD_HEIGHT;

static ili93xx_color_t g_ul_pixel_cache[LCD_DATA_CACHE_SIZE];

static volatile ili93xx_coord_t limit_start_x, limit_start_y;
static volatile ili93xx_coord_t limit_end_x, limit_end_y;

/** Global variable describing the font size used by the driver */
const struct ili93xx_font gfont = {10, 14};

/**
 * Character set table for font 10x14
 * Coding format:
 * Char height is 14 bits, which is coded using 2 bytes per column
 * (2 unused bits).
 * Char width is 10 bits.
 */
const uint8_t p_uc_charset10x14[] = {
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xCC,
	0xFF, 0xCC, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0xF0, 0x00, 0xF0, 0x00, 0x00, 0x00,
	0x00, 0x00, 0xF0, 0x00, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x0C, 0xC0, 0x0C, 0xC0, 0xFF, 0xFC, 0xFF, 0xFC, 0x0C, 0xC0,
	0x0C, 0xC0, 0xFF, 0xFC, 0xFF, 0xFC, 0x0C, 0xC0, 0x0C, 0xC0,
	0x0C, 0x60, 0x1E, 0x70, 0x3F, 0x30, 0x33, 0x30, 0xFF, 0xFC,
	0xFF, 0xFC, 0x33, 0x30, 0x33, 0xF0, 0x39, 0xE0, 0x18, 0xC0,
	0x60, 0x00, 0xF0, 0x0C, 0xF0, 0x3C, 0x60, 0xF0, 0x03, 0xC0,
	0x0F, 0x00, 0x3C, 0x18, 0xF0, 0x3C, 0xC0, 0x3C, 0x00, 0x18,
	0x3C, 0xF0, 0x7F, 0xF8, 0xC3, 0x1C, 0xC7, 0x8C, 0xCF, 0xCC,
	0xDC, 0xEC, 0x78, 0x78, 0x30, 0x30, 0x00, 0xFC, 0x00, 0xCC,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x44, 0x00, 0xEC, 0x00,
	0xF8, 0x00, 0x70, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x0F, 0xC0, 0x3F, 0xF0, 0x78, 0x78,
	0x60, 0x18, 0xC0, 0x0C, 0xC0, 0x0C, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0xC0, 0x0C, 0xC0, 0x0C, 0x60, 0x18,
	0x78, 0x78, 0x3F, 0xF0, 0x0F, 0xC0, 0x00, 0x00, 0x00, 0x00,
	0x0C, 0x60, 0x0E, 0xE0, 0x07, 0xC0, 0x03, 0x80, 0x3F, 0xF8,
	0x3F, 0xF8, 0x03, 0x80, 0x07, 0xC0, 0x0E, 0xE0, 0x0C, 0x60,
	0x03, 0x00, 0x03, 0x00, 0x03, 0x00, 0x03, 0x00, 0x3F, 0xF0,
	0x3F, 0xF0, 0x03, 0x00, 0x03, 0x00, 0x03, 0x00, 0x03, 0x00,
	0x00, 0x44, 0x00, 0xEC, 0x00, 0xF8, 0x00, 0x70, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x03, 0x00, 0x03, 0x00, 0x03, 0x00, 0x03, 0x00, 0x03, 0x00,
	0x03, 0x00, 0x03, 0x00, 0x03, 0x00, 0x03, 0x00, 0x03, 0x00,
	0x00, 0x18, 0x00, 0x3C, 0x00, 0x3C, 0x00, 0x18, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x0C, 0x00, 0x3C, 0x00, 0xF0, 0x03, 0xC0,
	0x0F, 0x00, 0x3C, 0x00, 0xF0, 0x00, 0xC0, 0x00, 0x00, 0x00,
	0x3F, 0xF0, 0x7F, 0xF8, 0xE0, 0xFC, 0xC1, 0xCC, 0xC3, 0x8C,
	0xC7, 0x0C, 0xCE, 0x0C, 0xFC, 0x1C, 0x7F, 0xF8, 0x3F, 0xF0,
	0x00, 0x00, 0x00, 0x00, 0x30, 0x0C, 0x70, 0x0C, 0xFF, 0xFC,
	0xFF, 0xFC, 0x00, 0x0C, 0x00, 0x0C, 0x00, 0x00, 0x00, 0x00,
	0x30, 0x0C, 0x70, 0x1C, 0xE0, 0x3C, 0xC0, 0x7C, 0xC0, 0xEC,
	0xC1, 0xCC, 0xC3, 0x8C, 0xE7, 0x0C, 0x7E, 0x0C, 0x3C, 0x0C,
	0x30, 0x30, 0x70, 0x38, 0xE0, 0x1C, 0xC0, 0x0C, 0xC0, 0x0C,
	0xC3, 0x0C, 0xC3, 0x0C, 0xE3, 0x1C, 0x7F, 0xF8, 0x3C, 0xF0,
	0x03, 0xC0, 0x07, 0xC0, 0x0E, 0xC0, 0x1C, 0xC0, 0x38, 0xC0,
	0x70, 0xC0, 0xFF, 0xFC, 0xFF, 0xFC, 0x00, 0xC0, 0x00, 0xC0,
	0xFC, 0x30, 0xFC, 0x38, 0xCC, 0x1C, 0xCC, 0x0C, 0xCC, 0x0C,
	0xCC, 0x0C, 0xCC, 0x0C, 0xCE, 0x1C, 0xC7, 0xF8, 0xC3, 0xF0,
	0x3F, 0xF0, 0x7F, 0xF8, 0xE3, 0x1C, 0xC3, 0x0C, 0xC3, 0x0C,
	0xC3, 0x0C, 0xC3, 0x0C, 0xE3, 0x9C, 0x71, 0xF8, 0x30, 0xF0,
	0xC0, 0x00, 0xC0, 0x00, 0xC0, 0x00, 0xC0, 0x00, 0xC3, 0xFC,
	0xC7, 0xFC, 0xCE, 0x00, 0xDC, 0x00, 0xF8, 0x00, 0xF0, 0x00,
	0x3C, 0xF0, 0x7F, 0xF8, 0xE7, 0x9C, 0xC3, 0x0C, 0xC3, 0x0C,
	0xC3, 0x0C, 0xC3, 0x0C, 0xE7, 0x9C, 0x7F, 0xF8, 0x3C, 0xF0,
	0x3C, 0x00, 0x7E, 0x00, 0xE7, 0x0C, 0xC3, 0x0C, 0xC3, 0x1C,
	0xC3, 0x38, 0xC3, 0x70, 0xE7, 0xE0, 0x7F, 0xC0, 0x3F, 0x80,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x18, 0x60, 0x3C, 0xF0,
	0x3C, 0xF0, 0x18, 0x60, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x18, 0x44, 0x3C, 0xEC,
	0x3C, 0xF8, 0x18, 0x70, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x03, 0x00, 0x07, 0x80, 0x0F, 0xC0, 0x1C, 0xE0,
	0x38, 0x70, 0x70, 0x38, 0xE0, 0x1C, 0xC0, 0x0C, 0x00, 0x00,
	0x0C, 0xC0, 0x0C, 0xC0, 0x0C, 0xC0, 0x0C, 0xC0, 0x0C, 0xC0,
	0x0C, 0xC0, 0x0C, 0xC0, 0x0C, 0xC0, 0x0C, 0xC0, 0x0C, 0xC0,
	0x00, 0x00, 0xC0, 0x0C, 0xE0, 0x1C, 0x70, 0x38, 0x38, 0x70,
	0x1C, 0xE0, 0x0F, 0xC0, 0x07, 0x80, 0x03, 0x00, 0x00, 0x00,
	0x30, 0x00, 0x70, 0x00, 0xE0, 0x00, 0xC0, 0x00, 0xC1, 0xEC,
	0xC3, 0xEC, 0xC3, 0x00, 0xE6, 0x00, 0x7E, 0x00, 0x3C, 0x00,
	0x30, 0xF0, 0x71, 0xF8, 0xE3, 0x9C, 0xC3, 0x0C, 0xC3, 0xFC,
	0xC3, 0xFC, 0xC0, 0x0C, 0xE0, 0x1C, 0x7F, 0xF8, 0x3F, 0xF0,
	0x3F, 0xFC, 0x7F, 0xFC, 0xE0, 0xC0, 0xC0, 0xC0, 0xC0, 0xC0,
	0xC0, 0xC0, 0xC0, 0xC0, 0xE0, 0xC0, 0x7F, 0xFC, 0x3F, 0xFC,
	0xFF, 0xFC, 0xFF, 0xFC, 0xC3, 0x0C, 0xC3, 0x0C, 0xC3, 0x0C,
	0xC3, 0x0C, 0xC3, 0x0C, 0xE7, 0x9C, 0x7F, 0xF8, 0x3C, 0xF0,
	0x3F, 0xF0, 0x7F, 0xF8, 0xE0, 0x1C, 0xC0, 0x0C, 0xC0, 0x0C,
	0xC0, 0x0C, 0xC0, 0x0C, 0xE0, 0x1C, 0x70, 0x38, 0x30, 0x30,
	0xFF, 0xFC, 0xFF, 0xFC, 0xC0, 0x0C, 0xC0, 0x0C, 0xC0, 0x0C,
	0xC0, 0x0C, 0xC0, 0x0C, 0xE0, 0x1C, 0x7F, 0xF8, 0x3F, 0xF0,
	0xFF, 0xFC, 0xFF, 0xFC, 0xC3, 0x0C, 0xC3, 0x0C, 0xC3, 0x0C,
	0xC3, 0x0C, 0xC3, 0x0C, 0xC3, 0x0C, 0xC0, 0x0C, 0xC0, 0x0C,
	0xFF, 0xFC, 0xFF, 0xFC, 0xC3, 0x00, 0xC3, 0x00, 0xC3, 0x00,
	0xC3, 0x00, 0xC3, 0x00, 0xC3, 0x00, 0xC0, 0x00, 0xC0, 0x00,
	0x3F, 0xF0, 0x7F, 0xF8, 0xE0, 0x1C, 0xC0, 0x0C, 0xC0, 0x0C,
	0xC3, 0x0C, 0xC3, 0x0C, 0xE3, 0x1C, 0x73, 0xF8, 0x33, 0xF0,
	0xFF, 0xFC, 0xFF, 0xFC, 0x03, 0x00, 0x03, 0x00, 0x03, 0x00,
	0x03, 0x00, 0x03, 0x00, 0x03, 0x00, 0xFF, 0xFC, 0xFF, 0xFC,
	0x00, 0x00, 0x00, 0x00, 0xC0, 0x0C, 0xC0, 0x0C, 0xFF, 0xFC,
	0xFF, 0xFC, 0xC0, 0x0C, 0xC0, 0x0C, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x30, 0x00, 0x38, 0xC0, 0x1C, 0xC0, 0x0C, 0xC0, 0x0C,
	0xC0, 0x1C, 0xFF, 0xF8, 0xFF, 0xF0, 0xC0, 0x00, 0xC0, 0x00,
	0xFF, 0xFC, 0xFF, 0xFC, 0x07, 0x80, 0x07, 0x80, 0x0F, 0xC0,
	0x1C, 0xE0, 0x38, 0x70, 0x70, 0x38, 0xE0, 0x1C, 0xC0, 0x0C,
	0xFF, 0xFC, 0xFF, 0xFC, 0x00, 0x0C, 0x00, 0x0C, 0x00, 0x0C,
	0x00, 0x0C, 0x00, 0x0C, 0x00, 0x0C, 0x00, 0x0C, 0x00, 0x0C,
	0xFF, 0xFC, 0xFF, 0xFC, 0x70, 0x00, 0x38, 0x00, 0x1F, 0x00,
	0x1F, 0x00, 0x38, 0x00, 0x70, 0x00, 0xFF, 0xFC, 0xFF, 0xFC,
	0xFF, 0xFC, 0xFF, 0xFC, 0x1C, 0x00, 0x0E, 0x00, 0x07, 0x00,
	0x03, 0x80, 0x01, 0xC0, 0x00, 0xE0, 0xFF, 0xFC, 0xFF, 0xFC,
	0x3F, 0xF0, 0x7F, 0xF8, 0xE0, 0x1C, 0xC0, 0x0C, 0xC0, 0x0C,
	0xC0, 0x0C, 0xC0, 0x0C, 0xE0, 0x1C, 0x7F, 0xF8, 0x3F, 0xF0,
	0xFF, 0xFC, 0xFF, 0xFC, 0xC3, 0x00, 0xC3, 0x00, 0xC3, 0x00,
	0xC3, 0x00, 0xC3, 0x00, 0xE7, 0x00, 0x7E, 0x00, 0x3C, 0x00,
	0x3F, 0xF0, 0x7F, 0xF8, 0xE0, 0x1C, 0xC0, 0x0C, 0xC0, 0xCC,
	0xC0, 0xEC, 0xC0, 0x7C, 0xE0, 0x38, 0x7F, 0xFC, 0x3F, 0xEC,
	0xFF, 0xFC, 0xFF, 0xFC, 0xC3, 0x00, 0xC3, 0x80, 0xC3, 0x80,
	0xC3, 0xC0, 0xC3, 0xC0, 0xE7, 0x70, 0x7E, 0x3C, 0x3C, 0x1C,
	0x3C, 0x18, 0x7E, 0x1C, 0xE7, 0x0C, 0xC3, 0x0C, 0xC3, 0x0C,
	0xC3, 0x0C, 0xC3, 0x0C, 0xC3, 0x9C, 0xE1, 0xF8, 0x60, 0xF0,
	0xC0, 0x00, 0xC0, 0x00, 0xC0, 0x00, 0xC0, 0x00, 0xFF, 0xFC,
	0xFF, 0xFC, 0xC0, 0x00, 0xC0, 0x00, 0xC0, 0x00, 0xC0, 0x00,
	0xFF, 0xF0, 0xFF, 0xF8, 0x00, 0x1C, 0x00, 0x0C, 0x00, 0x0C,
	0x00, 0x0C, 0x00, 0x0C, 0x00, 0x1C, 0xFF, 0xF8, 0xFF, 0xF0,
	0xFF, 0xC0, 0xFF, 0xE0, 0x00, 0x70, 0x00, 0x38, 0x00, 0x1C,
	0x00, 0x1C, 0x00, 0x38, 0x00, 0x70, 0xFF, 0xE0, 0xFF, 0xC0,
	0xFF, 0xF0, 0xFF, 0xF8, 0x00, 0x1C, 0x00, 0x3C, 0x00, 0xF8,
	0x00, 0xF8, 0x00, 0x3C, 0x00, 0x1C, 0xFF, 0xF8, 0xFF, 0xF0,
	0xF0, 0x3C, 0xF8, 0x7C, 0x1C, 0xE0, 0x0F, 0xC0, 0x07, 0x80,
	0x07, 0x80, 0x0F, 0xC0, 0x1C, 0xE0, 0xF8, 0x7C, 0xF0, 0x3C,
	0xFC, 0x00, 0xFE, 0x00, 0x07, 0x00, 0x03, 0x80, 0x01, 0xFC,
	0x01, 0xFC, 0x03, 0x80, 0x07, 0x00, 0xFE, 0x00, 0xFC, 0x00,
	0xC0, 0x3C, 0xC0, 0x7C, 0xC0, 0xEC, 0xC1, 0xCC, 0xC3, 0x8C,
	0xC7, 0x0C, 0xCE, 0x0C, 0xDC, 0x0C, 0xF8, 0x0C, 0xF0, 0x0C,
	0x00, 0x00, 0x00, 0x00, 0xFF, 0xFC, 0xFF, 0xFC, 0xC0, 0x0C,
	0xC0, 0x0C, 0xC0, 0x0C, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x30, 0x00, 0x30, 0x00, 0x0C, 0x00, 0x0C, 0x00, 0x03, 0x00,
	0x03, 0x00, 0x00, 0xC0, 0x00, 0xC0, 0x00, 0x30, 0x00, 0x30,
	0x00, 0x00, 0x00, 0x00, 0xC0, 0x0C, 0xC0, 0x0C, 0xC0, 0x0C,
	0xFF, 0xFC, 0xFF, 0xFC, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x0C, 0x00, 0x1C, 0x00, 0x38, 0x00, 0x70, 0x00, 0xE0, 0x00,
	0xE0, 0x00, 0x70, 0x00, 0x38, 0x00, 0x1C, 0x00, 0x0C, 0x00,
	0x00, 0x0C, 0x00, 0x0C, 0x00, 0x0C, 0x00, 0x0C, 0x00, 0x0C,
	0x00, 0x0C, 0x00, 0x0C, 0x00, 0x0C, 0x00, 0x0C, 0x00, 0x0C,
	0x00, 0x00, 0x00, 0x00, 0xC0, 0x00, 0xE0, 0x00, 0x70, 0x00,
	0x38, 0x00, 0x18, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x30, 0x06, 0x78, 0x0E, 0xFC, 0x0C, 0xCC, 0x0C, 0xCC,
	0x0C, 0xCC, 0x0C, 0xCC, 0x0E, 0xCC, 0x07, 0xFC, 0x03, 0xF8,
	0xFF, 0xFC, 0xFF, 0xFC, 0x03, 0x0C, 0x03, 0x0C, 0x03, 0x0C,
	0x03, 0x0C, 0x03, 0x0C, 0x03, 0x9C, 0x01, 0xF8, 0x00, 0xF0,
	0x03, 0xF0, 0x07, 0xF8, 0x0E, 0x1C, 0x0C, 0x0C, 0x0C, 0x0C,
	0x0C, 0x0C, 0x0C, 0x0C, 0x0E, 0x1C, 0x07, 0x38, 0x03, 0x30,
	0x00, 0xF0, 0x01, 0xF8, 0x03, 0x9C, 0x03, 0x0C, 0x03, 0x0C,
	0x03, 0x0C, 0x03, 0x0C, 0x03, 0x0C, 0xFF, 0xFC, 0xFF, 0xFC,
	0x03, 0xF0, 0x07, 0xF8, 0x0E, 0xDC, 0x0C, 0xCC, 0x0C, 0xCC,
	0x0C, 0xCC, 0x0C, 0xCC, 0x0E, 0xDC, 0x07, 0xD8, 0x03, 0x90,
	0x00, 0x00, 0x03, 0x00, 0x3F, 0xFC, 0x7F, 0xFC, 0xE3, 0x00,
	0xE3, 0x00, 0x70, 0x00, 0x30, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x03, 0x18, 0x07, 0x9C, 0x0F, 0xCC, 0x0C, 0xCC, 0x0C, 0xCC,
	0x0C, 0xCC, 0x0C, 0xCC, 0x0C, 0xDC, 0x0F, 0xF8, 0x07, 0xF0,
	0xFF, 0xFC, 0xFF, 0xFC, 0x03, 0x00, 0x03, 0x00, 0x03, 0x00,
	0x03, 0x00, 0x03, 0x80, 0x01, 0xFC, 0x00, 0xFC, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1B, 0xFC,
	0x1B, 0xFC, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x30, 0x00, 0x38, 0x00, 0x1C, 0x00, 0x0C,
	0x00, 0x0C, 0x00, 0x1C, 0xCF, 0xF8, 0xCF, 0xF0, 0x00, 0x00,
	0x00, 0x00, 0xFF, 0xFC, 0xFF, 0xFC, 0x00, 0xE0, 0x01, 0xE0,
	0x03, 0xF0, 0x07, 0x38, 0x0E, 0x1C, 0x0C, 0x0C, 0x00, 0x00,
	0x00, 0x00, 0x00, 0x00, 0xC0, 0x0C, 0xC0, 0x0C, 0xFF, 0xFC,
	0xFF, 0xFC, 0x00, 0x0C, 0x00, 0x0C, 0x00, 0x00, 0x00, 0x00,
	0x0F, 0xFC, 0x0F, 0xFC, 0x0E, 0x00, 0x07, 0x00, 0x03, 0xC0,
	0x03, 0xC0, 0x07, 0x00, 0x0E, 0x00, 0x0F, 0xFC, 0x0F, 0xFC,
	0x0F, 0xFC, 0x0F, 0xFC, 0x03, 0x00, 0x07, 0x00, 0x0E, 0x00,
	0x0C, 0x00, 0x0C, 0x00, 0x0E, 0x00, 0x07, 0xFC, 0x03, 0xFC,
	0x03, 0xF0, 0x07, 0xF8, 0x0E, 0x1C, 0x0C, 0x0C, 0x0C, 0x0C,
	0x0C, 0x0C, 0x0C, 0x0C, 0x0E, 0x1C, 0x07, 0xF8, 0x03, 0xF0,
	0x0F, 0xFC, 0x0F, 0xFC, 0x0C, 0xC0, 0x0C, 0xC0, 0x0C, 0xC0,
	0x0C, 0xC0, 0x0C, 0xC0, 0x0F, 0xC0, 0x07, 0x80, 0x03, 0x00,
	0x03, 0x00, 0x07, 0x80, 0x0F, 0xC0, 0x0C, 0xC0, 0x0C, 0xC0,
	0x0C, 0xC0, 0x0C, 0xC0, 0x0C, 0xC0, 0x0F, 0xFC, 0x0F, 0xFC,
	0x0F, 0xFC, 0x0F, 0xFC, 0x03, 0x80, 0x07, 0x00, 0x0E, 0x00,
	0x0C, 0x00, 0x0C, 0x00, 0x0E, 0x00, 0x07, 0x00, 0x03, 0x00,
	0x03, 0x18, 0x07, 0x9C, 0x0F, 0xCC, 0x0C, 0xCC, 0x0C, 0xCC,
	0x0C, 0xCC, 0x0C, 0xCC, 0x0C, 0xFC, 0x0E, 0x78, 0x06, 0x30,
	0x00, 0x00, 0x0C, 0x00, 0x0C, 0x00, 0xFF, 0xF0, 0xFF, 0xF8,
	0x0C, 0x1C, 0x0C, 0x1C, 0x0C, 0x38, 0x0C, 0x30, 0x00, 0x00,
	0x0F, 0xF0, 0x0F, 0xF8, 0x00, 0x1C, 0x00, 0x0C, 0x00, 0x0C,
	0x00, 0x0C, 0x00, 0x0C, 0x00, 0x1C, 0x0F, 0xF8, 0x0F, 0xF0,
	0x0F, 0xC0, 0x0F, 0xE0, 0x00, 0x70, 0x00, 0x38, 0x00, 0x1C,
	0x00, 0x1C, 0x00, 0x38, 0x00, 0x70, 0x0F, 0xE0, 0x0F, 0xC0,
	0x0F, 0xF0, 0x0F, 0xF8, 0x00, 0x1C, 0x00, 0x1C, 0x00, 0xF8,
	0x00, 0xF8, 0x00, 0x1C, 0x00, 0x1C, 0x0F, 0xF8, 0x0F, 0xF0,
	0x0C, 0x0C, 0x0E, 0x1C, 0x07, 0x38, 0x03, 0xF0, 0x01, 0xE0,
	0x01, 0xE0, 0x03, 0xF0, 0x07, 0x38, 0x0E, 0x1C, 0x0C, 0x0C,
	0x0C, 0x00, 0x0E, 0x00, 0x07, 0x0C, 0x03, 0x9C, 0x01, 0xF8,
	0x01, 0xF0, 0x03, 0x80, 0x07, 0x00, 0x0E, 0x00, 0x0C, 0x00,
	0x0C, 0x0C, 0x0C, 0x1C, 0x0C, 0x3C, 0x0C, 0x7C, 0x0C, 0xEC,
	0x0D, 0xCC, 0x0F, 0x8C, 0x0F, 0x0C, 0x0E, 0x0C, 0x0C, 0x0C,
	0x00, 0x00, 0x03, 0x00, 0x07, 0x80, 0x3F, 0xF0, 0x7C, 0xF8,
	0xE0, 0x1C, 0xC0, 0x0C, 0xC0, 0x0C, 0xC0, 0x0C, 0x00, 0x00,
	0x03, 0x0C, 0x03, 0x0C, 0x3F, 0xFC, 0x7F, 0xFC, 0xE3, 0x0C,
	0xC3, 0x0C, 0xC0, 0x0C, 0xE0, 0x0C, 0x70, 0x0C, 0x30, 0x0C,
	0x00, 0x00, 0xC0, 0x0C, 0xC0, 0x0C, 0xC0, 0x0C, 0xE0, 0x1C,
	0x7C, 0xF8, 0x3F, 0xF0, 0x07, 0x80, 0x03, 0x00, 0x00, 0x00,
	0xC0, 0x00, 0xC0, 0x00, 0xC0, 0x00, 0xC0, 0x00, 0xC0, 0x00,
	0xC0, 0x00, 0xC0, 0x00, 0xC0, 0x00, 0xC0, 0x00, 0xC0, 0x00,
	0xFF, 0xFC, 0xFF, 0xFC, 0xFF, 0xFC, 0xFF, 0xFC, 0xFF, 0xFC,
	0xFF, 0xFC, 0xFF, 0xFC, 0xFF, 0xFC, 0xFF, 0xFC, 0xFF, 0xFC
};

/**
 * \brief Prepare to write GRAM data for ili93xx.
 */
static void ili93xx_write_ram_prepare(void)
{
	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		/** Write Data to GRAM (R22h) */
		LCD_IR(0);
		LCD_IR(ILI9325_GRAM_DATA_REG);
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		/** memory write command (R2Ch)*/
		LCD_IR(ILI9341_CMD_MEMORY_WRITE);
		LCD_IR(0);
		LCD_IR(ILI9341_CMD_WRITE_MEMORY_CONTINUE);
	}
}

/**
 * \brief Write data to LCD GRAM.
 *
 * \param ul_color 24-bits RGB color.
 */
static void ili93xx_write_ram(ili93xx_color_t ul_color)
{
	LCD_WD((ul_color >> 16) & 0xFF);
	LCD_WD((ul_color >> 8) & 0xFF);
	LCD_WD(ul_color & 0xFF);
}

/**
 * \brief Write multiple data in buffer to LCD controller for ili93xx.
 *
 * \param p_ul_buf data buffer.
 * \param ul_size size in pixels.
 */
static void ili93xx_write_ram_buffer(const ili93xx_color_t *p_ul_buf,
		uint32_t ul_size)
{
	uint32_t ul_addr;
	for (ul_addr = 0; ul_addr < (ul_size - ul_size % 8); ul_addr += 8) {
		ili93xx_write_ram(p_ul_buf[ul_addr]);
		ili93xx_write_ram(p_ul_buf[ul_addr + 1]);
		ili93xx_write_ram(p_ul_buf[ul_addr + 2]);
		ili93xx_write_ram(p_ul_buf[ul_addr + 3]);
		ili93xx_write_ram(p_ul_buf[ul_addr + 4]);
		ili93xx_write_ram(p_ul_buf[ul_addr + 5]);
		ili93xx_write_ram(p_ul_buf[ul_addr + 6]);
		ili93xx_write_ram(p_ul_buf[ul_addr + 7]);
	}
	for (; ul_addr < ul_size; ul_addr++) {
		ili93xx_write_ram(p_ul_buf[ul_addr]);
	}
}

/**
 * \brief Write a word (16bits)to LCD Register.
 *
 * \param uc_reg register address.
 * \param us_data data to be written.
 */
static void ili93xx_write_register_word(uint8_t uc_reg, uint16_t us_data)
{
	LCD_IR(0);
	LCD_IR(uc_reg);
	LCD_WD((us_data >> 8) & 0xFF);
	LCD_WD(us_data & 0xFF);
}

/**
 * \brief Write data to LCD Register for ili93xx.
 *
 * \param uc_reg register address.
 * \param us_data data to be written.
 */
static void ili93xx_write_register(uint8_t uc_reg, uint8_t *p_data,
		uint8_t uc_datacnt)
{
uint8_t i;

	LCD_IR(0);
	LCD_IR(uc_reg);
	for (i = 0; i < uc_datacnt; i++) {
		LCD_WD(p_data[i]);
	}
}

/**
 * \brief Prepare to read GRAM data for ili93xx.
 */
static void ili93xx_read_ram_prepare(void)
{
	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		LCD_IR(0);
		/** Write Data to GRAM (R22h) */
		LCD_IR(ILI9325_GRAM_DATA_REG);
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		LCD_IR(0);
		/** Write Data to GRAM (R2Eh) */
		LCD_IR(ILI9341_CMD_MEMORY_READ);
	}
}

/**
 * \brief Read data to LCD GRAM for ili93xx.
 *
 * \note For ili9325, because pixel data LCD GRAM is 18-bits, so convertion
 * to RGB 24-bits will cause low color bit lose.
 *
 * \return color 24-bits RGB color.
 */
static uint32_t ili93xx_read_ram(void)
{
	uint8_t value[3];
	uint32_t color;
	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		/** dummy read*/
		value[0] = LCD_RD();
		value[1] = LCD_RD();
		/** data upper byte*/
		value[0] = LCD_RD();
		/** data lower byte */
		value[1] = LCD_RD();

		/** Convert RGB565 to RGB888 */
		/** For BGR format */
		color = ((value[0] & 0xF8)) | ((value[0] & 0x07) << 13) |
				((value[1] & 0xE0) << 5) |
				((value[1] & 0x1F) << 19);
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		/** dummy read */
		value[0] = LCD_RD();
		/** the highest byte - R byte*/
		value[0] = LCD_RD();
		/** the middle byte - G byte*/
		value[1] = LCD_RD();
		/** the lowest byte - B byte*/
		value[2] = LCD_RD();
		/** combine R, G, B byte to a color value */
		color = (value[0] << 16) | (value[1] << 8) | value[2];
	}

	return color;
}

/**
 * \brief Read data from LCD Register.
 *
 * \param uc_reg register address.
 * \param p_data the pointer to the read data.
 * \param uc_datacnt the number of the read data
 */
static void ili93xx_read_register(uint8_t uc_reg, uint8_t *p_data,
		uint8_t uc_datacnt)
{
uint8_t i;

	LCD_IR(0);
	LCD_IR(uc_reg);

	for (i = 0; i < uc_datacnt; i++) {
		p_data[i] = LCD_RD();
	}
}

/**
 * \brief Delay function.
 */
static void ili93xx_delay(uint32_t ul_ms)
{
	volatile uint32_t i;

	for (i = 0; i < ul_ms; i++) {
		for (i = 0; i < 100000; i++) {
		}
	}
}

/**
 * \brief Check box coordinates.
 *
 * \param p_ul_x1 X coordinate of upper-left corner on LCD.
 * \param p_ul_y1 Y coordinate of upper-left corner on LCD.
 * \param p_ul_x2 X coordinate of lower-right corner on LCD.
 * \param p_ul_y2 Y coordinate of lower-right corner on LCD.
 */
static void ili93xx_check_box_coordinates(uint32_t *p_ul_x1, uint32_t *p_ul_y1,
		uint32_t *p_ul_x2, uint32_t *p_ul_y2)
{
	uint32_t dw;

	if (*p_ul_x1 >= g_ul_lcd_x_length) {
		*p_ul_x1 = g_ul_lcd_x_length - 1;
	}

	if (*p_ul_x2 >= g_ul_lcd_x_length) {
		*p_ul_x2 = g_ul_lcd_x_length - 1;
	}

	if (*p_ul_y1 >= g_ul_lcd_y_length) {
		*p_ul_y1 = g_ul_lcd_y_length - 1;
	}

	if (*p_ul_y2 >= g_ul_lcd_y_length) {
		*p_ul_y2 = g_ul_lcd_y_length - 1;
	}

	if (*p_ul_x1 > *p_ul_x2) {
		dw = *p_ul_x1;
		*p_ul_x1 = *p_ul_x2;
		*p_ul_x2 = dw;
	}

	if (*p_ul_y1 > *p_ul_y2) {
		dw = *p_ul_y1;
		*p_ul_y1 = *p_ul_y2;
		*p_ul_y2 = dw;
	}
}

/**
 * \brief Read device ID to idenfity the device
 *        ILI9325 device ID locates in Device Code Read (R00h) register.
 *        ILI9341 device ID locates in Read ID4 (RD3h) register.
 *
 * \return 0 if secceed in identifying device; otherwise fails.
 */
uint8_t ili93xx_device_type_identify(void)
{
	uint8_t paratable[6];
	uint16_t chipid;

	/** Read ID4 (RD4h) register to get device code for ILI9341*/
	ili93xx_read_register(ILI9341_CMD_READ_ID4, paratable, 4);
	chipid = ((uint16_t)paratable[2] << 8) + paratable[3];

	if (chipid == ILI9341_DEVICE_CODE) {
		g_uc_device_type = DEVICE_TYPE_ILI9341;
		return 0;
	}

	/** Driver Code Read (R00h) for ILI9325*/
	ili93xx_read_register(ILI9325_DEVICE_CODE_REG, paratable, 2);
	chipid = ((uint16_t)paratable[0] << 8) + paratable[1];
	if (chipid == ILI9325_DEVICE_CODE) {
		g_uc_device_type = DEVICE_TYPE_ILI9325;
		return 0;
	}

	return 1;
}

/**
 * \brief Initialize the ILI93XX lcd driver.
 *
 * \note Make sure below works have been done before calling ili93xx_init()
 * 1. ILI93xx related Pins have been initialized correctly.
 * 2. SMC has been configured correctly for access ILI93xx (8-bit system
 *    interface for now).
 *
 * \param p_opt pointer to ILI93xx option structure.
 *
 * \return 0 if initialization succeeds, otherwise fails.
 */
uint32_t ili93xx_init(struct ili93xx_opt_t *p_opt)
{
	uint8_t paratable[15];

	/** Identify the LCD driver device*/
	if (ili93xx_device_type_identify() != 0) {
		return 1;
	}

	g_ul_lcd_x_length = ILI93XX_LCD_WIDTH;
	g_ul_lcd_y_length = ILI93XX_LCD_HEIGHT;

	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		/** Turn off LCD */
		ili93xx_write_register_word(ILI9325_DISP_CTRL1, ILI9325_DISP_CTRL1_GON |
				ILI9325_DISP_CTRL1_DTE | ILI9325_DISP_CTRL1_D(0x03));

		/** Start initial sequence */
		/** Disable sleep and standby mode*/
		ili93xx_write_register_word(ILI9325_POWER_CTRL1, 0x0000);
		/** Start internal OSC */
		ili93xx_write_register_word(ILI9325_START_OSC_CTRL,
				ILI9325_START_OSC_CTRL_EN);
		/** Set SS bit and direction output from S720 to S1 */
		ili93xx_write_register_word(ILI9325_DRIVER_OUTPUT_CTRL1,
				ILI9325_DRIVER_OUTPUT_CTRL1_SS);
		/** Set 1 line inversion */
		ili93xx_write_register_word(ILI9325_LCD_DRIVING_CTRL,
				ILI9325_LCD_DRIVING_CTRL_BIT10 | ILI9325_LCD_DRIVING_CTRL_EOR
				| ILI9325_LCD_DRIVING_CTRL_BC0);
		/** Disable resizing feature */
		ili93xx_write_register_word(ILI9325_RESIZE_CTRL, 0x0000);
		/** Set the back porch and front porch */
		ili93xx_write_register_word(ILI9325_DISP_CTRL2,
				ILI9325_DISP_CTRL2_BP(
				0x07) | ILI9325_DISP_CTRL2_FP(0x02));
		/** Set non-display area refresh cycle ISC[3:0] */
		ili93xx_write_register_word(ILI9325_DISP_CTRL3, 0x0000);
		/** Disable FMARK function */
		ili93xx_write_register_word(ILI9325_DISP_CTRL4, 0x0000);
		/** 18-bit RGB interface and writing display data by system
		 *interface */
		ili93xx_write_register_word(ILI9325_RGB_DISP_INTERFACE_CTRL1,
				0x0000);
		/** Set the output position of frame cycle */
		ili93xx_write_register_word(ILI9325_FRAME_MAKER_POS, 0x0000);
		/** RGB interface polarity */
		ili93xx_write_register_word(ILI9325_RGB_DISP_INTERFACE_CTRL2,
				0x0000);

		/** Power on sequence */
		/** Disable sleep and standby mode */
		ili93xx_write_register_word(ILI9325_POWER_CTRL1, 0x0000);

		/**
		 * Selects the operating frequency of the step-up circuit 1,2
		 * and Sets the ratio factor of Vci.
		 */
		ili93xx_write_register_word(ILI9325_POWER_CTRL2, 0x0000);
		/** Set VREG1OUT voltage */
		ili93xx_write_register_word(ILI9325_POWER_CTRL3, 0x0000);
		/** Set VCOM amplitude */
		ili93xx_write_register_word(ILI9325_POWER_CTRL4, 0x0000);
		ili93xx_delay(200);

		/** Enable power supply and source driver */

		/**
		 * Adjusts the constant current and Sets the factor used
		 * in the step-up circuits.
		 */
		ili93xx_write_register_word(ILI9325_POWER_CTRL1,
				ILI9325_POWER_CTRL1_SAP | ILI9325_POWER_CTRL1_BT(0x02) |
				ILI9325_POWER_CTRL1_APE |
				ILI9325_POWER_CTRL1_AP(0x01));

		/**
		 * Select the operating frequency of the step-up circuit 1,2 and
		 * Sets the ratio factor of Vci
		 */
		ili93xx_write_register_word(ILI9325_POWER_CTRL2,
				ILI9325_POWER_CTRL2_DC1(0x02) |
				ILI9325_POWER_CTRL2_DC0(0x02) | ILI9325_POWER_CTRL2_VC(0x07));
		ili93xx_delay(50);
		/** Internal reference voltage= Vci */
		ili93xx_write_register_word(ILI9325_POWER_CTRL3,
				ILI9325_POWER_CTRL3_PON | ILI9325_POWER_CTRL3_VRH(0x0B));
		ili93xx_delay(50);
		/** Set VDV[4:0] for VCOM amplitude */
		ili93xx_write_register_word(ILI9325_POWER_CTRL4,
				ILI9325_POWER_CTRL4_VDV(0x11));
		/** Set VCM[5:0] for VCOMH */
		ili93xx_write_register_word(ILI9325_POWER_CTRL7,
				ILI9325_POWER_CTRL7_VCM(0x19));
		/** Set Frame Rate */
		ili93xx_write_register_word(ILI9325_FRAME_RATE_AND_COLOR_CTRL,
				ILI9325_FRAME_RATE_AND_COLOR_CTRL_FRS(0x0D));
		ili93xx_delay(50);

		/** Adjust the Gamma Curve */
		ili93xx_write_register_word(ILI9325_GAMMA_CTL1, 0x0000);
		ili93xx_write_register_word(ILI9325_GAMMA_CTL2,
				ILI9325_GAMMA_CTL2_KP3(0x02) |
				ILI9325_GAMMA_CTL2_KP2(0x04));
		ili93xx_write_register_word(ILI9325_GAMMA_CTL3,
				ILI9325_GAMMA_CTL3_KP5(0x02) |
				ILI9325_GAMMA_CTL3_KP4(0x00));
		ili93xx_write_register_word(ILI9325_GAMMA_CTL4,
				ILI9325_GAMMA_CTL4_RP1(0x00) |
				ILI9325_GAMMA_CTL4_RP0(0x07));
		ili93xx_write_register_word(ILI9325_GAMMA_CTL5,
				ILI9325_GAMMA_CTL5_VRP1(0x14) |
				ILI9325_GAMMA_CTL5_VRP0(0x04));
		ili93xx_write_register_word(ILI9325_GAMMA_CTL6,
				ILI9325_GAMMA_CTL6_KN1(0x07) |
				ILI9325_GAMMA_CTL6_KN0(0x05));
		ili93xx_write_register_word(ILI9325_GAMMA_CTL7,
				ILI9325_GAMMA_CTL7_KN3(0x03) |
				ILI9325_GAMMA_CTL7_KN2(0x05));
		ili93xx_write_register_word(ILI9325_GAMMA_CTL8,
				ILI9325_GAMMA_CTL8_KN5(0x07) |
				ILI9325_GAMMA_CTL8_KN4(0x07));
		ili93xx_write_register_word(ILI9325_GAMMA_CTL9,
				ILI9325_GAMMA_CTL9_RN1(0x07) |
				ILI9325_GAMMA_CTL9_RN0(0x01));
		ili93xx_write_register_word(ILI9325_GAMMA_CTL10,
				ILI9325_GAMMA_CTL10_VRN1(0x00) |
				ILI9325_GAMMA_CTL10_VRN0(0x0E));
		/**
		 * Use the high speed write mode (HWM=1)
		 * When TRI = 1, data are transferred to the internal RAM in
		 * 8-bit x 3 transfers mode via the 8-bit interface.
		 * DFM Set the mode of transferring data to the internal RAM
		 * when TRI = 1.
		 * I/D[1:0] = 11 Horizontal : increment Vertical : increment,
		 * AM=0:Horizontal
		 */
		ili93xx_write_register_word(ILI9325_ENTRY_MODE,
				ILI9325_ENTRY_MODE_TRI | ILI9325_ENTRY_MODE_DFM |
				ILI9325_ENTRY_MODE_ID(0x01) | ILI9325_ENTRY_MODE_BGR);
		/**
		 * Sets the number of lines to drive the LCD at an interval of 8
		 * lines. The scan direction is from G320 to G1
		 */
		ili93xx_write_register_word(ILI9325_DRIVER_OUTPUT_CTRL2,
				ILI9325_DRIVER_OUTPUT_CTRL2_GS |
				ILI9325_DRIVER_OUTPUT_CTRL2_NL(0x27));

		/** Vertical Scrolling */
		/** Disable scrolling and enable the grayscale inversion */
		ili93xx_write_register_word(ILI9325_BASE_IMG_DISP_CTRL,
				ILI9325_BASE_IMG_DISP_CTRL_REV);
		ili93xx_write_register_word(ILI9325_VERTICAL_SCROLL_CTRL,
				0x0000);

		/** Disable Partial Display */
		ili93xx_write_register_word(ILI9325_PARTIAL_IMG1_DISP_POS,
				0x0000);
		ili93xx_write_register_word(
				ILI9325_PARTIAL_IMG1_AREA_START_LINE,
				0x0000);
		ili93xx_write_register_word(ILI9325_PARTIAL_IMG1_AREA_END_LINE,
				0x0000);
		ili93xx_write_register_word(ILI9325_PARTIAL_IMG2_DISP_POS,
				0x0000);
		ili93xx_write_register_word(
				ILI9325_PARTIAL_IMG2_AREA_START_LINE,
				0x0000);
		ili93xx_write_register_word(ILI9325_PARTIAL_IMG2_AREA_END_LINE,
				0x0000);

		/** Panel Control */
		ili93xx_write_register_word(ILI9325_PANEL_INTERFACE_CTRL1,
				ILI9325_PANEL_INTERFACE_CTRL1_RTNI(0x10));
		ili93xx_write_register_word(ILI9325_PANEL_INTERFACE_CTRL2,
				ILI9325_PANEL_INTERFACE_CTRL2_NOWI(0x06));
		ili93xx_write_register_word(ILI9325_PANEL_INTERFACE_CTRL4,
				ILI9325_PANEL_INTERFACE_CTRL4_DIVE(0x01) |
				ILI9325_PANEL_INTERFACE_CTRL4_RTNE(0x10));

		ili93xx_set_window(0, 0, p_opt->ul_width, p_opt->ul_height);
		ili93xx_set_foreground_color(p_opt->foreground_color);
		ili93xx_set_cursor_position(0, 0);
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		/** init for ILI9341 **/
		/** power control A configuration*/
		paratable[0] = 0x39;
		paratable[1] = 0x2C;
		paratable[2] = 0x00;
		paratable[3] = 0x34;
		paratable[4] = 0x02;
		ili93xx_write_register(ILI9341_CMD_POWER_CONTROL_A, paratable, 5);

		/** power control B configuration */
		paratable[0] = 0;
		paratable[1] = 0xAA;
		paratable[2] = 0xB0;
		ili93xx_write_register(ILI9341_CMD_POWER_CONTROL_B, paratable, 3);

		/** Pump Ratio Control configuration */
		paratable[0] = 0x30;
		ili93xx_write_register(ILI9341_CMD_PUMP_RATIO_CONTROL,
				paratable, 1);

		/** Power Control 1 configuration*/
		paratable[0] = 0x25;
		ili93xx_write_register(ILI9341_CMD_POWER_CONTROL_1, paratable, 1);

		/** Power Control 2 configuration*/
		paratable[0] = 0x11;
		ili93xx_write_register(ILI9341_CMD_POWER_CONTROL_2, paratable, 1);

		/** VOM Control 1 configuration*/
		paratable[0] = 0x5C;
		paratable[1] = 0x4C;
		ili93xx_write_register(ILI9341_CMD_VCOM_CONTROL_1, paratable, 2);

		/** VOM control 2 configuration*/
		paratable[0] = 0x94;
		ili93xx_write_register(ILI9341_CMD_VCOM_CONTROL_2, paratable, 1);

		/** Driver Timing Control A configuration*/
		paratable[0] = 0x85;
		paratable[1] = 0x01;
		paratable[2] = 0x78;
		ili93xx_write_register(ILI9341_CMD_DRIVER_TIMING_CTL_A, paratable, 3);

		/** Driver Timing Control B configuration*/
		paratable[0] = 0x00;
		paratable[1] = 0x00;
		ili93xx_write_register(ILI9341_CMD_DRIVER_TIMING_CTL_B, paratable, 2);

		/** Memory Access Control configuration*/
		paratable[0] = ILI9341_CMD_MEMORY_ACCESS_CONTROL_MX |
				ILI9341_CMD_MEMORY_ACCESS_CONTROL_BGR;
		ili93xx_write_register(ILI9341_CMD_MEMORY_ACCESS_CONTROL,
				paratable, 1);

		/** Colmod Pixel Format Set configuation*/
		paratable[0] = 0x06;
		ili93xx_write_register(ILI9341_CMD_PIXEL_FORMAT_SET, paratable, 1);

		/** Display Function Control */
		paratable[0] = 0x02;
		paratable[1] = 0x82;
		paratable[2] = 0x27;
		paratable[3] = 0x00;
		ili93xx_write_register(ILI9341_CMD_DISPLAY_FUNCTION_CTL,
				      paratable, 4);
				
		paratable[0] = 0x00;
		ili93xx_write_register(ILI9341_CMD_ENABLE_3_GAMMA_CONTROL,
				      paratable,1);
		
		paratable[0] = 0x01;
		ili93xx_write_register(ILI9341_CMD_GAMMA_SET, paratable,1);
		
		/** set gamma curve parameters*/
		paratable[0]=0x0F;
		paratable[1]=0x31;
		paratable[2]=0x2B;
		paratable[3]=0x0C;
		paratable[4]=0x0E;
		paratable[5]=0x08;
		paratable[6]=0x4E;
		paratable[7]=0xF1;
		paratable[8]=0x37;
		paratable[9]=0x07;
		paratable[10]=0x10;
		paratable[11]=0x03;
		paratable[12]=0x0E;
		paratable[13]=0x09;
		paratable[14]=0x00;
		ili93xx_write_register(ILI9341_CMD_POSITIVE_GAMMA_CORRECTION,
				      paratable, 15);
		paratable[0]=0x00;
		paratable[1]=0x0E;
		paratable[2]=0x14;
		paratable[3]=0x03;
		paratable[4]=0x11;
		paratable[5]=0x07;
		paratable[6]=0x31;
		paratable[7]=0xC1;
		paratable[8]=0x48;
		paratable[9]=0x08;
		paratable[10]=0x0F;
		paratable[11]=0x0C;
		paratable[12]=0x31;
		paratable[13]=0x36;
		paratable[14]=0x0F;
		ili93xx_write_register(ILI9341_CMD_NEGATIVE_GAMMA_CORRECTION,
				      paratable, 15);
		
		/** set window area*/
		ili93xx_set_window(0, 0, p_opt->ul_width, p_opt->ul_height);
		ili93xx_set_foreground_color(p_opt->foreground_color);
		/** Leave sleep mode*/
		ili93xx_write_register(ILI9341_CMD_SLEEP_OUT, paratable, 0);
		ili93xx_delay(10);
		/** Display on*/
		ili93xx_write_register(ILI9341_CMD_DISPLAY_ON, paratable, 0);
	} else {
		/** exit with return value 1 if device type is not supported.*/
		return 1;
	}

	return 0;
}

/**
 * \brief get the device type.
 */
uint8_t ili93xx_device_type(void)
{
	return g_uc_device_type;
}

/**
 * \brief Turn on the LCD.
 */
void ili93xx_display_on(void)
{
	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		ili93xx_write_register_word(ILI9325_DISP_CTRL1,
				ILI9325_DISP_CTRL1_BASEE |
				ILI9325_DISP_CTRL1_GON |
				ILI9325_DISP_CTRL1_DTE |
				ILI9325_DISP_CTRL1_D(0x03));
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		ili93xx_write_register(ILI9341_CMD_DISPLAY_ON, NULL, 0);
	}
}

/**
 * \brief Turn off the LCD.
 */
void ili93xx_display_off(void)
{
	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		ili93xx_write_register_word(ILI9325_DISP_CTRL1, 0x00);
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		ili93xx_write_register(ILI9341_CMD_DISPLAY_OFF, NULL, 0);
	}
}

/**
 * \brief Set foreground color.
 *
 * \param ul_color foreground color.
 */
void ili93xx_set_foreground_color(ili93xx_color_t ul_color)
{
	uint32_t i;

	/** Fill the cache with selected color */
	for (i = 0; i < LCD_DATA_CACHE_SIZE; ++i) {
		g_ul_pixel_cache[i] = ul_color;
	}
}

/**
 * \brief Fill the LCD buffer with the specified color.
 *
 * \param ul_color fill color.
 */
void ili93xx_fill(ili93xx_color_t ul_color)
{
	uint32_t dw;
	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		ili93xx_set_cursor_position(0, 0);
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		ili93xx_set_window(0, 0, g_ul_lcd_x_length, g_ul_lcd_y_length);
	}

	ili93xx_write_ram_prepare();

	for (dw = ILI93XX_LCD_WIDTH * ILI93XX_LCD_HEIGHT; dw > 0; dw--) {
		ili93xx_write_ram(ul_color);
	}
}

/**
 * \brief Set display window.
 *
 * \param ul_x Horizontal address start position
 * \param ul_y Vertical address start position
 * \param ul_width The width of the window.
 * \param ul_height The height of the window.
 */
void ili93xx_set_window(uint32_t ul_x, uint32_t ul_y, uint32_t ul_width,
		uint32_t ul_height)
{
	Assert(ul_x <= (g_ul_lcd_x_length - 1));
	Assert(ul_y <= (g_ul_lcd_y_length - 1));
	Assert(ul_width <= (g_ul_lcd_x_length - ul_x));
	Assert(ul_height <= (g_ul_lcd_y_length - ul_y));
	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		/** Set Horizontal Address Start Position */
		ili93xx_write_register_word(ILI9325_HORIZONTAL_ADDR_START,
				(uint16_t)ul_x);

		/** Set Horizontal Address End Position */
		ili93xx_write_register_word(ILI9325_HORIZONTAL_ADDR_END,
				(uint16_t)(ul_x + ul_width - 1));

		/** Set Vertical Address Start Position */
		ili93xx_write_register_word(ILI9325_VERTICAL_ADDR_START,
				(uint16_t)ul_y);

		/** Set Vertical Address End Position */
		ili93xx_write_register_word(ILI9325_VERTICAL_ADDR_END,
				(uint16_t)(ul_y + ul_height - 1));
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		uint8_t paratable[4];

		/** Set Column Address Position */
		paratable[0] = (ul_x >> 8) & 0xFF;
		paratable[1] = ul_x & 0xFF;
		paratable[2] = ((ul_x + ul_width - 1) >> 8) & 0xFF;
		paratable[3] = (ul_x + ul_width - 1) & 0xFF;
		ili93xx_write_register(ILI9341_CMD_COLUMN_ADDRESS_SET,
				paratable, 4);

		/** Set Page Address Position */
		paratable[0] = (ul_y >> 8) & 0xFF;
		paratable[1] = ul_y & 0xFF;
		paratable[2] = ((ul_y + ul_height - 1) >> 8) & 0xFF;
		paratable[3] = (ul_y + ul_height - 1) & 0xFF;
		ili93xx_write_register(ILI9341_CMD_PAGE_ADDRESS_SET,
				       paratable, 4);
	}
}

/**
 * \brief Set cursor of LCD screen.
 *
 * \param us_x X coordinate of upper-left corner on LCD.
 * \param us_y Y coordinate of upper-left corner on LCD.
 */
void ili93xx_set_cursor_position(uint16_t us_x, uint16_t us_y)
{
	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		/** GRAM Horizontal/Vertical Address Set (R20h, R21h) */
		ili93xx_write_register_word(ILI9325_HORIZONTAL_GRAM_ADDR_SET, us_x);
		ili93xx_write_register_word(ILI9325_VERTICAL_GRAM_ADDR_SET, us_y);
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		/** There is no corresponding operation for ILI9341. */
	}
}

/**
 * \brief Scroll up/down for the number of specified lines.
 *
 * \param ul_lines number of lines to scroll.
 */
void ili93xx_scroll(int32_t ul_lines)
{
	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		ili93xx_write_register_word(ILI9325_VERTICAL_SCROLL_CTRL, ul_lines);
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		uint8_t paratable[2];

		paratable[0] = (ul_lines >> 8) & 0xFF;
		paratable[1] = ul_lines & 0xFF;
		ili93xx_write_register(ILI9341_CMD_VERT_SCROLL_START_ADDRESS,
				paratable, 2);
	}
}

/**
 * \brief Vertical Scroll area definition for ili9341.
 *
 * \param us_tfa the top fixed area (the No. of lines)
 * \param us_vsa the height of the vetical scrolling area
 * \param us_bfa the bottom fixed area (the No. of lines)
 */
void ili93xx_vscroll_area_define(uint16_t us_tfa, uint16_t us_vsa,
		uint16_t us_bfa)
{
	if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		uint8_t paratable[6];

		paratable[0] = (us_tfa >> 8) & 0xFF;
		paratable[1] = us_tfa & 0xFF;
		paratable[2] = (us_vsa >> 8) & 0xFF;
		paratable[3] = us_vsa & 0xFF;
		paratable[4] = (us_bfa >> 8) & 0xFF;
		paratable[5] = us_bfa & 0xFF;
		ili93xx_write_register(ILI9341_CMD_VERT_SCROLL_DEFINITION,
				paratable, 6);
	}
}

/**
 * \brief Enable the scrolling feature.
 */
void ili93xx_enable_scroll(void)
{
	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		ili93xx_write_register_word(ILI9325_BASE_IMG_DISP_CTRL,
				ILI9325_BASE_IMG_DISP_CTRL_REV |
				ILI9325_BASE_IMG_DISP_CTRL_VLE);
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		/** no operation needed for ILI9341*/
	}
}

/**
 * \brief Disable the scrolling feature.
 */
void ili93xx_disable_scroll(void)
{
	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		ili93xx_write_register_word(ILI9325_BASE_IMG_DISP_CTRL,
				ILI9325_BASE_IMG_DISP_CTRL_REV);
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		ili93xx_display_off();
		ili93xx_write_register(ILI9341_CMD_NORMAL_DISP_MODE_ON, NULL, 0);
		ili93xx_display_on();
	}
}

/**
 * \brief Set display direction.
 *
 * \param e_dd 0: horizontal direction, 1: vertical direction
 * \param e_shd: horizontal increase(0) or decrease(1)
 * \param e_scd: vertical increase(1) or decrease(0)
 */
void ili93xx_set_display_direction(enum ili93xx_display_direction e_dd,
		enum ili93xx_shift_direction e_shd,
		enum ili93xx_scan_direction e_scd)
{
	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		if (e_dd == LANDSCAPE) {
			ili93xx_write_register_word(ILI9325_ENTRY_MODE,
					ILI9325_ENTRY_MODE_BGR | ILI9325_ENTRY_MODE_TRI |
					ILI9325_ENTRY_MODE_DFM | ILI9325_ENTRY_MODE_ID(0x00)|
					ILI9325_ENTRY_MODE_AM);
			g_ul_lcd_x_length = ILI93XX_LCD_HEIGHT;
			g_ul_lcd_y_length = ILI93XX_LCD_WIDTH;
		} else {
			ili93xx_write_register_word(ILI9325_ENTRY_MODE,
					ILI9325_ENTRY_MODE_BGR | ILI9325_ENTRY_MODE_TRI |
					ILI9325_ENTRY_MODE_DFM | ILI9325_ENTRY_MODE_ID(0x01));
			g_ul_lcd_x_length = ILI93XX_LCD_WIDTH;
			g_ul_lcd_y_length = ILI93XX_LCD_HEIGHT;
		}

		if (e_shd == H_INCREASE) {
			ili93xx_write_register_word(ILI9325_DRIVER_OUTPUT_CTRL1, 0x0000);
		} else {
			ili93xx_write_register_word(ILI9325_DRIVER_OUTPUT_CTRL1,
					ILI9325_DRIVER_OUTPUT_CTRL1_SS);
		}

		if (e_scd == V_INCREASE) {
			ili93xx_write_register_word(ILI9325_DRIVER_OUTPUT_CTRL2,
					ILI9325_DRIVER_OUTPUT_CTRL2_NL(0x27));
		} else {
			ili93xx_write_register_word(ILI9325_DRIVER_OUTPUT_CTRL2,
					ILI9325_DRIVER_OUTPUT_CTRL2_GS |
					ILI9325_DRIVER_OUTPUT_CTRL2_NL(0x27));
		}
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		if (e_dd == LANDSCAPE) {
			uint8_t paratable[1];
			paratable[0] = ILI9341_CMD_MEMORY_ACCESS_CONTROL_MV |
					ILI9341_CMD_MEMORY_ACCESS_CONTROL_BGR;
			ili93xx_write_register(
					ILI9341_CMD_MEMORY_ACCESS_CONTROL,
					paratable, 1);
			g_ul_lcd_x_length = ILI93XX_LCD_HEIGHT;
			g_ul_lcd_y_length = ILI93XX_LCD_WIDTH;
		} else {
			uint8_t paratable[1];
			paratable[0] = ILI9341_CMD_MEMORY_ACCESS_CONTROL_BGR |
					ILI9341_CMD_MEMORY_ACCESS_CONTROL_MX;
			ili93xx_write_register(
					ILI9341_CMD_MEMORY_ACCESS_CONTROL,
					paratable, 1);
			g_ul_lcd_x_length = ILI93XX_LCD_WIDTH;
			g_ul_lcd_y_length = ILI93XX_LCD_HEIGHT;
		}
	}
}

/**
 * \brief Draw a pixel on LCD.
 *
 * \param ul_x X coordinate of pixel.
 * \param ul_y Y coordinate of pixel.
 *
 * \return 0 if succeeds, otherwise fails.
 */
uint32_t ili93xx_draw_pixel(uint32_t ul_x, uint32_t ul_y)
{
	if ((ul_x >= g_ul_lcd_x_length) || (ul_y >= g_ul_lcd_y_length)) {
		return 1;
	}

	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		/** Set cursor */
		ili93xx_set_cursor_position(ul_x, ul_y);
		/** Prepare to write in GRAM */
		ili93xx_write_ram_prepare();
		ili93xx_write_ram(*g_ul_pixel_cache);
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		ili93xx_set_window(ul_x, ul_y, 0, 0);
		/** Prepare to write in GRAM */
		ili93xx_write_ram_prepare();
		ili93xx_write_ram(*g_ul_pixel_cache);
	}

	return 0;
}

/**
 * \brief Get a pixel from LCD.
 *
 * \param ul_x X coordinate of pixel.
 * \param ul_y Y coordinate of pixel.
 *
 * \return the pixel color.
 */
ili93xx_color_t ili93xx_get_pixel(uint32_t ul_x, uint32_t ul_y)
{
	Assert(ul_x <= g_ul_lcd_x_length);
	Assert(ul_y <= g_ul_lcd_y_length);

	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		/** Set cursor */
		ili93xx_set_cursor_position(ul_x, ul_y);
		/** Prepare to write in GRAM */
		ili93xx_read_ram_prepare();
		return ili93xx_read_ram();
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		ili93xx_set_window(ul_x, ul_y, 0, 0);
		/** Prepare to write in GRAM */
		ili93xx_read_ram_prepare();
		return ili93xx_read_ram();
	}

	return 0;
}

/**
 * \brief Draw a line on LCD, which is not horizontal or vertical.
 *
 * \param ul_x1 X coordinate of line start.
 * \param ul_y1 Y coordinate of line start.
 * \param ul_x2 X coordinate of line end.
 * \param ul_y2 Y coordinate of line endl.
 */
static void ili93xx_draw_line_bresenham(uint32_t ul_x1, uint32_t ul_y1,
		uint32_t ul_x2, uint32_t ul_y2)
{
	int dx, dy;
	int i;
	int xinc, yinc, cumul;
	int x, y;

	x = ul_x1;
	y = ul_y1;
	dx = ul_x2 - ul_x1;
	dy = ul_y2 - ul_y1;
	xinc = (dx > 0) ? 1 : -1;
	yinc = (dy > 0) ? 1 : -1;
	dx = abs(ul_x2 - ul_x1);
	dy = abs(ul_y2 - ul_y1);

	ili93xx_draw_pixel(x, y);

	if (dx > dy) {
		cumul = dx >> 1;

		for (i = 1; i <= dx; i++) {
			x += xinc;
			cumul += dy;

			if (cumul >= dx) {
				cumul -= dx;
				y += yinc;
			}

			ili93xx_draw_pixel(x, y);
		}
	} else {
		cumul = dy >> 1;

		for (i = 1; i <= dy; i++) {
			y += yinc;
			cumul += dx;

			if (cumul >= dy) {
				cumul -= dy;
				x += xinc;
			}

			ili93xx_draw_pixel(x, y);
		}
	}
}

/**
 * \brief Draw a line on LCD.
 *
 * \param ul_x1 X coordinate of line start.
 * \param ul_y1 Y coordinate of line start.
 * \param ul_x2 X coordinate of line end.
 * \param ul_y2 Y coordinate of line end.
 */
void ili93xx_draw_line(uint32_t ul_x1, uint32_t ul_y1,
		uint32_t ul_x2, uint32_t ul_y2)
{
	if ((ul_y1 == ul_y2) || (ul_x1 == ul_x2)) {
		ili93xx_draw_filled_rectangle(ul_x1, ul_y1, ul_x2, ul_y2);
	} else {
		ili93xx_draw_line_bresenham(ul_x1, ul_y1, ul_x2, ul_y2);
	}
}

/**
 * \brief Draw a rectangle on LCD.
 *
 * \param ul_x1 X coordinate of upper-left corner on LCD.
 * \param ul_y1 Y coordinate of upper-left corner on LCD.
 * \param ul_x2 X coordinate of lower-right corner on LCD.
 * \param ul_y2 Y coordinate of lower-right corner on LCD.
 */
void ili93xx_draw_rectangle(uint32_t ul_x1, uint32_t ul_y1,
		uint32_t ul_x2, uint32_t ul_y2)
{
	ili93xx_check_box_coordinates(&ul_x1, &ul_y1, &ul_x2, &ul_y2);

	ili93xx_draw_filled_rectangle(ul_x1, ul_y1, ul_x2, ul_y1);
	ili93xx_draw_filled_rectangle(ul_x1, ul_y2, ul_x2, ul_y2);

	ili93xx_draw_filled_rectangle(ul_x1, ul_y1, ul_x1, ul_y2);
	ili93xx_draw_filled_rectangle(ul_x2, ul_y1, ul_x2, ul_y2);
}

/**
 * \brief Draw a filled rectangle on LCD.
 *
 * \param ul_x1 X coordinate of upper-left corner on LCD.
 * \param ul_y1 Y coordinate of upper-left corner on LCD.
 * \param ul_x2 X coordinate of lower-right corner on LCD.
 * \param ul_y2 Y coordinate of lower-right corner on LCD.
 */
void ili93xx_draw_filled_rectangle(uint32_t ul_x1, uint32_t ul_y1,
		uint32_t ul_x2, uint32_t ul_y2)
{
	uint32_t size, blocks;

	/** Swap coordinates if necessary */
	ili93xx_check_box_coordinates(&ul_x1, &ul_y1, &ul_x2, &ul_y2);

	/** Determine the refresh window area */
	ili93xx_set_window(ul_x1, ul_y1, (ul_x2 - ul_x1) + 1,
			(ul_y2 - ul_y1) + 1);

	/** Set cursor */
	ili93xx_set_cursor_position(ul_x1, ul_y1);

	/** Prepare to write in Graphic RAM */
	ili93xx_write_ram_prepare();

	size = (ul_x2 - ul_x1 + 1) * (ul_y2 - ul_y1 + 1);

	/** Send pixels blocks => one SPI IT / block */
	blocks = size / LCD_DATA_CACHE_SIZE;
	while (blocks--) {
		ili93xx_write_ram_buffer(g_ul_pixel_cache,
								LCD_DATA_CACHE_SIZE);
	}

	/** Send remaining pixels */
	ili93xx_write_ram_buffer(g_ul_pixel_cache,
					size % LCD_DATA_CACHE_SIZE);

	/** Reset the refresh window area */
	ili93xx_set_window(0, 0, g_ul_lcd_x_length, g_ul_lcd_y_length);
}

/**
 * \brief Draw a circle on LCD.
 *
 * \param ul_x X coordinate of circle center.
 * \param ul_y Y coordinate of circle center.
 * \param ul_r circle radius.
 *
 * \return 0 if succeeds, otherwise fails.
 */
uint32_t ili93xx_draw_circle(uint32_t ul_x, uint32_t ul_y, uint32_t ul_r)
{
	int32_t d;
	uint32_t curX;
	uint32_t curY;

	if (ul_r == 0) {
		return 1;
	}

	d = 3 - (ul_r << 1);
	curX = 0;
	curY = ul_r;

	while (curX <= curY) {
		ili93xx_draw_pixel(ul_x + curX, ul_y + curY);
		ili93xx_draw_pixel(ul_x + curX, ul_y - curY);
		ili93xx_draw_pixel(ul_x - curX, ul_y + curY);
		ili93xx_draw_pixel(ul_x - curX, ul_y - curY);
		ili93xx_draw_pixel(ul_x + curY, ul_y + curX);
		ili93xx_draw_pixel(ul_x + curY, ul_y - curX);
		ili93xx_draw_pixel(ul_x - curY, ul_y + curX);
		ili93xx_draw_pixel(ul_x - curY, ul_y - curX);

		if (d < 0) {
			d += (curX << 2) + 6;
		} else {
			d += ((curX - curY) << 2) + 10;
			curY--;
		}

		curX++;
	}

	return 0;
}

/**
 * \brief Draw a filled circle on LCD.
 *
 * \param ul_x X coordinate of circle center.
 * \param ul_y Y coordinate of circle center.
 * \param ul_r circle radius.
 *
 * \return 0 if succeeds, otherwise fails.
 */
uint32_t ili93xx_draw_filled_circle(uint32_t ul_x, uint32_t ul_y, uint32_t ul_r)
{
	signed int d;       /* Decision Variable */
	uint32_t dwCurX;    /* Current X Value */
	uint32_t dwCurY;    /* Current Y Value */
	uint32_t dwXmin, dwYmin;

	if (ul_r == 0) {
		return 1;
	}

	d = 3 - (ul_r << 1);
	dwCurX = 0;
	dwCurY = ul_r;

	while (dwCurX <= dwCurY) {
		dwXmin = (dwCurX > ul_x) ? 0 : ul_x - dwCurX;
		dwYmin = (dwCurY > ul_y) ? 0 : ul_y - dwCurY;
		ili93xx_draw_filled_rectangle(dwXmin, dwYmin, ul_x + dwCurX,
				dwYmin);
		ili93xx_draw_filled_rectangle(dwXmin, ul_y + dwCurY,
				ul_x + dwCurX, ul_y + dwCurY);
		dwXmin = (dwCurY > ul_x) ? 0 : ul_x - dwCurY;
		dwYmin = (dwCurX > ul_y) ? 0 : ul_y - dwCurX;
		ili93xx_draw_filled_rectangle(dwXmin, dwYmin, ul_x + dwCurY,
				dwYmin);
		ili93xx_draw_filled_rectangle(dwXmin, ul_y + dwCurX,
				ul_x + dwCurY, ul_y + dwCurX);

		if (d < 0) {
			d += (dwCurX << 2) + 6;
		} else {
			d += ((dwCurX - dwCurY) << 2) + 10;
			dwCurY--;
		}

		dwCurX++;
	}

	return 0;
}

/**
 * \brief Draw an ASCII character on LCD.
 *
 * \param ul_x X coordinate of character upper-left corner.
 * \param ul_y Y coordinate of character upper-left corner.
 * \param uc_c character to print.
 */
static void ili93xx_draw_char(uint32_t ul_x, uint32_t ul_y, uint8_t uc_c)
{
	uint32_t row, col;
	uint32_t offset, offset0, offset1;

	/**
	 * Compute offset according of the specified ASCII character
	 *  Note: the first 32 characters of the ASCII table are not handled
	 */
	offset = ((uint32_t)uc_c - 0x20) * 20;

	for (col = 0; col < 10; col++) {
		/** Compute the first and second byte offset of a column */
		offset0 = offset + col * 2;
		offset1 = offset0 + 1;

		/**
		 * Draw pixel on screen depending on the corresponding bit value
		 * from the charset
		 */
		for (row = 0; row < 8; row++) {
			if ((p_uc_charset10x14[offset0] >> (7 - row)) & 0x1) {
				ili93xx_draw_pixel(ul_x + col, ul_y + row);
			}
		}

		for (row = 0; row < 6; row++) {
			if ((p_uc_charset10x14[offset1] >> (7 - row)) & 0x1) {
				ili93xx_draw_pixel(ul_x + col, ul_y + row + 8);
			}
		}
	}
}

/**
 * \brief Draw a string on LCD.
 *
 * \param ul_x X coordinate of string top-left corner.
 * \param ul_y Y coordinate of string top-left corner.
 * \param p_str String to display.
 */
void ili93xx_draw_string(uint32_t ul_x, uint32_t ul_y, const uint8_t *p_str)
{
	uint32_t xorg = ul_x;

	while (*p_str != 0) {
		/** If newline, jump to the next line (font height + 2) */
		if (*p_str == '\n') {
			ul_y += gfont.height + 2;
			ul_x = xorg;
		} else {
			/**
			 * Draw the character and place cursor right after (font
			 * width + 2)
			 */
			ili93xx_draw_char(ul_x, ul_y, *p_str);
			ul_x += gfont.width + 2;
		}

		p_str++;
	}
}

/**
 * \brief Draw a pixmap on LCD.
 *
 * \param ul_x X coordinate of upper-left corner on LCD.
 * \param ul_y Y coordinate of upper-left corner on LCD.
 * \param ul_width width of the picture.
 * \param ul_height height of the picture.
 * \param p_ul_pixmap pixmap of the image.
 */
void ili93xx_draw_pixmap(uint32_t ul_x, uint32_t ul_y, uint32_t ul_width,
		uint32_t ul_height, const ili93xx_color_t *p_ul_pixmap)
{
	uint32_t size;
	uint32_t dwX1, dwY1, dwX2, dwY2;
	dwX1 = ul_x;
	dwY1 = ul_y;
	dwX2 = ul_x + ul_width;
	dwY2 = ul_y + ul_height;

	/** Swap coordinates if necessary */
	ili93xx_check_box_coordinates(&dwX1, &dwY1, &dwX2, &dwY2);

	/** Determine the refresh window area */
	ili93xx_set_window(dwX1, dwY1, (dwX2 - dwX1 + 1), (dwY2 - dwY1 + 1));

	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		/** Set cursor */
		ili93xx_set_cursor_position(dwX1, dwY1);
		/** Prepare to write in GRAM */
		ili93xx_write_ram_prepare();

		size = (dwX2 - dwX1) * (dwY2 - dwY1);

		ili93xx_write_ram_buffer(p_ul_pixmap, size);

		/** Reset the refresh window area */
		ili93xx_set_window(0, 0, g_ul_lcd_x_length, g_ul_lcd_y_length);
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		/** Prepare to write in GRAM */
		ili93xx_write_ram_prepare();

		size = (dwX2 - dwX1) * (dwY2 - dwY1);

		ili93xx_write_ram_buffer(p_ul_pixmap, size);

		/** Reset the refresh window area */
		ili93xx_set_window(0, 0, g_ul_lcd_x_length, g_ul_lcd_y_length);
	}
}

/**
 * \internal
 * \brief Helper function to send the drawing limits (boundaries) to the display
 *
 * This function is used to send the currently set upper-left and lower-right
 * drawing limits to the display, as set through the various limit functions.
 *
 * \param send_end_limits  True to also send the lower-right drawing limits
 */
static inline void ili93xx_send_draw_limits(const bool send_end_limits)
{
	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		/** Set Horizontal Address Start Position */
		ili93xx_write_register_word(ILI9325_HORIZONTAL_ADDR_START,
				(uint16_t)limit_start_x);

		if (send_end_limits) {
			/** Set Horizontal Address End Position */
			ili93xx_write_register_word(ILI9325_HORIZONTAL_ADDR_END,
					(uint16_t)(limit_end_x));
		}

		/** Set Vertical Address Start Position */
		ili93xx_write_register_word(ILI9325_VERTICAL_ADDR_START,
				(uint16_t)limit_start_y);
		if (send_end_limits) {
			/** Set Vertical Address End Position */
			ili93xx_write_register_word(ILI9325_VERTICAL_ADDR_END,
					(uint16_t)(limit_end_y));
		}

		/** GRAM Horizontal/Vertical Address Set (R20h, R21h) */
		ili93xx_write_register_word(ILI9325_HORIZONTAL_GRAM_ADDR_SET,
				limit_start_x);
		ili93xx_write_register_word(ILI9325_VERTICAL_GRAM_ADDR_SET,
				limit_start_y);

	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		/** Set Horizontal Address Start Position */
		ili93xx_write_register_word(ILI9341_CMD_COLUMN_ADDRESS_SET,
				(uint16_t)limit_start_x);

		if (send_end_limits) {
			/** Set Horizontal Address End Position */
			ili93xx_write_register_word(
					ILI9341_CMD_COLUMN_ADDRESS_SET,
					(uint16_t)(limit_end_x));
		}

		ili93xx_write_register(0, NULL, 0);

		/** Set Vertical Address Start Position */
		ili93xx_write_register_word(ILI9341_CMD_PAGE_ADDRESS_SET,
				(uint16_t)limit_start_y);
		if (send_end_limits) {
			/** Set Vertical Address End Position */
			ili93xx_write_register_word(
					ILI9341_CMD_PAGE_ADDRESS_SET,
					(uint16_t)(limit_end_y));
		}

		ili93xx_write_register(0, NULL, 0);
	}
}

/**
 * \brief Set the display top left drawing limit
 *
 * Use this function to set the top left limit of the drawing limit box.
 *
 * \param x The x coordinate of the top left corner
 * \param y The y coordinate of the top left corner
 */
void ili93xx_set_top_left_limit(ili93xx_coord_t x, ili93xx_coord_t y)
{
	limit_start_x = x;
	limit_start_y = y;

	ili93xx_send_draw_limits(false);
}

/**
 * \brief Set the display bottom right drawing limit
 *
 * Use this function to set the bottom right corner of the drawing limit box.
 *
 * \param x The x coordinate of the bottom right corner
 * \param y The y coordinate of the bottom right corner
 */
void ili93xx_set_bottom_right_limit(ili93xx_coord_t x, ili93xx_coord_t y)
{
	limit_end_x = x;
	limit_end_y = y;

	ili93xx_send_draw_limits(true);
}

/**
 * \brief Set the full display drawing limits
 *
 * Use this function to set the full drawing limit box.
 *
 * \param start_x The x coordinate of the top left corner
 * \param start_y The y coordinate of the top left corner
 * \param end_x The x coordinate of the bottom right corner
 * \param end_y The y coordinate of the bottom right corner
 */
void ili93xx_set_limits(ili93xx_coord_t start_x, ili93xx_coord_t start_y,
		ili93xx_coord_t end_x, ili93xx_coord_t end_y)
{
	limit_start_x = start_x;
	limit_start_y = start_y;
	limit_end_x = end_x;
	limit_end_y = end_y;

	ili93xx_send_draw_limits(true);
}

/**
 * \brief Read a single color from the graphical memory
 *
 * Use this function to read a color from the graphical memory of the
 * controller.
 *
 * \retval ili93xx_color_t The read color pixel
 */
ili93xx_color_t ili93xx_read_gram(void)
{
	uint8_t value[3];
	ili93xx_color_t color;

	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		LCD_IR(0);
		/** Write Data to GRAM (R22h) */
		LCD_IR(ILI9325_GRAM_DATA_REG);
		/** two dummy read */
		value[0] = LCD_RD();
		value[1] = LCD_RD();
		/** data upper byte */
		value[0] = LCD_RD();
		/** data lower byte */
		value[1] = LCD_RD();

		/** Convert RGB565 to RGB888 */
		/** For BGR format */
		color = ((value[0] & 0xF8)) |
				((value[0] & 0x07) << 13) | ((value[1] & 0xE0) << 5) |
				((value[1] & 0x1F) << 19);
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		LCD_IR(0);
		/** Write Data to GRAM (R2Eh) */
		LCD_IR(ILI9341_CMD_MEMORY_READ);
		/** dummy read */
		value[0] = LCD_RD();
		/** the highest byte - R byte*/
		value[0] = LCD_RD();
		/** the middle byte - G byte*/
		value[1] = LCD_RD();
		/** the lowest byte - B byte*/
		value[2] = LCD_RD();
		/** combine R, G, B byte to a color value */
		color = (value[0] << 16) | (value[1] << 8) | value[2];
	}
	return color;
}

/**
 * \brief Write the graphical memory with a single color pixel
 *
 * Use this function to write a single color pixel to the controller memory.
 *
 * \param color The color pixel to write to the screen
 */
void ili93xx_write_gram(ili93xx_color_t color)
{
	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		LCD_IR(0);
		/** Write Data to GRAM (R22h) */
		LCD_IR(ILI9325_GRAM_DATA_REG);
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		/** memory write command (R2Ch)*/
		LCD_IR(ILI9341_CMD_MEMORY_WRITE);
		LCD_IR(0);
		LCD_IR(ILI9341_CMD_WRITE_MEMORY_CONTINUE);
	}
	LCD_WD((color >> 16) & 0xFF);
	LCD_WD((color >> 8) & 0xFF);
	LCD_WD(color & 0xFF);
}

/**
 * \brief Copy pixels from SRAM to the screen
 *
 * Used to copy a large quantitative of data to the screen in one go.
 *
 * \param pixels Pointer to the pixel data
 * \param count Number of pixels to copy to the screen
 */
void ili93xx_copy_pixels_to_screen(const ili93xx_color_t *pixels,
		uint32_t count)
{
	/** Sanity check to make sure that the pixel count is not zero */
	Assert(count > 0);

	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		LCD_IR(0);
		LCD_IR(ILI9325_GRAM_DATA_REG);
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		LCD_IR(ILI9341_CMD_MEMORY_WRITE);
		LCD_IR(0);
		LCD_IR(ILI9341_CMD_WRITE_MEMORY_CONTINUE);
	}

	while (count--) {
		LCD_WD((*pixels >> 16) & 0xFF);
		LCD_WD((*pixels >> 8) & 0xFF);
		LCD_WD(*pixels & 0xFF);
		pixels++;
	}
}

/**
 * \brief Copy pixels from SRAM to the screen
 *
 * Used to copy a large quantitative of data to the screen in one go.
 *
 * \param pixels Pointer to the pixel data
 * \param count Number of pixels to copy to the screen
 */
void ili93xx_copy_raw_pixel_24bits_to_screen(const uint8_t *raw_pixels,
		uint32_t count)
{
	ili93xx_color_t pixels;

	/** Sanity check to make sure that the pixel count is not zero */
	Assert(count > 0);

	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		LCD_IR(0);
		LCD_IR(ILI9325_GRAM_DATA_REG);
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		LCD_IR(ILI9341_CMD_MEMORY_WRITE);
		LCD_IR(0);
		LCD_IR(ILI9341_CMD_WRITE_MEMORY_CONTINUE);
	}
	while (count--) {
		pixels = (*raw_pixels)  |
				(*(raw_pixels +1)) << 8 |
				(*(raw_pixels + 2)) << 16;
		LCD_WD((pixels >> 16) & 0xFF);
		LCD_WD((pixels >> 8) & 0xFF);
		LCD_WD(pixels & 0xFF);
		raw_pixels += 3;
	}
}

/**
 * \brief Set a given number of pixels to the same color
 *
 * Use this function to write a certain number of pixels to the same color
 * within a set limit.
 *
 * \param color The color to write to the display
 * \param count The number of pixels to write with this color
 */
void ili93xx_duplicate_pixel(const ili93xx_color_t color, uint32_t count)
{
	/** Sanity check to make sure that the pixel count is not zero */
	Assert(count > 0);

	if (g_uc_device_type == DEVICE_TYPE_ILI9325) {
		/** Write Data to GRAM (R22h) */
		LCD_IR(0);
		LCD_IR(ILI9325_GRAM_DATA_REG);
	} else if (g_uc_device_type == DEVICE_TYPE_ILI9341) {
		LCD_IR(ILI9341_CMD_MEMORY_WRITE);
		LCD_IR(0);
		LCD_IR(ILI9341_CMD_WRITE_MEMORY_CONTINUE);
	}

	while (count--) {
		LCD_WD((color >> 16) & 0xFF);
		LCD_WD((color >> 8) & 0xFF);
		LCD_WD(color & 0xFF);
	}
}

/**
 * \brief Copy pixels from the screen to a pixel buffer
 *
 * Use this function to copy pixels from the display to an internal SRAM buffer.
 *
 * \param pixels Pointer to the pixel buffer to read to
 * \param count Number of pixels to read
 */
void ili93xx_copy_pixels_from_screen(ili93xx_color_t *pixels, uint32_t count)
{
	/** Remove warnings */
	UNUSED(pixels);
	UNUSED(count);
}

/**
 * \}
 */
