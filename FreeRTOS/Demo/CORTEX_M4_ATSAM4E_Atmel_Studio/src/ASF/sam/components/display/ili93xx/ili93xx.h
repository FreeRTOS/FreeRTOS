/**
 * \file
 *
 * \brief API driver for ili93xx TFT display component.
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

#ifndef ILI93XX_H_INCLUDED
#define ILI93XX_H_INCLUDED

/**
 * \defgroup ili93xx_display_group - LCD with ili93xx component driver
 *
 * This is a driver for LCD with ili93xx. Now this driver supports ili9325 and
 * ili9341.This component is custom LCD used for SAM4E-EK.
 * The driver provides functions for initializtion and control of the LCD.
 *
 * See \ref sam_component_ili93xx_quickstart.
 *
 * \{
 */

#include "compiler.h"
#include "board.h"
#include "conf_ili93xx.h"

/** @cond 0 */
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/** @endcond */

/** Type define for an integer type large enough to store a pixel color. */
typedef uint32_t ili93xx_color_t;

/** Type define for an integer type large enough to store a pixel coordinate.
 */
typedef int16_t ili93xx_coord_t;

/** This macro generates a 16-bit native color for the display from a
 *  24-bit RGB value.
 */
#define ili93xx_COLOR(r, g, b) ((r << 16) | (g << 8) | b)

typedef ili93xx_color_t gfx_color_t;
typedef int16_t gfx_coord_t;

/** ili93xx screen size */
#define ILI93XX_LCD_WIDTH  240
#define ILI93XX_LCD_HEIGHT 320

/** ili93xx ID code */
#define ILI9325_DEVICE_CODE (0x9325u)
#define ILI9341_DEVICE_CODE (0x9341u)
#define DEVICE_TYPE_ILI9325  1
#define DEVICE_TYPE_ILI9341  2
/** Define EBI access for ILI93xx 8-bit System Interface.*/
#if defined(BOARD_ILI93XX_ADDR) && defined (BOARD_ILI93XX_RS)
static inline void LCD_IR(uint8_t lcd_index)
{
	/** ILI9325 index register address */
	*((volatile uint8_t *)(BOARD_ILI93XX_ADDR)) = lcd_index;
}

static inline void LCD_WD(uint8_t lcd_data)
{
	*((volatile uint8_t *)((BOARD_ILI93XX_ADDR) | (BOARD_ILI93XX_RS))) =
																lcd_data;
}

static inline uint8_t LCD_RD(void)
{
	return *((volatile uint8_t *)((BOARD_ILI93XX_ADDR) |(BOARD_ILI93XX_RS)));
}

#else
	#error "Missing module configuration for ILI93xx!"
#endif

/** RGB 24-bits color table definition (RGB888). */
#define COLOR_BLACK          (0x000000u)
#define COLOR_WHITE          (0xFFFFFFu)
#define COLOR_BLUE           (0x0000FFu)
#define COLOR_GREEN          (0x00FF00u)
#define COLOR_RED            (0xFF0000u)
#define COLOR_NAVY           (0x000080u)
#define COLOR_DARKBLUE       (0x00008Bu)
#define COLOR_DARKGREEN      (0x006400u)
#define COLOR_DARKCYAN       (0x008B8Bu)
#define COLOR_CYAN           (0x00FFFFu)
#define COLOR_TURQUOISE      (0x40E0D0u)
#define COLOR_INDIGO         (0x4B0082u)
#define COLOR_DARKRED        (0x800000u)
#define COLOR_OLIVE          (0x808000u)
#define COLOR_GRAY           (0x808080u)
#define COLOR_SKYBLUE        (0x87CEEBu)
#define COLOR_BLUEVIOLET     (0x8A2BE2u)
#define COLOR_LIGHTGREEN     (0x90EE90u)
#define COLOR_DARKVIOLET     (0x9400D3u)
#define COLOR_YELLOWGREEN    (0x9ACD32u)
#define COLOR_BROWN          (0xA52A2Au)
#define COLOR_DARKGRAY       (0xA9A9A9u)
#define COLOR_SIENNA         (0xA0522Du)
#define COLOR_LIGHTBLUE      (0xADD8E6u)
#define COLOR_GREENYELLOW    (0xADFF2Fu)
#define COLOR_SILVER         (0xC0C0C0u)
#define COLOR_LIGHTGREY      (0xD3D3D3u)
#define COLOR_LIGHTCYAN      (0xE0FFFFu)
#define COLOR_VIOLET         (0xEE82EEu)
#define COLOR_AZUR           (0xF0FFFFu)
#define COLOR_BEIGE          (0xF5F5DCu)
#define COLOR_MAGENTA        (0xFF00FFu)
#define COLOR_TOMATO         (0xFF6347u)
#define COLOR_GOLD           (0xFFD700u)
#define COLOR_ORANGE         (0xFFA500u)
#define COLOR_SNOW           (0xFFFAFAu)
#define COLOR_YELLOW         (0xFFFF00u)

/**
 * Input parameters when initializing ili9325 driver.
 */
struct ili93xx_opt_t {
	/** LCD width in pixel*/
	uint32_t ul_width;
	/** LCD height in pixel*/
	uint32_t ul_height;
	/** LCD foreground color*/
	uint32_t foreground_color;
	/** LCD background color*/
	uint32_t background_color;
};

/**
 * Font structure
 */
struct ili93xx_font {
	/** Font width in pixels. */
	uint8_t width;
	/** Font height in pixels. */
	uint8_t height;
};

/**
 * Display direction option
 */
enum ili93xx_display_direction {
	LANDSCAPE  = 0,
	PORTRAIT   = 1
};

/**
 * Shift direction option
 */
enum ili93xx_shift_direction {
	H_INCREASE  = 0,
	H_DECREASE  = 1
};

/**
 * Scan direction option
 */
enum ili93xx_scan_direction {
	V_INCREASE  = 0,
	V_DEREASE   = 1
};

uint32_t ili93xx_init(struct ili93xx_opt_t *p_opt);
void ili93xx_display_on(void);
void ili93xx_display_off(void);
void ili93xx_set_foreground_color(ili93xx_color_t ul_color);
void ili93xx_fill(ili93xx_color_t ul_color);
void ili93xx_set_window(uint32_t ul_x, uint32_t ul_y,
		uint32_t ul_width, uint32_t ul_height);
void ili93xx_set_cursor_position(uint16_t us_x, uint16_t us_y);
void ili93xx_scroll(int32_t ul_lines);
void ili93xx_enable_scroll(void);
void ili93xx_disable_scroll(void);
void ili93xx_set_display_direction(enum ili93xx_display_direction e_dd,
		enum ili93xx_shift_direction e_shd,
		enum ili93xx_scan_direction e_scd);
uint32_t ili93xx_draw_pixel(uint32_t ul_x, uint32_t ul_y);
ili93xx_color_t ili93xx_get_pixel(uint32_t ul_x, uint32_t ul_y);
void ili93xx_draw_line(uint32_t ul_x1, uint32_t ul_y1,
		uint32_t ul_x2, uint32_t ul_y2);
void ili93xx_draw_rectangle(uint32_t ul_x1, uint32_t ul_y1,
		uint32_t ul_x2, uint32_t ul_y2);
void ili93xx_draw_filled_rectangle(uint32_t ul_x1, uint32_t ul_y1,
		uint32_t ul_x2, uint32_t ul_y2);
uint32_t ili93xx_draw_circle(uint32_t ul_x, uint32_t ul_y, uint32_t ul_r);
uint32_t ili93xx_draw_filled_circle(uint32_t ul_x, uint32_t ul_y,
		uint32_t ul_r);
void ili93xx_draw_string(uint32_t ul_x, uint32_t ul_y, const uint8_t *p_str);
void ili93xx_draw_pixmap(uint32_t ul_x, uint32_t ul_y, uint32_t ul_width,
		uint32_t ul_height, const ili93xx_color_t *p_ul_pixmap);
void ili93xx_set_top_left_limit(ili93xx_coord_t x, ili93xx_coord_t y);
void ili93xx_set_bottom_right_limit(ili93xx_coord_t x, ili93xx_coord_t y);
void ili93xx_set_limits(ili93xx_coord_t start_x, ili93xx_coord_t start_y,
		ili93xx_coord_t end_x, ili93xx_coord_t end_y);
ili93xx_color_t ili93xx_read_gram(void);
void ili93xx_write_gram(ili93xx_color_t color);
void ili93xx_copy_pixels_to_screen(const ili93xx_color_t *pixels,
		uint32_t count);
void ili93xx_copy_raw_pixel_24bits_to_screen(const uint8_t *raw_pixels,
		uint32_t count);
void ili93xx_duplicate_pixel(const ili93xx_color_t color, uint32_t count);
void ili93xx_copy_pixels_from_screen(ili93xx_color_t *pixels, uint32_t count);
uint8_t ili93xx_device_type(void);
void ili93xx_vscroll_area_define(uint16_t us_tfa, uint16_t us_vsa,
		uint16_t us_bfa);
uint8_t ili93xx_device_type_identify(void);

/** @cond 0 */
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/** @endcond */

/**
 * \}
 */

/**
 * \page sam_component_ili93xx_quickstart Quick Start Guide for the ILI93XX
 * LCD Glass component.
 *
 * This is the quick start guide for the \ref ili93xx_display_group, with
 * step-by-step instructions on how to configure and use the driver for
 * a specific use case.The code examples can be copied into e.g the main
 * application loop or any other function that will need to control the
 * ili93xx LCD Glass component module. Now ili9325 and ili9341 are supported.
 *
 * \section ili93xx_qs_use_cases Use cases
 * - \ref ili93xx_basic
 *
 * \section ili93xx_basic ili93xx LCD Glass basic usage
 *
 * This use case will demonstrate how to initialize the ili93xx LCD Glass
 * module.
 *
 *
 * \section ili93xx_basic_setup Setup steps
 *
 * \subsection ili93xx_basic_prereq Prerequisites
 *
 * This module requires the following driver
 * - \ref smc_group
 *
 * \subsection ili93xx_basic_setup_code
 *
 * Add this to the main loop or a setup function:
 * \code
 * struct ili93xx_opt_t g_ili93xx_display_opt;
 * g_ili93xx_display_opt.ul_width = ILI93XX_LCD_WIDTH;
 * g_ili93xx_display_opt.ul_height = ILI93XX_LCD_HEIGHT;
 * g_ili93xx_display_opt.foreground_color = COLOR_BLACK;
 * g_ili93xx_display_opt.background_color = COLOR_WHITE;
 * ili93xx_init(&g_ili93xx_display_opt);
 * \endcode
 *
 * \subsection ili93xx_basic_setup_workflow
 * -\ref ili93xx_basic_setup_code
 *
 * \section ili93xx_basic_usage Usage steps
 *
 * \subsection ili93xx_basic_usage_code
 *
 * -# Set display on
 * \code
 * ili93xx_display_on();
 * \endcode
 *
 * -# Turn display off
 * \code
 * ili93xx_display_off();
 * \endcode
 *
 * -# Draw a pixel
 * \code
 * ili93xx_set_foreground_color(COLOR_RED);
 * ili93xx_draw_pixel(60, 60);
 * \endcode
 *
 * -# Draw a line and circle
 * \code
 * ili93xx_set_foreground_color(COLOR_BLUE);
 * ili93xx_draw_circle(180, 160, 40);
 * ili93xx_set_foreground_color(COLOR_VIOLET);
 * ili93xx_draw_line(0, 0, 240, 320);
 * \endcode
 *
 * -# Draw a string of text
 * \code
 * ili93xx_set_foreground_color(COLOR_BLACK);
 * ili93xx_draw_string(10, 20, (uint8_t *)"ili93xx_lcd example");
 * \endcode
 *
 * -# Fill a rectangle with one certain color
 * \code
 * ili93xx_set_foreground_color(COLOR_BLUE);
 * ili93xx_draw_filled_rectangle(0, 0, ILI93XX_LCD_WIDTH, ILI93XX_LCD_HEIGHT);
 * \endcode
 *
 * -# Get device type
 * \code
 * ili93xx_device_type();
 * \endcode
 */

#endif /* ILI93XX_H_INCLUDED */
