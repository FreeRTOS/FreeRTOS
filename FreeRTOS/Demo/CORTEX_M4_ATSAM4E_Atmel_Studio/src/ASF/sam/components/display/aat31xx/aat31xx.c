/**
 * \file
 *
 * \brief API driver for component aat31xx.
 *
 * Copyright (c) 2011-2013 Atmel Corporation. All rights reserved.
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
 * \defgroup aat31xx_display_group Display - AAT31XX Controller
 *
 * Low-level driver for the AAT31XX LCD backlight controller. This driver provides access to the main
 * features of the AAT31XX controller.
 *
 * \{
 */

#include "board.h"
#include "ioport.h"
#include "aat31xx.h"
#include "conf_aat31xx.h"

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/// @endcond

#define DELAY_PULSE      (0x18u)
#define DELAY_ENABLE     (0x20000u)
#define DELAY_DISABLE    (0x20000u)

/**
 * \brief Set the LCD backlight level.
 *
 * \param ul_level backlight level.
 *
 * \note pin BOARD_AAT31XX_SET_GPIO must be configured before calling aat31xx_set_backlight.
 */
void aat31xx_set_backlight(uint32_t ul_level)
{
	volatile uint32_t ul_delay;
	uint32_t i;

#ifdef CONF_BOARD_AAT3155
	ul_level = AAT31XX_MAX_BACKLIGHT_LEVEL - ul_level + 1;
#endif

#ifdef CONF_BOARD_AAT3193
	ul_level = AAT31XX_MAX_BACKLIGHT_LEVEL - ul_level + 1;
#endif

	/* Ensure valid level */
	ul_level = (ul_level > AAT31XX_MAX_BACKLIGHT_LEVEL) ? AAT31XX_MAX_BACKLIGHT_LEVEL : ul_level;
	ul_level = (ul_level < AAT31XX_MIN_BACKLIGHT_LEVEL) ? AAT31XX_MIN_BACKLIGHT_LEVEL : ul_level;

	/* Set new backlight level */
	for (i = 0; i < ul_level; i++) {
		ioport_set_pin_level(BOARD_AAT31XX_SET_GPIO, IOPORT_PIN_LEVEL_LOW);
		ul_delay = DELAY_PULSE;
		while (ul_delay--) {
		}

		ioport_set_pin_level(BOARD_AAT31XX_SET_GPIO, IOPORT_PIN_LEVEL_HIGH);

		ul_delay = DELAY_PULSE;
		while (ul_delay--) {
		}
	}

	ul_delay = DELAY_ENABLE;
	while (ul_delay--) {
	}
}

/**
 * \brief Switch off backlight.
 */
void aat31xx_disable_backlight(void)
{
	volatile uint32_t ul_delay;

	ioport_set_pin_level(BOARD_AAT31XX_SET_GPIO, IOPORT_PIN_LEVEL_LOW);

	ul_delay = DELAY_DISABLE;
	while (ul_delay--) {
	}
}

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/// @endcond

/**
 * \}
 */
