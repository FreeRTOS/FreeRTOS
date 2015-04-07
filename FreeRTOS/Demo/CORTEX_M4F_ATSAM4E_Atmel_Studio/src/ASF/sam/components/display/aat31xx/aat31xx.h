/**
 * \file
 *
 * \brief API driver for component aat31xx.
 *
 * Copyright (c) 2011-2012 Atmel Corporation. All rights reserved.
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

#ifndef AAT31XX_H_INCLUDED
#define AAT31XX_H_INCLUDED

#include "compiler.h"
#include "conf_board.h"

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/// @endcond

/* The minimum, average and maximum brightness level values */
#ifdef CONF_BOARD_AAT3155
#define AAT31XX_MIN_BACKLIGHT_LEVEL           1
#define AAT31XX_AVG_BACKLIGHT_LEVEL           8
#define AAT31XX_MAX_BACKLIGHT_LEVEL           16
#endif
#ifdef CONF_BOARD_AAT3193
#define AAT31XX_MIN_BACKLIGHT_LEVEL           1
#define AAT31XX_AVG_BACKLIGHT_LEVEL           8
#define AAT31XX_MAX_BACKLIGHT_LEVEL           16
#endif
#ifdef CONF_BOARD_AAT3194
#define AAT31XX_MIN_BACKLIGHT_LEVEL           1
#define AAT31XX_AVG_BACKLIGHT_LEVEL           25
#define AAT31XX_MAX_BACKLIGHT_LEVEL           32
#endif

/* No component found */
#ifndef AAT31XX_MIN_BACKLIGHT_LEVEL
#warning Cannot configure AAT31XX. The component must be declared in conf_board.h first!
#define AAT31XX_MIN_BACKLIGHT_LEVEL           0
#define AAT31XX_AVG_BACKLIGHT_LEVEL           0
#define AAT31XX_MAX_BACKLIGHT_LEVEL           0
#endif

void aat31xx_set_backlight(uint32_t ul_level);
void aat31xx_disable_backlight(void);

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/// @endcond

#endif /* AAT31XX_H_INCLUDED */
