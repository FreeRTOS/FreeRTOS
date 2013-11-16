/**
 * \file
 *
 * \brief registers definition for ili9341 TFT display component.
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

#ifndef ILI9341_REGS_H_INCLUDED
#define ILI9341_REGS_H_INCLUDED

/** @cond 0 */
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/** @endcond */

/** ili9341 LCD Registers */

/** Level 1 Commands (from the display Datasheet) */
/** Nop operation*/
#define ILI9341_CMD_NOP                             0x00
/** Software reset*/
#define ILI9341_CMD_SOFTWARE_RESET                  0x01
/** Read Display Identification information*/
#define ILI9341_CMD_READ_DISP_ID                    0x04
/** Read display status*/
#define ILI9341_CMD_READ_DISP_STATUS                0x09
/** Read display power mode*/
#define ILI9341_CMD_READ_DISP_POWER_MODE            0x0A
/** Read display MADCTL*/
#define ILI9341_CMD_READ_DISP_MADCTRL               0x0B
/** Read display pixel format*/
#define ILI9341_CMD_READ_DISP_PIXEL_FORMAT          0x0C
/** Read display image format*/
#define ILI9341_CMD_READ_DISP_IMAGE_FORMAT          0x0D
/** Read display signal mode*/
#define ILI9341_CMD_READ_DISP_SIGNAL_MODE           0x0E
/** read display self-diagnostic resutl*/
#define ILI9341_CMD_READ_DISP_SELF_DIAGNOSTIC       0x0F
/** Enter sleep mode*/
#define ILI9341_CMD_ENTER_SLEEP_MODE                0x10
/** Sleep out*/
#define ILI9341_CMD_SLEEP_OUT                       0x11
/** Partial mode on*/
#define ILI9341_CMD_PARTIAL_MODE_ON                 0x12
/** Normal display mode on*/
#define ILI9341_CMD_NORMAL_DISP_MODE_ON             0x13
/** Display inversion off*/
#define ILI9341_CMD_DISP_INVERSION_OFF              0x20
/** Display inversion on*/
#define ILI9341_CMD_DISP_INVERSION_ON               0x21
/** Gamma set*/
#define ILI9341_CMD_GAMMA_SET                       0x26
/** Display off*/
#define ILI9341_CMD_DISPLAY_OFF                     0x28
/** Display on*/
#define ILI9341_CMD_DISPLAY_ON                      0x29
/** Column address set*/
#define ILI9341_CMD_COLUMN_ADDRESS_SET              0x2A
/** Page address set*/
#define ILI9341_CMD_PAGE_ADDRESS_SET                0x2B
/** Memory write*/
#define ILI9341_CMD_MEMORY_WRITE                    0x2C
/** Color set*/
#define ILI9341_CMD_COLOR_SET                       0x2D
/** Memory read*/
#define ILI9341_CMD_MEMORY_READ                     0x2E
/** Partial area*/
#define ILI9341_CMD_PARTIAL_AREA                    0x30
/** Vertical scrolling definition*/
#define ILI9341_CMD_VERT_SCROLL_DEFINITION          0x33
/** Tearing effect line off*/
#define ILI9341_CMD_TEARING_EFFECT_LINE_OFF         0x34
/** Tearing effect line on*/
#define ILI9341_CMD_TEARING_EFFECT_LINE_ON          0x35

/** Memory Access control*/
#define ILI9341_CMD_MEMORY_ACCESS_CONTROL           0x36
#define ILI9341_CMD_MEMORY_ACCESS_CONTROL_MY        (0x1u << 7)
#define ILI9341_CMD_MEMORY_ACCESS_CONTROL_MX        (0x1u << 6)
#define ILI9341_CMD_MEMORY_ACCESS_CONTROL_MV        (0x1u << 5)
#define ILI9341_CMD_MEMORY_ACCESS_CONTROL_ML        (0x1u << 4)
#define ILI9341_CMD_MEMORY_ACCESS_CONTROL_BGR       (0x1u << 3)
#define ILI9341_CMD_MEMORY_ACCESS_CONTROL_MH        (0x1u << 2)

/** Vetical scrolling start address*/
#define ILI9341_CMD_VERT_SCROLL_START_ADDRESS       0x37
/** Idle mode off*/
#define ILI9341_CMD_IDLE_MODE_OFF                   0x38
/** Idle mode on*/
#define ILI9341_CMD_IDLE_MODE_ON                    0x39
/** Pixel Format set*/
#define ILI9341_CMD_PIXEL_FORMAT_SET                0x3A
/** write memory continue*/
#define ILI9341_CMD_WRITE_MEMORY_CONTINUE           0x3C
/** Read memory continue*/
#define ILI9341_CMD_READ_MEMORY_CONTINUE            0x3E
/** set tear scanline*/
#define ILI9341_CMD_SET_TEAR_SCANLINE               0x44
/** get scanline*/
#define ILI9341_CMD_GET_SCANLINE                    0x45
/** write display brightness*/
#define ILI9341_CMD_WRITE_DISPLAY_BRIGHTNESS        0x51
/** read display brightness*/
#define ILI9341_CMD_READ_DISPLAY_BRIGHTNESS         0x52
/** write control display*/
#define ILI9341_CMD_WRITE_CTRL_DISPLAY              0x53
/** read control display*/
#define ILI9341_CMD_READ_CTRL_DISPLAY               0x54
/** write content adaptive brightness control*/
#define ILI9341_CMD_WRITE_CONTENT_ADAPT_BRIGHTNESS  0x55
/** read content adaptive brightness control*/
#define ILI9341_CMD_READ_CONTENT_ADAPT_BRIGHTNESS   0x56
/** write CABC minimum brightness*/
#define ILI9341_CMD_WRITE_MIN_CAB_LEVEL             0x5E
/** read CABC minimum brightness*/
#define ILI9341_CMD_READ_MIN_CAB_LEVEL              0x5F
/** Read ID1*/
#define ILI9341_CMD_READ_ID1                        0xDA
/** Read ID2*/
#define ILI9341_CMD_READ_ID2                        0xDB
/** Read ID3*/
#define ILI9341_CMD_READ_ID3                        0xDC

/** Level 2 Commands (from the display Datasheet) */
/** RGB interface signal control*/
#define ILI9341_CMD_RGB_SIGNAL_CONTROL              0xB0
/** frame control*/
#define ILI9341_CMD_FRAME_RATE_CONTROL_NORMAL       0xB1
/** frame control in idle mode*/
#define ILI9341_CMD_FRAME_RATE_CONTROL_IDLE_8COLOR  0xB2
/** frame control in partial mode*/
#define ILI9341_CMD_FRAME_RATE_CONTROL_PARTIAL      0xB3
/** display inversion control*/
#define ILI9341_CMD_DISPLAY_INVERSION_CONTROL       0xB4
/** blanking porch control*/
#define ILI9341_CMD_BLANKING_PORCH_CONTROL          0xB5
/** display function control*/
#define ILI9341_CMD_DISPLAY_FUNCTION_CTL            0xB6
#define ILI9341_DISP_FUNC_CTL_REV                   (0x1u << 7)
#define ILI9341_DISP_FUNC_CTL_GS                    (0x1u << 6)
#define ILI9341_DISP_FUNC_CTL_SS                    (0x1u << 5)
#define ILI9341_DISP_FUNC_CTL_SM                    (0x1u << 4)
#define ILI9341_DISP_FUNC_CTL_ISC_POS               0
#define ILI9341_DISP_FUNC_CTL_ISC_MSK               (0x0F << 0)
#define ILI9341_DISP_FUNC_CTL_ISC(value) \
	(ILI9341_DISP_FUNC_CTL_ISC_MSK & \
	(value << ILI9341_DISP_FUNC_CTL_ISC_POS))

/** entry mode set*/
#define ILI9341_CMD_ENTRY_MODE_SET                  0xB7
/** backlight control1*/
#define ILI9341_CMD_BACKLIGHT_CONTROL_1             0xB8
/** backlight control2*/
#define ILI9341_CMD_BACKLIGHT_CONTROL_2             0xB9
/** backlight control3*/
#define ILI9341_CMD_BACKLIGHT_CONTROL_3             0xBA
/** backlight control 4*/
#define ILI9341_CMD_BACKLIGHT_CONTROL_4             0xBB
/** backlight control 5*/
#define ILI9341_CMD_BACKLIGHT_CONTROL_5             0xBC
/** backlight control 7*/
#define ILI9341_CMD_BACKLIGHT_CONTROL_7             0xBE
/** backlight control 8*/
#define ILI9341_CMD_BACKLIGHT_CONTROL_8             0xBF
/** power control 1*/
#define ILI9341_CMD_POWER_CONTROL_1                 0xC0
/** power control 2*/
#define ILI9341_CMD_POWER_CONTROL_2                 0xC1
/** VCOM control 1*/
#define ILI9341_CMD_VCOM_CONTROL_1                  0xC5
/** VCOM control 2*/
#define ILI9341_CMD_VCOM_CONTROL_2                  0xC7
/** Power control A*/
#define ILI9341_CMD_POWER_CONTROL_A                 0xCB
/** Power control B*/
#define ILI9341_CMD_POWER_CONTROL_B                 0xCF
/** NV memory write*/
#define ILI9341_CMD_NVMEM_WRITE                     0xD0
/** NV memory protection key*/
#define ILI9341_CMD_NVMEM_PROTECTION_KEY            0xD1
/** NV memory status read*/
#define ILI9341_CMD_NVMEM_STATUS_READ               0xD2
/** Read ID4*/
#define ILI9341_CMD_READ_ID4                        0xD3
/** positive gamma correction*/
#define ILI9341_CMD_POSITIVE_GAMMA_CORRECTION       0xE0
/** negative gamma correction*/
#define ILI9341_CMD_NEGATIVE_GAMMA_CORRECTION       0xE1
/** digital gamma control 1*/
#define ILI9341_CMD_DIGITAL_GAMMA_CONTROL_1         0xE2
/** digital gamma control 2*/
#define ILI9341_CMD_DIGITAL_GAMMA_CONTROL_2         0xE3
/** driver timing control A*/
#define ILI9341_CMD_DRIVER_TIMING_CTL_A             0xE8
/** driver timing control B*/
#define ILI9341_CMD_DRIVER_TIMING_CTL_B             0xEA
/** power-on sequence control*/
#define ILI9341_CMD_POWER_ON_SEQUENCE_CONTROL       0xED
/** enable 3g gamma control*/
#define ILI9341_CMD_ENABLE_3_GAMMA_CONTROL          0xF2
/** Interface control*/
#define ILI9341_CMD_INTERFACE_CONTROL               0xF6
/** pump ration control*/
#define ILI9341_CMD_PUMP_RATIO_CONTROL              0xF7

#endif /* ILI9341_REGS_H_INCLUDED */
