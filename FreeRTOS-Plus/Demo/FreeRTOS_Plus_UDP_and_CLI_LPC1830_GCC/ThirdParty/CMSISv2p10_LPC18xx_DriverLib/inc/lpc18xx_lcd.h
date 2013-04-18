/**********************************************************************
* $Id$		lpc18xx_lcd.h		2011-06-02
*//**
* @file		lpc18xx_lcd.h
* @brief	Contains all macro definitions and function prototypes
* 			support for LCD Driver
* @version	1.0
* @date		02. June. 2011
* @author	NXP MCU SW Application Team
*
* Copyright(C) 2011, NXP Semiconductor
* All rights reserved.
*
***********************************************************************
* Software that is described herein is for illustrative purposes only
* which provides customers with programming information regarding the
* products. This software is supplied "AS IS" without any warranties.
* NXP Semiconductors assumes no responsibility or liability for the
* use of the software, conveys no license or title under any patent,
* copyright, or mask work right to the product. NXP Semiconductors
* reserves the right to make changes in the software without
* notification. NXP Semiconductors also make no representation or
* warranty that such application will be suitable for the specified
* use without further testing or modification.
**********************************************************************/

/* Peripheral group ----------------------------------------------------------- */
/** @defgroup LCD LCD
 * @ingroup LPC1800CMSIS_FwLib_Drivers
 * @{
 */

#ifndef __LPC18XX_LCD_H_
#define __LPC18XX_LCD_H_

/* Includes ------------------------------------------------------------------- */
#include "LPC18xx.h"
#include "lpc_types.h"

#ifdef __cplusplus
extern "C"
{
#endif

/* Private Macros ------------------------------------------------------------- */
/** @defgroup LCD_Private_Macros LCD Private Macros
 * @{
 */

/* --------------------- BIT DEFINITIONS -------------------------------------- */
/* LCD control enable bit */
#define CLCDC_LCDCTRL_ENABLE    _BIT(0)
/* LCD control power enable bit */
#define CLCDC_LCDCTRL_PWR       _BIT(11)

/**
 * @}
 */


/* Public Types --------------------------------------------------------------- */
/** @defgroup LCD_Public_Types LCD Public Types
 * @{
 */

/*********************************************************************//**
 * @brief LCD enumeration
 **********************************************************************/

/** @brief LCD Interrupt Source */
typedef enum{
	LCD_INT_FUF = _BIT(1),		/* FIFO underflow bit */
	LCD_INT_LNBU = _BIT(2),		/* LCD next base address update bit */
	LCD_INT_VCOMP = _BIT(3),	/* vertical compare bit */
	LCD_INT_BER = _BIT(4)		/* AHB master error interrupt bit */
} LCD_INT_SRC;

/** @brief LCD signal polarity */
typedef enum {
	LCD_SIGNAL_ACTIVE_HIGH = 0,
	LCD_SIGNAL_ACTIVE_LOW = 1
} LCD_SIGNAL_POLARITY_OPT;

/** @brief LCD clock edge polarity */
typedef enum {
	LCD_CLK_RISING = 0,
	LCD_CLK_FALLING= 1
} LCD_CLK_EDGE_OPT;

/** @brief LCD bits per pixel and pixel format */
typedef enum {
	LCD_BPP1 = 0,
	LCD_BPP2,
	LCD_BPP4,
	LCD_BPP8,
	LCD_BPP16,
	LCD_BPP24,
	LCD_BPP16_565,
	LCD_BPP12_444
}LCD_PIXEL_FORMAT_OPT;

/** @brief LCD color format */
typedef enum {
	LCD_COLOR_FORMAT_RGB = 0,
	LCD_COLOR_FORMAT_BGR
}LCD_COLOR_FORMAT_OPT;


/*********************************************************************//**
 * @brief LCD structure definitions
 **********************************************************************/
/** @brief LCD Palette entry format */
typedef struct
{
	uint32_t Rl:5;
	uint32_t Gl:5;
	uint32_t Bl:5;
	uint32_t Il:1;
	uint32_t Ru:5;
	uint32_t Gu:5;
	uint32_t Bu:5;
	uint32_t Iu:1;
} LCD_PALETTE_ENTRY_Type;

/** @brief LCD cursor format in 1 byte LBBP */
typedef struct
{
	uint8_t Pixel3:2;
	uint8_t Pixel2:2;
	uint8_t Pixel1:2;
	uint8_t Pixel0:2;
} LCD_CURSOR_PIXEL_Type;

/** @brief LCD cursor size */
typedef enum
{
	LCD_CURSOR_32x32 = 0,
	LCD_CURSOR_64x64
} LCD_CURSOR_SIZE_OPT;

/** @brief LCD panel type */
typedef enum
{
	LCD_TFT = 0x02, 	/* standard TFT */
	LCD_MONO_4 = 0x01,  /* 4-bit STN mono */
	LCD_MONO_8 = 0x05,  /* 8-bit STN mono */
	LCD_CSTN = 0x00     /* color STN */
} LCD_PANEL_OPT;

/** @brief LCD porch configuration structure */
typedef struct {
	uint16_t front;		/* front porch setting in clocks */
	uint16_t back;		/* back porch setting in clocks */
}LCD_PORCHCFG_Type;

/** @brief LCD configuration structure */
typedef struct {
	uint16_t				screen_width;			/* Pixels per line */
	uint16_t				screen_height;			/* Lines per panel */
	LCD_PORCHCFG_Type		horizontal_porch;		/* porch setting for horizontal */
	LCD_PORCHCFG_Type		vertical_porch;			/* porch setting for vertical */
	uint16_t				HSync_pulse_width;		/* HSYNC pulse width in clocks */
	uint16_t				VSync_pulse_width;		/* VSYNC pulse width in clocks */
	uint8_t         		ac_bias_frequency;    	/* AC bias frequency in clocks */
	LCD_SIGNAL_POLARITY_OPT	HSync_pol;				/* HSYNC polarity */
	LCD_SIGNAL_POLARITY_OPT	VSync_pol;				/* VSYNC polarity */
	LCD_CLK_EDGE_OPT		panel_clk_edge;			/* Panel Clock Edge Polarity */
	LCD_SIGNAL_POLARITY_OPT	OE_pol;					/* Output Enable polarity */
	uint32_t				line_end_delay;			/* 0 if not use */
	LCD_PIXEL_FORMAT_OPT	bits_per_pixel;       	/* Maximum bits per pixel the display supports */
	LCD_PANEL_OPT     		lcd_panel_type;       	/* LCD panel type */
	LCD_COLOR_FORMAT_OPT	color_format;			/* BGR or RGB */
	Bool         			dual_panel;           	/* Dual panel, TRUE = dual panel display */
	uint16_t				pcd;
} LCD_CFG_Type;

/**
 * @}
 */

/* Public Functions ----------------------------------------------------------- */
/** @defgroup LCD_Public_Functions LCD Public Functions
 * @{
 */

void LCD_Init(LPC_LCD_Type *LCDx, LCD_CFG_Type *LCD_ConfigStruct);
void LCD_DeInit(LPC_LCD_Type *LCDx);

void LCD_Power(LPC_LCD_Type *LCDx, FunctionalState OnOff);
void LCD_Enable(LPC_LCD_Type *LCDx, FunctionalState EnDis);
void LCD_SetFrameBuffer(LPC_LCD_Type *LCDx, void* buffer);
void LCD_SetLPFrameBuffer(LPC_LCD_Type *LCDx, void* buffer);
void LCD_LoadPalette(LPC_LCD_Type *LCDx, void* palette);
void LCD_SetInterrupt(LPC_LCD_Type *LCDx, LCD_INT_SRC Int);
void LCD_ClrInterrupt(LPC_LCD_Type *LCDx, LCD_INT_SRC Int);
LCD_INT_SRC LCD_GetInterrupt(LPC_LCD_Type *LCDx);

void LCD_Cursor_Config(LPC_LCD_Type *LCDx, LCD_CURSOR_SIZE_OPT cursor_size, Bool sync);
void LCD_Cursor_WriteImage(LPC_LCD_Type *LCDx, uint8_t cursor_num, void* Image);
void* LCD_Cursor_GetImageBufferAddress(LPC_LCD_Type *LCDx, uint8_t cursor_num);
void LCD_Cursor_Enable(LPC_LCD_Type *LCDx, uint8_t cursor_num, FunctionalState OnOff);
void LCD_Cursor_LoadPalette0(LPC_LCD_Type *LCDx, uint32_t palette_color);
void LCD_Cursor_LoadPalette1(LPC_LCD_Type *LCDx, uint32_t palette_color);
void LCD_Cursor_SetInterrupt(LPC_LCD_Type *LCDx);
void LCD_Cursor_ClrInterrupt(LPC_LCD_Type *LCDx);
void LCD_Cursor_SetPos(LPC_LCD_Type *LCDx, uint16_t x, uint16_t y);
void LCD_Cursor_SetClipPos(LPC_LCD_Type *LCDx, uint16_t x, uint16_t y);

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __LPC18XX_LCD_H_ */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */

