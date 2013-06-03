/*
 * @brief LCD controller Registers and control functions
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
 * All rights reserved.
 *
 * @par
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licensor disclaim any and
 * all warranties, express or implied, including all implied warranties of
 * merchantability, fitness for a particular purpose and non-infringement of
 * intellectual property rights.  NXP Semiconductors assumes no responsibility
 * or liability for the use of the software, conveys no license or rights under any
 * patent, copyright, mask work right, or any other intellectual property rights in
 * or to any products. NXP Semiconductors reserves the right to make changes
 * in the software without notification. NXP Semiconductors also makes no
 * representation or warranty that such application will be suitable for the
 * specified use without further testing or modification.
 *
 * @par
 * Permission to use, copy, modify, and distribute this software and its
 * documentation is hereby granted, under NXP Semiconductors' and its
 * licensor's relevant copyrights in the software, without fee, provided that it
 * is used in conjunction with NXP Semiconductors microcontrollers.  This
 * copyright, permission, and disclaimer notice must appear in all copies of
 * this code.
 */

#ifndef __LCD_001_H_
#define __LCD_001_H_

#include "sys_config.h"
#include "cmsis.h"

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup IP_LCD_001 IP: LCD register block and driver
 * @ingroup IP_Drivers
 * @{
 */

/**
 * @brief LCD Controller register block structure
 */
typedef struct {				/*!< LCD Structure          */
	__IO uint32_t  TIMH;		/*!< Horizontal Timing Control register */
	__IO uint32_t  TIMV;		/*!< Vertical Timing Control register */
	__IO uint32_t  POL;			/*!< Clock and Signal Polarity Control register */
	__IO uint32_t  LE;			/*!< Line End Control register */
	__IO uint32_t  UPBASE;		/*!< Upper Panel Frame Base Address register */
	__IO uint32_t  LPBASE;		/*!< Lower Panel Frame Base Address register */
	__IO uint32_t  CTRL;		/*!< LCD Control register   */
	__IO uint32_t  INTMSK;		/*!< Interrupt Mask register */
	__I  uint32_t  INTRAW;		/*!< Raw Interrupt Status register */
	__I  uint32_t  INTSTAT;		/*!< Masked Interrupt Status register */
	__O  uint32_t  INTCLR;		/*!< Interrupt Clear register */
	__I  uint32_t  UPCURR;		/*!< Upper Panel Current Address Value register */
	__I  uint32_t  LPCURR;		/*!< Lower Panel Current Address Value register */
	__I  uint32_t  RESERVED0[115];
	__IO uint16_t PAL[256];		/*!< 256x16-bit Color Palette registers */
	__I  uint32_t  RESERVED1[256];
	__IO uint32_t CRSR_IMG[256];/*!< Cursor Image registers */
	__IO uint32_t  CRSR_CTRL;	/*!< Cursor Control register */
	__IO uint32_t  CRSR_CFG;	/*!< Cursor Configuration register */
	__IO uint32_t  CRSR_PAL0;	/*!< Cursor Palette register 0 */
	__IO uint32_t  CRSR_PAL1;	/*!< Cursor Palette register 1 */
	__IO uint32_t  CRSR_XY;		/*!< Cursor XY Position register */
	__IO uint32_t  CRSR_CLIP;	/*!< Cursor Clip Position register */
	__I  uint32_t  RESERVED2[2];
	__IO uint32_t  CRSR_INTMSK;	/*!< Cursor Interrupt Mask register */
	__O  uint32_t  CRSR_INTCLR;	/*!< Cursor Interrupt Clear register */
	__I  uint32_t  CRSR_INTRAW;	/*!< Cursor Raw Interrupt Status register */
	__I  uint32_t  CRSR_INTSTAT;/*!< Cursor Masked Interrupt Status register */
} IP_LCD_001_T;

/**
 * @brief LCD Palette entry format
 */
typedef struct {
	uint32_t Rl : 5;
	uint32_t Gl : 5;
	uint32_t Bl : 5;
	uint32_t Il : 1;
	uint32_t Ru : 5;
	uint32_t Gu : 5;
	uint32_t Bu : 5;
	uint32_t Iu : 1;
} LCD_PALETTE_ENTRY_T;

/**
 * @brief LCD Panel type
 */
typedef enum IP_LCD_PANEL_OPT {
	LCD_TFT = 0x02,		/*!< standard TFT */
	LCD_MONO_4 = 0x01,	/*!< 4-bit STN mono */
	LCD_MONO_8 = 0x05,	/*!< 8-bit STN mono */
	LCD_CSTN = 0x00		/*!< color STN */
} IP_LCD_PANEL_OPT_T;

/**
 * @brief LCD Color Format
 */
typedef enum IP_LCD_COLOR_FORMAT_OPT {
	LCD_COLOR_FORMAT_RGB = 0,
	LCD_COLOR_FORMAT_BGR
} IP_LCD_COLOR_FORMAT_OPT_T;

/** LCD Interrupt control mask register bits */
#define LCD_INTMSK_FUFIM   0x2	/*!< FIFO underflow interrupt enable */
#define LCD_INTMSK_LNBUIM  0x4	/*!< LCD next base address update interrupt enable */
#define LCD_INTMSK_VCOMPIM 0x8	/*!< Vertical compare interrupt enable */
#define LCD_INTMSK_BERIM   0x10	/*!< AHB master error interrupt enable */

#define CLCDC_LCDCTRL_ENABLE    _BIT(0)		/*!< LCD control enable bit */
#define CLCDC_LCDCTRL_PWR       _BIT(11)	/*!< LCD control power enable bit */

/**
 * @brief A structure for LCD Configuration
 */
typedef struct {
	uint8_t  HBP;	/*!< Horizontal back porch in clocks */
	uint8_t  HFP;	/*!< Horizontal front porch in clocks */
	uint8_t  HSW;	/*!< HSYNC pulse width in clocks */
	uint16_t PPL;	/*!< Pixels per line */
	uint8_t  VBP;	/*!< Vertical back porch in clocks */
	uint8_t  VFP;	/*!< Vertical front porch in clocks */
	uint8_t  VSW;	/*!< VSYNC pulse width in clocks */
	uint16_t LPP;	/*!< Lines per panel */
	uint8_t  IOE;	/*!< Invert output enable, 1 = invert */
	uint8_t  IPC;	/*!< Invert panel clock, 1 = invert */
	uint8_t  IHS;	/*!< Invert HSYNC, 1 = invert */
	uint8_t  IVS;	/*!< Invert VSYNC, 1 = invert */
	uint8_t  ACB;	/*!< AC bias frequency in clocks (not used) */
	uint8_t  BPP;	/*!< Maximum bits per pixel the display supports */
	IP_LCD_PANEL_OPT_T  LCD;	/*!< LCD panel type */
	IP_LCD_COLOR_FORMAT_OPT_T  color_format;	/*!<BGR or RGB */
	uint8_t  Dual;	/*!< Dual panel, 1 = dual panel display */
} LCD_Config_T;

/**
 * @brief LCD Cursor Size
 */
typedef enum IP_LCD_CURSOR_SIZE_OPT {
	LCD_CURSOR_32x32 = 0,
	LCD_CURSOR_64x64
} IP_LCD_CURSOR_SIZE_OPT_T;

/**
 * @brief	Enable Controller Interrupt
 * @param	pLCD	: pointer to LCD Controller Reg Struct
 * @param	ints	: OR'ed interrupt bits to enable
 * @return	None
 */
STATIC INLINE void IP_LCD_EnableInts(IP_LCD_001_T *pLCD, uint32_t ints)
{
	pLCD->INTMSK = ints;
}

/**
 * @brief	Disable Controller Interrupt
 * @param	pLCD	: pointer to LCD Controller Reg Struct
 * @param	ints	: OR'ed interrupt bits to disable
 * @return	None
 */
STATIC INLINE void IP_LCD_DisableInts(IP_LCD_001_T *pLCD, uint32_t ints)
{
	pLCD->INTMSK = pLCD->INTMSK & ~(ints);
}

/**
 * @brief	Clear Controller Interrupt
 * @param	pLCD	: pointer to LCD Controller Reg Struct
 * @param	ints	: OR'ed interrupt bits to clear
 * @return	None
 */
STATIC INLINE void IP_LCD_ClearInts(IP_LCD_001_T *pLCD, uint32_t ints)
{
	pLCD->INTCLR = pLCD->INTMSK & (ints);
}

/**
 * @brief	Power-on the LCD Panel (power pin)
 * @param	pLCD	: pointer to LCD Controller Reg Struct
 * @return	None
 */
STATIC INLINE void IP_LCD_PowerOn(IP_LCD_001_T *pLCD) {
	volatile int i;
	pLCD->CTRL |= CLCDC_LCDCTRL_PWR;
	for (i = 0; i < 1000000; i++) {}
	pLCD->CTRL |= CLCDC_LCDCTRL_ENABLE;
}

/**
 * @brief	Power-off the LCD Panel (power pin)
 * @param	pLCD	: pointer to LCD Controller Reg Struct
 * @return	None
 */
STATIC INLINE void IP_LCD_PowerOff(IP_LCD_001_T *pLCD) {
	volatile int i;
	pLCD->CTRL &= ~CLCDC_LCDCTRL_PWR;
	for (i = 0; i < 1000000; i++) {}
	pLCD->CTRL &= ~CLCDC_LCDCTRL_ENABLE;
}

/**
 * @brief	Enable the LCD Controller
 * @param	pLCD	: pointer to LCD Controller Reg Struct
 * @return	None
 */
STATIC INLINE void IP_LCD_Enable(IP_LCD_001_T *pLCD) {
	pLCD->CTRL |= CLCDC_LCDCTRL_ENABLE;
}

/**
 * @brief	Enable the LCD Controller
 * @param	pLCD	: pointer to LCD Controller Reg Struct
 * @return	None
 */
STATIC INLINE void IP_LCD_Disable(IP_LCD_001_T *pLCD) {
	pLCD->CTRL &= ~CLCDC_LCDCTRL_ENABLE;
}

/**
 * @brief	Set LCD Upper Panel Frame Buffer for Single Panel or Upper Panel Frame
 *			Buffer for Dual Panel
 * @param	pLCD	: pointer to LCD Controller Reg Struct
 * @param	buffer	: address of buffer
 * @return	None
 */
STATIC INLINE void IP_LCD_SetUPFrameBuffer(IP_LCD_001_T *pLCD, void *buffer)
{
	pLCD->UPBASE = (uint32_t) buffer;
}

/**
 * @brief	Set LCD Lower Panel Frame Buffer for Dual Panel
 * @param	pLCD	: pointer to LCD Controller Reg Struct
 * @param	buffer	: address of buffer
 * @return	None
 */
STATIC INLINE void IP_LCD_SetLPFrameBuffer(IP_LCD_001_T *pLCD, void *buffer)
{
	pLCD->LPBASE = (uint32_t) buffer;
}

/**
 * @brief	Configure Cursor
 * @param	pLCD	: pointer to LCD Controller Reg Struct
 * @param	cursor_size	: specify size of cursor
 *                  - LCD_CURSOR_32x32	:cursor size is 32x32 pixels
 *                  - LCD_CURSOR_64x64	:cursor size is 64x64 pixels
 * @param	sync		: cursor sync mode
 *                  - TRUE	:cursor sync to the frame sync pulse
 *                  - FALSE	:cursor async mode
 * @return	None
 */
STATIC INLINE void IP_LCD_Cursor_Config(IP_LCD_001_T *pLCD, IP_LCD_CURSOR_SIZE_OPT_T cursor_size, bool sync)
{
	pLCD->CRSR_CFG = ((sync ? 1 : 0) << 1) | cursor_size;
}

/**
 * @brief	Get Internal Cursor Image Buffer Address
 * @param	pLCD		: pointer to LCD Controller Reg Struct
 * @param	cursor_num	: specify number of cursor is going to be written
 *							this param must < 4
 * @return	Cursor Image Buffer Address
 */
STATIC INLINE void *IP_LCD_Cursor_GetImageBufferAddress(IP_LCD_001_T *pLCD, uint8_t cursor_num)
{
	return (void *) &(pLCD->CRSR_IMG[cursor_num * 64]);
}

/**
 * @brief	Enable Cursor
 * @param	pLCD		: pointer to LCD Controller Reg Struct
 * @param	cursor_num	: specify number of cursor is going to be written
 *							this param must < 4
 * @return	None
 */
STATIC INLINE void IP_LCD_Cursor_Enable(IP_LCD_001_T *pLCD, uint8_t cursor_num) {
	pLCD->CRSR_CTRL = (cursor_num << 4) | 1;
}

/**
 * @brief	Disable Cursor
 * @param	pLCD		: pointer to LCD Controller Reg Struct
 * @param	cursor_num	: specify number of cursor is going to be written
 *							this param must < 4
 * @return	None
 */
STATIC INLINE void IP_LCD_Cursor_Disable(IP_LCD_001_T *pLCD, uint8_t cursor_num) {
	pLCD->CRSR_CTRL = (cursor_num << 4);
}

/**
 * @brief	Load Cursor Palette
 * @param	pLCD			: pointer to LCD Controller Reg Struct
 * @param	palette_color	: cursor palette 0 value
 * @return	None
 */
STATIC INLINE void IP_LCD_Cursor_LoadPalette0(IP_LCD_001_T *pLCD, uint32_t palette_color)
{
	/* 7:0 - Red
	   15:8 - Green
	   23:16 - Blue
	   31:24 - Not used*/
	pLCD->CRSR_PAL0 = (uint32_t) palette_color;
}

/**
 * @brief	Load Cursor Palette
 * @param	pLCD			: pointer to LCD Controller Reg Struct
 * @param	palette_color	: cursor palette 1 value
 * @return	None
 */
STATIC INLINE void IP_LCD_Cursor_LoadPalette1(IP_LCD_001_T *pLCD, uint32_t palette_color)
{
	/* 7:0 - Red
	       15:8 - Green
	       23:16 - Blue
	       31:24 - Not used*/
	pLCD->CRSR_PAL1 = (uint32_t) palette_color;

}

/**
 * @brief	Set Cursor Position
 * @param	pLCD	: pointer to LCD Controller Reg Struct
 * @param	x		: horizontal position
 * @param	y		: vertical position
 * @return	None
 */
STATIC INLINE void IP_LCD_Cursor_SetPos(IP_LCD_001_T *pLCD, uint16_t x, uint16_t y)
{
	pLCD->CRSR_XY = (x & 0x3FF) | ((y & 0x3FF) << 16);
}

/**
 * @brief	Set Cursor Clipping Position
 * @param	pLCD	: pointer to LCD Controller Reg Struct
 * @param	x		: horizontal position, should be in range: 0..63
 * @param	y		: vertical position, should be in range: 0..63
 * @return	None
 */
STATIC INLINE void IP_LCD_Cursor_SetClip(IP_LCD_001_T *pLCD, uint16_t x, uint16_t y)
{
	pLCD->CRSR_CLIP = (x & 0x3F) | ((y & 0x3F) << 8);
}

/**
 * @brief	Load a color Palette entry
 * @param	pLCD			: pointer to LCD Controller Reg Struct
 * @param	palette_addr	: Address of palette table to load from
 * @param	index			: palette entry index to load
 * @return	None
 */
STATIC INLINE void IP_LCD_Color_LoadPalette(IP_LCD_001_T *pLCD, uint32_t *palette_addr, uint32_t index)
{
	pLCD->PAL[index] = *(uint32_t *) palette_addr;
}

/**
 * @brief	Initialize the LCD controller
 * @param	pLCD				: pointer to LCD Controller Reg Struct
 * @param	LCD_ConfigStruct	: Pointer to LCD configuration
 * @return  LCD_FUNC_OK is executed successfully or LCD_FUNC_ERR on error
 */
void IP_LCD_Init(IP_LCD_001_T *pLCD, LCD_Config_T *LCD_ConfigStruct);

/**
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __LCD_001_H_ */
