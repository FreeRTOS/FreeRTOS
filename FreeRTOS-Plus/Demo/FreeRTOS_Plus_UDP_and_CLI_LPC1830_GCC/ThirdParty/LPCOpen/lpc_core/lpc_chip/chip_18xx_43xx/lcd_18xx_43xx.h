/*
 * @brief LPC18xx/43xx LCD chip driver
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

#ifndef __LCD_18XX_43XX_H_
#define __LCD_18XX_43XX_H_

#ifdef __cplusplus
extern "C" {
#endif

/** @defgroup LCD_18XX_43XX CHIP: LPC18xx/43xx LCD driver
 * @ingroup CHIP_18XX_43XX_Drivers
 * @{
 */

/**
 * @brief	Initialize the LCD controller
 * @param	pLCD				: The base of LCD peripheral on the chip
 * @param	LCD_ConfigStruct	: Pointer to LCD configuration
 * @return  LCD_FUNC_OK is executed successfully or LCD_FUNC_ERR on error
 */
void Chip_LCD_Init(LPC_LCD_T *pLCD, LCD_Config_T *LCD_ConfigStruct);

/**
 * @brief	Shutdown the LCD controller
 * @param	pLCD	: The base of LCD peripheral on the chip
 * @return  Nothing
 */
void Chip_LCD_DeInit(LPC_LCD_T *pLCD);

/**
 * @brief	Power-on the LCD Panel (power pin)
 * @param	pLCD	: The base of LCD peripheral on the chip
 * @return	None
 */
STATIC INLINE void Chip_LCD_PowerOn(LPC_LCD_T *pLCD)
{
	IP_LCD_PowerOn(pLCD);
}

/**
 * @brief	Power-off the LCD Panel (power pin)
 * @param	pLCD	: The base of LCD peripheral on the chip
 * @return	None
 */
STATIC INLINE void Chip_LCD_PowerOff(LPC_LCD_T *pLCD)
{
	IP_LCD_PowerOff(pLCD);
}

/**
 * @brief	Enable/Disable the LCD Controller
 * @param	pLCD	: The base of LCD peripheral on the chip
 * @return	None
 */
STATIC INLINE void Chip_LCD_Enable(LPC_LCD_T *pLCD)
{
	IP_LCD_Enable(pLCD);
}

/**
 * @brief	Enable/Disable the LCD Controller
 * @param	pLCD	: The base of LCD peripheral on the chip
 * @return	None
 */
STATIC INLINE void Chip_LCD_Disable(LPC_LCD_T *pLCD)
{
	IP_LCD_Disable(pLCD);
}

/**
 * @brief	Set LCD Upper Panel Frame Buffer for Single Panel or Upper Panel Frame
 *			Buffer for Dual Panel
 * @param	pLCD	: The base of LCD peripheral on the chip
 * @param	buffer	: address of buffer
 * @return	None
 */
STATIC INLINE void Chip_LCD_SetUPFrameBuffer(LPC_LCD_T *pLCD, void *buffer)
{
	IP_LCD_SetUPFrameBuffer(pLCD, buffer);
}

/**
 * @brief	Set LCD Lower Panel Frame Buffer for Dual Panel
 * @param	pLCD	: The base of LCD peripheral on the chip
 * @param	buffer	: address of buffer
 * @return	None
 */
STATIC INLINE void Chip_LCD_SetLPFrameBuffer(LPC_LCD_T *pLCD, void *buffer)
{
	IP_LCD_SetLPFrameBuffer(pLCD, buffer);
}

/**
 * @brief	Configure Cursor
 * @param	pLCD		: The base of LCD peripheral on the chip
 * @param	cursor_size	: specify size of cursor
 *                  - LCD_CURSOR_32x32	:cursor size is 32x32 pixels
 *                  - LCD_CURSOR_64x64	:cursor size is 64x64 pixels
 * @param	sync		: cursor sync mode
 *                  - TRUE	:cursor sync to the frame sync pulse
 *                  - FALSE	:cursor async mode
 * @return	None
 */
void Chip_LCD_Cursor_Config(LPC_LCD_T *pLCD, IP_LCD_CURSOR_SIZE_OPT_T cursor_size, bool sync);

/**
 * @brief	Enable Cursor
 * @param	pLCD		: The base of LCD peripheral on the chip
 * @param	cursor_num	: specify number of cursor is going to be written
 *							this param must < 4
 * @return	None
 */
STATIC INLINE void Chip_LCD_Cursor_Enable(LPC_LCD_T *pLCD, uint8_t cursor_num)
{
	IP_LCD_Cursor_Enable(pLCD, cursor_num);
}

/**
 * @brief	Disable Cursor
 * @param	pLCD		: The base of LCD peripheral on the chip
 * @param	cursor_num	: specify number of cursor is going to be written
 *							this param must < 4
 * @return	None
 */
STATIC INLINE void Chip_LCD_Cursor_Disable(LPC_LCD_T *pLCD, uint8_t cursor_num)
{
	IP_LCD_Cursor_Disable(pLCD, cursor_num);
}

/**
 * @brief	Load Cursor Palette
 * @param	pLCD			: The base of LCD peripheral on the chip
 * @param	palette_color	: cursor palette 0 value
 * @return	None
 */
STATIC INLINE void Chip_LCD_Cursor_LoadPalette0(LPC_LCD_T *pLCD, uint32_t palette_color)
{
	IP_LCD_Cursor_LoadPalette0(pLCD, palette_color);
}

/**
 * @brief	Load Cursor Palette
 * @param	pLCD			: The base of LCD peripheral on the chip
 * @param	palette_color	: cursor palette 1 value
 * @return	None
 */
STATIC INLINE void Chip_LCD_Cursor_LoadPalette1(LPC_LCD_T *pLCD, uint32_t palette_color)
{
	IP_LCD_Cursor_LoadPalette1(pLCD, palette_color);
}

/**
 * @brief	Set Cursor Position
 * @param	pLCD	: The base of LCD peripheral on the chip
 * @param	x		: horizontal position
 * @param	y		: vertical position
 * @return	None
 */
STATIC INLINE void Chip_LCD_Cursor_SetPos(LPC_LCD_T *pLCD, uint16_t x, uint16_t y)
{
	IP_LCD_Cursor_SetPos(pLCD, x, y);
}

/**
 * @brief	Set Cursor Clipping Position
 * @param	pLCD	: The base of LCD peripheral on the chip
 * @param	x		: horizontal position, should be in range: 0..63
 * @param	y		: vertical position, should be in range: 0..63
 * @return	None
 */
STATIC INLINE void Chip_LCD_Cursor_SetClip(LPC_LCD_T *pLCD, uint16_t x, uint16_t y)
{
	IP_LCD_Cursor_SetClip(pLCD, x, y);
}

/**
 * @brief	Enable Controller Interrupt
 * @param	pLCD	: The base of LCD peripheral on the chip
 * @param	ints	: OR'ed interrupt bits to enable
 * @return	None
 */
STATIC INLINE void Chip_LCD_EnableInts(LPC_LCD_T *pLCD, uint32_t ints)
{
	IP_LCD_EnableInts(pLCD, ints);
}

/**
 * @brief	Disable Controller Interrupt
 * @param	pLCD	: The base of LCD peripheral on the chip
 * @param	ints	: OR'ed interrupt bits to disable
 * @return	None
 */
STATIC INLINE void Chip_LCD_DisableInts(LPC_LCD_T *pLCD, uint32_t ints)
{
	IP_LCD_DisableInts(pLCD, ints);
}

/**
 * @brief	Clear Controller Interrupt
 * @param	pLCD	: The base of LCD peripheral on the chip
 * @param	ints	: OR'ed interrupt bits to clear
 * @return	None
 */
STATIC INLINE void Chip_LCD_ClearInts(LPC_LCD_T *pLCD, uint32_t ints)
{
	IP_LCD_ClearInts(pLCD, ints);
}

/**
 * @brief	Write Cursor Image into Internal Cursor Image Buffer
 * @param	pLCD		: The base of LCD peripheral on the chip
 * @param	cursor_num	: Cursor index
 * @param	Image		: Pointer to image data
 * @return	None
 */
void Chip_LCD_Cursor_WriteImage(LPC_LCD_T *pLCD, uint8_t cursor_num, void *Image);

/**
 * @brief	Load LCD Palette
 * @param	pLCD	: The base of LCD peripheral on the chip
 * @param	palette	: Address of palette table to load
 * @return	None
 */
void Chip_LCD_LoadPalette(LPC_LCD_T *pLCD, void *palette);

#ifdef __cplusplus
}
#endif

/**
 * @}
 */

#endif /* __LCD_18XX_43XX_H_ */
