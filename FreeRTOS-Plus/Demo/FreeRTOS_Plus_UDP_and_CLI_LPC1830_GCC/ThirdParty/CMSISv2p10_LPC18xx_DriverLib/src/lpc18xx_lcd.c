/**********************************************************************
* $Id$		lpc18xx_lcd.c		2011-06-02
*//**
* @file		lpc18xx_lcd.c
* @brief	Contains all function support for LCD Driver
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
/** @addtogroup LCD
 * @{
 */

/* Includes ------------------------------------------------------------------- */
#include "LPC18xx.h"
#include "lpc18xx_lcd.h"

/* If this source file built with example, the LPC18xx FW library configuration
 * file in each example directory ("lpc18xx_libcfg.h") must be included,
 * otherwise the default FW library configuration file must be included instead
 */
#ifdef __BUILD_WITH_EXAMPLE__
#include "lpc18xx_libcfg.h"
#else
#include "lpc18xx_libcfg_default.h"
#endif /* __BUILD_WITH_EXAMPLE__ */

#ifdef _LCD

LCD_CURSOR_SIZE_OPT LCD_Cursor_Size = LCD_CURSOR_64x64;

/* Private Functions ---------------------------------------------------------- */

/*********************************************************************//**
 * @brief 		Init the LPC18xx LCD Controller
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @param[in]	LCD_ConfigStruct point to LCD_CFG_Type that describe the LCD Panel
 * @return 		None
 **********************************************************************/
void LCD_Init(LPC_LCD_Type *LCDx, LCD_CFG_Type *LCD_ConfigStruct){
	uint32_t i, regValue, *pPal;
	uint32_t pcd;
	/* disable the display */
	LCDx->CTRL &= ~CLCDC_LCDCTRL_ENABLE;

	/* Setting LCD_TIMH register */
	regValue= ( ((((LCD_ConfigStruct->screen_width/16)-1)&0x3F) << 2)
	|         (( (LCD_ConfigStruct->HSync_pulse_width-1)    &0xFF) << 8)
	|         (( (LCD_ConfigStruct->horizontal_porch.front-1)    &0xFF) << 16)
	|         (( (LCD_ConfigStruct->horizontal_porch.back-1)    &0xFF) << 24) );

	LCDx->TIMH = regValue;

	/* Setting LCD_TIMV register */
	regValue =((((LCD_ConfigStruct->screen_height-1) &0x3FF) << 0)
	|        (((LCD_ConfigStruct->VSync_pulse_width-1) &0x03F) << 10)
	|        (((LCD_ConfigStruct->vertical_porch.front-1) &0x0FF) << 16)
	|        (((LCD_ConfigStruct->vertical_porch.back-1) &0x0FF) << 24) );

	LCDx->TIMV = regValue;

	/* Generate the clock and signal polarity control word */
	regValue = 0;
	regValue = (((LCD_ConfigStruct->ac_bias_frequency-1) & 0x1F) << 6);

	regValue |= (LCD_ConfigStruct->OE_pol & 1)<< 14;

	regValue |= (LCD_ConfigStruct->panel_clk_edge & 1)<< 13;

	regValue |= (LCD_ConfigStruct->HSync_pol & 1)<< 12;

	regValue |= (LCD_ConfigStruct->VSync_pol & 1)<< 11;

	/* Compute clocks per line based on panel type */

	switch(LCD_ConfigStruct->lcd_panel_type)
	{
	  case LCD_MONO_4:
		regValue |= ((((LCD_ConfigStruct->screen_width / 4)-1) & 0x3FF) << 16);
		break;
	  case LCD_MONO_8:
		regValue |= ((((LCD_ConfigStruct->screen_width / 8)-1) & 0x3FF) << 16);
		break;
	  case LCD_CSTN:
		regValue |= (((((LCD_ConfigStruct->screen_width * 3)/8)-1) & 0x3FF) << 16);
		break;
	  case LCD_TFT:
	  default:
		regValue |= 1<<26 | (((LCD_ConfigStruct->screen_width-1) & 0x3FF) << 16);
	}

	/* panel clock divisor */
	pcd = LCD_ConfigStruct->pcd;   // TODO: should be calculated from LCDDCLK
	pcd &= 0x3FF;
	regValue |=  ((pcd>>5)<<27) | ((pcd)&0x1F);

	LCDx->POL = regValue;

	/* configure line end control */
	CHECK_PARAM(LCD_ConfigStruct->line_end_delay<=(1<<7));
	if(LCD_ConfigStruct->line_end_delay)
		LCDx->LE  = (LCD_ConfigStruct->line_end_delay-1) | 1<<16;
	else
		LCDx->LE = 0;

	/* disable interrupts */
	LCDx->INTMSK = 0;

	/* set bits per pixel */
	regValue = LCD_ConfigStruct->bits_per_pixel << 1;

	/* set color format BGR or RGB */
	regValue |= LCD_ConfigStruct->color_format << 8;

	regValue |= LCD_ConfigStruct->lcd_panel_type << 4;

	if(LCD_ConfigStruct->dual_panel == 1)
	{
		regValue |= 1 << 7;
	}
	LCDx->CTRL = regValue;
	/* clear palette */
	pPal = (uint32_t*) (&(LCDx->PAL));

	for(i = 0; i < 128; i++)
	{
		*pPal = 0;
		pPal++;
	}
}


/*********************************************************************//**
 * @brief 		Deinit LCD controller
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @return 		None
 **********************************************************************/
void LCD_DeInit(LPC_LCD_Type *LCDx);


/*********************************************************************//**
 * @brief 		Power the LCD Panel
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @param[in]	OnOff	Turn on/off LCD
 * 					- TRUE	:Turn on
 * 					- FALSE :Turn off
 * @return 		None
 **********************************************************************/
void LCD_Power(LPC_LCD_Type *LCDx, FunctionalState OnOff){
int i;
	if(OnOff){
		LPC_LCD->CTRL |= CLCDC_LCDCTRL_PWR;
		for(i=0;i<100000;i++);
		LPC_LCD->CTRL |= CLCDC_LCDCTRL_ENABLE;
	}else{
		LPC_LCD->CTRL &= ~CLCDC_LCDCTRL_PWR;
		for(i=0;i<100000;i++);
		LPC_LCD->CTRL &= ~CLCDC_LCDCTRL_ENABLE;
	}
}


/*********************************************************************//**
 * @brief 		Enable/Disable the LCD Controller
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @param[in]	EnDis	Enable/disable status
 * 					- TRUE	:Enable
 * 					- FALSE :Disable
 * @return 		None
 **********************************************************************/
void LCD_Enable(LPC_LCD_Type *LCDx, FunctionalState EnDis){
	if (EnDis)
	{
	  LCDx->CTRL |= CLCDC_LCDCTRL_ENABLE;
	}
	else
	{
	  LCDx->CTRL &= ~CLCDC_LCDCTRL_ENABLE;
	}
}


/*********************************************************************//**
 * @brief 		Set LCD Frame Buffer for Single Panel or Upper Panel Frame
 * 				Buffer for Dual Panel
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @param[in]	buffer address of buffer
 * @return 		None
 **********************************************************************/
void LCD_SetFrameBuffer(LPC_LCD_Type *LCDx, void* buffer){
	LCDx->UPBASE = (uint32_t)buffer;
}


/*********************************************************************//**
 * @brief 		Set LCD Lower Panel Frame Buffer for Dual Panel
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @param[in]	buffer address of buffer
 * @return 		None
 **********************************************************************/
void LCD_SetLPFrameBuffer(LPC_LCD_Type *LCDx, void* buffer){
	LCDx->LPBASE = (uint32_t)buffer;
}


/*********************************************************************//**
 * @brief 		Configure Cursor
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @param[in]	cursor_size specify size of cursor
 * 					- LCD_CURSOR_32x32	:cursor size is 32x32 pixels
 * 					- LCD_CURSOR_64x64	:cursor size is 64x64 pixels
 * @param[in]	sync cursor sync mode
 * 					- TRUE	:cursor sync to the frame sync pulse
 * 					- FALSE	:cursor async mode
 * @return 		None
 **********************************************************************/
void LCD_Cursor_Config(LPC_LCD_Type *LCDx, LCD_CURSOR_SIZE_OPT cursor_size, Bool sync){
	LCD_Cursor_Size = cursor_size;
	LCDx->CRSR_CFG = ((sync?1:0)<<1) | cursor_size;
}


/*********************************************************************//**
 * @brief 		Write Cursor Image into Internal Cursor Image Buffer
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @param[in]	cursor_num specify number of cursor is going to be written
 * 				this param must < 4
 * @param[in]	Image point to Cursor Image Buffer
 * @return 		None
 **********************************************************************/
void LCD_Cursor_WriteImage(LPC_LCD_Type *LCDx, uint8_t cursor_num, void* Image){
	int i,j;
	uint8_t *fifoptr, *crsr_ptr = (uint8_t *)Image;

	CHECK_PARAM(cursor_num<4);
	/* Check if Cursor Size was configured as 32x32 or 64x64*/
	if(LCD_Cursor_Size == LCD_CURSOR_32x32){
		i = cursor_num * 256;
		j = i + 256;
	}else{
		i = 0;
		j = 1024;
	}
	fifoptr = (uint8_t*)&(LCDx->CRSR_IMG[0]);
	/* Copy Cursor Image content to FIFO */
	for(; i < j; i++)
	{
	  fifoptr[i] = *(uint8_t *)crsr_ptr;
	  crsr_ptr++;
	}
}


/*********************************************************************//**
 * @brief 		Get Internal Cursor Image Buffer Address
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @param[in]	cursor_num specify number of cursor is going to be written
 * 				this param must < 4
 * @return 		Cursor Image Buffer Address
 **********************************************************************/
void* LCD_Cursor_GetImageBufferAddress(LPC_LCD_Type *LCDx, uint8_t cursor_num){
	CHECK_PARAM(cursor_num<4);
	return (void*)&(LCDx->CRSR_IMG[cursor_num*64]);
}


/*********************************************************************//**
 * @brief 		Enable Cursor
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @param[in]	cursor_num specify number of cursor is going to be written
 * 				this param must < 4
 * @param[in]	OnOff Turn on/off LCD
 * 					- TRUE	:Enable
 * 					- FALSE :Disable
 * @return 		None
 **********************************************************************/
void LCD_Cursor_Enable(LPC_LCD_Type *LCDx, uint8_t cursor_num, FunctionalState OnOff){
	CHECK_PARAM(cursor_num<4);
	if (OnOff)
	{
	  LCDx->CRSR_CTRL = (cursor_num<<4) | 1;
	}
	else
	{
	  LCDx->CRSR_CTRL = (cursor_num<<4);
	}
}


/*********************************************************************//**
 * @brief 		Load LCD Palette
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @param[in]	palette point to palette address
 * @return 		None
 **********************************************************************/
void LCD_LoadPalette(LPC_LCD_Type *LCDx, void* palette){
	LCD_PALETTE_ENTRY_Type pal_entry, *ptr_pal_entry;
	uint8_t i, *pal_ptr;
	/* This function supports loading of the color palette from
	the C file generated by the bmp2c utility. It expects the
	palette to be passed as an array of 32-bit BGR entries having
	the following format:
	2:0 - Not used
	7:3 - Blue
	10:8 - Not used
	15:11 - Green
	18:16 - Not used
	23:19 - Red
	31:24 - Not used
	arg = pointer to input palette table address */
	ptr_pal_entry = &pal_entry;
	pal_ptr = (uint8_t *) palette;

	/* 256 entry in the palette table */
	for(i = 0; i < 256/2; i++)
	{
	pal_entry.Bl = (*pal_ptr++) >> 3;  /* blue first */
	pal_entry.Gl = (*pal_ptr++) >> 3;  /* get green */
	pal_entry.Rl = (*pal_ptr++) >> 3;  /* get red */
	pal_ptr++;      /* skip over the unused byte */
	/* do the most significant halfword of the palette */
	pal_entry.Bu = (*pal_ptr++) >> 3;  /* blue first */
	pal_entry.Gu = (*pal_ptr++) >> 3;  /* get green */
	pal_entry.Ru = (*pal_ptr++) >> 3;  /* get red */
	pal_ptr++;      /* skip over the unused byte */

	LCDx->PAL[i] = *(uint32_t *)ptr_pal_entry;
	}
}


/*********************************************************************//**
 * @brief 		Load Cursor Palette
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @param[in]	palette_color cursor palette 0 value
 * @return 		None
 **********************************************************************/
void LCD_Cursor_LoadPalette0(LPC_LCD_Type *LCDx, uint32_t palette_color){
	/* 7:0 - Red
	15:8 - Green
	23:16 - Blue
	31:24 - Not used*/
	LCDx->CRSR_PAL0 = (uint32_t)palette_color;
}


/*********************************************************************//**
 * @brief 		Load Cursor Palette
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @param[in]	palette_color cursor palette 1 value
 * @return 		None
 **********************************************************************/
void LCD_Cursor_LoadPalette1(LPC_LCD_Type *LCDx, uint32_t palette_color){
	/* 7:0 - Red
	15:8 - Green
	23:16 - Blue
	31:24 - Not used*/
	LCDx->CRSR_PAL1 = (uint32_t)palette_color;
}


/*********************************************************************//**
 * @brief 		Set Interrupt
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @param[in]	Int LCD Interrupt Source, should be:
 * 					- LCD_INT_FUF	:FIFO underflow
 * 					- LCD_INT_LNBU	:LCD next base address update bit
 * 					- LCD_INT_VCOMP	:Vertical compare bit
 * 					- LCD_INT_BER	:AHB master error interrupt bit
 * @return 		None
 **********************************************************************/
void LCD_SetInterrupt(LPC_LCD_Type *LCDx, LCD_INT_SRC Int){
	LCDx->INTMSK |= Int;
}


/*********************************************************************//**
 * @brief 		Clear Interrupt
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @param[in]	Int LCD Interrupt Source, should be:
 * 					- LCD_INT_FUF	:FIFO underflow
 * 					- LCD_INT_LNBU	:LCD next base address update bit
 * 					- LCD_INT_VCOMP	:Vertical compare bit
 * 					- LCD_INT_BER	:AHB master error interrupt bit
 * @return 		None
 **********************************************************************/
void LCD_ClrInterrupt(LPC_LCD_Type *LCDx, LCD_INT_SRC Int){
	LCDx->INTCLR |= Int;
}


/*********************************************************************//**
 * @brief 		Get LCD Interrupt Status
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @return 		None
 **********************************************************************/
LCD_INT_SRC LCD_GetInterrupt(LPC_LCD_Type *LCDx){
	return (LCD_INT_SRC)LCDx->INTRAW;
}


/*********************************************************************//**
 * @brief 		Enable Cursor Interrupt
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @return 		None
 **********************************************************************/
void LCD_Cursor_SetInterrupt(LPC_LCD_Type *LCDx){
	LCDx->CRSR_INTMSK |= 1;
}


/*********************************************************************//**
 * @brief 		Clear Cursor Interrupt
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @return 		None
 **********************************************************************/
void LCD_Cursor_ClrInterrupt(LPC_LCD_Type *LCDx){
	LCDx->CRSR_INTCLR |= 1;
}


/*********************************************************************//**
 * @brief 		Set Cursor Position
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @param[in]	x horizontal position
 * @param[in]	y vertical position
 * @return 		None
 **********************************************************************/
void LCD_Cursor_SetPos(LPC_LCD_Type *LCDx, uint16_t x, uint16_t y){
	LCDx->CRSR_XY = (x & 0x3FF) | ((y & 0x3FF) << 16);
}


/*********************************************************************//**
 * @brief 		Set Cursor Clipping Position
 * @param[in]	LCDx pointer to LCD Controller Reg Struct, should be: LPC_LCD
 * @param[in]	x horizontal position, should be in range: 0..63
 * @param[in]	y vertical position, should be in range: 0..63
 * @return 		None
 **********************************************************************/
void LCD_Cursor_SetClip(LPC_LCD_Type *LCDx, uint16_t x, uint16_t y){
	LCDx->CRSR_CLIP = (x & 0x3F) | ((y & 0x3F) << 8);
}
#endif /* _LCD */

/**
 * @}
 */

/* --------------------------------- End Of File ------------------------------ */
