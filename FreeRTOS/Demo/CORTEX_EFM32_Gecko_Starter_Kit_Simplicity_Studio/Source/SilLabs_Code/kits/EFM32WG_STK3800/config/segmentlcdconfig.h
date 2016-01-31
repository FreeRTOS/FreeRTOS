/**************************************************************************//**
 * @file
 * @brief Segment LCD Config
 * @version 4.0.0
 ******************************************************************************
 * @section License
 * <b>(C) Copyright 2014 Silicon Labs, http://www.silabs.com</b>
 *******************************************************************************
 *
 * This file is licensed under the Silabs License Agreement. See the file
 * "Silabs_License_Agreement.txt" for details. Before using this software for
 * any purpose, you must agree to the terms of that agreement.
 *
 ******************************************************************************/

#ifndef __SEGMENTLCDCONFIG_H
#define __SEGMENTLCDCONFIG_H

#include "em_lcd.h"

#ifdef __cplusplus
extern "C" {
#endif

/** Range of symbols available on display */
typedef enum {
    LCD_SYMBOL_GECKO,
    LCD_SYMBOL_ANT,
    LCD_SYMBOL_PAD0,
    LCD_SYMBOL_PAD1,
    LCD_SYMBOL_EFM32,
    LCD_SYMBOL_MINUS,
    LCD_SYMBOL_COL3,
    LCD_SYMBOL_COL5,
    LCD_SYMBOL_COL10,
    LCD_SYMBOL_DEGC,
    LCD_SYMBOL_DEGF,
    LCD_SYMBOL_DP2,
    LCD_SYMBOL_DP3,
    LCD_SYMBOL_DP4,
    LCD_SYMBOL_DP5,
    LCD_SYMBOL_DP6,
    LCD_SYMBOL_DP10,
} lcdSymbol;

#define LCD_SYMBOL_GECKO_COM  1
#define LCD_SYMBOL_GECKO_SEG  12
#define LCD_SYMBOL_ANT_COM  0
#define LCD_SYMBOL_ANT_SEG  32
#define LCD_SYMBOL_PAD0_COM  3
#define LCD_SYMBOL_PAD0_SEG  39
#define LCD_SYMBOL_PAD1_COM  2
#define LCD_SYMBOL_PAD1_SEG  12
#define LCD_SYMBOL_EFM32_COM  0
#define LCD_SYMBOL_EFM32_SEG  28
#define LCD_SYMBOL_MINUS_COM  3
#define LCD_SYMBOL_MINUS_SEG  12
#define LCD_SYMBOL_COL3_COM  4
#define LCD_SYMBOL_COL3_SEG  12
#define LCD_SYMBOL_COL5_COM  0
#define LCD_SYMBOL_COL5_SEG  30
#define LCD_SYMBOL_COL10_COM  5
#define LCD_SYMBOL_COL10_SEG  39
#define LCD_SYMBOL_DEGC_COM  0
#define LCD_SYMBOL_DEGC_SEG  34
#define LCD_SYMBOL_DEGF_COM  0
#define LCD_SYMBOL_DEGF_SEG  35
#define LCD_SYMBOL_DP2_COM  7
#define LCD_SYMBOL_DP2_SEG  12
#define LCD_SYMBOL_DP3_COM  5
#define LCD_SYMBOL_DP3_SEG  12
#define LCD_SYMBOL_DP4_COM  6
#define LCD_SYMBOL_DP4_SEG  12
#define LCD_SYMBOL_DP5_COM  7
#define LCD_SYMBOL_DP5_SEG  29
#define LCD_SYMBOL_DP6_COM  7
#define LCD_SYMBOL_DP6_SEG  31
#define LCD_SYMBOL_DP10_COM  4
#define LCD_SYMBOL_DP10_SEG  39

/* LCD Controller Prescaler (divide LFACLK / 64) */
/* LFACLK_LCDpre = 512 Hz */
/* Set FDIV=0, means 512/1 = 512 Hz */
/* With octaplex mode, 512/16 => 32 Hz Frame Rate */
#define LCD_CMU_CLK_PRE         cmuClkDiv_64
#define LCD_CMU_CLK_DIV         cmuClkDiv_1

#define LCD_BOOST_LEVEL         lcdVBoostLevel3


#define LCD_INIT_DEF \
{ true,\
  lcdMuxOctaplex,\
  lcdBiasOneFourth,\
  lcdWaveLowPower,\
  lcdVLCDSelVDD, \
  lcdConConfVLCD }

#define LCD_NUMBER_OFF() \
do { \
  LCD_SegmentSetHigh(1, 0x00000078, 0x00000000); \
  LCD_SegmentSetHigh(2, 0x00000078, 0x00000000); \
  LCD_SegmentSetHigh(3, 0x00000078, 0x00000000); \
  LCD_SegmentSetHigh(4, 0x00000078, 0x00000000); \
  LCD_SegmentSetHigh(5, 0x00000078, 0x00000000); \
  LCD_SegmentSetHigh(6, 0x00000078, 0x00000000); \
  LCD_SegmentSetHigh(7, 0x00000078, 0x00000000); \
} while (0)

#define LCD_ALPHA_NUMBER_OFF() \
do { \
  LCD_SegmentSetLow(7, 0x500FE000, 0x00000000);\
  LCD_SegmentSetLow(6, 0xF00FE000, 0x00000000);\
  LCD_SegmentSetLow(5, 0xF00FE000, 0x00000000);\
  LCD_SegmentSetLow(4, 0xF00FE000, 0x00000000);\
  LCD_SegmentSetLow(3, 0xF00FE000, 0x00000000);\
  LCD_SegmentSetLow(2, 0xF00FE000, 0x00000000);\
  LCD_SegmentSetLow(1, 0xF00FE000, 0x00000000);\
  LCD_SegmentSetLow(0, 0xA0000000, 0x00000000);\
  LCD_SegmentSetHigh(7, 0x00000007, 0x00000000);\
  LCD_SegmentSetHigh(6, 0x00000007, 0x00000000);\
  LCD_SegmentSetHigh(5, 0x00000007, 0x00000000);\
  LCD_SegmentSetHigh(4, 0x00000007, 0x00000000);\
  LCD_SegmentSetHigh(3, 0x00000007, 0x00000000);\
  LCD_SegmentSetHigh(2, 0x00000007, 0x00000000);\
  LCD_SegmentSetHigh(1, 0x00000007, 0x00000000);\
} while(0)

#define LCD_ALL_SEGMENTS_OFF() \
do { \
  LCD_SegmentSetLow(0, 0xF00FF000, 0x00000000);\
  LCD_SegmentSetLow(1, 0xF00FF000, 0x00000000);\
  LCD_SegmentSetLow(2, 0xF00FF000, 0x00000000);\
  LCD_SegmentSetLow(3, 0xF00FF000, 0x00000000);\
  LCD_SegmentSetLow(4, 0xF00FF000, 0x00000000);\
  LCD_SegmentSetLow(5, 0xF00FF000, 0x00000000);\
  LCD_SegmentSetLow(6, 0xF00FF000, 0x00000000);\
  LCD_SegmentSetLow(7, 0xF00FF000, 0x00000000);\
  LCD_SegmentSetHigh(0, 0x000000FF, 0x00000000);\
  LCD_SegmentSetHigh(1, 0x000000FF, 0x00000000);\
  LCD_SegmentSetHigh(2, 0x000000FF, 0x00000000);\
  LCD_SegmentSetHigh(3, 0x000000FF, 0x00000000);\
  LCD_SegmentSetHigh(4, 0x000000FF, 0x00000000);\
  LCD_SegmentSetHigh(5, 0x000000FF, 0x00000000);\
  LCD_SegmentSetHigh(6, 0x000000FF, 0x00000000);\
  LCD_SegmentSetHigh(7, 0x000000FF, 0x00000000);\
} while(0)

#define LCD_ALL_SEGMENTS_ON() \
do { \
  LCD_SegmentSetLow(0, 0xF00FF000, 0xFFFFFFFF);\
  LCD_SegmentSetLow(1, 0xF00FF000, 0xFFFFFFFF);\
  LCD_SegmentSetLow(2, 0xF00FF000, 0xFFFFFFFF);\
  LCD_SegmentSetLow(3, 0xF00FF000, 0xFFFFFFFF);\
  LCD_SegmentSetLow(4, 0xF00FF000, 0xFFFFFFFF);\
  LCD_SegmentSetLow(5, 0xF00FF000, 0xFFFFFFFF);\
  LCD_SegmentSetLow(6, 0xF00FF000, 0xFFFFFFFF);\
  LCD_SegmentSetLow(7, 0xF00FF000, 0xFFFFFFFF);\
  LCD_SegmentSetHigh(0, 0x000000FF, 0xFFFFFFFF);\
  LCD_SegmentSetHigh(1, 0x000000FF, 0xFFFFFFFF);\
  LCD_SegmentSetHigh(2, 0x000000FF, 0xFFFFFFFF);\
  LCD_SegmentSetHigh(3, 0x000000FF, 0xFFFFFFFF);\
  LCD_SegmentSetHigh(4, 0x000000FF, 0xFFFFFFFF);\
  LCD_SegmentSetHigh(5, 0x000000FF, 0xFFFFFFFF);\
  LCD_SegmentSetHigh(6, 0x000000FF, 0xFFFFFFFF);\
  LCD_SegmentSetHigh(7, 0x000000FF, 0xFFFFFFFF);\
} while(0)

#define LCD_SEGMENTS_ENABLE() \
do { \
LCD_SegmentRangeEnable(lcdSegment12_15, true);\
LCD_SegmentRangeEnable(lcdSegment16_19, true);\
LCD_SegmentRangeEnable(lcdSegment28_31, true);\
LCD_SegmentRangeEnable(lcdSegment32_35, true);\
LCD_SegmentRangeEnable(lcdSegment36_39, true);\
} while(0)

#define LCD_DISPLAY_ENABLE() \
do { \
  ;\
} while(0)

#define EFM_DISPLAY_DEF {\
  .Text        = {\
    { /* 1 */\
      .com[0] = 1, .com[1] = 1, .com[2] = 5, .com[3] = 7,\
      .bit[0] = 13, .bit[1] = 14, .bit[2] = 14, .bit[3] = 14,\
      .com[4] = 7, .com[5] = 3, .com[6] = 4, .com[7] = 2,\
      .bit[4] = 13, .bit[5] = 13, .bit[6] = 13, .bit[7] = 13,\
      .com[8] = 3, .com[9] = 2, .com[10] = 4, .com[11] = 6,\
      .bit[8] = 14, .bit[9] = 14, .bit[10] = 14, .bit[11] = 14,\
      .com[12] = 5, .com[13] = 6,\
      .bit[12] = 13, .bit[13] = 13\
    },\
    { /* 2 */\
      .com[0] = 1, .com[1] = 1, .com[2] = 5, .com[3] = 7,\
      .bit[0] = 15, .bit[1] = 16, .bit[2] = 16, .bit[3] = 16,\
      .com[4] = 7, .com[5] = 3, .com[6] = 4, .com[7] = 2,\
      .bit[4] = 15, .bit[5] = 15, .bit[6] = 15, .bit[7] = 15,\
      .com[8] = 3, .com[9] = 2, .com[10] = 4, .com[11] = 6,\
      .bit[8] = 16, .bit[9] = 16, .bit[10] = 16, .bit[11] = 16,\
      .com[12] = 5, .com[13] = 6,\
      .bit[12] = 15, .bit[13] = 15\
    },\
    { /* 3 */\
      .com[0] = 1, .com[1] = 1, .com[2] = 5, .com[3] = 7,\
      .bit[0] = 17, .bit[1] = 18, .bit[2] = 18, .bit[3] = 18,\
      .com[4] = 7, .com[5] = 3, .com[6] = 4, .com[7] = 2,\
      .bit[4] = 17, .bit[5] = 17, .bit[6] = 17, .bit[7] = 17,\
      .com[8] = 3, .com[9] = 2, .com[10] = 4, .com[11] = 6,\
      .bit[8] = 18, .bit[9] = 18, .bit[10] = 18, .bit[11] = 18,\
      .com[12] = 5, .com[13] = 6,\
      .bit[12] = 17, .bit[13] = 17\
    },\
    { /* 4 */\
      .com[0] = 1, .com[1] = 1, .com[2] = 5, .com[3] = 7,\
      .bit[0] = 19, .bit[1] = 28, .bit[2] = 28, .bit[3] = 28,\
      .com[4] = 7, .com[5] = 3, .com[6] = 4, .com[7] = 2,\
      .bit[4] = 19, .bit[5] = 19, .bit[6] = 19, .bit[7] = 19,\
      .com[8] = 3, .com[9] = 2, .com[10] = 4, .com[11] = 6,\
      .bit[8] = 28, .bit[9] = 28, .bit[10] = 28, .bit[11] = 28,\
      .com[12] = 5, .com[13] = 6,\
      .bit[12] = 19, .bit[13] = 19\
    },\
    { /* 5 */\
      .com[0] = 0, .com[1] = 1, .com[2] = 5, .com[3] = 7,\
      .bit[0] = 29, .bit[1] = 30, .bit[2] = 30, .bit[3] = 30,\
      .com[4] = 6, .com[5] = 2, .com[6] = 3, .com[7] = 1,\
      .bit[4] = 29, .bit[5] = 29, .bit[6] = 29, .bit[7] = 29,\
      .com[8] = 3, .com[9] = 2, .com[10] = 4, .com[11] = 6,\
      .bit[8] = 30, .bit[9] = 30, .bit[10] = 30, .bit[11] = 30,\
      .com[12] = 4, .com[13] = 5,\
      .bit[12] = 29, .bit[13] = 29\
    },\
    { /* 6 */\
      .com[0] = 0, .com[1] = 1, .com[2] = 5, .com[3] = 7,\
      .bit[0] = 31, .bit[1] = 32, .bit[2] = 32, .bit[3] = 32,\
      .com[4] = 6, .com[5] = 2, .com[6] = 3, .com[7] = 1,\
      .bit[4] = 31, .bit[5] = 31, .bit[6] = 31, .bit[7] = 31,\
      .com[8] = 3, .com[9] = 2, .com[10] = 4, .com[11] = 6,\
      .bit[8] = 32, .bit[9] = 32, .bit[10] = 32, .bit[11] = 32,\
      .com[12] = 4, .com[13] = 5,\
      .bit[12] = 31, .bit[13] = 31\
    },\
    { /* 7 */\
      .com[0] = 1, .com[1] = 1, .com[2] = 5, .com[3] = 7,\
      .bit[0] = 33, .bit[1] = 34, .bit[2] = 34, .bit[3] = 34,\
      .com[4] = 7, .com[5] = 3, .com[6] = 4, .com[7] = 2,\
      .bit[4] = 33, .bit[5] = 33, .bit[6] = 33, .bit[7] = 33,\
      .com[8] = 3, .com[9] = 2, .com[10] = 4, .com[11] = 6,\
      .bit[8] = 34, .bit[9] = 34, .bit[10] = 34, .bit[11] = 34,\
      .com[12] = 5, .com[13] = 6,\
      .bit[12] = 33, .bit[13] = 33\
    },\
  },\
  .Number      = {\
    {\
      .com[0] = 7, .com[1] = 5, .com[2] = 2, .com[3] = 1,\
      .bit[0] = 35, .bit[1] = 35, .bit[2] = 35, .bit[3] = 35,\
      .com[4] = 3, .com[5] = 6, .com[6] = 4,\
      .bit[4] = 35, .bit[5] = 35, .bit[6] = 35,\
    },\
    {\
      .com[0] = 7, .com[1] = 5, .com[2] = 2, .com[3] = 1,\
      .bit[0] = 36, .bit[1] = 36, .bit[2] = 36, .bit[3] = 36,\
      .com[4] = 3, .com[5] = 6, .com[6] = 4,\
      .bit[4] = 36, .bit[5] = 36, .bit[6] = 36,\
    },\
    {\
      .com[0] = 7, .com[1] = 5, .com[2] = 2, .com[3] = 1,\
      .bit[0] = 37, .bit[1] = 37, .bit[2] = 37, .bit[3] = 37,\
      .com[4] = 3, .com[5] = 6, .com[6] = 4,\
      .bit[4] = 37, .bit[5] = 37, .bit[6] = 37,\
    },\
    {\
      .com[0] = 7, .com[1] = 5, .com[2] = 2, .com[3] = 1,\
      .bit[0] = 38, .bit[1] = 38, .bit[2] = 38, .bit[3] = 38,\
      .com[4] = 3, .com[5] = 6, .com[6] = 4,\
      .bit[4] = 38, .bit[5] = 38, .bit[6] = 38,\
    },\
  },\
  .EMode       = {\
    .com[0] = 0, .bit[0] = 39,\
    .com[1] = 1, .bit[1] = 39,\
    .com[2] = 7, .bit[2] = 39,\
    .com[3] = 2, .bit[3] = 39,\
    .com[4] = 6, .bit[4] = 39,\
  },\
  .ARing       = {\
    .com[0] = 0, .bit[0] = 19,\
    .com[1] = 0, .bit[1] = 18,\
    .com[2] = 0, .bit[2] = 17,\
    .com[3] = 0, .bit[3] = 16,\
    .com[4] = 0, .bit[4] = 15,\
    .com[5] = 0, .bit[5] = 14,\
    .com[6] = 0, .bit[6] = 13,\
    .com[7] = 0, .bit[7] = 12,\
  },\
  .Battery     = {\
    .com[0] = 0, .bit[0] = 33,\
    .com[1] = 0, .bit[1] = 37,\
    .com[2] = 0, .bit[2] = 36,\
    .com[3] = 0, .bit[3] = 38,\
  }\
}


#ifdef __cplusplus
}
#endif

#endif
