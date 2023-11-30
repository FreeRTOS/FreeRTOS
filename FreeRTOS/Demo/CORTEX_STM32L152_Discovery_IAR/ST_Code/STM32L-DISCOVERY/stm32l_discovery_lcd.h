 /**
  ******************************************************************************
  * @file    stm32l_discovery_lcd.h
  * @author  Microcontroller Division
  * @version V1.0.3
  * @date    May-2013
  * @brief   This file contains all the functions prototypes for the glass LCD
  *          firmware driver.
  ******************************************************************************
  * @copy
  *
  * THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
  * WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE
  * TIME. AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY
  * DIRECT, INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING
  * FROM THE CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE
  * CODING INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
  *
  * <h2><center>&copy; COPYRIGHT 2011 STMicroelectronics</center></h2>
  */ 

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __stm32l_discovery_lcd
#define __stm32l_discovery_lcd

/* Includes ------------------------------------------------------------------*/
#include "stm32l1xx.h"   
#include "discover_board.h"

/* Define for scrolling sentences*/
#define SCROLL_SPEED  	75
#define SCROLL_SPEED_L  600
#define SCROLL_NUM    	1

/* Define for character '.' */
#define  POINT_OFF FALSE
#define  POINT_ON TRUE

/* Define for caracter ":" */
#define  COLUMN_OFF FALSE
#define  COLUMN_ON TRUE

#define DOT 0x8000 /* for add decimal point in string */
#define DOUBLE_DOT 0x4000 /* for add decimal point in string */


/*  =========================================================================
                                 LCD MAPPING
    =========================================================================
	    A
     _  ----------
COL |_| |\   |J  /|
       F| H  |  K |B
     _  |  \ | /  |
COL |_| --G-- --M--
        |   /| \  |
       E|  Q |  N |C
     _  | /  |P  \|   
DP  |_| -----------  
	    D         

 An LCD character coding is based on the following matrix:
      { E , D , P , N   }
      { M , C , COL , DP}
      { B , A , K , J   }
      { G , F , Q , H   }

 The character 'A' for example is:
  -------------------------------
LSB   { 1 , 0 , 0 , 0   }
      { 1 , 1 , 0 , 0   }
      { 1 , 1 , 0 , 0   }
MSB   { 1 , 1 , 0 , 0   }
      -------------------
  'A' =  F    E   0   0 hexa

*/
/* Macros used for set/reset bar LCD bar */
#define BAR0_ON  t_bar[1] |= 8
#define BAR0_OFF t_bar[1] &= ~8
#define BAR1_ON  t_bar[0] |= 8
#define BAR1_OFF t_bar[0] &= ~8
#define BAR2_ON  t_bar[1] |= 2
#define BAR2_OFF t_bar[1] &= ~2
#define BAR3_ON t_bar[0]  |= 2 
#define BAR3_OFF t_bar[0] &= ~2 

/* code for 'µ' character */
#define C_UMAP 0x6084

/* code for 'm' character */
#define C_mMap 0xb210

/* code for 'n' character */
#define C_nMap 0x2210

/* constant code for '*' character */
#define star 0xA0DD

/* constant code for '-' character */
#define C_minus 0xA000

/* constant code for '/' */
#define C_slatch  0x00c0

/* constant code for ° */
#define C_percent_1 0xec00

/* constant code  for small o */
#define C_percent_2 0xb300

#define C_full 0xffdd

void LCD_bar(void);
void LCD_GLASS_Init(void);
void LCD_GLASS_WriteChar(uint8_t* ch, bool point, bool column,uint8_t position);
void LCD_GLASS_DisplayString(uint8_t* ptr);
void LCD_GLASS_DisplayStrDeci(uint16_t* ptr);
void LCD_GLASS_ClearChar(uint8_t position);
void LCD_GLASS_Clear(void);
void LCD_GLASS_ScrollSentence(uint8_t* ptr, uint16_t nScroll, uint16_t ScrollSpeed);
void LCD_GLASS_WriteTime(char a, uint8_t posi, bool column);
void LCD_GLASS_Configure_GPIO(void);

#endif /* stm32l_discovery_lcd*/

/******************* (C) COPYRIGHT 2011 STMicroelectronics *****END OF FILE****/
