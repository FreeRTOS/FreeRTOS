/**
  ******************************************************************************
  * @file    stm32_eval_legacy.h
  * @author  MCD Application Team
  * @version V5.0.1
  * @date    28-December-2011
  * @brief   This file contains defines legacy for STM32 EVAL drivers.
  ******************************************************************************
  * @attention
  *
  * THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
  * WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE
  * TIME. AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY
  * DIRECT, INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING
  * FROM THE CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE
  * CODING INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
  *
  * FOR MORE INFORMATION PLEASE READ CAREFULLY THE LICENSE AGREEMENT FILE
  * LOCATED IN THE ROOT DIRECTORY OF THIS FIRMWARE PACKAGE.
  *
  * <h2><center>&copy; COPYRIGHT 2011 STMicroelectronics</center></h2>
  ******************************************************************************
  */ 
  
/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32_EVAL_LEGACY_H
#define __STM32_EVAL_LEGACY_H

#ifdef __cplusplus
 extern "C" {
#endif 

/* Includes ------------------------------------------------------------------*/

/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/
/* STM322xG_EVAL Defines Legacy */ 
#ifdef USE_STM3220F_EVAL       
  #define USE_STM322xG_EVAL
#endif
#define STM3220F_LCD_Init       STM322xG_LCD_Init

/* Button Defines Legacy */ 
#define Button_WAKEUP        BUTTON_WAKEUP
#define Button_TAMPER        BUTTON_TAMPER
#define Button_KEY           BUTTON_KEY
#define Button_RIGHT         BUTTON_RIGHT
#define Button_LEFT          BUTTON_LEFT
#define Button_UP            BUTTON_UP
#define Button_DOWN          BUTTON_DOWN
#define Button_SEL           BUTTON_SEL
#define Mode_GPIO            BUTTON_MODE_GPIO
#define Mode_EXTI            BUTTON_MODE_EXTI
#define Button_Mode_TypeDef  ButtonMode_TypeDef
#define JOY_CENTER           JOY_SEL
#define JOY_State_TypeDef    JOYState_TypeDef 

/* LCD Defines Legacy */ 
#define LCD_RSNWR_GPIO_CLK  LCD_NWR_GPIO_CLK
#define LCD_SPI_GPIO_PORT   LCD_SPI_SCK_GPIO_PORT
#define LCD_SPI_GPIO_CLK    LCD_SPI_SCK_GPIO_CLK
#define R0                  LCD_REG_0
#define R1                  LCD_REG_1
#define R2                  LCD_REG_2
#define R3                  LCD_REG_3
#define R4                  LCD_REG_4
#define R5                  LCD_REG_5
#define R6                  LCD_REG_6
#define R7                  LCD_REG_7
#define R8                  LCD_REG_8
#define R9                  LCD_REG_9
#define R10                 LCD_REG_10
#define R12                 LCD_REG_12
#define R13                 LCD_REG_13
#define R14                 LCD_REG_14
#define R15                 LCD_REG_15
#define R16                 LCD_REG_16
#define R17                 LCD_REG_17
#define R18                 LCD_REG_18
#define R19                 LCD_REG_19
#define R20                 LCD_REG_20
#define R21                 LCD_REG_21
#define R22                 LCD_REG_22
#define R23                 LCD_REG_23
#define R24                 LCD_REG_24
#define R25                 LCD_REG_25
#define R26                 LCD_REG_26
#define R27                 LCD_REG_27
#define R28                 LCD_REG_28
#define R29                 LCD_REG_29
#define R30                 LCD_REG_30
#define R31                 LCD_REG_31
#define R32                 LCD_REG_32
#define R33                 LCD_REG_33
#define R34                 LCD_REG_34
#define R36                 LCD_REG_36
#define R37                 LCD_REG_37
#define R40                 LCD_REG_40
#define R41                 LCD_REG_41
#define R43                 LCD_REG_43
#define R45                 LCD_REG_45
#define R48                 LCD_REG_48
#define R49                 LCD_REG_49
#define R50                 LCD_REG_50
#define R51                 LCD_REG_51
#define R52                 LCD_REG_52
#define R53                 LCD_REG_53
#define R54                 LCD_REG_54
#define R55                 LCD_REG_55
#define R56                 LCD_REG_56
#define R57                 LCD_REG_57
#define R59                 LCD_REG_59
#define R60                 LCD_REG_60
#define R61                 LCD_REG_61
#define R62                 LCD_REG_62
#define R63                 LCD_REG_63
#define R64                 LCD_REG_64
#define R65                 LCD_REG_65
#define R66                 LCD_REG_66
#define R67                 LCD_REG_67
#define R68                 LCD_REG_68
#define R69                 LCD_REG_69
#define R70                 LCD_REG_70
#define R71                 LCD_REG_71
#define R72                 LCD_REG_72
#define R73                 LCD_REG_73
#define R74                 LCD_REG_74
#define R75                 LCD_REG_75
#define R76                 LCD_REG_76
#define R77                 LCD_REG_77
#define R78                 LCD_REG_78
#define R79                 LCD_REG_79
#define R80                 LCD_REG_80
#define R81                 LCD_REG_81
#define R82                 LCD_REG_82
#define R83                 LCD_REG_83
#define R96                 LCD_REG_96
#define R97                 LCD_REG_97
#define R106                LCD_REG_106
#define R118                LCD_REG_118
#define R128                LCD_REG_128
#define R129                LCD_REG_129
#define R130                LCD_REG_130
#define R131                LCD_REG_131
#define R132                LCD_REG_132
#define R133                LCD_REG_133
#define R134                LCD_REG_134
#define R135                LCD_REG_135
#define R136                LCD_REG_136
#define R137                LCD_REG_137
#define R139                LCD_REG_139
#define R140                LCD_REG_140
#define R141                LCD_REG_141
#define R143                LCD_REG_143
#define R144                LCD_REG_144
#define R145                LCD_REG_145
#define R146                LCD_REG_146
#define R147                LCD_REG_147
#define R148                LCD_REG_148
#define R149                LCD_REG_149
#define R150                LCD_REG_150
#define R151                LCD_REG_151
#define R152                LCD_REG_152
#define R153                LCD_REG_153
#define R154                LCD_REG_154
#define R157                LCD_REG_157
#define R192                LCD_REG_192
#define R193                LCD_REG_193
#define R227                LCD_REG_227
#define R229                LCD_REG_229
#define R231                LCD_REG_231
#define R239                LCD_REG_239
#define White               LCD_COLOR_WHITE
#define Black               LCD_COLOR_BLACK
#define Grey                LCD_COLOR_GREY
#define Blue                LCD_COLOR_BLUE
#define Blue2               LCD_COLOR_BLUE2
#define Red                 LCD_COLOR_RED
#define Magenta             LCD_COLOR_MAGENTA
#define Green               LCD_COLOR_GREEN
#define Cyan                LCD_COLOR_CYAN
#define Yellow              LCD_COLOR_YELLOW
#define Line0               LCD_LINE_0
#define Line1               LCD_LINE_1
#define Line2               LCD_LINE_2
#define Line3               LCD_LINE_3
#define Line4               LCD_LINE_4
#define Line5               LCD_LINE_5
#define Line6               LCD_LINE_6
#define Line7               LCD_LINE_7
#define Line8               LCD_LINE_8
#define Line9               LCD_LINE_9
#define Horizontal          LCD_DIR_HORIZONTAL
#define Vertical            LCD_DIR_VERTICAL

/* Exported macro ------------------------------------------------------------*/
/* Exported functions --------------------------------------------------------*/ 

#ifdef __cplusplus
}
#endif

#endif /* __STM32_EVAL_LEGACY_H */

/******************* (C) COPYRIGHT 2011 STMicroelectronics *****END OF FILE****/
