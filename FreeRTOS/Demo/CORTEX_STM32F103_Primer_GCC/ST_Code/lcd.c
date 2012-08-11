/********************* (C) COPYRIGHT 2007 RAISONANCE S.A.S. *******************/
/**
*
* @file     lcd.c
* @brief    The LCD driver for the ST7637.
* @author   FL
* @date     07/2007
*
**/
/******************************************************************************/

/* Includes ------------------------------------------------------------------*/
#include "lcd.h"
#include "circle.h"

/// @cond Internal

/* Private define ------------------------------------------------------------*/
#define V9_MADCTRVAL                0x90     /*!< Left orientation value.     */
#define V12_MADCTRVAL               0x30     /*!< Up orientation value.       */
#define V3_MADCTRVAL                0x50     /*!< Right orientation value.    */
#define V6_MADCTRVAL                0xF0     /*!< Bottom orientation value.   */
#define BACKLIGHT_DIVIDER           500      /*!< LCD handler step.           */

/* Private variables ---------------------------------------------------------*/

// vars for timer dedicated for lcd backlight
static TIM_TimeBaseInitTypeDef      TIM_TimeBaseStructure;
static TIM_OCInitTypeDef            TIM_OCInitStructure;
static int                          HandlerDivider             = 0;

int                                 Current_CCR_BackLightStart = DEFAULT_CCR_BACKLIGHTSTART;

/* External variable ---------------------------------------------------------*/
extern GPIO_InitTypeDef             GPIO_InitStructure;
extern u16                          CCR_BackLight_Tab[5];
extern int                          CurrentRotateScreen;
extern Rotate_H12_V_Match_TypeDef   CurrentScreenOrientation;

/*! ASCII Table. Each character is 7 column (7dots large) on two pages (16dots high)
    7 column character: Two 8 bit data to display one column*/
static const u8 AsciiDotsTable[95 * 14 ] = {
  /* ASCII 32  */  0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 33  */  0x00,0x00,0x00,0x00,0x00,0x00,0x13,0xe0,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 34  */  0x00,0x00,0x00,0xe0,0x00,0x20,0x00,0x00,0x00,0xe0,0x00,0x20,0x00,0x00,
  /* ASCII 35  */  0x00,0x00,0x35,0x00,0x0f,0x80,0x35,0x60,0x0f,0x80,0x05,0x60,0x00,0x00,
  /* ASCII 36  */  0x00,0x00,0x0d,0x80,0x0a,0x40,0x3a,0x60,0x06,0x40,0x00,0x00,0x00,0x00,
  /* ASCII 37  */  0x00,0x00,0x02,0x40,0x02,0xa0,0x0a,0x40,0x15,0x00,0x09,0x00,0x00,0x00,
  /* ASCII 38  */  0x00,0x00,0x0c,0x00,0x13,0x00,0x14,0x80,0x08,0x80,0x14,0x00,0x00,0x00,
  /* ASCII 39  */  0x00,0x00,0x00,0x00,0x00,0x00,0x01,0xe0,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 40  */  0x00,0x00,0x00,0x00,0x00,0x00,0x1f,0x80,0x60,0x60,0x00,0x00,0x00,0x00,
  /* ASCII 41  */  0x00,0x00,0x00,0x00,0x60,0x60,0x1f,0x80,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 42  */  0x00,0x00,0x00,0x40,0x03,0x40,0x00,0xe0,0x03,0x40,0x00,0x40,0x00,0x00,
  /* ASCII 43  */  0x02,0x00,0x02,0x00,0x02,0x00,0x1f,0xc0,0x02,0x00,0x02,0x00,0x02,0x00,
  /* ASCII 44  */  0x00,0x00,0x00,0x00,0x60,0x00,0x38,0x00,0x08,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 45  */  0x00,0x00,0x02,0x00,0x02,0x00,0x02,0x00,0x02,0x00,0x02,0x00,0x00,0x00,
  /* ASCII 46  */  0x00,0x00,0x00,0x00,0x18,0x00,0x18,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 47  */  0x00,0x00,0x20,0x00,0x18,0x00,0x06,0x00,0x01,0x80,0x00,0x60,0x00,0x00,
  /* ASCII 48  */  0x00,0x00,0x0f,0xc0,0x10,0x20,0x10,0x20,0x10,0x20,0x0f,0xc0,0x00,0x00,
  /* ASCII 49  */  0x00,0x00,0x10,0x00,0x10,0x20,0x1f,0xe0,0x10,0x00,0x10,0x00,0x00,0x00,
  /* ASCII 50  */  0x00,0x00,0x18,0x40,0x14,0x20,0x12,0x20,0x11,0x20,0x18,0xc0,0x00,0x00,
  /* ASCII 51  */  0x00,0x00,0x08,0x40,0x10,0x20,0x11,0x20,0x11,0x20,0x0e,0xc0,0x00,0x00,
  /* ASCII 52  */  0x00,0x00,0x06,0x00,0x05,0x00,0x04,0xc0,0x14,0x20,0x1f,0xe0,0x14,0x00,
  /* ASCII 53  */  0x00,0x00,0x08,0x00,0x11,0xe0,0x11,0x20,0x11,0x20,0x0e,0x20,0x00,0x00,
  /* ASCII 54  */  0x00,0x00,0x0f,0x80,0x11,0x40,0x11,0x20,0x11,0x20,0x0e,0x20,0x00,0x00,
  /* ASCII 55  */  0x00,0x00,0x00,0x60,0x00,0x20,0x18,0x20,0x07,0x20,0x00,0xe0,0x00,0x00,
  /* ASCII 56  */  0x00,0x00,0x0e,0xc0,0x11,0x20,0x11,0x20,0x11,0x20,0x0e,0xc0,0x00,0x00,
  /* ASCII 57  */  0x00,0x00,0x11,0xc0,0x12,0x20,0x12,0x20,0x0a,0x20,0x07,0xc0,0x00,0x00,
  /* ASCII 58  */  0x00,0x00,0x00,0x00,0x19,0x80,0x19,0x80,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 59  */  0x00,0x00,0x00,0x00,0x30,0x00,0x19,0x80,0x09,0x80,0x00,0x00,0x00,0x00,
  /* ASCII 60  */  0x02,0x00,0x05,0x00,0x05,0x00,0x08,0x80,0x10,0x40,0x10,0x40,0x00,0x00,
  /* ASCII 61  */  0x00,0x00,0x05,0x00,0x05,0x00,0x05,0x00,0x05,0x00,0x05,0x00,0x00,0x00,
  /* ASCII 62  */  0x10,0x40,0x10,0x40,0x08,0x80,0x05,0x00,0x05,0x00,0x02,0x00,0x00,0x00,
  /* ASCII 63  */  0x00,0x00,0x00,0x00,0x10,0x80,0x14,0x40,0x02,0x40,0x01,0x80,0x00,0x00,
  /* ASCII 64  */  0x00,0x00,0x1f,0xe0,0x20,0x10,0x23,0x10,0x24,0x90,0x17,0xe0,0x00,0x00,
  /* ASCII 65  */  0x10,0x00,0x1c,0x00,0x17,0xa0,0x04,0x60,0x17,0x80,0x1c,0x00,0x10,0x00,
  /* ASCII 66  */  0x10,0x20,0x1f,0xe0,0x11,0x20,0x11,0x20,0x11,0x20,0x0e,0xc0,0x00,0x00,
  /* ASCII 67  */  0x00,0x00,0x0f,0xc0,0x10,0x20,0x10,0x20,0x10,0x20,0x08,0x60,0x00,0x00,
  /* ASCII 68  */  0x10,0x20,0x1f,0xe0,0x10,0x20,0x10,0x20,0x08,0x40,0x07,0x80,0x00,0x00,
  /* ASCII 69  */  0x10,0x20,0x1f,0xe0,0x11,0x20,0x13,0xa0,0x10,0x20,0x18,0x60,0x00,0x00,
  /* ASCII 70  */  0x00,0x00,0x10,0x20,0x1f,0xe0,0x11,0x20,0x03,0xa0,0x00,0x20,0x00,0x60,
  /* ASCII 71  */  0x00,0x00,0x0f,0xc0,0x10,0x20,0x10,0x20,0x12,0x20,0x0e,0x60,0x02,0x00,
  /* ASCII 72  */  0x10,0x20,0x1f,0xe0,0x11,0x20,0x01,0x00,0x11,0x20,0x1f,0xe0,0x10,0x20,
  /* ASCII 73  */  0x00,0x00,0x10,0x20,0x10,0x20,0x1f,0xe0,0x10,0x20,0x10,0x20,0x00,0x00,
  /* ASCII 74  */  0x00,0x00,0x0e,0x00,0x10,0x20,0x10,0x20,0x0f,0xe0,0x00,0x20,0x00,0x00,
  /* ASCII 75  */  0x10,0x20,0x1f,0xe0,0x12,0x20,0x03,0x00,0x04,0xa0,0x18,0x60,0x10,0x20,
  /* ASCII 76  */  0x00,0x00,0x10,0x20,0x1f,0xe0,0x10,0x20,0x10,0x00,0x1c,0x00,0x00,0x00,
  /* ASCII 77  */  0x10,0x20,0x1f,0xe0,0x10,0xe0,0x03,0x00,0x10,0xe0,0x1f,0xe0,0x10,0x20,
  /* ASCII 78  */  0x10,0x20,0x1f,0xe0,0x10,0xe0,0x07,0x00,0x18,0x20,0x1f,0xe0,0x00,0x20,
  /* ASCII 79  */  0x00,0x00,0x0f,0xc0,0x10,0x20,0x10,0x20,0x10,0x20,0x0f,0xc0,0x00,0x00,
  /* ASCII 80  */  0x00,0x00,0x10,0x20,0x1f,0xe0,0x12,0x20,0x02,0x20,0x01,0xc0,0x00,0x00,
  /* ASCII 81  */  0x00,0x00,0x0f,0xc0,0x10,0x20,0x30,0x20,0x30,0x20,0x2f,0xc0,0x00,0x00,
  /* ASCII 82  */  0x10,0x20,0x1f,0xe0,0x12,0x20,0x02,0x20,0x06,0x20,0x09,0xc0,0x10,0x00,
  /* ASCII 83  */  0x00,0x00,0x18,0xc0,0x09,0x20,0x11,0x20,0x11,0x40,0x0e,0x60,0x00,0x00,
  /* ASCII 84  */  0x00,0x60,0x00,0x20,0x10,0x20,0x1f,0xe0,0x10,0x20,0x00,0x20,0x00,0x60,
  /* ASCII 85  */  0x00,0x20,0x0f,0xe0,0x10,0x20,0x10,0x00,0x10,0x20,0x0f,0xe0,0x00,0x20,
  /* ASCII 86  */  0x00,0x20,0x00,0xe0,0x07,0x20,0x18,0x00,0x07,0x20,0x00,0xe0,0x00,0x20,
  /* ASCII 87  */  0x00,0x20,0x0f,0xe0,0x10,0x20,0x0f,0x00,0x10,0x20,0x0f,0xe0,0x00,0x20,
  /* ASCII 88  */  0x10,0x20,0x18,0x60,0x04,0x80,0x03,0x00,0x04,0x80,0x18,0x60,0x10,0x20,
  /* ASCII 89  */  0x00,0x20,0x00,0x60,0x11,0xa0,0x1e,0x00,0x11,0xa0,0x00,0x60,0x00,0x20,
  /* ASCII 90  */  0x00,0x00,0x18,0x60,0x14,0x20,0x13,0x20,0x10,0xa0,0x18,0x60,0x00,0x00,
  /* ASCII 91  */  0x00,0x00,0x00,0x00,0x7f,0xe0,0x40,0x20,0x40,0x20,0x00,0x00,0x00,0x00,
  /* ASCII 92  */  0x00,0x00,0x00,0x20,0x01,0xc0,0x06,0x00,0x38,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 93  */  0x00,0x00,0x00,0x00,0x40,0x20,0x40,0x20,0x7f,0xe0,0x00,0x00,0x00,0x00,
  /* ASCII 94  */  0x00,0x00,0x01,0x00,0x00,0x80,0x00,0x60,0x00,0x80,0x01,0x00,0x00,0x00,
  /* ASCII 95  */  0x80,0x00,0x80,0x00,0x80,0x00,0x80,0x00,0x80,0x00,0x80,0x00,0x80,0x00,
  /* ASCII 96  */  0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x20,0x00,0x40,0x00,0x00,0x00,0x00,
  /* ASCII 97  */  0x00,0x00,0x0d,0x00,0x12,0x80,0x12,0x80,0x12,0x80,0x1f,0x00,0x10,0x00,
  /* ASCII 98  */  0x10,0x20,0x1f,0xe0,0x11,0x00,0x10,0x80,0x10,0x80,0x0f,0x00,0x00,0x00,
  /* ASCII 99  */  0x00,0x00,0x0f,0x00,0x10,0x80,0x10,0x80,0x10,0x80,0x09,0x80,0x00,0x00,
  /* ASCII 100 */  0x00,0x00,0x0f,0x00,0x10,0x80,0x10,0x80,0x11,0x20,0x1f,0xe0,0x10,0x00,
  /* ASCII 101 */  0x00,0x00,0x0f,0x00,0x12,0x80,0x12,0x80,0x12,0x80,0x13,0x00,0x00,0x00,
  /* ASCII 102 */  0x00,0x00,0x10,0x80,0x1f,0xc0,0x10,0xa0,0x10,0xa0,0x10,0xa0,0x00,0x00,
  /* ASCII 103 */  0x00,0x00,0x0f,0x00,0x50,0x80,0x50,0x80,0x51,0x00,0x3f,0x80,0x00,0x80,
  /* ASCII 104 */  0x10,0x20,0x1f,0xe0,0x11,0x00,0x00,0x80,0x10,0x80,0x1f,0x00,0x10,0x00,
  /* ASCII 105 */  0x00,0x00,0x10,0x80,0x10,0x80,0x1f,0xa0,0x10,0x00,0x10,0x00,0x00,0x00,
  /* ASCII 106 */  0x00,0x00,0x40,0x80,0x40,0x80,0x40,0xa0,0x3f,0x80,0x00,0x00,0x00,0x00,
  /* ASCII 107 */  0x10,0x20,0x1f,0xe0,0x02,0x00,0x16,0x80,0x19,0x80,0x10,0x80,0x00,0x00,
  /* ASCII 108 */  0x00,0x00,0x10,0x00,0x10,0x20,0x1f,0xe0,0x10,0x00,0x10,0x00,0x00,0x00,
  /* ASCII 109 */  0x10,0x80,0x1f,0x80,0x10,0x80,0x1f,0x00,0x10,0x80,0x1f,0x00,0x10,0x00,
  /* ASCII 110 */  0x10,0x80,0x1f,0x80,0x11,0x00,0x00,0x80,0x10,0x80,0x1f,0x00,0x10,0x00,
  /* ASCII 111 */  0x00,0x00,0x0f,0x00,0x10,0x80,0x10,0x80,0x10,0x80,0x0f,0x00,0x00,0x00,
  /* ASCII 112 */  0x40,0x80,0x7f,0x80,0x51,0x00,0x10,0x80,0x10,0x80,0x0f,0x00,0x00,0x00,
  /* ASCII 113 */  0x00,0x00,0x0f,0x00,0x10,0x80,0x10,0x80,0x51,0x00,0x7f,0x80,0x40,0x80,
  /* ASCII 114 */  0x00,0x00,0x10,0x80,0x1f,0x80,0x11,0x00,0x10,0x80,0x10,0x80,0x00,0x00,
  /* ASCII 115 */  0x00,0x00,0x19,0x00,0x12,0x80,0x12,0x80,0x12,0x80,0x0d,0x80,0x00,0x00,
  /* ASCII 116 */  0x00,0x00,0x00,0x80,0x0f,0xc0,0x10,0x80,0x10,0x80,0x10,0x80,0x08,0x00,
  /* ASCII 117 */  0x00,0x80,0x0f,0x80,0x10,0x00,0x10,0x00,0x08,0x80,0x1f,0x80,0x10,0x00,
  /* ASCII 118 */  0x00,0x80,0x03,0x80,0x0c,0x80,0x10,0x00,0x0c,0x80,0x03,0x80,0x00,0x80,
  /* ASCII 119 */  0x00,0x80,0x0f,0x80,0x10,0x80,0x0e,0x00,0x10,0x80,0x0f,0x80,0x00,0x80,
  /* ASCII 120 */  0x10,0x80,0x19,0x80,0x06,0x00,0x06,0x00,0x19,0x80,0x10,0x80,0x00,0x00,
  /* ASCII 121 */  0x00,0x80,0x41,0x80,0x46,0x80,0x78,0x00,0x4c,0x80,0x03,0x80,0x00,0x80,
  /* ASCII 122 */  0x00,0x00,0x19,0x80,0x14,0x80,0x12,0x80,0x11,0x80,0x18,0x80,0x00,0x00,
  /* ASCII 123 */  0x00,0x00,0x00,0x00,0x04,0x00,0x3b,0xc0,0x40,0x20,0x00,0x00,0x00,0x00,
  /* ASCII 124 */  0x00,0x00,0x00,0x00,0x00,0x00,0x3f,0xe0,0x00,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 125 */  0x00,0x00,0x00,0x00,0x40,0x20,0x3b,0xc0,0x04,0x00,0x00,0x00,0x00,0x00,
  /* ASCII 126 */  0x00,0x00,0x04,0x00,0x02,0x00,0x04,0x00,0x04,0x00,0x02,0x00,0x00,0x00};

int OrientationOffsetX [] = { 0 /* V12*/,0 /* V3*/,+4 /* V6*/,+4 /* V9*/ };
int OrientationOffsetY [] = { +4 /* V12*/,0 /* V3*/,0 /* V6*/,+4 /* V9*/ };

/* Private function prototypes -----------------------------------------------*/
static void LCD_7637_Controller( void );
static void LCD_DrawChar( u8 x, u8 y, u8 width, const u8 *bmp, u16 textColor, u16 bGndColor, u16 charMagniCoeff );
static void LCD_BackLightChange( void );
static void LCD_BackLightConfig( void );
static void LCD_CtrlLinesWrite( GPIO_TypeDef* GPIOx, u32 CtrlPins, BitAction BitVal );

/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
*
*                                LCD_DataLinesConfig
*
*******************************************************************************/
/**
*  Configure data lines D0~D7 in Input Floating mode for read from LCD or in
*  Output Push-Pull mode for write on LCD
*
*  @param[in]  Mode Specifies the configuration mode for data lines D0~D7.
*                @n @c Input: configure in Input Floating mode
*                @n @c Output: configure in Output Push-Pul mode
*
**/
/******************************************************************************/
static void LCD_DataLinesConfig( DataConfigMode_TypeDef Mode )
   {
   GPIO_InitTypeDef             GPIO_InitStructure;
	   
   GPIO_InitStructure.GPIO_Pin   =  LCD_DATA_PINS;
   GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;

   if( Mode == Input )
      {
      /* Configure D0~D7 lines as Input */
      GPIO_InitStructure.GPIO_Mode = GPIO_Mode_IN_FLOATING;
      }
   else
      {
      /* Configure D0~D7 lines in Output Push-Pull mode */
      GPIO_InitStructure.GPIO_Mode = GPIO_Mode_Out_PP;
      }

   GPIO_Init( GPIOx_D_LCD, &GPIO_InitStructure );
   }

/*******************************************************************************
*
*                                LCD_DataLinesWrite
*
*******************************************************************************/
/**
*  Write a value on D0~D7
*
*  @param[in]  GPIOx    GPIO port to write on.
*  @param[in]  PortVal  The value to write. Only the lowest 8 bits are taken into
*                       account.
*
**/
/******************************************************************************/
static void LCD_DataLinesWrite( GPIO_TypeDef* GPIOx, u32 PortVal )
   {
   // Write only the lowest 8 bits!
   GPIOx->ODR = ( (GPIOx->ODR) & 0xFF00 ) | (u8)PortVal;
   }

/*******************************************************************************
*
*                                LCD_CtrlLinesConfig
*
*******************************************************************************/
/**
*  Configure control lines in Output Push-Pull mode.
*
**/
/******************************************************************************/
static void LCD_CtrlLinesConfig( void )
   {
   GPIO_InitTypeDef             GPIO_InitStructure;
	   
   GPIO_InitStructure.GPIO_Pin   =  LCD_CTRL_PINS;
   GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;
   GPIO_InitStructure.GPIO_Mode  = GPIO_Mode_Out_PP;

   GPIO_Init( GPIOx_CTRL_LCD, &GPIO_InitStructure );

   GPIO_InitStructure.GPIO_Pin   =  CtrlPin_CS;
   GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;
   GPIO_InitStructure.GPIO_Mode  = GPIO_Mode_Out_PP;

   GPIO_Init( GPIOx_CS_LCD, &GPIO_InitStructure );

   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RS,  Bit_SET );    /* RS = 1   */
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RD,  Bit_SET );    /* RD = 1   */
   LCD_CtrlLinesWrite( GPIOx_CS_LCD,   CtrlPin_CS,  Bit_SET );    /* CS = 1   */
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_WR,  Bit_SET );    /* WR = 1   */
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RST, Bit_RESET );  /* RST = 0  */
   }

/*******************************************************************************
*
*                                LCD_CtrlLinesWrite
*
*******************************************************************************/
/**
*  Set or reset control lines.
*
*  @param[in]  GPIOx       Where x can be 0, 1 or 2 to select the GPIO peripheral.
*  @param[in]  CtrlPins    The Control line.
*  @param[in]  BitVal
*
**/
/******************************************************************************/
static void LCD_CtrlLinesWrite( GPIO_TypeDef* GPIOx, u32 CtrlPins, BitAction BitVal )
   {
   /* Set or Reset the control line */
   GPIO_WriteBit( GPIOx, CtrlPins, BitVal );
   }

/*******************************************************************************
*
*                                LCD_CheckLCDStatus
*
*******************************************************************************/
/**
*  Check whether LCD LCD is busy or not.
*
**/
/******************************************************************************/
static void LCD_CheckLCDStatus( void )
   {
   unsigned char ID1;
   unsigned char ID2;
   unsigned char ID3;

   LCD_SendLCDCmd( ST7637_RDDID );

   /* Configure Data lines as Input */
   LCD_DataLinesConfig (Input );

   /* Start the LCD send data sequence */
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RS, Bit_RESET );     /* RS = 0 */
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RD, Bit_RESET );     /* RD = 0 */
   LCD_CtrlLinesWrite( GPIOx_CS_LCD,   CtrlPin_CS, Bit_RESET );     /* CS = 0 */
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_WR, Bit_SET );       /* WR = 1 */

   /* Read data to the LCD */
   GPIO_ReadInputData( GPIOx_D_LCD );
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RD, Bit_SET );       /* RD = 1 */
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RD, Bit_RESET );     /* RD = 0 */

   ID1 = GPIO_ReadInputData( GPIOx_D_LCD );

   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RD, Bit_SET );       /* RD = 1 */
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RD, Bit_RESET );     /* RD = 0 */

   ID2 = GPIO_ReadInputData( GPIOx_D_LCD );

   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RD, Bit_SET );       /* RD = 1 */
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RD, Bit_RESET );     /* RD = 0 */

   ID3 = GPIO_ReadInputData( GPIOx_D_LCD );

   LCD_DataLinesConfig( Output );
   }

/*******************************************************************************
*
*                                LCD_DrawChar
*
*******************************************************************************/
/**
*  Draw a character on the LCD screen.
*
*  @param[in]  x           The line where to display the character shape.
*  @param[in]  y           The column start address.
*  @param[in]  width       The number of columns (dots) in a character width.
*  @param[in]  bmp         The character (monochrome) bitmap. A pointer of the dot matrix data.
*  @param[in]  textColor   The character color.
*  @param[in]  bGndColor   The character background color.
*  @param[in]  charMagniCoeff The character magnifying coefficient.
*
*  @warning    The (0x0) point in on the low left corner.
*
**/
/******************************************************************************/
static void LCD_DrawChar( u8 x, u8 y, u8 width, const u8* bmp, u16 textColor, u16 bGndColor, u16 charMagniCoeff )
   {
   int i;
   int j;
   int k1;
   int k2;

   // Select the area for LCD output.
   LCD_SetRect_For_Cmd( x, y, 7 * charMagniCoeff, 14 * charMagniCoeff );

   // Select LCD output mode.
   LCD_SendLCDCmd( ST7637_RAMWR );

   for( i = 0; i < 7; i++ )
      {
      for( k1 = 0; k1 < charMagniCoeff; k1++ )
         {
         for( j = 0x80; j; j >>= 1 ) // 8
            {
            for( k2 = 0; k2 < charMagniCoeff; k2++ )
               {
               LCD_SendLCDData( ( bmp[2*i] & j ) ? ( textColor & 255 ) : ( bGndColor &  255 ) );
               LCD_SendLCDData( ( bmp[2*i] & j ) ? ( textColor >> 8  ) : ( bGndColor >> 8 ) );
               }
            }

         for( j = 0x80; j > 2; j >>= 1 )  // 8
            {
            for( k2 = 0; k2 < charMagniCoeff; k2++ )
               {
               LCD_SendLCDData( ( bmp[2*i+1] & j ) ? ( textColor & 255 ) : ( bGndColor & 255 ) );
               LCD_SendLCDData( ( bmp[2*i+1] & j ) ? ( textColor >> 8  ) : ( bGndColor >> 8 ) );
               }
            }
         }
      }
   }

/*******************************************************************************
*
*                                LCD_DisplayRotate
*
*******************************************************************************/
/**
*  Configure the LCD controller for a given orientation.
*
*  @param[in]  H12 The new screen orientation.
*
**/
/******************************************************************************/
static void LCD_DisplayRotate( Rotate_H12_V_Match_TypeDef H12 )
   {
   // Memory Access Control 0x36
   LCD_SendLCDCmd( ST7637_MADCTR );

   switch( H12 )
      {
      case V3  :
         LCD_SendLCDData( V3_MADCTRVAL );
         break;

      case V6  :
         LCD_SendLCDData( V6_MADCTRVAL );
         break;

      case V9  :
         LCD_SendLCDData( V9_MADCTRVAL );
         break;

      case V12 :
      default  :
         LCD_SendLCDData( V12_MADCTRVAL );
         break;
      }
   }

/*******************************************************************************
*
*                                LCD_7637_Controller
*
*******************************************************************************/
/**
*  Initialization of the controller registers.
*
*  @note See ST7637.PDF for more information.
*
**/
/******************************************************************************/
static void LCD_7637_Controller( void )
   {
   extern void starting_delay ( long unsigned  );

   /** Apply hardware reset **/
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RST, Bit_SET );    /* RST = 1  */
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RST, Bit_RESET );  /* RST = 0  */
   starting_delay( 0x500 );

   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RST, Bit_SET );    /* RST = 1  */
   starting_delay( 0x500 );

   //default mode is output
   LCD_DataLinesConfig( Output );

   LCD_CheckLCDStatus();

   LCD_SendLCDCmd( ST7637_SWRESET );

   //-----------disable autoread + Manual read once ----------------------------
   LCD_SendLCDCmd( ST7637_AUTOLOADSET );  // Auto Load Set 0xD7
   LCD_SendLCDData( 0xBF );               // Auto Load Disable

   LCD_SendLCDCmd( ST7637_EPCTIN );       // EE Read/write mode 0xE0
   LCD_SendLCDData( 0x00 );               // Set read mode

   LCD_SendLCDCmd( ST7637_EPMRD );        // Read active 0xE3
   LCD_SendLCDCmd( ST7637_EPCTOUT );      // Cancel control 0xE1

   //---------------------------------- Sleep OUT ------------------------------
   LCD_SendLCDCmd( ST7637_DISPOFF );      // display off 0x28
   LCD_SendLCDCmd( ST7637_SLPOUT );       // Sleep Out 0x11

   //--------------------------------Vop setting--------------------------------
   LCD_SendLCDCmd( ST7637_VOPSET );       // Set Vop by initial Module 0xC0
   LCD_SendLCDData( 0xFB );               // Vop = 13.64
   LCD_SendLCDData( 0x00 );               // base on Module

   //----------------------------Set Register-----------------------------------
   LCD_SendLCDCmd( ST7637_BIASSEL );      // Bias select 0xC3
   LCD_SendLCDData( 0x00 );               // 1/12 Bias, base on Module

   LCD_SendLCDCmd( ST7637_BSTBMPXSEL );   // Setting Booster times 0xC4
   LCD_SendLCDData( 0x05 );               // Booster X 8

   LCD_SendLCDCmd( ST7637_BSTEFFSEL );    // Booster eff 0xC5
   LCD_SendLCDData( 0x11 );               // BE = 0x01 (Level 2)

   LCD_SendLCDCmd( ST7637_VGSORCSEL );    // Vg with booster x2 control 0xcb
   LCD_SendLCDData( 0x01 );               // Vg from Vdd2

   LCD_SendLCDCmd( ST7637_ID1SET );       // ID1 = 00 0xcc
   LCD_SendLCDData( 0x00 );               //

   LCD_SendLCDCmd( ST7637_ID3SET );       // ID3 = 00 0xce
   LCD_SendLCDData( 0x00 );               //

   LCD_SendLCDCmd( 0xB7 );                // Glass direction
   LCD_SendLCDData( 0xC0 );               //

   LCD_SendLCDCmd( ST7637_ANASET );       // Analog circuit setting 0xd0
   LCD_SendLCDData( 0x1D );               //

   LCD_SendLCDCmd( 0xB4 );                // PTL mode set
   LCD_SendLCDData( 0x18 );               // power normal mode
   LCD_SendLCDCmd( ST7637_INVOFF );       // Display Inversion OFF 0x20

   LCD_SendLCDCmd( 0x2A );                // column range
   LCD_SendLCDData( 0x04 );               //
   LCD_SendLCDData( 0x83 );               //

   LCD_SendLCDCmd( 0x2B );                // raw range
   LCD_SendLCDData( 0x04 );               //
   LCD_SendLCDData( 0x83 );               //


   LCD_SendLCDCmd( ST7637_COLMOD );       // Color mode = 65k 0x3A
   LCD_SendLCDData( 0x05 );               //

   LCD_SendLCDCmd( ST7637_MADCTR );       // Memory Access Control 0x36
   LCD_SendLCDData( V9_MADCTRVAL );

   LCD_SendLCDCmd( ST7637_DUTYSET );      // Duty = 132 duty 0xb0
   LCD_SendLCDData( 0x7F );

   LCD_SendLCDCmd( 0x29 );                // Display ON
   LCD_SendLCDCmd( 0xF9 );                // Gamma
   LCD_SendLCDData( 0x00 );               //
   LCD_SendLCDData( 0x03 );               //
   LCD_SendLCDData( 0x05 );               //
   LCD_SendLCDData( 0x07 );               //
   LCD_SendLCDData( 0x09 );               //
   LCD_SendLCDData( 0x0B );               //
   LCD_SendLCDData( 0x0D );               //
   LCD_SendLCDData( 0x0F );               //
   LCD_SendLCDData( 0x11 );               //
   LCD_SendLCDData( 0x13 );               //
   LCD_SendLCDData( 0x15 );               //
   LCD_SendLCDData( 0x17 );               //
   LCD_SendLCDData( 0x19 );               //
   LCD_SendLCDData( 0x1B );               //
   LCD_SendLCDData( 0x1D );               //
   LCD_SendLCDData( 0x1F );               //
   }

/*******************************************************************************
*
*                                LCD_BackLightConfig
*
*******************************************************************************/
/**
*  Setting of the PWM that drives the backlight intensity.
*
**/
/******************************************************************************/
static void LCD_BackLightConfig( void )
   {
   GPIO_InitTypeDef GPIO_InitStructure;

   /* Enable GPIOB clock  */
   RCC_APB2PeriphClockCmd( RCC_APB2Periph_GPIOB, ENABLE );

   /* GPIOB Configuration:TIM4 2 in Output */
   GPIO_InitStructure.GPIO_Pin   = GPIO_Pin_7;
   GPIO_InitStructure.GPIO_Mode  = GPIO_Mode_AF_PP;
   GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;

   GPIO_Init( GPIOB, &GPIO_InitStructure );

   /* TIM4 Configuration -----------------------------------------------------*/
   /* TIM4CLK = 12 MHz, Prescaler = 0x0 */

   /* Enable TIM4 clock */
   RCC_APB1PeriphClockCmd( RCC_APB1Periph_TIM4, ENABLE );

   TIM_DeInit( TIM4 );
   TIM_TimeBaseStructInit( &TIM_TimeBaseStructure );
   TIM_OCStructInit( &TIM_OCInitStructure );

   /* Time base configuration */
   TIM_TimeBaseStructure.TIM_Period          = 0xFFFF;
   TIM_TimeBaseStructure.TIM_Prescaler       = 0x0;
   TIM_TimeBaseStructure.TIM_ClockDivision   = 0x0;
   TIM_TimeBaseStructure.TIM_CounterMode     = TIM_CounterMode_Up;

   TIM_TimeBaseInit( TIM4, &TIM_TimeBaseStructure );

   /* Output Compare Toggle Mode configuration: Channel2 */
   TIM_OCInitStructure.TIM_OCMode   = TIM_OCMode_PWM1;
   TIM_OCInitStructure.TIM_OutputState = TIM_OutputState_Enable;
   TIM_OCInitStructure.TIM_Pulse    = Current_CCR_BackLightStart;

   TIM_OC2Init( TIM4, &TIM_OCInitStructure );
   TIM_OC4PreloadConfig( TIM4, TIM_OCPreload_Disable );

   TIM_ARRPreloadConfig( TIM4, ENABLE );

   /* Enable TIM4 IT */
   TIM_ITConfig( TIM4, TIM_IT_CC2, ENABLE );

   // Go !!!
   TIM_Cmd( TIM4, ENABLE );
   }

/*******************************************************************************
*
*                                LCD_BackLightChange
*
*******************************************************************************/
/**
*  Modify the PWM rate.
*
**/
/******************************************************************************/
static void LCD_BackLightChange( void )
   {
   /* Output Compare Toggle Mode configuration: Channel2 */
   TIM_OCInitStructure.TIM_Pulse = Current_CCR_BackLightStart;

   TIM_OCInit( TIM4, &TIM_OCInitStructure );
   }

/* Public functions for CircleOS ---------------------------------------------*/

/*******************************************************************************
*
*                                LCD_Init
*
*******************************************************************************/
/**
*
*  Initialize LCD. Called at CircleOS startup.
*
*  @attention  This function must <b>NOT</b> be called by the user.
*
**/
/******************************************************************************/
void LCD_Init( void )
   {
   LCD_SetBackLight( UTIL_ReadBackupRegister( BKP_BKLIGHT ) );

   /* Do some gpio configs*/
   GPIO_InitTypeDef GPIO_InitStructure;

   /* Enable GPIO clock for LCD */
   RCC_APB2PeriphClockCmd( GPIO_LCD_CTRL_PERIPH, ENABLE );
   RCC_APB2PeriphClockCmd( GPIO_LCD_D_PERIPH, ENABLE );
   RCC_APB2PeriphClockCmd( GPIO_LCD_CS_PERIPH, ENABLE );

   /* Enable GPIOC clock */
   RCC_APB2PeriphClockCmd( RCC_APB2Periph_GPIOC, ENABLE );

   /* Init BackLight*/
   LCD_BackLightConfig();

   /* Configure control lines signals as output mode */
   LCD_CtrlLinesConfig();

   /* LCD LCD Init */
   LCD_7637_Controller();
   }

/*******************************************************************************
*
*                                LCD_Handler
*
*******************************************************************************/
/**
*
*  Called by the CircleOS scheduler to manage LCD tasks.
*
*  @attention  This function must <b>NOT</b> be called by the user.
*
**/
/******************************************************************************/
void LCD_Handler( void )
   {
   if( ++HandlerDivider % BACKLIGHT_DIVIDER )
      {
      return;
      }

   LCD_BackLightChange();
   }


/// @endcond

/* Public functions ----------------------------------------------------------*/

/*******************************************************************************
*
*                                LCD_SendLCDCmd
*
*******************************************************************************/
/**
*
*  Send on command byte to the LCD.
*
*  @param[in]  Cmd   An unsigned char containing the user command to send to the LCD.
*
**/
/******************************************************************************/
void LCD_SendLCDCmd( u8 Cmd )
   {
   /* Start the LCD send data sequence */
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RS, Bit_RESET );     /* RS = 0 */
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RD, Bit_SET );       /* RD = 1 */
   LCD_CtrlLinesWrite( GPIOx_CS_LCD,   CtrlPin_CS, Bit_RESET );     /* CS = 0 */
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_WR, Bit_RESET );     /* WR = 0 */

   /* Write data to the LCD */
   LCD_DataLinesWrite( GPIOx_D_LCD, (u32)Cmd );
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_WR, Bit_SET );       /* WR = 1 */
   }

/*******************************************************************************
*
*                                LCD_SendLCDData
*
*******************************************************************************/
/**
*
*  Send one data byte to the LCD.
*
*  @param[in]  Data  An unsigned character containing the data to send to the LCD.
*  @pre        An LCD_SendLCDCmd was done with a command waiting for data.
*
*
**/
/******************************************************************************/
void LCD_SendLCDData( u8 Data )
   {
   /* Configure Data lines as Output */
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RS, Bit_SET );
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RD, Bit_SET );
   LCD_CtrlLinesWrite( GPIOx_CS_LCD,   CtrlPin_CS, Bit_RESET );
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_WR, Bit_RESET );

   /* Write data to the LCD */
   LCD_DataLinesWrite( GPIOx_D_LCD,(u32)Data );
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_WR, Bit_SET );
   }

/***********************************************************************************
*
*                                LCD_ReadLCDData
*
************************************************************************************/
/**
*
*  Read one data byte from the LCD.
*
*  @return     An unsigned 32 bit word containing the data returned by a LCD command.
*  @pre        An LCD_SendLCDCmd was done with a command returning data.
*
**/
/********************************************************************************/
u32 LCD_ReadLCDData( void )
   {
   u32 LCDData = 0;

   /* Configure Data lines as Input */
   LCD_DataLinesConfig(Input);

   /* Start the LCD send data sequence */
   LCD_CtrlLinesWrite( GPIOx_D_LCD,  CtrlPin_RS, Bit_SET );         /* RS = 1 */
   LCD_CtrlLinesWrite( GPIOx_D_LCD,  CtrlPin_WR, Bit_SET );         /* WR = 1 */
   LCD_CtrlLinesWrite( GPIOx_CS_LCD, CtrlPin_CS, Bit_RESET );       /* CS = 0 */
   LCD_CtrlLinesWrite( GPIOx_D_LCD,  CtrlPin_RD, Bit_RESET );       /* RD = 0 */

   /* Read data from the LCD */
   LCDData = (GPIO_ReadInputData( GPIOx_D_LCD ) & LCD_DATA_PINS );

   LCD_CtrlLinesWrite( GPIOx_D_LCD, CtrlPin_RD, Bit_SET );          /* RD = 1 */

   /* Read the LCD returned data */
   LCD_DataLinesConfig( Output );

   return LCDData;
   }

/*******************************************************************************
*
*                                LCD_FillRect
*
*******************************************************************************/
/**
*
*  Fill a rectangle with a provided color.
*
*  @param[in]  x        The horizontal coordinate of the rectangle low left corner.
*  @param[in]  y        The vertical coordinate of the rectangle low left corner.
*  @param[in]  width    The rectangle width in pixels.
*  @param[in]  height   The rectangle height in pixels.
*  @param[in]  color    The RGB color to fill the rectangle with.
*
*  @warning    The (0x0) point in on the low left corner.
*
**/
/******************************************************************************/
void LCD_FillRect( u16 x, u16 y, u16 width, u16 height, u16 color )
   {
   u8 Line;
   u8 Column;

   /* Select LCD screen area. */
   LCD_SetRect_For_Cmd( x, y, width, height );

   /* Send LCD RAM write command. */
   LCD_SendLCDCmd( ST7637_RAMWR );

   /* Fill selected LCD screen area with provided color. */
   for( Line = 0; Line < width; Line++ )
      {
      for( Column = 0; Column < height; Column++ )
         {
         LCD_SendLCDData( color & 0xff );
         LCD_SendLCDData( ( color >> 8 ) & 0xff );
         }
      }

   #ifdef TESTLCD
   /* Configure Data lines as Input */
   LCD_DataLinesConfig( Input );

   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RST, Bit_SET );    /* RST = 1  */
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RST, Bit_RESET );  /* RST = 0  */
   LCD_CtrlLinesWrite( GPIOx_CTRL_LCD, CtrlPin_RST, Bit_SET );    /* RST = 1  */

   /* Start the LCD send data sequence */
   LCD_CtrlLinesWrite( GPIOx_D_LCD,  CtrlPin_RS, Bit_SET );       /* RS = 1   */
   LCD_CtrlLinesWrite( GPIOx_D_LCD,  CtrlPin_RS, Bit_RESET );     /* RS = 0   */
   LCD_CtrlLinesWrite( GPIOx_D_LCD,  CtrlPin_RS, Bit_SET );       /* RS = 1   */

   LCD_CtrlLinesWrite( GPIOx_D_LCD,  CtrlPin_RS, Bit_SET );       /* RS = 1   */
   LCD_CtrlLinesWrite( GPIOx_D_LCD,  CtrlPin_RS, Bit_RESET );     /* RS = 0   */
   LCD_CtrlLinesWrite( GPIOx_D_LCD,  CtrlPin_RS, Bit_SET );       /* RS = 1   */

   LCD_CtrlLinesWrite( GPIOx_D_LCD,  CtrlPin_WR, Bit_SET );       /* WR = 1   */
   LCD_CtrlLinesWrite( GPIOx_D_LCD,  CtrlPin_WR, Bit_RESET );     /* WR = 1   */
   LCD_CtrlLinesWrite( GPIOx_D_LCD,  CtrlPin_WR, Bit_SET );       /* WR = 1   */

   LCD_CtrlLinesWrite( GPIOx_D_LCD,  CtrlPin_RD, Bit_SET );       /* RD = 1   */
   LCD_CtrlLinesWrite( GPIOx_D_LCD,  CtrlPin_RD, Bit_RESET );     /* RD = 0   */
   LCD_CtrlLinesWrite( GPIOx_D_LCD,  CtrlPin_RD, Bit_SET );       /* RD = 1   */

   LCD_CtrlLinesWrite( GPIOx_D_LCD,  CtrlPin_RD, Bit_SET );       /* RD = 1   */
   LCD_CtrlLinesWrite( GPIOx_D_LCD,  CtrlPin_RD, Bit_RESET );     /* RD = 0   */
   LCD_CtrlLinesWrite( GPIOx_D_LCD,  CtrlPin_RD, Bit_SET );       /* RD = 1   */

   /* Configure Data lines as Input */
   LCD_DataLinesConfig( Output );

   LCD_DataLinesWrite( GPIOx_D_LCD, ~0 );
   LCD_DataLinesWrite( GPIOx_D_LCD, 0 );
   LCD_DataLinesWrite( GPIOx_D_LCD, ~1 );
   LCD_DataLinesWrite( GPIOx_D_LCD, 1 );
   LCD_DataLinesWrite( GPIOx_D_LCD, ~2 );
   LCD_DataLinesWrite( GPIOx_D_LCD, 2 );
   LCD_DataLinesWrite( GPIOx_D_LCD, ~4 );
   LCD_DataLinesWrite( GPIOx_D_LCD, 4 );
   LCD_DataLinesWrite( GPIOx_D_LCD, ~8 );
   LCD_DataLinesWrite( GPIOx_D_LCD, 8 );
   LCD_DataLinesWrite( GPIOx_D_LCD, ~0x10 );
   LCD_DataLinesWrite( GPIOx_D_LCD, 0x10 );
   LCD_DataLinesWrite( GPIOx_D_LCD, ~0x20 );
   LCD_DataLinesWrite( GPIOx_D_LCD, 0x20 );
   LCD_DataLinesWrite( GPIOx_D_LCD, ~0x40 );
   LCD_DataLinesWrite( GPIOx_D_LCD, 0x40 );
   LCD_DataLinesWrite( GPIOx_D_LCD, ~0x80 );
   LCD_DataLinesWrite( GPIOx_D_LCD, 0x80 );

   LCD_DataLinesConfig( Input );

   #endif
   }

/*******************************************************************************
*
*                                LCD_DrawRect
*
*******************************************************************************/
/**
*
*  Draw a rectangle with a provided color.
*
*  @param[in]  x        The horizontal coordinate of the rectangle low left corner.
*  @param[in]  y        The vertical coordinate of the rectangle low left corner.
*  @param[in]  width    The rectangle width in pixels.
*  @param[in]  height   The rectangle height in pixels.
*  @param[in]  color    The RGB color to draw the rectangle with.
*
*  @warning    The (0x0) point in on the low left corner.
*
**/
/******************************************************************************/
void LCD_DrawRect( u16 x, u16 y, u16 width, u16 height, u16 color )
   {
   // Draw horizontal sides.
   LCD_FillRect( x, y,              width, 1, color );
   LCD_FillRect( x, y + height - 1, width, 1, color );

   // Draw vertical sides.
   LCD_FillRect( x,              y, 1, height, color );
   LCD_FillRect( x + width - 1,  y, 1, height, color );
   }

/*******************************************************************************
*
*                                LCD_DrawPixel
*
*******************************************************************************/
/**
*
*  Draw a pixel on the LCD with the provided color.
*
*  @param[in]  XPos     The horizontal coordinate of the pixel.
*  @param[in]  YPos     The vertical coordinate of the pixel.
*  @param[in]  Color    The RGB color to draw the pixel with.
*
*  @warning    The (0x0) point in on the low left corner.
*
**/
/******************************************************************************/
void LCD_DrawPixel( u8 XPos, u8 YPos, u16 Color )
   {
   /* Select LCD screen area. */
   LCD_SetRect_For_Cmd( XPos, YPos, 1, 1 );

   /* Send LCD RAM write command. */
   LCD_SendLCDCmd( ST7637_RAMWR );

   // Draw pixel.
   LCD_SendLCDData( Color );
   LCD_SendLCDData( Color >> 8 );
   }

/*******************************************************************************
*
*                                LCD_RectRead
*
*******************************************************************************/
/**
*
*  Save the pixels of a rectangle part of the LCD into a RAM variable.
*
*  @param[in]  x        The horizontal coordinate of the rectangle low left corner.
*  @param[in]  y        The vertical coordinate of the rectangle low left corner.
*  @param[in]  width    The rectangle width in pixels.
*  @param[in]  height   The rectangle height in pixels.
*  @param[out] bmp      The variable to store the read data into.
*
*  @warning    One pixel weights 2 bytes.
*  @warning    The (0x0) point in on the low left corner.
*
**/
/******************************************************************************/
void LCD_RectRead( u16 x, u16 y, u16 width, u16 height, u8* bmp )
   {
   int i;
   int bytesize = (width * height) *2; // 2 bytes per pixel.

   /* Select LCD screen area. */
   LCD_SetRect_For_Cmd( x, y, width, height );

   /* Send LCD RAM write command. */
   LCD_SendLCDCmd(ST7637_RAMRD);

   // First read byte is dummy!
   LCD_ReadLCDData();

   // Read pixels from LCD screen.
   for( i = 0; i < bytesize; i++ )
      {
      *bmp++ = LCD_ReadLCDData();
      }
   }

/*******************************************************************************
*
*                                LCD_GetPixel
*
*******************************************************************************/
/**
*
*  Read the RGB color of the pixel the coordinate are provided in parameter.
*
*  @param[in]  x        The horizontal coordinate of the pixel.
*  @param[in]  y        The vertical coordinate of the pixel.
*  @return              An unsigned 16 bit word containing the RGB color of the pixel.
*
*  @warning    The (0x0) point in on the low left corner.
*  @see        LCD_RectRead
*
**/
/******************************************************************************/
u16 LCD_GetPixel( u8 x, u8 y )
   {
   u16 val;

   LCD_RectRead( x, y, 1, 1, (u8*)&val );

   return val;
   }

/*******************************************************************************
*
*                                LCD_DisplayChar
*
*******************************************************************************/
/**
*
*  Display at provided coordinates the provided ASCII character with the provided
*  text and background colors and with the provided magnify coefficient.
*
*  @param[in]  x              The horizontal coordinate of the character.
*  @param[in]  y              The vertical coordinate of the character.
*  @param[in]  Ascii          The ASCII code of the character to display.
*                             @n Ascii must be higher than 31 and lower than 127.
*  @param[in]  TextColor      The color used to draw the character.
*  @param[in]  BGndColor      The background color of the drawn character.
*  @param[in]  CharMagniCoeff The magnify coefficient used to draw the character.
*
*  @warning    The (0x0) point in on the low left corner.
*
**/
/******************************************************************************/
void LCD_DisplayChar( u8 x, u8 y, u8 Ascii, u16 TextColor, u16 BGndColor, u16 CharMagniCoeff)
   {
   // Display the selected bitmap according to the provided ASCII character.
   LCD_DrawChar( x, y, 7, (u8*)&AsciiDotsTable[ (Ascii-32) * 14 ], TextColor, BGndColor, CharMagniCoeff );
   }

/*******************************************************************************
*
*                                LCD_SetRect_For_Cmd
*
*******************************************************************************/
/**
*
*  Define the rectangle for the next command to be applied.
*
*  @param[in]  x        The horizontal coordinate of the rectangle low left corner.
*  @param[in]  y        The vertical coordinate of the rectangle low left corner.
*  @param[in]  width    The rectangle width in pixels.
*  @param[in]  height   The rectangle height in pixels.
*
*  @warning    The (0x0) point in on the low left corner.
*
**/
/******************************************************************************/
void LCD_SetRect_For_Cmd( s16 x, s16 y, s16 width, s16 height )
   {
   LCD_SendLCDCmd( ST7637_CASET );
   LCD_SendLCDData( y + OrientationOffsetX[ CurrentScreenOrientation ] );
   LCD_SendLCDData( y + OrientationOffsetX[ CurrentScreenOrientation ] + height - 1 );

   LCD_SendLCDCmd( ST7637_RASET );
   LCD_SendLCDData( x + OrientationOffsetY[ CurrentScreenOrientation ] );
   LCD_SendLCDData( x + OrientationOffsetY[ CurrentScreenOrientation ] + width - 1 );
   }

/*******************************************************************************
*
*                                LCD_SetBackLight
*
*******************************************************************************/
/**
*
*  Modify the PWM rate. Any value below BACKLIGHTMIN reset the value to the
*  default value (DEFAULT_CCR_BACKLIGHTSTART).
*
*  @param[in]  newBacklightStart The new PWM rate.
*
**/
/******************************************************************************/
void LCD_SetBackLight( u32 newBacklightStart )
   {
   if( newBacklightStart >= BACKLIGHTMIN )
      {
      Current_CCR_BackLightStart = newBacklightStart;
      }
   else
      {
      Current_CCR_BackLightStart = DEFAULT_CCR_BACKLIGHTSTART;
      }
   }

/*******************************************************************************
*
*                                LCD_SetBackLightOff
*
*******************************************************************************/
/**
*
*  Switch the LCD back light off.
*
**/
/******************************************************************************/
void LCD_SetBackLightOff( void )
   {
   Current_CCR_BackLightStart = 0;
   }

/*******************************************************************************
*
*                                LCD_SetBackLightOn
*
*******************************************************************************/
/**
*
*  Switch the LCD back light on.
*
**/
/******************************************************************************/
void LCD_SetBackLightOn( void )
   {
   Current_CCR_BackLightStart = DEFAULT_CCR_BACKLIGHTSTART;
   }

/*******************************************************************************
*
*                                LCD_GetBackLight
*
*******************************************************************************/
/**
*
*  Returns le LCD PWM rate.
*
*  @return The current LCD PWM rate.
*
**/
/******************************************************************************/
u32 LCD_GetBackLight( void )
   {
   return Current_CCR_BackLightStart;
   }

/*******************************************************************************
*
*                                LCD_SetRotateScreen
*
*******************************************************************************/
/**
*
*  Enable or disable the ability of the screen display to rotate according to
*  the MEMs information.
*
*  @param[in]  RotateScreen 0 to disable screen rotation and 1 to enable.
*
**/
/******************************************************************************/
void LCD_SetRotateScreen( u8 RotateScreen)
   {
   CurrentRotateScreen = RotateScreen;
   }

/*******************************************************************************
*
*                                LCD_GetRotateScreen
*
*******************************************************************************/
/**
*
*  Return the screen rotation mode.
*
*  @retval 0 screen rotation is disabled.
*  @retval 1 screen rotation is enabled.
*
**/
/******************************************************************************/
u8 LCD_GetRotateScreen( void )
   {
   return CurrentRotateScreen;
   }

/*******************************************************************************
*
*                                LCD_SetScreenOrientation
*
*******************************************************************************/
/**
*
*  Set the screen orientation.
*
*  @param[in]  ScreenOrientation The new screen orientation.
*
**/
/******************************************************************************/
void LCD_SetScreenOrientation( Rotate_H12_V_Match_TypeDef ScreenOrientation )
   {
   CurrentScreenOrientation = ScreenOrientation;

   LCD_DisplayRotate( CurrentScreenOrientation );
   }

/*******************************************************************************
*
*                                LCD_GetScreenOrientation
*
*******************************************************************************/
/**
*
*  Return current screen orientation.
*
*  @return   A Rotate_H12_V_Match_TypeDef telling the current screen orientation.
*
**/
/******************************************************************************/
Rotate_H12_V_Match_TypeDef LCD_GetScreenOrientation( void )
   {
   return CurrentScreenOrientation;
   }

