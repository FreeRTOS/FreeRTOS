/********************* (C) COPYRIGHT 2007 RAISONANCE S.A.S. *******************/
/**
*
* @file     circle.h
* @brief    General header for the CircleOS project.
* @author   FL
* @date     07/2007
* @version  1.5
*
* It contains the list of the utilities functions organized by sections 
* (MEMS, LCD, POINTER, ...)
*
* @date     10/2007
* @version  1.5 types of OutX_F64 and OutX_F256 changed to u32 (same for Y and Z)
**/
/******************************************************************************/

#include "scheduler.h"

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __CIRCLE_H
#define __CIRCLE_H

//-------------------------------- General -------------------------------------
/* Defines  ------------------------------------------------------------------*/
#define VDD_VOLTAGE_MV  3300 //Voltage (mV) of the STM32
#define FA_TABLE        0x8006000
#define TIM2            ((TIM_TypeDef *) TIM2_BASE)
#define CIRCLEOS_RAM_BASE 0x20004000

/* Variables  ----------------------------------------------------------------*/
extern GPIO_InitTypeDef GPIO_InitStructure;

/* Utilities -----------------------------------------------------------------*/
void UTIL_uint2str( char *ptr , u32 X, u16 digit, int fillwithzero );
void UTIL_int2str( char *ptr , s32 X, u16 digit, int fillwithzero );
u16  UTIL_ReadBackupRegister( u16 BKP_DR );
void UTIL_WriteBackupRegister( u16 BKP_DR, u16 Data );
u16 UTIL_GetBat( void );
u8 UTIL_GetUsb( void );
u16 UTIL_GetTemp ( void ) ;
void UTIL_SetTempMode ( int mode );
//typedef void  (*tHandler)    ( void );
void UTIL_SetIrqHandler ( int , tHandler );
tHandler UTIL_GetIrqHandler ( int  );
extern u16  ADC_ConvertedValue[17];


extern enum eSpeed
   {
   SPEED_VERY_LOW    = 1,
   SPEED_LOW         = 2,
   SPEED_MEDIUM      = 3,
   SPEED_HIGH        = 4,
   SPEED_VERY_HIGH   = 5
   } CurrentSpeed;

enum eSchHandler
   {
   LED_SCHHDL_ID     = 0,
   BUTTON_SCHHDL_ID  = 1,
   BUZZER_SCHHDL_ID  = 2,
   MENU_SCHHDL_ID    = 3,
   POINTER_SCHHDL_ID = 4,
   LCD_SCHHDL_ID     = 5,
   DRAW_SCHHDL_ID    = 6,
   RTC_SCHHDL_ID     = 7,

   UNUSED0_SCHHDL_ID = 8,
   UNUSED1_SCHHDL_ID = 9,
   UNUSED2_SCHHDL_ID = 10,
   UNUSED3_SCHHDL_ID = 11,
   UNUSED4_SCHHDL_ID = 12,
   UNUSED5_SCHHDL_ID = 13,
   UNUSED6_SCHHDL_ID = 14,
   UNUSED7_SCHHDL_ID = 15   
   } dummy_var ; //for doxygen

void UTIL_SetSchHandler (  enum eSchHandler , tHandler );
tHandler UTIL_GetSchHandler (  enum eSchHandler  );
#define NULL_SCHHDL (0)
#define LAST_SCHHDL ((tHandler)(-1))


void UTIL_SetPll( enum eSpeed speed );
const char* UTIL_GetVersion( void );
enum eSpeed UTIL_GetPll( void );
extern RCC_ClocksTypeDef RCC_ClockFreq;
extern u8 fTemperatureInFahrenheit;  /*!< 1 : Fahrenheit, 0 : Celcius (default). */


//---------------------------------   MEMS  ------------------------------------

/* Exported types ------------------------------------------------------------*/
typedef enum
  {
    V12=0,
    V3=1,
    V6=2,
    V9=3
} Rotate_H12_V_Match_TypeDef;

typedef struct
   {
   s16 OutX ;
   s16 OutX_F4 ;
   s16 OutX_F16 ;
   s32 OutX_F64 ;
   s32 OutX_F256 ;
   s16 OutY ;
   s16 OutY_F4 ;
   s16 OutY_F16 ;
   s32 OutY_F64 ;
   s32 OutY_F256 ;
   s16 OutZ ;
   s16 OutZ_F4 ;
   s16 OutZ_F16 ;
   s32 OutZ_F64 ;
   s32 OutZ_F256 ;
   s16 Shocked ;
   s16 RELATIVE_X ;
   s16 RELATIVE_Y ;
   s16 DoubleClick ;
   } tMEMS_Info;

extern tMEMS_Info MEMS_Info;

/* Exported functions --------------------------------------------------------*/
void MEMS_Init(void);
void MEMS_Handler(void);
void MEMS_GetPosition(s16 * pX, s16* pY);
void MEMS_SetNeutral( void );
void MEMS_GetRotation(Rotate_H12_V_Match_TypeDef * H12);
tMEMS_Info* MEMS_GetInfo (void);
u8 MEMS_ReadID(void);

//----------------------------------   LED -------------------------------------

/* Exported types ------------------------------------------------------------*/
enum LED_mode { LED_UNDEF = -1, LED_OFF = 0, LED_ON = 1, LED_BLINKING_LF = 2, LED_BLINKING_HF = 3 };
enum LED_id { LED_GREEN = 0, LED_RED = 1};

/* Exported functions --------------------------------------------------------*/
void LED_Init (void);
void LED_Handler_hw ( enum LED_id id );
void LED_Handler ( void );
void LED_Set ( enum LED_id id, enum LED_mode mode );

//--------------------------------   ADC  --------------------------------------

/* Exported functions --------------------------------------------------------*/
void ADConverter_Init (void);


//==============================================================================
//--------------------------------   SHUTDOWN  ---------------------------------
/* Exported functions --------------------------------------------------------*/
void SHUTDOWN_Action (void);

//--------------------------------   BUTTON  -----------------------------------
/* Exported types ------------------------------------------------------------*/
enum BUTTON_mode  { BUTTON_DISABLED  = -1, BUTTON_ONOFF    = 0,
                     BUTTON_ONOFF_FORMAIN = 1, BUTTON_WITHCLICK  = 2 };
enum BUTTON_state { BUTTON_UNDEF = -1, BUTTON_RELEASED = 0, BUTTON_PUSHED = 1,
                     BUTTON_PUSHED_FORMAIN = 2 , BUTTON_CLICK = 3, BUTTON_DBLCLICK = 4 };

/* Exported functions -------------------------------------------------------*/
void BUTTON_Init (void);
void BUTTON_Handler(void);
enum BUTTON_state BUTTON_GetState();
void BUTTON_SetMode( enum BUTTON_mode mode);
enum BUTTON_mode BUTTON_GetMode ( void ) ;
void BUTTON_WaitForRelease();

//--------------------------------   POINTER  ----------------------------------

/* Exported types ------------------------------------------------------------*/
enum POINTER_mode  { POINTER_UNDEF  = -1, POINTER_OFF = 0, POINTER_ON = 1, POINTER_MENU  = 2, POINTER_APPLICATION = 3, POINTER_RESTORE_LESS = 4 };
enum POINTER_state { POINTER_S_UNDEF  = -1,  POINTER_S_DISABLED = 0, POINTER_S_ENABLED = 1 };

/* Exported defines ----------------------------------------------------------*/
#define POINTER_WIDTH 7

typedef struct
   {
   s16 xPos ;
   s16 yPos ;
   s16 shift_PosX ;
   s16 shift_PosY ;
   s16 X_PosMin ;
   s16 Y_PosMin ;
   s16 X_PosMax ;
   s16 Y_PosMax ;
   } tPointer_Info;

extern tPointer_Info POINTER_Info ;

/* Exported vars -------------------------------------------------------------*/
extern unsigned char *BallPointerBmpSize;
extern unsigned char BallPointerBmp [POINTER_WIDTH], *CurrentPointerBmp,*CurrentPointerSize;
extern u16 CurrentPointerColor;
extern u16 BallColor;
extern s16 POINTER_X_PosMin;
extern s16 POINTER_Y_PosMin;
extern s16 POINTER_X_PosMax;
extern s16 POINTER_Y_PosMax;
extern unsigned char PointerAreaStore [2*POINTER_WIDTH*POINTER_WIDTH];

/* Exported functions --------------------------------------------------------*/
extern void POINTER_Init ( void ) ;
void POINTER_Handler(void);
u16  POINTER_GetCurrentAngleStart ( void );
void POINTER_SetCurrentAngleStart ( u16 );
u16  POINTER_GetCurrentSpeedOnAngle ( void );
void POINTER_SetCurrentSpeedOnAngle ( u16  newspeed );
void POINTER_SetMode( enum POINTER_mode mode);
void POINTER_SetCurrentPointer( unsigned char width, unsigned char height, unsigned char *bmp);
enum POINTER_state POINTER_GetState(void);
void POINTER_Draw (u8 Line, u8 Column, u8 Width, u8 Height, u8 *Bmp);
void POINTER_SetRect ( s16 x, s16 y, s16 width, s16 height );  //Restrict the move of the pointer to a rectangle
void POINTER_SetRectScreen ( void );   //Remove any space restriction for the pointer moves.
void POINTER_Save (u8 Line, u8 Column, u8 Width, u8 Height);
void POINTER_Restore (u8 Line, u8 Column, u8 Width, u8 Height);
u16  POINTER_GetPos(void);     //Return the poistion of the cursor (x=lower byte, y = upperbyte)
void POINTER_SetPos ( u16 x, u16 y );
typedef void  (*tAppPtrMgr) ( int , int );
void POINTER_SetApplication_Pointer_Mgr(  tAppPtrMgr mgr );
tPointer_Info* POINTER_GetInfo ( void );
u16 POINTER_GetColor ( void ) ;
void POINTER_SetColor ( u16 color );
enum POINTER_mode POINTER_GetMode( void );
void POINTER_SetCurrentAreaStore ( u8 *ptr );
void LCD_SetRotateScreen ( u8 RotateScreen);
u8 LCD_GetRotateScreen ();
void LCD_SetScreenOrientation (Rotate_H12_V_Match_TypeDef ScreenOrientation);
Rotate_H12_V_Match_TypeDef LCD_GetScreenOrientation ();

//----------------------------------   LCD   -----------------------------------

/* Exported defines ----------------------------------------------------------*/
//RGB is 16-bit coded as    G2G1G0B4 B3B2B1B0 R4R3R2R1 R0G5G4G3
#define RGB_MAKE(xR,xG,xB)    ( ( (xG&0x07)<<13 ) + ( (xG)>>5 )  +      \
                                ( ((xB)>>3) << 8 )          +      \
                                ( ((xR)>>3) << 3 ) )
#define RGB_RED         0x00F8
#define RGB_BLACK       0x0000
#define RGB_WHITE       0xffff
#define RGB_BLUE        0x1F00
#define RGB_GREEN       0xE007
#define RGB_YELLOW      (RGB_GREEN|RGB_RED)
#define RGB_MAGENTA     (RGB_BLUE|RGB_RED)
#define RGB_LIGHTBLUE   (RGB_BLUE|RGB_GREEN)
#define RGB_ORANGE      (RGB_RED | 0xE001)   //green/2 + red
#define RGB_PINK        (RGB_MAGENTA | 0xE001)   //green/2 + magenta

// SCREEN Infos
#define SCREEN_WIDTH        128
#define SCREEN_HEIGHT        128
#define CHIP_SCREEN_WIDTH    132
#define CHIP_SCREEN_HEIGHT 132

// Characters Infos
#define CHAR_WIDTH            7
#define CHAR_HEIGHT           14

// PWM rates.
#define BACKLIGHTMIN                0x1000   /*!< Minimal PWM rate.           */
#define DEFAULT_CCR_BACKLIGHTSTART  0x8000   /*!< Default PWM rate.           */

/* Exported vars -------------------------------------------------------------*/
extern Rotate_H12_V_Match_TypeDef Screen_Orientation;
extern int rotate_screen;

/* Exported functions --------------------------------------------------------*/
void LCD_Init(void);
void LCD_Handler(void);
void LCD_SetRect_For_Cmd( s16 x, s16 y, s16 width, s16 height );
u16  LCD_GetPixel( u8 x, u8 y );
void LCD_DrawPixel( u8 x, u8 y, u16 Pixel );
void LCD_SendLCDCmd( u8 Cmd );
void LCD_SendLCDData( u8 Data );
u32  LCD_ReadLCDData( void );
void LCD_FillRect( u16 x, u16 y, u16 width, u16 height, u16 color );
void LCD_DrawRect( u16 x, u16 y, u16 width, u16 height, u16 color );
void LCD_DisplayChar( u8 x, u8 y, u8 Ascii, u16 TextColor, u16 BGndColor, u16 CharMagniCoeff );
void LCD_RectRead( u16 x, u16 y, u16 width, u16 height, u8* bmp );
void LCD_SetBackLight (u32 newBacklightStart);
u32  LCD_GetBackLight ( void );
void LCD_SetBackLightOff( void );
void LCD_SetBackLightOn( void );

#include "lcd.h"

//----------------------------------   DRAW   ----------------------------------

/* Exported functions --------------------------------------------------------*/
void DRAW_Init(void);
void DRAW_Clear(void);
void DRAW_Handler(void);
void DRAW_SetDefaultColor (void);
void DRAW_SetImage(const u16 *imageptr, u8 x, u8 y, u8 width, u8 height);
void DRAW_SetImageBW(const u8 *imageptr, u8 x, u8 y, u8 width, u8 height);
void DRAW_SetLogoBW(void);
void DRAW_DisplayVbat(u8 x, u8 y);
void DRAW_DisplayTime(u8 x, u8 y);
void DRAW_DisplayTemp(u8 x, u8 y);
void DRAW_DisplayString( u8 x, u8 y, const u8 *ptr, u8 len );
void DRAW_DisplayStringInverted( u8 x, u8 y, const u8 *ptr, u8 len );
u16  DRAW_GetCharMagniCoeff(void);
void DRAW_SetCharMagniCoeff(u16 Coeff);
u16  DRAW_GetTextColor(void);
void DRAW_SetTextColor(u16 Color);
u16  DRAW_GetBGndColor(void);
void DRAW_SetBGndColor(u16 Color);
void DRAW_Batt( void );
void DRAW_Line (s16 x1, s16 y1, s16 x2, s16 y2, u16 color );

/* Exported vars -------------------------------------------------------------*/
extern int fDisplayTime;


//--------------------------------   BUZZER  -----------------------------------

/* Exported defines ----------------------------------------------------------*/
#define BUZZER_BEEP  BUZZER_SHORTBEEP

/* Exported type def ---------------------------------------------------------*/
enum  BUZZER_mode  { BUZZER_UNDEF  = -1, BUZZER_OFF    = 0, BUZZER_ON    = 1,
                        BUZZER_SHORTBEEP  = 2, BUZZER_LONGBEEP  = 3, BUZZER_PLAYMUSIC = 4 };

/* Exported type functions ---------------------------------------------------*/
void  BUZZER_Init(void);
void  BUZZER_Handler(void);
void  BUZZER_SetMode( enum BUZZER_mode mode);
enum  BUZZER_mode BUZZER_GetMode( void );
void  BUZZER_PlayMusic (const u8 *melody );

//---------------------------------   MENU   -----------------------------------

/* Exported defines ----------------------------------------------------------*/
#define MENU_MAXITEM 6
#define APP_VOID ((tMenuItem *)(-1))
#define MAX_APP_MENU_SIZE 10
#define MAXAPP  64
#define MAX_MENUAPP_SIZE 3
#define REMOVE_MENU  0x01
#define APP_MENU     0x02

enum  MENU_code  {   MENU_LEAVE  = 0, MENU_CONTINUE = 1, MENU_REFRESH = 2,
                        MENU_CHANGE = 3, MENU_CONTINUE_COMMAND = 4};

/* Exported type def ---------------------------------------------------------*/
typedef struct
   {
   const char *Text;
   enum MENU_code (*Fct_Init)  ( void );
   enum MENU_code (*Fct_Manage)( void );
   int fMenuFlag;
   } tMenuItem;

typedef struct
   {
   unsigned fdispTitle : 1;
   const char *Title;
   int NbItems;
   int LgMax;
   int XPos, YPos;
   int XSize, YSize;
   unsigned int SelectedItem;
   tMenuItem Items[MENU_MAXITEM];
   } tMenu;

/* Exported vars -------------------------------------------------------------*/
extern tMenu MainMenu, *CurrentMenu;
extern tMenuItem *CurrentCommand;
extern int BGndColor_Menu;
extern int TextColor_Menu;

/* Exported type functions ---------------------------------------------------*/
enum  MENU_code fColor ( void ) ;
void  MENU_Set ( tMenu *mptr );
void  MENU_Handler ( void ) ;
extern enum MENU_code MENU_Quit ( void );
void  MENU_Remove ( void ) ;
void  MENU_Question ( char *str, int *answer );
void  MENU_Print ( char *str );
enum  MENU_code MENU_SetLevel_Ini( void );
enum  MENU_code MENU_SetLevel_Mgr( u32 *value, u32 value_range [] ) ;
void  MENU_ClearCurrentCommand( void );
void  MENU_SetLevelTitle(u8* title);
void  MENU_SetTextColor ( int TextColor );
int   MENU_GetTextColor ( void );
void  MENU_SetBGndColor ( int BGndColor );
int   MENU_GetBGndColor ( void );
extern enum MENU_code fQuit ( void ) ;
void MENU_ClearCurrentMenu(void);

//--------------------------------   BACKLIGHT  --------------------------------

/* Exported type functions ---------------------------------------------------*/
void  BackLight_Configuration (void);
void  ManageBackLight (void);
void  BackLight_Change (void);

//--------------------------------   RTC  --------------------------------------

/* Exported type functions ---------------------------------------------------*/
void  RTC_Init(void);
void  RTC_SetTime (u32 THH, u32 TMM, u32 TSS);
void  RTC_GetTime (u32 * THH, u32 * TMM, u32 * TSS);
void  RTC_DisplayTime ( void );

//Backup registers
#define BKP_SYS1     1
#define BKP_SYS2     2
#define BKP_SYS3     3
#define BKP_SYS4     4
#define BKP_SYS5     5
#define BKP_SYS6     6
#define BKP_USER1    7
#define BKP_USER2    8
#define BKP_USER3    9
#define BKP_USER4    10

#define BKP_PLL      (BKP_SYS2)
#define BKP_BKLIGHT  (BKP_SYS3)

//--------------------------------- Application --------------------------------
void  (*Application_Pointer_Mgr) ( int sposX, int sposY);

#endif /*__CIRCLE_H */
