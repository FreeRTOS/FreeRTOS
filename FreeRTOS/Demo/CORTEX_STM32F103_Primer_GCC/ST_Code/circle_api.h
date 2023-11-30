/********************* (C) COPYRIGHT 2007 RAISONANCE S.A.S. *******************/
/**
*
* @file     circle_api.h
* @brief    General header for the STM32-circle projects.
* @author   FL
* @date     07/2007
* @version  1.2
* @date     10/2007
* @version  1.5 types of OutX_F64 and OutX_F256 changed to u32 (same for Y and Z)
* @date     10/2007
* @version  1.6 Add the IRQ handler replacement
*
* It contains the list of the utilities functions organized by sections
* (MEMS, LCD, POINTER, ...)
*
**/
/*******************************************************************************
*
* Use this header with version 1.5 or later of the OS.
*
* For a complete documentation on the CircleOS, please go to:
*  http://www.stm32circle.com
*
*******************************************************************************/

#include "stm32f10x_lib.h"

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __CIRCLE_API_H
#define __CIRCLE_API_H

//-------------------------------- General -------------------------------------

/**
* @enum  eSpeed
* @brief Clock speeds.
*
* Available clock speeds.
**/
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
   }; 


/// @cond Internal

extern RCC_ClocksTypeDef RCC_ClockFreq;

/* Typedefs ------------------------------------------------------------------*/
typedef u32 (*tCircleFunc0 ) (void);
typedef u32 (*tCircleFunc1 ) (u32 param1);
typedef u32 (*tCircleFunc2 ) (u32 param1, u32 param2);
typedef u32 (*tCircleFunc3 ) (u32 param1, u32 param2, u32 param3);
typedef u32 (*tCircleFunc4 ) (u32 param1, u32 param2, u32 param3, u32 param4);
typedef u32 (*tCircleFunc5 ) (u32 param1, u32 param2, u32 param3, u32 param4, u32 param5);
typedef u32 (*tCircleFunc6 ) (u32 param1, u32 param2, u32 param3, u32 param4, u32 param5, u32 param6);

extern tCircleFunc0 (*ptrCircle_API) [];

/* Defines -------------------------------------------------------------------*/
#define Circle_API   (*ptrCircle_API)

#define POINTER_ID   0x00
#define DRAW_ID      0x20
#define LCD_ID       0x40
#define LED_ID       0x60
#define MEMS_ID      0x70
#define BUTTON_ID    0x80
#define BUZZER_ID    0x90
#define MENU_ID      0xA0
#define UTIL_ID      0xB0
#define RTC_ID       0xC0

// UTIL functions definition.
#define UTIL_SET_PLL_ID                 (UTIL_ID + 0)    // Set clock frequency.
#define UTIL_GET_PLL_ID                 (UTIL_ID + 1)    // Get clock frequency.
#define UTIL_UINT2STR_ID                (UTIL_ID + 2)    // Convert an unsigned integer into a string.
#define UTIL_INT2STR_ID                 (UTIL_ID + 3)    // Convert a signed integer into a string.
#define UTIL_GET_VERSION_ID             (UTIL_ID + 4)    // Get CircleOS version.
#define UTIL_READ_BACKUPREGISTER_ID     (UTIL_ID + 5)    // Reads data from the specified Data Backup Register.
#define UTIL_WRITE_BACKUPREGISTER_ID    (UTIL_ID + 6)    // Writes data to the specified Data Backup Register.
#define UTIL_GET_BAT_ID                 (UTIL_ID + 7)    // Return the batterie tension in mV.
#define UTIL_GET_USB_ID                 (UTIL_ID + 8)    // Return the USB connexion state.
#define UTIL_SET_IRQ_HANDLER_ID         (UTIL_ID + 9)    // Replace an irq handler
#define UTIL_GET_IRQ_HANDLER_ID         (UTIL_ID + 10)   // Get the current irq handler
#define UTIL_SET_SCH_HANDLER_ID         (UTIL_ID + 11)    // Replace an irq handler
#define UTIL_GET_SCH_HANDLER_ID         (UTIL_ID + 12)   // Get the current irq handler
#define UTIL_GET_TEMP_ID                (UTIL_ID + 13)   // Return the temperature (1/100 C)
#define UTIL_SET_TEMPMODE_ID            (UTIL_ID + 14)   // Set the temperature mode (0: mCelcius, 1: mFahrenheit
typedef void (*tHandler) (void);

// Prototypes.
#define UTIL_SetPll(a)                          ((tCircleFunc1)(Circle_API [UTIL_SET_PLL_ID])) ((u32)(a))                                    // void UTIL_SetPll( enum eSpeed speed );
#define UTIL_GetPll()                  (u32)    (((tCircleFunc0)(Circle_API [UTIL_GET_PLL_ID])) ())                                          // enum eSpeed UTIL_GetPll( void );
#define UTIL_uint2str(a,b,c,d)                  ((tCircleFunc4)(Circle_API [UTIL_UINT2STR_ID])) ((u32)(a),(u32)(b),(u32)(c),(u32)(d))        // void uint2str( char* ptr , u32 X, u16 digit, int fillwithzero );
#define UTIL_int2str(a,b,c,d)                   ((tCircleFunc4)(Circle_API [UTIL_INT2STR_ID])) ((u32)(a),(u32)(b),(u32)(c),(u32)(d))         // void  int2str( char* ptr , s32 X, u16 digit, int fillwithzero );
#define UTIL_GetVersion()              (u32)    (((tCircleFunc0)(Circle_API [UTIL_GET_VERSION_ID])) ())                                      // char* UTIL_GetVersion( void );
#define UTIL_ReadBackupRegister(a)     (u32)    (((tCircleFunc1)(Circle_API [UTIL_READ_BACKUPREGISTER_ID])) ((u32)(a)))                      // u16 UTIL_ReadBackupRegister( u16 BKP_DR );
#define UTIL_WriteBackupRegister(a,b)           ((tCircleFunc2)(Circle_API [UTIL_WRITE_BACKUPREGISTER_ID])) ((u32)(a),(u32)(b))              // void UTIL_WriteBackupRegister( u16 BKP_DR, u16 Data );
#define UTIL_GetBat()                  (u32)    (((tCircleFunc0)(Circle_API [UTIL_GET_BAT_ID])) ())                                          // u16 UTIL_GetBat( void );
#define UTIL_GetUsb()                  (u32)    (((tCircleFunc0)(Circle_API [UTIL_GET_USB_ID])) ())                                          // u8 UTIL_GetUsb( void );
#define UTIL_SetIrqHandler(a,b)                 (((tCircleFunc2)(Circle_API [UTIL_SET_IRQ_HANDLER_ID])) ((int)a,(tHandler)b))                // void UTIL_SetIrqHandler ( int , tHandler );
#define UTIL_GetIrqHandler(a)          (u32)    (((tCircleFunc1)(Circle_API [UTIL_GET_IRQ_HANDLER_ID])) ((int)a))                            // tHandler* UTIL_GetIrqHandler ( int );
#define UTIL_SetSchHandler(a,b)                 (((tCircleFunc2)(Circle_API [UTIL_SET_SCH_HANDLER_ID])) ((int)a,(tHandler)b))                // void UTIL_SetSchHandler ( int , tHandler );
#define UTIL_GetSchHandler(a)          (u32)    (((tCircleFunc1)(Circle_API [UTIL_GET_SCH_HANDLER_ID])) ((int)a))                            // tHandler* UTIL_GetSchHandler ( int );
#define UTIL_GetTemp()                 (u32)    (((tCircleFunc0)(Circle_API [UTIL_GET_TEMP_ID])) ())                                         // u16 UTIL_GetTemp( void );
#define UTIL_SetTempMode(a)                     (((tCircleFunc1)(Circle_API [UTIL_SET_TEMPMODE_ID])) ((int)a))                               // void UTIL_SetTempMode( int mode );

/// @endcond

//---------------------------------   MEMS  ------------------------------------

/* Exported types ------------------------------------------------------------*/

/**
* @enum  Rotate_H12_V_Match_TypeDef
* @brief The 4 possible rotations.
*
* The 4 possible MEM rotations.
**/
typedef enum
   {
   V12 = 0,                                        /*!< No rotation.          */
   V3  = 1,                                        /*!< Rotation to the right.*/
   V6  = 2,                                        /*!< Rotation to the left. */
   V9  = 3                                         /*!< Half a rotation.      */
   } Rotate_H12_V_Match_TypeDef;

/**
* @struct   tMEMS_Info
* @brief    MEMS state description.
**/
typedef struct
   {
   s16 OutX;                     /*!< MEMS X position.                        */
   s16 OutX_F4;                  /*!< MEMS X position filtered on 4 values.   */
   s16 OutX_F16;                 /*!< MEMS X position filtered on 16 values.  */
   s32 OutX_F64;                 /*!< MEMS X position filtered on 64 values.  */
   s32 OutX_F256;                /*!< MEMS X position filtered on 256 values. */
   s16 OutY;                     /*!< MEMS Y position.                        */
   s16 OutY_F4;                  /*!< MEMS Y position filtered on 4 values.   */
   s16 OutY_F16;                 /*!< MEMS Y position filtered on 16 values.  */
   s32 OutY_F64;                 /*!< MEMS Y position filtered on 64 values.  */
   s32 OutY_F256;                /*!< MEMS Y position filtered on 256 values. */
   s16 OutZ;                     /*!< MEMS Z position.                        */
   s16 OutZ_F4;                  /*!< MEMS Z position filtered on 4 values.   */
   s16 OutZ_F16;                 /*!< MEMS Z position filtered on 16 values.  */
   s32 OutZ_F64;                 /*!< MEMS Z position filtered on 64 values.  */
   s32 OutZ_F256;                /*!< MEMS Z position filtered on 256 values. */
   s16 Shocked;                  /*!< MEMS shock counter (incremented...)     */
   s16 RELATIVE_X;               /*!< MEMS relative X position.               */
   s16 RELATIVE_Y;               /*!< MEMS relative Y position.               */
   s16 DoubleClick;              /*!< MEMS DoubleClick counter(incremented...)*/
   } tMEMS_Info;

/// @cond Internal

/* Exported defines ----------------------------------------------------------*/

// MEMS functions definition
#define MEMS_GET_POSITION_ID   (MEMS_ID + 0)       // Return the current (relative) Mems information
#define MEMS_GET_ROTATION_ID   (MEMS_ID + 1)       // Return the current screen orientation of the circle
#define MEMS_SET_NEUTRAL_ID    (MEMS_ID + 2)       // Set the current position as "neutral position"
#define MEMS_GET_INFO_ID       (MEMS_ID + 3)       // Return Mems informations

// Prototypes
#define MEMS_GetPosition(a,b)             ((tCircleFunc2)(Circle_API [MEMS_GET_POSITION_ID])) ((u32)(a),(u32)(b))      //  void MEMS_GetPosition(s16 * pX, s16* pY);
#define MEMS_GetRotation(a)               ((tCircleFunc1)(Circle_API [MEMS_GET_ROTATION_ID])) ((u32)(a))      //  void MEMS_GetRotation(Rotate_H12_V_Match_TypeDef * H12);
#define MEMS_SetNeutral()                 ((tCircleFunc0)(Circle_API [MEMS_GET_ROTATION_ID])) ()                       //  void MEMS_SetNeutral( void );
#define MEMS_GetInfo()    ( (tMEMS_Info*) (((tCircleFunc0)(Circle_API [MEMS_GET_INFO_ID])) ()))                        //  tMEMS_Info* MEMS_GetInfo (void)

/// @endcond

//--------------------------------   POINTER  ----------------------------------

/* Exported types ------------------------------------------------------------*/

/**
* @enum  POINTER_mode
* @brief Available pointer modes.
*
* Description of all the available pointer modes in CircleOS.
**/
enum POINTER_mode
   {
   POINTER_UNDEF        = -1,    /*!< Pointer's mode is unknown!              */
   POINTER_OFF          =  0,    /*!< Pointer isn't managed and displayed.    */
   POINTER_ON           =  1,    /*!< Pointer mode used in main screen.       */
   POINTER_MENU         =  2,    /*!< Pointer management is used to select item menu (but pointer isn't displayed).  */
   POINTER_APPLICATION  =  3,    /*!< The managment of pointer depend of extern application.                         */
   POINTER_RESTORE_LESS =  4     /*!< The background isn't restored (to go faster).                                  */
   };

/**
* @enum  POINTER_state
* @brief The different pointer modes.
*
* Despite beeing in a undefined state, the pointer can be disabled or enable.
**/
enum POINTER_state
   {
   POINTER_S_UNDEF      = -1,                /*!< Pointer state is unknown!   */
   POINTER_S_DISABLED   =  0,                /*!< Pointer is disabled.        */
   POINTER_S_ENABLED    =  1                 /*!< Pointer is enabled.         */
   };

/**
* @struct   tPointer_Info
* @brief    Pointer position description.
**/
typedef struct
   {
   s16 xPos;                              /*!< X position of pointer.         */
   s16 yPos;                              /*!< Y position of pointer.         */
   s16 shift_PosX;                        /*!< Pointer speed on X axis.       */
   s16 shift_PosY;                        /*!< Pointer speed on Y axis        */
   s16 X_PosMin;                          /*!< Minimum position on X axis.    */
   s16 Y_PosMin;                          /*!< Minimum position on Y axis.    */
   s16 X_PosMax;                          /*!< Maximum position on X axis.    */
   s16 Y_PosMax;                          /*!< Maximum position on Y axis.    */
   } tPointer_Info;

/// @cond Internal

/* Exported defines ---------------------------------------------------------*/
#define POINTER_WIDTH 7

// POINTER functions definition
#define POINTER_SET_RECT_ID                   (POINTER_ID + 0)          // Set new limits for the move of the pointer
#define POINTER_SETRECTSCREEN_ID              (POINTER_ID + 1)          // Remove any space restriction for the pointer moves.
#define POINTER_GETCURRENTANGLESTART_ID       (POINTER_ID + 2)          // Return the current minimum angle to move pointer
#define POINTER_SETCURRENTANGLESTART_ID       (POINTER_ID + 3)          // Set the current minimum angle to move pointer
#define POINTER_GETCURRENTSPEEDONANGLE_ID     (POINTER_ID + 4)          // Return the ratio speed / angle
#define POINTER_SETCURRENTSPEEDONANGLE_ID     (POINTER_ID + 5)          // Set the ratio speed / angle
#define POINTER_SETMODE_ID                    (POINTER_ID + 6)          // Change the current mode of the pointer management
#define POINTER_GETMODE_ID                    (POINTER_ID + 7)          // Return the current mode of the pointer management
#define POINTER_SETCURRENTPOINTER_ID          (POINTER_ID + 8)          // Set the dimention and bitmap of pointer
#define POINTER_GETSTATE_ID                   (POINTER_ID + 9)          // Return the current state
#define POINTER_DRAW_ID                       (POINTER_ID + 10)         // Draw a pointer
#define POINTER_SAVE_ID                       (POINTER_ID + 11)         // Save the background of the pointer
#define POINTER_RESTORE_ID                    (POINTER_ID + 12)         // Restore the background of the pointer
#define POINTER_GETPOSITION_ID                (POINTER_ID + 13)         // Return the poistion of the cursor (x=lower byte, y = upperbyte)
#define POINTER_SETPOSITION_ID                (POINTER_ID + 14)         // Force the position of the pointer in the screen
#define POINTER_SETAPPLICATION_POINTER_MGR_ID (POINTER_ID + 15)         // Set the application pointer manager
#define POINTER_SETCOLOR_ID                   (POINTER_ID + 16)         // Set pointer color
#define POINTER_GETCOLOR_ID                   (POINTER_ID + 17)         // Return pointer color
#define POINTER_GETINFO_ID                    (POINTER_ID + 18)         // Return pointer informations
#define POINTER_SET_CURRENT_AREASTORE_ID      (POINTER_ID + 19)         // Change the current storage area

// Prototypes
#define POINTER_SetRect(a,b,c,d)                     ((tCircleFunc4)(Circle_API [POINTER_SET_RECT_ID])) ((u32)(a),(u32)(b),(u32)(c),(u32)(d))          //void POINTER_SetRect ( s16 x, s16 y, s16 width, s16 height );  //Restrict the move of the pointer to a rectangle
#define POINTER_SetRectScreen()                      ((tCircleFunc0)(Circle_API [POINTER_SETRECTSCREEN_ID])) ()                                        //void POINTER_SetRectScreen ( void );
#define POINTER_GetCurrentAngleStart()    (u16)      (((tCircleFunc0)(Circle_API [POINTER_GETCURRENTANGLESTART_ID])) ())                               //u16  POINTER_GetCurrentAngleStart ( void );
#define POINTER_SetCurrentAngleStart(a)              ((tCircleFunc1)(Circle_API [POINTER_SETCURRENTANGLESTART_ID])) ((u32)(a))                         //void POINTER_SetCurrentAngleStart ( u16 );
#define POINTER_GetCurrentSpeedOnAngle()  (u16)      (((tCircleFunc0)(Circle_API [POINTER_GETCURRENTSPEEDONANGLE_ID])) ())                             //u16  POINTER_GetCurrentSpeedOnAngle ( void );
#define POINTER_SetCurrentSpeedOnAngle(a)            ((tCircleFunc1)(Circle_API [POINTER_SETCURRENTSPEEDONANGLE_ID])) ((u32)(a))                       //void POINTER_SetCurrentSpeedOnAngle ( u16  newspeed );
#define POINTER_SetMode(a)                           ((tCircleFunc1)(Circle_API [POINTER_SETMODE_ID])) ((u32)(a))                                      //void POINTER_SetMode( enum POINTER_mode mode);
#define POINTER_GetMode()       (enum POINTER_mode)  (((tCircleFunc0)(Circle_API [POINTER_GETMODE_ID])) ())                                            //enum POINTER_mode POINTER_GetMode( void );
#define POINTER_SetCurrentPointer(a,b,c)             ((tCircleFunc3)(Circle_API [POINTER_SETCURRENTPOINTER_ID])) ((u32)(a),(u32)(b),(u32)(c))          //void POINTER_SetCurrentPointer( unsigned char width, unsigned char height, unsigned char *bmp);
#define POINTER_GetState()      (enum POINTER_state) (((tCircleFunc0)(Circle_API [POINTER_GETSTATE_ID])) ())                                           //enum POINTER_state POINTER_GetState(void);
#define POINTER_Draw(a,b,c,d,e)                      ((tCircleFunc5)(Circle_API [POINTER_DRAW_ID])) ((u32)(a),(u32)(b),(u32)(c),(u32)(d),(u32)(e))     //void POINTER_Draw (u8 Line, u8 Column, u8 Width, u8 Height, u8 *Bmp);
#define POINTER_Save(a,b,c,d)                        ((tCircleFunc4)(Circle_API [POINTER_SAVE_ID])) ((u32)(a),(u32)(b),(u32)(c),(u32)(d))              //void POINTER_Save (u8 Line, u8 Column, u8 Width, u8 Height);
#define POINTER_Restore(a,b,c,d)                     ((tCircleFunc4)(Circle_API [POINTER_RESTORE_ID])) ((u32)(a),(u32)(b),(u32)(c),(u32)(d))           //void POINTER_Restore (u8 Line, u8 Column, u8 Width, u8 Height);
#define POINTER_GetPos()                  (u16)      (((tCircleFunc0)(Circle_API [POINTER_GETPOSITION_ID])) ())                                        //u16  POINTER_GetPos(void);
#define POINTER_SetPos(a,b)                          ((tCircleFunc2)(Circle_API [POINTER_SETPOSITION_ID])) ((u32)(a),(u32)(b))                         //void POINTER_SetPos ( u16 x, u16 y );
#define POINTER_SetApplication_Pointer_Mgr(a)        ((tCircleFunc1)(Circle_API [POINTER_SETAPPLICATION_POINTER_MGR_ID])) ((u32)(a))                   //void POINTER_SetApplication_Pointer_Mgr(  tAppPtrMgr mgr );
#define POINTER_SetColor(a)                          ((tCircleFunc1)(Circle_API [POINTER_SETCOLOR_ID])) ((u32)(a))                                     //void POINTER_SetColor ( u16 color )
#define POINTER_GetColor()                (u16)      (((tCircleFunc0)(Circle_API [POINTER_GETCOLOR_ID])) ())                                           //u16  POINTER_GetColor ( void )
#define POINTER_GetInfo()      (tPointer_Info*)      (((tCircleFunc0)(Circle_API [POINTER_GETINFO_ID])) ())                                            //tPointer_Info* POINTER_GetInfo ( void )
#define POINTER_SetCurrentAreaStore(a)               ((tCircleFunc1)(Circle_API [POINTER_SET_CURRENT_AREASTORE_ID])) ((u32)(a))                        //void POINTER_SetCurrentAreaStore ( u8 *ptr )

/// @endcond

//--------------------------------   BUTTON  -----------------------------------

/* Exported types ------------------------------------------------------------*/

/**
* @enum  BUTTON_mode
* @brief Available button modes.
*
* List of all the available button mode in the CircleOS.
**/
enum BUTTON_mode
   {
   BUTTON_DISABLED      = -1,       /*!< No action on the button is detected. */
   BUTTON_ONOFF         =  0,       /*!< Detect ON/OFF pression type.         */
   BUTTON_ONOFF_FORMAIN =  1,       /*!< Special mode for main screen.        */
   BUTTON_WITHCLICK     =  2        /*!< Currently unused.                    */
   };

/**
* @enum  BUTTON_state
* @brief CircleOS button states.
*
* Description of the button states provided by CircleOS.
**/
enum BUTTON_state
   {
   BUTTON_UNDEF            = -1,    /*!< Undefined state.                     */
   BUTTON_RELEASED         =  0,    /*!< Button is released.                  */
   BUTTON_PUSHED           =  1,    /*!< Button was just pushed.              */
   BUTTON_PUSHED_FORMAIN   =  2,    /*!< Same as BUTTON_PUSHED when button mode is BUTTON_ONOFF_FORMAIN. */
   BUTTON_CLICK            =  3,    /*!< Currently unused.                    */
   BUTTON_DBLCLICK         =  4     /*!< Currently unused.                    */
   };

/// @cond Internal

/* Exported defines ----------------------------------------------------------*/

// BUTTON functions definition
#define BUTTON_GETSTATE_ID                   (BUTTON_ID + 0)         // Return state of button
#define BUTTON_SETMODE_ID                    (BUTTON_ID + 1)         // Set button mode
#define BUTTON_GETMODE_ID                    (BUTTON_ID + 2)         // Return button mode
#define BUTTON_WAITFORRELEASE_ID             (BUTTON_ID + 3)         // Disable temporarily any new button event

// Prototypes
#define BUTTON_GetState()       (enum BUTTON_state)   (((tCircleFunc0)(Circle_API [BUTTON_GETSTATE_ID])) ())        // enum BUTTON_state BUTTON_GetState(void);
#define BUTTON_SetMode(a);                            ((tCircleFunc1)(Circle_API [BUTTON_SETMODE_ID])) ((u32)(a))   // void BUTTON_SetMode( enum BUTTON_mode mode);
#define BUTTON_GetMode();       (enum BUTTON_mode)    (((tCircleFunc0)(Circle_API [BUTTON_GETMODE_ID])) ())         // enum BUTTON_mode BUTTON_GetMode ( void ) ;
#define BUTTON_WaitForRelease()                       ((tCircleFunc0)(Circle_API [BUTTON_WAITFORRELEASE_ID])) ()    // void BUTTON_WaitForRelease(void);

/// @endcond

//----------------------------------   LCD   -----------------------------------

/* Exported defines ----------------------------------------------------------*/

// RGB is 16-bit coded as    G2G1G0B4 B3B2B1B0 R4R3R2R1 R0G5G4G3
#define RGB_MAKE(xR,xG,xB)    ( ( (xG&0x07)<<13 ) + ( (xG)>>5 )  +      \
                                ( ((xB)>>3) << 8 )          +      \
                                ( ((xR)>>3) << 3 ) )                    /*!< Macro to make a LCD compatible color format from RGB.  */

#define RGB_RED         0x00F8                  /*!<  Predefined color.       */
#define RGB_BLACK       0x0000                  /*!<  Predefined color.       */
#define RGB_WHITE       0xffff                  /*!<  Predefined color.       */
#define RGB_BLUE        0x1F00                  /*!<  Predefined color.       */
#define RGB_GREEN       0xE007                  /*!<  Predefined color.       */
#define RGB_YELLOW      (RGB_GREEN|RGB_RED)     /*!<  Predefined color.       */
#define RGB_MAGENTA     (RGB_BLUE|RGB_RED)      /*!<  Predefined color.       */
#define RGB_LIGHTBLUE   (RGB_BLUE|RGB_GREEN)    /*!<  Predefined color.       */
#define RGB_ORANGE      (RGB_RED | 0xE001)      /*!<  Predefined color ( Green/2 + red ).  */
#define RGB_PINK        (RGB_MAGENTA | 0xE001)  /*!<  Predefined color ( Green/2 + magenta ). */

// PWM rates.
#define BACKLIGHTMIN                0x1000   /*!< Minimal PWM rate.           */
#define DEFAULT_CCR_BACKLIGHTSTART  0x8000   /*!< Default PWM rate.           */

// SCREEN Infos
#define SCREEN_WIDTH          128         /*!< Width of visible screen in pixels.   */
#define SCREEN_HEIGHT         128         /*!< Height of visible screen in pixels.  */
#define CHIP_SCREEN_WIDTH     132         /*!< Width of screen driven by LCD controller in pixels.  */
#define CHIP_SCREEN_HEIGHT    132         /*!< Height of screen driven by LCD controller in pixels.  */

// Characters Infos
#define CHAR_WIDTH            7           /*!< Width of a character.   */
#define CHAR_HEIGHT           14          /*!< Height of a character.   */

/// @cond Internal

// LCD functions definition
#define LCD_SETRECTFORCMD_ID                   (LCD_ID + 0)          // Define the rectangle (for the next command to be applied)
#define LCD_GETPIXEL_ID                        (LCD_ID + 1)          // Read the value of one pixel
#define LCD_DRAWPIXEL_ID                       (LCD_ID + 2)          // Draw a Graphic image on slave LCD.
#define LCD_SENDLCDCMD_ID                      (LCD_ID + 3)          // Send one byte command to LCD LCD.
#define LCD_SENDLCDDATA_ID                     (LCD_ID + 4)          // Display one byte data to LCD LCD.
#define LCD_READLCDDATA_ID                     (LCD_ID + 5)          // Read LCD byte data displayed on LCD LCD.
#define LCD_FILLRECT_ID                        (LCD_ID + 6)          // Fill a rectangle with one color
#define LCD_DRAWRECT_ID                        (LCD_ID + 7)          // Draw a rectangle with one color
#define LCD_DISPLAYCHAR_ID                     (LCD_ID + 8)          // Display one character
#define LCD_RECTREAD_ID                        (LCD_ID + 9)          // Save a rectangle of the monitor RAM
#define LCD_SETBACKLIGHT_ID                    (LCD_ID + 10)         // Modify the PWM rate
#define LCD_GETBACKLIGHT_ID                    (LCD_ID + 11)         // Return the PWM rate
#define LCD_SETROTATESCREEN_ID                 (LCD_ID + 12)         // Enable/Disable screen rotation
#define LCD_GETROTATESCREEN_ID                 (LCD_ID + 13)         // Return screen rotation mode
#define LCD_SETSCREENORIENTATION_ID            (LCD_ID + 14)         // Set screen orientation
#define LCD_GETSCREENORIENTATION_ID            (LCD_ID + 15)         // Return screen orientation
#define LCD_SETBACKLIGHT_OFF_ID                (LCD_ID + 16)         // Switch the LCD back light off.
#define LCD_SETBACKLIGHT_ON_ID                 (LCD_ID + 17)         // Switch the LCD back light on.

// Prototypes
#define LCD_SetRect_For_Cmd(a,b,c,d)                 ((tCircleFunc4)(Circle_API [LCD_SETRECTFORCMD_ID])) ((u32)(a),(u32)(b),(u32)(c),(u32)(d))                  //void  LCD_SetRect_For_Cmd ( s16 x, s16 y, s16 width, s16 height)
#define LCD_GetPixel(a,b)                 (u16)      (((tCircleFunc2)(Circle_API [LCD_GETPIXEL_ID])) ((u32)(a),(u32)(b)))                                       //u16   LCD_GetPixel (u8 x, u8 y)
#define LCD_DrawPixel(a,b,c)                         ((tCircleFunc3)(Circle_API [LCD_DRAWPIXEL_ID])) ((u32)(a),(u32)(b),(u32)(c))                               //void  LCD_SetPixel (u8 x, u8 y, u16 Pixel) ;
#define LCD_SendLCDCmd(a)                            ((tCircleFunc1)(Circle_API [LCD_SENDLCDCMD_ID])) ((u32)(a))                                                //void  LCD_SendLCDCmd(u8 Cmd);
#define LCD_SendLCDData(a)                           ((tCircleFunc1)(Circle_API [LCD_SENDLCDDATA_ID])) ((u32)(a))                                               //void  LCD_SendLCDData(u8 Data);
#define LCD_ReadLCDData()                 (u32)      (((tCircleFunc0)(Circle_API [LCD_READLCDDATA_ID])) ())                                                     //u32   LCD_ReadLCDData(void);
#define LCD_FillRect(a,b,c,d,e)                      ((tCircleFunc5)(Circle_API [LCD_FILLRECT_ID])) ((u32)(a),(u32)(b),(u32)(c),(u32)(d),(u32)(e))              //void  LCD_FillRect ( u16 x, u16 y, u16 width, u16 height, u16 color );
#define LCD_DrawRect(a,b,c,d,e)                      ((tCircleFunc5)(Circle_API [LCD_DRAWRECT_ID])) ((u32)(a),(u32)(b),(u32)(c),(u32)(d),(u32)(e))              //void  LCD_DrawRect ( u16 x, u16 y, u16 width, u16 height, u16 color );
#define LCD_DisplayChar(a,b,c,d,e,f)                 ((tCircleFunc6)(Circle_API [LCD_DISPLAYCHAR_ID])) ((u32)(a),(u32)(b),(u32)(c),(u32)(d),(u32)(e),(u32)(f))  //void  LCD_DisplayChar(u8 x, u8 y, u8 Ascii, u16 TextColor, u16 BGndColor, u16 CharMagniCoeff);
#define LCD_RectRead(a,b,c,d,e)                      ((tCircleFunc5)(Circle_API [LCD_RECTREAD_ID])) ((u32)(a),(u32)(b),(u32)(c),(u32)(d),(u32)(e))              //void  LCD_RectRead ( u16 x, u16 y, u16 width, u16 height, u8* bmp );
#define LCD_SetBackLight(a)                          ((tCircleFunc1)(Circle_API [LCD_SETBACKLIGHT_ID])) ((u32)(a))                                              //void  LCD_SetBackLight(u32 newBaclightStart);
#define LCD_GetBackLight()                (u32)      (((tCircleFunc0)(Circle_API [LCD_GETBACKLIGHT_ID])) ())                                                    //u32   LCD_GetBackLight(void);
#define LCD_SetRotateScreen(a)                       ((tCircleFunc1)(Circle_API [LCD_SETROTATESCREEN_ID])) ((u32)(a))                                           //void  LCD_SetRotateScreen ( u8 RotateScreen)
#define LCD_GetRotateScreen()             (u32)      (((tCircleFunc0)(Circle_API [LCD_GETROTATESCREEN_ID])) ())                                                 //u8    LCD_GetRotateScreen (void)
#define LCD_SetScreenOrientation(a)                  ((tCircleFunc1)(Circle_API [LCD_SETSCREENORIENTATION_ID])) ((u32)(a))                                      //void LCD_SetScreenOrientation (Rotate_H12_V_Match_TypeDef ScreenOrientation)
#define LCD_GetScreenOrientation()        (u32)      (((tCircleFunc0)(Circle_API [LCD_GETSCREENORIENTATION_ID])) ())                                            //Rotate_H12_V_Match_TypeDef LCD_GetScreenOrientation (void)
#define LCD_SetBackLightOff()                        ((tCircleFunc0)(Circle_API [LCD_SETBACKLIGHT_OFF_ID])) ()
#define LCD_SetBackLightOn()                         ((tCircleFunc0)(Circle_API [LCD_SETBACKLIGHT_ON_ID])) ()

/// @endcond

//----------------------------------   DRAW   ----------------------------------

/// @cond Internal

/* Exported defines ----------------------------------------------------------*/

// DRAW functions definition
#define DRAW_SETDEFAULTCOLOR_ID                   (DRAW_ID + 0)         // Reset colors (bgnd + text)
#define DRAW_CLEAR_ID                             (DRAW_ID + 1)         // Clear the LCD display
#define DRAW_SETIMAGE_ID                          (DRAW_ID + 2)         // Draw a colored image
#define DRAW_SETIMAGEBW_ID                        (DRAW_ID + 3)         // Draw a black and white image
#define DRAW_SETLOGOBW_ID                         (DRAW_ID + 4)         // Draw logo
#define DRAW_DISPLAYVBAT_ID                       (DRAW_ID + 5)         // Display the voltage of battery in ascii
#define DRAW_DISPLAYTIME_ID                       (DRAW_ID + 6)         // Display time in ascii
#define DRAW_DISPLAYSTRING_ID                     (DRAW_ID + 7)         // Display a 17char max string of characters
#define DRAW_DISPLAYSTRINGINVERTED_ID             (DRAW_ID + 8)         // Display a 17char max string of characters with inverted colors
#define DRAW_GETCHARMAGNICOEFF_ID                 (DRAW_ID + 9)         // Return the magnifying value for the characters
#define DRAW_SETCHARMAGNICOEFF_ID                 (DRAW_ID + 10)        // Set the magnifying value for the characters
#define DRAW_GETTEXTCOLOR_ID                      (DRAW_ID + 11)        // Return the current text color
#define DRAW_SETTEXTCOLOR_ID                      (DRAW_ID + 12)        // Set the current text color
#define DRAW_GETBGNDCOLOR_ID                      (DRAW_ID + 13)        // Return the current background color
#define DRAW_SETBGNDCOLOR_ID                      (DRAW_ID + 14)        // Set the current background color
#define DRAW_LINE_ID                              (DRAW_ID + 15)        // Draw a Line between (using Bresenham algorithm) 

//Prototypes
#define DRAW_SetDefaultColor()                      ((tCircleFunc0)(Circle_API [DRAW_SETDEFAULTCOLOR_ID])) ()                                                 //void  DRAW_SetDefaultColor (void);
#define DRAW_Clear()                                ((tCircleFunc0)(Circle_API [DRAW_CLEAR_ID])) ()                                                           //void  DRAW_Clear(void);
#define DRAW_SetImage(a,b,c,d,e)                    ((tCircleFunc5)(Circle_API [DRAW_SETIMAGE_ID])) ((u32)(a),(u32)(b),(u32)(c),(u32)(d),(u32)(e))            //void  DRAW_SetImage(const u16 *imageptr, u8 x, u8 y, u8 width, u8 height);
#define DRAW_SetImageBW(a,b,c,d,e)                  ((tCircleFunc5)(Circle_API [DRAW_SETIMAGEBW_ID])) ((u32)(a),(u32)(b),(u32)(c),(u32)(d),(u32)(e))          //void  DRAW_SetImageBW(const u8 *imageptr, u8 x, u8 y, u8 width, u8 height);
#define DRAW_SetLogoBW()                            ((tCircleFunc0)(Circle_API [DRAW_SETLOGOBW_ID])) ()                                                       //void  DRAW_SetLogoBW(void);
#define DRAW_DisplayVbat(a,b)                       ((tCircleFunc2)(Circle_API [DRAW_DISPLAYVBAT_ID])) ((u32)(a),(u32)(b))                                    //void  DRAW_DisplayVbat(u8 x, u8 y);
#define DRAW_DisplayTime(a,b)                       ((tCircleFunc2)(Circle_API [DRAW_DISPLAYTIME_ID])) ((u32)(a),(u32)(b))                                    //void  DRAW_DisplayTime(u8 x, u8 y);
#define DRAW_DisplayString(a,b,c,d)                 ((tCircleFunc4)(Circle_API [DRAW_DISPLAYSTRING_ID])) ((u32)(a),(u32)(b),(u32)(c),(u32)(d))                //void  DRAW_DisplayString( u8 x, u8 y, u8 *ptr, u8 len );
#define DRAW_DisplayStringInverted(a,b,c,d)         ((tCircleFunc4)(Circle_API [DRAW_DISPLAYSTRINGINVERTED_ID])) ((u32)(a),(u32)(b),(u32)(c),(u32)(d))        //void  DRAW_DisplayStringInverted( u8 x, u8 y, u8 *ptr, u8 len );
#define DRAW_GetCharMagniCoeff()              (u16) (((tCircleFunc0)(Circle_API [DRAW_GETCHARMAGNICOEFF_ID])) ())                                             //u16   DRAW_GetCharMagniCoeff(void);
#define DRAW_SetCharMagniCoeff(a)                   ((tCircleFunc1)(Circle_API [DRAW_SETCHARMAGNICOEFF_ID])) ((u32)(a))                                       //void  DRAW_SetCharMagniCoeff(u16 Coeff);
#define DRAW_GetTextColor()                   (u16) (((tCircleFunc0)(Circle_API [DRAW_GETTEXTCOLOR_ID])) ())                                                  //u16   DRAW_GetTextColor(void);
#define DRAW_SetTextColor(a)                        ((tCircleFunc1)(Circle_API [DRAW_SETTEXTCOLOR_ID])) ((u32)(a))                                            //void  DRAW_SetTextColor(u16 Color);
#define DRAW_GetBGndColor()                   (u16) (((tCircleFunc0)(Circle_API [DRAW_GETBGNDCOLOR_ID])) ())                                                  //u16   DRAW_GetBGndColor(void);
#define DRAW_SetBGndColor(a)                        ((tCircleFunc1)(Circle_API [DRAW_SETBGNDCOLOR_ID])) ((u32)(a))                                            //void  DRAW_SetBGndColor(u16 Color);
#define DRAW_Line(a,b,c,d,e)                        ((tCircleFunc5)(Circle_API [DRAW_LINE_ID])) ((u32)(a),(u32)(b),(u32)(c),(u32)(d),(u32)(e))                //void  DRAW_Line(s16 x1, s16 y1, s16 x2, s16 y2, u16 color );
/// @endcond

//--------------------------------   BUZZER  -----------------------------------

/* Exported type def ---------------------------------------------------------*/

/**
* @enum  BUZZER_mode
* @brief CircleOS buzzer modes.
*
* Without the undefined mode, the CircleOS provides 5 modes for its buzzer.
**/
enum BUZZER_mode
   {
   BUZZER_UNDEF      = -1,         /*!<  undefined mode for buzzer            */
   BUZZER_OFF        =  0,         /*!<  The buzzer is put off.               */
   BUZZER_ON         =  1,         /*!<  The buzzer is put on.                */
   BUZZER_SHORTBEEP  =  2,         /*!<  Make buzzer to bip for a short time  */
   BUZZER_LONGBEEP   =  3,         /*!<  Make buzzer to bip for a long time   */
   BUZZER_PLAYMUSIC  =  4          /*!<  Make buzzer to play a music          */
   };

/// @cond Internal

/* Exported defines ----------------------------------------------------------*/
#define BUZZER_BEEP  BUZZER_SHORTBEEP

// BUZZER functions definition
#define BUZZER_SETMODE_ID                       (BUZZER_ID + 0)   // Set new buzzer mode
#define BUZZER_GETMODE_ID                       (BUZZER_ID + 1)   // Get the current buzzer mode.
#define BUZZER_PLAY_MUSIC_ID                    (BUZZER_ID + 2)   // Plays the provided melody that follows the RTTTL Format.

// Prototypes
#define BUZZER_SetMode(a)                            ((tCircleFunc1)(Circle_API [BUZZER_SETMODE_ID])) ((u32)(a))               //void  BUZZER_SetMode( enum BUZZER_mode mode);
#define BUZZER_GetMode()      (enum  BUZZER_mode)    (((tCircleFunc0)(Circle_API [BUZZER_GETMODE_ID])) ())                     //enum  BUZZER_mode BUZZER_GetMode( void );
#define BUZZER_PlayMusic(a)                          ((tCircleFunc1)(Circle_API [BUZZER_PLAY_MUSIC_ID])) ((u32)(a))            //void BUZZER_PlayMusic (const u8 *melody );

/// @endcond

//---------------------------------   MENU   -----------------------------------

/* Exported defines ----------------------------------------------------------*/
#define REMOVE_MENU     0x01  /*!< Menu flag: remove menu when item selected. */
#define APP_MENU        0x02  /*!< Menu flag: item is an application.         */
#define MENU_MAXITEM    8     /*!< Maximum number of item in a menu.          */

/* Exported type def ---------------------------------------------------------*/

/**
* @struct   tMenuItem
* @brief    Menu item description.
**/
typedef struct
   {
   const char* Text;                            /*!<  Name of Item displayed in menu   */
   enum MENU_code (*Fct_Init)  ( void );        /*!<  First function launched if item is selected. */
   enum MENU_code (*Fct_Manage)( void );        /*!<  Second function launched after a "return MENU_CONTINU_COMMAND" in the first function   */
   int fRemoveMenu;                             /*!<  Flag to know if remove menu at end  */
   } tMenuItem;

/**
* @struct   tMenu
* @brief    Menu description.
**/
typedef struct
   {
   unsigned fdispTitle: 1;                /*!< Display title is set.          */
   const char* Title;                     /*!< Menu title.                    */
   int NbItems;                           /*!< Number of items in the menu ( must be <= MENU_MAXITEM )  */
   int LgMax;                             /*!< Unused.                        */
   int XPos;                              /*!< X position of menu bottom-left corner. */
   int YPos;                              /*!< Y position of menu bottom-left corner. */
   int XSize;                             /*!< Unused.                        */
   int YSize;                             /*!< Unused.                        */
   unsigned int SelectedItem;             /*!< ID of selected item (0 for first item, 1 for second item, ...) */
   tMenuItem Items[MENU_MAXITEM];         /*!< Items of menu.  */
   } tMenu;

/**
* @enum  MENU_code
* @brief Application return values.
*
* List of all the codes available for CircleOS application return values.
**/
enum MENU_code
   {
   MENU_LEAVE              = 0,                    /*!< Leave application.    */
   MENU_CONTINUE           = 1,                    /*!< Continue application. */
   MENU_REFRESH            = 2,                    /*!< Refresh current menu. */
   MENU_CHANGE             = 3,                    /*!< Change current menu.  */
   MENU_CONTINUE_COMMAND   = 4                     /*!< Sent by Ini functions.*/
   };

/// @cond Internal

/* Exported defines ----------------------------------------------------------*/

// MENU functions definition
#define MENU_SET_ID                             (MENU_ID + 0)        // Display a menu
#define MENU_REMOVE_ID                          (MENU_ID + 1)        // Remove the current menu, DRAW_Clear and set pointer mode to "POINTER_ON".
#define MENU_QUESTION_ID                        (MENU_ID + 2)        // Dedicated menu for ask question and yes/no responses
#define MENU_PRINT_ID                           (MENU_ID + 3)        // Display a popup menu with a string.
#define MENU_CLEAR_CURRENT_COMMAND_ID           (MENU_ID + 4)        // Set CurrentCommand to 0
#define MENU_SET_LEVELTITLE_ID                  (MENU_ID + 5)        // Set the title of level menu managed by MENU_SetLevel_Mgr.
#define MENU_SET_TEXTCOLOR_ID                   (MENU_ID + 6)        // Set the color used for text menu.
#define MENU_GET_TEXTCOLOR_ID                   (MENU_ID + 7)        // Return the color used for text menu.
#define MENU_SET_BGNDCOLOR_ID                   (MENU_ID + 8)        // Set the background color used for menu.
#define MENU_GET_BGNDCOLOR_ID                   (MENU_ID + 9)        // Return the background color used for menu.
#define MENU_QUIT_ID                            (MENU_ID + 10)       // Leave the current menu (stand for "cancel" and do a DRAW_Clear)
#define MENU_SET_LEVELINI_ID                    (MENU_ID + 11)       // Initialise a generic function to set a avalue in the range of [0,4]
#define MENU_CLEAR_CURRENT_MENU_ID              (MENU_ID + 12)       // Set CurrentMenu to 0
#define MENU_SET_LEVEL_MGR_ID                   (MENU_ID + 13)       // Generic function to set a avalue in the range of [0,4] (handling of the control)

// Prototypes
#define MENU_Set(a)                                  ((tCircleFunc1)(Circle_API [MENU_SET_ID])) ((u32)(a))                    //void  MENU_Set ( tMenu *mptr );
#define MENU_Remove()                                ((tCircleFunc0)(Circle_API [MENU_REMOVE_ID])) ()                         //void  MENU_Remove ( void ) ;
#define MENU_Question(a,b)                           ((tCircleFunc2)(Circle_API [MENU_QUESTION_ID])) ((u32)(a),(u32)(b))      //void  MENU_Question ( char *str, int *answer );
#define MENU_Print(a)                                ((tCircleFunc1)(Circle_API [MENU_PRINT_ID])) ((u32)(a))                  //void  MENU_Print ( char *str );
#define MENU_ClearCurrentCommand()                   ((tCircleFunc0)(Circle_API [MENU_CLEAR_CURRENT_COMMAND_ID])) ()          //void MENU_ClearCurrentCommand(void)
#define MENU_SetLevelTitle(a)                        ((tCircleFunc1)(Circle_API [MENU_SET_LEVELTITLE_ID])) ((u32)(a))         //void MENU_SetLevelTitle(u8* title)
#define MENU_SetTextColor(a)                         ((tCircleFunc1)(Circle_API [MENU_SET_TEXTCOLOR_ID])) ((u32)(a))          //void MENU_SetTextColor ( int TextColor )
#define MENU_GetTextColor()                 (u32)    (((tCircleFunc0)(Circle_API [MENU_GET_TEXTCOLOR_ID])) ())                //int MENU_GetTextColor ( void )
#define MENU_SetBGndColor(a)                         ((tCircleFunc1)(Circle_API [MENU_SET_BGNDCOLOR_ID])) ((u32)(a))          //void MENU_SetBGndColor ( int BGndColor )
#define MENU_GetBGndColor()                 (u32)    (((tCircleFunc0)(Circle_API [MENU_GET_BGNDCOLOR_ID])) ())                //int MENU_GetBGndColor ( void )
#define MENU_Quit()              (enum MENU_code)    (((tCircleFunc0)(Circle_API [MENU_QUIT_ID])) ())                         //enum MENU_code MENU_Quit ( void )
#define MENU_SetLevel_Ini()      (enum MENU_code)    (((tCircleFunc0)(Circle_API [MENU_SET_LEVELINI_ID])) ())                 //enum MENU_code MENU_SetLevel_Ini ( void )
#define MENU_ClearCurrentMenu()                       ((tCircleFunc0)(Circle_API [MENU_CLEAR_CURRENT_MENU_ID])) ()            //void MENU_ClearCurrentMenu(void)
#define MENU_SetLevel_Mgr(a,b)   (enum MENU_code)    ((tCircleFunc2)(Circle_API [MENU_SET_LEVEL_MGR_ID])) ((u32)(a),(u32)(b)) //enum MENU_code MENU_SetLevel_Mgr ( u32 *value, u32 value_range [] )

/// @endcond

//----------------------------------   LED -------------------------------------

/* Exported types ------------------------------------------------------------*/

/**
* @enum  LED_mode
* @brief LED modes.
*
* LEDs may be on, off or blinking slowly or fastly!
**/
enum LED_mode
   {
   LED_UNDEF       = -1,                     /*!< Undefined led mode.         */
   LED_OFF         = 0,                      /*!< Put off the led.            */
   LED_ON          = 1,                      /*!< Put on the led.             */
   LED_BLINKING_LF = 2,                      /*!< Slow blinking led mode.     */
   LED_BLINKING_HF = 3                       /*!< Fast blinking led mode.     */
   };

/**
* @enum LED_id
* @brief Available LEDs.
*
* List of all the available LEDs.
**/
enum LED_id
   {
   LED_GREEN = 0,                                        /*!< Green led id.   */
   LED_RED = 1                                           /*!< Red led id.     */
   };

/// @cond Internal

/* Exported defines ----------------------------------------------------------*/

// LED functions definition
#define LED_SET_ID            (LED_ID + 0)      // Set a specified LED in a specified mode.

// Prototypes
#define LED_Set(a,b)          ((tCircleFunc2)(Circle_API [LED_SET_ID])) ((u32)(a),(u32)(b))  //void LED_Set ( enum LED_id id, enum LED_mode mode )               //void LED_Set ( enum LED_id id, enum LED_mode mode );

/// @endcond

//--------------------------------   RTC  --------------------------------------

/* Exported defines ----------------------------------------------------------*/

// Backup registers
#define BKP_SYS1  1        /*!<  Backup register reserved for OS  */
#define BKP_SYS2  2        /*!<  Backup register reserved for OS  */
#define BKP_SYS3  3        /*!<  Backup register reserved for OS  */
#define BKP_SYS4  4        /*!<  Backup register reserved for OS  */
#define BKP_SYS5  5        /*!<  Backup register reserved for OS  */
#define BKP_SYS6  6        /*!<  Backup register reserved for OS  */

#define BKP_USER1    7     /*!<  Backup available for users application */
#define BKP_USER2    8     /*!<  Backup available for users application */
#define BKP_USER3    9     /*!<  Backup available for users application */
#define BKP_USER4    10    /*!<  Backup available for users application */

/// @cond Internal

//RTC functions definition
#define RTC_SET_TIME_ID       (RTC_ID + 0)      // Set current time.
#define RTC_GET_TIME_ID       (RTC_ID + 1)      // Return current time.
#define RTC_DISPLAY_TIME_ID   (RTC_ID + 2)      // Display current time on the 6th line at column 0.

// Prototypes
#define RTC_SetTime(a,b,c)    ((tCircleFunc3)(Circle_API [RTC_SET_TIME_ID])) ((u32)(a),(u32)(b),(u32)(c))     //void  RTC_SetTime (u32 THH, u32 TMM, u32 TSS);
#define RTC_GetTime(a,b,c)    ((tCircleFunc3)(Circle_API [RTC_GET_TIME_ID])) ((u32)(a),(u32)(b),(u32)(c))     //void  RTC_GetTime (u32 * THH, u32 * TMM, u32 * TSS);
#define RTC_DisplayTime()     ((tCircleFunc0)(Circle_API [RTC_DISPLAY_TIME_ID])) ()                           //void  RTC_DisplayTime ( void );

/// @endcond

//--------------------------------- Application -------------------------------
typedef void  (*tAppPtrMgr) ( int , int );

#endif /*__CIRCLE_API_H */
