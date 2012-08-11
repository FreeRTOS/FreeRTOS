/********************* (C) COPYRIGHT 2007 RAISONANCE S.A.S. *******************/
/**
*
* @file     draw.c
* @brief    Various utilities for drawings (characters, ..)
* @author   FL
* @author   IB
* @date     07/2007
*
**/
/******************************************************************************/

/* Includes ------------------------------------------------------------------*/
#include "circle.h"

/// @cond Internal

/* Private define ------------------------------------------------------------*/
#define V9_MADCTRVAL    0x90
#define V12_MADCTRVAL   0x30
#define V3_MADCTRVAL    0x50
#define V6_MADCTRVAL    0xF0

#define ROTATE_DIVISER  500

/* Private variables ---------------------------------------------------------*/

static u16 CharMagniCoeff = 1;   /*!< Current character magnify coefficient.  */
static u16 BGndColor;            /*!< Current background color.               */
static u16 TextColor;            /*!< Current text color.                     */

int fDisplayTime = 0;
u16 BatState;
u16 OldBatState;
u32 OldTHH;
u32 OldTMM;
u32 OldTSS;
u32 OldTemp;   //FL071107
u16 xBat;
u16 yBat;
u16 widthBat;
u16 heightBat;
u8 UsbState,OldUsbState;
static int divider_coord = 0;

// Screen orientation management
int                        rotate_counter             = 0;
Rotate_H12_V_Match_TypeDef previous_H12               = V9;
Rotate_H12_V_Match_TypeDef previous_previous_H12      = V9;
Rotate_H12_V_Match_TypeDef H12;
Rotate_H12_V_Match_TypeDef CurrentScreenOrientation;
int                        CurrentRotateScreen        = 1;

extern s16 XInit;
extern s16 YInit;

/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
*
*                                vbattoa
*
*******************************************************************************/
/**
*
*  This function convert an u16 in ascii radix 10
*
*  @param[out] ptr   A pointer to a string where the converted value will be put.
*  @param[in]  X     The value to convert.
*
*  @see  DRAW_DisplayVbat
*
**/
/******************************************************************************/
static void vbattoa( char* ptr, u16 X )
   {
   u8 c;
   u16 r = 0;

   // 1 000 digit
   c = ((X-r)/1000);
   r = r + (c*1000);
   *ptr++ = c + 0x30;

   // dot
   *ptr++ = '.';

   // 100 digit
   c = ((X-r)/100);
   r = r + (c*100);
   *ptr++ = c + 0x30;

   // 10 digit
   c = ((X-r)/10);
   r = r + (c*10);
   *ptr++ = c + 0x30;

   // Volt
   *ptr++ = 'V';
   *ptr++ = 0;
   }

/*******************************************************************************
*
*                                DRAW_DisplayStringWithMode
*
*******************************************************************************/
/**
*
*  This function is used to display a 17char max string of
*  characters on the LCD display on the selected line.
*  Note:
*  this function is the user interface to use the LCD driver.
*
*  @param[in]  x     The horizontal screen coordinate where to draw the string.
*  @param[in]  y     The vertical screen coordinate where to draw the string.
*  @param[in]  ptr   Pointer to string to display.
*  @param[in]  len   String size.
*  @param[in]  mode  Display mode: 0 normal, 1 inverted colors.
*
*  @warning       The (0x0) point in on the low left corner.
*
*  @see           DRAW_DisplayString
*  @see           DRAW_DisplayStringInverted
*
**/
/******************************************************************************/
static void DRAW_DisplayStringWithMode( u8 x, u8 y, const u8* ptr, u8 len, int mode )
   {
   u8 ref_x = x, i = 0;

   /* Send the string character by character on LCD */
   while ((*ptr!=0)&&(i<18))
      {
      /* Display one character on LCD */
      LCD_DisplayChar( ref_x, y, *ptr, mode ? BGndColor : TextColor,  mode ? TextColor : BGndColor, CharMagniCoeff );

      /* Increment the column position by 7 */
      ref_x+= (7*CharMagniCoeff);

      /* Point on the next character */
      ptr++;

      /* Increment the character counter */
      i++;
      /* If we reach the maximum Line character */
      }

   while ( i < len )
      {
      /* Display one character on LCD */
      LCD_DisplayChar( ref_x, y, ' ', mode ? BGndColor : TextColor, mode ? TextColor : BGndColor, CharMagniCoeff );

      /* Increment the column position by 7 */
      ref_x += ( 7 * CharMagniCoeff );

      /* Increment the character counter */
      i++;
      }
   }

/* Public functions for CircleOS ---------------------------------------------*/

/*******************************************************************************
*
*                                DRAW_Init
*
*******************************************************************************/
/**
*
*  Initialize GUI drawing. Called at CircleOS startup.
*
*  @attention  This function must <b>NOT</b> be called by the user.
*
**/
/******************************************************************************/
void DRAW_Init( void )
   {
   LCD_Init();
#ifdef _MEMS
   MEMS_GetRotation( &CurrentScreenOrientation );
#endif
   LCD_SetScreenOrientation( CurrentScreenOrientation );

   xBat        = 98;
   yBat        = 3;
   OldBatState = 10;
   OldTSS      = 100;
   OldTMM      = 100;
   OldTHH      = 100;
   OldTemp     = -1;

   // Clear LCD and draw black and white logo
   DRAW_SetDefaultColor();
	LCD_FillRect( 0, 0, CHIP_SCREEN_WIDTH, CHIP_SCREEN_HEIGHT, BGndColor );
//   POINTER_Init();
   }




/* Public functions ----------------------------------------------------------*/

/*******************************************************************************
*
*                                DRAW_SetCharMagniCoeff
*
*******************************************************************************/
/**
*
*  Set the magnifying value for the characters (should be 1 or 2)
*
*  @param[in]  Coeff The new magnifying coefficent.
*
**/
/******************************************************************************/
void DRAW_SetCharMagniCoeff( u16 Coeff )
   {
   CharMagniCoeff = Coeff;
   }

 /******************************************************************************
*
*                                DRAW_GetCharMagniCoeff
*
*******************************************************************************/
/**
*
*  Return the current magnifying value for the characters
*
*  @return  Current magnifying value.
*
**/
/******************************************************************************/
u16 DRAW_GetCharMagniCoeff( void )
   {
   return CharMagniCoeff;
   }

 /******************************************************************************
*
*                                DRAW_GetTextColor
*
*******************************************************************************/
/**
*
*  Return current text color.
*
*  @return  The current RGB color used to draw text.
*
**/
/******************************************************************************/
u16 DRAW_GetTextColor( void )
   {
   return TextColor;
   }

/*******************************************************************************
*
*                                DRAW_SetTextColor
*
*******************************************************************************/
/**
*
*  Set current text color.
*
*  @param[in]  Color The new RGB color used when drawing text.
*
**/
/******************************************************************************/
void DRAW_SetTextColor( u16 Color )
   {
   TextColor = Color ;
   }

/*******************************************************************************
*
*                                DRAW_GetBGndColor
*
*******************************************************************************/
/**
*
*  Return current background color.
*
*  @return  The current RGB color used for the background.
*
**/
/******************************************************************************/
u16 DRAW_GetBGndColor( void )
   {
   return BGndColor;
   }

/*******************************************************************************
*
*                                DRAW_SetBGndColor
*
*******************************************************************************/
/**
*
*  Set current background color
*
*  @param[in]  Color The new RGB color for background.
*
**/
/******************************************************************************/
void DRAW_SetBGndColor(u16 Color)
   {
   BGndColor = Color;
   }


/*******************************************************************************
*
*                                DRAW_SetImage
*
*******************************************************************************/
/**
*
*  The provided bitmap is made width * height 2 byte words. Each 2 byte word contains
*  the RGB color of a pixel.
*
*  @brief      Draw a color bitmap at the provided coordinates.
*  @param[in]  imageptr    A pointer to an array of width * height 2 byte words.
*  @param[in]  x           The horizontal coordinate of the low left corner of the bitmap.
*  @param[in]  y           The vertical coordinate of the low left corner of the bitmap.
*  @param[in]  width       The bitmap width.
*  @param[in]  height      The bitmap height.
*
*  @warning       The (0x0) point in on the low left corner.
*
**/
/******************************************************************************/
void DRAW_SetImage( const u16* imageptr, u8 x, u8 y, u8 width, u8 height )
   {
   int i;

   // Select screen area to access.
   LCD_SetRect_For_Cmd( x, y, width, height );

   // Send command to write data on the LCD screen.
   LCD_SendLCDCmd(ST7637_RAMWR);

   for( i = 0; i < ( width * height ); i++ )
      {
      LCD_SendLCDData( imageptr[ i ] & 0xff );
      LCD_SendLCDData( ( imageptr[ i ] >> 8 ) & 0xff );
      }
   }



/*******************************************************************************
*
*                                DRAW_DisplayString
*
*******************************************************************************/
/**
*
*  This function is used to display a 17 character max string of
*  characters on the LCD display at the provided coordinates.
*
*  @param[in] x      The horizontal coordinate of the displayed string.
*  @param[in] y      The vertical coordinate of the display string.
*  @param[in] *ptr   Pointer to the string to display on LCD.
*  @param[in] len    String length.
*
*  @warning       The (0x0) point in on the low left corner.
*
**/
/******************************************************************************/
void DRAW_DisplayString( u8 x, u8 y, const u8* ptr, u8 len )
   {
   DRAW_DisplayStringWithMode( x, y, ptr, len, 0 );
   }

/*******************************************************************************
*
*                                DRAW_DisplayStringInverted
*
*******************************************************************************/
/**
*
*  This function is used to display a 17 character max string of
*  characters on the LCD display at the provided coordinates with inverted colors.
*
*  @param[in] x      The horizontal coordinate of the displayed string.
*  @param[in] y      The vertical coordinate of the display string.
*  @param[in] *ptr   Pointer to the string to display on LCD.
*  @param[in] len    String length.
*
*  @warning       The (0x0) point in on the low left corner.
*
**/
/******************************************************************************/
void DRAW_DisplayStringInverted( u8 x, u8 y, const u8* ptr, u8 len )
   {
   //BackGround and Text Colors are inverted
   DRAW_DisplayStringWithMode( x, y, ptr, len, 1 );
   }

/*******************************************************************************
*
*                                DRAW_SetDefaultColor
*
*******************************************************************************/
/**
*
*  Reset text and background colors to their default values.
*
**/
/******************************************************************************/
void DRAW_SetDefaultColor (void)
   {
   BGndColor = RGB_WHITE;
   TextColor = RGB_BLACK;
   }

/*******************************************************************************
*
*                                DRAW_DisplayTemp
*
*******************************************************************************/
/**
*
*  This function is used to display the current temperature in ascii.
*  The choice between Celcius and Fahrenheit is fixed by UTIL_SetModeTemp()
*
*  @param[in]  x  The horizontal coordinate of the displayed string.
*  @param[in]  y  The vertical coordinate of the display string.
*
*  @warning       The (0x0) point in on the low left corner.
*
**/
/******************************************************************************/
void DRAW_DisplayTemp( u8 x, u8 y )
   {
   u32 Temp = 0;
   u8  TextBuffer[5] = { 0,0,0,0,0};
   
   // Get Time
   Temp = UTIL_GetTemp() ;

   if( Temp != OldTemp ) 
      {
      // Display C (if modified).
      UTIL_uint2str( TextBuffer, Temp/10, 2, 1 );
      TextBuffer[ 2 ] = '.';
      DRAW_DisplayString( x + ( 0 * CharMagniCoeff * 7 ), y, TextBuffer, 3 );

      // Display C/10 (if modified).
      UTIL_uint2str( TextBuffer, Temp%10, 1, 1 );
      TextBuffer[ 1 ] = fTemperatureInFahrenheit ? 'F' : 'C'; TextBuffer[ 2 ] = 0;
      DRAW_DisplayString( x + ( 3 * CharMagniCoeff * 7 ), y, TextBuffer, 2 );
      }
   OldTemp = Temp;
   }

/*******************************************************************************
*
*                                DRAW_Line
*
*******************************************************************************/
/**
*  Draw a line on the LCD screen. Optimized for horizontal/vertical lines, 
*  and use the Bresenham algorithm for other cases.
*
*  @param[in]  x1          The x-coordinate of the first line endpoint.
*  @param[in]  x2          The x-coordinate of the second line endpoint.
*  @param[in]  y1          The y-coordinate of the first line endpoint.
*  @param[in]  y2          The y-coordinate of the second line endpoint.
*  @param[in]  color       The line color.
*
**/
void DRAW_Line (s16 x1, s16 y1, s16 x2, s16 y2, u16 color )
   {
   int i,dx,dy,sdx,sdy,dxabs,dyabs,x,y,px,py;

   #define abs(X) ( ( (X) < 0 ) ? -(X) : (X) )
   #define sgn(X) ( ( (X) < 0 ) ? -1 : 1 )

   if ( x1==x2 )  //Vertical Line
      {
      if ( y1 > y2 ) //We assume y2>y1 and invert if not
         {
         i = y2;
         y2 = y1;
         y1 = i;
         }
      LCD_FillRect( x1, y1, 1, y2-y1+1, color );
      return;
      }
   else if ( y1==y2 )  //Horizontal Line
      {
      if ( x1 > x2 ) //We assume x2>x1 and we swap them if not
         {
         i = x2;
         x2 = x1;
         x1 = i;
         }
      LCD_FillRect( x1, y1, x2-x1+1, 1, color );
      return;
      }
   
   dx=x2-x1;      /* the horizontal distance of the line */
   dy=y2-y1;      /* the vertical distance of the line */
   dxabs=abs(dx);
   dyabs=abs(dy);
   sdx=sgn(dx);
   sdy=sgn(dy);
   x=dyabs>>1;
   y=dxabs>>1;
   px=x1;
   py=y1;

   if (dxabs>=dyabs) /* the line is more horizontal than vertical */
      {
      for(i=0;i<dxabs;i++)
         {
         y+=dyabs;
         if (y>=dxabs)
            {
            y-=dxabs;
            py+=sdy;
            }
         px+=sdx;
         LCD_DrawPixel(px,py,color);
         }
      }
   else /* the line is more vertical than horizontal */
      {
      for(i=0;i<dyabs;i++)
         {
         x+=dxabs;
         if (x>=dyabs)
            {
            x-=dyabs;
            px+=sdx;
            }
         py+=sdy;
         LCD_DrawPixel(px,py,color);
         }
      }
   }

