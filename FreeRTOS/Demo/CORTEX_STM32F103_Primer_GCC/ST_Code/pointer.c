/********************* (C) COPYRIGHT 2007 RAISONANCE S.A.S. *******************/
/**
*
* @file     pointer.c
* @brief    Various utilities for the pointer management for STM32-primer.
* @author   FL
* @date     07/2007
* @version  1.1
* @date     10/2007
* @version  1.5 various corrections reported by Ron Miller to suppress jittery
*
*
**/
/******************************************************************************/

/* Includes ------------------------------------------------------------------*/
#include "circle.h"

/// @cond Internal

/* Private define ------------------------------------------------------------*/
#define POS_MIN                     0
#define POS_MAX                     (SCREEN_WIDTH - POINTER_WIDTH - 1)
#define POINTER_DIVIDER             50
#define POINTER_DEFAULT_COLOR       RGB_BLUE

// defines for pointer move
#define ANGLEPAUSE                  500 
#define DEFAULT_ANGLESTART          25
#define MIN_ANGLE_FOR_SHIFT_UP      (ANGLEPAUSE+CurrentAngleStart)
#define MIN_ANGLE_FOR_SHIFT_DOWN    (ANGLEPAUSE-CurrentAngleStart)
#define MIN_ANGLE_FOR_SHIFT_RIGHT   (signed)(0+CurrentAngleStart)
#define MIN_ANGLE_FOR_SHIFT_LEFT    (signed)(0-CurrentAngleStart)
#define DEFAULT_SPEED_ON_ANGLE      60

/* Private variables ---------------------------------------------------------*/
static int           divider                          = 0;

unsigned char        BallPointerBmp[ POINTER_WIDTH ]  = { 0x38, 0x7C, 0xFF, 0xFF, 0xFF, 0x7C, 0x38 } ;
unsigned char        locbuf[ POINTER_WIDTH ];
unsigned char        DefaultAreaStore[ 2 * POINTER_WIDTH * POINTER_WIDTH ];

// Variables for pointer.
u8*                  CurrentPointerBmp                = 0;
u8                   CurrentPointerWidth              = 0;
u8                   CurrentPointerHeight             = 0;
u16                  CurrentSpeedOnAngle              = DEFAULT_SPEED_ON_ANGLE;
u32                  CurrentAngleStart                = DEFAULT_ANGLESTART  ;
unsigned char*       ptrAreaStore                     = DefaultAreaStore;
u16                  CurrentPointerColor              = POINTER_DEFAULT_COLOR;
enum POINTER_mode    Pointer_Mode                     = POINTER_UNDEF;
enum POINTER_state   Pointer_State                    = POINTER_S_UNDEF;

s16                  OUT_X;
s16                  OUT_Y;

// Init pointer Info Structure (structure definition in circle.h)
tPointer_Info POINTER_Info = {
         SCREEN_WIDTH - POINTER_WIDTH / 2,
         SCREEN_WIDTH - POINTER_WIDTH / 2,
         0,
         0} ;

/* Private function prototypes -----------------------------------------------*/
static int   POINTER_Move ( void );

/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
*
*                                Pointer_Move
*
*******************************************************************************/
/**
*  Moves LCD pointer according to Mems indications.
*
*  @retval  0  The pointer resides in the screen
*  @retval  -1 The pointer touche the screen edges.
*
**/
/******************************************************************************/
static int POINTER_Move( void )
   {
   int res                    = 0;
   s16 oldPointer_xPos        = POINTER_Info.xPos;
   s16 oldPointer_yPos        = POINTER_Info.yPos;
   s16 unmodied_shift_PosX;
   s16 unmodied_shift_PosY;
   signed outx                = MEMS_Info.OutX_F16 >> 4;
   signed outy                = MEMS_Info.OutY_F16 >> 4;

   POINTER_Info.shift_PosX  =  POINTER_Info.shift_PosY  = 0;

   // The move depends on the screen orientation
   switch( LCD_GetScreenOrientation() )
      {
      // north
      case V12 :
         MEMS_Info.RELATIVE_X = outx;
         MEMS_Info.RELATIVE_Y = outy;

         if( outx > MIN_ANGLE_FOR_SHIFT_RIGHT )
            {
            POINTER_Info.shift_PosX = ( outx - MIN_ANGLE_FOR_SHIFT_RIGHT );
            }
         else if( outx < MIN_ANGLE_FOR_SHIFT_LEFT )
            {
            POINTER_Info.shift_PosX  = ( outx - MIN_ANGLE_FOR_SHIFT_LEFT );
            }               

         if( outy < -MIN_ANGLE_FOR_SHIFT_UP )
            {
            POINTER_Info.shift_PosY = ( outy + MIN_ANGLE_FOR_SHIFT_UP  );
            }
         else if( outy > -MIN_ANGLE_FOR_SHIFT_DOWN )
            {
            POINTER_Info.shift_PosY = ( outy + MIN_ANGLE_FOR_SHIFT_DOWN );
            }
         break;

      // West
      case V9 :   
         MEMS_Info.RELATIVE_X = -( outy );
         MEMS_Info.RELATIVE_Y = outx;

         if( outy > MIN_ANGLE_FOR_SHIFT_RIGHT )
            {
            POINTER_Info.shift_PosX = -( outy - MIN_ANGLE_FOR_SHIFT_RIGHT );
            }
         else if( outy < MIN_ANGLE_FOR_SHIFT_LEFT )
            {
            POINTER_Info.shift_PosX = -( outy - MIN_ANGLE_FOR_SHIFT_LEFT );
            }

         if( outx < -MIN_ANGLE_FOR_SHIFT_UP )
            {
            POINTER_Info.shift_PosY = ( outx + MIN_ANGLE_FOR_SHIFT_UP );
            }
         else if( outx > -MIN_ANGLE_FOR_SHIFT_DOWN )
            {
            POINTER_Info.shift_PosY = ( outx + MIN_ANGLE_FOR_SHIFT_DOWN );
            }
         break;

      // South
      case V6 :   
         MEMS_Info.RELATIVE_X = -( outx );
         MEMS_Info.RELATIVE_Y = -( outy );

         if( outx > MIN_ANGLE_FOR_SHIFT_RIGHT )
            {
            POINTER_Info.shift_PosX = ( MIN_ANGLE_FOR_SHIFT_RIGHT - outx );
            }
         else if( outx < MIN_ANGLE_FOR_SHIFT_LEFT )
            {
            POINTER_Info.shift_PosX = ( MIN_ANGLE_FOR_SHIFT_LEFT - outx );
            }

         if( outy > MIN_ANGLE_FOR_SHIFT_UP )
            {
            POINTER_Info.shift_PosY = -( outy - MIN_ANGLE_FOR_SHIFT_UP );
            }
         else if( outy < MIN_ANGLE_FOR_SHIFT_DOWN )
            {
            POINTER_Info.shift_PosY = +( MIN_ANGLE_FOR_SHIFT_DOWN - outy );
            }
         break;

      // East
      case V3 :   
         MEMS_Info.RELATIVE_X = outy;
         MEMS_Info.RELATIVE_Y = -( outx );

         if( outy > MIN_ANGLE_FOR_SHIFT_RIGHT )
            {
            POINTER_Info.shift_PosX = ( outy - MIN_ANGLE_FOR_SHIFT_RIGHT );
            }
         else if( outy < MIN_ANGLE_FOR_SHIFT_LEFT )
            {
            POINTER_Info.shift_PosX = ( outy - MIN_ANGLE_FOR_SHIFT_LEFT );
            }

         if( outx > MIN_ANGLE_FOR_SHIFT_UP )
            {
            POINTER_Info.shift_PosY = ( MIN_ANGLE_FOR_SHIFT_UP - outx);
            }
         else if( outx < MIN_ANGLE_FOR_SHIFT_DOWN )
            {
            POINTER_Info.shift_PosY = ( MIN_ANGLE_FOR_SHIFT_DOWN - outx );
            }

      default :
         break;
      }

   unmodied_shift_PosX = POINTER_Info.shift_PosX;
   unmodied_shift_PosY = POINTER_Info.shift_PosY;

   POINTER_Info.shift_PosX /= CurrentSpeedOnAngle;
   POINTER_Info.shift_PosY /= CurrentSpeedOnAngle;

   if( Pointer_Mode == POINTER_APPLICATION )
      {
      if ( Application_Pointer_Mgr )
         {
         Application_Pointer_Mgr( POINTER_Info.shift_PosX, POINTER_Info.shift_PosY );
         }

      return 0;
      }

   POINTER_Info.xPos += POINTER_Info.shift_PosX;
   POINTER_Info.yPos += POINTER_Info.shift_PosY;

   if( POINTER_Info.xPos < POINTER_Info.X_PosMin )
      {
      POINTER_Info.xPos = POINTER_Info.X_PosMin;
      }

   if( POINTER_Info.xPos > POINTER_Info.X_PosMax )
      {
      POINTER_Info.xPos = POINTER_Info.X_PosMax;
      }

   if( POINTER_Info.yPos < POINTER_Info.Y_PosMin )
      {
      POINTER_Info.yPos = POINTER_Info.Y_PosMin;
      }

   if( POINTER_Info.yPos > POINTER_Info.Y_PosMax )
      {
      POINTER_Info.yPos = POINTER_Info.Y_PosMax;
      }

   if( ( Pointer_Mode != POINTER_MENU ) && ( Pointer_Mode != POINTER_RESTORE_LESS ) &&
       ( ( oldPointer_xPos != POINTER_Info.xPos ) || ( oldPointer_yPos != POINTER_Info.yPos ) )  )
      {
      // Use default area.
      POINTER_SetCurrentAreaStore( 0 );

      // Restore previously drawn area.
      POINTER_Restore( oldPointer_xPos, oldPointer_yPos, POINTER_WIDTH, POINTER_WIDTH );

      // Save new area and draw pointer
      POINTER_Save( POINTER_Info.xPos, POINTER_Info.yPos, POINTER_WIDTH, POINTER_WIDTH );
      POINTER_Draw( POINTER_Info.xPos, POINTER_Info.yPos, POINTER_WIDTH, POINTER_WIDTH, CurrentPointerBmp );
      }

   if( ( Pointer_Mode == POINTER_RESTORE_LESS ) &&
       ( ( oldPointer_xPos != POINTER_Info.xPos ) || ( oldPointer_yPos != POINTER_Info.yPos ) )  )
      {
      // Use default area.
      POINTER_SetCurrentAreaStore( 0 );

      // Restore previously drawn area.
      POINTER_Restore( oldPointer_xPos, oldPointer_yPos, CurrentPointerWidth, CurrentPointerHeight );

      // Save new area and draw pointer
      POINTER_Save( POINTER_Info.xPos, POINTER_Info.yPos, CurrentPointerWidth, CurrentPointerHeight );
      POINTER_Draw( POINTER_Info.xPos, POINTER_Info.yPos, CurrentPointerWidth, CurrentPointerHeight, CurrentPointerBmp );
      }

   // Is the pointer touching one edge of the screen ?
   if( ( POINTER_Info.xPos == POS_MIN ) || ( POINTER_Info.yPos == POS_MIN ) ||
       ( POINTER_Info.xPos == POS_MAX ) || ( POINTER_Info.yPos == POS_MAX ) )
      {
      res = -1;
      }

   return res;
   }

/* Public functions for CircleOS ---------------------------------------------*/

/*******************************************************************************
*
*                                POINTER_Init
*
*******************************************************************************/
/**
*  Initialize pointer. Called at CircleOS startup. Set default pointer at the
*  middle of the screen and allows it to move into the whole screen.
*
*  @attention  This function must <b>NOT</b> be called by the user.
*
**/
/******************************************************************************/
void POINTER_Init( void )
   {
   // Increase pointer sensibility.
   POINTER_SetCurrentSpeedOnAngle( DEFAULT_SPEED_ON_ANGLE );
   POINTER_SetCurrentAngleStart( DEFAULT_ANGLESTART );
   POINTER_SetCurrentPointer( POINTER_WIDTH, POINTER_WIDTH, BallPointerBmp );
   POINTER_SetMode( POINTER_ON );
   POINTER_SetPos( 56, 56 );
   POINTER_SetRectScreen();

   CurrentPointerColor = POINTER_DEFAULT_COLOR;
   }

/*******************************************************************************
*
*                                POINTER_Handler
*
*******************************************************************************/
/**
*
*  Called by the CircleOS scheduler to manage the pointer.
*
*  @attention  This function must <b>NOT</b> be called by the user.
*
**/
/******************************************************************************/
void POINTER_Handler( void )
   {
   switch( Pointer_Mode )
      {
      // Nothing to do!
      case POINTER_OFF  :
      case POINTER_UNDEF:
         return;
      }

   // Where is the MEMS ?
   MEMS_GetPosition( &OUT_X, &OUT_Y );

   POINTER_Move();
   }

/// @endcond

/* Public functions ----------------------------------------------------------*/

/*******************************************************************************
*
*                                POINTER_SetCurrentPointer
*
*******************************************************************************/
/**
*
*  Set the dimension and the bitmap of the pointer.
*  @note The bitmap is a monochrome one!
*
*  @param[in]  width    width of the pointer  (u8)
*  @param[in]  height   height of the pointer (u8)
*  @param[in]  bmp      pointer to an array of width * height bits.
*
**/
/********************************************************************************/
void POINTER_SetCurrentPointer( u8 width, u8 height, u8* bmp )
   {
   if( !bmp )
      {
      bmp = BallPointerBmp;
      }

   CurrentPointerWidth  = width;
   CurrentPointerHeight = height;
   CurrentPointerBmp    = bmp;
   }

/*******************************************************************************
*
*                                POINTER_GetCurrentAngleStart
*
*******************************************************************************/
/**
*
*  Get the current minimal angle to move pointer
*
*  @return  current minimal angle.
*
**/
/******************************************************************************/
u16 POINTER_GetCurrentAngleStart( void )
   {
   return CurrentAngleStart;
   }

/*******************************************************************************
*
*                                POINTER_SetCurrentAngleStart
*
*******************************************************************************/
/**
*
*  Set the current minimal angle to move pointer
*
*  @param[in]  newangle The new minimal angle to move pointer.
*
**/
/******************************************************************************/
void POINTER_SetCurrentAngleStart( u16 newangle )
   {
   CurrentAngleStart = newangle;
   }

/*******************************************************************************
*
*                                POINTER_GetCurrentSpeedOnAngle
*
*******************************************************************************/
/**
*
*  Return the current speed/angle ratio.
*
*  @return  current ratio.
*
**/
/******************************************************************************/
u16 POINTER_GetCurrentSpeedOnAngle( void )
   {
   return CurrentSpeedOnAngle;
   }

/*******************************************************************************
*
*                                POINTER_SetCurrentSpeedOnAngle
*
*******************************************************************************/
/**
*
*  Set the current speed/angle ratio.
*
*  @param[in]  newspeed New speed/angle ratio.
*
**/
/******************************************************************************/
void POINTER_SetCurrentSpeedOnAngle( u16 newspeed )
   {
   CurrentSpeedOnAngle = newspeed;
   }

/*******************************************************************************
*
*                                POINTER_SetCurrentAreaStore
*
*******************************************************************************/
/**
*
*  Change the current storage area. If the provided value is NULL, the default
*  storage area will be used.
*
*  @param[in]  ptr New storage area (may be null).
*
*  @warning    Memory space pointed by the provided pointer must be large enough
*              to store a color bitmap corresponding to the pointer area.
*              In other words, space must be width * height * 2 large.
*
**/
/******************************************************************************/
void POINTER_SetCurrentAreaStore( u8* ptr )
   {
   ptrAreaStore = ( ptr == 0 ) ? DefaultAreaStore : ptr;
   }

/*******************************************************************************
*
*                                POINTER_SetMode
*
*******************************************************************************/
/**
*
*  Change the current mode of the pointer management.
*
*  @note Must be called only ONCE!!
*
*  @param[in]  mode New pointer management mode.
*
**/
/******************************************************************************/
void POINTER_SetMode( enum POINTER_mode mode )
   {
   u16*  ptr;
   u16   i;
   u16   color;

   switch( mode )
      {
      case POINTER_APPLICATION:
         ptr   = (u16*)DefaultAreaStore;
         color = DRAW_GetBGndColor();

         for ( i = 0; i < (CurrentPointerWidth*CurrentPointerHeight) ; i++ )
            {
            *ptr++ = color;
            }

         POINTER_Draw( POINTER_Info.xPos, POINTER_Info.yPos, CurrentPointerWidth, CurrentPointerHeight, CurrentPointerBmp );
         break;

      case POINTER_RESTORE_LESS:
         POINTER_Draw( POINTER_Info.xPos, POINTER_Info.yPos, CurrentPointerWidth, CurrentPointerHeight, CurrentPointerBmp );
         break;

      case POINTER_ON:
         POINTER_SetCurrentAreaStore( 0 );
         POINTER_Save( POINTER_Info.xPos, POINTER_Info.yPos, POINTER_WIDTH, POINTER_WIDTH );
         POINTER_Draw( POINTER_Info.xPos, POINTER_Info.yPos, CurrentPointerWidth, CurrentPointerHeight,CurrentPointerBmp );
         break;

      case POINTER_OFF:
         POINTER_Info.xPos = ( SCREEN_WIDTH - POINTER_WIDTH ) / 2;
         POINTER_Info.yPos = ( SCREEN_WIDTH - POINTER_WIDTH ) / 2;

      case POINTER_MENU:
         if( Pointer_Mode == POINTER_ON )
            {
            POINTER_SetCurrentAreaStore( 0 );
            POINTER_Restore( POINTER_Info.xPos, POINTER_Info.yPos, POINTER_WIDTH, POINTER_WIDTH );
            }
         break;
      }

   Pointer_Mode = mode;
   }

/*******************************************************************************
*
*                                POINTER_GetMode
*
*******************************************************************************/
/**
*
*  Return the current mode of the pointer management
*
*  @return  Current pointer management mode.
*
**/
/******************************************************************************/
enum POINTER_mode POINTER_GetMode( void )
   {
   return Pointer_Mode;
   }

/*******************************************************************************
*
*                                POINTER_GetState
*
*******************************************************************************/
/**
*
*  Return current pointer state.
*
*  @return  Current pointer state.
*
**/
/******************************************************************************/
enum POINTER_state POINTER_GetState( void )
   {
   return Pointer_State;
   }

/*******************************************************************************
*
*                                POINTER_SetRect
*
*******************************************************************************/
/**
*
*  Set new limits for the move of the pointer
*
*  @param[in]  x        Horizontal coordinate of the bottom left corner of the new area.
*  @param[in]  y        Vertical coordinate of the bottom left corner of the new are.
*  @param[in]  width    New area width.
*  @param[in]  height   New area height.
*
*  @warning       The (0x0) point in on the low left corner.
*
**/
/******************************************************************************/
void POINTER_SetRect( s16 x, s16 y, s16 width, s16 height )
   {
   POINTER_Info.X_PosMin = x;

   if( POINTER_Info.xPos < POINTER_Info.X_PosMin )
      {
      POINTER_Info.xPos = POINTER_Info.X_PosMin;
      }

   POINTER_Info.X_PosMax = x + width - 1;

   if( POINTER_Info.xPos > POINTER_Info.X_PosMax )
      {
      POINTER_Info.xPos = POINTER_Info.X_PosMax;
      }

   POINTER_Info.Y_PosMin = y;

   if( POINTER_Info.yPos < POINTER_Info.Y_PosMin )
      {
      POINTER_Info.yPos = POINTER_Info.Y_PosMin;
      }

   POINTER_Info.Y_PosMax = y + height - 1;

   if( POINTER_Info.yPos > POINTER_Info.Y_PosMax )
      {
      POINTER_Info.yPos = POINTER_Info.Y_PosMax;
      }
   }

/*******************************************************************************
*
*                                POINTER_SetRectScreen
*
*******************************************************************************/
/**
*
*  Allow the pointer to move on the whole screen.
*
**/
/******************************************************************************/
void POINTER_SetRectScreen( void )
   {
   POINTER_SetRect( 0, 0, POS_MAX, POS_MAX );
   }

/*******************************************************************************
*
*                                POINTER_GetPos
*
*******************************************************************************/
/**
*
*  Return the current position of the pointer (on the screen).
*
*  @return  The current pointer screen position with X in the LSB and Y in the MSB.
*
*  @warning       The (0x0) point in on the low left corner.
**/
/******************************************************************************/
u16 POINTER_GetPos( void )
   {
   return ( POINTER_Info.xPos | ( POINTER_Info.yPos << 8 ) );
   }

/*******************************************************************************
*
*                                POINTER_SetPos
*
*******************************************************************************/
/**
*
*  Force the screen position of the pointer.
*
*  @param[in]  x  New horizontal coordinate.
*  @param[in]  y  New vertical coordinate.
*
*  @warning       The (0x0) point in on the low left corner.
*
**/
/******************************************************************************/
void POINTER_SetPos( u16 x, u16 y )
   {
   POINTER_Info.xPos = x;
   POINTER_Info.yPos = y;
   }

/*******************************************************************************
*
*                                POINTER_Draw
*
*******************************************************************************/
/**
*
*  Draw pointer.
*
*  @param[in]  x        Horizontal coordinate of the bottom left corner of the pointer.
*  @param[in]  y        Vertical coordinate of the bottom left corner of the pointer.
*  @param[in]  width    Pointer bitmap width.
*  @param[in]  height   Pointer bitmap height.
*  @param[in]  bmp      Pointer to width * height bit array. If null used default
*                       pointer bitmap.
*
*  @note          The provided bitmap is a monochrome one.
*  @warning       The (0x0) point in on the low left corner.
*
**/
/******************************************************************************/
void POINTER_Draw( u8 x, u8 y, u8 width, u8 height, u8* bmp )
   {
   int   i     = 0;
   int   l     = 0;
   int   n     = 0;
   char* ptr   = ptrAreaStore;
   char  c;
   u16   val;

   // No bitmap provided, use the default one!
   if( bmp == 0 )
      {
      bmp = BallPointerBmp;
      }

   // Select the screen area were going to take care about!
   LCD_SetRect_For_Cmd( x, y, width, height );

   // Let draw to the LCD screen.
   LCD_SendLCDCmd( ST7637_RAMWR );

   while( n < ( width * height ) )
      {
      if( Pointer_Mode != POINTER_RESTORE_LESS )
         {
         // Draw pixel using current storage area data for background pixels.
         c = *ptr++;
         LCD_SendLCDData( ( bmp[ l + ( i / 8 ) ] & ( 1 << ( 7 - ( i % 8 ) ) ) ) ? ( POINTER_GetColor() & 255 ) : c );

         c = *ptr++;
         LCD_SendLCDData( ( bmp[ l + ( i / 8 ) ] & ( 1 << ( 7 - ( i % 8 ) ) ) ) ? ( POINTER_GetColor() >> 8 )  : c );
         }
      else
         {
         // POINTER_RESTORE_LESS: use current background color for background color.
         c = DRAW_GetBGndColor();
         val = ( bmp[ l + ( i / 8 ) ] & ( 1 << ( 7 - ( i % 8 ) ) ) ) ? POINTER_GetColor() : c;

         LCD_SendLCDData( val & 255 );
         LCD_SendLCDData( val >> 8 );
         }

      n++;

      i++;

      // End of line ?
      if( i == width )
         {
         // Next line!
         l++;
         i=0;
         }
      }
   }

/*******************************************************************************
*
*                                POINTER_Save
*
*******************************************************************************/
/**
*
*  Save the background of the pointer.
*
*  @param[in]  x        Horizontal coordinate of the bottom left corner of the area to save.
*  @param[in]  y        Vertical coordinate of the bottom left corner of the area to save.
*  @param[in]  width    Width of the area to save.
*  @param[in]  height   Height of the area to save.
*
*  @note          The store area must be large enough to store all the pixels (16 bits).
*  @warning       The (0x0) point in on the low left corner.
*  @see  POINTER_Restore
*  @see  POINTER_SetCurrentAreaStore
*
**/
/******************************************************************************/
void POINTER_Save( u8 x, u8 y, u8 width, u8 height )
   {
   int   i;
   char* ptr      = ptrAreaStore;
   int   bytesize = ( width * height ) * 2;                // 2 bytes per pixel.

   // Is this pointer management mode, don't save pointer background!
   if( Pointer_Mode == POINTER_RESTORE_LESS )
      {
      return;
      }

   // Select the LCD screen area to read.
   LCD_SetRect_For_Cmd ( x, y, width, height );

   // Send the memory read command to the LCD controller.
   LCD_SendLCDCmd( ST7637_RAMRD );

   // First returned byte is a dummy!
   LCD_ReadLCDData();

   for( i = 0; i < bytesize; i++ )
      {
      *ptr++ = LCD_ReadLCDData();
      }
   }

/*******************************************************************************
*
*                                POINTER_Restore
*
*******************************************************************************/
/**
*
*  Restore the background of the pointer with data saved in the current store area.
*
*  @param[in]  x        Horizontal coordinate of the bottom left corner of the area to restore.
*  @param[in]  y        Vertical coordinate of the bottom left corner of the area to restore.
*  @param[in]  width    Width of the area to restore.
*  @param[in]  height   Height of the area to restore.
*
*  @warning       The (0x0) point in on the low left corner.
*  @see  POINTER_Save
*  @see  POINTER_SetCurrentAreaStore
*
**/
/******************************************************************************/
void POINTER_Restore( u8 x, u8 y, u8 width, u8 height )
   {
   int   i;
   char* ptr      = ptrAreaStore;
   int   bytesize = ( width * height ) * 2;                // 2 bytes per pixel.

   // Select the screen area to write.
   LCD_SetRect_For_Cmd( x, y, width, height );

   // Send the memory write command to the LCD controller.
   LCD_SendLCDCmd( ST7637_RAMWR );

   for( i = 0; i < bytesize; i++ )
      {
      // In this mode, use background color (no data was previously saved).
      if ( Pointer_Mode == POINTER_RESTORE_LESS )
         {
         LCD_SendLCDData( DRAW_GetBGndColor() );
         }
      else
         {
         LCD_SendLCDData( *ptr++ );
         }
      }
   }

/*******************************************************************************
*
*                                POINTER_SetApplication_Pointer_Mgr
*
*******************************************************************************/
/**
*
*  Provides an user defined pointer manager.
*
*  @param[in]  mgr Pointer to the user defined pointer manager.
*
**/
/******************************************************************************/
void POINTER_SetApplication_Pointer_Mgr( tAppPtrMgr mgr )
   {
   Application_Pointer_Mgr = mgr;
   }

/*******************************************************************************
*
*                                POINTER_SetColor
*
*******************************************************************************/
/**
*
*  Set the pointer color.
*
*  @param[in]  color The new pointer color.
*
**/
/******************************************************************************/
void POINTER_SetColor( u16 color )
   {
   CurrentPointerColor = color;
   }

/*******************************************************************************
*
*                                POINTER_GetColor
*
*******************************************************************************/
/**
*
*  Return the current pointer color.
*
*  @return  Current pointer color.
*
**/
/******************************************************************************/
u16 POINTER_GetColor( void )
   {
   return CurrentPointerColor;
   }

/*******************************************************************************
*
*                                POINTER_GetInfo
*
*******************************************************************************/
/**
*
*  Get pointer informations.
*
*  @return  A pointer to a pointer information structure.
*
**/
/******************************************************************************/
tPointer_Info* POINTER_GetInfo( void )
   {
   return &POINTER_Info;
   }
