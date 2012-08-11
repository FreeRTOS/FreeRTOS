/********************* (C) COPYRIGHT 2007 RAISONANCE S.A.S. *******************/
/**
*
* @file     mems.c
* @brief    Mems Initialization and management
* @author   FL
* @date     07/2007
* @version  1.1
* @date     10/2007
* @version  1.5 various corrections reported by Ron Miller 
*
**/
/******************************************************************************/

/* Includes ------------------------------------------------------------------*/
#include "circle.h"

/// @cond Internal

/* Private define ------------------------------------------------------------*/
#define RDOUTXL               0xE8  /*!< Multiple Read from OUTXL             */
#define WRCTRL_REG1           0x20  /*!< Single Write CTRL_REG                */
#define RDCTRL_REG1           0xA0  /*!< Single Read CTRL_REG                 */
#define RDID                  0x8F  /*!< Single Read WHO_AM_I                 */
#define LOW                   0x00  /*!< ChipSelect line low                  */
#define HIGH                  0x01  /*!< ChipSelect line high                 */
#define DUMMY_BYTE            0xA5
#define MEMS_DIVIDER          1
#define MEMS_TESTING_DIVIDER  101
#define MARGIN                500
#define DELAY_REACT           20
#define MIN_REACT             15
#define DIV_REACT             10
#define GRAD_SHOCK            200000

/* Private variables ---------------------------------------------------------*/
tMEMS_Info                          MEMS_Info                        = {0};   // structure definition in circle.h
int                                 TestingActive                    = 0;
int                                 StartingFromResetOrShockCounter  = 1000;
int                                 TimeCounterForDoubleClick        = 0;
int                                 TimeLastShock                    = 0;
static int                          divider                          = 0;
static Rotate_H12_V_Match_TypeDef   previous_Screen_Orientation;
u32                                 Gradient2;

//Filtering
unsigned                            N_filtering                      = 0;

//Gradient
s16                                 GradX                            = 0;
s16                                 GradY                            = 0;
s16                                 GradZ                            = 0;

// Pointer move:
// each coordinate (X, Y and Z) is described by 3 variables where suffix means:
//  f = flag to indicate that a move has been done. Cleared by the Ptr Manager when acknowledged.
//  i = amplitude of the move (Grad / 10)
//  t = delay to accept the counter reaction
int fMovePtrX; 
int iMovePtrX;
int tMovePtrX;
int fMovePtrY;
int iMovePtrY;
int tMovePtrY;
int fMovePtrZ;
int iMovePtrZ;
int tMovePtrZ;

s16 XInit      = 0;
s16 YInit      = 0;
s16 ZInit      = 0;

/* Private function prototypes -----------------------------------------------*/
static void MEMS_ChipSelect( u8 State );
static u8 MEMS_SendByte( u8 byte );
static void MEMS_WriteEnable( void );
static u32 MEMS_ReadOutXY( void );
static void MEMS_WakeUp( void );

/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
*
*                                MEMS_WakeUp
*
*******************************************************************************/
/**
*  Wake Up Mems.
*
**/
/******************************************************************************/
static void MEMS_WakeUp( void )
   {
   u8 reg_val;

   /* read RDCTRL_REG1 */

   /* Chip Select low */
   MEMS_ChipSelect( LOW );

   /* Send "RDCTRL_REG1" instruction */
   MEMS_SendByte( RDCTRL_REG1 );

   reg_val = MEMS_SendByte( DUMMY_BYTE );

   /* Chip Select high */
   MEMS_ChipSelect( HIGH );

   /* SET P0:P1 to '11' */
   /* 0xC0 to wake up and 0x30 for full speed frequency (640 Hz). */
   reg_val = reg_val | 0xC0 | 0x30;

   /* Chip Select low */
   MEMS_ChipSelect( LOW );

   /* Send "WRCTRL_REG1" instruction */
   MEMS_SendByte( WRCTRL_REG1 );
   MEMS_SendByte( reg_val );

   /* Chip Select high */
   MEMS_ChipSelect( HIGH );
   }

/*******************************************************************************
*
*                                MEMS_ReadOutXY
*
*******************************************************************************/
/**
*  Reads X and Y Out.
*
*  @return An unsigned 32 bit word with the highest 16 bits containing the Y
*          and the lowest 16 bits the X.
*
**/
/******************************************************************************/
static u32 MEMS_ReadOutXY( void )
   {
   u8 OutXL;
   u8 OutXH;
   u8 OutYL;
   u8 OutYH;
   u8 OutZL;
   u8 OutZH;

   /* Chip Select low */
   MEMS_ChipSelect( LOW );

   /* Send "RDOUTXL" instruction */
   MEMS_SendByte( RDOUTXL );

   /* Read a byte */
   OutXL = MEMS_SendByte( DUMMY_BYTE );

   /* Read a byte */
   OutXH = MEMS_SendByte( DUMMY_BYTE );

   /* Read a byte */
   OutYL = MEMS_SendByte( DUMMY_BYTE );

   /* Read a byte */
   OutYH = MEMS_SendByte( DUMMY_BYTE );

   /* Read a byte */
   OutZL = MEMS_SendByte( DUMMY_BYTE );

   /* Read a byte */
   OutZH = MEMS_SendByte( DUMMY_BYTE );

   MEMS_Info.OutX =  OutXL + ( OutXH << 8 );
   MEMS_Info.OutY =  OutYL + ( OutYH << 8 );
   MEMS_Info.OutZ =  OutZL + ( OutZH << 8 );

   /* Chip Select high */
   MEMS_ChipSelect( HIGH );

   MEMS_Info.OutX_F4 += ( MEMS_Info.OutX - ( MEMS_Info.OutX_F4 >> 2 ) ); // Filter on 4 values.
   MEMS_Info.OutY_F4 += ( MEMS_Info.OutY - ( MEMS_Info.OutY_F4 >> 2 ) ); // Filter on 4 values.
   MEMS_Info.OutZ_F4 += ( MEMS_Info.OutZ - ( MEMS_Info.OutZ_F4 >> 2 ) ); // Filter on 4 values.

   MEMS_Info.OutX_F16 += ( MEMS_Info.OutX - ( MEMS_Info.OutX_F16 >> 4 ) ); // Filter on 16 values.
   MEMS_Info.OutY_F16 += ( MEMS_Info.OutY - ( MEMS_Info.OutY_F16 >> 4 ) ); // Filter on 16 values.
   MEMS_Info.OutZ_F16 += ( MEMS_Info.OutZ - ( MEMS_Info.OutZ_F16 >> 4 ) ); // Filter on 16 values.

   MEMS_Info.OutX_F64 += ( MEMS_Info.OutX - ( MEMS_Info.OutX_F64 >> 6 ) ); // Filter on 64 values.
   MEMS_Info.OutY_F64 += ( MEMS_Info.OutY - ( MEMS_Info.OutY_F64 >> 6 ) ); // Filter on 64 values.
   MEMS_Info.OutZ_F64 += ( MEMS_Info.OutZ - ( MEMS_Info.OutZ_F64 >> 6 ) ); // Filter on 64 values.

   MEMS_Info.OutX_F256 += ( MEMS_Info.OutX - ( MEMS_Info.OutX_F256 >> 8) ); // Filter on 256 values.
   MEMS_Info.OutY_F256 += ( MEMS_Info.OutY - ( MEMS_Info.OutY_F256 >> 8) ); // Filter on 256 values.
   MEMS_Info.OutZ_F256 += ( MEMS_Info.OutZ - ( MEMS_Info.OutZ_F256 >> 8) ); // Filter on 256 values.

   if( N_filtering < 256 )
      {
      // Just to validate the calculated average values.
      N_filtering++; 
      }

   return ( MEMS_Info.OutX + ( MEMS_Info.OutY << 16 ) );
   }

/*******************************************************************************
*
*                                MEMS_ChipSelect
*
*******************************************************************************/
/**
*  Selects or deselects the MEMS device.
*
*  @param[in]  State Level to be applied on ChipSelect pin.
*
**/
/******************************************************************************/
static void MEMS_ChipSelect( u8 State )
   {
   /* Set High or low the chip select line on PA.4 pin */
   GPIO_WriteBit( GPIOD, GPIO_Pin_2, (BitAction)State );
   }

/*******************************************************************************
*
*                                MEMS_SendByte
*
*******************************************************************************/
/**
*  Sends a byte through the SPI interface and return the byte received from 
*  the SPI bus.
*
*  @param[in]  byte The byte to send to the SPI interface.                  
*
*  @return The byte returned by the SPI bus.
*
**/
/******************************************************************************/
static u8 MEMS_SendByte( u8 byte )
   {
   /* Loop while DR register in not emplty */
   while( SPI_I2S_GetFlagStatus( SPI2, SPI_I2S_FLAG_TXE ) == RESET );

   /* Send byte through the SPI2 peripheral */
   SPI_I2S_SendData( SPI2, byte );

   /* Wait to receive a byte */
   while( SPI_I2S_GetFlagStatus( SPI2, SPI_I2S_FLAG_RXNE ) == RESET );

   /* Return the byte read from the SPI bus */
   return SPI_I2S_ReceiveData( SPI2 );
   }

/* Public functions for CircleOS ---------------------------------------------*/

/*******************************************************************************
*
*                                MEMS_Init
*
*******************************************************************************/
/**
*
*  Initializes the peripherals used by the SPI MEMS driver.
*
*  @attention  This function must <b>NOT</b> be called by the user.
*
**/
/******************************************************************************/
void MEMS_Init(void)
{
   SPI_InitTypeDef  SPI_InitStructure;
   GPIO_InitTypeDef GPIO_InitStructure;

   /* Configure PC6 and PC7 as Output push-pull For MEMS*/
   GPIO_InitStructure.GPIO_Pin   = GPIO_Pin_6 | GPIO_Pin_7;
   GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;
   GPIO_InitStructure.GPIO_Mode  = GPIO_Mode_Out_PP;

   GPIO_Init( GPIOC, &GPIO_InitStructure );

   /* Enable SPI2 and GPIOA clocks */
   RCC_APB1PeriphClockCmd( RCC_APB1Periph_SPI2,  ENABLE );
   RCC_APB2PeriphClockCmd( RCC_APB2Periph_GPIOB, ENABLE );
   RCC_APB2PeriphClockCmd( RCC_APB2Periph_GPIOD, ENABLE );

   /* Configure SPI2 pins: SCK, MISO and MOSI */
   GPIO_InitStructure.GPIO_Pin   = GPIO_Pin_13 | GPIO_Pin_14 | GPIO_Pin_15;
   GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;
   GPIO_InitStructure.GPIO_Mode  = GPIO_Mode_AF_PP;

   GPIO_Init( GPIOB, &GPIO_InitStructure );

   /* Configure PD2 as Output push-pull, used as MEMS Chip select */
   GPIO_InitStructure.GPIO_Pin   = GPIO_Pin_2;
   GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;
   GPIO_InitStructure.GPIO_Mode  = GPIO_Mode_Out_PP;

   GPIO_Init( GPIOD, &GPIO_InitStructure );

   /* SPI2 configuration */
   SPI_InitStructure.SPI_Direction           = SPI_Direction_2Lines_FullDuplex;
   SPI_InitStructure.SPI_Mode                = SPI_Mode_Master;
   SPI_InitStructure.SPI_DataSize            = SPI_DataSize_8b;
   SPI_InitStructure.SPI_CPOL                = SPI_CPOL_High;
   SPI_InitStructure.SPI_CPHA                = SPI_CPHA_2Edge;
   SPI_InitStructure.SPI_NSS                 = SPI_NSS_Soft;
   SPI_InitStructure.SPI_BaudRatePrescaler   = SPI_BaudRatePrescaler_256;
   SPI_InitStructure.SPI_FirstBit            = SPI_FirstBit_MSB;
   SPI_InitStructure.SPI_CRCPolynomial       = 7;

   SPI_Init( SPI2, &SPI_InitStructure );

   /* Enable SPI2  */
   SPI_Cmd( SPI2, ENABLE );

   if( MEMS_ReadID() != 0x3A )
      {
      int i;

      // Try to resynchronize
      for( i = 0 ; i < 17 ; i++ )
         {
         /* Configure SPI2 pins: SCK, MISO and MOSI */
         GPIO_InitStructure.GPIO_Pin   = GPIO_Pin_13 | GPIO_Pin_15;
         GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;
         GPIO_InitStructure.GPIO_Mode  = GPIO_Mode_Out_PP;

         GPIO_Init( GPIOB, &GPIO_InitStructure );
         GPIO_WriteBit( GPIOB, GPIO_Pin_15, HIGH );
         MEMS_ChipSelect( LOW );

         GPIO_WriteBit( GPIOB, GPIO_Pin_13, LOW );
         GPIO_WriteBit( GPIOB, GPIO_Pin_13, HIGH );
         MEMS_ChipSelect( HIGH );

         /* Configure again PB. SCK as SPI2 pin */
         GPIO_InitStructure.GPIO_Pin   = GPIO_Pin_13 | GPIO_Pin_15;
         GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;
         GPIO_InitStructure.GPIO_Mode  = GPIO_Mode_AF_PP;

         GPIO_Init( GPIOB, &GPIO_InitStructure );
         if ( MEMS_ReadID() == 0x3A )
            {
            break;
            }
         }

      if( i == 17 )
         {
         DRAW_DisplayString( 1, 50, "Test MEM ID Failed", 17 );
         }
      }

   /* Read for the first time */
   N_filtering = 0;

   MEMS_ReadOutXY();

   MEMS_Info.OutX_F4 = MEMS_Info.OutX_F16 = MEMS_Info.OutX_F64 = MEMS_Info.OutX_F256 = MEMS_Info.OutX;
   MEMS_Info.OutY_F4 = MEMS_Info.OutY_F16 = MEMS_Info.OutY_F64 = MEMS_Info.OutY_F256 = MEMS_Info.OutY;
   MEMS_Info.OutZ_F4 = MEMS_Info.OutZ_F16 = MEMS_Info.OutZ_F64 = MEMS_Info.OutZ_F256 = MEMS_Info.OutZ;

   /* Init X and Y*/
   MEMS_GetPosition( &XInit, &YInit );

   /* Wake Up Mems*/
   MEMS_WakeUp();
}

/*******************************************************************************
*
*                                MEMS_Handler
*
*******************************************************************************/
/**
*
*  Called by the CircleOS scheduler to manage the MEMS. The Circle beeps if the
*  MEMS is shocked.
*
*  @attention  This function must <b>NOT</b> be called by the user.
*
**/
/******************************************************************************/
void MEMS_Handler( void )
   {
   char buffer [20];
   int  i;
   int  ofs_disp = 0;

   if( StartingFromResetOrShockCounter )
      {
      StartingFromResetOrShockCounter--;
      }
   TimeCounterForDoubleClick++;

   MEMS_ReadOutXY();

   // Evaluate gradients
   GradX = ( MEMS_Info.OutX_F4 >> 2 ) - MEMS_Info.OutX;
   GradY = ( MEMS_Info.OutY_F4 >> 2 ) - MEMS_Info.OutY;
   GradZ = ( MEMS_Info.OutZ_F4 >> 2 ) - MEMS_Info.OutZ;

   // Decide whether a direction is selected
   if( tMovePtrX == 0 )
      {
      if( ( GradX > MIN_REACT ) || ( GradX < -MIN_REACT ) )
         {
         iMovePtrX = GradX / DIV_REACT; 
         tMovePtrX = DELAY_REACT;
         fMovePtrX = 1;
         }
      }
   else
      {
      tMovePtrX--;
      }

   if( tMovePtrY == 0 )
      {
      if( ( GradY > MIN_REACT ) || ( GradY < -MIN_REACT ) )
         {
         iMovePtrY = GradY / DIV_REACT;   //FL071012 rrm fix
         tMovePtrY = DELAY_REACT;
         fMovePtrY = 1;
         }
      }
   else
      {
      tMovePtrY--;
      }

   if( tMovePtrZ==0 )
      {
      if( ( GradZ > MIN_REACT ) || ( GradY < -MIN_REACT ) )
         {
         iMovePtrZ = GradZ / DIV_REACT;
         tMovePtrZ = DELAY_REACT;
         fMovePtrZ = 1;
         }
      }
   else
      {
      tMovePtrZ--;
      }

   Gradient2 = (s32)GradX * (s32)GradX + (s32)GradY * (s32)GradY + (s32)GradZ * (s32)GradZ;

   // MEMS is shocked, let's beep!
   if( ( Gradient2 > GRAD_SHOCK ) && ( BUZZER_GetMode() == BUZZER_OFF ) && ( StartingFromResetOrShockCounter == 0 ) )
      {
      MEMS_Info.Shocked++;
/*FL071007       = 1;
      Suggested by Bob Seabrook:  a further posiblity is to increment Shocked rather than just setting it
      So it can still be tested for non zero as before but one can  get more
      info from the int without extra cost. */

#define DELAY_BETWEEN_TWO_SHOCK      20
#define MAX_DELAY_FOR_DOUBLECLICK    150
      StartingFromResetOrShockCounter  = DELAY_BETWEEN_TWO_SHOCK; //< filter: short delay before detecting the next shock
      if ( (TimeCounterForDoubleClick - TimeLastShock) < MAX_DELAY_FOR_DOUBLECLICK )
         {
         MEMS_Info.DoubleClick++;
         TimeLastShock = 0;
         }
      else
         {
         TimeLastShock = TimeCounterForDoubleClick;
         }    
      BUZZER_SetMode( BUZZER_SHORTBEEP );
      }
   }

/*******************************************************************************
*
*                                MEMS_ReadID
*
*******************************************************************************/
/**
*  Reads SPI chip identification.
*
*  @return The SPI chip identification.
*
**/
/******************************************************************************/
u8 MEMS_ReadID( void )
   {
   u8 Temp = 0;

   /* Chip Select low */
   MEMS_ChipSelect( LOW );

   /* Send "RDID" instruction */
   MEMS_SendByte( RDID );

   /* Read a byte from the MEMS */
   Temp = MEMS_SendByte( DUMMY_BYTE );

   /* Chip Select low */
   MEMS_ChipSelect( HIGH );

   return Temp;
   }

/// @endcond

/* Public functions ----------------------------------------------------------*/

/*******************************************************************************
*
*                                MEMS_GetPosition
*
*******************************************************************************/
/**
*
*  Returns the current (relative) position of the Primer.
*  Only X-Y axis are considered here. 
*
*  @param[out] pX    Current horizontal coordinate.
*  @param[out] pY    Current vertical coordinate.
*
*  @warning    The (0x0) point in on the low left corner.
*  @note       For absolute position information use MEMS_GetInfo()
*
**/
/******************************************************************************/
void MEMS_GetPosition( s16* pX, s16* pY )
   {
   *pX = MEMS_Info.OutX - XInit;
   *pY = MEMS_Info.OutY - YInit;
   }

/*******************************************************************************
*
*                                MEMS_GetRotation
*
*******************************************************************************/
/**
*
*  Returns current screen orientation.
*
*  @param[out]  pH12 Current screen orientation.
*
**/
/******************************************************************************/
void MEMS_GetRotation( Rotate_H12_V_Match_TypeDef* pH12 )
   {
   s16 sX = MEMS_Info.OutX;
   s16 sY = MEMS_Info.OutY;

   if( ( ( sX <= -MARGIN ) && ( sY <= 0 ) && (sX<=sY ) ) || 
       ( ( sX <=- MARGIN ) && ( sY > 0) && (sX <= (-sY ) ) ) )
      {
      // 1st case: x<0, |x|>y => H12 = V9
      *pH12 = V9;
      }
   else if( ( ( sY <= -MARGIN ) && ( sX <= 0 ) && ( sY <= sX ) ) ||
            ( ( sY <= -MARGIN ) && ( sX > 0 ) && ( sY <= (-sX ) ) ) ) 
      {
      // 2nd case: y<0, |y|>x => H12 = V12
      *pH12 = V12;
      }
   else if( ( ( sX >= MARGIN ) && ( sY <= 0 ) && ( sX >= (-sY) ) ) || 
            ( ( sX >= MARGIN ) && ( sY > 0 ) && ( sX >= sY ) ) )
      {
      // 3rd case: x>0, |x|>y => H12=V3
      *pH12 = V3;
      }
   else if( ( ( sY >= MARGIN ) && ( sX <= 0 ) && ( sY >= (-sX ) ) ) ||
            ( ( sY >= MARGIN ) && ( sX > 0 ) && ( sY >= sX ) ) )
      {
      // 4th case: y>0,  |y|>x => H12=V6
      *pH12 = V6;
      }
   }

/*******************************************************************************
*
*                                MEMS_SetNeutral
*
*******************************************************************************/
/**
*
*  Set current position as "neutral position".
*
**/
/******************************************************************************/
void MEMS_SetNeutral( void )
   {
   // Set Neutral position.
   MEMS_GetPosition( &XInit, &YInit );
   }

/*******************************************************************************
*
*                                MEMS_GetInfo
*
*******************************************************************************/
/**
*
*  Return the current MEMS information (state, absolute position...).
*
*  @return  a pointer to tMEMS_Info
*
**/
/******************************************************************************/
tMEMS_Info* MEMS_GetInfo( void )
   {
   return &MEMS_Info;
   }
