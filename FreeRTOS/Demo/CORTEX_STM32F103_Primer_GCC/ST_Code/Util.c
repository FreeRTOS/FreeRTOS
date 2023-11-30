/********************* (C) COPYRIGHT 2007 RAISONANCE S.A.S. *******************/
/**
*
* @file     Util.c
* @brief    Various utilities  for STM32 CircleOS.
* @author   RT
* @date     07/2007
*
**/
/******************************************************************************/

/* Includes ------------------------------------------------------------------*/

#include "circle.h"
#include "adc.h"

/// @cond Internal

/* Private defines -----------------------------------------------------------*/
#define  GPIO_USB_PIN   GPIO_Pin_1
#define  GPIOx_USB      GPIOA
#define  OsVersion      "V 1.7"    /*!< CircleOS version string. */

/* Private typedef -----------------------------------------------------------*/
enum eSpeed CurrentSpeed;

/* Private variables ---------------------------------------------------------*/
RCC_ClocksTypeDef    RCC_ClockFreq;
int                  dummycounter   = 0;
u8                   fTemperatureInFahrenheit = 0;  /*!< 1 : Fahrenheit, 0 : Celcius (default). */

/* Private function prototypes -----------------------------------------------*/
static void _int2str( char* ptr, s32 X, u16 digit, int flagunsigned, int fillwithzero );

/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
*
*                    _int2str
*
*******************************************************************************/
/**
*
*  Translate a 32 bit word into a string.
*
*  @param[in,out] ptr            A pointer to a string large enough to contain
*                                the translated 32 bit word.
*  @param[in]     X              The 32 bit word to translate.
*  @param[in]     digit          The amount of digits wanted in the result string.
*  @param[in]     flagunsigned   Is the input word unsigned?
*  @param[in]     fillwithzero   Fill with zeros or spaces.
*
**/
/******************************************************************************/
static void _int2str( char* ptr, s32 X, u16 digit, int flagunsigned, int fillwithzero )
   {
   u8    c;
   u8    fFirst   = 0;
   u8    fNeg     = 0;
   u32   DIG      = 1;
   int   i;

   for( i = 1; i < digit; i++ )
      {
      DIG *= 10;
      }

   if( !flagunsigned && ( X < 0 ) )
      {
      fNeg = 1;
      X    = -X;
      }

   u32 r = X;

   for( i = 0; i < digit; i++, DIG /= 10 )
      {
      c  = (r/DIG);
      r -= (c*DIG);

      if( fillwithzero || fFirst || c || ( i == ( digit - 1 ) ) )
         {
         if( ( fFirst == 0 ) && !flagunsigned )
            {
            *ptr++ = fNeg ? '-' : ' ';
            }

         *ptr++ = c + 0x30;
         fFirst = 1;
         }
       else
         {
         *ptr++ = ' ';
         }
      }

   *ptr++ = 0;
   }

/* Public functions for CircleOS ---------------------------------------------*/

/*******************************************************************************
*
*                    delay_unit
*
*******************************************************************************/
/**
*
*  Called by starting_delay().
*
*  @note Not in main.c to avoid inlining.
*
**/
/******************************************************************************/
void delay_unit( void )
   {
   dummycounter++;
   }

/// @endcond

/* Public functions ----------------------------------------------------------*/

/*******************************************************************************
*
*                    UTIL_GetBat
*
*******************************************************************************/
/**
*
*  Return the batterie tension in mV.
*
*  @return Batterie tension in mV.
*
**/
/******************************************************************************/
u16 UTIL_GetBat( void )
   {
#ifdef _ADC
   u16 vbat;

   // Measure VBAT
   vbat = ADC_ConvertedValue[0];  //*( (u16*)ADC1_DR_Address );      // <=== note changed 
   vbat = vbat & 0xFFF;
   vbat = ( vbat * VDD_VOLTAGE_MV ) / 0x1000;

   return vbat;
#else
   return 0;
#endif
   }

/*******************************************************************************
*
*                    UTIL_GetTemp
*
*******************************************************************************/
/**
*
*  Return the Temperature: degrees / 10, Celcius or Fahrenheit.
*
*  @return The temperature (C or F) (averaging of several channels).
*
**/
/******************************************************************************/
u16 UTIL_GetTemp( void )
   {
   s32 temp;
   s16 *p=&ADC_ConvertedValue[1];  //intent; point to first of 8 results from same source - use a short name for it!
   
   // Measure temp
   //temp = ADC_ConvertedValue[1];//*( (u16*)ADC1_DR_Address ); 
   temp = (p[0]+p[1]+p[2]+p[3]+p[4]+p[5]+p[6]+p[7])/8; //take avg of burst of 8 temp reads. may only help reject hi freq noise a bit
                                                       //will not help reduce mains ripple because conversions are SO FAST!!
   temp = temp & 0xFFF;
   temp = ( temp * VDD_VOLTAGE_MV ) / 0x1000;  //finds mV  
   temp = (((1400-temp)*100000)/448)+25000;  //gives approx temp x 1000 degrees C
   
   //Fahrenheit = 32 + 9 / 5 * Celsius
   if ( fTemperatureInFahrenheit ) 
      {
      temp = 32000 + (9 * temp) / 5 ;
      }
   
   return temp / 100;
   }

/*******************************************************************************
*
*                    UTIL_SetTempMode
*
*******************************************************************************/
/**
*
*  Set the temperature mode (F/C)
*
*  @param[in]     mode       0: Celcius, 1: Fahrenheit 
*
**/
/******************************************************************************/
void UTIL_SetTempMode ( int mode )
   {
   fTemperatureInFahrenheit = mode; 
  
   return;
   }


/*******************************************************************************
*
*                    UTIL_GetUsb
*
*******************************************************************************/
/**
*
*  Return the USB connexion state.
*
*  @return The USB connexion state.
*
**/
/******************************************************************************/
u8 UTIL_GetUsb( void )
   {
   GPIO_InitStructure.GPIO_Pin   =  GPIO_USB_PIN;
   GPIO_InitStructure.GPIO_Mode  = GPIO_Mode_IN_FLOATING;
   GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;

   GPIO_Init( GPIOx_USB, &GPIO_InitStructure );

   return ( GPIO_ReadInputDataBit( GPIOx_USB, GPIO_USB_PIN ) == Bit_SET );
   }

/*******************************************************************************
*
*                   UTIL_uint2str
*
*******************************************************************************/
/**
*
*  Convert an <b>unsigned</b> integer into a string.
*
*  @param [out]  ptr    The output string.
*  @param [in]   X      The unsigned value to convert.
*  @param [in]   digit  The number of digits in the output string.
*  @param [in]   fillwithzero  \li 0   fill with blanks.
*                              \li 1   fill with zeros.
*
**/
/********************************************************************************/
void UTIL_uint2str( char* ptr, u32 X, u16 digit, int fillwithzero )
   {
   _int2str( ptr, X, digit, 1, fillwithzero);
   }

/*******************************************************************************
*
*                   UTIL_int2str
*
*******************************************************************************/
/**
*
*  Convert a <b>signed</b> integer into a string.
*
*  @param [out]  ptr    The output string.
*  @param [in]   X      The unsigned value to convert.
*  @param [in]   digit  The number of digits in the output string.
*  @param [in]   fillwithzero  \li 0   fill with blanks.
*                              \li 1   fill with zeros.
*
**/
/******************************************************************************/
void UTIL_int2str( char* ptr, s32 X, u16 digit, int fillwithzero )
   {
   _int2str( ptr, X, digit, 0, fillwithzero);
   }

/*******************************************************************************
*
*                                UTIL_SetPll
*
*******************************************************************************/
/**
*
*  Set clock frequency (lower to save energy)
*
*  @param [in]   speed  New clock speed from very low to very fast.
*
**/
/******************************************************************************/
void UTIL_SetPll( enum eSpeed speed )
   {
   /* Select PLL as system clock source */
   RCC_SYSCLKConfig( RCC_SYSCLKSource_HSI );

   /* Enable PLL */
   RCC_PLLCmd( DISABLE );

   if( ( speed < SPEED_VERY_LOW ) || ( speed > SPEED_VERY_HIGH ) )
      {
      speed = SPEED_MEDIUM;
      } 

   CurrentSpeed = speed; 

   switch( speed )
      {
      // 18 MHz
      case SPEED_VERY_LOW  :
         /* PLLCLK = 6MHz * 3 = 18 MHz */
         RCC_PLLConfig( RCC_PLLSource_HSE_Div2, RCC_PLLMul_3 );
         break;

      // 24MHz
      case SPEED_LOW       :
         /* PLLCLK = 12MHz * 2 = 24 MHz */
         RCC_PLLConfig( RCC_PLLSource_HSE_Div1, RCC_PLLMul_2 );
         break;

      // 36MHz
      case SPEED_MEDIUM    :   
      default              :
         /* PLLCLK = 12MHz * 3 = 36 MHz */
         RCC_PLLConfig( RCC_PLLSource_HSE_Div1, RCC_PLLMul_3 );
         break;

      // 48MHz
      case SPEED_HIGH      :
         /* PLLCLK = 12MHz * 4 = 48 MHz */
         RCC_PLLConfig( RCC_PLLSource_HSE_Div1, RCC_PLLMul_4 );
         break;

      // 72MHz
      case SPEED_VERY_HIGH :
         /* PLLCLK = 12MHz * 6 = 72 MHz */
         RCC_PLLConfig( RCC_PLLSource_HSE_Div1, RCC_PLLMul_6 );
         break;
      }

   /* Enable PLL */
   RCC_PLLCmd( ENABLE );

   /* Wait till PLL is ready */
   while( RCC_GetFlagStatus( RCC_FLAG_PLLRDY ) == RESET )
      { ; }

   /* Select PLL as system clock source */
   RCC_SYSCLKConfig( RCC_SYSCLKSource_PLLCLK );

   /* Wait till PLL is used as system clock source */
   while( RCC_GetSYSCLKSource() != 0x08 )
      { ; }

   /* This function fills a RCC_ClocksTypeDef structure with the current frequencies
     of different on chip clocks (for debug purpose) */
   RCC_GetClocksFreq( &RCC_ClockFreq );
   }

/*******************************************************************************
*
*                                UTIL_GetPll
*
*******************************************************************************/
/**
*
*  Get clock frequency
*
*  @return   Current clock speed from very low to very fast.
*
**/
/******************************************************************************/
enum eSpeed UTIL_GetPll( void )
   {
   return CurrentSpeed;
   }

/*******************************************************************************
*
*                                UTIL_GetVersion
*
*******************************************************************************/
/**
*
*  Get CircleOS version.
*
*  @return  A pointer to a string containing the CircleOS version.
*
**/
/******************************************************************************/
const char* UTIL_GetVersion( void )
   {
   return OsVersion;
   }

/*******************************************************************************
*
*                                UTIL_ReadBackupRegister
*
*******************************************************************************/
/**
*
*  Reads data from the specified Data Backup Register.
*
*  @param[in]  BKP_DR   Specifies the Data Backup Register. This parameter can be BKP_DRx where x:[1, 10]
*
*  @return  The content of the specified Data Backup Register.
*
**/
/******************************************************************************/
u16 UTIL_ReadBackupRegister( u16 BKP_DR )
   {
  return (*(vu16 *)( BKP_BASE + 4 * BKP_DR ) );
   }

/*******************************************************************************
*
*                                UTIL_WriteBackupRegister
*
*******************************************************************************/
/**
*
*  Writes data to the specified Data Backup Register.
*
*  @param[in]  BKP_DR   Specifies the Data Backup Register. This parameter can be BKP_DRx where x:[1, 10]
*  @param[in]  Data     The data to write.
*
**/
/********************************************************************************/
void UTIL_WriteBackupRegister( u16 BKP_DR, u16 Data )
   {
  *(vu16 *)( BKP_BASE + 4 * BKP_DR ) = Data;
   }


/*******************************************************************************
*
*                                UTIL_SetIrqHandler
*
*******************************************************************************/
/**
*
*  Redirect an IRQ handler.
*
*  @param[in]  Offs   Address in the NVIC table
*  @param[in]  pHDL   Pointer to the handler.
*
**/
/********************************************************************************/
void UTIL_SetIrqHandler( int Offs, tHandler pHDL )
   {
   if ( (Offs >= 8) && (Offs<0x100) )
      *(tHandler *)( CIRCLEOS_RAM_BASE + Offs ) = pHDL;
   }

/*******************************************************************************
*
*                                UTIL_GetIrqHandler
*
*******************************************************************************/
/**
*
*  Get the current IRQ handler.
*  Since (V1.6) the vector table is relocated in RAM, the vectors can be easily modified
*  by the applications. 
*
*  @param[in]  Offs   Address in the NVIC table
*  @return  A pointer to the current handler.
*
**/
/********************************************************************************/
tHandler UTIL_GetIrqHandler( int Offs )
   {
   if ( (Offs >= 8) && (Offs<0x100) )
      return *(tHandler *)( CIRCLEOS_RAM_BASE + Offs );
   }



/*******************************************************************************
*
*                                UTIL_SetSchHandler
*
*******************************************************************************/
/**
*
*  Redirect a SCHEDULER handler.
*  Set the current SCHEDULER handler. With UTIL_GetSchHandler(), these functions 
*  allow to take the control of the different handler. You can: 
*        - replace them (get-Set)by your own handler
*        - disable a handler: UTIL_SetSchHandler(Ix,0);  
*        - create a new handler (using the unused handlers).
*  See scheduler.c to understand further...
*
*  @param[in]  Ix   ID if the SCH Handler
*  @param[in]  pHDL   Pointer to the handler.
*
**/
/********************************************************************************/
void UTIL_SetSchHandler( enum eSchHandler Ix, tHandler pHDL )
   {
   if (Ix<SCH_HDL_MAX)
      SchHandler[Ix] = pHDL;
   }

/*******************************************************************************
*
*                                UTIL_GetSchHandler
*
*******************************************************************************/
/**
*
*  Get the current SCHEDULER handler. With UTIL_SetSchHandler(), these functions 
*  allow to take the control of the different handler. You can: 
*        - replace them (get-Set)by your own handler
*        - disable a handler: UTIL_SetSchHandler(Ix,0);  
*        - create a new handler (using the unused handlers).
*  See scheduler.c to understand further...
*
*  @param[in]  Ix   ID is the SCH Handler
*  @return  A pointer to the current handler.
*
**/
/********************************************************************************/
tHandler UTIL_GetSchHandler( enum eSchHandler Ix )
   {
   if ( Ix<SCH_HDL_MAX ) 
      return SchHandler [Ix] ; 
   }

