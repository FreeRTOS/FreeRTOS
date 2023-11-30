/********************* (C) COPYRIGHT 2007 RAISONANCE S.A.S. *******************/
/**
*
* @file     led.c
* @brief    LED management.
* @author   IB
* @date     07/2007
*
**/
/******************************************************************************/

/* Includes ------------------------------------------------------------------*/
#include "circle.h"

/// @cond Internal

/* Private variables ---------------------------------------------------------*/

int            GreenLED_Counter  = 0;
int            RedLED_Counter    = 0;
enum LED_mode  GreenLED_mode     = LED_UNDEF;
enum LED_mode  RedLED_mode       = LED_UNDEF;
enum LED_mode  GreenLED_newmode  = LED_OFF;
enum LED_mode  RedLED_newmode    = LED_OFF;
const int      HalfPeriod_LF     = 200;
const int      HalfPeriod_HF     = 50;
const int      Period_LF         = 200 * 2;
const int      Period_HF         = 50 * 2;

/* Public functions for CircleOS ---------------------------------------------*/

/*******************************************************************************
*
*                                LED_Init
*
*******************************************************************************/
/**
*
*  Initialization of the GPIOs for the LEDs
*
*  @note    Is called by CircleOS startup.
*
**/
/******************************************************************************/
void LED_Init( void )
   {
   GPIO_InitTypeDef GPIO_InitStructure;

   /* Enable LED GPIO clock */
   RCC_APB2PeriphClockCmd( RCC_APB2Periph_GPIOB, ENABLE );

   /* Configure LED pins as output push-pull */
   GPIO_InitStructure.GPIO_Pin   = GPIO_Pin_8 | GPIO_Pin_9 ;
   GPIO_InitStructure.GPIO_Mode  = GPIO_Mode_Out_PP;
   GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;

   GPIO_Init( GPIOB, &GPIO_InitStructure );
   }

/*******************************************************************************
*
*                                LED_Handler
*
*******************************************************************************/
/**
*
*  Called by the CircleOS scheduler to manage the states of the LEDs.
*  LEDs may be on, off or blinking according to their state.
*
**/
/******************************************************************************/
void LED_Handler( void )
   {
   LED_Handler_hw(LED_GREEN);
   LED_Handler_hw(LED_RED);
   }

/*******************************************************************************
*
*                                LED_Handler
*
*******************************************************************************/
/**
*
*  Called by the CircleOS scheduler to manage the states of the LEDs.
*  LEDs may be on, off or blinking according to their state.
*
*  @param[in]  id       A LED_id indicating the LED to take care of.
*
**/
/******************************************************************************/
void LED_Handler_hw( enum LED_id id )
   {
   int            counter;
   enum LED_mode  mode;
   
   // Choose the right LED parameters.
   if( id == LED_GREEN )
      {
      counter = GreenLED_Counter;
      mode    = GreenLED_newmode;
      }
   else
      {
      counter = RedLED_Counter;
      mode    = RedLED_newmode;
      }

   switch( mode )
      {
      case LED_OFF         :
      case LED_ON          :
         if( ( ( id == LED_GREEN ) && ( GreenLED_mode == mode ) ) ||
             ( ( id == LED_RED   ) && ( RedLED_mode   == mode ) ) )
            {
            return;
            }

         if( id == LED_GREEN )
            {
            GPIO_WriteBit( GPIOB, GPIO_Pin_8, ( mode == LED_OFF ) ? Bit_RESET : Bit_SET );

            GreenLED_mode = mode;
            }
         else if( id == LED_RED )
            {
            GPIO_WriteBit( GPIOB, GPIO_Pin_9, ( mode == LED_OFF ) ? Bit_RESET : Bit_SET );

            RedLED_mode = mode;
            }

         counter = -1;
         break;

      case LED_BLINKING_HF :
         counter++;

         if( counter == HalfPeriod_HF )
            {
            GPIO_WriteBit( GPIOB, ( id == LED_RED ) ? GPIO_Pin_9 : GPIO_Pin_8, Bit_SET );
            }
         else if( ( counter < 0 ) || ( counter >= Period_HF ) )
            {
            GPIO_WriteBit( GPIOB, ( id == LED_RED ) ? GPIO_Pin_9 : GPIO_Pin_8, Bit_RESET );

            counter = 0;
            }
         break;

      case LED_BLINKING_LF :
         counter++;

         if( counter == HalfPeriod_LF )
            {
            GPIO_WriteBit( GPIOB, ( id == LED_RED ) ? GPIO_Pin_9 : GPIO_Pin_8, Bit_SET );
            }

         else if( ( counter < 0 ) || ( counter >= Period_LF ) )
            {
            GPIO_WriteBit( GPIOB, ( id == LED_RED ) ? GPIO_Pin_9 : GPIO_Pin_8, Bit_RESET );

            counter = 0;
            }
         break;

      default              :
         break;
      }

   if( id == LED_GREEN )
      {
      GreenLED_Counter = counter;
      GreenLED_mode    = mode;
      }
   else
      {
      RedLED_Counter = counter;
      RedLED_mode    = mode;
      }
   }

/// @endcond

/* Public functions ----------------------------------------------------------*/

/*******************************************************************************
*
*                                LED_Set
*
*******************************************************************************/
/**
*
*  Set a specified LED in a specified mode.
*
*  @param[in]  id    A LED_id specifying the LED to change the mode.
*  @param[in]  mode  A LED_mode describing the new LED mode.
*
**/
/******************************************************************************/
void LED_Set( enum LED_id id, enum LED_mode mode )
   {
   if( id == LED_GREEN )
      {
      GreenLED_newmode = mode;
      }
   else if( id == LED_RED )
      {
      RedLED_newmode = mode;
      }
   }
