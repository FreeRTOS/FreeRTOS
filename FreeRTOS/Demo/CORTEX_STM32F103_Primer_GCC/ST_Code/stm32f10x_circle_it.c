/********************* (C) COPYRIGHT 2007 RAISONANCE S.A.S. *******************/
/**
*
* @file     stm32f10x_circle_it.c
* @brief    Interrupt handler for the CircleOS project.
* @author   FL
* @author   IB
* @date     07/2007
*
**/
/******************************************************************************/

/* Includes ------------------------------------------------------------------*/
#include "circle.h"

/* External variables --------------------------------------------------------*/
extern u16 CCR_Val;
extern u16 Current_CCR_BackLightStart;

/*******************************************************************************
*
*                                NMIException
*
*******************************************************************************/
/**
*
*  Handles the NMI exception.
*
**/
/******************************************************************************/
void NMIException( void ) {}

/*******************************************************************************
*
*                                HardFaultException
*
*******************************************************************************/
/**
*
*  Handles the Hard Fault exception.
*
**/
/******************************************************************************/
void HardFaultException( void ) 
   {
   #ifdef TIMING_ANALYSIS     //to debug with a scope
   GPIO_WriteBit( GPIOA, GPIO_Pin_5, Bit_RESET );  
   GPIO_WriteBit( GPIOA, GPIO_Pin_5, Bit_SET );    
   #endif
   }

/*******************************************************************************
*
*                                MemManageException
*
*******************************************************************************/
/**
*
*  Handles the Memory Manage exception.
*
**/
/******************************************************************************/
void MemManageException( void ) {}

/*******************************************************************************
*
*                                BusFaultException
*
*******************************************************************************/
/**
*
*  Handles the Bus Fault exception.
*
**/
/******************************************************************************/
void BusFaultException( void ) {}

/*******************************************************************************
*
*                                UsageFaultException
*
*******************************************************************************/
/**
*
*  Handles the Usage Fault exception.
*
**/
/******************************************************************************/
void UsageFaultException( void ) {}

/*******************************************************************************
*
*                                DebugMonitor
*
*******************************************************************************/
/**
*
*  Handles the  Debug Monitor exception.
*
**/
/******************************************************************************/
void DebugMonitor( void ) {}

/*******************************************************************************
*
*                                SVCHandler
*
*******************************************************************************/
/**
*
*  Handles the SVCall exception.
*
**/
/******************************************************************************/
void SVCHandler( void ) {}

/*******************************************************************************
*
*                                PendSVC
*
*******************************************************************************/
/**
*
*  Handles the PendSVC exception.
*
**/
/******************************************************************************/
void PendSVC( void ) {}

/*******************************************************************************
*
*                                DummyHandler
*
*******************************************************************************/
/**
*
*  Default handling for the IRQ-Exception
*
**/
/******************************************************************************/
void DummyHandler ( void ) {}

/*******************************************************************************
*
*                                TIM2_IRQHandler
*
*******************************************************************************/
/**
*
*  Handles the TIM2 global interrupt request.
*
**/
/******************************************************************************/
void TIM2_IRQHandler( void )
   {
   #ifdef TIMING_ANALYSIS     //to debug with a scope
   GPIO_WriteBit( GPIOA, GPIO_Pin_7, Bit_RESET );
   #endif

   /* Clear TIM2 update interrupt */
   TIM_ClearITPendingBit( TIM2, TIM_IT_Update );

   MEMS_Handler();

   #ifdef TIMING_ANALYSIS     //to debug with a scope
   GPIO_WriteBit( GPIOA, GPIO_Pin_7, Bit_SET );
   #endif
   }

/*******************************************************************************
*
*                                TIM3_IRQHandler
*
*******************************************************************************/
/**
*
*  Handles the TIM3 global interrupt request.
*
**/
/******************************************************************************/
void TIM3_IRQHandler( void )
{
   u16 capture = 0;

   if( TIM_GetITStatus( TIM3, TIM_IT_CC3 ) != RESET )
      {
      capture = TIM_GetCapture3( TIM3 );

      TIM_SetCompare3( TIM3, capture + CCR_Val + 1 );
      TIM_ClearITPendingBit( TIM3, TIM_IT_CC3 );
   }
}

/*******************************************************************************
*
*                                TIM4_IRQHandler
*
*******************************************************************************/
/**
*
*  Handles the TIM4 global interrupt request.
*
**/
/******************************************************************************/
void TIM4_IRQHandler( void )
{
   u16 BackLight_capture = 0;

   if( TIM_GetITStatus( TIM4, TIM_IT_CC2 ) != RESET )
      {
      BackLight_capture = TIM_GetCapture2( TIM4 );

      TIM_SetCompare2( TIM4, BackLight_capture + Current_CCR_BackLightStart + 1 );
      TIM_ClearITPendingBit( TIM4, TIM_IT_CC2 );
  }
}

