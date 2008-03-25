/******************** (C) COPYRIGHT 2003 STMicroelectronics ********************
* File Name          : rccu.c
* Author             : MCD Application Team
* Date First Issued  : 07/28/2003
* Description        : This file provides all the RCCU software functions
********************************************************************************
* History:
*  30/11/2004 : V2.0
*  14/07/2004 : V1.3
*  01/01/2004 : V1.2
*******************************************************************************
 THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS WITH
 CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
 AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, INDIRECT
 OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE CONTENT
 OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING INFORMATION
 CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/
#include "rccu.h"

/*******************************************************************************
* Function Name  : RCCU_PLL1Config
* Description    : Configures the PLL1 div & mul factors.
* Input          : New_Mul ( RCCU_PLL1_Mul_12, RCCU_PLL1_Mul_16, RCCU_PLL1_Mul_20,
*                  RCCU_PLL1_Mul_24 )
*                : New_Div ( RCCU_Div_1, RCCU_Div_2, RCCU_Div_3, RCCU_Div_4,
*                  RCCU_Div_5, RCCU_Div_6, RCCU_Div_7)
* Return         : None
*******************************************************************************/
void RCCU_PLL1Config ( RCCU_PLL1_Mul New_Mul, RCCU_PLL_Div New_Div )
{
  u32 Tmp = ( RCCU->PLL1CR & ~RCCU_MX_Mask ) | ( New_Mul << RCCU_MX_Index );
  RCCU->PLL1CR = ( Tmp & ~RCCU_DX_Mask ) | New_Div | 0x40;
}

/*******************************************************************************
* Function Name  : RCCU_PLL2Config
* Description    : Configures the PLL2 div & mul factors.
* Input          : New_Mul ( RCCU_PLL2_Mul_12, RCCU_PLL2_Mul_16, RCCU_PLL2_Mul_20, 
*                  RCCU_Mul_PLL2_28 )
*                : New_Div ( RCCU_Div_1, RCCU_Div_2, RCCU_Div_3, RCCU_Div_4,
*                  RCCU_Div_5, RCCU_Div_6, RCCU_Div_7)
* Return         : None
*******************************************************************************/
void RCCU_PLL2Config ( RCCU_PLL2_Mul New_Mul, RCCU_PLL_Div New_Div )
{
  u32 Tmp = ( PCU->PLL2CR & ~RCCU_MX_Mask ) | ( New_Mul << RCCU_MX_Index );
  PCU->PLL2CR = ( Tmp & ~RCCU_DX_Mask ) | ( New_Div  | RCCU_FREEN_Mask );
}

/*******************************************************************************
* Function Name  : RCCU_RCLKSourceConfig
* Description    : Selects the RCLK source clock
* Input          : New_Clock ( RCCU_PLL1_Output, RCCU_CLOCK2_16, RCCU_CLOCK2 )
* Return         : None
*******************************************************************************/
void RCCU_RCLKSourceConfig ( RCCU_RCLK_Clocks New_Clock )
{
  switch ( New_Clock )
  {
    case RCCU_CLOCK2    :{// Resets the CSU_Cksel bit in clk_flag
                             RCCU->CFR &= ~RCCU_CSU_CKSEL_Mask;
                          // Set the CK2_16 Bit in the CFR
                             RCCU->CFR |= RCCU_CK2_16_Mask;
                          // Deselect The CKAF
                             RCCU->CCR   &= ~RCCU_CKAF_SEL_Mask;
                           // switch off the PLL1
                              RCCU->PLL1CR=((RCCU->PLL1CR & ~RCCU_DX_Mask)\
                              |0x00000003) & ~RCCU_FREEN_Mask;
                              break;}
    case RCCU_CLOCK2_16  :{// ReSet the CK2_16 Bit in the CFR
                              RCCU->CFR &= ~RCCU_CK2_16_Mask;
                           // Deselect The CKAF
                              RCCU->CCR   &= ~RCCU_CKAF_SEL_Mask;
                           // switch off the PLL1
                              RCCU->PLL1CR=((RCCU->PLL1CR & ~RCCU_DX_Mask)\
                              |0x00000003) & ~RCCU_FREEN_Mask;
                              break;}
    case RCCU_PLL1_Output:{// Set the CK2_16 Bit in the CFR
                              RCCU->CFR = RCCU->CFR | RCCU_CK2_16_Mask;
                           // Waits the PLL1 to lock if DX bits are different from '111'
                           // If all DX bit are set the PLL lock flag in meaningless
                              if (( RCCU->PLL1CR & 0x0007 ) != 7)
                                while(!(RCCU->CFR & RCCU_LOCK_Mask));
                           // Deselect The CKAF
                              RCCU->CCR  &= ~RCCU_CKAF_SEL_Mask;
                           // Select The CSU_CKSEL
                              RCCU->CFR |= RCCU_CSU_CKSEL_Mask;
                              break;}
    case RCCU_RTC_CLOCK  :   {RCCU->CCR |= 0x04;
                              break;}
  }
}

/*******************************************************************************
* Function Name  : RCCU_RCLKClockSource
* Description    : Returns the current RCLK source clock
* Input          : None
* Return         : RCCU_PLL1_Output, RCCU_CLOCK2_16, RCCU_CLOCK2, RCCU_RTC_CLOCK
*******************************************************************************/
RCCU_RCLK_Clocks RCCU_RCLKClockSource ( void )
{
  if ((RCCU->CCR & 0x04)==0x04)
    return RCCU_RTC_CLOCK;

  else if ((RCCU->CFR & RCCU_CK2_16_Mask)==0)
    return RCCU_CLOCK2_16;

  else if (RCCU->CFR & RCCU_CSU_CKSEL_Mask)
    return RCCU_PLL1_Output;

  else
    return RCCU_CLOCK2;
}

/*******************************************************************************
* Function Name  : RCCU_USBClockSource
* Description    : Gets the RCLK source clock
* Input          : None
* Return         : RCCU_USB_Clocks ( RCCU_PLL2_Output, RCCU_USBCK )
*******************************************************************************/
RCCU_USB_Clocks RCCU_USBClockSource ( void )
{
  if ((PCU->PLL2CR & RCCU_USBEN_Mask ) >> RCCU_USBEN_Index == 1 )
     return RCCU_PLL2_Output;
  else return RCCU_USBCK;
}

/*******************************************************************************
* Function Name  : RCCU_FrequencyValue
* Description    : Calculates & Returns any internal RCCU clock frequency
*                  passed in parametres
* Input          : RCCU_Clocks ( RCCU_CLK2, RCCU_RCLK, RCCU_MCLK, RCCU_PCLK, RCCU_FCLK )
* Return         : u32
*******************************************************************************/
u32 RCCU_FrequencyValue ( RCCU_Clocks Internal_Clk )
{
  u32 Tmp;
  u8 Div, Mul;
  RCCU_RCLK_Clocks CurrentRCLK;

  Tmp = ( RCCU_Div2Status() == SET )? RCCU_Main_Osc / 2 :  RCCU_Main_Osc;

  if ( Internal_Clk == RCCU_CLK2 )
  {
   Div = 1;
   Mul = 1;
  }
  else
  { CurrentRCLK = RCCU_RCLKClockSource ();
    switch ( CurrentRCLK ){
      case RCCU_CLOCK2_16 : Div = 16;
                            Mul = 1;
                            break;
      case RCCU_CLOCK2    : Div = 1;
                            Mul = 1;
                            break;
      case RCCU_PLL1_Output :{Mul=(RCCU->PLL1CR & RCCU_MX_Mask ) >> RCCU_MX_Index;
                              switch ( Mul )
                              {case 0: Mul = 20; break;
                               case 1: Mul = 12; break;
                               case 2: Mul = 28; break;
                               case 3: Mul = 16; break;
                              }
                              Div = ( RCCU->PLL1CR & RCCU_DX_Mask ) + 1;
                              break;}
     case RCCU_RTC_CLOCK :  Mul = 1;
                            Div = 1;
                            Tmp = RCCU_RTC_Osc;
                            break;}}

  switch ( Internal_Clk ){
      case RCCU_MCLK :{Div <<= PCU->MDIVR & RCCU_FACT_Mask;
                       break;}
      case RCCU_PCLK :{Div <<=(PCU->PDIVR & RCCU_FACT2_Mask ) >> RCCU_FACT2_Index;
                       break;}
      case RCCU_FCLK :{Div <<=  PCU->PDIVR & 0x3;
                       break;}}

  return (Tmp * Mul) / Div;
}

/******************* (C) COPYRIGHT 2003 STMicroelectronics *****END OF FILE****/
