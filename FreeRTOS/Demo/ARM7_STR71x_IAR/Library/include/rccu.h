/******************** (C) COPYRIGHT 2003 STMicroelectronics ********************
* File Name          : rccu.h
* Author             : MCD Application Team
* Date First Issued  : 28/07/2003
* Description        : This file contains all the functions prototypes for the
*                      RCCU software library.
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

#ifndef __RCCU_H
#define __RCCU_H

#include "71x_map.h"

typedef enum {
               RCCU_DEFAULT=0x00,
               RCCU_RCLK_2 =0x01,
               RCCU_RCLK_4 =0x02,
               RCCU_RCLK_8 =0x03
             } RCCU_Clock_Div;

typedef enum {
               RCCU_PLL1_Output,
               RCCU_CLOCK2_16,
               RCCU_CLOCK2,
               RCCU_RTC_CLOCK
             } RCCU_RCLK_Clocks;


                     typedef enum {
               RCCU_PLL1_Mul_12=0x01,
               RCCU_PLL1_Mul_16=0x03,
               RCCU_PLL1_Mul_20=0x00,
               RCCU_PLL1_Mul_24=0x02
             } RCCU_PLL1_Mul;

typedef enum {
               RCCU_PLL2_Mul_12=0x01,
               RCCU_PLL2_Mul_16=0x03,
               RCCU_PLL2_Mul_20=0x00,
               RCCU_PLL2_Mul_28=0x02
             } RCCU_PLL2_Mul;

typedef enum {
               RCCU_Div_1=0x00,
               RCCU_Div_2=0x01,
               RCCU_Div_3=0x02,
               RCCU_Div_4=0x03,
               RCCU_Div_5=0x04,
               RCCU_Div_6=0x05,
               RCCU_Div_7=0x06
             } RCCU_PLL_Div;

typedef enum {
               RCCU_PLL2_Output = 0x01,
               RCCU_USBCK       = 0x00
             } RCCU_USB_Clocks;

typedef enum {
               RCCU_CLK2,
               RCCU_RCLK,
               RCCU_MCLK,
               RCCU_PCLK,
               RCCU_FCLK
             } RCCU_Clocks;

typedef enum {
               RCCU_PLL1_LOCK_IT = 0x0080,
               RCCU_CKAF_IT      = 0x0100,
               RCCU_CK2_16_IT    = 0x0200,
               RCCU_STOP_IT      = 0x0400
             } RCCU_Interrupts;

typedef enum {
               RCCU_PLL1_LOCK   = 0x0002,
               RCCU_CKAF_ST     = 0x0004,
               RCCU_PLL1_LOCK_I = 0x0800,
               RCCU_CKAF_I      = 0x1000,
               RCCU_CK2_16_I    = 0x2000,
               RCCU_STOP_I      = 0x4000
             } RCCU_Flags;

typedef enum {
               RCCU_ExternalReset = 0x00000000,
               RCCU_SoftwareReset = 0x00000020,
               RCCU_WDGReset      = 0x00000040,
               RCCU_RTCAlarmReset = 0x00000080,
               RCCU_LVDReset      = 0x00000200,
               RCCU_WKPReset      = 0x00000400
              }RCCU_ResetSources;


#define RCCU_Div2_Mask  0x00008000
#define RCCU_Div2_Index 0x0F
#define RCCU_FACT_Mask  0x0003

#define RCCU_FACT1_Mask  0x0003

#define RCCU_FACT2_Mask  0x0300
#define RCCU_FACT2_Index 0x08

#define RCCU_MX_Mask   0x00000030
#define RCCU_MX_Index  0x04

#define RCCU_DX_Mask   0x00000007

#define RCCU_FREEN_Mask    0x00000080

#define RCCU_CSU_CKSEL_Mask 0x00000001

#define RCCU_CK2_16_Mask    0x00000008

#define RCCU_CKAF_SEL_Mask  0x00000004

#define RCCU_LOCK_Mask     0x00000002

#define RCCU_USBEN_Mask   0x0100
#define RCCU_USBEN_Index  0x08
#define RCCU_ResetSources_Mask 0x000006E0

// RTC Oscillator Frequency value = 32 768 Hz
#define RCCU_RTC_Osc  32768


/*******************************************************************************
* Function Name  : RCCU_Div2Config
* Description    : Enables/Disables the clock division by two
* Input          : NewState : ENABLE or DISABLE
* Return         : None
*******************************************************************************/
inline void RCCU_Div2Config ( FunctionalState NewState )
{
  if (NewState == ENABLE) RCCU->CFR |= RCCU_Div2_Mask;
    else RCCU->CFR &= ~RCCU_Div2_Mask;
}

/*******************************************************************************
* Function Name  : RCCU_Div2Status
* Description    : Gets the Div2 Flag status
* Input          : None
* Input          : FlagStatus
* Return         : None
*******************************************************************************/
inline FlagStatus RCCU_Div2Status ( void )
{
  return (RCCU->CFR & RCCU_Div2_Mask) == 0 ? RESET : SET;
}

/*******************************************************************************
* Function Name  : RCCU_MCLKConfig
* Description    : Selects the division factor for RCLK to obtain the
*                  MCLK clock for the CPU
* Input          : New_Clock : RCCU_DEFAULT, RCCU_RCLK_2, RCCU_RCLK_4, RCCU_RCLK_8
* Return         : None
*******************************************************************************/
inline void RCCU_MCLKConfig ( RCCU_Clock_Div New_Clock )
{
  PCU->MDIVR = ( PCU->MDIVR & ~RCCU_FACT_Mask ) | New_Clock;
}

/*******************************************************************************
* Function Name  : RCCU_FCLKConfig
* Description    : Selects the division factor for RCLK to obtain the
*                  FCLK clock for the APB1 fast peripherals (PCLK1).
* Input          : New_Clock : RCCU_DEFAULT, RCCU_RCLK_2,
*                               RCCU_RCLK_4, RCCU_RCLK_8
* Return         : None
*******************************************************************************/
inline void RCCU_FCLKConfig ( RCCU_Clock_Div New_Clock )
{
  PCU->PDIVR = ( PCU->PDIVR & ~RCCU_FACT1_Mask ) | New_Clock;
}

/*******************************************************************************
* Function Name  : RCCU_PCLKConfig
* Description    : Selects the division factor for RCLK to obtain the
*                  PCLK clock for the APB2 peripherals (PCLK2).
* Input          : New_Clock : RCCU_DEFAULT, RCCU_RCLK_2,
*                              RCCU_RCLK_4, RCCU_RCLK_8
* Return         : None
*******************************************************************************/
inline void RCCU_PCLKConfig ( RCCU_Clock_Div New_Clock )
{
  PCU->PDIVR =(PCU->PDIVR & ~RCCU_FACT2_Mask)|(New_Clock << RCCU_FACT2_Index);
}

/*******************************************************************************
* Function Name  : RCCU_PLL1Config
* Description    : Configures the PLL1 div & mul factors.
* Input          : New_Mul : RCCU_Mul_12, RCCU_Mul_16, RCCU_Mul_20, RCCU_Mul_28
*                : New_Div : RCCU_Div_1, RCCU_Div_2, RCCU_Div_3,
*                            RCCU_Div_4, RCCU_Div_5, RCCU_Div_6, RCCU_Div_7
* Return         : None
*******************************************************************************/
void RCCU_PLL1Config ( RCCU_PLL1_Mul New_Mul, RCCU_PLL_Div New_Div );

/*******************************************************************************
* Function Name  : RCCU_PLL2Config
* Description    : Configures the PLL2 div & mul factors.
* Input          : New_Mul : RCCU_Mul_12, RCCU_Mul_16, RCCU_Mul_20, RCCU_Mul_28
*                : New_Div : RCCU_Div_1, RCCU_Div_2, RCCU_Div_3, RCCU_Div_4,
*                            RCCU_Div_5, RCCU_Div_6, RCCU_Div_7
* Return         : None
*******************************************************************************/
void RCCU_PLL2Config ( RCCU_PLL2_Mul New_Mul, RCCU_PLL_Div New_Div );

/*******************************************************************************
* Function Name  : RCCU_RCLKSourceConfig
* Description    : Selects the RCLK source clock
* Input          : New_Clock : RCCU_PLL1_OutPut, RCCU_CLOCK2_16, RCCU_CLOCK2
* Return         : None
*******************************************************************************/
void RCCU_RCLKSourceConfig ( RCCU_RCLK_Clocks New_Clock );

/*******************************************************************************
* Function Name  : RCCU_RCLKClockSource
* Description    : Returns the current RCLK source clock
* Input          : None
* Return         : RCCU_PLL1_Output, RCCU_CLOCK2_16, RCCU_CLOCK2
*******************************************************************************/
RCCU_RCLK_Clocks RCCU_RCLKClockSource ( void );

/*******************************************************************************
* Function Name  : RCCU_USBCLKConfig
* Description    : Selects the USB source clock
* Input          : New_Clock : RCCU_PLL2_Output, RCCU_USBCK
* Return         : None
*******************************************************************************/
inline void RCCU_USBCLKConfig ( RCCU_USB_Clocks New_Clock )
{
  PCU->PLL2CR = (PCU->PLL2CR & ~RCCU_USBEN_Mask)|(New_Clock << RCCU_USBEN_Index);
}

/*******************************************************************************
* Function Name  : RCCU_USBClockSource
* Description    : Gets the USB source clock
* Input          : None
* Return         : RCCU_USB_Clocks
*******************************************************************************/
RCCU_USB_Clocks RCCU_USBClockSource ( void );

/*******************************************************************************
* Function Name  : RCCU_FrequencyValue
* Description    : Calculates & Returns any internal RCCU clock freuqency
*                  passed in parametres
* Input          : RCCU_Clocks : RCCU_CLK2, RCCU_RCLK, RCCU_MCLK,
*                  RCCU_PCLK, RCCU_FCLK
* Return         : u32
*******************************************************************************/
u32 RCCU_FrequencyValue ( RCCU_Clocks Internal_Clk );

/*******************************************************************************
* Function Name  : RCCU_ITConfig
* Description    : Configures the RCCU interrupts
* Input          : RCCU interrupts : RCCU_CK2_16_IT, RCCU_CKAF_IT,
*                  RCCU_PLL1_LOCK_IT
* Return         : None
*******************************************************************************/
inline void RCCU_ITConfig ( RCCU_Interrupts RCCU_IT, FunctionalState NewState)
{
  if (NewState == ENABLE) RCCU->CCR |= RCCU_IT; else RCCU->CCR &= ~RCCU_IT;
}

/*******************************************************************************
* Function Name  : RCCU_FlagStatus
* Description    : Checks the RCCU clock flag register status
* Input          : RCCU Flags : RCCU_CK2_16, RCCU_CKAF, RCCU_PLL1_LOCK
* Return         : FlagStatus : SET or RESET
*******************************************************************************/
inline FlagStatus RCCU_FlagStatus ( RCCU_Flags RCCU_flag )
{
  return (RCCU->CFR & RCCU_flag) == 0 ? RESET : SET;
}

/*******************************************************************************
* Function Name  : RCCU_FlagClear
* Description    : Clears a specified flag in the RCCU registers
* Input          : RCCU Flags : RCCU_CK2_16, RCCU_CKAF, RCCU_PLL1_LOCK
* Return         : None
*******************************************************************************/
inline void RCCU_FlagClear ( RCCU_Interrupts RCCU_IT )
{
  RCCU->CFR |= RCCU_IT;
}

/*******************************************************************************
* Function Name  : RCCU_ResetSources
* Description    : Return the source of the system reset
* Input          : None
* Return         : The reset source
*******************************************************************************/
inline RCCU_ResetSources RCCU_ResetSource ()
{

  switch(RCCU->CFR & RCCU_ResetSources_Mask)
  {
    case 0x00000020: return RCCU_SoftwareReset;
    case 0x00000040: return RCCU_WDGReset;
    case 0x00000080: return RCCU_RTCAlarmReset;
    case 0x00000200: return RCCU_LVDReset;
    case 0x00000400: return RCCU_WKPReset;
    default : return RCCU_ExternalReset;
  }
}

#endif	// __RCCU_H

/******************* (C) COPYRIGHT 2003 STMicroelectronics *****END OF FILE****/
