/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_scu.c
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : This file provides the SCU library software functions
********************************************************************************
* History:
* 05/24/2006 : Version 1.1
* 05/18/2006 : Version 1.0
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS WITH
* CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME. AS
* A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, INDIRECT
* OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE CONTENT
* OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING INFORMATION
* CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Includes ------------------------------------------------------------------*/
#include "91x_scu.h"

/* Include of other module interface headers ---------------------------------*/
/* Local includes ------------------------------------------------------------*/
/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
#define SCU_PLLEN 0x80000
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Interface functions -------------------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : SCU_MCLKSourceConfig
* Description    : Configures the MCLK source clock
* Input          : MCLK_Source = SCU_MCLK_OSC, SCU_MCLK_PLL or SCU_MCLK_RTC
* Output         : None
* Return         : ErrorStatus: SUCCESS or ERROR
* Note           : this function returns ERROR if trying to select the PLL as
*                  clock source while the PLL is disabled or not locked.
*******************************************************************************/
ErrorStatus SCU_MCLKSourceConfig(u32 MCLK_Source)
{
  u32 CLKCNTR_Value;

  CLKCNTR_Value = SCU->CLKCNTR;         /*get CLKCNTR register value*/
  CLKCNTR_Value &=~0x3;                 /*clear field MCLKSEL*/
  if (MCLK_Source == SCU_MCLK_PLL)      /*PLL selected as clock source*/
  {
    /*check if PLL enabled & locked*/
    if (!((SCU->PLLCONF&SCU_PLLEN)&&(SCU->SYSSTATUS&SCU_FLAG_LOCK)))
    return ERROR;
  }
  else CLKCNTR_Value |=MCLK_Source;     /*OSC or RTC selected as clock source*/
  SCU->CLKCNTR = CLKCNTR_Value;         /*Update CLKCNTR register value*/
  return SUCCESS;
}

/*******************************************************************************
* Function Name  : SCU_PLLFactorsConfig
* Description    : Sets the PLL factors
* Input          : PLLN, PLLM and PLLP
* Output         : None
* Return         : ErrorStatus: ERROR or SUCCESS
* Notes          : -The PLL factors must respect the PLL specification requirements
*                  -The function returns ERROR if trying to change PLL
*                   factors while PLL is selected as Main Clock source (MCLK)
*                  -This function disables the PLL, to enable the PLL use
*                   function" SCU_PLLCmd(ENABLE)" after setting the PLL factors
******************************************************************************/
ErrorStatus SCU_PLLFactorsConfig(u8 PLLN, u8 PLLM, u8 PLLP)
{
  if (SCU_PLLCmd(DISABLE)==SUCCESS)      /*Disable PLL*/
  {
    SCU->PLLCONF =0;                     /*clear PLLCONF register*/
    SCU->PLLCONF |=(PLLN<<8);            /*update PLLN field*/
    SCU->PLLCONF |=PLLM;                 /*update PLLM field*/
    SCU->PLLCONF |=PLLP<<16;             /*update PLLP field*/
    return SUCCESS;
  }
  return ERROR;
}

/*******************************************************************************
* Function Name  : SCU_PLLCmd
* Description    : Enable or Disable the PLL
* Input          : NewState = ENABLE or DISABLE
* Output         : None
* Return         : ErrorStatus: SUCCESS or ERROR
* Note           : -The function returns ERROR if:
*                   *trying to disable the PLL while it is selected as the MCLK
*                   *trying to enable the PLL while it is already enabled and
*                    locked
*******************************************************************************/
ErrorStatus SCU_PLLCmd(FunctionalState NewState)
{
  vu32 i;
  if (NewState==ENABLE)
  {
    if (!((SCU->PLLCONF&SCU_PLLEN)&&(SCU->SYSSTATUS&SCU_FLAG_LOCK)))
    {
      SCU->SYSSTATUS|=SCU_FLAG_LOCK;               /*clear LOCK bit*/
      SCU->PLLCONF |=SCU_PLLEN;                    /*PLL Enable*/
      while(!SCU->SYSSTATUS&SCU_FLAG_LOCK);        /*Wait PLL to lock*/
      return SUCCESS;
    }
    else return ERROR;
  }
  else /*NewState = DISABLE*/
  {
    if(SCU->CLKCNTR&0x3)                /*check if PLL not sys CLK*/
    {
      for(i=10;i>0;i--);                /*delay before PLL disabling*/
      SCU->PLLCONF &=~SCU_PLLEN;        /*PLL Disable*/
      return SUCCESS;
    }
    else return ERROR;
  }
}

/*******************************************************************************
* Function Name  : SCU_RCLKDivisorConfig
* Description    : Sets the RCLK divisor value
* Input          : RCLK_Divisor
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_RCLKDivisorConfig(u32 RCLK_Divisor)
{
  SCU->CLKCNTR &=SCU_RCLK_Div1;              /*clear RCLKDIV[2:0] field*/
  if (RCLK_Divisor!=SCU_RCLK_Div1)
  SCU->CLKCNTR |= RCLK_Divisor;              /*update field with RCLK divisor*/
}

/*******************************************************************************
* Function Name  : SCU_HCLKDivisorConfig
* Description    : Sets the HCLK divisor value
* Input          : HCLK_Divisor
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_HCLKDivisorConfig(u32 HCLK_Divisor)
{
  SCU->CLKCNTR &=SCU_HCLK_Div1;              /*clear AHBDIV[1:0] field*/
  if (HCLK_Divisor!=SCU_HCLK_Div1)
  SCU->CLKCNTR |= HCLK_Divisor;              /*update field with HCLK divisor*/
}

/*******************************************************************************
* Function Name  : SCU_PCLKDivisorConfig
* Description    : Sets the PCLK divisor value
* Input          : PCLK_Divisor
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_PCLKDivisorConfig(u32 PCLK_Divisor)
{
  SCU->CLKCNTR &=SCU_PCLK_Div1;              /*clear APBDIV[1:0] field*/
  if (PCLK_Divisor!=SCU_PCLK_Div1)
  SCU->CLKCNTR |= PCLK_Divisor;              /*update field with PCLK Divisor*/
}

/*******************************************************************************
* Function Name  : SCU_APBPeriphClockConfig
* Description    : Enable the clock for an APB peripheral
* Input          : -APBPerip : APB peripherals(__RTC, __ADC ,...)
*                  -NewState : ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_APBPeriphClockConfig(u32 APBPeriph, FunctionalState NewState)
{
  if (NewState==ENABLE)                     /*Enable clock for APB peripheral*/
  SCU->PCGR1 |=APBPeriph;
  else
  SCU->PCGR1 &=~APBPeriph;                  /*Disable clock for APB peripheral*/
}

/*******************************************************************************
* Function Name  : SCU_AHBPeriphClockConfig
* Description    : Enable the clock for an AHB peripheral
* Input          : -AHBPerip: AHB peripherals(__USB, __DMA,...)
*                  -NewState : ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_AHBPeriphClockConfig(u32 AHBPeriph, FunctionalState NewState)
{
  if (NewState==ENABLE)                     /*Enable clock for AHB peripheral*/
  SCU->PCGRO |=AHBPeriph;
  else
  SCU->PCGRO &=~AHBPeriph;                  /*Disable clock for AHB peripheral*/
}

/*******************************************************************************
* Function Name  : SCU_APBPeriphReset
* Description    : Assert or deassert Reset on APB peripheral
* Input          : -APBPeriph: APB peripherals(__RTC, __ADC,...)
                   -NewState : ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_APBPeriphReset(u32 APBPeriph, FunctionalState NewState)
{
  if (NewState==DISABLE)                    /*APB peripheral not held in Reset*/
  SCU->PRR1 |=APBPeriph;
  else
  SCU->PRR1 &=~APBPeriph;                   /*APB peripheral held in Reset*/
}

/*******************************************************************************
* Function Name  : SCU_AHBPeriphReset
* Description    : Assert or deassert Reset on AHB peripheral
* Input          : -AHBPeriph: AHB peripherals(__USB, __DMA,...)
                   -NewState : ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_AHBPeriphReset(u32 AHBPeriph, FunctionalState NewState)
{
  if (NewState==DISABLE)
  SCU->PRR0 |=AHBPeriph;                    /*AHB peripheral not held in Reset*/
  else
  SCU->PRR0 &=~AHBPeriph;                   /*AHB peripheral held in Reset*/
}

/*******************************************************************************
* Function Name  : SCU_APBPeriphIdleConfig
* Description    : Enable or Disable Periph Clock during Idle mode
* Input          : -APBPeriph: APB peripherals(__RTC, __ADC,...)
                   -NewState : ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_APBPeriphIdleConfig(u32 APBPeriph, FunctionalState NewState)
{
  if (NewState==ENABLE)
  SCU->MGR1 |=APBPeriph;      /*APB peripheral clock enabled during Idle mode*/
  else
  SCU->MGR1 &=~APBPeriph;     /*APB peripheral clock disabled during Idle mode*/
}

/*******************************************************************************
* Function Name  : SCU_AHBPeriphIdleConfig
* Description    : Enable or Disable Periph Clock during Idle mode
* Input          : -AHBPeriph: AHB peripherals(__USB, __DMA,...)
                   -NewState : ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_AHBPeriphIdleConfig(u32 AHBPeriph, FunctionalState NewState)
{
  if (NewState==ENABLE)
  SCU->MGR0 |=AHBPeriph;      /*AHB peripheral clock enabled during Idle mode*/
  else
  SCU->MGR0 &=~AHBPeriph;     /*AHB peripheral clock disabled during Idle mode*/
}

/*******************************************************************************
* Function Name  : SCU_APBPeriphDebugConfig
* Description    : Enable or Disable Periph Clock during ARM debug state
* Input          : -APBPeriph: APB peripherals(__RTC, __ADC,...)
                   -NewState : ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_APBPeriphDebugConfig(u32 APBPeriph, FunctionalState NewState)
{
  if (NewState==ENABLE)
  SCU->PECGR1 |=APBPeriph;    /*APB peripheral clock enabled during ARM debug state*/
  else
  SCU->PECGR1 &=~APBPeriph;   /*APB peripheral clock disabled during ARM debug state*/
}

/*******************************************************************************
* Function Name  : SCU_AHBPeriphDebugConfig
* Description    : Enable or Disable Periph Clock during ARM debug state
* Input          : -AHBPeriph: AHB peripherals(__USB, __DMA,...)
                   -NewState : ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_AHBPeriphDebugConfig(u32 AHBPeriph, FunctionalState NewState)
{
  if (NewState==ENABLE)
  SCU->PECGR0 |=AHBPeriph;    /*AHB peripheral clock enabled during ARM debug state*/
  else
  SCU->PECGR0 &=~AHBPeriph;   /*AHB peripheral clock disabled during ARM debug state*/
}
/*******************************************************************************
* Function Name  : SCU_BRCLKDivisorConfig
* Description    : Sets the BRCLK divisor value
* Input          : BRCLK_Divisor
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_BRCLKDivisorConfig(u32 BRCLK_Divisor)
{
  SCU->CLKCNTR &=SCU_BRCLK_Div1;              /*Clear BRSEL bit*/
  if (BRCLK_Divisor!=SCU_BRCLK_Div1)
  SCU->CLKCNTR |= SCU_BRCLK_Div2;             /*set bit BRSEL*/
}

/*******************************************************************************
* Function Name  : SCU_TIMCLKSourceConfig
* Description    : Sets the TIMx clock source
* Input          : - TIMx : SCU_TIM01 or SCU_TIM23
*                  - TIMCLK_Source = SCU_TIMCLK_EXT or SCU_TIMCLK_INT
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_TIMCLKSourceConfig(u8 TIMx, u32 TIMCLK_Source)
{
  if (TIMx== SCU_TIM01)                     /*TIM01 clock source configuration*/
  {
    SCU->CLKCNTR &=0xFFFFDFFF;
    if (TIMCLK_Source == SCU_TIMCLK_EXT)
    SCU->CLKCNTR |=0x2000;
  }
  else
  {
    SCU->CLKCNTR &=0xFFFFBFFF;            /*TIM23 clock source configuration*/
    if (TIMCLK_Source == SCU_TIMCLK_EXT)
    SCU->CLKCNTR |=0x4000;
  }
}

/*******************************************************************************
* Function Name  : SCU_TIMPresConfig
* Description    : Sets the TIMx Prescaler Value
* Input          : - TIMx : SCU_TIM01 or SCU_TIM23
*                  - Prescaler (16 bit value)
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_TIMPresConfig(u8 TIMx, u16 Prescaler)
{
  if (TIMx==SCU_TIM01)                     /*TIM01 Prescaler configuration*/
  SCU->SCR1 = Prescaler&0xFFFF;
  else
  SCU->SCR2 = Prescaler&0xFFFF;            /*TIM23 Prescaler configuration*/
}

/*******************************************************************************
* Function Name  : SCU_USBCLKConfig
* Description    : Configures the clock source for the 48MHz USBCLK
* Input          : USBCLK_Source: SCU_USBCLK_MCLK,SCU_USBCLK_MCLK2 or SCU_USBCLK_EXT
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_USBCLKConfig(u32 USBCLK_Source)
{
  SCU->CLKCNTR &=SCU_USBCLK_MCLK;            /*clear USBSEL[1:0] field*/
  if (USBCLK_Source!=SCU_USBCLK_MCLK)
  SCU->CLKCNTR |= USBCLK_Source;             /*update field with USBCLK_Source*/
}

/*******************************************************************************
* Function Name  : SCU_PHYCLKConfig
* Description    : Enable or Disable PHY clock output
* Input          : NewState : ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_PHYCLKConfig(FunctionalState NewState)
{
  if (NewState==ENABLE)
  SCU->CLKCNTR |= 0x1000;                    /*enable MIIPHY clock*/
  else
  SCU->CLKCNTR &=~0x1000;                    /*disable MIIPHY clock*/
}

/*******************************************************************************
* Function Name  : SCU_FMICLKDivisorConfig
* Description    : Set the FMI clock divisor
* Input          : FMICLK_Divisor: SCU_FMICLK_Div1 or SCU_FMICLK_DIV2
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_FMICLKDivisorConfig(u32 FMICLK_Divisor)
{
  SCU->CLKCNTR &=SCU_FMICLK_Div1;            /*FMICLK = RCLK*/
  if (FMICLK_Divisor!=SCU_FMICLK_Div1)
  SCU->CLKCNTR |=SCU_FMICLK_Div2;            /*FMICLK = RCLK/2 */
}

/*******************************************************************************
* Function Name  : SCU_EMIBCLKDivisorConfig
* Description    : Set the EMI Bus clock divisor: EMIBCLK = HCLK or HCLK/2
* Input          : SCU_EMICLK: SCU_EMIBCLK_Div1 , SCU_EMIBCLK_Div2
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_EMIBCLKDivisorConfig(u32 SCU_EMIBCLK)
{
  SCU->CLKCNTR &=SCU_EMIBCLK_Div1;          /*EMIBCLK = HCLK */
  if (SCU_EMIBCLK!=SCU_EMIBCLK_Div1)
  SCU->CLKCNTR |= SCU_EMIBCLK_Div2;         /*EMIBCLK = HCLK/2 */
}

/*******************************************************************************
* Function Name  : SCU_EMIModeConfig
* Description    : Configure the EMI as Multiplexed or Demultiplexed
* Input          : SCU_EMIMODE : SCU_EMI_MUX or SCU_EMI_DEMUX
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_EMIModeConfig(u32 SCU_EMIMODE)
{
  SCU->SCR0 &=SCU_EMI_MUX;                 /*EMI mode = Multiplexed*/
  if (SCU_EMIMODE!=SCU_EMI_MUX)
  SCU->SCR0 |= SCU_EMI_DEMUX;                /*EMI mode = Demultiplexed*/
}

/*******************************************************************************
* Function Name  : SCU_EMIALEConfig
* Description    : Configure the ALE signal (length & polarity)
* Input          : -SCU_EMIALE_LEN : SCU_EMIALE_LEN1 or SCU_EMIALE_LEN2
*                  -SCU_EMIALE_POL : SCU_EMIALE_POLLow or SCU_EMI_POLHigh
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_EMIALEConfig(u32 SCU_EMIALE_LEN, u32 SCU_EMIALE_POL)
{
  /*Configure EMI ALE Length*/
  SCU->SCR0 &=SCU_EMIALE_LEN1;
  if (SCU_EMIALE_LEN!=SCU_EMIALE_LEN1)
  SCU->SCR0 |= SCU_EMIALE_LEN2;

  /*Configure EMI ALE POL*/
  SCU->SCR0 &=SCU_EMIALE_POLLow;
  if (SCU_EMIALE_POL!=SCU_EMIALE_POLLow)
  SCU->SCR0 |= SCU_EMIALE_POLHigh;
}

/*******************************************************************************
* Function Name  : SCU_ITConfig
* Description    : ENBALE or DISABLE an SCU interrupt
* Input          : -SCU_IT:   interrupt mask
*                  -NewState: ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_ITConfig(u32 SCU_IT, FunctionalState NewState)
{
  if (NewState==ENABLE)
  SCU->ITCMSK&=~SCU_IT;                    /*IT enable */
  else
  SCU->ITCMSK|=SCU_IT;                     /*IT disable( mask)*/
}

/*******************************************************************************
* Function Name  : SCU_GetFlagStatus
* Description    : Returns flag status
* Input          : SCU_Flag
* Output         : NONE
* Return         : SET or RESET
*******************************************************************************/
FlagStatus SCU_GetFlagStatus(u32 SCU_Flag)
{
  if (SCU->SYSSTATUS&SCU_Flag)
  return SET;
  else return RESET;
}

/*******************************************************************************
* Function Name  : SCU_ClearFlag
* Description    : Clears a SYSTATUS Flag
* Input          : SCU_Flag
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_ClearFlag(u32 SCU_Flag)
{
  SCU->SYSSTATUS = SCU_Flag;
}
/*******************************************************************************
* Function Name  : SCU_GetPLLfreqValue
* Description    : Gets the current PLL frequency
* Input          : None
* Output         : None
* Return         : PLL frequency (KHz)
*******************************************************************************/
u32 SCU_GetPLLFreqValue(void)
{
  u8 PLL_M;
  u8 PLL_N;
  u8 PLL_P;

  PLL_M = SCU->PLLCONF&0xFF;
  PLL_N = (SCU->PLLCONF&0xFF00)>>8;
  PLL_P = (SCU->PLLCONF&0x70000)>>16;

  if ((PLL_M>0)&&(PLL_N>0))
  return (u32)(((_Main_Crystal*2)*PLL_N)/(PLL_M<<PLL_P));

  else return 0;
}
/*******************************************************************************
* Function Name  : SCU_GetMCLKFreqValue
* Description    : Gets the current MCLK frequency
* Input          : None
* Output         : None
* Return         : MCLK frequency (KHz)
*******************************************************************************/
u32 SCU_GetMCLKFreqValue(void)
{
  if ((SCU->CLKCNTR&0x3) == 0x2) return (u32)(_Main_Crystal);
  if ((SCU->CLKCNTR&0x3) == 0x1) return (u32)(32);
  else return (SCU_GetPLLFreqValue());
}

/*******************************************************************************
* Function Name  : SCU_GetRCLKFreqValue
* Description    : Gets the current RCLK frequency
* Input          : None
* Output         : None
* Return         : RCLK frequency (KHz)
*******************************************************************************/
u32 SCU_GetRCLKFreqValue(void)
{
  u8 RCLK_Div;
  RCLK_Div = (SCU->CLKCNTR&0x1C)>>2;
  if (RCLK_Div==0x5) RCLK_Div=10;
  return (u32)(SCU_GetMCLKFreqValue() >>RCLK_Div);
}

/*******************************************************************************
* Function Name  : SCU_GetHCLKFreqValue
* Description    : Gets the current PCLK frequency
* Input          : None
* Output         : None
* Return         : HCLK frequency (KHz)
*******************************************************************************/
u32 SCU_GetHCLKFreqValue(void)
{
  u8 HCLK_Div;
  HCLK_Div = (SCU->CLKCNTR&0x60)>>5;
  return (u32)(SCU_GetRCLKFreqValue() >>HCLK_Div);
}

/*******************************************************************************
* Function Name  : SCU_GetPCLKFreqValue
* Description    : Gets the current HCLK frequency
* Input          : None
* Output         : None
* Return         : PCLK frequency (KHz)
*******************************************************************************/
u32 SCU_GetPCLKFreqValue(void)
{
  u8 PCLK_Div;
  PCLK_Div = (SCU->CLKCNTR&0x180)>>7;
  return (u32)(SCU_GetRCLKFreqValue() >>PCLK_Div);
}

/*******************************************************************************
* Function Name  : SCU_WakeUpLineConfig
* Description    : Configures an External interrupt as WakeUp line
* Input          : EXTint : 0 -> 31
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_WakeUpLineConfig(u8 EXTint)
{
  if (EXTint < 8)
  {
    SCU->WKUPSEL&=~0x7;
    SCU->WKUPSEL|=EXTint;
  }
  else if (EXTint<16)
  {
    SCU->WKUPSEL&=~0x38;
    SCU->WKUPSEL|=(EXTint-8)<<3;
  }
  else if (EXTint<24)
  {
    SCU->WKUPSEL&=~0x1C0;
    SCU->WKUPSEL|=(EXTint-16)<<6;
  }
  else
  {
    SCU->WKUPSEL&=~0xE00;
    SCU->WKUPSEL|=(EXTint-24)<<9;
  }
}

/*******************************************************************************
* Function Name  : SCU_SpecIntRunModeConfig
* Description    : Enables or Disables the Special Run mode
* Input          : newstate = ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_SpecIntRunModeConfig(FunctionalState NewState)
{
  if (NewState == ENABLE)
  SCU->PWRMNG |=0x8;
  else
  SCU->PWRMNG &=~0x8;
}
/*******************************************************************************
* Function Name  : SCU_EnterIdleMode
* Description    : Enters in Idle mode
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_EnterIdleMode(void)
{
  SCU->PWRMNG |=0x1;
}
/*******************************************************************************
* Function Name  : SCU_EnterSleepMode
* Description    : Enters in Sleep mode
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_EnterSleepMode(void)
{
  SCU->PWRMNG |=0x2;
}

/*******************************************************************************
* Function Name  : SCU_UARTIrDAConfig
* Description    : Enable or Disable the Irda mode for UARTx
* Input          : - UARTx :x=0,1 or 2
*                  - UART_IrDA_Mode : SCU_UARTMode_IrDA or SCU_UARTMode_UART
* Output         :  None
* Return         :  None
*******************************************************************************/
void SCU_UARTIrDASelect(UART_TypeDef * UARTx, u8 UART_IrDA_Mode)
{
  if (UART_IrDA_Mode == SCU_UARTMode_IrDA)
  {
    if (UARTx== UART0) SCU->SCR0 |=0x400;
    else if (UARTx==UART1) SCU->SCR0 |=0x800;
    else SCU->SCR0 |=0x1000;
  }
  else
  {
    if (UARTx== UART0) SCU->SCR0 &=~0x400;
    else if (UARTx==UART1) SCU->SCR0 &=~0x800;
    else SCU->SCR0 &=~0x1000;
  }
}
/*******************************************************************************
* Function Name  : SCU_PFQBCCmd
* Description    : Enable or Disable PFQBC
* Input          : NewState : ENABLE or DISABLE
* Output         : None
* Return         : None
*******************************************************************************/
void SCU_PFQBCCmd(FunctionalState NewState)
{
  if (NewState==ENABLE)
  SCU->SCR0 |=0x1;
  else SCU->SCR0 &=~0x1;
}

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
