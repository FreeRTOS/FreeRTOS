/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_vic.c
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : This file provides all the VIC software functions.
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


/* Standard include ----------------------------------------------------------*/
#include "91x_vic.h"

/* Include of other module interface headers ---------------------------------*/
/* Local includes ------------------------------------------------------------*/
/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/

#define VIC_REGISTER_NUMBER              16
#define VIC_PROTECTION_ENABLE_MASK       0x1
#define VIC_PROTECTION_DISABLE_MASK      0xFFFFFFFE
#define VIC_VECTOR_ENABLE_MASK           0x20
#define VIC_IT_SOURCE_MASK               0xFFFFFFE0
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/

static void VIC_ITModeConfig(u16 VIC_Source, VIC_ITLineMode VIC_LineMode);
static void VIC_ISRVectAddConfig(u16 VIC_Source, u16 VIC_Priority, \
                                 void (*VIC_VectAddress)(void));
static void VIC_VectEnableConfig(u16 VIC_Source, u16 VIC_Priority);
static void VIC_ITSourceConfig(u16 VIC_Source, u16 VIC_Priority);

/* Interface functions -------------------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : VIC_DeInit
* Description    : Deinitialize the VIC module registers to their default reset
*                  values.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void VIC_DeInit(void)
{
  SCU_AHBPeriphReset(__VIC, ENABLE);     /* VIC peripheral is under Reset */
  SCU_AHBPeriphReset(__VIC, DISABLE);    /* VIC peripheral Reset off */
}

/*******************************************************************************
* Function Name  : VIC_GetIRQStatus
* Description    : Get the status of interrupts after IRQ masking.
* Input          : VIC_Source: specifies the number of the source line.
*                  This parameter can be one of the following values:
*                     - WDG_ITLine   : VIC source 0
*                     - SW_ITLine    : VIC source 1
*                     - ARMRX_ITLine : VIC source 2
*                     - ARMTX_ITLine : VIC source 3
*                     - TIM0_ITLine  : VIC source 4
*                     - TIM1_ITLine  : VIC source 5
*                     - TIM2_ITLine  : VIC source 6
*                     - TIM3_ITLine  : VIC source 7
*                     - USBHP_ITLine : VIC source 8
*                     - USBLP_ITLine : VIC source 9
*                     - SCU_ITLine   : VIC source 10
*                     - ENET_ITLine : VIC source 11
*                     - DMA_ITLine   : VIC source 12
*                     - CAN_ITLine   : VIC source 13
*                     - MC_ITLine    : VIC source 14
*                     - ADC_ITLine   : VIC source 15
*                     - UART0_ITLine : VIC source 16
*                     - UART1_ITLine : VIC source 17
*                     - UART2_ITLine : VIC source 18
*                     - I2C0_ITLine  : VIC source 19
*                     - I2C1_ITLine  : VIC source 20
*                     - SSP0_ITLine  : VIC source 21
*                     - SSP1_ITLine  : VIC source 22
*                     - LVD_ITLine   : VIC source 23
*                     - RTC_ITLine   : VIC source 24
*                     - WIU_ITLine   : VIC source 25
*                     - EXTIT0_ITLine: VIC source 26
*                     - EXTIT1_ITLine: VIC source 27
*                     - EXTIT2_ITLine: VIC source 28
*                     - EXTIT3_ITLine: VIC source 29
*                     - USBWU_ITLine : VIC source 30
*                     - PFQBC_ITLine : VIC source 31
* Output         : None
* Return         : The status of the IRQ interrupt after masking (SET or RESET).
*******************************************************************************/
FlagStatus VIC_GetIRQStatus(u16 VIC_Source)
{
  u32 VIC_Mask = 1;
  if (VIC_Source < VIC_REGISTER_NUMBER)
  {
    if ((VIC0->ISR | VIC_Mask << VIC_Source) != RESET)
      return SET;
    else
      return RESET;
  }
  else
  {
    if ((VIC1->ISR | VIC_Mask << (VIC_Source - VIC_REGISTER_NUMBER)) != RESET)
      return SET;
    else
      return RESET;
  }
}

/*******************************************************************************
* Function Name  : VIC_GetFIQStatus
* Description    : Get the status of interrupts after FIQ masking
* Input          : VIC_Source: specifies the number of the source line.
*                  This parameter can be one of the following values:
*                     - WDG_ITLine   : VIC source 0
*                     - SW_ITLine    : VIC source 1
*                     - ARMRX_ITLine : VIC source 2
*                     - ARMTX_ITLine : VIC source 3
*                     - TIM0_ITLine  : VIC source 4
*                     - TIM1_ITLine  : VIC source 5
*                     - TIM2_ITLine  : VIC source 6
*                     - TIM3_ITLine  : VIC source 7
*                     - USBHP_ITLine : VIC source 8
*                     - USBLP_ITLine : VIC source 9
*                     - SCU_ITLine   : VIC source 10
*                     - ENET_ITLine : VIC source 11
*                     - DMA_ITLine   : VIC source 12
*                     - CAN_ITLine   : VIC source 13
*                     - MC_ITLine    : VIC source 14
*                     - ADC_ITLine   : VIC source 15
*                     - UART0_ITLine : VIC source 16
*                     - UART1_ITLine : VIC source 17
*                     - UART2_ITLine : VIC source 18
*                     - I2C0_ITLine  : VIC source 19
*                     - I2C1_ITLine  : VIC source 20
*                     - SSP0_ITLine  : VIC source 21
*                     - SSP1_ITLine  : VIC source 22
*                     - LVD_ITLine   : VIC source 23
*                     - RTC_ITLine   : VIC source 24
*                     - WIU_ITLine   : VIC source 25
*                     - EXTIT0_ITLine: VIC source 26
*                     - EXTIT1_ITLine: VIC source 27
*                     - EXTIT2_ITLine: VIC source 28
*                     - EXTIT3_ITLine: VIC source 29
*                     - USBWU_ITLine : VIC source 30
*                     - PFQBC_ITLine : VIC source 31
* Output         : None
* Return         : The status of the FIQ interrupt after masking (SET or RESET)
*******************************************************************************/
FlagStatus VIC_GetFIQStatus(u16 VIC_Source)
{
  u32 VIC_Mask = 1;
  if (VIC_Source < VIC_REGISTER_NUMBER)
  {
    if ((VIC0->RINTSR | VIC_Mask << VIC_Source) != RESET)
      return SET;
    else
      return RESET;
  }
  else
  {
    if ((VIC1->RINTSR | VIC_Mask << (VIC_Source - VIC_REGISTER_NUMBER)) != RESET)
      return SET;
    else
      return RESET;
  }
}

/*******************************************************************************
* Function Name  : VIC_GetSourceITStatus
* Description    : Get the status of the source interrupts before masking.
* Input          : VIC_Source: specifies the number of the source line.
*                  This parameter can be one of the following values:
*                     - WDG_ITLine   : VIC source 0
*                     - SW_ITLine    : VIC source 1
*                     - ARMRX_ITLine : VIC source 2
*                     - ARMTX_ITLine : VIC source 3
*                     - TIM0_ITLine  : VIC source 4
*                     - TIM1_ITLine  : VIC source 5
*                     - TIM2_ITLine  : VIC source 6
*                     - TIM3_ITLine  : VIC source 7
*                     - USBHP_ITLine : VIC source 8
*                     - USBLP_ITLine : VIC source 9
*                     - SCU_ITLine   : VIC source 10
*                     - ENET_ITLine : VIC source 11
*                     - DMA_ITLine   : VIC source 12
*                     - CAN_ITLine   : VIC source 13
*                     - MC_ITLine    : VIC source 14
*                     - ADC_ITLine   : VIC source 15
*                     - UART0_ITLine : VIC source 16
*                     - UART1_ITLine : VIC source 17
*                     - UART2_ITLine : VIC source 18
*                     - I2C0_ITLine  : VIC source 19
*                     - I2C1_ITLine  : VIC source 20
*                     - SSP0_ITLine  : VIC source 21
*                     - SSP1_ITLine  : VIC source 22
*                     - LVD_ITLine   : VIC source 23
*                     - RTC_ITLine   : VIC source 24
*                     - WIU_ITLine   : VIC source 25
*                     - EXTIT0_ITLine: VIC source 26
*                     - EXTIT1_ITLine: VIC source 27
*                     - EXTIT2_ITLine: VIC source 28
*                     - EXTIT3_ITLine: VIC source 29
*                     - USBWU_ITLine : VIC source 30
*                     - PFQBC_ITLine : VIC source 31
* Output         : None
* Return         : The status of the source interrupt before masking
*******************************************************************************/
FlagStatus VIC_GetSourceITStatus(u16 VIC_Source)
{
  u32 VIC_Mask = 1;
  if (VIC_Source < VIC_REGISTER_NUMBER)
  {
    if ((VIC0->FSR | VIC_Mask << VIC_Source) != RESET)
      return SET;
    else
      return RESET;
  }
  else
  {
    if ((VIC1->FSR | VIC_Mask << (VIC_Source - VIC_REGISTER_NUMBER)) != RESET)
      return SET;
    else
      return RESET;
  }
}

/*******************************************************************************
* Function Name  : VIC_ITModeConfig
* Description    : Select the type of interrupt (IRQ or FIQ)
* Input1         : VIC_Source: specifies the number of the source line.
*                  This parameter can be one of the following values:
*                     - WDG_ITLine   : VIC source 0
*                     - SW_ITLine    : VIC source 1
*                     - ARMRX_ITLine : VIC source 2
*                     - ARMTX_ITLine : VIC source 3
*                     - TIM0_ITLine  : VIC source 4
*                     - TIM1_ITLine  : VIC source 5
*                     - TIM2_ITLine  : VIC source 6
*                     - TIM3_ITLine  : VIC source 7
*                     - USBHP_ITLine : VIC source 8
*                     - USBLP_ITLine : VIC source 9
*                     - SCU_ITLine   : VIC source 10
*                     - ENET_ITLine : VIC source 11
*                     - DMA_ITLine   : VIC source 12
*                     - CAN_ITLine   : VIC source 13
*                     - MC_ITLine    : VIC source 14
*                     - ADC_ITLine   : VIC source 15
*                     - UART0_ITLine : VIC source 16
*                     - UART1_ITLine : VIC source 17
*                     - UART2_ITLine : VIC source 18
*                     - I2C0_ITLine  : VIC source 19
*                     - I2C1_ITLine  : VIC source 20
*                     - SSP0_ITLine  : VIC source 21
*                     - SSP1_ITLine  : VIC source 22
*                     - LVD_ITLine   : VIC source 23
*                     - RTC_ITLine   : VIC source 24
*                     - WIU_ITLine   : VIC source 25
*                     - EXTIT0_ITLine: VIC source 26
*                     - EXTIT1_ITLine: VIC source 27
*                     - EXTIT2_ITLine: VIC source 28
*                     - EXTIT3_ITLine: VIC source 29
*                     - USBWU_ITLine : VIC source 30
*                     - PFQBC_ITLine : VIC source 31
* Input2         : VIC_LineMode :specifies the type of interrupt of the source
*                  line. This parameter can be one of the following values:
*                     - VIC_IRQ: the correspondent line is configured as IRQ.
*                     - VIC_FIQ: the correspondent line is configured as FIQ.
* Output         : None
* Return         : None
*******************************************************************************/
static void VIC_ITModeConfig(u16 VIC_Source, VIC_ITLineMode VIC_LineMode)
{
  u32 VIC_Mask = 1;

  if (VIC_Source < VIC_REGISTER_NUMBER) /* VIC0 */
  {
    if (VIC_LineMode == VIC_IRQ)
      VIC0->INTSR &= ~(VIC_Mask << VIC_Source);
    else /* VIC_LineMode == VIC_FIQ */
      VIC0->INTSR |= (VIC_Mask << VIC_Source);
  }
  else /* VIC1 */
  {
    if (VIC_LineMode == VIC_IRQ)
      VIC1->INTSR &= ~(VIC_Mask << (VIC_Source - VIC_REGISTER_NUMBER));
    else /* VIC_LineMode == VIC_FIQ */
      VIC1->INTSR |= (VIC_Mask << (VIC_Source - VIC_REGISTER_NUMBER));
  }
}

/*******************************************************************************
* Function Name  : VIC_ITCmd
* Description    : Enable or disable the interrupt request lines.
* Input1         : VIC_Source: specifies the number of the source line.
*                  This parameter can be one of the following values:
*                     - WDG_ITLine   : VIC source 0
*                     - SW_ITLine    : VIC source 1
*                     - ARMRX_ITLine : VIC source 2
*                     - ARMTX_ITLine : VIC source 3
*                     - TIM0_ITLine  : VIC source 4
*                     - TIM1_ITLine  : VIC source 5
*                     - TIM2_ITLine  : VIC source 6
*                     - TIM3_ITLine  : VIC source 7
*                     - USBHP_ITLine : VIC source 8
*                     - USBLP_ITLine : VIC source 9
*                     - SCU_ITLine   : VIC source 10
*                     - ENET_ITLine : VIC source 11
*                     - DMA_ITLine   : VIC source 12
*                     - CAN_ITLine   : VIC source 13
*                     - MC_ITLine    : VIC source 14
*                     - ADC_ITLine   : VIC source 15
*                     - UART0_ITLine : VIC source 16
*                     - UART1_ITLine : VIC source 17
*                     - UART2_ITLine : VIC source 18
*                     - I2C0_ITLine  : VIC source 19
*                     - I2C1_ITLine  : VIC source 20
*                     - SSP0_ITLine  : VIC source 21
*                     - SSP1_ITLine  : VIC source 22
*                     - LVD_ITLine   : VIC source 23
*                     - RTC_ITLine   : VIC source 24
*                     - WIU_ITLine   : VIC source 25
*                     - EXTIT0_ITLine: VIC source 26
*                     - EXTIT1_ITLine: VIC source 27
*                     - EXTIT2_ITLine: VIC source 28
*                     - EXTIT3_ITLine: VIC source 29
*                     - USBWU_ITLine : VIC source 30
*                     - PFQBC_ITLine : VIC source 31
* Input2         : FMI_NewState: specifies the line status.
*                  This parameter can be one of the following values:
*                     - ENABLE:  The line is enabled.
*                     - DISABLE: The line is disabled.
* Output         : None
* Return         : None
*******************************************************************************/
void VIC_ITCmd(u16 VIC_Source, FunctionalState VIC_NewState)
{
  u32 VIC_Mask = 1;

  if (VIC_NewState == ENABLE)
  {
    if (VIC_Source < VIC_REGISTER_NUMBER)  /* VIC0 */
      VIC0->INTER |= (VIC_Mask << VIC_Source);
    else /* VIC1 */
      VIC1->INTER |= (VIC_Mask << (VIC_Source - VIC_REGISTER_NUMBER));
  }
  else /* VIC_NewState == DISABLE */
  {
    if (VIC_Source < VIC_REGISTER_NUMBER)  /* VIC0 */
      VIC0->INTECR |= (VIC_Mask << VIC_Source);
    else /* VIC1 */
      VIC1->INTECR |= (VIC_Mask << (VIC_Source - VIC_REGISTER_NUMBER));
  }
}

/*******************************************************************************
* Function Name  : VIC_SWITCmd
* Description    : Generate a software interrupt for the specific source
*                  interrupt.
* Input1         : VIC_Source: specifies the number of the source line.
*                  This parameter can be one of the following values:
*                     - WDG_ITLine   : VIC source 0
*                     - SW_ITLine    : VIC source 1
*                     - ARMRX_ITLine : VIC source 2
*                     - ARMTX_ITLine : VIC source 3
*                     - TIM0_ITLine  : VIC source 4
*                     - TIM1_ITLine  : VIC source 5
*                     - TIM2_ITLine  : VIC source 6
*                     - TIM3_ITLine  : VIC source 7
*                     - USBHP_ITLine : VIC source 8
*                     - USBLP_ITLine : VIC source 9
*                     - SCU_ITLine   : VIC source 10
*                     - ENET_ITLine : VIC source 11
*                     - DMA_ITLine   : VIC source 12
*                     - CAN_ITLine   : VIC source 13
*                     - MC_ITLine    : VIC source 14
*                     - ADC_ITLine   : VIC source 15
*                     - UART0_ITLine : VIC source 16
*                     - UART1_ITLine : VIC source 17
*                     - UART2_ITLine : VIC source 18
*                     - I2C0_ITLine  : VIC source 19
*                     - I2C1_ITLine  : VIC source 20
*                     - SSP0_ITLine  : VIC source 21
*                     - SSP1_ITLine  : VIC source 22
*                     - LVD_ITLine   : VIC source 23
*                     - RTC_ITLine   : VIC source 24
*                     - WIU_ITLine   : VIC source 25
*                     - EXTIT0_ITLine: VIC source 26
*                     - EXTIT1_ITLine: VIC source 27
*                     - EXTIT2_ITLine: VIC source 28
*                     - EXTIT3_ITLine: VIC source 29
*                     - USBWU_ITLine : VIC source 30
*                     - PFQBC_ITLine : VIC source 31
* Input2         : FMI_NewState: specifies the software interrupt status.
*                  This parameter can be one of the following values:
*                     - ENABLE:  The software interrupt is enabled.
*                     - DISABLE: The software interrupt is disabled.
* Output         : None
* Return         : None
*******************************************************************************/
void VIC_SWITCmd(u16 VIC_Source, FunctionalState VIC_NewState)
{
  u32 VIC_Mask = 1;

  if (VIC_NewState == ENABLE)
  {
    if (VIC_Source < VIC_REGISTER_NUMBER)  /* VIC0 */
      VIC0->SWINTR |= (VIC_Mask << VIC_Source);
    else /* VIC1 */
      VIC1->SWINTR |= (VIC_Mask << (VIC_Source - VIC_REGISTER_NUMBER));
  }
  else /* VIC_NewState == DISABLE */
  {
    if (VIC_Source < VIC_REGISTER_NUMBER)  /* VIC0 */
      VIC0->SWINTCR = (VIC_Mask << VIC_Source);
    else /* VIC1 */
      VIC1->SWINTCR = (VIC_Mask << (VIC_Source - VIC_REGISTER_NUMBER));
  }
}

/*******************************************************************************
* Function Name  : VIC_ProtectionCmd
* Description    : Enable or Disable the register access protection.
* Input          : FMI_NewState: specifies the protection status.
*                  This parameter can be one of the following values:
*                     - ENABLE:  The protection is enabled.
*                     - DISABLE: The protection is disabled.
* Output         : None
* Return         : None
*******************************************************************************/
void VIC_ProtectionCmd(FunctionalState VIC_NewState)
{
  if (VIC_NewState == ENABLE)
  {
    VIC0->PER |= VIC_PROTECTION_ENABLE_MASK;
    VIC1->PER |= VIC_PROTECTION_ENABLE_MASK;
  }
  else
  {
    VIC0->PER &= VIC_PROTECTION_DISABLE_MASK;
    VIC1->PER &= VIC_PROTECTION_DISABLE_MASK;
  }
}

/*******************************************************************************
* Function Name  : VIC_GetCurrentISRAdd
* Description    : Get the address of the current active ISR.
* Input          : VICx: specifies the VIC peripheral
*                  This parameter can be one of the following values:
*                     - VIC0: To select VIC0.
*                     - VIC1: To select VIC1.
* Output         : None
* Return         : The Address of the active ISR.
*******************************************************************************/
u32 VIC_GetCurrentISRAdd(VIC_TypeDef* VICx)
{
  return VICx->VAR;
}

/*******************************************************************************
* Function Name  : VIC_ISRVectAddConfig
* Description    : Configuration of the ISR vector address.
* Input1         : VIC_Source: specifies the number of the source line.
*                  This parameter can be one of the following values:
*                     - WDG_ITLine   : VIC source 0
*                     - SW_ITLine    : VIC source 1
*                     - ARMRX_ITLine : VIC source 2
*                     - ARMTX_ITLine : VIC source 3
*                     - TIM0_ITLine  : VIC source 4
*                     - TIM1_ITLine  : VIC source 5
*                     - TIM2_ITLine  : VIC source 6
*                     - TIM3_ITLine  : VIC source 7
*                     - USBHP_ITLine : VIC source 8
*                     - USBLP_ITLine : VIC source 9
*                     - SCU_ITLine   : VIC source 10
*                     - ENET_ITLine : VIC source 11
*                     - DMA_ITLine   : VIC source 12
*                     - CAN_ITLine   : VIC source 13
*                     - MC_ITLine    : VIC source 14
*                     - ADC_ITLine   : VIC source 15
*                     - UART0_ITLine : VIC source 16
*                     - UART1_ITLine : VIC source 17
*                     - UART2_ITLine : VIC source 18
*                     - I2C0_ITLine  : VIC source 19
*                     - I2C1_ITLine  : VIC source 20
*                     - SSP0_ITLine  : VIC source 21
*                     - SSP1_ITLine  : VIC source 22
*                     - LVD_ITLine   : VIC source 23
*                     - RTC_ITLine   : VIC source 24
*                     - WIU_ITLine   : VIC source 25
*                     - EXTIT0_ITLine: VIC source 26
*                     - EXTIT1_ITLine: VIC source 27
*                     - EXTIT2_ITLine: VIC source 28
*                     - EXTIT3_ITLine: VIC source 29
*                     - USBWU_ITLine : VIC source 30
*                     - PFQBC_ITLine : VIC source 31
* Input2         : VIC_Priority: specifies the priority of the interrupt.
*                  It can be a value from 0 to 15. 0 is the highest priority.
* Input3         : void (*VIC_VectAddress)(void): specifies the ISR vector
*                  address pointer.
* Output         : None
* Return         : None
*******************************************************************************/
static void VIC_ISRVectAddConfig(u16 VIC_Source, u16 VIC_Priority, \
                          void (*VIC_VectAddress)(void))
{
  if (VIC_Source < VIC_REGISTER_NUMBER) /* VIC0 */
    VIC0->VAiR[VIC_Priority] = (u32)VIC_VectAddress;
  else /* VIC1 */
    VIC1->VAiR[VIC_Priority] = (u32)VIC_VectAddress;
}

/*******************************************************************************
* Function Name  : VIC_GetISRVectAdd
* Description    : Get the ISR vector address of the correspondent line.
* Input          : VIC_Source: specifies the number of the source line.
*                  This parameter can be one of the following values:
*                     - WDG_ITLine   : VIC source 0
*                     - SW_ITLine    : VIC source 1
*                     - ARMRX_ITLine : VIC source 2
*                     - ARMTX_ITLine : VIC source 3
*                     - TIM0_ITLine  : VIC source 4
*                     - TIM1_ITLine  : VIC source 5
*                     - TIM2_ITLine  : VIC source 6
*                     - TIM3_ITLine  : VIC source 7
*                     - USBHP_ITLine : VIC source 8
*                     - USBLP_ITLine : VIC source 9
*                     - SCU_ITLine   : VIC source 10
*                     - ENET_ITLine : VIC source 11
*                     - DMA_ITLine   : VIC source 12
*                     - CAN_ITLine   : VIC source 13
*                     - MC_ITLine    : VIC source 14
*                     - ADC_ITLine   : VIC source 15
*                     - UART0_ITLine : VIC source 16
*                     - UART1_ITLine : VIC source 17
*                     - UART2_ITLine : VIC source 18
*                     - I2C0_ITLine  : VIC source 19
*                     - I2C1_ITLine  : VIC source 20
*                     - SSP0_ITLine  : VIC source 21
*                     - SSP1_ITLine  : VIC source 22
*                     - LVD_ITLine   : VIC source 23
*                     - RTC_ITLine   : VIC source 24
*                     - WIU_ITLine   : VIC source 25
*                     - EXTIT0_ITLine: VIC source 26
*                     - EXTIT1_ITLine: VIC source 27
*                     - EXTIT2_ITLine: VIC source 28
*                     - EXTIT3_ITLine: VIC source 29
*                     - USBWU_ITLine : VIC source 30
*                     - PFQBC_ITLine : VIC source 31
* Output         : None
* Return         : The correspondent ISR vector address.
*******************************************************************************/
u32 VIC_GetISRVectAdd(u16 VIC_Source)
{
  if (VIC_Source < VIC_REGISTER_NUMBER) /* VIC0 */
    return VIC0->VAiR[VIC_Source];
  else /* VIC1 */
    return VIC1->VAiR[VIC_Source - VIC_REGISTER_NUMBER];
}

/*******************************************************************************
* Function Name  : VIC_VectEnableConfig
* Description    : Enable the vector interrupt.
* Input1         : VIC_Source: specifies the number of the source line.
*                  This parameter can be one of the following values:
*                     - WDG_ITLine   : VIC source 0
*                     - SW_ITLine    : VIC source 1
*                     - ARMRX_ITLine : VIC source 2
*                     - ARMTX_ITLine : VIC source 3
*                     - TIM0_ITLine  : VIC source 4
*                     - TIM1_ITLine  : VIC source 5
*                     - TIM2_ITLine  : VIC source 6
*                     - TIM3_ITLine  : VIC source 7
*                     - USBHP_ITLine : VIC source 8
*                     - USBLP_ITLine : VIC source 9
*                     - SCU_ITLine   : VIC source 10
*                     - ENET_ITLine : VIC source 11
*                     - DMA_ITLine   : VIC source 12
*                     - CAN_ITLine   : VIC source 13
*                     - MC_ITLine    : VIC source 14
*                     - ADC_ITLine   : VIC source 15
*                     - UART0_ITLine : VIC source 16
*                     - UART1_ITLine : VIC source 17
*                     - UART2_ITLine : VIC source 18
*                     - I2C0_ITLine  : VIC source 19
*                     - I2C1_ITLine  : VIC source 20
*                     - SSP0_ITLine  : VIC source 21
*                     - SSP1_ITLine  : VIC source 22
*                     - LVD_ITLine   : VIC source 23
*                     - RTC_ITLine   : VIC source 24
*                     - WIU_ITLine   : VIC source 25
*                     - EXTIT0_ITLine: VIC source 26
*                     - EXTIT1_ITLine: VIC source 27
*                     - EXTIT2_ITLine: VIC source 28
*                     - EXTIT3_ITLine: VIC source 29
*                     - USBWU_ITLine : VIC source 30
*                     - PFQBC_ITLine : VIC source 31
* Input2         : VIC_Priority: specifies the priority of the interrupt.
*                  It can be a value from 0 to 15. 0 is the highest priority.
* Output         : None
* Return         : None
*******************************************************************************/
static void VIC_VectEnableConfig(u16 VIC_Source, u16 VIC_Priority)
{
  if (VIC_Source < VIC_REGISTER_NUMBER) /* VIC0 */
    VIC0->VCiR[VIC_Priority] |= VIC_VECTOR_ENABLE_MASK;
  else /* VIC1 */
    VIC1->VCiR[VIC_Priority] |= VIC_VECTOR_ENABLE_MASK;
}

/*******************************************************************************
* Function Name  : VIC_ITSourceConfig
* Description    : Select the interrupt source.
* Input1         : VIC_Source: specifies the number of the source line.
*                  This parameter can be one of the following values:
*                     - WDG_ITLine   : VIC source 0
*                     - SW_ITLine    : VIC source 1
*                     - ARMRX_ITLine : VIC source 2
*                     - ARMTX_ITLine : VIC source 3
*                     - TIM0_ITLine  : VIC source 4
*                     - TIM1_ITLine  : VIC source 5
*                     - TIM2_ITLine  : VIC source 6
*                     - TIM3_ITLine  : VIC source 7
*                     - USBHP_ITLine : VIC source 8
*                     - USBLP_ITLine : VIC source 9
*                     - SCU_ITLine   : VIC source 10
*                     - ENET_ITLine : VIC source 11
*                     - DMA_ITLine   : VIC source 12
*                     - CAN_ITLine   : VIC source 13
*                     - MC_ITLine    : VIC source 14
*                     - ADC_ITLine   : VIC source 15
*                     - UART0_ITLine : VIC source 16
*                     - UART1_ITLine : VIC source 17
*                     - UART2_ITLine : VIC source 18
*                     - I2C0_ITLine  : VIC source 19
*                     - I2C1_ITLine  : VIC source 20
*                     - SSP0_ITLine  : VIC source 21
*                     - SSP1_ITLine  : VIC source 22
*                     - LVD_ITLine   : VIC source 23
*                     - RTC_ITLine   : VIC source 24
*                     - WIU_ITLine   : VIC source 25
*                     - EXTIT0_ITLine: VIC source 26
*                     - EXTIT1_ITLine: VIC source 27
*                     - EXTIT2_ITLine: VIC source 28
*                     - EXTIT3_ITLine: VIC source 29
*                     - USBWU_ITLine : VIC source 30
*                     - PFQBC_ITLine : VIC source 31
* Input2         : VIC_Priority: specifies the priority of the interrupt.
*                  It can be a value from 0 to 15. 0 is the highest priority.
* Output         : None
* Return         : None
*******************************************************************************/
static void VIC_ITSourceConfig(u16 VIC_Source, u16 VIC_Priority)
{
  if (VIC_Source < VIC_REGISTER_NUMBER) /* VIC0 */
  {
    VIC0->VCiR[VIC_Priority] &= VIC_IT_SOURCE_MASK;
    VIC0->VCiR[VIC_Priority] |= VIC_Source;
  }
  else /* VIC1 */
  {
    VIC1->VCiR[VIC_Priority] &= VIC_IT_SOURCE_MASK;
    VIC1->VCiR[VIC_Priority] |= VIC_Source - VIC_REGISTER_NUMBER;
  }
}

/*******************************************************************************
* Function Name  : VIC_Config
* Description    : Configure the ISR, the line, the mode and the priority for
*                  each interrupt source line.
* Input1         : VIC_Source: specifies the number of the source line.
*                  This parameter can be one of the following values:
*                     - WDG_ITLine   : VIC source 0
*                     - SW_ITLine    : VIC source 1
*                     - ARMRX_ITLine : VIC source 2
*                     - ARMTX_ITLine : VIC source 3
*                     - TIM0_ITLine  : VIC source 4
*                     - TIM1_ITLine  : VIC source 5
*                     - TIM2_ITLine  : VIC source 6
*                     - TIM3_ITLine  : VIC source 7
*                     - USBHP_ITLine : VIC source 8
*                     - USBLP_ITLine : VIC source 9
*                     - SCU_ITLine   : VIC source 10
*                     - ENET_ITLine : VIC source 11
*                     - DMA_ITLine   : VIC source 12
*                     - CAN_ITLine   : VIC source 13
*                     - MC_ITLine    : VIC source 14
*                     - ADC_ITLine   : VIC source 15
*                     - UART0_ITLine : VIC source 16
*                     - UART1_ITLine : VIC source 17
*                     - UART2_ITLine : VIC source 18
*                     - I2C0_ITLine  : VIC source 19
*                     - I2C1_ITLine  : VIC source 20
*                     - SSP0_ITLine  : VIC source 21
*                     - SSP1_ITLine  : VIC source 22
*                     - LVD_ITLine   : VIC source 23
*                     - RTC_ITLine   : VIC source 24
*                     - WIU_ITLine   : VIC source 25
*                     - EXTIT0_ITLine: VIC source 26
*                     - EXTIT1_ITLine: VIC source 27
*                     - EXTIT2_ITLine: VIC source 28
*                     - EXTIT3_ITLine: VIC source 29
*                     - USBWU_ITLine : VIC source 30
*                     - PFQBC_ITLine : VIC source 31
* Input2         : VIC_LineMode :specifies the type of interrupt of the source
*                  line. This parameter can be one of the following values:
*                     - VIC_IRQ: the correspondent line is configured as IRQ.
*                     - VIC_FIQ: the correspondent line is configured as FIQ.
* Input3         : VIC_Priority: specifies the priority of the interrupt.
*                  It can be a value from 0 to 15. 0 is the highest priority.
* Output         : None
* Return         : None
*******************************************************************************/
void VIC_Config(u16 VIC_Source, VIC_ITLineMode VIC_LineMode, u8 VIC_Priority)
{
  switch (VIC_Source)
  {
    case 0:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, WDG_IRQHandler);
             break;

    case 1:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, SW_IRQHandler);
             break;

    case 2:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, ARMRX_IRQHandler);
             break;

    case 3:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, ARMTX_IRQHandler);
             break;

    case 4:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, TIM0_IRQHandler);
             break;

    case 5:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, TIM1_IRQHandler);
             break;

    case 6:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, TIM2_IRQHandler);
             break;

    case 7:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, TIM3_IRQHandler);
             break;

    case 8:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, USBHP_IRQHandler);
             break;

    case 9:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, USBLP_IRQHandler);
             break;

    case 10:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, SCU_IRQHandler);
              break;

    case 11:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, ENET_IRQHandler);
              break;

    case 12:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, DMA_IRQHandler);
              break;

    case 13:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, CAN_IRQHandler);
              break;

    case 14:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, MC_IRQHandler);
              break;

    case 15:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, ADC_IRQHandler);
              break;

    case 16:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, UART0_IRQHandler);
              break;

    case 17:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, UART1_IRQHandler);
              break;

    case 18:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, UART2_IRQHandler);
              break;

    case 19:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, I2C0_IRQHandler);
              break;

    case 20:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, I2C1_IRQHandler);
              break;

    case 21:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, SSP0_IRQHandler);
              break;

    case 22:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, SSP1_IRQHandler);
              break;

    case 23:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, LVD_IRQHandler);
              break;

    case 24:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, RTC_IRQHandler);
              break;

    case 25:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, WIU_IRQHandler);
              break;

    case 26:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, EXTIT0_IRQHandler);
              break;

    case 27:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, EXTIT1_IRQHandler);
              break;

    case 28:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, EXTIT2_IRQHandler);
              break;

    case 29:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, EXTIT3_IRQHandler);
              break;

    case 30:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, USBWU_IRQHandler);
              break;

    case 31:  VIC_ISRVectAddConfig(VIC_Source, VIC_Priority, PFQBC_IRQHandler);
              break;

    default:  break;
  }
  VIC_ITModeConfig(VIC_Source, VIC_LineMode);
  VIC_VectEnableConfig(VIC_Source, VIC_Priority);
  VIC_ITSourceConfig(VIC_Source, VIC_Priority);
}

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
