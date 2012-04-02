/******************** (C) COPYRIGHT 2007 STMicroelectronics ********************
* File Name          : stm32f10x_tim.c
* Author             : MCD Application Team
* Date First Issued  : 09/29/2006
* Description        : This file provides all the TIM firmware functions.
********************************************************************************
* History:
* 04/02/2007: V0.2
* 02/05/2007: V0.1
* 09/29/2006: V0.01
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Includes ------------------------------------------------------------------*/
#include "stm32f10x_tim.h"
#include "stm32f10x_rcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* ---------------------- TIM registers bit mask ------------------------ */
#define CR1_CEN_Set                 ((u16)0x0001)
#define CR1_CEN_Reset               ((u16)0x03FE)
#define CR1_UDIS_Set                ((u16)0x0002)
#define CR1_UDIS_Reset              ((u16)0x03FD)
#define CR1_URS_Set                 ((u16)0x0004)
#define CR1_URS_Reset               ((u16)0x03FB)
#define CR1_OPM_Mask                ((u16)0x03F7)
#define CR1_CounterMode_Mask        ((u16)0x039F)
#define CR1_ARPE_Set                ((u16)0x0080)
#define CR1_ARPE_Reset              ((u16)0x037F)
#define CR1_CKD_Mask                ((u16)0x00FF)

#define CR2_CCDS_Set                ((u16)0x0008)
#define CR2_CCDS_Reset              ((u16)0x0007)
#define CR2_MMS_Mask                ((u16)0x0080)
#define CR2_TI1S_Set                ((u16)0x0080)
#define CR2_TI1S_Reset              ((u16)0xFF70)

#define SMCR_SMS_Mask               ((u16)0xFFF0)
#define SMCR_ETR_Mask               ((u16)0x00F7)
#define SMCR_TS_Mask                ((u16)0xFF87)
#define SMCR_MSM_Mask               ((u16)0xFF77)
#define SMCR_ECE_Set                ((u16)0x4000)

#define CCMR_CC13S_Mask             ((u16)0x7F7C)
#define CCMR_CC24S_Mask             ((u16)0x7C7F)
#define CCMR_TI13Direct_Set         ((u16)0x0001)
#define CCMR_TI24Direct_Set         ((u16)0x0100)
#define CCMR_OC13FE_Mask            ((u16)0x7F7B)
#define CCMR_OC24FE_Mask            ((u16)0x7B7F)
#define CCMR_OC13PE_Mask            ((u16)0x7F77)
#define CCMR_OC24PE_Mask            ((u16)0x777F)
#define CCMR_OCM13_Mask             ((u16)0x7F0F)
#define CCMR_OCM24_Mask             ((u16)0x0F7F)
#define CCMR_IC13PSC_Mask           ((u16)0xFFF3)
#define CCMR_IC24PSC_Mask           ((u16)0xF3FF)
#define CCMR_IC13F_Mask             ((u16)0xFF0F)
#define CCMR_IC24F_Mask             ((u16)0x0FFF)
#define CCER_CC1P_Mask              ((u16)0xFFFD)

#define CCER_CC2P_Mask              ((u16)0xFFDF)
#define CCER_CC3P_Mask              ((u16)0xFDFF)
#define CCER_CC4P_Mask              ((u16)0xDFFF)

#define CCRE_CC1E_Set               ((u16)0x0001)
#define CCRE_CC1E_Reset             ((u16)0xFFFE)
#define CCRE_CC1E_Mask              ((u16)0xFFFE)

#define CCRE_CC2E_Set               ((u16)0x0010)
#define CCRE_CC2E_Reset             ((u16)0xFFEF)
#define CCRE_CC2E_Mask              ((u16)0xFFEF)

#define CCRE_CC3E_Set               ((u16)0x0100)
#define CCRE_CC3E_Reset             ((u16)0xFEFF)

#define CCRE_CC4E_Set               ((u16)0x1000)
#define CCRE_CC4E_Reset             ((u16)0xEFFF)
#define CCRE_CC4E_Mask              ((u16)0xEFFF)

#define DCR_DMA_Mask                ((u16)0x0000)

/* TIM private Masks */
#define TIM_Period_Reset_Mask       ((u16)0x0000)
#define TIM_Prescaler_Reset_Mask    ((u16)0x0000)
#define TIM_Pulse_Reset_Mask        ((u16)0x0000)
#define TIM_ICFilter_Mask           ((u8)0x00)

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
static uc16 Tab_OCModeMask[4] = {0xFF00, 0x00FF, 0xFF00, 0x00FF};
static uc16 Tab_PolarityMask[4] = {CCER_CC1P_Mask, CCER_CC2P_Mask, CCER_CC3P_Mask, CCER_CC4P_Mask};

/* Private function prototypes -----------------------------------------------*/
static void PWMI_Config(TIM_TypeDef* TIMx, TIM_ICInitTypeDef* TIM_ICInitStruct);
static void TI1_Config(TIM_TypeDef* TIMx, u16 TIM_ICPolarity, u16 TIM_ICSelection,
                       u8 TIM_ICFilter);
static void TI2_Config(TIM_TypeDef* TIMx, u16 TIM_ICPolarity, u16 TIM_ICSelection,
                       u8 TIM_ICFilter);
static void TI3_Config(TIM_TypeDef* TIMx, u16 TIM_ICPolarity, u16 TIM_ICSelection,
                       u8 TIM_ICFilter);
static void TI4_Config(TIM_TypeDef* TIMx, u16 TIM_ICPolarity, u16 TIM_ICSelection,
                       u8 TIM_ICFilter);
static void ETR_Config(TIM_TypeDef* TIMx, u16 TIM_ExtTRGPrescaler, 
                       u16 TIM_ExtTRGPolarity, u8 ExtTRGFilter);
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : TIM_DeInit
* Description    : Deinitializes the TIMx peripheral registers to their default
*                  reset values.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_DeInit(TIM_TypeDef* TIMx)
{  
  switch (*(u32*)&TIMx)
  {
    case TIM2_BASE:
      RCC_APB1PeriphResetCmd(RCC_APB1Periph_TIM2, ENABLE);
      RCC_APB1PeriphResetCmd(RCC_APB1Periph_TIM2, DISABLE);
      break;
 
    case TIM3_BASE:
      RCC_APB1PeriphResetCmd(RCC_APB1Periph_TIM3, ENABLE);
      RCC_APB1PeriphResetCmd(RCC_APB1Periph_TIM3, DISABLE);
      break;
 
    case TIM4_BASE:
      RCC_APB1PeriphResetCmd(RCC_APB1Periph_TIM4, ENABLE);
      RCC_APB1PeriphResetCmd(RCC_APB1Periph_TIM4, DISABLE);
      break;
 
    default:
      break;
  }
}

/*******************************************************************************
* Function Name  : TIM_TimeBaseInit
* Description    : Initializes the TIMx Time Base Unit peripheral according to 
*                  the specified parameters in the TIM_TimeBaseInitStruct.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_TimeBaseInitStruct: pointer to a TIM_TimeBaseInitTypeDef
*                   structure that contains the configuration information for
*                   the specified TIM peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_TimeBaseInit(TIM_TypeDef* TIMx, TIM_TimeBaseInitTypeDef* TIM_TimeBaseInitStruct)
{
  /* Check the parameters */
  assert(IS_TIM_COUNTER_MODE(TIM_TimeBaseInitStruct->TIM_CounterMode));
  assert(IS_TIM_CKD_DIV(TIM_TimeBaseInitStruct->TIM_ClockDivision));
  
  /* Set the Autoreload value */
  TIMx->ARR = TIM_TimeBaseInitStruct->TIM_Period ;

  /* Set the Prescaler value */
  TIMx->PSC = TIM_TimeBaseInitStruct->TIM_Prescaler;

  /* Select the Counter Mode and set the clock division */
  TIMx->CR1 &= CR1_CKD_Mask & CR1_CounterMode_Mask;
  TIMx->CR1 |= (u32)TIM_TimeBaseInitStruct->TIM_ClockDivision |
               TIM_TimeBaseInitStruct->TIM_CounterMode;
}
/*******************************************************************************
* Function Name  : TIM_OCInit
* Description    : Initializes the TIMx peripheral according to the specified
*                  parameters in the TIM_OCInitStruct.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_OCInitStruct: pointer to a TIM_OCInitTypeDef structure
*                    that contains the configuration information for the specified
*                    TIM peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_OCInit(TIM_TypeDef* TIMx, TIM_OCInitTypeDef* TIM_OCInitStruct)
{
  u32 tmpccmrx = 0, tmpccer = 0;
  
  /* Check the parameters */
  assert(IS_TIM_OC_MODE(TIM_OCInitStruct->TIM_OCMode));
  assert(IS_TIM_CHANNEL(TIM_OCInitStruct->TIM_Channel));
  assert(IS_TIM_OC_POLARITY(TIM_OCInitStruct->TIM_OCPolarity));

  tmpccer = TIMx->CCER;

  if ((TIM_OCInitStruct->TIM_Channel == (u16)TIM_Channel_1) ||
      (TIM_OCInitStruct->TIM_Channel == (u16)TIM_Channel_2))
  {
    tmpccmrx = TIMx->CCMR1;
    
    /* Reset the Output Compare Bits */
    tmpccmrx &= Tab_OCModeMask[TIM_OCInitStruct->TIM_Channel];

    /* Set the Output Polarity level */
    tmpccer &= Tab_PolarityMask[TIM_OCInitStruct->TIM_Channel];

    if (TIM_OCInitStruct->TIM_Channel == TIM_Channel_1)
    {
      /* Disable the Channel 1: Reset the CCE Bit */
      TIMx->CCER &= CCRE_CC1E_Reset;

      /* Select the Output Compare Mode */
      tmpccmrx |= TIM_OCInitStruct->TIM_OCMode;

      /* Set the Capture Compare Register value */
      TIMx->CCR1 = TIM_OCInitStruct->TIM_Pulse;

      /* Set the Capture Compare Enable Bit */
      tmpccer |= CCRE_CC1E_Set;

      /* Set the Capture Compare Polarity */
      tmpccer |= TIM_OCInitStruct->TIM_OCPolarity;
    }
    else /* TIM_Channel_2 */
    {
      /* Disable the Channel 2: Reset the CCE Bit */
      TIMx->CCER &= CCRE_CC2E_Reset;

      /* Select the Output Compare Mode */
      tmpccmrx |= (u32)TIM_OCInitStruct->TIM_OCMode << 8;

      /* Set the Capture Compare Register value */
      TIMx->CCR2 = TIM_OCInitStruct->TIM_Pulse;

      /* Set the Capture Compare Enable Bit */
      tmpccer |= CCRE_CC2E_Set;

      /* Set the Capture Compare Polarity */
      tmpccer |= (u32)TIM_OCInitStruct->TIM_OCPolarity << 4;
    }

    TIMx->CCMR1 = (u16)tmpccmrx;
  }
  else 
  {
    if ((TIM_OCInitStruct->TIM_Channel == TIM_Channel_3) ||
        (TIM_OCInitStruct->TIM_Channel == TIM_Channel_4))
    { 
      tmpccmrx = TIMx->CCMR2;

      /* Reset the Output Compare Bits */
      tmpccmrx &= Tab_OCModeMask[TIM_OCInitStruct->TIM_Channel];

      /* Set the Output Polarity level */
      tmpccer &= Tab_PolarityMask[TIM_OCInitStruct->TIM_Channel];

      if (TIM_OCInitStruct->TIM_Channel == TIM_Channel_3)
      {
        /* Disable the Channel 3: Reset the CCE Bit */
        TIMx->CCER &= CCRE_CC3E_Reset;

        /* Select the Output Compare Mode */
        tmpccmrx |= TIM_OCInitStruct->TIM_OCMode;

        /* Set the Capture Compare Register value */
        TIMx->CCR3 = TIM_OCInitStruct->TIM_Pulse;

        /* Set the Capture Compare Enable Bit */
        tmpccer |= CCRE_CC3E_Set;

        /* Set the Capture Compare Polarity */
        tmpccer |= (u32)TIM_OCInitStruct->TIM_OCPolarity << 8;
      }
      else  /* TIM_Channel_4 */
      {
        /* Disable the Channel 4: Reset the CCE Bit */
        TIMx->CCER &= CCRE_CC4E_Reset;

       /* Select the Output Compare Mode */
        tmpccmrx |= (u32)TIM_OCInitStruct->TIM_OCMode << 8;

        /* Set the Capture Compare Register value */
        TIMx->CCR4 = TIM_OCInitStruct->TIM_Pulse;

        /* Set the Capture Compare Enable Bit */
        tmpccer |= CCRE_CC4E_Set;

        /* Set the Capture Compare Polarity */
        tmpccer |= (u32)TIM_OCInitStruct->TIM_OCPolarity << 12;
      }

      TIMx->CCMR2 = (u16)tmpccmrx;
    }
  }
  
  TIMx->CCER = (u16)tmpccer;
}

/*******************************************************************************
* Function Name  : TIM_ICInit
* Description    : Initializes the TIMx peripheral according to the specified
*                  parameters in the TIM_ICInitStruct.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_ICInitStruct: pointer to a TIM_ICInitTypeDef structure
*                    that contains the configuration information for the specified
*                    TIM peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ICInit(TIM_TypeDef* TIMx, TIM_ICInitTypeDef* TIM_ICInitStruct)
{
  /* Check the parameters */
  assert(IS_TIM_IC_MODE(TIM_ICInitStruct->TIM_ICMode));
  assert(IS_TIM_CHANNEL(TIM_ICInitStruct->TIM_Channel));
  assert(IS_TIM_IC_POLARITY(TIM_ICInitStruct->TIM_ICPolarity));
  assert(IS_TIM_IC_SELECTION(TIM_ICInitStruct->TIM_ICSelection));
  assert(IS_TIM_IC_PRESCALER(TIM_ICInitStruct->TIM_ICPrescaler));
  assert(IS_TIM_IC_FILTER(TIM_ICInitStruct->TIM_ICFilter));
  
  if (TIM_ICInitStruct->TIM_ICMode == TIM_ICMode_ICAP)
  {
    if (TIM_ICInitStruct->TIM_Channel == TIM_Channel_1)
    {
      /* TI1 Configuration */
      TI1_Config(TIMx, TIM_ICInitStruct->TIM_ICPolarity,
                 TIM_ICInitStruct->TIM_ICSelection,
                 TIM_ICInitStruct->TIM_ICFilter);

      /* Set the Input Capture Prescaler value */
      TIM_SetIC1Prescaler(TIMx, TIM_ICInitStruct->TIM_ICPrescaler);
    }
    else if (TIM_ICInitStruct->TIM_Channel == TIM_Channel_2)
    {
      /* TI2 Configuration */
      TI2_Config(TIMx, TIM_ICInitStruct->TIM_ICPolarity,
                 TIM_ICInitStruct->TIM_ICSelection,
                 TIM_ICInitStruct->TIM_ICFilter);

      /* Set the Input Capture Prescaler value */
      TIM_SetIC2Prescaler(TIMx, TIM_ICInitStruct->TIM_ICPrescaler);
    }
    else if (TIM_ICInitStruct->TIM_Channel == TIM_Channel_3)
    {
      /* TI3 Configuration */
      TI3_Config(TIMx, TIM_ICInitStruct->TIM_ICPolarity,
                 TIM_ICInitStruct->TIM_ICSelection,
                 TIM_ICInitStruct->TIM_ICFilter);

      /* Set the Input Capture Prescaler value */
      TIM_SetIC3Prescaler(TIMx, TIM_ICInitStruct->TIM_ICPrescaler);
    }
    else /* TIM_Channel_4 */
    {
      /* TI4 Configuration */
      TI4_Config(TIMx, TIM_ICInitStruct->TIM_ICPolarity,
                 TIM_ICInitStruct->TIM_ICSelection,
                 TIM_ICInitStruct->TIM_ICFilter);

      /* Set the Input Capture Prescaler value */
      TIM_SetIC4Prescaler(TIMx, TIM_ICInitStruct->TIM_ICPrescaler);
    }
  }
  else
  {
    PWMI_Config(TIMx, TIM_ICInitStruct);
  }
}

/*******************************************************************************
* Function Name  : TIM_TimeBaseStructInit
* Description    : Fills each TIM_TimeBaseInitStruct member with its default value.
* Input          : - TIM_TimeBaseInitStruct: pointer to a TIM_TimeBaseInitTypeDef
*                    structure which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_TimeBaseStructInit(TIM_TimeBaseInitTypeDef* TIM_TimeBaseInitStruct)
{
  /* Set the default configuration */
  TIM_TimeBaseInitStruct->TIM_Period = TIM_Period_Reset_Mask;
  TIM_TimeBaseInitStruct->TIM_Prescaler = TIM_Prescaler_Reset_Mask;
  TIM_TimeBaseInitStruct->TIM_ClockDivision = TIM_CKD_DIV1;
  TIM_TimeBaseInitStruct->TIM_CounterMode = TIM_CounterMode_Up;
}

/*******************************************************************************
* Function Name  : TIM_OCStructInit
* Description    : Fills each TIM_OCInitStruct member with its default value.
* Input          : - TIM_OCInitStruct: pointer to a TIM_OCInitTypeDef structure
*                    which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_OCStructInit(TIM_OCInitTypeDef* TIM_OCInitStruct)
{
  /* Set the default configuration */
  TIM_OCInitStruct->TIM_OCMode = TIM_OCMode_Timing;
  TIM_OCInitStruct->TIM_Channel = TIM_Channel_1;
  TIM_OCInitStruct->TIM_Pulse = TIM_Pulse_Reset_Mask;
  TIM_OCInitStruct->TIM_OCPolarity = TIM_OCPolarity_High;
}

/*******************************************************************************
* Function Name  : TIM_ICStructInit
* Description    : Fills each TIM_InitStruct member with its default value.
* Input          : - TIM_ICInitStruct: pointer to a TIM_ICInitTypeDef structure
*                    which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ICStructInit(TIM_ICInitTypeDef* TIM_ICInitStruct)
{
  /* Set the default configuration */
  TIM_ICInitStruct->TIM_ICMode = TIM_ICMode_ICAP;
  TIM_ICInitStruct->TIM_Channel = TIM_Channel_1;
  TIM_ICInitStruct->TIM_ICPolarity = TIM_ICPolarity_Rising;
  TIM_ICInitStruct->TIM_ICSelection = TIM_ICSelection_DirectTI;
  TIM_ICInitStruct->TIM_ICPrescaler = TIM_ICPSC_DIV1;
  TIM_ICInitStruct->TIM_ICFilter = TIM_ICFilter_Mask;
}

/*******************************************************************************
* Function Name  : TIM_Cmd
* Description    : Enables or disables the specified TIM peripheral.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIMx peripheral.
*                  - Newstate: new state of the TIMx peripheral.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_Cmd(TIM_TypeDef* TIMx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));
  
  if (NewState != DISABLE)
  {
    /* Enable the TIM Counter */
    TIMx->CR1 |= CR1_CEN_Set;
  }
  else
  {
    /* Disable the TIM Counter */
    TIMx->CR1 &= CR1_CEN_Reset;
  }
}

/*******************************************************************************
* Function Name  : TIM_ITConfig
* Description    : Enables or disables the TIMx interrupts.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_IT: specifies the TIM interrupts sources to be enabled
*                    or disabled.
*                    This parameter can be any combination of the following values:
*                       - TIM_IT_Update: Timer update Interrupt
*                       - TIM_IT_CC1: Capture Compare 1 Interrupt
*                       - TIM_IT_CC2: Capture Compare 2 Interrupt
*                       - TIM_IT_CC3: Capture Compare 3 Interrupt
*                       - TIM_IT_CC4: Capture Compare 4 Interrupt
*                       - TIM_IT_Trigger: Trigger Interrupt
*                  - Newstate: new state of the specified TIMx interrupts.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ITConfig(TIM_TypeDef* TIMx, u16 TIM_IT, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_TIM_IT(TIM_IT));
  assert(IS_FUNCTIONAL_STATE(NewState));
  
  if (NewState != DISABLE)
  {
    /* Enable the Interrupt sources */
    TIMx->DIER |= TIM_IT;
  }
  else
  {
    /* Disable the Interrupt sources */
    TIMx->DIER &= (u16)(~TIM_IT);
  }
}

/*******************************************************************************
* Function Name  : TIM_DMAConfig
* Description    : Configures the TIMx’s DMA interface.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_DMABase: DMA Base address.
*                    This parameter can be one of the following values:
*                       - TIM_DMABase_CR1, TIM_DMABase_CR2, TIM_DMABase_SMCR,
*                         TIM_DMABase_DIER, TIM_DMABase_SR, TIM_DMABase_EGR,
*                         TIM_DMABase_CCMR1, TIM_DMABase_CCMR2, TIM_DMABase_CCER,
*                         TIM_DMABase_CNT, TIM_DMABase_PSC, TIM_DMABase_ARR,
*                         TIM_DMABase_CCR1, TIM_DMABase_CCR2, TIM_DMABase_CCR3,
*                         TIM_DMABase_CCR4, TIM_DMABase_DCR.
*                  - TIM_DMABurstLength: DMA Burst length.
*                    This parameter can be one value between:
*                    TIM_DMABurstLength_1Byte and TIM_DMABurstLength_18Bytes.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_DMAConfig(TIM_TypeDef* TIMx, u16 TIM_DMABase, u16 TIM_DMABurstLength)
{
  u32 tmpdcr = 0;

  /* Check the parameters */
  assert(IS_TIM_DMA_BASE(TIM_DMABase));
  assert(IS_TIM_DMA_LENGTH(TIM_DMABurstLength));
  
  tmpdcr = TIMx->DCR;

  /* Reset the DBA and the DBL Bits */
  tmpdcr &= DCR_DMA_Mask;

  /* Set the DMA Base and the DMA Burst Length */
  tmpdcr |= TIM_DMABase | TIM_DMABurstLength;

  TIMx->DCR = (u16)tmpdcr;
}

/*******************************************************************************
* Function Name  : TIM_DMACmd
* Description    : Enables or disables the TIMx’s DMA Requests.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_DMASources: specifies the DMA Request sources.
*                    This parameter can be any combination of the following values:
*                       - TIM_DMA_CC1: Capture Compare 1 DMA source
*                       - TIM_DMA_CC2: Capture Compare 2 DMA source
*                       - TIM_DMA_CC3: Capture Compare 3 DMA source
*                       - TIM_DMA_CC4: Capture Compare 4 DMA source
*                       - TIM_DMA_Trigger: Trigger DMA source
*                  - Newstate: new state of the DMA Request sources.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_DMACmd(TIM_TypeDef* TIMx, u16 TIM_DMASource, FunctionalState Newstate)
{
  u32 tmpdier = 0;
  
  /* Check the parameters */
  assert(IS_TIM_DMA_SOURCE(TIM_DMASource));
  assert(IS_FUNCTIONAL_STATE(Newstate));

  tmpdier = TIMx->DIER;

  if (Newstate != DISABLE)
  {
    /* Enable the DMA sources */
    tmpdier |= TIM_DMASource;
  }
  else
  {
    /* Disable the DMA sources */
    tmpdier &= (u16)(~TIM_DMASource);
  }
  TIMx->DIER = (u16)tmpdier;
}

/*******************************************************************************
* Function Name  : TIM_InternalClockConfig
* Description    : Configures the TIMx interrnal Clock
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_InternalClockConfig(TIM_TypeDef* TIMx)
{
  /* Disable slave mode to clock the prescaler directly with the internal clock */
  TIMx->SMCR &=  SMCR_SMS_Mask;
}
/*******************************************************************************
* Function Name  : TIM_ITRxExternalClockConfig
* Description    : Configures the TIMx Internal Trigger as External Clock
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_ITRSource: Trigger source.
*                    This parameter can be one of the following values:
*                       - TIM_TS_ITR0: Internal Trigger 0
*                       - TIM_TS_ITR1: Internal Trigger 1
*                       - TIM_TS_ITR2: Internal Trigger 2
*                       - TIM_TS_ITR3: Internal Trigger 3
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ITRxExternalClockConfig(TIM_TypeDef* TIMx, u16 TIM_InputTriggerSource)
{
  /* Check the parameters */
  assert(IS_TIM_INTERNAL_TRIGGER_SELECTION(TIM_InputTriggerSource));

  /* Select the Internal Trigger */
  TIM_SelectInputTrigger(TIMx, TIM_InputTriggerSource);

  /* Select the External clock mode1 */
  TIMx->SMCR |= TIM_SlaveMode_External1;
}
/*******************************************************************************
* Function Name  : TIM_TIxExternalClockConfig
* Description    : Configures the TIMx Trigger as External Clock
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_TIxExternalCLKSource: Trigger source.
*                    This parameter can be one of the following values:
*                       - TIM_TS_TI1F_ED: TI1 Edge Detector
*                       - TIM_TS_TI1FP1: Filtered Timer Input 1
*                       - TIM_TS_TI2FP2: Filtered Timer Input 2
*                  - TIM_ICPolarity: specifies the TIx Polarity.
*                    This parameter can be:
*                       - TIM_ICPolarity_Rising
*                       - TIM_ICPolarity_Falling
*                   - ICFilter : specifies the filter value.
*                     This parameter must be a value between 0x0 and 0xF.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_TIxExternalClockConfig(TIM_TypeDef* TIMx, u16 TIM_TIxExternalCLKSource,
                                u16 TIM_ICPolarity, u8 ICFilter)
{
  /* Check the parameters */
  assert(IS_TIM_TIX_TRIGGER_SELECTION(TIM_TIxExternalCLKSource));
  assert(IS_TIM_IC_POLARITY(TIM_ICPolarity));
  assert(IS_TIM_IC_FILTER(ICFilter));

  /* Configure the Timer Input Clock Source */
  if (TIM_TIxExternalCLKSource == TIM_TIxExternalCLK1Source_TI2)
  {
    TI2_Config(TIMx, TIM_ICPolarity, TIM_ICSelection_DirectTI, ICFilter);
  }
  else
  {
    TI1_Config(TIMx, TIM_ICPolarity, TIM_ICSelection_DirectTI, ICFilter);
  }

  /* Select the Trigger source */
  TIM_SelectInputTrigger(TIMx, TIM_TIxExternalCLKSource);

  /* Select the External clock mode1 */
  TIMx->SMCR |= TIM_SlaveMode_External1;
}

/*******************************************************************************
* Function Name  : TIM_ETRClockMode1Config
* Description    : Configures the External clock Mode1
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_ExtTRGPrescaler: The external Trigger Prescaler.
*                    It can be one of the following values:
*                       - TIM_ExtTRGPSC_OFF
*                       - TIM_ExtTRGPSC_DIV2
*                       - TIM_ExtTRGPSC_DIV4
*                       - TIM_ExtTRGPSC_DIV8.
*                  - TIM_ExtTRGPolarity: The external Trigger Polarity.
*                    It can be one of the following values:
*                       - TIM_ExtTRGPolarity_Inverted
*                       - TIM_ExtTRGPolarity_NonInverted
*                  - ExtTRGFilter: External Trigger Filter.
*                    This parameter must be a value between 0x00 and 0x0F
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ETRClockMode1Config(TIM_TypeDef* TIMx, u16 TIM_ExtTRGPrescaler, u16 TIM_ExtTRGPolarity,
                             u8 ExtTRGFilter)
{
  /* Check the parameters */
  assert(IS_TIM_EXT_PRESCALER(TIM_ExtTRGPrescaler));
  assert(IS_TIM_EXT_POLARITY(TIM_ExtTRGPolarity));

  /* Configure the ETR Clock source */
  ETR_Config(TIMx, TIM_ExtTRGPrescaler, TIM_ExtTRGPolarity, ExtTRGFilter);

  /* Select the External clock mode1 */
  TIMx->SMCR &= SMCR_SMS_Mask;
  TIMx->SMCR |= TIM_SlaveMode_External1;

  /* Select the Trigger selection : ETRF */
  TIMx->SMCR &= SMCR_TS_Mask;
  TIMx->SMCR |= TIM_TS_ETRF;
}

/*******************************************************************************
* Function Name  : TIM_ETRClockMode2Config
* Description    : Configures the External clock Mode2
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_ExtTRGPrescaler: The external Trigger Prescaler.
*                    It can be one of the following values:
*                       - TIM_ExtTRGPSC_OFF
*                       - TIM_ExtTRGPSC_DIV2
*                       - TIM_ExtTRGPSC_DIV4
*                       - TIM_ExtTRGPSC_DIV8
*                  - TIM_ExtTRGPolarity: The external Trigger Polarity.
*                    It can be one of the following values:
*                       - TIM_ExtTRGPolarity_Inverted
*                       - TIM_ExtTRGPolarity_NonInverted
*                  - ExtTRGFilter: External Trigger Filter.
*                    This parameter must be a value between 0x00 and 0x0F
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ETRClockMode2Config(TIM_TypeDef* TIMx, u16 TIM_ExtTRGPrescaler, 
                             u16 TIM_ExtTRGPolarity, u8 ExtTRGFilter)
{
  /* Check the parameters */
  assert(IS_TIM_EXT_PRESCALER(TIM_ExtTRGPrescaler));
  assert(IS_TIM_EXT_POLARITY(TIM_ExtTRGPolarity));

  /* Configure the ETR Clock source */
  ETR_Config(TIMx, TIM_ExtTRGPrescaler, TIM_ExtTRGPolarity, ExtTRGFilter);

  /* Enable the External clock mode2 */
  TIMx->SMCR |= SMCR_ECE_Set;
}
/*******************************************************************************
* Function Name  : TIM_SelectInputTrigger
* Description    : Selects the Input Trigger source
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_InputTriggerSource: The Input Trigger source.
*                    This parameter can be one of the following values:
*                       - TIM_TS_ITR0: Internal Trigger 0
*                       - TIM_TS_ITR1: Internal Trigger 1
*                       - TIM_TS_ITR2: Internal Trigger 2
*                       - TIM_TS_ITR3: Internal Trigger 3
*                       - TIM_TS_TI1F_ED: TI1 Edge Detector
*                       - TIM_TS_TI1FP1: Filtered Timer Input 1
*                       - TIM_TS_TI2FP2: Filtered Timer Input 2
*                       - TIM_TS_ETRF: External Trigger input
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SelectInputTrigger(TIM_TypeDef* TIMx, u16 TIM_InputTriggerSource)
{
  u32 tmpsmcr = 0;

  /* Check the parameters */
  assert(IS_TIM_TRIGGER_SELECTION(TIM_InputTriggerSource));

  tmpsmcr = TIMx->SMCR;

  /* Select the Tgigger Source */
  tmpsmcr &= SMCR_TS_Mask;
  tmpsmcr |= TIM_InputTriggerSource;

  TIMx->SMCR = (u16)tmpsmcr;
}

/*******************************************************************************
* Function Name  : TIM_PrescalerConfig
* Description    : Configures the TIMx Prescaler.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - Prescaler: specifies the Prescaler Register value
*                  - TIM_PSCReloadMode: specifies the TIM Prescaler Reload mode
*                    This parameter can be one of the following values:
*                       - TIM_PSCReloadMode_Update: The Prescaler is loaded at
*                         the update event.
*                       - TIM_PSCReloadMode_Immediate: The Prescaler is loaded
*                         immediatly.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_PrescalerConfig(TIM_TypeDef* TIMx, u16 Prescaler, u16 TIM_PSCReloadMode)
{
  /* Check the parameters */
  assert(IS_TIM_PRESCALER_RELOAD(TIM_PSCReloadMode));

  /* Set the Prescaler value */
  TIMx->PSC = Prescaler;

  /* Set or reset the UG Bit */
  if (TIM_PSCReloadMode == TIM_PSCReloadMode_Immediate)
  {
    TIMx->EGR |= TIM_EventSource_Update;
  }
  else
  {
    TIMx->EGR &= TIM_EventSource_Update;
  }
}

/*******************************************************************************
* Function Name  : TIM_CounterModeConfig
* Description    : Specifies the TIMx Counter Mode to be used.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_CounterMode: specifies the Counter Mode to be used
*                    This parameter can be one of the following values:
*                       - TIM_CounterMode_Up: TIM Up Counting Mode
*                       - TIM_CounterMode_Down: TIM Down Counting Mode
*                       - TIM_CounterMode_CenterAligned1: TIM Center Aligned Mode1
*                       - TIM_CounterMode_CenterAligned2: TIM Center Aligned Mode2
*                       - TIM_CounterMode_CenterAligned3: TIM Center Aligned Mode3
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_CounterModeConfig(TIM_TypeDef* TIMx, u16 TIM_CounterMode)
{
  u32 tmpcr1 = 0;

  /* Check the parameters */
  assert(IS_TIM_COUNTER_MODE(TIM_CounterMode));

  tmpcr1 = TIMx->CR1;

  /* Reset the CMS and DIR Bits */
  tmpcr1 &= CR1_CounterMode_Mask;

  /* Set the Counter Mode */
  tmpcr1 |= TIM_CounterMode;

  TIMx->CR1 = (u16)tmpcr1;
}

/*******************************************************************************
* Function Name  : TIM_ForcedOC1Config
* Description    : Forces the TIMx output 1 waveform to active or inactive level.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_ForcedAction: specifies the forced Action to be set to
*                    the output waveform.
*                    This parameter can be one of the following values:
*                       - TIM_ForcedAction_Active: Force active level on OC1REF
*                       - TIM_ForcedAction_InActive: Force inactive level on
*                         OC1REF.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ForcedOC1Config(TIM_TypeDef* TIMx, u16 TIM_ForcedAction)
{
  u32 tmpccmr1 = 0;

  /* Check the parameters */
  assert(IS_TIM_FORCED_ACTION(TIM_ForcedAction));

  tmpccmr1 = TIMx->CCMR1;

  /* Reset the OCM Bits */
  tmpccmr1 &= CCMR_OCM13_Mask;

  /* Configure The Forced output Mode */
  tmpccmr1 |= TIM_ForcedAction;

  TIMx->CCMR1 = (u16)tmpccmr1;
}

/*******************************************************************************
* Function Name  : TIM_ForcedOC2Config
* Description    : Forces the TIMx output 2 waveform to active or inactive level.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_ForcedAction: specifies the forced Action to be set to
*                    the output waveform.
*                    This parameter can be one of the following values:
*                       - TIM_ForcedAction_Active: Force active level on OC2REF
*                       - TIM_ForcedAction_InActive: Force inactive level on
*                         OC2REF.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ForcedOC2Config(TIM_TypeDef* TIMx, u16 TIM_ForcedAction)
{
  u32 tmpccmr1 = 0;

  /* Check the parameters */
  assert(IS_TIM_FORCED_ACTION(TIM_ForcedAction));

  tmpccmr1 = TIMx->CCMR1;

  /* Reset the OCM Bits */
  tmpccmr1 &= CCMR_OCM24_Mask;

  /* Configure The Forced output Mode */
  tmpccmr1 |= (u16)(TIM_ForcedAction << 8);

  TIMx->CCMR1 = (u16)tmpccmr1;
}

/*******************************************************************************
* Function Name  : TIM_ForcedOC3Config
* Description    : Forces the TIMx output 3 waveform to active or inactive level.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_ForcedAction: specifies the forced Action to be set to
*                    the output waveform.
*                    This parameter can be one of the following values:
*                       - TIM_ForcedAction_Active: Force active level on OC3REF
*                       - TIM_ForcedAction_InActive: Force inactive level on
*                         OC3REF.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ForcedOC3Config(TIM_TypeDef* TIMx, u16 TIM_ForcedAction)
{
  u32 tmpccmr2 = 0;

  /* Check the parameters */
  assert(IS_TIM_FORCED_ACTION(TIM_ForcedAction));

  tmpccmr2 = TIMx->CCMR2;

  /* Reset the OCM Bits */
  tmpccmr2 &= CCMR_OCM13_Mask;

  /* Configure The Forced output Mode */
  tmpccmr2 |= TIM_ForcedAction;

  TIMx->CCMR2 = (u16)tmpccmr2;
}

/*******************************************************************************
* Function Name  : TIM_ForcedOC4Config
* Description    : Forces the TIMx output 4 waveform to active or inactive level.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_ForcedAction: specifies the forced Action to be set to
*                    the output waveform.
*                    This parameter can be one of the following values:
*                       - TIM_ForcedAction_Active: Force active level on OC4REF
*                       - TIM_ForcedAction_InActive: Force inactive level on
*                         OC4REF.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ForcedOC4Config(TIM_TypeDef* TIMx, u16 TIM_ForcedAction)
{
  u32 tmpccmr2 = 0;

  /* Check the parameters */
  assert(IS_TIM_FORCED_ACTION(TIM_ForcedAction));

  tmpccmr2 = TIMx->CCMR2;

  /* Reset the OCM Bits */
  tmpccmr2 &= CCMR_OCM24_Mask;

  /* Configure The Forced output Mode */
  tmpccmr2 |= (u16)(TIM_ForcedAction << 8);

  TIMx->CCMR2 = (u16)tmpccmr2;
}

/*******************************************************************************
* Function Name  : TIM_ARRPreloadConfig
* Description    : Enables or disables TIMx peripheral Preload register on ARR.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - Newstate: new state of the TIMx peripheral Preload register
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ARRPreloadConfig(TIM_TypeDef* TIMx, FunctionalState Newstate)
{
  u32 tmpcr1 = 0;
  
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(Newstate));

  tmpcr1 = TIMx->CR1;

  if (Newstate != DISABLE)
  {
    /* Set the ARR Preload Bit */
    tmpcr1 |= CR1_ARPE_Set;
  }
  else
  {
    /* Reset the ARR Preload Bit */
    tmpcr1 &= CR1_ARPE_Reset;
  }

  TIMx->CR1 = (u16)tmpcr1;
}

/*******************************************************************************
* Function Name  : TIM_SelectCCDMA
* Description    : Selects the TIMx peripheral Capture Compare DMA source.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - Newstate: new state of the Capture Compare DMA source
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SelectCCDMA(TIM_TypeDef* TIMx, FunctionalState Newstate)
{
  u32 tmpcr2 = 0;

  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(Newstate));

  tmpcr2 = TIMx->CR2;

  if (Newstate != DISABLE)
  {
    /* Set the CCDS Bit */
    tmpcr2 |= CR2_CCDS_Set;
  }
  else
  {
    /* Reset the CCDS Bit */
    tmpcr2 &= CR2_CCDS_Reset;
  }

  TIMx->CR2 = (u16)tmpcr2;
}

/*******************************************************************************
* Function Name  : TIM_OC1PreloadConfig
* Description    : Enables or disables the TIMx peripheral Preload register on CCR1.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_OCPreload: new state of the TIMx peripheral Preload
*                    register
*                    This parameter can be one of the following values:
*                       - TIM_OCPreload_Enable
*                       - TIM_OCPreload_Disable
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_OC1PreloadConfig(TIM_TypeDef* TIMx, u16 TIM_OCPreload)
{
  u32 tmpccmr1 = 0;

  /* Check the parameters */
  assert(IS_TIM_OCPRELOAD_STATE(TIM_OCPreload));

  tmpccmr1 = TIMx->CCMR1;

  /* Reset the OCPE Bit */
  tmpccmr1 &= CCMR_OC13PE_Mask;

  /* Enable or Disable the Output Compare Preload feature */
  tmpccmr1 |= TIM_OCPreload;

  TIMx->CCMR1 = (u16)tmpccmr1;
}

/*******************************************************************************
* Function Name  : TIM_OC2PreloadConfig
* Description    : Enables or disables the TIMx peripheral Preload register on CCR2.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_OCPreload: new state of the TIMx peripheral Preload
*                    register
*                    This parameter can be one of the following values:
*                       - TIM_OCPreload_Enable
*                       - TIM_OCPreload_Disable
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_OC2PreloadConfig(TIM_TypeDef* TIMx, u16 TIM_OCPreload)
{
  u32 tmpccmr1 = 0;

  /* Check the parameters */
  assert(IS_TIM_OCPRELOAD_STATE(TIM_OCPreload));

  tmpccmr1 = TIMx->CCMR1;

  /* Reset the OCPE Bit */
  tmpccmr1 &= CCMR_OC24PE_Mask;

  /* Enable or Disable the Output Compare Preload feature */
  tmpccmr1 |= (u16)(TIM_OCPreload << 8);

  TIMx->CCMR1 = (u16)tmpccmr1;
}

/*******************************************************************************
* Function Name  : TIM_OC3PreloadConfig
* Description    : Enables or disables the TIMx peripheral Preload register on CCR3.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_OCPreload: new state of the TIMx peripheral Preload
*                    register
*                    This parameter can be one of the following values:
*                       - TIM_OCPreload_Enable
*                       - TIM_OCPreload_Disable
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_OC3PreloadConfig(TIM_TypeDef* TIMx, u16 TIM_OCPreload)
{
  u32 tmpccmr2 = 0;

  /* Check the parameters */
  assert(IS_TIM_OCPRELOAD_STATE(TIM_OCPreload));

  tmpccmr2 = TIMx->CCMR2;

  /* Reset the OCPE Bit */
  tmpccmr2 &= CCMR_OC13PE_Mask;

  /* Enable or Disable the Output Compare Preload feature */
  tmpccmr2 |= TIM_OCPreload;

  TIMx->CCMR2 = (u16)tmpccmr2;
}

/*******************************************************************************
* Function Name  : TIM_OC4PreloadConfig
* Description    : Enables or disables the TIMx peripheral Preload register on CCR4.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_OCPreload: new state of the TIMx peripheral Preload
*                    register
*                    This parameter can be one of the following values:
*                       - TIM_OCPreload_Enable
*                       - TIM_OCPreload_Disable
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_OC4PreloadConfig(TIM_TypeDef* TIMx, u16 TIM_OCPreload)
{
  u32 tmpccmr2 = 0;

  /* Check the parameters */
  assert(IS_TIM_OCPRELOAD_STATE(TIM_OCPreload));

  tmpccmr2 = TIMx->CCMR2;

  /* Reset the OCPE Bit */
  tmpccmr2 &= CCMR_OC24PE_Mask;

  /* Enable or Disable the Output Compare Preload feature */
  tmpccmr2 |= (u16)(TIM_OCPreload << 8);

  TIMx->CCMR2 = (u16)tmpccmr2;
}

/*******************************************************************************
* Function Name  : TIM_OC1FastConfig
* Description    : Configures the TIMx Output Compare 1 Fast feature.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_OCFast: new state of the Output Compare Fast Enable Bit.
*                    This parameter can be one of the following values:
*                       - TIM_OCFast_Enable
*                       - TIM_OCFast_Disable
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_OC1FastConfig(TIM_TypeDef* TIMx, u16 TIM_OCFast)
{
  u32 tmpccmr1 = 0;

  /* Check the parameters */
  assert(IS_TIM_OCFAST_STATE(TIM_OCFast));

  tmpccmr1 = TIMx->CCMR1;

  /* Reset the OCFE Bit */
  tmpccmr1 &= CCMR_OC13FE_Mask;

  /* Enable or Disable the Output Compare Fast Bit */
  tmpccmr1 |= TIM_OCFast;

  TIMx->CCMR1 = (u16)tmpccmr1;
}

/*******************************************************************************
* Function Name  : TIM_OC2FastConfig
* Description    : Configures the TIMx Output Compare 2 Fast feature.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_OCFast: new state of the Output Compare Fast Enable Bit.
*                    This parameter can be one of the following values:
*                       - TIM_OCFast_Enable
*                       - TIM_OCFast_Disable
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_OC2FastConfig(TIM_TypeDef* TIMx, u16 TIM_OCFast)
{
  u32 tmpccmr1 = 0;

  /* Check the parameters */
  assert(IS_TIM_OCFAST_STATE(TIM_OCFast));

  tmpccmr1 = TIMx->CCMR1;

  /* Reset the OCFE Bit */
  tmpccmr1 &= CCMR_OC24FE_Mask;

  /* Enable or Disable the Output Compare Fast Bit */
  tmpccmr1 |= (u16)(TIM_OCFast << 8);

  TIMx->CCMR1 = (u16)tmpccmr1;
}

/*******************************************************************************
* Function Name  : TIM_OC3FastConfig
* Description    : Configures the TIMx Output Compare 3 Fast feature.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_OCFast: new state of the Output Compare Fast Enable Bit.
*                    This parameter can be one of the following values:
*                       - TIM_OCFast_Enable
*                       - TIM_OCFast_Disable
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_OC3FastConfig(TIM_TypeDef* TIMx, u16 TIM_OCFast)
{
  u32 tmpccmr2 = 0;

  /* Check the parameters */
  assert(IS_TIM_OCFAST_STATE(TIM_OCFast));

  tmpccmr2 = TIMx->CCMR2;

  /* Reset the OCFE Bit */
  tmpccmr2 &= CCMR_OC13FE_Mask;

  /* Enable or Disable the Output Compare Fast Bit */
  tmpccmr2 |= TIM_OCFast;

  TIMx->CCMR2 = (u16)tmpccmr2;
}

/*******************************************************************************
* Function Name  : TIM_OC4FastConfig
* Description    : Configures the TIMx Output Compare 4 Fast feature.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_OCFast: new state of the Output Compare Fast Enable Bit.
*                    This parameter can be one of the following values:
*                       - TIM_OCFast_Enable
*                       - TIM_OCFast_Disable
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_OC4FastConfig(TIM_TypeDef* TIMx, u16 TIM_OCFast)
{
  u32 tmpccmr2 = 0;

  /* Check the parameters */
  assert(IS_TIM_OCFAST_STATE(TIM_OCFast));

  tmpccmr2 = TIMx->CCMR2;

  /* Reset the OCFE Bit */
  tmpccmr2 &= CCMR_OC24FE_Mask;

  /* Enable or Disable the Output Compare Fast Bit */
  tmpccmr2 |= (u16)(TIM_OCFast << 8);

  TIMx->CCMR2 = (u16)tmpccmr2;
}

/*******************************************************************************
* Function Name  : TIM_UpdateDisableConfig
* Description    : Enables or Disables the TIMx Update event.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - Newstate: new state of the TIMx peripheral Preload register
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_UpdateDisableConfig(TIM_TypeDef* TIMx, FunctionalState Newstate)
{
  u32 tmpcr1 = 0;

  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(Newstate));

  tmpcr1 = TIMx->CR1;

  if (Newstate != DISABLE)
  {
    /* Set the Update Disable Bit */
    tmpcr1 |= CR1_UDIS_Set;
  }
  else
  {
    /* Reset the Update Disable Bit */
    tmpcr1 &= CR1_UDIS_Reset;
  }

  TIMx->CR1 = (u16)tmpcr1;
}

/*******************************************************************************
* Function Name  : TIM_EncoderInterfaceConfig
* Description    : Configures the TIMx Encoder Interface.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_EncoderMode: specifies the TIMx Encoder Mode.
*                    This parameter can be one of the following values:
*                       - TIM_EncoderMode_TI1: Counter counts on TI1FP1 edge
*                         depending on TI2FP2 level.
*                       - TIM_EncoderMode_TI2: Counter counts on TI2FP2 edge
*                         depending on TI1FP1 level.
*                       - TIM_EncoderMode_TI12: Counter counts on both TI1FP1 and
*                         TI2FP2 edges depending on the level of the other input.
*                  - TIM_IC1Polarity: specifies the IC1 Polarity
*                    This parmeter can be one of the following values:
*                        - TIM_ICPolarity_Falling
*                        - TIM_ICPolarity_Rising
*                  - TIM_IC2Polarity: specifies the IC2 Polarity
*                    This parmeter can be one of the following values:
*                       - TIM_ICPolarity_Falling
*                       - TIM_ICPolarity_Rising
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_EncoderInterfaceConfig(TIM_TypeDef* TIMx, u16 TIM_EncoderMode,
                                u16 TIM_IC1Polarity, u16 TIM_IC2Polarity)
{
  u32 tmpsmcr = 0;
  u32 tmpccmr1 = 0;
  u32 tmpccer = 0;
    
  /* Check the parameters */
  assert(IS_TIM_ENCODER_MODE(TIM_EncoderMode));
  assert(IS_TIM_IC_POLARITY(TIM_IC1Polarity));
  assert(IS_TIM_IC_POLARITY(TIM_IC2Polarity));

  tmpsmcr = TIMx->SMCR;
  tmpccmr1 = TIMx->CCMR1;
  tmpccer = TIMx->CCER;

  /* Set the encoder Mode */
  tmpsmcr &= SMCR_SMS_Mask;
  tmpsmcr |= TIM_EncoderMode;

  /* Select the Capture Compare 1 and the Capture Compare 2 as input */
  tmpccmr1 &= CCMR_CC13S_Mask & CCMR_CC24S_Mask;
  tmpccmr1 |= CCMR_TI13Direct_Set | CCMR_TI24Direct_Set;

  /* Set the TI1 and the TI2 Polarities */
  tmpccer &= CCER_CC1P_Mask & CCER_CC2P_Mask;
  tmpccer |= (TIM_IC1Polarity | (u16)((u16)TIM_IC2Polarity << 4));

  TIMx->SMCR = (u16)tmpsmcr;

  TIMx->CCMR1 = (u16)tmpccmr1;

  TIMx->CCER = (u16)tmpccer;
}

/*******************************************************************************
* Function Name  : TIM_GenerateEvent
* Description    : Configures the TIMx event to be generate by software.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_EventSource: specifies the event source.
*                    This parameter can be one or more of the following values:
*                       - TIM_EventSource_Update: Timer update Event source
*                       - TIM_EventSource_CC1: Timer Capture Compare 1 Event source
*                       - TIM_EventSource_CC2: Timer Capture Compare 2 Event source
*                       - TIM_EventSource_CC3: Timer Capture Compare 3 Event source
*                       - TIM_EventSource_CC4: Timer Capture Compare 4 Event source
*                       - TIM_EventSource_Trigger: Timer Trigger Event source
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_GenerateEvent(TIM_TypeDef* TIMx, u16 TIM_EventSource)
{
  /* Check the parameters */
  assert(IS_TIM_EVENT_SOURCE(TIM_EventSource));

  /* Set the event sources */
  TIMx->EGR |= TIM_EventSource;
}

/*******************************************************************************
* Function Name  : TIM_OC1PolarityConfig
* Description    : Configures the TIMx channel 1 polarity.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_OCPolarity: specifies the OC1 Polarity
*                    This parmeter can be one of the following values:
*                       - TIM_OCPolarity_High: Output Compare active high
*                       - TIM_OCPolarity_Low: Output Compare active low
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_OC1PolarityConfig(TIM_TypeDef* TIMx, u16 TIM_OCPolarity)
{
  u32 tmpccer = 0;

  /* Check the parameters */
  assert(IS_TIM_OC_POLARITY(TIM_OCPolarity));

  tmpccer = TIMx->CCER;

  /* Set or Reset the CC1P Bit */
  tmpccer &= CCER_CC1P_Mask;
  tmpccer |= TIM_OCPolarity;

  TIMx->CCER = (u16)tmpccer;
}

/*******************************************************************************
* Function Name  : TIM_OC2PolarityConfig
* Description    : Configures the TIMx channel 2 polarity.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_OCPolarity: specifies the OC2 Polarity
*                    This parmeter can be one of the following values:
*                       - TIM_OCPolarity_High: Output Compare active high
*                       - TIM_OCPolarity_Low: Output Compare active low
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_OC2PolarityConfig(TIM_TypeDef* TIMx, u16 TIM_OCPolarity)
{
  u32 tmpccer = 0;

  /* Check the parameters */
  assert(IS_TIM_OC_POLARITY(TIM_OCPolarity));

  tmpccer = TIMx->CCER;

  /* Set or Reset the CC2P Bit */
  tmpccer &= CCER_CC2P_Mask;
  tmpccer |= (u16)((u16)TIM_OCPolarity << 4);

  TIMx->CCER = (u16)tmpccer;
}

/*******************************************************************************
* Function Name  : TIM_OC3PolarityConfig
* Description    : Configures the TIMx channel 3 polarity.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_OCPolarity: specifies the OC3 Polarity
*                    This parmeter can be one of the following values:
*                       - TIM_OCPolarity_High: Output Compare active high
*                       - TIM_OCPolarity_Low: Output Compare active low
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_OC3PolarityConfig(TIM_TypeDef* TIMx, u16 TIM_OCPolarity)
{
  u32 tmpccer = 0;

  /* Check the parameters */
  assert(IS_TIM_OC_POLARITY(TIM_OCPolarity));

  tmpccer = TIMx->CCER;

  /* Set or Reset the CC3P Bit */
  tmpccer &= CCER_CC3P_Mask;
  tmpccer |= (u16)((u16)TIM_OCPolarity << 8);

  TIMx->CCER = (u16)tmpccer;
}

/*******************************************************************************
* Function Name  : TIM_OC4PolarityConfig
* Description    : Configures the TIMx channel 4 polarity.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_OCPolarity: specifies the OC4 Polarity
*                    This parmeter can be one of the following values:
*                       - TIM_OCPolarity_High: Output Compare active high
*                       - TIM_OCPolarity_Low: Output Compare active low
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_OC4PolarityConfig(TIM_TypeDef* TIMx, u16 TIM_OCPolarity)
{
  u32 tmpccer = 0;

  /* Check the parameters */
  assert(IS_TIM_OC_POLARITY(TIM_OCPolarity));

  tmpccer = TIMx->CCER;

  /* Set or Reset the CC4P Bit */
  tmpccer &= CCER_CC4P_Mask;
  tmpccer |= (u16)((u16)TIM_OCPolarity << 12);

  TIMx->CCER = (u16)tmpccer;
}

/*******************************************************************************
* Function Name  : TIM_UpdateRequestConfig
* Description    : Configures the TIMx Update Request Interrupt source.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_UpdateSource: specifies the Update source.
*                    This parameter can be one of the following values:
*                       - TIM_UpdateSource_Regular
*                       - TIM_UpdateSource_Global
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_UpdateRequestConfig(TIM_TypeDef* TIMx, u16 TIM_UpdateSource)
{
  u32 tmpcr1 = 0;

  /* Check the parameters */
  assert(IS_TIM_UPDATE_SOURCE(TIM_UpdateSource));

  tmpcr1 = TIMx->CR1;

  if (TIM_UpdateSource == TIM_UpdateSource_Regular)
  {
    /* Set the URS Bit */
    tmpcr1 |= CR1_URS_Set;
  }
  else
  {
    /* Reset the URS Bit */
    tmpcr1 &= CR1_URS_Reset;
  }
  TIMx->CR1 = (u16)tmpcr1;
}

/*******************************************************************************
* Function Name  : TIM_SelectHallSensor
* Description    : Enables or disables the TIMx’s Hall sensor interface.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - Newstate: new state of the TIMx Hall sensor interface.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SelectHallSensor(TIM_TypeDef* TIMx, FunctionalState Newstate)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(Newstate));

  if (Newstate != DISABLE)
  {
    /* Set the TI1S Bit */
    TIMx->CR2 |= CR2_TI1S_Set;
  }
  else
  {
    /* Reset the TI1S Bit */
    TIMx->CR2 &= CR2_TI1S_Reset;
  }
}

/*******************************************************************************
* Function Name  : TIM_SelectOnePulseMode
* Description    : Selects the TIMx’s One Pulse Mode.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_OPMode: specifies the OPM Mode to be used.
*                    This parameter can be one of the following values:
*                       - TIM_OPMode_Single
*                       - TIM_OPMode_Repetitive
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SelectOnePulseMode(TIM_TypeDef* TIMx, u16 TIM_OPMode)
{
  u32 tmpcr1 = 0;

  /* Check the parameters */
  assert(IS_TIM_OPM_MODE(TIM_OPMode));

  tmpcr1 = TIMx->CR1;

  /* Reset the OPM Bit */
  tmpcr1 &= CR1_OPM_Mask;

  /* Configure the OPM Mode */
  tmpcr1 |= TIM_OPMode;

  TIMx->CR1 = (u16)tmpcr1;
}

/*******************************************************************************
* Function Name  : TIM_SelectOutputTrigger
* Description    : Selects the TIMx Trigger Output Mode.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_TRGOSource: specifies the Trigger Output source.
*                    This paramter can be one of the following values:
*                       - TIM_TRGOSource_Reset
*                       - TIM_TRGOSource_Enable
*                       - TIM_TRGOSource_Update
*                       - TIM_TRGOSource_OC1
*                       - TIM_TRGOSource_OC1Ref
*                       - TIM_TRGOSource_OC2Ref
*                       - TIM_TRGOSource_OC3Ref
*                       - TIM_TRGOSource_OC4Ref
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SelectOutputTrigger(TIM_TypeDef* TIMx, u16 TIM_TRGOSource)
{
  u32 tmpcr2 = 0;

  /* Check the parameters */
  assert(IS_TIM_TRGO_SOURCE(TIM_TRGOSource));

  tmpcr2 = TIMx->CR2;
  /* Reset the MMS Bits */
  tmpcr2 &= CR2_MMS_Mask;

  /* Select the TRGO source */
  tmpcr2 |=  TIM_TRGOSource;

  TIMx->CR2 = (u16)tmpcr2;
}

/*******************************************************************************
* Function Name  : TIM_SelectSlaveMode
* Description    : Selects the TIMx Slave Mode.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_SlaveMode: specifies the Timer Slave Mode.
*                    This paramter can be one of the following values:
*                       - TIM_SlaveMode_Reset
*                       - TIM_SlaveMode_Gated
*                       - TIM_SlaveMode_Trigger
*                       - TIM_SlaveMode_External1
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SelectSlaveMode(TIM_TypeDef* TIMx, u16 TIM_SlaveMode)
{
  u32 tmpsmcr = 0;

  /* Check the parameters */
  assert(IS_TIM_SLAVE_MODE(TIM_SlaveMode));

  tmpsmcr = TIMx->SMCR;

  /* Reset the SMS Bits */
  tmpsmcr &= SMCR_SMS_Mask;

  /* Select the Slave Mode */
  tmpsmcr |= TIM_SlaveMode;

  TIMx->SMCR = (u16)tmpsmcr;
}

/*******************************************************************************
* Function Name  : TIM_SelectMasterSlaveMode
* Description    : Sets or Resets the TIMx Master/Slave Mode.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_MasterSlaveMode: specifies the Timer Master Slave Mode.
*                    This paramter can be one of the following values:
*                       - TIM_MasterSlaveMode_Enable: synchronization between the
*                         current timer and its slaves (through TRGO).
*                       - TIM_MasterSlaveMode_Disable: No action
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SelectMasterSlaveMode(TIM_TypeDef* TIMx, u16 TIM_MasterSlaveMode)
{
  u32 tmpsmcr = 0;

  /* Check the parameters */
  assert(IS_TIM_MSM_STATE(TIM_MasterSlaveMode));

  tmpsmcr = TIMx->SMCR;

  /* Set or Reset the MSM Bit */
  tmpsmcr &= SMCR_MSM_Mask;
  tmpsmcr |= TIM_MasterSlaveMode;

  TIMx->SMCR = (u16)tmpsmcr;
}

/*******************************************************************************
* Function Name  : TIM_SetAutoreload
* Description    : Sets the TIMx Autoreload Register value
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - Autoreload: specifies the Autoreload register new value.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SetAutoreload(TIM_TypeDef* TIMx, u16 Autoreload)
{
  /* Set the Autoreload Register value */
  TIMx->ARR = Autoreload;
}

/*******************************************************************************
* Function Name  : TIM_SetCompare1
* Description    : Sets the TIMx Capture Compare1 Register value
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - Compare1: specifies the Capture Compare1 register new value.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SetCompare1(TIM_TypeDef* TIMx, u16 Compare1)
{
  /* Set the Capture Compare1 Register value */
  TIMx->CCR1 = Compare1;
}

/*******************************************************************************
* Function Name  : TIM_SetCompare2
* Description    : Sets the TIMx Capture Compare2 Register value
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - Compare2: specifies the Capture Compare2 register new value.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SetCompare2(TIM_TypeDef* TIMx, u16 Compare2)
{
  /* Set the Capture Compare2 Register value */
  TIMx->CCR2 = Compare2;
}

/*******************************************************************************
* Function Name  : TIM_SetCompare3
* Description    : Sets the TIMx Capture Compare3 Register value
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - Compare3: specifies the Capture Compare3 register new value.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SetCompare3(TIM_TypeDef* TIMx, u16 Compare3)
{
  /* Set the Capture Compare3 Register value */
  TIMx->CCR3 = Compare3;
}

/*******************************************************************************
* Function Name  : TIM_SetCompare4
* Description    : Sets the TIMx Capture Compare4 Register value
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - Compare4: specifies the Capture Compare4 register new value.
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SetCompare4(TIM_TypeDef* TIMx, u16 Compare4)
{
  /* Set the Capture Compare4 Register value */
  TIMx->CCR4 = Compare4;
}

/*******************************************************************************
* Function Name  : TIM_SetIC1Prescaler
* Description    : Sets the TIMx Input Capture 1 prescaler.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_IC1Prescaler: specifies the Input Capture1 prescaler
*                    new value.
*                    This parameter can be one of the following values:
*                       - TIM_ICPSC_DIV1: no prescaler
*                       - TIM_ICPSC_DIV2: capture is done once every 2 events
*                       - TIM_ICPSC_DIV4: capture is done once every 4 events
*                       - TIM_ICPSC_DIV8: capture is done once every 8 events
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SetIC1Prescaler(TIM_TypeDef* TIMx, u16 TIM_IC1Prescaler)
{
  u32 tmpccmr1 = 0;

  /* Check the parameters */
  assert(IS_TIM_IC_PRESCALER(TIM_IC1Prescaler));

  tmpccmr1 = TIMx->CCMR1;

  /* Reset the IC1PSC Bits */
  tmpccmr1 &= CCMR_IC13PSC_Mask;

  /* Set the IC1PSC value */
  tmpccmr1 |= TIM_IC1Prescaler;

  TIMx->CCMR1 = (u16)tmpccmr1;
}

/*******************************************************************************
* Function Name  : TIM_SetIC2Prescaler
* Description    : Sets the TIMx Input Capture 2 prescaler.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_IC2Prescaler: specifies the Input Capture2 prescaler
*                    new value.
*                    This parameter can be one of the following values:
*                       - TIM_ICPSC_DIV1: no prescaler
*                       - TIM_ICPSC_DIV2: capture is done once every 2 events
*                       - TIM_ICPSC_DIV4: capture is done once every 4 events
*                       - TIM_ICPSC_DIV8: capture is done once every 8 events
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SetIC2Prescaler(TIM_TypeDef* TIMx, u16 TIM_IC2Prescaler)
{
  u32 tmpccmr1 = 0;

  /* Check the parameters */
  assert(IS_TIM_IC_PRESCALER(TIM_IC2Prescaler));

  tmpccmr1 = TIMx->CCMR1;

  /* Reset the IC2PSC Bits */
  tmpccmr1 &= CCMR_IC24PSC_Mask;

  /* Set the IC2PSC value */
  tmpccmr1 |= (u16)((u16)TIM_IC2Prescaler << 8);

  TIMx->CCMR1 = (u16)tmpccmr1;
}

/*******************************************************************************
* Function Name  : TIM_SetIC3Prescaler
* Description    : Sets the TIMx Input Capture 3 prescaler.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_IC3Prescaler: specifies the Input Capture3 prescaler
*                    new value.
*                    This parameter can be one of the following values:
*                       - TIM_ICPSC_DIV1: no prescaler
*                       - TIM_ICPSC_DIV2: capture is done once every 2 events
*                       - TIM_ICPSC_DIV4: capture is done once every 4 events
*                       - TIM_ICPSC_DIV8: capture is done once every 8 events
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SetIC3Prescaler(TIM_TypeDef* TIMx, u16 TIM_IC3Prescaler)
{
  u32 tmpccmr2 = 0;

  /* Check the parameters */
  assert(IS_TIM_IC_PRESCALER(TIM_IC3Prescaler));

  tmpccmr2 = TIMx->CCMR2;

  /* Reset the IC3PSC Bits */
  tmpccmr2 &= CCMR_IC13PSC_Mask;

  /* Set the IC3PSC value */
  tmpccmr2 |= TIM_IC3Prescaler;

  TIMx->CCMR2 = (u16)tmpccmr2;
}

/*******************************************************************************
* Function Name  : TIM_SetIC4Prescaler
* Description    : Sets the TIMx Input Capture 4 prescaler.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_IC4Prescaler: specifies the Input Capture4 prescaler
*                    new value.
*                    This parameter can be one of the following values:
*                      - TIM_ICPSC_DIV1: no prescaler
*                      - TIM_ICPSC_DIV2: capture is done once every 2 events
*                      - TIM_ICPSC_DIV4: capture is done once every 4 events
*                      - TIM_ICPSC_DIV8: capture is done once every 8 events
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SetIC4Prescaler(TIM_TypeDef* TIMx, u16 TIM_IC4Prescaler)
{
  u32 tmpccmr2 = 0;
   
  /* Check the parameters */
  assert(IS_TIM_IC_PRESCALER(TIM_IC4Prescaler));

  tmpccmr2 = TIMx->CCMR2;

  /* Reset the IC4PSC Bits */
  tmpccmr2 &= CCMR_IC24PSC_Mask;

  /* Set the IC4PSC value */
  tmpccmr2 |= (u16)((u16)TIM_IC4Prescaler << 8);

  TIMx->CCMR2 = (u16)tmpccmr2;
}

/*******************************************************************************
* Function Name  : TIM_SetClockDivision
* Description    : Sets the TIMx Clock Division value.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_CKD: specifies the clock division value.
*                    This parameter can be one of the following value:
*                       - TIM_CKD_DIV1: TDTS = Tck_tim
*                       - TIM_CKD_DIV2: TDTS = 2*Tck_tim
*                       - TIM_CKD_DIV4: TDTS = 4*Tck_tim
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_SetClockDivision(TIM_TypeDef* TIMx, u16 TIM_CKD)
{
  u32 tmpcr1 = 0;

  /* Check the parameters */
  assert(IS_TIM_CKD_DIV(TIM_CKD));

  tmpcr1 = TIMx->CR1;

  /* Reset the CKD Bits */
  tmpcr1 &= CR1_CKD_Mask;

  /* Set the CKD value */
  tmpcr1 |= TIM_CKD;

  TIMx->CR1 = (u16)tmpcr1;
}

/*******************************************************************************
* Function Name  : TIM_GetCapture1
* Description    : Gets the TIMx Input Capture 1 value.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
* Output         : None
* Return         : Capture Compare 1 Register value.
*******************************************************************************/
u16 TIM_GetCapture1(TIM_TypeDef* TIMx)
{
  /* Get the Capture 1 Register value */
  return TIMx->CCR1;
}

/*******************************************************************************
* Function Name  : TIM_GetCapture2
* Description    : Gets the TIMx Input Capture 2 value.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
* Output         : None
* Return         : Capture Compare 2 Register value.
*******************************************************************************/
u16 TIM_GetCapture2(TIM_TypeDef* TIMx)
{
  /* Get the Capture 2 Register value */
  return TIMx->CCR2;
}

/*******************************************************************************
* Function Name  : TIM_GetCapture3
* Description    : Gets the TIMx Input Capture 3 value.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
* Output         : None
* Return         : Capture Compare 3 Register value.
*******************************************************************************/
u16 TIM_GetCapture3(TIM_TypeDef* TIMx)
{
  /* Get the Capture 3 Register value */
  return TIMx->CCR3;
}

/*******************************************************************************
* Function Name  : TIM_GetCapture4
* Description    : Gets the TIMx Input Capture 4 value.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
* Output         : None
* Return         : Capture Compare 4 Register value.
*******************************************************************************/
u16 TIM_GetCapture4(TIM_TypeDef* TIMx)
{
  /* Get the Capture 4 Register value */
  return TIMx->CCR4;
}

/*******************************************************************************
* Function Name  : TIM_GetCounter
* Description    : Gets the TIMx Counter value.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
* Output         : None
* Return         : Counter Register value.
*******************************************************************************/
u16 TIM_GetCounter(TIM_TypeDef* TIMx)
{
  /* Get the Counter Register value */
  return TIMx->CNT;
}

/*******************************************************************************
* Function Name  : TIM_GetPrescaler
* Description    : Gets the TIMx Prescaler value.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
* Output         : None
* Return         : Prescaler Register value.
*******************************************************************************/
u16 TIM_GetPrescaler(TIM_TypeDef* TIMx)
{
  /* Get the Prescaler Register value */
  return TIMx->PSC;
}

/*******************************************************************************
* Function Name  : TIM_GetFlagStatus
* Description    : Checks whether the specified TIMx flag is set or not.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_FLAG: specifies the flag to check.
*                    This parameter can be one of the following values:
*                       - TIM_FLAG_Update: Timer update Flag
*                       - TIM_FLAG_CC1: Timer Capture Compare 1 Flag
*                       - TIM_FLAG_CC2: Timer Capture Compare 2 Flag
*                       - TIM_FLAG_CC3: Timer Capture Compare 3 Flag
*                       - TIM_FLAG_CC4: Timer Capture Compare 4 Flag
*                       - TIM_FLAG_Trigger: Timer Trigger Flag
*                       - TIM_FLAG_CC1OF: Timer Capture Compare 1 overcapture Flag
*                       - TIM_FLAG_CC2OF: Timer Capture Compare 2 overcapture Flag
*                       - TIM_FLAG_CC3OF: Timer Capture Compare 3 overcapture Flag
*                       - TIM_FLAG_CC4OF: Timer Capture Compare 4 overcapture Flag
* Output         : None
* Return         : The new state of TIM_FLAG (SET or RESET).
*******************************************************************************/
FlagStatus TIM_GetFlagStatus(TIM_TypeDef* TIMx, u16 TIM_FLAG)
{
  FlagStatus bitstatus = RESET;

  /* Check the parameters */
  assert(IS_TIM_GET_FLAG(TIM_FLAG));

  if ((TIMx->SR & TIM_FLAG) != (u16)RESET )
  {
    bitstatus = SET;
  }
  else
  {
    bitstatus = RESET;
  }
  return bitstatus;
}

/*******************************************************************************
* Function Name  : TIM_ClearFlag
* Description    : Clears the TIMx's pending flags.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_FLAG: specifies the flag bit to clear.
*                    This parameter can be any combination of the following values:
*                       - TIM_FLAG_Update: Timer update Flag
*                       - TIM_FLAG_CC1: Timer Capture Compare 1 Flag
*                       - TIM_FLAG_CC2: Timer Capture Compare 2 Flag
*                       - TIM_FLAG_CC3: Timer Capture Compare 3 Flag
*                       - TIM_FLAG_CC4: Timer Capture Compare 4 Flag
*                       - TIM_FLAG_Trigger: Timer Trigger Flag
*                       - TIM_FLAG_CC1OF: Timer Capture Compare 1 overcapture Flag
*                       - TIM_FLAG_CC2OF: Timer Capture Compare 2 overcapture Flag
*                       - TIM_FLAG_CC3OF: Timer Capture Compare 3 overcapture Flag
*                       - TIM_FLAG_CC4OF: Timer Capture Compare 4 overcapture Flag
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ClearFlag(TIM_TypeDef* TIMx, u16 TIM_FLAG)
{
  /* Check the parameters */
  assert(IS_TIM_CLEAR_FLAG(TIM_FLAG));

  /* Clear the flags */
  TIMx->SR &= (u16)~TIM_FLAG;
}

/*******************************************************************************
* Function Name  : TIM_GetITStatus
* Description    : Checks whether the TIMx interrupt has occurred or not.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_IT: specifies the TIM interrupt source to check.
*                    This parameter can be one of the following values:
*                         - TIM_IT_Update: Timer update Interrupt source
*                         - TIM_IT_CC1: Timer Capture Compare 1 Interrupt source
*                         - TIM_IT_CC2: Timer Capture Compare 2 Interrupt source
*                         - TIM_IT_CC3: Timer Capture Compare 3 Interrupt source
*                         - TIM_IT_CC4: Timer Capture Compare 4 Interrupt source
*                         - TIM_IT_Trigger: Timer Trigger Interrupt source
* Output         : None
* Return         : The new state of the TIM_IT(SET or RESET).
*******************************************************************************/
ITStatus TIM_GetITStatus(TIM_TypeDef* TIMx, u16 TIM_IT)
{
  ITStatus bitstatus = RESET;
  
  u16 itstatus = 0x0, itenable = 0x0;

  /* Check the parameters */
  assert(IS_TIM_GET_IT(TIM_IT));
  
  itstatus = TIMx->SR & TIM_IT;
  
  itenable = TIMx->DIER & TIM_IT;

  if ((itstatus != (u16)RESET)  && (itenable != (u16)RESET))
  {
    bitstatus = SET;
  }
  else
  {
    bitstatus = RESET;
  }
  return bitstatus;
}

/*******************************************************************************
* Function Name  : TIM_ClearITPendingBit
* Description    : Clears the TIMx's interrupt pending bits.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_IT: specifies the pending bit to clear.
*                    This parameter can be any combination of the following values:
*                       - TIM_IT_Update: Timer update Interrupt source
*                       - TIM_IT_CC1: Timer Capture Compare 1 Interrupt source
*                       - TIM_IT_CC2: Timer Capture Compare 2 Interrupt source
*                       - TIM_IT_CC3: Timer Capture Compare 3 Interrupt source
*                       - TIM_IT_CC4: Timer Capture Compare 4 Interrupt source
*                       - TIM_IT_Trigger: Timer Trigger Interrupt source
* Output         : None
* Return         : None
*******************************************************************************/
void TIM_ClearITPendingBit(TIM_TypeDef* TIMx, u16 TIM_IT)
{
  /* Check the parameters */
  assert(IS_TIM_IT(TIM_IT));
  
  /* Clear the IT pending Bit */
  TIMx->SR &= (u16)~TIM_IT;
}

/*******************************************************************************
* Function Name  : PWMInput_Config
* Description    : Configures the TIM peripheral according to the specified
*                  parameters in the TIM_ICInitStruct to measure an external PWM
*                  signal.
* Input          : - TIM_ICInitStruct: pointer to a TIM_ICInitTypeDef structure
*                    that contains the configuration information for the specified
*                    TIM peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
static void PWMI_Config(TIM_TypeDef* TIMx, TIM_ICInitTypeDef* TIM_ICInitStruct)
{
  u8 ICPolarity = TIM_ICPolarity_Rising;
  u8 ICSelection = TIM_ICSelection_DirectTI;

  /* Select the Opposite Input Polarity */
  if (TIM_ICInitStruct->TIM_ICPolarity == TIM_ICPolarity_Rising)
  {
    ICPolarity = TIM_ICPolarity_Falling;
  }
  else
  {
    ICPolarity = TIM_ICPolarity_Rising;
  }

  /* Select the Opposite Input */
  if (TIM_ICInitStruct->TIM_ICSelection == TIM_ICSelection_DirectTI)
  {
    ICSelection = TIM_ICSelection_IndirectTI;
  }
  else
  {
    ICSelection = TIM_ICSelection_DirectTI;
  }

  if (TIM_ICInitStruct->TIM_Channel == TIM_Channel_1)
  {
    /* TI1 Configuration */
    TI1_Config(TIMx, TIM_ICInitStruct->TIM_ICPolarity, TIM_ICInitStruct->TIM_ICSelection,
               TIM_ICInitStruct->TIM_ICFilter);

    /* Set the Input Capture Prescaler value */
    TIM_SetIC1Prescaler(TIMx, TIM_ICInitStruct->TIM_ICPrescaler);

    /* TI2 Configuration */
    TI2_Config(TIMx, ICPolarity, ICSelection, TIM_ICInitStruct->TIM_ICFilter);

    /* Set the Input Capture Prescaler value */
    TIM_SetIC2Prescaler(TIMx, TIM_ICInitStruct->TIM_ICPrescaler);
  }
  else
  {	 
    /* TI1 Configuration */
    TI2_Config(TIMx, TIM_ICInitStruct->TIM_ICPolarity, TIM_ICInitStruct->TIM_ICSelection,
               TIM_ICInitStruct->TIM_ICFilter);

    /* Set the Input Capture Prescaler value */
    TIM_SetIC2Prescaler(TIMx, TIM_ICInitStruct->TIM_ICPrescaler);

    /* TI2 Configuration */
    TI1_Config(TIMx, ICPolarity, ICSelection, TIM_ICInitStruct->TIM_ICFilter);

    /* Set the Input Capture Prescaler value */
    TIM_SetIC1Prescaler(TIMx, TIM_ICInitStruct->TIM_ICPrescaler);
  }
}

/*******************************************************************************
* Function Name  : TI1_Config
* Description    : Configure the TI1 as Input.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_ICPolarity : The Input Polarity.
*                    This parameter can be one of the following values:
*                       - TIM_ICPolarity_Rising
*                       - TIM_ICPolarity_Falling
*                  - TIM_ICSelection: specifies the input to be used.
*                    This parameter can be one of the following values:
*                       - TIM_ICSelection_DirectTI: TIM Input 1 is selected to
*                         be connected to IC1.
*                       - TIM_ICSelection_IndirectTI: TIM Input 1 is selected to
*                         be connected to IC2.
*                       - TIM_ICSelection_TRGI: TIM Input 1 is selected to be
*                         connected to TRGI.
*                  - TIM_ICFilter: Specifies the Input Capture Filter.
*                    This parameter must be a value between 0x00 and 0x0F.
* Output         : None
* Return         : None
*******************************************************************************/
static void TI1_Config(TIM_TypeDef* TIMx, u16 TIM_ICPolarity, u16 TIM_ICSelection,
                       u8 TIM_ICFilter)
{
  u32 tmpccmr1 = 0, tmpccer = 0;

  tmpccmr1 = TIMx->CCMR1;
  tmpccer = TIMx->CCER;

  /* Disable the Channel 1: Reset the CCE Bit */
  TIMx->CCER &= CCRE_CC1E_Reset;

  /* Select the Input and set the filter */
  tmpccmr1 &= CCMR_CC13S_Mask & CCMR_IC13F_Mask;
  tmpccmr1 |= TIM_ICSelection | (u16)((u16)TIM_ICFilter << 4);

  /* Select the Polarity  and set the CCE Bit */
  tmpccer &= CCER_CC1P_Mask & CCRE_CC1E_Mask;
  tmpccer |= TIM_ICPolarity | CCRE_CC1E_Set;

  TIMx->CCMR1 = 0x0000;
  TIMx->CCMR1 = (u16)tmpccmr1;
  TIMx->CCER = (u16)tmpccer;
}

/*******************************************************************************
* Function Name  : TI2_Config
* Description    : Configure the TI2 as Input.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_ICPolarity : The Input Polarity.
*                    This parameter can be one of the following values:
*                       - TIM_ICPolarity_Rising
*                       - TIM_ICPolarity_Falling
*                  - TIM_ICSelection: specifies the input to be used.
*                    This parameter can be one of the following values:
*                       - TIM_ICSelection_DirectTI: TIM Input 2 is selected to
*                         be connected to IC2.
*                       - TIM_ICSelection_IndirectTI: TIM Input 2 is selected to
*                         be connected to IC1.
*                       - TIM_ICSelection_TRGI: TIM Input 2 is selected to be
*                         connected to TRGI.
*                  - TIM_ICFilter: Specifies the Input Capture Filter.
*                    This parameter must be a value between 0x00 and 0x0F.
* Output         : None
* Return         : None
*******************************************************************************/
static void TI2_Config(TIM_TypeDef* TIMx, u16 TIM_ICPolarity, u16 TIM_ICSelection,
                       u8 TIM_ICFilter)
{
  u32 tmpccmr1 = 0, tmpccer = 0, tmp = 0;

  tmpccmr1 = TIMx->CCMR1;
  tmpccer = TIMx->CCER;
  tmp = (u16)((u16)TIM_ICPolarity << 4);

  /* Disable the Channel 2: Reset the CCE Bit */
  TIMx->CCER &= CCRE_CC2E_Reset;

  /* Select the Input and set the filter */
  tmpccmr1 &= CCMR_CC24S_Mask & CCMR_IC24F_Mask;
  tmpccmr1 |= (u16)((u16)TIM_ICFilter << 12);
  tmpccmr1 |= (u16)((u16)TIM_ICSelection << 8);

  /* Select the Polarity  and set the CCE Bit */
  tmpccer &= CCER_CC2P_Mask & CCRE_CC2E_Mask;
  tmpccer |=  tmp | CCRE_CC2E_Set;

  TIMx->CCMR1 = (u16)tmpccmr1 ;
  TIMx->CCER = (u16)tmpccer;
}

/*******************************************************************************
* Function Name  : TI3_Config
* Description    : Configure the TI3 as Input.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_ICPolarity : The Input Polarity.
*                    This parameter can be one of the following values:
*                       - TIM_ICPolarity_Rising
*                       - TIM_ICPolarity_Falling
*                  - TIM_ICSelection: specifies the input to be used.
*                    This parameter can be one of the following values:
*                       - TIM_ICSelection_DirectTI: TIM Input 3 is selected to
*                         be connected to IC3.
*                       - TIM_ICSelection_IndirectTI: TIM Input 3 is selected to
*                         be connected to IC4.
*                       - TIM_ICSelection_TRGI: TIM Input 3 is selected to be
*                         connected to TRGI.
*                  - TIM_ICFilter: Specifies the Input Capture Filter.
*                    This parameter must be a value between 0x00 and 0x0F.
* Output         : None
* Return         : None
*******************************************************************************/
static void TI3_Config(TIM_TypeDef* TIMx, u16 TIM_ICPolarity, u16 TIM_ICSelection,
                       u8 TIM_ICFilter)
{
  u32 tmpccmr2 = 0, tmpccer = 0, tmp = 0;

  tmpccmr2 = TIMx->CCMR2;
  tmpccer = TIMx->CCER;
  tmp = (u16)((u16)TIM_ICPolarity << 8);

  /* Disable the Channel 3: Reset the CCE Bit */
  TIMx->CCER &= CCRE_CC3E_Reset;

  /* Select the Input and set the filter */
  tmpccmr2 &= CCMR_CC13S_Mask & CCMR_IC13F_Mask;
  tmpccmr2 |= TIM_ICSelection | (u16)((u16)TIM_ICFilter << 4);

  /* Select the Polarity  and set the CCE Bit */
  tmpccer &= CCER_CC1P_Mask & CCRE_CC1E_Mask;
  tmpccer |= tmp | CCRE_CC3E_Set;

  TIMx->CCMR2 = (u16)tmpccmr2;
  TIMx->CCER = (u16)tmpccer;
}

/*******************************************************************************
* Function Name  : TI4_Config
* Description    : Configure the TI1 as Input.
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_ICPolarity : The Input Polarity.
*                    This parameter can be one of the following values:
*                       - TIM_ICPolarity_Rising
*                       - TIM_ICPolarity_Falling
*                  - TIM_ICSelection: specifies the input to be used.
*                    This parameter can be one of the following values:
*                       - TIM_ICSelection_DirectTI: TIM Input 4 is selected to
*                         be connected to IC4.
*                       - TIM_ICSelection_IndirectTI: TIM Input 4 is selected to
*                         be connected to IC3.
*                       - TIM_ICSelection_TRGI: TIM Input 4 is selected to be
*                         connected to TRGI.
*                  - TIM_ICFilter: Specifies the Input Capture Filter.
*                    This parameter must be a value between 0x00 and 0x0F.
* Output         : None
* Return         : None
*******************************************************************************/
static void TI4_Config(TIM_TypeDef* TIMx, u16 TIM_ICPolarity, u16 TIM_ICSelection,
                       u8 TIM_ICFilter)
{
  u32 tmpccmr2 = 0, tmpccer = 0, tmp = 0;

  tmpccmr2 = TIMx->CCMR2;
  tmpccer = TIMx->CCER;
  tmp = (u16)((u16)TIM_ICPolarity << 12);

  /* Disable the Channel 4: Reset the CCE Bit */
  TIMx->CCER &= CCRE_CC4E_Reset;

  /* Select the Input and set the filter */
  tmpccmr2 &= CCMR_CC24S_Mask & CCMR_IC24F_Mask;
  tmpccmr2 |= (u16)((u16)TIM_ICSelection << 8) | (u16)((u16)TIM_ICFilter << 12);

  /* Select the Polarity  and set the CCE Bit */
  tmpccer &= CCER_CC4P_Mask & CCRE_CC4E_Mask;
  tmpccer |= tmp | CCRE_CC4E_Set;

  TIMx->CCMR2 = (u16)tmpccmr2;
  TIMx->CCER = (u16)tmpccer ;
}

/*******************************************************************************
* Function Name  : ETR_Config
* Description    : Configure the External Trigger
* Input          : - TIMx: where x can be 2, 3 or 4 to select the TIM peripheral.
*                  - TIM_ExtTRGPrescaler: The external Trigger Prescaler.
*                    This parameter can be one of the following values:
*                       - TIM_ExtTRGPSC_OFF
*                       - TIM_ExtTRGPSC_DIV2
*                       - TIM_ExtTRGPSC_DIV4
*                       - TIM_ExtTRGPSC_DIV8
*                  - TIM_ExtTRGPolarity: The external Trigger Polarity.
*                    This parameter can be one of the following values:
*                       - TIM_ExtTRGPolarity_Inverted
*                       - TIM_ExtTRGPolarity_NonInverted
*                  - ExtTRGFilter: External Trigger Filter.
*                    This parameter must be a value between 0x00 and 0x0F.
* Output         : None
* Return         : None
*******************************************************************************/
static void ETR_Config(TIM_TypeDef* TIMx, u16 TIM_ExtTRGPrescaler, u16 TIM_ExtTRGPolarity,
                       u8 ExtTRGFilter)
{
  u32 tmpsmcr = 0;

  tmpsmcr = TIMx->SMCR;

  /* Set the Prescaler, the Filter value and the Polarity */
  tmpsmcr &= SMCR_ETR_Mask;
  tmpsmcr |= TIM_ExtTRGPrescaler | TIM_ExtTRGPolarity | (u16)((u16)ExtTRGFilter << 8);

  TIMx->SMCR = (u16)tmpsmcr;
}
/******************* (C) COPYRIGHT 2007 STMicroelectronics *****END OF FILE****/
