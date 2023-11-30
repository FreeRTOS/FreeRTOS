/******************** (C) COPYRIGHT 2007 STMicroelectronics ********************
* File Name          : stm32f10x_adc.c
* Author             : MCD Application Team
* Date First Issued  : 09/29/2006
* Description        : This file provides all the ADC firmware functions.
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
#include "stm32f10x_adc.h"
#include "stm32f10x_rcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* ADC ADON mask */
#define CR2_ADON_Set               ((u32)0x00000001)
#define CR2_ADON_Reset             ((u32)0xFFFFFFFE)

/* ADC DMA mask */
#define CR2_DMA_Set                ((u16)0x0100)
#define CR2_DMA_Reset              ((u16)0xFEFF)

/* ADC RSTCAL mask */
#define CR2_RSTCAL_Set             ((u16)0x0008)

/* ADC CAL mask */
#define CR2_CAL_Set                ((u16)0x0004)

/* ADC SWSTRT mask */
#define CR2_SWSTRT_Set             ((u32)0x00400000)

/* ADC DISCNUM mask */
#define CR1_DISCNUM_Reset          ((u32)0xFFFF1FFF)

/* ADC DISCEN mask */
#define CR1_DISCEN_Set             ((u32)0x00000800)
#define CR1_DISCEN_Reset           ((u32)0xFFFFF7FF)

/* ADC EXTTRIG mask */
#define CR2_EXTTRIG_Set            ((u32)0x00100000)
#define CR2_EXTTRIG_Reset          ((u32)0xFFEFFFFF)

/* ADC Software start mask */
#define CR2_EXTTRIG_SWSTRT_Set     ((u32)0x00500000)
#define CR2_EXTTRIG_SWSTRT_Reset   ((u32)0xFFAFFFFF)

/* ADC JAUTO mask */
#define CR1_JAUTO_Set              ((u32)0x00000400)
#define CR1_JAUTO_Reset            ((u32)0xFFFFFBFF)

/* ADC JDISCEN mask */
#define CR1_JDISCEN_Set            ((u32)0x00001000)
#define CR1_JDISCEN_Reset          ((u32)0xFFFFEFFF)

/* ADC JEXTSEL mask */
#define CR2_JEXTSEL_Reset          ((u32)0xFFFF8FFF)

/* ADC JEXTTRIG mask */
#define CR2_JEXTTRIG_Set           ((u32)0x00008000)
#define CR2_JEXTTRIG_Reset         ((u32)0xFFFF7FFF)

/* ADC JSWSTRT mask */
#define CR2_JSWSTRT_Set            ((u32)0x00200000)

/* ADC injected software start mask */
#define CR2_JEXTTRIG_JSWSTRT_Set   ((u32)0x00208000)
#define CR2_JEXTTRIG_JSWSTRT_Reset ((u32)0xFFDF7FFF)

/* ADC AWDCH mask */
#define CR1_AWDCH_Reset            ((u32)0xFFFFFFE0)

/* ADC SQx mask */
#define SQR3_SQ_Set                ((u8)0x1F)
#define SQR2_SQ_Set                ((u8)0x1F)
#define SQR1_SQ_Set                ((u8)0x1F)

/* ADC JSQx mask */
#define JSQR_JSQ_Set               ((u8)0x1F)

/* ADC JL mask */
#define JSQR_JL_Reset              ((u32)0xFFCFFFFF)

/* ADC SMPx mask */
#define SMPR1_SMP_Set              ((u8)0x07)
#define SMPR2_SMP_Set              ((u8)0x07)

/* ADC Analog watchdog enable mode mask */
#define CR1_AWDMode_Reset          ((u32)0xFF3FFDFF)

/* ADC TSPD mask */
#define CR2_TSPD_Set               ((u32)0x00800000)
#define CR2_TSPD_Reset             ((u32)0xFF7FFFFF)

/* ADC JDRx registers= offset */
#define JDR_Offset                 ((u8)0x28)

/* ADC registers Masks */
#define CR1_CLEAR_Mask             ((u32)0xFFF0FEFF)
#define CR2_CLEAR_Mask             ((u32)0xFFF1F7FD)
#define SQR1_CLEAR_Mask            ((u32)0xFF0FFFFF)

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : ADC_DeInit
* Description    : Deinitializes the ADCx peripheral registers to their default
*                  reset values.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_DeInit(ADC_TypeDef* ADCx)
{
  switch (*(u32*)&ADCx)
  {
    case ADC1_BASE:
      /* Enable ADC1 reset state */
      RCC_APB2PeriphResetCmd(RCC_APB2Periph_ADC1, ENABLE);
      /* Release ADC1 from reset state */
      RCC_APB2PeriphResetCmd(RCC_APB2Periph_ADC1, DISABLE);
      break;
    
    case ADC2_BASE:
      /* Enable ADC2 reset state */
      RCC_APB2PeriphResetCmd(RCC_APB2Periph_ADC2, ENABLE);
      /* Release ADC2 from reset state */
      RCC_APB2PeriphResetCmd(RCC_APB2Periph_ADC2, DISABLE);
      break;

    default:
      break;
  }
}

/*******************************************************************************
* Function Name  : ADC_Init
* Description    : Initializes the ADCx according to the specified parameters
*                  in the ADC_InitStruct.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - ADC_InitStruct: pointer to a ADC_InitTypeDef structure that
*                    contains the configuration information for the specified
*                    ADC peripheral.
* Output         : None
* Return         : None
******************************************************************************/
void ADC_Init(ADC_TypeDef* ADCx, ADC_InitTypeDef* ADC_InitStruct)
{
  u32 tmpreg1 = 0;
  u8 tmpreg2 = 0;

  /* Check the parameters */
  assert(IS_ADC_MODE(ADC_InitStruct->ADC_Mode));
  assert(IS_FUNCTIONAL_STATE(ADC_InitStruct->ADC_ScanConvMode));
  assert(IS_FUNCTIONAL_STATE(ADC_InitStruct->ADC_ContinuousConvMode));  		    
  assert(IS_ADC_EXT_TRIG(ADC_InitStruct->ADC_ExternalTrigConv));   
  assert(IS_ADC_DATA_ALIGN(ADC_InitStruct->ADC_DataAlign)); 
  assert(IS_ADC_REGULAR_LENGTH(ADC_InitStruct->ADC_NbrOfChannel));

  /*---------------------------- ADCx CR1 Configuration -----------------*/
  /* Get the ADCx CR1 value */
  tmpreg1 = ADCx->CR1;
  /* Clear DUALMODE and SCAN bits */
  tmpreg1 &= CR1_CLEAR_Mask;
  /* Configure ADCx: Dual mode and scan conversion mode */
  /* Set DUALMODE bits according to ADC_Mode value */
  /* Set SCAN bit according to ADC_ScanConvMode value */
  tmpreg1 |= (u32)(ADC_InitStruct->ADC_Mode | ((u32)ADC_InitStruct->ADC_ScanConvMode << 8));
  /* Write to ADCx CR1 */
  ADCx->CR1 = tmpreg1;

  /*---------------------------- ADCx CR2 Configuration -----------------*/
  /* Get the ADCx CR2 value */
  tmpreg1 = ADCx->CR2;
  /* Clear CONT, ALIGN and EXTTRIG bits */
  tmpreg1 &= CR2_CLEAR_Mask;
  /* Configure ADCx: external trigger event and continuous conversion mode */
  /* Set ALIGN bit according to ADC_DataAlign value */
  /* Set EXTTRIG bits according to ADC_ExternalTrigConv value */
  /* Set CONT bit according to ADC_ContinuousConvMode value */
  tmpreg1 |= (u32)(ADC_InitStruct->ADC_DataAlign | ADC_InitStruct->ADC_ExternalTrigConv |
            ((u32)ADC_InitStruct->ADC_ContinuousConvMode << 1));
  /* Write to ADCx CR2 */
  ADCx->CR2 = tmpreg1;

  /*---------------------------- ADCx SQR1 Configuration -----------------*/
  /* Get the ADCx SQR1 value */
  tmpreg1 = ADCx->SQR1;
  /* Clear L bits */
  tmpreg1 &= SQR1_CLEAR_Mask;
  /* Configure ADCx: regular channel sequence length */
  /* Set L bits according to ADC_NbrOfChannel value */
  tmpreg2 |= (ADC_InitStruct->ADC_NbrOfChannel - 1);
  tmpreg1 |= ((u32)tmpreg2 << 20);
  /* Write to ADCx SQR1 */
  ADCx->SQR1 = tmpreg1;
}

/*******************************************************************************
* Function Name  : ADC_StructInit
* Description    : Fills each ADC_InitStruct member with its default value.
* Input          : ADC_InitStruct : pointer to a ADC_InitTypeDef structure
*                  which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_StructInit(ADC_InitTypeDef* ADC_InitStruct)
{
  /* Reset ADC init structure parameters values */
  /* Initialize the ADC_Mode member */
  ADC_InitStruct->ADC_Mode = ADC_Mode_Independent;

  /* initialize the ADC_ScanConvMode member */
  ADC_InitStruct->ADC_ScanConvMode = DISABLE;

  /* Initialize the ADC_ContinuousConvMode member */
  ADC_InitStruct->ADC_ContinuousConvMode = DISABLE;

  /* Initialize the ADC_ExternalTrigConv member */
  ADC_InitStruct->ADC_ExternalTrigConv = ADC_ExternalTrigConv_T1_CC1;

  /* Initialize the ADC_DataAlign member */
  ADC_InitStruct->ADC_DataAlign = ADC_DataAlign_Right;

  /* Initialize the ADC_NbrOfChannel member */
  ADC_InitStruct->ADC_NbrOfChannel = 1;
}

/*******************************************************************************
* Function Name  : ADC_Cmd
* Description    : Enables or disables the specified ADC peripheral.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - NewState: new state of the ADCx peripheral. This parameter
*                    can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_Cmd(ADC_TypeDef* ADCx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Set the ADON bit to wake up the ADC from power down mode */
    ADCx->CR2 |= CR2_ADON_Set;
  }
  else
  {
    /* Disable the selected ADC peripheral */
    ADCx->CR2 &= CR2_ADON_Reset;
  }
}

/*******************************************************************************
* Function Name  : ADC_DMACmd
* Description    : Enables or disables the specified ADC DMA request.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - NewState: new state of the selected ADC DMA transfer.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_DMACmd(ADC_TypeDef* ADCx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the selected ADC DMA request */
    ADCx->CR2 |= CR2_DMA_Set;
  }
  else
  {
    /* Disable the selected ADC DMA request */
    ADCx->CR2 &= CR2_DMA_Reset;
  }
}

/*******************************************************************************
* Function Name  : ADC_ITConfig
* Description    : Enables or disables the specified ADC interrupts.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - ADC_IT: specifies the ADC interrupts sources to be enabled
*                    or disabled. 
*                    This parameter can be any combination of the following values:
*                       - ADC_IT_EOC: End of conversion interrupt mask
*                       - ADC_IT_AWD: Analog watchdog interrupt mask
*                       - ADC_IT_JEOC: End of injected conversion interrupt mask
*                  - NewState: new state of the specified ADC interrupts.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_ITConfig(ADC_TypeDef* ADCx, u16 ADC_IT, FunctionalState NewState)
{
  u8 itmask = 0;

  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));
  assert(IS_ADC_IT(ADC_IT));

  /* Get the ADC IT index */
  itmask = (u8)ADC_IT;

  if (NewState != DISABLE)
  {
    /* Enable the selected ADC interrupts */
    ADCx->CR1 |= itmask;
  }
  else
  {
    /* Disable the selected ADC interrupts */
    ADCx->CR1 &= (~(u32)itmask);
  }
}

/*******************************************************************************
* Function Name  : ADC_ResetCalibration
* Description    : Resets the ADC calibration registers.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_ResetCalibration(ADC_TypeDef* ADCx)
{
  /* Resets the selected ADC calibartion registers */  
  ADCx->CR2 |= CR2_RSTCAL_Set;
}

/*******************************************************************************
* Function Name  : ADC_GetResetCalibrationStatus
* Description    : Gets the ADC reset calibration registers status.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
* Output         : None
* Return         : The new state of ADC Reset Calibration registers (SET or RESET).
*******************************************************************************/
FlagStatus ADC_GetResetCalibrationStatus(ADC_TypeDef* ADCx)
{
  FlagStatus bitstatus = RESET;

  /* Check the status of RSTCAL bit */
  if ((ADCx->CR2 & CR2_RSTCAL_Set) != (u16)RESET)
  {
    /* RSTCAL bit is set */
    bitstatus = SET;
  }
  else
  {
    /* RSTCAL bit is reset */
    bitstatus = RESET;
  }
  /* Return the RSTCAL bit status */
  return  bitstatus;
}

/*******************************************************************************
* Function Name  : ADC_StartCalibration
* Description    : Starts the calibration process.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_StartCalibration(ADC_TypeDef* ADCx)
{
  /* Enable the selected ADC calibration process */  
  ADCx->CR2 |= CR2_CAL_Set;
}

/*******************************************************************************
* Function Name  : ADC_GetCalibrationStatus
* Description    : Gets the ADC calibration status.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
* Output         : None
* Return         : The new state of ADC calibration (SET or RESET).
*******************************************************************************/
FlagStatus ADC_GetCalibrationStatus(ADC_TypeDef* ADCx)
{
  FlagStatus bitstatus = RESET;

  /* Check the status of CAL bit */
  if ((ADCx->CR2 & CR2_CAL_Set) != (u16)RESET)
  {
    /* CAL bit is set: calibration on going */
    bitstatus = SET;
  }
  else
  {
    /* CAL bit is reset: end of calibration */
    bitstatus = RESET;
  }
  /* Return the CAL bit status */
  return  bitstatus;
}

/*******************************************************************************
* Function Name  : ADC_SoftwareStartConvCmd
* Description    : Enables or disables the ADC software start conversion .
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - NewState: new state of the selected ADC software start conversion.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_SoftwareStartConvCmd(ADC_TypeDef* ADCx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the selected ADC conversion on external event */
	/* Starts the selected ADC conversion */
	ADCx->CR2 |= CR2_EXTTRIG_SWSTRT_Set;
  }
  else
  {
    /* Stops the selected ADC conversion */
    /* Disable the selected ADC conversion on external event */
	ADCx->CR2 &= CR2_EXTTRIG_SWSTRT_Reset;
  }
}

/*******************************************************************************
* Function Name  : ADC_GetSoftwareStartConvStatus
* Description    : Gets the ADC Software start conversion Status.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
* Output         : None
* Return         : The new state of ADC software start conversion (SET or RESET).
*******************************************************************************/
FlagStatus ADC_GetSoftwareStartConvStatus(ADC_TypeDef* ADCx)
{
  FlagStatus bitstatus = RESET;

  /* Check the status of SWSTRT bit */
  if ((ADCx->CR2 & CR2_SWSTRT_Set) != (u32)RESET)
  {
    /* SWSTRT bit is set */
    bitstatus = SET;
  }
  else
  {
    /* SWSTRT bit is reset */
    bitstatus = RESET;
  }
  /* Return the SWSTRT bit status */
  return  bitstatus;
}

/*******************************************************************************
* Function Name  : ADC_DiscModeChannelCountConfig
* Description    : Configures the discontinuous mode for the selected ADC regular
*                  group channel.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - Number: specifies the discontinuous mode regular channel
*                    count value. This mumber must be between 1 and 8.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_DiscModeChannelCountConfig(ADC_TypeDef* ADCx, u8 Number)
{
  u32 tmpreg1 = 0;
  u8 tmpreg2 = 0;

  /* Check the parameters */
  assert(IS_ADC_REGULAR_DISC_NUMBER(Number));

  /* Get the old register value */
  tmpreg1 = ADCx->CR1;
  /* Clear the old discontinuous mode channel count */
  tmpreg1 &= CR1_DISCNUM_Reset;
  /* Set the discontinuous mode channel count */
  tmpreg2 = Number - 1;
  tmpreg1 |= ((u32)tmpreg2 << 13);
  /* Store the new register value */
  ADCx->CR1 = tmpreg1;
}

/*******************************************************************************
* Function Name  : ADC_DiscModeCmd
* Description    : Enables or disables the discontinuous mode on regular group
*                  channel for the specified ADC
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - NewState: new state of the selected ADC discontinuous mode
*                    on regular group channel.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_DiscModeCmd(ADC_TypeDef* ADCx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the selected ADC regular discontinuous mode */
    ADCx->CR1 |= CR1_DISCEN_Set;
  }
  else
  {
    /* Disable the selected ADC regular discontinuous mode */
    ADCx->CR1 &= CR1_DISCEN_Reset;
  }
}

/*******************************************************************************
* Function Name  : ADC_RegularChannelConfig
* Description    : Configures for the selected ADC regular channel its corresponding
*                  rank in the sequencer and its sample time.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - ADC_Channel: the ADC channel to configure. 
*                    This parameter can be one of the following values:
*                       - ADC_Channel_0: ADC Channel0 selected
*                       - ADC_Channel_1: ADC Channel1 selected
*                       - ADC_Channel_2: ADC Channel2 selected
*                       - ADC_Channel_3: ADC Channel3 selected
*                       - ADC_Channel_4: ADC Channel4 selected
*                       - ADC_Channel_5: ADC Channel5 selected
*                       - ADC_Channel_6: ADC Channel6 selected
*                       - ADC_Channel_7: ADC Channel7 selected
*                       - ADC_Channel_8: ADC Channel8 selected
*                       - ADC_Channel_9: ADC Channel9 selected
*                       - ADC_Channel_10: ADC Channel10 selected
*                       - ADC_Channel_11: ADC Channel11 selected
*                       - ADC_Channel_12: ADC Channel12 selected
*                       - ADC_Channel_13: ADC Channel13 selected
*                       - ADC_Channel_14: ADC Channel14 selected
*                       - ADC_Channel_15: ADC Channel15 selected
*                       - ADC_Channel_16: ADC Channel16 selected
*                       - ADC_Channel_17: ADC Channel17 selected
*                  - Rank: The rank in the regular group sequencer. This parameter
*                    must be between 1 to 16.
*                  - ADC_SampleTime: The sample time value to be set for the
*                    selected channel. 
*                    This parameter can be one of the following values:
*                       - ADC_SampleTime_1Cycles5: Sample time equal to 1.5 cycles
*                       - ADC_SampleTime_7Cycles5: Sample time equal to 7.5 cycles
*                       - ADC_SampleTime_13Cycles5: Sample time equal to 13.5 cycles
*                       - ADC_SampleTime_28Cycles5: Sample time equal to 28.5 cycles	
*                       - ADC_SampleTime_41Cycles5: Sample time equal to 41.5 cycles	
*                       - ADC_SampleTime_55Cycles5: Sample time equal to 55.5 cycles	
*                       - ADC_SampleTime_71Cycles5: Sample time equal to 71.5 cycles	
*                       - ADC_SampleTime_239Cycles5: Sample time equal to 239.5 cycles	
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_RegularChannelConfig(ADC_TypeDef* ADCx, u8 ADC_Channel, u8 Rank, u8 ADC_SampleTime)
{
  u32 tmpreg1 = 0, tmpreg2 = 0;

  /* Check the parameters */
  assert(IS_ADC_CHANNEL(ADC_Channel));
  assert(IS_ADC_REGULAR_RANK(Rank));
  assert(IS_ADC_SAMPLE_TIME(ADC_SampleTime));

  /* if ADC_Channel_10 ... ADC_Channel_17 is selected */
  if (ADC_Channel > ADC_Channel_9)
  {
    /* Get the old register value */
    tmpreg1 = ADCx->SMPR1;
    /* Calculate the mask to clear */
    tmpreg2 = (u32)SMPR1_SMP_Set << (3 * (ADC_Channel - 10));
    /* Clear the old discontinuous mode channel count */
    tmpreg1 &= ~tmpreg2;
    /* Calculate the mask to set */
    tmpreg2 = (u32)ADC_SampleTime << (3 * (ADC_Channel - 10));
    /* Set the discontinuous mode channel count */
    tmpreg1 |= tmpreg2;
    /* Store the new register value */
    ADCx->SMPR1 = tmpreg1;
  }
  else /* ADC_Channel include in ADC_Channel_[0..9] */
  {
    /* Get the old register value */
    tmpreg1 = ADCx->SMPR2;
    /* Calculate the mask to clear */
    tmpreg2 = (u32)SMPR2_SMP_Set << (3 * ADC_Channel);
    /* Clear the old discontinuous mode channel count */
    tmpreg1 &= ~tmpreg2;
    /* Calculate the mask to set */
    tmpreg2 = (u32)ADC_SampleTime << (3 * ADC_Channel);
    /* Set the discontinuous mode channel count */
    tmpreg1 |= tmpreg2;
    /* Store the new register value */
    ADCx->SMPR2 = tmpreg1;
  }
  /* For Rank 1 to 6 */
  if (Rank < 7)
  {
    /* Get the old register value */
    tmpreg1 = ADCx->SQR3;
    /* Calculate the mask to clear */
    tmpreg2 = (u32)SQR3_SQ_Set << (5 * (Rank - 1));
    /* Clear the old SQx bits for the selected rank */
    tmpreg1 &= ~tmpreg2;
    /* Calculate the mask to set */
    tmpreg2 = (u32)ADC_Channel << (5 * (Rank - 1));
    /* Set the SQx bits for the selected rank */
    tmpreg1 |= tmpreg2;
    /* Store the new register value */
    ADCx->SQR3 = tmpreg1;
  }
  /* For Rank 7 to 12 */
  else if (Rank < 13)
  {
    /* Get the old register value */
    tmpreg1 = ADCx->SQR2;
    /* Calculate the mask to clear */
    tmpreg2 = (u32)SQR2_SQ_Set << (5 * (Rank - 7));
    /* Clear the old SQx bits for the selected rank */
    tmpreg1 &= ~tmpreg2;
    /* Calculate the mask to set */
    tmpreg2 = (u32)ADC_Channel << (5 * (Rank - 7));
    /* Set the SQx bits for the selected rank */
    tmpreg1 |= tmpreg2;
    /* Store the new register value */
    ADCx->SQR2 = tmpreg1;
  }
  /* For Rank 13 to 16 */
  else
  {
    /* Get the old register value */
    tmpreg1 = ADCx->SQR1;
    /* Calculate the mask to clear */
    tmpreg2 = (u32)SQR1_SQ_Set << (5 * (Rank - 13));
    /* Clear the old SQx bits for the selected rank */
    tmpreg1 &= ~tmpreg2;
    /* Calculate the mask to set */
    tmpreg2 = (u32)ADC_Channel << (5 * (Rank - 13));
    /* Set the SQx bits for the selected rank */
    tmpreg1 |= tmpreg2;
    /* Store the new register value */
    ADCx->SQR1 = tmpreg1;
  }
}

/*******************************************************************************
* Function Name  : ADC_ExternalTrigConvCmd
* Description    : Enables or disables the ADCx conversion through external trigger.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - NewState: new state of the selected ADC external trigger
*                    start of conversion.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_ExternalTrigConvCmd(ADC_TypeDef* ADCx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the selected ADC conversion on external event */
    ADCx->CR2 |= CR2_EXTTRIG_Set;
  }
  else
  {
    /* Disable the selected ADC conversion on external event */
    ADCx->CR2 &= CR2_EXTTRIG_Reset;
  }
}

/*******************************************************************************
* Function Name  : ADC_GetConversionValue
* Description    : Returns the last ADC conversion result data for regular channel.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
* Output         : None
* Return         : The Data conversion value.
*******************************************************************************/
u16 ADC_GetConversionValue(ADC_TypeDef* ADCx)
{
  /* Return the selected ADC conversion value */
  return (u16) ADCx->DR;
}

/*******************************************************************************
* Function Name  : ADC_GetDualModeConversionValue
* Description    : Returns the last ADCs conversion result data in dual mode.
* Output         : None
* Return         : The Data conversion value.
*******************************************************************************/
u32 ADC_GetDualModeConversionValue(void)
{
  /* Return the dual mode conversion value */
  return ADC1->DR;
}

/*******************************************************************************
* Function Name  : ADC_AutoInjectedConvCmd
* Description    : Enables or disables the automatic injected group conversion
*                  after regular one.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - NewState: new state of the selected ADC auto injected
*                    conversion
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_AutoInjectedConvCmd(ADC_TypeDef* ADCx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the selected ADC automatic injected group conversion */
    ADCx->CR1 |= CR1_JAUTO_Set;
  }
  else
  {
    /* Disable the selected ADC automatic injected group conversion */
    ADCx->CR1 &= CR1_JAUTO_Reset;
  }
}

/*******************************************************************************
* Function Name  : ADC_InjectedDiscModeCmd
* Description    : Enables or disables the discontinuous mode for injected group
*                  channel for the specified ADC
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - NewState: new state of the selected ADC discontinuous mode
*                    on injected group channel.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_InjectedDiscModeCmd(ADC_TypeDef* ADCx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the selected ADC injected discontinuous mode */
    ADCx->CR1 |= CR1_JDISCEN_Set;
  }
  else
  {
    /* Disable the selected ADC injected discontinuous mode */
    ADCx->CR1 &= CR1_JDISCEN_Reset;
  }
}

/*******************************************************************************
* Function Name  : ADC_ExternalTrigInjectedConvConfig
* Description    : Configures the external trigger for injected channels conversion.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - ADC_ExternalTrigInjecConv: specifies the ADC trigger to
*                    start injected conversion. 
*                    This parameter can be one of the following values:
*                       - ADC_ExternalTrigInjecConv_T1_TRGO: Timer1 TRGO event 
*                         selected
*                       - ADC_ExternalTrigInjecConv_T1_CC4: Timer1 capture
*                         compare4 selected
*                       - ADC_ExternalTrigInjecConv_T2_TRGO: Timer2 TRGO event
*                         selected
*                       - ADC_ExternalTrigInjecConv_T2_CC1: Timer2 capture
*                         compare1 selected
*                       - ADC_ExternalTrigInjecConv_T3_CC4: Timer3 capture
*                         compare4 selected
*                       - ADC_ExternalTrigInjecConv_T4_TRGO: Timer4 TRGO event
*                         selected 
*                       - ADC_ExternalTrigInjecConv_Ext_Interrupt15: External
*                         interrupt 15 event selected
*                       - ADC_ExternalTrigInjecConv_None: Injected conversion
*                         started by software and not by external trigger
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_ExternalTrigInjectedConvConfig(ADC_TypeDef* ADCx, u32 ADC_ExternalTrigInjecConv)
{
  u32 tmpreg = 0;

  /* Check the parameters */
  assert(IS_ADC_EXT_INJEC_TRIG(ADC_ExternalTrigInjecConv));

  /* Get the old register value */
  tmpreg = ADCx->CR2;
  /* Clear the old external event selection for injected group */
  tmpreg &= CR2_JEXTSEL_Reset;
  /* Set the external event selection for injected group */
  tmpreg |= ADC_ExternalTrigInjecConv;
  /* Store the new register value */
  ADCx->CR2 = tmpreg;
}

/*******************************************************************************
* Function Name  : ADC_ExternalTrigInjectedConvCmd
* Description    : Enables or disables the ADCx injected channels conversion
*                  through external trigger
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - NewState: new state of the selected ADC external trigger
*                    start of injected conversion.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_ExternalTrigInjectedConvCmd(ADC_TypeDef* ADCx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the selected ADC external event selection for injected group */
    ADCx->CR2 |= CR2_JEXTTRIG_Set;
  }
  else
  {
    /* Disable the selected ADC external event selection for injected group */
    ADCx->CR2 &= CR2_JEXTTRIG_Reset;
  }
}

/*******************************************************************************
* Function Name  : ADC_SoftwareStartInjectedConvCmd
* Description    : Enables or disables the start of the injected channels conversion.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - NewState: new state of the selected ADC software start
*                    injected conversion.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_SoftwareStartInjectedConvCmd(ADC_TypeDef* ADCx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the selected ADC external event selection for injected group */
    /* Starts the selected ADC injected conversion */
    ADCx->CR2 |= CR2_JEXTTRIG_JSWSTRT_Set;
  }
  else
  {
    /* Stops the selected ADC injected conversion */
    /* Disable the selected ADC external event selection for injected group */
	ADCx->CR2 &= CR2_JEXTTRIG_JSWSTRT_Reset;
  }
}

/*******************************************************************************
* Function Name  : ADC_GetSoftwareStartInjectedConvCmdStatus
* Description    : Gets the ADC Software start injected conversion Status.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
* Output         : None
* Return         : The new state of ADC software start injected conversion (SET or RESET).
*******************************************************************************/
FlagStatus ADC_GetSoftwareStartInjectedConvCmdStatus(ADC_TypeDef* ADCx)
{
  FlagStatus bitstatus = RESET;

  /* Check the status of JSWSTRT bit */
  if ((ADCx->CR2 & CR2_JSWSTRT_Set) != (u32)RESET)
  {
    /* JSWSTRT bit is set */
    bitstatus = SET;
  }
  else
  {
    /* JSWSTRT bit is reset */
    bitstatus = RESET;
  }
  /* Return the JSWSTRT bit status */
  return  bitstatus;
}

/*******************************************************************************
* Function Name  : ADC_InjectedChannelConfig
* Description    : Configures for the selected ADC injected channel its corresponding
*                  rank in the sequencer and its sample time.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - ADC_Channel: the ADC channel to configure. 
*                    This parameter can be one of the following values:
*                       - ADC_Channel_0: ADC Channel0 selected
*                       - ADC_Channel_1: ADC Channel1 selected
*                       - ADC_Channel_2: ADC Channel2 selected
*                       - ADC_Channel_3: ADC Channel3 selected
*                       - ADC_Channel_4: ADC Channel4 selected
*                       - ADC_Channel_5: ADC Channel5 selected
*                       - ADC_Channel_6: ADC Channel6 selected
*                       - ADC_Channel_7: ADC Channel7 selected
*                       - ADC_Channel_8: ADC Channel8 selected
*                       - ADC_Channel_9: ADC Channel9 selected
*                       - ADC_Channel_10: ADC Channel10 selected
*                       - ADC_Channel_11: ADC Channel11 selected
*                       - ADC_Channel_12: ADC Channel12 selected
*                       - ADC_Channel_13: ADC Channel13 selected
*                       - ADC_Channel_14: ADC Channel14 selected
*                       - ADC_Channel_15: ADC Channel15 selected
*                       - ADC_Channel_16: ADC Channel16 selected
*                       - ADC_Channel_17: ADC Channel17 selected
*                  - Rank: The rank in the injected group sequencer. This parameter
*                    must be between 1 to 4.
*                  - ADC_SampleTime: The sample time value to be set for the
*                    selected channel. 
*                    This parameter can be one of the following values:
*                       - ADC_SampleTime_1Cycles5: Sample time equal to 1.5 cycles
*                       - ADC_SampleTime_7Cycles5: Sample time equal to 7.5 cycles
*                       - ADC_SampleTime_13Cycles5: Sample time equal to 13.5 cycles
*                       - ADC_SampleTime_28Cycles5: Sample time equal to 28.5 cycles	
*                       - ADC_SampleTime_41Cycles5: Sample time equal to 41.5 cycles	
*                       - ADC_SampleTime_55Cycles5: Sample time equal to 55.5 cycles	
*                       - ADC_SampleTime_71Cycles5: Sample time equal to 71.5 cycles	
*                       - ADC_SampleTime_239Cycles5: Sample time equal to 239.5 cycles	
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_InjectedChannelConfig(ADC_TypeDef* ADCx, u8 ADC_Channel, u8 Rank, u8 ADC_SampleTime)
{
  u32 tmpreg1 = 0, tmpreg2 = 0;
  u8 tmpreg3 = 0;

  /* Check the parameters */
  assert(IS_ADC_CHANNEL(ADC_Channel));
  assert(IS_ADC_INJECTED_RANK(Rank));
  assert(IS_ADC_SAMPLE_TIME(ADC_SampleTime));

  /* if ADC_Channel_10 ... ADC_Channel_17 is selected */
  if (ADC_Channel > ADC_Channel_9)
  {
    /* Get the old register value */
    tmpreg1 = ADCx->SMPR1;
    /* Calculate the mask to clear */
    tmpreg2 = (u32)SMPR1_SMP_Set << (3*(ADC_Channel - 10));
    /* Clear the old discontinuous mode channel count */
    tmpreg1 &= ~tmpreg2;
    /* Calculate the mask to set */
    tmpreg2 = (u32)ADC_SampleTime << (3*(ADC_Channel - 10));
    /* Set the discontinuous mode channel count */
    tmpreg1 |= tmpreg2;
    /* Store the new register value */
    ADCx->SMPR1 = tmpreg1;
  }
  else /* ADC_Channel include in ADC_Channel_[0..9] */
  {
    /* Get the old register value */
    tmpreg1 = ADCx->SMPR2;
    /* Calculate the mask to clear */
    tmpreg2 = (u32)SMPR2_SMP_Set << (3 * ADC_Channel);
    /* Clear the old discontinuous mode channel count */
    tmpreg1 &= ~tmpreg2;
    /* Calculate the mask to set */
    tmpreg2 = (u32)ADC_SampleTime << (3 * ADC_Channel);
    /* Set the discontinuous mode channel count */
    tmpreg1 |= tmpreg2;
    /* Store the new register value */
    ADCx->SMPR2 = tmpreg1;
  }

  /* Rank configuration */
  /* Get the old register value */
  tmpreg1 = ADCx->JSQR;
  /* Get JL value: Number = JL+1 */
  tmpreg3 =  (u8)((tmpreg1 & (u32)~JSQR_JL_Reset)>> 20);
  /* Calculate the mask to clear: ((Rank-1)+(4-JL-1)) */
  tmpreg2 = (u32)JSQR_JSQ_Set << (5 * ((Rank + 3) - (tmpreg3 + 1)));
  /* Clear the old JSQx bits for the selected rank */
  tmpreg1 &= ~tmpreg2;
  /* Calculate the mask to set: ((Rank-1)+(4-JL-1)) */
  tmpreg2 = (u32)ADC_Channel << (5 * ((Rank + 3) - (tmpreg3 + 1)));
  /* Set the JSQx bits for the selected rank */
  tmpreg1 |= tmpreg2;
  /* Store the new register value */
  ADCx->JSQR = tmpreg1;
}

/*******************************************************************************
* Function Name  : ADC_InjectedSequencerLengthConfig
* Description    : Configures the sequencer for injected channels
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - Length: The sequencer length. 
*                    This parameter must be a number between 1 to 4.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_InjectedSequencerLengthConfig(ADC_TypeDef* ADCx, u8 Length)
{
  u32 tmpreg1 = 0;
  u8 tmpreg2 = 0;

  /* Check the parameters */
  assert(IS_ADC_INJECTED_LENGTH(Length));
  
  /* Get the old register value */
  tmpreg1 = ADCx->JSQR;
  /* Clear the old injected sequnence lenght JL bits */
  tmpreg1 &= JSQR_JL_Reset;
  /* Set the injected sequnence lenght JL bits */
  tmpreg2 = Length - 1; 
  tmpreg1 |= (u32)tmpreg2 << 20;
  /* Store the new register value */
  ADCx->JSQR = tmpreg1;
}

/*******************************************************************************
* Function Name  : ADC_SetInjectedOffset
* Description    : Set the injected channels conversion value offset
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - ADC_InjectedChannel: the ADC injected channel to set its
*                    offset. 
*                    This parameter can be one of the following values:
*                       - ADC_InjectedChannel_1: Injected Channel1 selected
*                       - ADC_InjectedChannel_2: Injected Channel2 selected
*                       - ADC_InjectedChannel_3: Injected Channel3 selected
*                       - ADC_InjectedChannel_4: Injected Channel4 selected
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_SetInjectedOffset(ADC_TypeDef* ADCx, u8 ADC_InjectedChannel, u16 Offset)
{
  /* Check the parameters */
  assert(IS_ADC_INJECTED_CHANNEL(ADC_InjectedChannel));
  assert(IS_ADC_OFFSET(Offset));  

  /* Set the selected injected channel data offset */
  *((u32 *)((*(u32*)&ADCx) + ADC_InjectedChannel)) = (u32)Offset;
}

/*******************************************************************************
* Function Name  : ADC_GetInjectedConversionValue
* Description    : Returns the ADC conversion result data for the selected
*                  injected channel
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - ADC_InjectedChannel: the converted ADC injected channel.
*                    This parameter can be one of the following values:
*                       - ADC_InjectedChannel_1: Injected Channel1 selected
*                       - ADC_InjectedChannel_2: Injected Channel2 selected
*                       - ADC_InjectedChannel_3: Injected Channel3 selected
*                       - ADC_InjectedChannel_4: Injected Channel4 selected
* Output         : None
* Return         : The Data conversion value.
*******************************************************************************/
u16 ADC_GetInjectedConversionValue(ADC_TypeDef* ADCx, u8 ADC_InjectedChannel)
{
  /* Check the parameters */
  assert(IS_ADC_INJECTED_CHANNEL(ADC_InjectedChannel));

  /* Returns the selected injected channel conversion data value */
  return (u16) (*(u32*) (((*(u32*)&ADCx) + ADC_InjectedChannel + JDR_Offset)));
}

/*******************************************************************************
* Function Name  : ADC_AnalogWatchdogCmd
* Description    : Enables or disables the analog watchdog on single/all regular
*                  or injected channels
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - ADC_AnalogWatchdog: the ADC analog watchdog configuration.
*                    This parameter can be one of the following values:
*                       - ADC_AnalogWatchdog_SingleRegEnable: Analog watchdog on
*                         a single regular channel
*                       - ADC_AnalogWatchdog_SingleInjecEnable: Analog watchdog on
*                         a single injected channel
*                       - ADC_AnalogWatchdog_SingleRegOrInjecEnable: Analog 
*                         watchdog on a single regular or injected channel
*                       - ADC_AnalogWatchdog_AllRegEnable: Analog watchdog on
*                         all regular channel
*                       - ADC_AnalogWatchdog_AllInjecEnable: Analog watchdog on
*                         all injected channel
*                       - ADC_AnalogWatchdog_AllRegAllInjecEnable: Analog watchdog
*                         on all regular and injected channels
*                       - ADC_AnalogWatchdog_None: No channel guarded by the
*                         analog watchdog
* Output         : None
* Return         : None	  
*******************************************************************************/
void ADC_AnalogWatchdogCmd(ADC_TypeDef* ADCx, u32 ADC_AnalogWatchdog)
{
  u32 tmpreg = 0;

  /* Check the parameters */
  assert(IS_ADC_ANALOG_WATCHDOG(ADC_AnalogWatchdog));

  /* Get the old register value */
  tmpreg = ADCx->CR1;
  /* Clear AWDEN, AWDENJ and AWDSGL bits */
  tmpreg &= CR1_AWDMode_Reset;
  /* Set the analog watchdog enable mode */
  tmpreg |= ADC_AnalogWatchdog;
  /* Store the new register value */
  ADCx->CR1 = tmpreg;
}

/*******************************************************************************
* Function Name  : ADC_AnalogWatchdogThresholdsConfig
* Description    : Configures the High and low thresholds of the analog watchdog.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - HighThreshold: the ADC analog watchdog High threshold value.
*                    This parameter must be a 12bit value.
*                  - LowThreshold: the ADC analog watchdog Low threshold value.
*                    This parameter must be a 12bit value.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_AnalogWatchdogThresholdsConfig(ADC_TypeDef* ADCx, u16 HighThreshold,
                                        u16 LowThreshold)
{
  /* Check the parameters */
  assert(IS_ADC_THRESHOLD(HighThreshold));
  assert(IS_ADC_THRESHOLD(LowThreshold));

  /* Set the ADCx high threshold */
  ADCx->HTR = HighThreshold;
  /* Set the ADCx low threshold */
  ADCx->LTR = LowThreshold;
}

/*******************************************************************************
* Function Name  : ADC_AnalogWatchdogSingleChannelConfig
* Description    : Configures the analog watchdog guarded single channel
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - ADC_Channel: the ADC channel to configure for the analog
*                    watchdog. 
*                    This parameter can be one of the following values:
*                       - ADC_Channel_0: ADC Channel0 selected
*                       - ADC_Channel_1: ADC Channel1 selected
*                       - ADC_Channel_2: ADC Channel2 selected
*                       - ADC_Channel_3: ADC Channel3 selected
*                       - ADC_Channel_4: ADC Channel4 selected
*                       - ADC_Channel_5: ADC Channel5 selected
*                       - ADC_Channel_6: ADC Channel6 selected
*                       - ADC_Channel_7: ADC Channel7 selected
*                       - ADC_Channel_8: ADC Channel8 selected
*                       - ADC_Channel_9: ADC Channel9 selected
*                       - ADC_Channel_10: ADC Channel10 selected
*                       - ADC_Channel_11: ADC Channel11 selected
*                       - ADC_Channel_12: ADC Channel12 selected
*                       - ADC_Channel_13: ADC Channel13 selected
*                       - ADC_Channel_14: ADC Channel14 selected
*                       - ADC_Channel_15: ADC Channel15 selected
*                       - ADC_Channel_16: ADC Channel16 selected
*                       - ADC_Channel_17: ADC Channel17 selected
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_AnalogWatchdogSingleChannelConfig(ADC_TypeDef* ADCx, u8 ADC_Channel)
{
  u32 tmpreg = 0;

  /* Check the parameters */
  assert(IS_ADC_CHANNEL(ADC_Channel));

  /* Get the old register value */
  tmpreg = ADCx->CR1;
  /* Clear the Analog watchdog channel select bits */
  tmpreg &= CR1_AWDCH_Reset;
  /* Set the Analog watchdog channel */
  tmpreg |= ADC_Channel;
  /* Store the new register value */
  ADCx->CR1 = tmpreg;
}

/*******************************************************************************
* Function Name  : ADC_TempSensorCmd
* Description    : Enables or disables the temperature sensor.
* Input          : - NewState: new state of the temperature sensor.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_TempSensorCmd(FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the temperature sensor  */
    ADC1->CR2 |= CR2_TSPD_Set;
  }
  else
  {
    /* Disable the temperature sensor */
	ADC1->CR2 &= CR2_TSPD_Reset;
  }
}

/*******************************************************************************
* Function Name  : ADC_GetFlagStatus
* Description    : Checks whether the specified ADC flag is set or not.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - ADC_FLAG: specifies the flag to check. 
*                    This parameter can be one of the following values:
*                       - ADC_FLAG_AWD: Analog watchdog flag
*                       - ADC_FLAG_EOC: End of conversion flag
*                       - ADC_FLAG_JEOC: End of injected group conversion flag
*                       - ADC_FLAG_JSTRT: Start of injected group conversion flag
*                       - ADC_FLAG_STRT: Start of regular group conversion flag
* Output         : None
* Return         : The new state of ADC_FLAG (SET or RESET).
*******************************************************************************/
FlagStatus ADC_GetFlagStatus(ADC_TypeDef* ADCx, u8 ADC_FLAG)
{
  FlagStatus bitstatus = RESET;

  /* Check the parameters */
  assert(IS_ADC_GET_FLAG(ADC_FLAG));

  /* Check the status of the specified ADC flag */
  if ((ADCx->SR & ADC_FLAG) != (u8)RESET)
  {
    /* ADC_FLAG is set */
    bitstatus = SET;
  }
  else
  {
    /* ADC_FLAG is reset */
    bitstatus = RESET;
  }
  /* Return the ADC_FLAG status */
  return  bitstatus;
}

/*******************************************************************************
* Function Name  : ADC_ClearFlag
* Description    : Clears the ADCx's pending flags.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - ADC_FLAG: specifies the flag to clear. 
*                    This parameter can be any combination of the following values:
*                       - ADC_FLAG_AWD: Analog watchdog flag
*                       - ADC_FLAG_EOC: End of conversion flag
*                       - ADC_FLAG_JEOC: End of injected group conversion flag
*                       - ADC_FLAG_JSTRT: Start of injected group conversion flag
*                       - ADC_FLAG_STRT: Start of regular group conversion flag
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_ClearFlag(ADC_TypeDef* ADCx, u8 ADC_FLAG)
{
  /* Check the parameters */
  assert(IS_ADC_CLEAR_FLAG(ADC_FLAG));

  /* Clear the selected ADC flags */
  ADCx->SR &= ~(u32)ADC_FLAG;
}

/*******************************************************************************
* Function Name  : ADC_GetITStatus
* Description    : Checks whether the specified ADC interrupt has occurred or not.
* Input          : - ADCx: where x can be 1 or 2 to select the ADC peripheral.
*                  - ADC_IT: specifies the ADC interrupt source to check. 
*                    This parameter can be one of the following values:
*                       - ADC_IT_EOC: End of conversion interrupt mask
*                       - ADC_IT_AWD: Analog watchdog interrupt mask
*                       - ADC_IT_JEOC: End of injected conversion interrupt mask
* Output         : None
* Return         : The new state of ADC_IT (SET or RESET).
*******************************************************************************/
ITStatus ADC_GetITStatus(ADC_TypeDef* ADCx, u16 ADC_IT)
{
  ITStatus bitstatus = RESET;
  u8 itmask = 0, enablestatus;

  /* Check the parameters */
  assert(IS_ADC_GET_IT(ADC_IT));

  /* Get the ADC IT index */
  itmask = (u8)(ADC_IT >> 8);

  /* Get the ADC_IT enable bit status */
  enablestatus = (ADCx->CR1 & (u8)ADC_IT) ;

  /* Check the status of the specified ADC interrupt */
  if (((ADCx->SR & itmask) != (u8)RESET) && enablestatus)
  {
    /* ADC_IT is set */
    bitstatus = SET;
  }
  else
  {
    /* ADC_IT is reset */
    bitstatus = RESET;
  }
  /* Return the ADC_IT status */
  return  bitstatus;
}

/*******************************************************************************
* Function Name  : ADC_ClearITPendingBit
* Description    : Clears the ADC’s interrupt pending bits.
* Input          : - ADC_IT: specifies the ADC interrupt pending bit to clear.
*                    This parameter can be any combination of the following values:
*                       - ADC_IT_EOC: End of conversion interrupt mask
*                       - ADC_IT_AWD: Analog watchdog interrupt mask
*                       - ADC_IT_JEOC: End of injected conversion interrupt mask
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_ClearITPendingBit(ADC_TypeDef* ADCx, u16 ADC_IT)
{
  u8 itmask = 0;

  /* Check the parameters */
  assert(IS_ADC_IT(ADC_IT));

  /* Get the ADC IT index */
  itmask = (u8)(ADC_IT >> 8);

  /* Clear the selected ADC interrupt pending bits */
  ADCx->SR &= ~(u32)itmask;
}

/******************* (C) COPYRIGHT 2007 STMicroelectronics *****END OF FILE****/
