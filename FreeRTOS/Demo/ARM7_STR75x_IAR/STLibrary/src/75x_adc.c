/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_adc.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file provides all the ADC software functions.
********************************************************************************
* History:
* 07/17/2006 : V1.0
* 03/10/2006 : V0.1
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, 
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING 
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Includes ------------------------------------------------------------------*/
#include "75x_adc.h"
#include "75x_mrcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/

/* Mask for Power Down Mode */
#define ADC_PowerDown_Enable  0x8000
#define ADC_PowerDown_Disable 0x7FFF

/* Mask for Watchdog Thresholds Enable */
#define ADC_AnalogWatchdog_Enable  0x8000
#define ADC_AnalogWatchdog_Disable 0x7FFF

/* Mask for Injected conversion start */
#define ADC_Injec_ConversionStart  0x8000

/* DMA enable */
#define ADC_DMA_ExtEnable_Mask  0x4000

/* Injected start trigger enable */
#define ADC_Injec_ExtTrigger_Enable   0x4000

/* ADC Masks */
#define ADC_DMAFirstEnabledChannel_Mask  0x000F 
#define ADC_DataRegisterOffset           0x0050
#define ADC_FirstChannel_Mask            0xFFF0
#define ADC_ChannelNumber_Mask           0xFC3F
#define ADC_Threshold_Mask               0xFC00
#define ADC_AnalogWatchdogChannel_Mask   0xC3FF
#define ADC_Prescalers_Mask              0x7F18
#define ADC_SPEN_Mask                    0x8000
#define ADC_FallingEdge_Mask             0xEFFF
#define ADC_LowLevel_Mask                0x4000
#define ADC_HighLevel_Mask               0xDFFF
#define ADC_Calibration_Mask             0x0002
	
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : ADC_DeInit                                           
* Description    : Deinitializes the ADC peripheral registers to their default
*                  reset values.
* Input          : None.  
* Output         : None                                              
* Return         : None.                                                
*******************************************************************************/
void ADC_DeInit(void)
{
  /* Reset the ADC registers values*/
  MRCC_PeripheralSWResetConfig(MRCC_Peripheral_ADC,ENABLE);
  MRCC_PeripheralSWResetConfig(MRCC_Peripheral_ADC,DISABLE); 
}

/*******************************************************************************
* Function Name  : ADC_Init                                                 
* Description    : Initializes the ADC  peripheral according to the specified
*                  parameters in the ADC_InitStruct.
* Input          : - ADC_InitStruct: pointer to an ADC_InitTypeDef structure that
                   contains the configuration information for the ADC peripheral.
* Output         : None                                                      
* Return         : None                                                      
*******************************************************************************/
void ADC_Init(ADC_InitTypeDef* ADC_InitStruct)
{
  /* Configure the conversion mode */
  if(ADC_InitStruct->ADC_ConversionMode == ADC_ConversionMode_Scan)
  {
    /* Set the scan conversion mode */
    ADC->CLR2 |= ADC_ConversionMode_Scan;
  }
  else
  {
    /* Set the one-shot conversion mode */
    ADC->CLR2 &= ADC_ConversionMode_OneShot;
  }
  
  /* Configure the external start conversion trigger */
  switch(ADC_InitStruct->ADC_ExtTrigger)
  {
    case ADC_ExtTrigger_HighLevel:
      /* Start conversion on High level of the external trigger (TIM0) */
      ADC->CLR0 &= ADC_HighLevel_Mask;
      ADC->CLR0 |= ADC_ExtTrigger_HighLevel;
      break;
      
    case ADC_ExtTrigger_LowLevel:
      /* Start conversion on low level of the external trigger (TIM0) */
      ADC->CLR0 &= ADC_ExtTrigger_LowLevel; 
      ADC->CLR0 |= ADC_LowLevel_Mask;
      break;
      
    case ADC_ExtTrigger_RisingEdge:
      /* Start conversion on rising edge of the external trigger (TIM0) */
      ADC->CLR0 |= ADC_ExtTrigger_RisingEdge;
      break;
    
    case ADC_ExtTrigger_FallingEdge:
      /* Start conversion on falling edge of the external trigger (TIM0) */
      ADC->CLR0 &= ADC_FallingEdge_Mask;
      ADC->CLR0 |= ADC_ExtTrigger_FallingEdge;
      break;
    
    case ADC_ExtTrigger_Disable:
      /* Disable the external trigger and start the conversion by software */
      ADC->CLR0 &= ADC_ExtTrigger_Disable;
      break;

    default:
      break; 
  }

  /* Configure the auto clock off feature */
  if (ADC_InitStruct->ADC_AutoClockOff == ADC_AutoClockOff_Enable)
  {
    /* Enable the auto clock off feature */
    ADC->CLR4 |= ADC_AutoClockOff_Enable;
  }
  else
  {
    /* Disable the auto clock off feature */
    ADC->CLR4 &= ADC_AutoClockOff_Disable;	
  }
  
  /* Clear conversion prescaler CNVP[2:0], sampling prescaler SMPP[2:0] bits 
     and Sample prescaler enable SPEN bit */
  ADC->CLR1 &= ADC_Prescalers_Mask;
  /* Set conversion prescaler value (sampling and conversion prescalers are equal
     while SPEN bit is reset */ 
  ADC->CLR1 |= (ADC_InitStruct->ADC_ConversionPrescaler<<5);
  
  /* In case ADC_SamplingPrescaler member is different from the conversion one */
  if(ADC_InitStruct->ADC_SamplingPrescaler != ADC_InitStruct->ADC_ConversionPrescaler)
  {
    /* Set the sampling prescaler value */
    ADC->CLR1 |= ADC_InitStruct->ADC_SamplingPrescaler;
    /* Set SPEN bit (sampling and conversion prescalers are different */
    ADC->CLR1 = (ADC->CLR1 | ADC_SPEN_Mask);	
  }
  
  /* Clear first channel to be converted FCH[3:0] bits */
  ADC->CLR2 &= ADC_FirstChannel_Mask;
  /* Set the first channel to be converted */
  ADC->CLR2 |= ADC_InitStruct->ADC_FirstChannel;
  /* Clear number of channels to be converted NCH[3:0] bits */
  ADC->CLR2 &= ADC_ChannelNumber_Mask;  
  /* Set the number of channels to be converted */
  ADC->CLR2 |= ((ADC_InitStruct->ADC_ChannelNumber)-1<<6);
}

/*******************************************************************************
* Function Name  : ADC_StructInit                                       
* Description    : Fills each ADC_InitStruct member with its default value.
* Input          : - ADC_InitStruct: pointer to an ADC_InitTypeDef structure
                     which will be initialized.  
* Output         : None 
* Return         : None.
*******************************************************************************/
void ADC_StructInit(ADC_InitTypeDef* ADC_InitStruct)
{
  /* Initialize the ADC_ConversionMode member */
  ADC_InitStruct->ADC_ConversionMode = ADC_ConversionMode_OneShot;
  
  /* Initialize the ADC_ExtTrigger member */
  ADC_InitStruct->ADC_ExtTrigger = ADC_ExtTrigger_Disable;
  
  /* Initialize the ADC_AutoClockOff member */
  ADC_InitStruct->ADC_AutoClockOff = ADC_AutoClockOff_Disable;
  
  /* Initialize the ADC_SamplingPrescaler member */
  ADC_InitStruct->ADC_SamplingPrescaler = 0;
  
  /* Initialize the ADC_ConversionPrescaler member */
  ADC_InitStruct->ADC_ConversionPrescaler = 0;
  
  /* Initialize the ADC_FirstChannel member */
  ADC_InitStruct->ADC_FirstChannel = ADC_CHANNEL0;
  
  /* Initialize the ADC_ChannelNumber member */
  ADC_InitStruct->ADC_ChannelNumber = 1;
 }

/*******************************************************************************
* Function Name  : ADC_StartCalibration                                       
* Description    : Starts the ADC Calibration. Calibration average enabled/disabled.
* Input          : - ADC_CalibAverage: Enables or disables ADC calibration average.
*                    This parameter can be one of the following values:
*                         - ADC_CalibAverage_Enable:  enable calibration average 
*                         - ADC_CalibAverage_Disable: disable calibration average  
* Output         : None 
* Return         : None                                                       
*******************************************************************************/
void ADC_StartCalibration(u16 ADC_CalibAverage)
{
  if (ADC_CalibAverage == ADC_CalibAverage_Enable)
  {
    /* Enable ADC Calibration Average */
    ADC->CLR4 &= ADC_CalibAverage_Enable;
  }
  else
  {
    /* Disable ADC Calibration Average */
    ADC->CLR4 |= ADC_CalibAverage_Disable;
  }

  /* Start Calibration */
  ADC->CLR0 |= ADC_Calibration_ON;
}

/*******************************************************************************
* Function Name  : ADC_GetCalibrationStatus
* Description    : Get the ADC Calibration Status.
* Input          : None
* Output         : None 
* Return         : The NewState of the ADC calibration (SET or RESET).
*******************************************************************************/
FlagStatus ADC_GetCalibrationStatus(void)
{
  /* Check the status of the ADC calibration */
  if((ADC->CLR0 & ADC_Calibration_Mask) != RESET)
  {
    /* Return SET if ADC Calibration is on going */
    return SET;
  }
  else
  {
    /* Return RESET if ADC Calibration is finished */
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : ADC_ConversionCmd
* Description    : Starts or stops the ADC conversion.
* Input          : - ADC_Conversion: specifies the ADC command to apply.
*                    This parameter can be one of the following values:
*                         - ADC_Conversion_Start: start conversion 
*                         - ADC_Conversion_Stop:  stop conversion 
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_ConversionCmd (u16 ADC_Conversion)
{
  if (ADC_Conversion == ADC_Conversion_Start)
  {
    /* Start the ADC Conversion */
    ADC->CLR0 |= ADC_Conversion_Start;
  }
  else
  {
    /* Stop the ADC Conversion */
    ADC->CLR0 &= ADC_Conversion_Stop;
  }
}

/*******************************************************************************
* Function Name  : ADC_GetSTARTBitStatus
* Description    : Gets the ADC START/STOP bit Status.
* Input          : None
* Output         : None 
* Return         : The NewState of the ADC START/STOP bit (SET or RESET).
*******************************************************************************/
FlagStatus ADC_GetSTARTBitStatus(void)
{
  /* Check the status of the ADC START/STOP bit */
  if((ADC->CLR0 & ADC_Conversion_Start) != RESET)
  {
    /* Return SET if ADC Conversion is started */
    return SET;
  }
  else
  {
    /* Return RESET if ADC Conversion is stopped */
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : ADC_Cmd
* Description    : Enables the ADC peripheral or puts it in power down mode.
*                  - NewState: new state of the ADC peripheral. 
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None  
* Return         : None.
*******************************************************************************/
void ADC_Cmd(FunctionalState NewState)
{
  if (NewState == DISABLE)
  {
    /* Enable ADC Power Down Mode */
    ADC->CLR4 |= ADC_PowerDown_Enable;
  }
  else
  {
    /* Disable ADC Power Down Mode */
    ADC->CLR4 &= ADC_PowerDown_Disable;
  }
}

/*******************************************************************************
* Function Name  : ADC_AutoClockOffConfig                                
* Description    : Enables or disables the Auto clock off feature.
*                  - NewState: new state of the Auto clock off feature. This 
*                    parameter can be: ENABLE or DISABLE.  
* Output         : None   
* Return         : None.                                                 
*******************************************************************************/
void ADC_AutoClockOffConfig(FunctionalState NewState)
{
  if (NewState == ENABLE)
  {
    /* Enable ADC Auto Clock Off */
    ADC->CLR4 |= ADC_AutoClockOff_Enable;
  }
  else
  {
    /* Disable ADC Auto Clock Off */
    ADC->CLR4 &= ADC_AutoClockOff_Disable;
  }
}

/*******************************************************************************
* Function Name  : ADC_AnalogWatchdogConfig                                       
* Description    : Configures the analog input channel to be used for the selected
*                  Analog Watchdog and defines its corresponding High and Low 
*                  threshold values.               
* Input          : - ADC_AnalogWatchdog: specifies the analog watchdog which will
*                    be affected to the desired converted channel. This parameter
*                    can be one of the following values: 
*                     - ADC_AnalogWatchdog0: select analog watchdog 0
*                     - ADC_AnalogWatchdog1: select analog watchdog 1
*                     - ADC_AnalogWatchdog2: select analog watchdog 2
*                     - ADC_AnalogWatchdog3: select analog watchdog 3
*                  - ADC_CHANNEL: specifies the channel linked to the selected 
*                    analog watchdog. This parameter can be ADC_CHANNELx where x 
*                    can be (0..15)                    
*                  - LowThreshold: Low Threshold for the selected Analog watchdog
*                  - HighThreshold: High Threshold for the selected Analog watchdog
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_AnalogWatchdogConfig(u16 ADC_AnalogWatchdog, u8 ADC_CHANNEL, 
                              u16 LowThreshold, u16 HighThreshold)
{
  switch (ADC_AnalogWatchdog)
  {
    /* Set the selected channel and their corresponding High and Low thresholds */
    case ADC_AnalogWatchdog0 :
      ADC->TRA0 = (ADC->TRA0 & ADC_AnalogWatchdogChannel_Mask) | ((u16) ADC_CHANNEL<<10);
      ADC->TRA0 = (ADC->TRA0 & ADC_Threshold_Mask) |  HighThreshold;
      ADC->TRB0 = (ADC->TRB0 & ADC_Threshold_Mask) |  LowThreshold;
      break;

    case ADC_AnalogWatchdog1 :
      ADC->TRA1 = (ADC->TRA1 & ADC_AnalogWatchdogChannel_Mask) | ((u16) ADC_CHANNEL<<10);
      ADC->TRA1 = (ADC->TRA1 & ADC_Threshold_Mask) |  HighThreshold;
      ADC->TRB1 = (ADC->TRB1 & ADC_Threshold_Mask) |  LowThreshold;
      break;

    case ADC_AnalogWatchdog2 :
      ADC->TRA2 = (ADC->TRA2 & ADC_AnalogWatchdogChannel_Mask) | ((u16) ADC_CHANNEL<<10);
      ADC->TRA2 = (ADC->TRA2 & ADC_Threshold_Mask) |  HighThreshold;
      ADC->TRB2 = (ADC->TRB2 & ADC_Threshold_Mask) |  LowThreshold;
      break;

    case ADC_AnalogWatchdog3 :
      ADC->TRA3 = (ADC->TRA3 & ADC_AnalogWatchdogChannel_Mask) | ((u16) ADC_CHANNEL<<10);
      ADC->TRA3 = (ADC->TRA3 & ADC_Threshold_Mask) |  HighThreshold;
      ADC->TRB3 = (ADC->TRB3 & ADC_Threshold_Mask) |  LowThreshold;
      break;

    default:
      break; 
  }
}

/*******************************************************************************
* Function Name  : ADC_AnalogWatchdogCmd                                   
* Description    : Enables or disables the selected analog Watchdog.
* Input          : - ADC_AnalogWatchdog: specifies the analog watchdog to be 
*                    enabled or disabled. This parameter can be one of the 
*                    following values: 
*                     - ADC_AnalogWatchdog0: select analog watchdog 0
*                     - ADC_AnalogWatchdog1: select analog watchdog 1
*                     - ADC_AnalogWatchdog2: select analog watchdog 2
*                     - ADC_AnalogWatchdog3: select analog watchdog 3
*                  - NewState: new state of the specified analog watchdog.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None.                                                   
*******************************************************************************/
void ADC_AnalogWatchdogCmd(u16 ADC_AnalogWatchdog, FunctionalState NewState)
{
  if (NewState == ENABLE)
  {
    /* Enable the selected ADC AnalogWatchdogx */
    switch (ADC_AnalogWatchdog)
    {
      case ADC_AnalogWatchdog0 : 
        ADC->TRB0 |= ADC_AnalogWatchdog_Enable;
        break;

      case ADC_AnalogWatchdog1 : 
        ADC->TRB1 |= ADC_AnalogWatchdog_Enable;  
        break;

      case ADC_AnalogWatchdog2 : 
        ADC->TRB2 |= ADC_AnalogWatchdog_Enable;  
        break;

      case ADC_AnalogWatchdog3 : 
        ADC->TRB3 |= ADC_AnalogWatchdog_Enable;  
        break;

      default:
        break; 
    }
  }
  else
  {
    /* Disable the selected ADC AnalogWatchdogx */
    switch (ADC_AnalogWatchdog)
    {
      case ADC_AnalogWatchdog0 : 
        ADC->TRB0 &= ADC_AnalogWatchdog_Disable;  
        break;

      case ADC_AnalogWatchdog1 : 
        ADC->TRB1 &= ADC_AnalogWatchdog_Disable;  
        break;

      case ADC_AnalogWatchdog2 : 
        ADC->TRB2 &= ADC_AnalogWatchdog_Disable;  
        break;

      case ADC_AnalogWatchdog3 : 
        ADC->TRB3 &= ADC_AnalogWatchdog_Disable;  
        break;

      default:
        break; 
    }
  }
}

/*******************************************************************************
* Function Name  : ADC_GetAnalogWatchdogResult
* Description    : Returns the comparison result of the selected analog watchdog.
* Input          : - ADC_AnalogWatchdog: specifies the analog watchdog channel 
*                    which its comparison result will be returned. This parameter
*                    can be one of the following values: 
*                     - ADC_AnalogWatchdog0: select analog watchdog 0
*                     - ADC_AnalogWatchdog1: select analog watchdog 1
*                     - ADC_AnalogWatchdog2: select analog watchdog 2
*                     - ADC_AnalogWatchdog3: select analog watchdog 3
* Output         : None
* Return         : The analog watchdog comparaison result value
*******************************************************************************/
u16 ADC_GetAnalogWatchdogResult(u16 ADC_AnalogWatchdog)
{
  /* Return the selected ADC AnalogWatchdogx comparaison result */
  switch(ADC_AnalogWatchdog)
  {
    case ADC_AnalogWatchdog0 :
      return ((ADC->PBR & ADC_AnalogWatchdog)>>4);

    case ADC_AnalogWatchdog1 :
      return ((ADC->PBR & ADC_AnalogWatchdog)>>6);

    case ADC_AnalogWatchdog2 :
      return ((ADC->PBR & ADC_AnalogWatchdog)>>8);

    case ADC_AnalogWatchdog3 :
      return ((ADC->PBR & ADC_AnalogWatchdog)>>10);

    default : return (0xFF);  /* if a wrong value of ADC_AnalogWatchdog is selected */
  }
}

/*******************************************************************************
* Function Name  : ADC_InjectedConversionConfig
* Description    : Configures the start trigger level for the injected channels 
*                  and the injected analog input channels to be converted. 
* Input          : - ADC_Injec_ExtTrigger: specifies the start trigger level.
*                    This parameter can be one of the following values:
*                         - ADC_Injec_ExtTrigger_Disable : external trigger disabled
*                         - ADC_Injec_ExtTrigger_RisingEdge: external trigger
*                           configured as rising edge of PWM Timer TRGO signal
*                         - ADC_Injec_ExtTrigger_FallingEdge: external trigger 
*                           configured as falling edge of PWM Timer TRGO signal 
*                  - FirstChannel: specifies the first injected channel to be
*                    converted. 
*                    This parameter can be ADC_CHANNELx  where x can be (0..15). 
*                  - ChannelNumber: specifies the Number of the injected channels 
*                    to be converted. This parameter can be a  value from 1 to 16.    
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_InjectedConversionConfig(u16 ADC_Injec_ExtTrigger, u8 FirstChannel, u8 ChannelNumber)
{
  /* Configure the external start injected conversion trigger */
  switch (ADC_Injec_ExtTrigger)
  {
    case ADC_Injec_ExtTrigger_Disable  :
      /* Disable the external trigger and start the injected conversion by software */
      ADC->CLR3 &= ADC_Injec_ExtTrigger_Disable ;
      break;
    case ADC_Injec_ExtTrigger_RisingEdge :
      /* Start injected conversion on rising edge of the external trigger (PWM) */
      ADC->CLR3 |= ADC_Injec_ExtTrigger_RisingEdge;
      break;
    case ADC_Injec_ExtTrigger_FallingEdge :
      /* Start injected conversion on falling edge of the external trigger (PWM) */
      ADC->CLR3 |= ADC_Injec_ExtTrigger_Enable; 
      ADC->CLR3 &= ADC_Injec_ExtTrigger_FallingEdge;
      break;

    default:
      break;
  }
  
  /* Clear first injected channel to be converted JFCH[3:0] bits */
  ADC->CLR3 &= ADC_FirstChannel_Mask;
  /* Set the first injected channel to be converted */
  ADC->CLR3 |= FirstChannel;
  /* Clear number of injected channels to be converted JNCH[3:0] bits */
  ADC->CLR3 &= ADC_ChannelNumber_Mask;  
  /* Set the number of injected channels to be converted */
  ADC->CLR3 |= ((ChannelNumber-1)<<6);
}

/*******************************************************************************
* Function Name  : ADC_StartInjectedConversion
* Description    : Starts by software the conversion of the injected input channels.
* Input          : None
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_StartInjectedConversion(void)
{
  /* Start the injected ADC Conversion */
  ADC->CLR3 |= ADC_Injec_ConversionStart;
}

/*******************************************************************************
* Function Name  : ADC_GetConversionValue
* Description    : Reads the conversion result from the appropriate data register.
* Input          : - ADC_CHANNEL :specifies the ADC channel which its conversion 
*                    value have to be returned. This parameter can be ADC_CHANNELx
*                    where x can be (0..15) to select channelx  
* Output         : None
* Return         : The returned value holds the conversion result of the selected   
*                  channel.
*******************************************************************************/
u16 ADC_GetConversionValue(u8 ADC_CHANNEL)
{
  /* Return the conversion result of the selected channel */
  return *((u16 *)(ADC_BASE + ((ADC_CHANNEL<<2) + ADC_DataRegisterOffset)));
}

/*******************************************************************************
* Function Name  : ADC_ITConfig
* Description    : Enables or disables the specified ADC interrupts.
* Input          : - ADC_IT: specifies the ADC interrupts to be enabled or disabled.
*                    This parameter can be any combination of the following values:
*                         - ADC_IT_ECH:  End of chain conversion interrupt
*                         - ADC_IT_EOC:  End of channel conversion interrupt
*                         - ADC_IT_JECH: Injected end of chain conversion interrupt
*                         - ADC_IT_JEOC: Injected end of channel conversion interrupt
*                         - ADC_IT_AnalogWatchdog0_LowThreshold:
*                                        Analog Watchdog 0 LowThreshold interrupt
*                         - ADC_IT_AnalogWatchdog0_HighThreshold:
*                                        Analog Watchdog 0 HighThreshold interrupt
*                         - ADC_IT_AnalogWatchdog1_LowThreshold:
*                                        Analog Watchdog 1 LowThreshold interrupt
*                         - ADC_IT_AnalogWatchdog1_HighThreshold:
*                                        Analog Watchdog 1 HighThreshold interrupt
*                         - ADC_IT_AnalogWatchdog2_LowThreshold:
*                                        Analog Watchdog 2 LowThreshold interrupt
*                         - ADC_IT_AnalogWatchdog2_HighThreshold:
*                                        Analog Watchdog 2 HighThreshold interrupt
*                         - ADC_IT_AnalogWatchdog3_LowThreshold:
*                                        Analog Watchdog 3 LowThreshold interrupt
*                         - ADC_IT_AnalogWatchdog3_HighThreshold:
*                                         Analog Watchdog 5 HighThreshold interrupt
*                         - ADC_IT_ALL:  All interrupts
*                  - NewState: new state of the specified ADC interrupts.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_ITConfig(u16 ADC_IT, FunctionalState NewState)
{
  if (NewState == ENABLE)
  {
    /* Enable the selected ADC interrupts */
    ADC->IMR |= ADC_IT;
  }
  else
  {
    /* Disable the selected ADC interrupts */
    ADC->IMR &= ~ADC_IT;
  }
}

/*******************************************************************************
* Function Name  : ADC_DMAConfig
* Description    : Configures the ADC’s DMA interface.
* Input          : - ADC_DMA_CHANNEL: specifies the channels to be enabled or 
*                    disabled for DMA transfer. This parameter can be any 
*                    combination of ADC_DMA_CHANNELx where x can be (0..15). 
*                  - NewState: new state of the specified ADC DMA channels.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_DMAConfig(u16 ADC_DMA_CHANNEL, FunctionalState NewState)
{
  if(NewState == ENABLE)
  {
    /* Enable DMA for the selected channels */
    ADC->DMAR |= ADC_DMA_CHANNEL ;
  }
  else
  {
    /* Disable DMA for the selected channels */
    ADC->DMAR &= ~ADC_DMA_CHANNEL;
  }
}

/*******************************************************************************
* Function Name  : ADC_DMACmd
* Description    : Enable or disable the DMA transfer for the ADC.
* Input          : - ADC_DMA: specifies the DMA command. This parameter can be 
*                    one of the following values:
*                         - ADC_DMA_Disable: disable the DMA capability
*                         - ADC_DMA_Enable: enabled by setting the global 
*                           enable bit
*                         - ADC_DMA_ExtTrigger_HighLevel: enabled by detection of
*                           high level of TIM2 OC2 signal
*                         - ADC_DMA_ExtTrigger_LowLevel: enabled by detection of
*                           low level of TIM2 OC2 signal
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_DMACmd(u16 ADC_DMA)
{
  /* Configure the DMA external trigger enable */
  switch (ADC_DMA)
  {
    case ADC_DMA_Disable :
      /* Disable DMA transfer */
      ADC->DMAE &= ADC_DMA_Disable;
      break;
      
    case ADC_DMA_Enable :
      /* Enable DMA transfer */
      ADC->DMAE |= ADC_DMA_Enable;
      break;
      
    case ADC_DMA_ExtTrigger_HighLevel :
      /* Enable DMA transfer on high level of the external trigger (TIM2) */
      ADC->DMAE &= ADC_DMA_Disable;
      ADC->DMAE |= ADC_DMA_ExtTrigger_HighLevel;
      break;
      
    case ADC_DMA_ExtTrigger_LowLevel :
      /* Enable DMA transfer on low level of the external trigger (TIM2) */
      ADC->DMAE |= ADC_DMA_ExtEnable_Mask; 
      ADC->DMAE &= ADC_DMA_ExtTrigger_LowLevel;
      break;

    default:
      break;      
  }  
}

/*******************************************************************************
* Function Name  : ADC_GetDMAFirstEnabledChannel
* Description    : Gets the first DMA-enabled channel configured at the time that
*                  DMA was last globally enabled.
* Input          : None
* Output         : None
* Return         : The first DMA enabled channel
*******************************************************************************/
u16 ADC_GetDMAFirstEnabledChannel(void)
{
  /* Return the DMA first enabled channel */
  return (ADC->DMAE & ADC_DMAFirstEnabledChannel_Mask);
}

/*******************************************************************************
* Function Name  : ADC_GetFlagStatus
* Description    : Checks whether the specified ADC flag is set or not.
* Input          : - ADC_FLAG: specifies the ADC flag to check. This parameter 
*                    can be one of the following values:
*                         - ADC_FLAG_ECH:  End of chain conversion Flag
*                         - ADC_FLAG_EOC:  End of channel conversion Flag
*                         - ADC_FLAG_JECH: End of injected chain conversion Flag
*                         - ADC_FLAG_JEOC: End of injected channel conversion Flag
*                         - ADC_FLAG_AnalogWatchdog0_LowThreshold:  
*                                          Analog Watchdog 0 LowThreshold Flag        
*                         - ADC_FLAG_AnalogWatchdog0_HighThreshold: 
*                                          Analog Watchdog 0 HighThreshold Flag 	
*                         - ADC_FLAG_AnalogWatchdog1_LowThreshold:  
*                                          Analog Watchdog 1 LowThreshold Flag  	
*                         - ADC_FLAG_AnalogWatchdog1_HighThreshold: 
*                                          Analog Watchdog 1 HighThreshold Flag  	
*                         - ADC_FLAG_AnalogWatchdog2_LowThreshold:  
*                                          Analog Watchdog 2 LowThreshold Flag  	
*                         - ADC_FLAG_AnalogWatchdog2_HighThreshold: 
*                                          Analog Watchdog 2 HighThreshold Flag 	
*                         - ADC_FLAG_AnalogWatchdog3_LowThreshold:  
*                                          Analog Watchdog 3 LowThreshold Flag  	
*                         - ADC_FLAG_AnalogWatchdog3_HighThreshold: 
*                                          Analog Watchdog 3 HighThreshold Flag 
* Output         : None	
* Return         : The new state of the ADC_FLAG (SET or RESET).
*******************************************************************************/
FlagStatus ADC_GetFlagStatus(u16 ADC_FLAG)
{
  /* Check the status of the specified ADC flag */
  if((ADC->PBR & ADC_FLAG) != RESET)
  {
    /* Return SET if ADC_FLAG is set */
    return SET;
  }
  else
  {
    /* Return RESET if ADC_FLAG is reset */
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : ADC_ClearFlag
* Description    : Clears the ADC’s pending flags.  
* Input          : - ADC_FLAG: specifies the flag to clear. This parameter can 
*                    be any combination of the following values:
*                         - ADC_FLAG_ECH:  End of chain conversion flag
*                         - ADC_FLAG_EOC:  End of channel conversion flag
*                         - ADC_FLAG_JECH: Injected end of chain conversion flag
*                         - ADC_FLAG_JEOC: Injected end of channel conversion flag
*                         - ADC_FLAG_AnalogWatchdog0_LowThreshold:  
*                                         Analog Watchdog 0 LowThreshold flag        
*                         - ADC_FLAG_AnalogWatchdog0_HighThreshold: 
*                                         Analog Watchdog 0 HighThreshold flag 	
*                         - ADC_FLAG_AnalogWatchdog1_LowThreshold:  
*                                         Analog Watchdog 1 LowThreshold flag  	
*                         - ADC_FLAG_AnalogWatchdog1_HighThreshold: 
*                                         Analog Watchdog 1 HighThreshold flag  	
*                         - ADC_FLAG_AnalogWatchdog2_LowThreshold:  
*                                         Analog Watchdog 2 LowThreshold flag  	
*                         - ADC_FLAG_AnalogWatchdog2_HighThreshold: 
*                                         Analog Watchdog 2 HighThreshold flag 	
*                         - ADC_FLAG_AnalogWatchdog3_LowThreshold:  
*                                         Analog Watchdog 3 LowThreshold flag  	
*                         - ADC_FLAG_AnalogWatchdog3_HighThreshold: 
*                                         Analog Watchdog 3 HighThreshold flag  	
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_ClearFlag(u16 ADC_FLAG)
{
  /* Clear the selected ADC flag */ 
  ADC->PBR = ADC_FLAG;
}

/*******************************************************************************
* Function Name  : ADC_GetITStatus
* Description    : Checks whether the specified ADC interrupt has occured or not.
* Input          : - ADC_IT: specifies the ADC interrupt source to check. This 
*                    parameter can be one of the following values:
*                         - ADC_IT_ECH :End of chain conversion interrupt 
*                         - ADC_IT_EOC :End of channel conversion interrupt
*                         - ADC_IT_JECH :End of injected chain conversion interrupt
*                         - ADC_IT_JEOC :End of injected channel conversion interrupt
*                         - ADC_IT_AnalogWatchdog0_LowThreshold:  
*                                         Analog Watchdog 0 LowThreshold interrupt
*                         - ADC_IT_AnalogWatchdog0_HighThreshold: 
*                                         Analog Watchdog 0 HighThreshold interrupt
*                         - ADC_IT_AnalogWatchdog1_LowThreshold:  
*                                         Analog Watchdog 1 LowThreshold interrupt
*                         - ADC_IT_AnalogWatchdog1_HighThreshold: 
*                                         Analog Watchdog 1 HighThreshold interrupt
*                         - ADC_IT_AnalogWatchdog2_LowThreshold:  
*                                         Analog Watchdog 2 LowThreshold interrupt
*                         - ADC_IT_AnalogWatchdog2_HighThreshold: 
*                                         Analog Watchdog 2 HighThreshold interrupt
*                         - ADC_IT_AnalogWatchdog3_LowThreshold:  
*                                         Analog Watchdog 3 LowThreshold interrupt
*                         - ADC_IT_AnalogWatchdog3_HighThreshold: 
*                                         Analog Watchdog 3 HighThreshold interrupt
* Output         : None	
* Return         : The new state of the ADC_IT (SET or RESET).
*******************************************************************************/
ITStatus ADC_GetITStatus(u16 ADC_IT)
{
  /* Check the status of the specified ADC interrupt */
  if((ADC->PBR & ADC_IT) != RESET)
  {
    /* Return SET if the ADC interrupt flag is set */
    return SET;
  }
  else
  {
    /* Return RESET if the ADC interrupt flag is reset */
    return RESET;
  }
}

/*******************************************************************************
* Function Name  : ADC_ClearITPendingBit
* Description    : Clears the ADC’s interrupt pending bits.  
* Input          : - ADC_IT: specifies the interrupt pending bit to clear. This 
*                    parameter can be can be any combination of the following 
*                    values:
*                         - ADC_IT_ECH:  End of chain conversion interrupt
*                         - ADC_IT_EOC:  End of channel conversion interrupt
*                         - ADC_IT_JECH: Injected end of chain conversion interrupt
*                         - ADC_IT_JEOC: Injected end of channel conversion interrupt
*                         - ADC_IT_AnalogWatchdog0_LowThreshold:  
*                                         Analog Watchdog 0 LowThreshold interrupt
*                         - ADC_IT_AnalogWatchdog0_HighThreshold: 
*                                         Analog Watchdog 0 HighThreshold interrupt
*                         - ADC_IT_AnalogWatchdog1_LowThreshold:  
*                                         Analog Watchdog 1 LowThreshold interrupt
*                         - ADC_IT_AnalogWatchdog1_HighThreshold: 
*                                         Analog Watchdog 1 HighThreshold interrupt
*                         - ADC_IT_AnalogWatchdog2_LowThreshold:  
*                                         Analog Watchdog 2 LowThreshold interrupt
*                         - ADC_IT_AnalogWatchdog2_HighThreshold: 
*                                         Analog Watchdog 2 HighThreshold interrupt
*                         - ADC_IT_AnalogWatchdog3_LowThreshold:  
*                                         Analog Watchdog 3 LowThreshold interrupt
*                         - ADC_IT_AnalogWatchdog3_HighThreshold: 
*                                         Analog Watchdog 5 HighThreshold interrupt
* Output         : None
* Return         : None
*******************************************************************************/
void ADC_ClearITPendingBit(u16 ADC_IT)
{
  /* Clear the selected ADC interrupts pending bits */
  ADC->PBR = ADC_IT;
}

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
