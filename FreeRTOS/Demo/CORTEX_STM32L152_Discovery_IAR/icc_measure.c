/**
  ******************************************************************************
  * @file    icc_measure.c
  * @author  Microcontroller Division
  * @version V1.0.3
  * @date    May-2013
  * @brief   Current measurements
  ******************************************************************************
  * @copy
  *
  * THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
  * WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE
  * TIME. AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY
  * DIRECT, INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING
  * FROM THE CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE
  * CODING INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
  *
  * <h2><center>&copy; COPYRIGHT 2011 STMicroelectronics</center></h2>
  */
 
/* Includes ------------------------------------------------------------------*/
#include "misc.h"
#include "stm32l1xx.h"
#include "stm32l1xx_adc.h"
#include "stm32l1xx_lcd.h"
#include "stm32l1xx_rcc.h"
#include "stm32l1xx_rtc.h"
#include "stm32l1xx_pwr.h"
#include "stm32l1xx_gpio.h"
#include "discover_board.h"
#include "icc_measure.h"
#include "discover_functions.h"
#include "stm32l_discovery_lcd.h"
#include "stm32l1xx_conf.h"

/* Current measurment in RAM for Run mode and LPOWER run mode */
#define TESTINRAM 1

extern bool UserButton; /* Indicate if GPIO PA1 is used for  user button instead of wake up signal */
volatile bool Idd_WakeUP; /* Indicate Wake UP setted in IT handler */

/* Variables used for save GPIO configuration */
uint32_t GPIOA_MODER, GPIOB_MODER, GPIOC_MODER,GPIOD_MODER,GPIOE_MODER ,GPIOE_MODER,GPIOH_MODER;
uint32_t GPIOA_PUPDR, GPIOB_PUPDR , GPIOC_PUPDR, GPIOD_PUPDR,GPIOE_PUPDR,GPIOH_PUPDR;

/**
  * @brief  Function used to Configure the GPIO in low consumption
  * @caller ADC_Icc_Test
  * @param None
  * @retval None
  */
void GPIO_LowPower_Config(void)
{
  GPIO_InitTypeDef GPIO_InitStructure;

  /* store GPIO configuration before lowpower switch */
  GPIOA_MODER = GPIOA->MODER;
  GPIOB_MODER = GPIOB->MODER;
  GPIOC_MODER = GPIOC->MODER;
  GPIOD_MODER = GPIOD->MODER;
  GPIOE_MODER = GPIOE->MODER;
  GPIOH_MODER = GPIOH->MODER;
  GPIOA_PUPDR = GPIOA->PUPDR;
  GPIOB_PUPDR = GPIOB->PUPDR;
  GPIOC_PUPDR = GPIOC->PUPDR;
  GPIOD_PUPDR = GPIOD->PUPDR;
  GPIOE_PUPDR = GPIOE->PUPDR;
  GPIOH_PUPDR = GPIOH->PUPDR;
  
  /* Configure all GPIO port pins in Analog input mode (trigger OFF) */
  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_All;
  GPIO_InitStructure.GPIO_Speed = GPIO_Speed_400KHz;
  GPIO_InitStructure.GPIO_Mode = GPIO_Mode_AN;
  GPIO_InitStructure.GPIO_OType = GPIO_OType_PP;
  GPIO_InitStructure.GPIO_PuPd = GPIO_PuPd_NOPULL;

  
  GPIOD->MODER   = 0xFFFFFFFF;
  GPIOE->MODER   = 0xFFFFFFFF;
  GPIOH->MODER   = 0xFFFFFFFF;
  
  /* all GPIOA */
  GPIO_InitStructure.GPIO_Pin =  GPIO_Pin_1 | GPIO_Pin_2 | GPIO_Pin_3 | GPIO_Pin_6| GPIO_Pin_7 \
    | GPIO_Pin_13 | GPIO_Pin_14|GPIO_Pin_5 | GPIO_Pin_8  |GPIO_Pin_9 | GPIO_Pin_10 | GPIO_Pin_11 |  GPIO_Pin_12 |GPIO_Pin_15 ;

	GPIO_Init(GPIOA, &GPIO_InitStructure);  

   /* All GPIOC except PC13 which is used for mesurement */
  GPIO_InitStructure.GPIO_Pin =  GPIO_Pin_0 | GPIO_Pin_1 | GPIO_Pin_2 | GPIO_Pin_3 | GPIO_Pin_4|  GPIO_Pin_5 |GPIO_Pin_6| GPIO_Pin_7| GPIO_Pin_8 \
                                 | GPIO_Pin_9 | GPIO_Pin_10 | GPIO_Pin_11 |  GPIO_Pin_12 | GPIO_Pin_14 | GPIO_Pin_15 ;
  GPIO_Init(GPIOC, &GPIO_InitStructure);  

   /* all GPIOB except PB6 and PB7 used for LED*/
  GPIO_InitStructure.GPIO_Pin =  GPIO_Pin_0 | GPIO_Pin_1 | GPIO_Pin_2 | GPIO_Pin_3 | GPIO_Pin_4|  GPIO_Pin_5 | GPIO_Pin_8 \
                                 | GPIO_Pin_9 | GPIO_Pin_10 | GPIO_Pin_11 |  GPIO_Pin_12 |GPIO_Pin_13 | GPIO_Pin_14 | GPIO_Pin_15 ;
  GPIO_Init(GPIOB, &GPIO_InitStructure);
  
  
  GPIO_LOW(GPIOB,GPIO_Pin_6);
  GPIO_LOW(GPIOB,GPIO_Pin_7);
}

/**
  * @brief  To restore register values for GPIO.
  * @caller ADC_Icc_Test
  * @param None
  * @retval None
  */
void Restore_GPIO_Config(void)
{
  GPIOA->MODER = GPIOA_MODER;
  GPIOB->MODER = GPIOB_MODER;
  GPIOC->MODER = GPIOC_MODER;
  GPIOD->MODER = GPIOD_MODER;
  GPIOE->MODER = GPIOE_MODER;
  GPIOH->MODER = GPIOH_MODER;

  GPIOA->PUPDR = GPIOA_PUPDR;
  GPIOB->PUPDR = GPIOB_PUPDR;
  GPIOC->PUPDR = GPIOC_PUPDR;
  GPIOD->PUPDR = GPIOD_PUPDR;
  GPIOE->PUPDR = GPIOE_PUPDR;
  GPIOH->PUPDR = GPIOH_PUPDR;
}


/**
  * @brief  Configures the clock system
  * @param  None
  * @retval None
  */
void Config_Systick()
{
  RCC_ClocksTypeDef RCC_Clocks;
  RCC_GetClocksFreq(&RCC_Clocks);
  SysTick_Config(RCC_Clocks.HCLK_Frequency / 2000);
}

/**
  * @brief  Configures the clock system in low frequency
  * @param  None
  * @retval None
  */
void Config_Systick_50ms()
{
  RCC_ClocksTypeDef RCC_Clocks;
  RCC_GetClocksFreq(&RCC_Clocks);
  SysTick_Config(RCC_Clocks.HCLK_Frequency / 2);
}

/**
  * @brief  To select MSI as System clock source 
  * @caller ADC_Icc_Test
  * @param Frequence, DIV by 2 ot not , With or without RTC
  * @retval None
  */
void SetHSICLKToMSI(uint32_t freq,bool div2,bool With_RTC)
{
  
  /* RCC system reset */
  RCC_DeInit();

  /* Flash no latency*/
  FLASH_SetLatency(FLASH_Latency_0);
  
  /* Disable Prefetch Buffer */
  FLASH_PrefetchBufferCmd(DISABLE);

  /* Disable 64-bit access */
  FLASH_ReadAccess64Cmd(DISABLE);
         
  /* Disable FLASH during SLeep  */
  FLASH_SLEEPPowerDownCmd(ENABLE);
 
  /* Enable the PWR APB1 Clock */
  RCC_APB1PeriphClockCmd(RCC_APB1Periph_PWR, ENABLE);

  /* Select the Voltage Range 3 (1.2V) */
  PWR_VoltageScalingConfig(PWR_VoltageScaling_Range3);

  /* Wait Until the Voltage Regulator is ready */
  while (PWR_GetFlagStatus(PWR_FLAG_VOS) != RESET);

  /* Configure the MSI frequency */
  RCC_MSIRangeConfig(freq);
  
  /* Select MSI as system clock source */
  RCC_SYSCLKConfig(RCC_SYSCLKSource_MSI);

  /* Wait until MSI is used as system clock source */
  while (RCC_GetSYSCLKSource() != 0x00);

  if (div2)
  {
    RCC_HCLKConfig(RCC_SYSCLK_Div2);    
  }

  RCC_HSICmd(DISABLE);

  /* Disable HSE clock */
  RCC_HSEConfig(RCC_HSE_OFF);

  /* Disable LSE clock */
  if (! With_RTC)
    RCC_LSEConfig(RCC_LSE_OFF);

  /* Disable LSI clock */
  RCC_LSICmd(DISABLE);  

}

/**
  * @brief  To select HSI as System clock source 
  * @caller ADC_Icc_Test
  * @param None
  * @retval None
  */
void SetHSICLK(void)
{
  /* Enable HSI Clock */
  RCC_HSICmd(ENABLE);
  
  /*!< Wait till HSI is ready */
  while (RCC_GetFlagStatus(RCC_FLAG_HSIRDY) == RESET);
  
  /* Enable 64-bit access */
  FLASH_ReadAccess64Cmd(ENABLE);
  
  /* Enable Prefetch Buffer */
  FLASH_PrefetchBufferCmd(ENABLE);
  
  /* Flash 1 wait state */
  FLASH_SetLatency(FLASH_Latency_1);
  
  RCC_SYSCLKConfig(RCC_SYSCLKSource_HSI);
  
  while (RCC_GetSYSCLKSource() != 0x04);
      
  RCC_HCLKConfig(RCC_SYSCLK_Div1);  
  /* PCLK2 = HCLK */
  RCC_PCLK2Config(RCC_HCLK_Div1);

  /* PCLK1 = HCLK */
  RCC_PCLK1Config(RCC_HCLK_Div1);    
 
}


/**
  * @brief ADC initialization (ADC_Channel_4)
  * @caller main and ADC_Icc_Test
  * @param None
  * @retval None
  */ 
void ADC_Icc_Init(void)
{
  ADC_InitTypeDef ADC_InitStructure;

/* Enable ADC clock */
  RCC_APB2PeriphClockCmd(RCC_APB2Periph_ADC1, ENABLE);

/* de-initialize ADC */
  ADC_DeInit(ADC1);

/*  ADC configured as follow:
  - NbrOfChannel = 1 - ADC_Channel_4
  - Mode = Single ConversionMode(ContinuousConvMode disabled)
  - Resolution = 12Bits
  - Prescaler = /1
  - sampling time 192 */

    /* ADC Configuration */
  ADC_StructInit(&ADC_InitStructure);
  ADC_InitStructure.ADC_Resolution = ADC_Resolution_12b;
  ADC_InitStructure.ADC_ScanConvMode = ENABLE;
  ADC_InitStructure.ADC_ContinuousConvMode = DISABLE;
  ADC_InitStructure.ADC_ExternalTrigConvEdge = ADC_ExternalTrigConvEdge_None;
  ADC_InitStructure.ADC_DataAlign = ADC_DataAlign_Right;
  ADC_InitStructure.ADC_NbrOfConversion = 1;
  ADC_Init(ADC1, &ADC_InitStructure);

  /* ADC1 regular channel4 configuration */
  ADC_RegularChannelConfig(ADC1, ADC_Channel_4, 1, ADC_SampleTime_192Cycles);
  ADC_DelaySelectionConfig(ADC1, ADC_DelayLength_Freeze);

  ADC_PowerDownCmd(ADC1, ADC_PowerDown_Idle_Delay, ENABLE);
  
  /* Enable ADC1 */
  ADC_Cmd(ADC1, ENABLE);
  
  /* Wait until ADC1 ON status */
  while (ADC_GetFlagStatus(ADC1, ADC_FLAG_ADONS) == RESET);
}

/**
  * @brief  To return the supply measurmeent
  * @caller several functions
  * @param None
  * @retval ADC value
  */ 
uint16_t ADC_Supply(void)
{
  uint8_t i;
  uint16_t res;

    /* Initializes ADC */
  ADC_Icc_Init();
 
  ADC_TempSensorVrefintCmd(ENABLE);

  /* ADC1 regular channel 17 for VREF configuration */
  ADC_RegularChannelConfig(ADC1, ADC_Channel_17, 1, ADC_SampleTime_192Cycles);
  
  /* initialize result */
  res = 0;
  for(i=4; i>0; i--)
  {
  /* start ADC convertion by software */
    ADC_SoftwareStartConv(ADC1);

    /* wait until end-of-covertion */
    while( ADC_GetFlagStatus(ADC1, ADC_FLAG_EOC) == 0 );
  /* read ADC convertion result */
    res += ADC_GetConversionValue(ADC1);
  }
	
  /* de-initialize ADC */
  ADC_TempSensorVrefintCmd(DISABLE);
  RCC_APB2PeriphClockCmd(RCC_APB2Periph_ADC1, DISABLE);
  
  return (res>>2);
}

/**
  * @brief To confgure RCC for current measurmeent
  * @caller  ADC_Icc_Test
  * @param Structure address for save the RCC configuration
  * @retval None
  */
void Config_RCC(RCC_TypeDef *sav_RCC)
{
  /* Save the RCC configuration registers */
  sav_RCC->AHBENR   = RCC->AHBENR;
  sav_RCC->APB1ENR  = RCC->APB1ENR;
  sav_RCC->APB2ENR  = RCC->APB2ENR;
  sav_RCC->AHBLPENR   = RCC->AHBLPENR;
  sav_RCC->APB1LPENR  = RCC->APB1LPENR;
  sav_RCC->APB2LPENR  = RCC->APB2LPENR;
  
  /* Set low power configuration */
  RCC->AHBENR = 0x05; // Ports A and C enable
  RCC->AHBLPENR = 0x05; 
  RCC->APB1ENR =  RCC_APB1ENR_PWREN;     // PWR management enable     
  RCC->APB2ENR = 0;
  
}

/**
  * @brief Current measurement
  * @caller main and ADC_Icc_Test
  * @param None
  * @retval ADC conversion value
  */
uint16_t Current_Measurement (void)
{
  uint16_t res,i;

  /* re-start ADC chanel 24 for Current measurement */
  ADC_Icc_Init();	

  /* initialize result */
  res = 0;

  for(i=4; i>0; i--)
  {
    /* start ADC convertion by software */
    ADC_SoftwareStartConv(ADC1);
    
    /* wait until end-of-covertion */
    while( ADC_GetFlagStatus(ADC1, ADC_FLAG_EOC) == 0 );
    
    /* read ADC convertion result */
    res += ADC_GetConversionValue(ADC1);
  }
   
  return (res>>2);
}

/**
  * @brief Current measurement in different MCU modes:
  * RUN/SLEEP/LowPower/STANDBY with/without RTC
  * @caller main and ADC_Icc_Test
  * @param MCU state
  * @retval ADC value.
  */
uint16_t ADC_Icc_Test(uint8_t Mcu_State)
{
  GPIO_InitTypeDef GPIO_InitStructure;
  uint16_t adc_measure;
  uint32_t i;
  RCC_TypeDef SavRCC;
  /* Reset UserButton State */
  UserButton = FALSE;
  /* Start counter */
  GPIO_HIGH(CTN_GPIO_PORT,CTN_CNTEN_GPIO_PIN);
  /* Disable the RTC Wakeup Interrupt */
  RTC_ITConfig(RTC_IT_WUT, DISABLE);
  /* Disable LCD */
  LCD_Cmd(DISABLE);
  /* wait until LCD disable */
  while (LCD_GetFlagStatus(LCD_FLAG_ENS) == SET);
  /*Reset Idd-WakeUP flag*/
  Idd_WakeUP = FALSE;
  /* Set IO in lowpower configuration*/
  GPIO_LowPower_Config(); 
  /*Disable fast wakeUp*/
  PWR_FastWakeUpCmd(DISABLE);
  
/* Test MCU state for configuration */
  switch (Mcu_State)
  {
    /* Run mode : Measurement Measurement performed with MSI 4 MHz without RTC*/	
    case MCU_RUN:
        /* switch on MSI clock */
        SetHSICLKToMSI(RCC_MSIRange_6,NoDIV2,NoRTC) ;   
        /* shitch on MSI clock */
        Config_RCC(&SavRCC);    
        SysTick->CTRL = 0;     
        RCC->APB1ENR = 0;

        /* To run nops during measurement:
        it's the best case for low current */     

        for (i=0;i<0xffff;i++) {
          __NOP();  __NOP();    __NOP();  __NOP();
          __NOP();  __NOP();    __NOP();  __NOP();
          __NOP();  __NOP();    __NOP();  __NOP();
          __NOP();  __NOP();    __NOP();  __NOP();
          __NOP();  __NOP();    __NOP();  __NOP();
          __NOP();  __NOP();    __NOP();  __NOP();
          __NOP();  __NOP();    __NOP();  __NOP();
          __NOP();  __NOP();    __NOP();  __NOP();
          __NOP();  __NOP();    __NOP();  __NOP();
          __NOP();  __NOP();    __NOP();  __NOP();
          __NOP();  __NOP();    __NOP();  __NOP();
        }
        
    break;

    /* SLEEP mode : Measurement performed with MSI 4 MHz without RTC in WFI mode*/
    case MCU_SLEEP:
         
        SetHSICLKToMSI(RCC_MSIRange_6,NoDIV2,NoRTC) ;   
        Config_RCC(&SavRCC);  
        Config_Systick_50ms();
        Delay(1);

       /* Request Wait For Interrupt */
        PWR_EnterSleepMode(PWR_Regulator_ON,PWR_SLEEPEntry_WFI);   
           
        break;    

   /* RUN LOW POWER mode :   Measurement performed with MSI 32 Khz without RTC */
    case MCU_LP_RUN:
      
        /* Disable PVD */
        PWR_PVDCmd(DISABLE);

        /* Enable The ultra Low Power Mode */
        PWR_UltraLowPowerCmd(ENABLE);         

        /* Save the RCC configuration registers */
        Config_RCC(&SavRCC);      
        
        /* Stop the sys tick in order to avoid IT */
        SysTick->CTRL = 0; 
        
#ifdef TESTINRAM        
        SetHSICLKToMSI(RCC_MSIRange_0,DIV2,NoRTC) ; 
        
        PWR_EnterLowPowerRunMode(ENABLE);
        while(PWR_GetFlagStatus(PWR_FLAG_REGLP) == RESET) ;  

        disableGlobalInterrupts();
        EnterLPRUNModeRAM();
        enableGlobalInterrupts();        
#else         
        /* Swith in MSI 32KHz */
        SetHSICLKToMSI(RCC_MSIRange_64KHz,DIV2,NoRTC) ;    
                
        PWR_EnterLowPowerRunMode(ENABLE);
        while(PWR_GetFlagStatus(PWR_FLAG_REGLP) == RESET) ;              
        
        /* Launch the counter */
        GPIO_LOW(CTN_GPIO_PORT,CTN_CNTEN_GPIO_PIN);           
           
        /* To run the nop during measurement:
        it's the best case for low current
        until counter reach detected by IT --> Idd_WakeUP */
        do{
          __NOP();  __NOP();    __NOP();  __NOP();
          __NOP();  __NOP();    __NOP();  __NOP(); 
          __NOP();  __NOP();    __NOP();  __NOP();
          __NOP();  __NOP();    __NOP();  __NOP();  
          __NOP();  __NOP();    __NOP();  __NOP();
          __NOP();  __NOP();    __NOP();  __NOP(); 
          __NOP();  __NOP();    __NOP();  __NOP();
          __NOP();  __NOP();    __NOP();  __NOP();            
        }  while (Idd_WakeUP == FALSE );       
#endif        
        
        PWR_EnterLowPowerRunMode(DISABLE);
        while(PWR_GetFlagStatus(PWR_FLAG_REGLP) != RESET) ;  
    
        break; 
      
      /* SLEEP LOW POWER mode
         Measurement done to MSI 32 Khz without RTC
      */	
      case MCU_LP_SLEEP:
        
        /* Disable PVD */
        PWR_PVDCmd(DISABLE);   
        
        /* Enable Ultra low power mode */
        PWR_UltraLowPowerCmd(ENABLE);

                
        /* To save the RCC configuration registers */
        Config_RCC(&SavRCC);     
        
        /* To stop the sys tick for avoid IT */
        SysTick->CTRL = 0; 
        
        /* Swith in MSI 32KHz */
        SetHSICLKToMSI(RCC_MSIRange_0,DIV2,NoRTC) ;

#ifdef TESTINRAM
        disableGlobalInterrupts();
        EnterLPSLEEPModeRAM();
        enableGlobalInterrupts();
#else        
        /* Falling edge for start counter */		
        GPIO_LOW(CTN_GPIO_PORT,CTN_CNTEN_GPIO_PIN);

        /* Request Wait For Interrupt */    
        PWR_EnterSleepMode(PWR_Regulator_LowPower,PWR_SLEEPEntry_WFI);
#endif              
        break;   
        
      /* STOP modes
       Measurement done to MSI 32 Khz without or with RTC
       */		
      case MCU_STOP_NoRTC:
      case MCU_STOP_RTC:

        /* Disable PVD */
        PWR_PVDCmd(DISABLE);
          
        /* Enable Ultra low power mode */
        PWR_UltraLowPowerCmd(ENABLE);           
        
        /* To save the RCC configuration registers */
        Config_RCC(&SavRCC);  

        /* To stop the sys tick for avoid IT */
        SysTick->CTRL = 0; 
               
       /* Swith in MSI 32KHz */
        if( Mcu_State == MCU_STOP_NoRTC )
          SetHSICLKToMSI(RCC_MSIRange_0,DIV2,NoRTC) ;
        else
         SetHSICLKToMSI(RCC_MSIRange_0,DIV2,WITHRTC) ;          

        /* Falling edge for start counter */		
        GPIO_LOW(CTN_GPIO_PORT,CTN_CNTEN_GPIO_PIN);
        
        /* Request Wait For Interrupt */    
        PWR_EnterSTOPMode(PWR_Regulator_LowPower,PWR_STOPEntry_WFI);              

        break;        
          
        /* Standby mode without RTC
          Measurement done to MSI 32 Khz without RTC
        */
        case MCU_STBY:
          
          /* Disable PVD */
          PWR_PVDCmd(DISABLE);
          
          /* Enable Ultra low power mode */
          PWR_UltraLowPowerCmd(ENABLE);
          
          RTC_OutputTypeConfig(RTC_OutputType_PushPull);
          RTC_OutputConfig(RTC_Output_WakeUp,RTC_OutputPolarity_High);        
          
          /* To configure PC13 WakeUP output */
          GPIO_InitStructure.GPIO_Pin = GPIO_Pin_13  ;
          GPIO_InitStructure.GPIO_OType = GPIO_OType_PP;
          GPIO_InitStructure.GPIO_PuPd = GPIO_PuPd_NOPULL;
          GPIO_InitStructure.GPIO_Speed = GPIO_Speed_400KHz;  
          GPIO_InitStructure.GPIO_Mode = GPIO_Mode_AF;
          GPIO_Init( GPIOC, &GPIO_InitStructure);   
          
          GPIO_PinAFConfig(GPIOC, GPIO_PinSource13,GPIO_AF_RTC_AF1) ;
          Config_RCC(&SavRCC);  
          
          SysTick->CTRL = 0; 
                  
          /* Swith in MSI 32KHz */
          SetHSICLKToMSI(RCC_MSIRange_0,DIV2,NoRTC) ;     
          
          PWR_WakeUpPinCmd(PWR_WakeUpPin_1,ENABLE);
          
          PWR_UltraLowPowerCmd(ENABLE); 
          
          PWR_EnterSTANDBYMode();
          /* Stop here WakeUp EXIT on RESET */
        
        break;
      }
  
  SetHSICLK();  

  Config_Systick(); 
  RCC->AHBENR = SavRCC.AHBENR;	
         
  PWR_VoltageScalingConfig(PWR_VoltageScaling_Range1);
  /* Wait Until the Voltage Regulator is ready */
  while (PWR_GetFlagStatus(PWR_FLAG_VOS) != RESET) ;

   /* Read ADC for current measurmeent */
   adc_measure = Current_Measurement();
    
  /* ICC_CNT_EN Hi */
  GPIO_HIGH(CTN_GPIO_PORT,CTN_CNTEN_GPIO_PIN);
  UserButton = TRUE;

  /* To restore RCC registers */
  RCC->APB1ENR = SavRCC.APB1ENR;
  RCC->APB2ENR = SavRCC.APB2ENR; 
  RCC->AHBLPENR = SavRCC.AHBLPENR;	
  RCC->APB1LPENR = SavRCC.APB1LPENR;
  RCC->APB2LPENR = SavRCC.APB2LPENR;
  
  /* Need to reinit RCC for LCD*/
  RCC_Configuration();

  PWR_EnterLowPowerRunMode(DISABLE);
  
  /* Disable Ultra low power mode */
  PWR_UltraLowPowerCmd(DISABLE);
  
  /* Disable FLASH during SLeep LP */
  FLASH_SLEEPPowerDownCmd(DISABLE);
  
  Restore_GPIO_Config();  
 
  /* Clear Wake Up flag */
  PWR_ClearFlag(PWR_FLAG_WU);
  
  /* Enable PVD */
  PWR_PVDCmd(ENABLE);

  LCD_GLASS_Init();
   
  return (adc_measure);
}



/******************* (C) COPYRIGHT 2011 STMicroelectronics *****END OF FILE****/
