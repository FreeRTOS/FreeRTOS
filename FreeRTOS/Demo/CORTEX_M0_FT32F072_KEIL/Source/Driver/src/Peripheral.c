/**
  *********************************************************************************
  * @file    	    Peripheral.c
  * @author  	    FMD AE
  * @brief   		Peripheral program body 	
  * @version 	    V1.0.0           
  * @data		    2021-09-27
  *********************************************************************************
  * @attention
  * COPYRIGHT (C) 2021 Fremont Micro Devices (SZ) Corporation All rights reserved.
  *    This software is provided by the copyright holders and contributors,and the
  *software is believed to be accurate and reliable. However, Fremont Micro Devices
  *(SZ) Corporation assumes no responsibility for the consequences of use of such
  *software or for any infringement of patents of other rights of third parties,
  *which may result from its use. No license is granted by implication or otherwise
  *under any patent rights of Fremont Micro Devices (SZ) Corporation.
  *  ******************************************************************************
  */
/* Includes ----------------------------------------------------------------------*/  
#include "Peripheral.h"
/* Private Constant --------------------------------------------------------------*/
/* Public Constant ---------------------------------------------------------------*/
const uint16_t TICK_RATE_HZ = 100;
/* Private typedef ---------------------------------------------------------------*/

/* Private variables -------------------------------------------------------------*/
uint16_t Channel1Pulse;
uint16_t TimerPeriod;

/* Public variables --------------------------------------------------------------*/
__IO uint32_t CaptureNumber, PeriodValue;
__IO uint16_t  ADC1ConvertedValue = 0, ADC1ConvertedVoltage = 0;
__IO uint32_t Timecount;
__IO uint8_t usart_rx_buff[RX_SIZE];

/* Private function prototypes ---------------------------------------------------*/
static void DMA_USART_RX_Config(void);

/* Public function ------ --------------------------------------------------------*/

/**********************************************************************************
  * @brief  Usart_Init program
  * @param  None
  * @note  
  * @retval None
  *********************************************************************************
*/
void Usart_Init(void)
{
	USART_InitTypeDef USART_InitStruct;
	GPIO_InitTypeDef GPIO_InitStruct;
	NVIC_InitTypeDef NVIC_InitStructure;
	
	RCC_AHBPeriphClockCmd(RCC_AHBPeriph_GPIOA,ENABLE);	
	RCC_APB2PeriphClockCmd(RCC_APB2Periph_USART1,ENABLE);

	/*GPIO INIT*/
	GPIO_InitStruct.GPIO_Pin = GPIO_Pin_9 | GPIO_Pin_10;
	GPIO_InitStruct.GPIO_Mode = GPIO_Mode_AF;
	GPIO_InitStruct.GPIO_Speed = GPIO_Speed_50MHz;
	GPIO_InitStruct.GPIO_OType = GPIO_OType_PP;
	GPIO_InitStruct.GPIO_PuPd = GPIO_PuPd_NOPULL;
	GPIO_Init(GPIOA,&GPIO_InitStruct);	

	GPIO_PinAFConfig(GPIOA,GPIO_PinSource9,GPIO_AF_1);
	GPIO_PinAFConfig(GPIOA,GPIO_PinSource10,GPIO_AF_1);
	
	
	USART_InitStruct.USART_BaudRate = 115200;
	USART_InitStruct.USART_WordLength = USART_WordLength_8b;
	USART_InitStruct.USART_StopBits = USART_StopBits_1;
	USART_InitStruct.USART_Parity = USART_Parity_No;
	USART_InitStruct.USART_Mode = USART_Mode_Tx | USART_Mode_Rx;
	USART_InitStruct.USART_HardwareFlowControl = USART_HardwareFlowControl_None;
	USART_Init(USART1,&USART_InitStruct);
	USART_Cmd(USART1,ENABLE);

	NVIC_InitStructure.NVIC_IRQChannel = USART1_IRQn;
	NVIC_InitStructure.NVIC_IRQChannelPriority = 0;
	NVIC_InitStructure.NVIC_IRQChannelCmd = ENABLE;
	NVIC_Init(&NVIC_InitStructure);
	

	USART_ITConfig(USART1,USART_IT_IDLE,ENABLE);	
	USART_ClearFlag(USART1,USART_FLAG_IDLE);
	
	DMA_USART_RX_Config();

	USART_DMAReceptionErrorConfig(USART1,USART_DMAOnError_Enable);

	USART_DMACmd(USART1,USART_DMAReq_Rx,ENABLE);

	DMA_Cmd(DMA1_Channel3,ENABLE);
	
//	printf("USART1 Init was complete!\r\n");
}

/**********************************************************************************
  * @brief  ADC_Config program
  * @param  None
  * @note  
  * @retval None
  *********************************************************************************
*/
void ADC_Config(void)
{
  ADC_InitTypeDef     ADC_InitStructure;
  GPIO_InitTypeDef    GPIO_InitStructure;
  
  RCC_AHBPeriphClockCmd(RCC_AHBPeriph_GPIOC, ENABLE);
  RCC_APB2PeriphClockCmd(RCC_APB2Periph_ADC1, ENABLE);
  
  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_0 ;
  GPIO_InitStructure.GPIO_Mode = GPIO_Mode_AN;
  GPIO_InitStructure.GPIO_PuPd = GPIO_PuPd_NOPULL ;
  GPIO_Init(GPIOC, &GPIO_InitStructure);
  
  ADC_DeInit(ADC1);
  ADC_StructInit(&ADC_InitStructure);
  ADC_InitStructure.ADC_Resolution = ADC_Resolution_12b;
  ADC_InitStructure.ADC_ContinuousConvMode = ENABLE; 
  ADC_InitStructure.ADC_ExternalTrigConvEdge = ADC_ExternalTrigConvEdge_None;
  ADC_InitStructure.ADC_DataAlign = ADC_DataAlign_Right;
  ADC_InitStructure.ADC_ScanDirection = ADC_ScanDirection_Upward;
  ADC_Init(ADC1, &ADC_InitStructure);
	
  ADC_VrefselConfig(ADC_Vrefsel_2_5V);		

  ADC_ChannelConfig(ADC1, ADC_Channel_10 , ADC_SampleTime_239_5Cycles);

  /* ADC Calibration */
  ADC_GetCalibrationFactor(ADC1);
  
  /* Enable the ADC peripheral */
  ADC_Cmd(ADC1, ENABLE);     
  
  /* Wait the ADRDY flag */
  while(!ADC_GetFlagStatus(ADC1, ADC_FLAG_ADRDY)); 
  
  /* ADC1 regular Software Start Conv */ 
  ADC_StartOfConversion(ADC1);
}
/**********************************************************************************
  * @brief  ADC_Measure program
  * @param  None
  * @note  
  * @retval None
  *********************************************************************************
*/
void ADC_Measure(void)
{	
  uint32_t ADC_Max,ADC_Min,ADC_SUM = 0;
  uint32_t ADC_Buff[10];
  for(uint8_t i = 0;i<10;i++)
  {
          /* Test EOC flag */
          while(ADC_GetFlagStatus(ADC1, ADC_FLAG_EOC) == RESET);
          
          /* Get ADC1 converted data */
          ADC1ConvertedValue =ADC_GetConversionValue(ADC1);
          
          /* Compute the voltage */
          ADC_Buff[i] = (ADC1ConvertedValue *2500)/0xFFF;		
  }
  ADC_Max = ADC_Min = ADC_Buff[0];
  for(uint8_t i = 0;i<10;i++)
  {	
          ADC_SUM += ADC_Buff[i];
          if(ADC_Buff[i]>ADC_Max)ADC_Max = ADC_Buff[i];
          else if(ADC_Buff[i]<ADC_Min)ADC_Min = ADC_Buff[i];		
  }
  ADC1ConvertedVoltage = (ADC_SUM - ADC_Max - ADC_Min)/8;
  printf("ADC_DATA = 0x%02x\r\n",ADC1ConvertedVoltage);		

}
/**********************************************************************************
  * @brief  TIM_PWM_Init program
  * @param  None
  * @note  
  * @retval None
  *********************************************************************************
*/
void TIM_PWM_Init(void)
{
  TIM_TimeBaseInitTypeDef  TIM_TimeBaseStructure;
  TIM_OCInitTypeDef  TIM_OCInitStructure;
  GPIO_InitTypeDef GPIO_InitStructure;
  NVIC_InitTypeDef NVIC_InitStructure;
	
  RCC_AHBPeriphClockCmd(RCC_AHBPeriph_GPIOB, ENABLE); 
  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_6;
  GPIO_InitStructure.GPIO_Mode = GPIO_Mode_AF;
  GPIO_InitStructure.GPIO_Speed = GPIO_Speed_50MHz;
  GPIO_InitStructure.GPIO_OType = GPIO_OType_PP;
  GPIO_InitStructure.GPIO_PuPd = GPIO_PuPd_UP ;
  GPIO_Init(GPIOB, &GPIO_InitStructure);											/* GPIOA Configuration: Channel 1 */
  GPIO_PinAFConfig(GPIOB, GPIO_PinSource6, GPIO_AF_2);		
    
  
  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_8;
  GPIO_Init(GPIOB, &GPIO_InitStructure); 											/* GPIOB Configuration: Channel 1N*/
  GPIO_PinAFConfig(GPIOB, GPIO_PinSource8, GPIO_AF_2); 
 
  /* Compute the value to be set in ARR regiter to generate signal frequency at 20 Khz */
  TimerPeriod = (SystemCoreClock / 20000 ) - 1;
  /* Compute CCR1 value to generate a duty cycle at 50% for channel 1 and 1N */
  Channel1Pulse = (uint16_t) (((uint32_t) 5 * (TimerPeriod - 1)) / 10);

  /* TIM1 clock enable */
  RCC_APB2PeriphClockCmd(RCC_APB2Periph_TIM16 , ENABLE);
  
  /* Time Base configuration */
  TIM_TimeBaseStructure.TIM_Prescaler = 0;
  TIM_TimeBaseStructure.TIM_CounterMode = TIM_CounterMode_Up;
  TIM_TimeBaseStructure.TIM_Period = TimerPeriod;
  TIM_TimeBaseStructure.TIM_ClockDivision = 0;
  TIM_TimeBaseStructure.TIM_RepetitionCounter = 0;
  TIM_TimeBaseInit(TIM16, &TIM_TimeBaseStructure);

  /* Channel 1, 2,3 and 4 Configuration in PWM mode */
  TIM_OCInitStructure.TIM_OCMode = TIM_OCMode_PWM2;
  TIM_OCInitStructure.TIM_OutputState = TIM_OutputState_Enable;
  TIM_OCInitStructure.TIM_OutputNState = TIM_OutputNState_Enable;
  TIM_OCInitStructure.TIM_Pulse = Channel1Pulse;
  TIM_OCInitStructure.TIM_OCPolarity = TIM_OCPolarity_Low;
  TIM_OCInitStructure.TIM_OCNPolarity = TIM_OCNPolarity_Low;
  TIM_OCInitStructure.TIM_OCIdleState = TIM_OCIdleState_Set;
  TIM_OCInitStructure.TIM_OCNIdleState = TIM_OCIdleState_Reset;
  TIM_OC1Init(TIM16, &TIM_OCInitStructure);
  /* TIM1 counter enable */
  TIM_Cmd(TIM16, ENABLE);
  /* Enable the CC2 Interrupt Request */

  
  /* Enable the TIM1 global Interrupt */
  NVIC_InitStructure.NVIC_IRQChannel = TIM16_IRQn;
  NVIC_InitStructure.NVIC_IRQChannelPriority = 0;
  NVIC_InitStructure.NVIC_IRQChannelCmd = ENABLE;
  NVIC_Init(&NVIC_InitStructure);

  TIM_ITConfig(TIM16, TIM_IT_Update, ENABLE);
  TIM_ClearITPendingBit(TIM16, TIM_IT_Update); 
  
  /* TIM1 Main Output Enable */
  TIM_CtrlPWMOutputs(TIM16, ENABLE);
}
/**********************************************************************************
  * @brief  Iwdg_Init program
  * @param  None
  * @note  
  * @retval None
  *********************************************************************************
*/
void Iwdg_Init(void)
{
	RCC_LSICmd(ENABLE);
	while((RCC ->CSR & RCC_CSR_LSIRDY) == 0);		//wait LSI ready	
	for(uint32_t i=1000;i>0;i--)
	{
		__ASM("NOP");
	}	
	IWDG_Enable();

	IWDG_WriteAccessCmd(IWDG_WriteAccess_Enable);
	
	IWDG_SetPrescaler(IWDG_Prescaler_16);
	while(IWDG_GetFlagStatus(IWDG_FLAG_PVU) == SET);
	
	IWDG_SetReload(500);
	while(IWDG_GetFlagStatus(IWDG_FLAG_RVU) == SET);
	
	IWDG_ReloadCounter();
}

/**********************************************************************************
  * @brief  LED_Flash program
  * @param  None
  * @note  
  * @retval None
  *********************************************************************************
*/
void LED_Flash(void)
{
   LED_Toggle(LED_PORT,LED3_PIN);
}
/**********************************************************************************
  * @brief  Key_Pro program
  * @param  Key_Value
  * @note  
  * @retval None
  *********************************************************************************
*/
void Key_Pro(uint8_t Key_Value)
{

	if(Key_Value)
	{
		switch(Key_Value)
		{
			case KEY1_Data:
				LED_Toggle(LED_PORT,LED4_PIN);
				if(Channel1Pulse<TimerPeriod-100)Channel1Pulse += 100;
				TIM_SetCompare1(TIM16,Channel1Pulse);
				printf("KEY1 PRESS, PWMPeriod = %02x, PWMPulse = %02x\r\n",TimerPeriod,Channel1Pulse);
				break;
			case KEY2_Data:
				LED_Toggle(LED_PORT,LED4_PIN);
				if(Channel1Pulse>100)Channel1Pulse -= 100;
				TIM_SetCompare1(TIM16,Channel1Pulse);			
				printf("KEY2 PRESS, PWMPeriod = %02x, PWMPulse = %02x\r\n",TimerPeriod,Channel1Pulse);
				break;			
		}	
	}
}
/**********************************************************************************
  * @brief  fputc program
  * @param  int ch, FILE *f
  * @note  
  * @retval None
  *********************************************************************************
*/
int fputc(int ch, FILE *f)
{
	while(USART_GetFlagStatus(USART1,USART_FLAG_TC)==RESET)
	{ 

	}
	USART_SendData(USART1,(uint8_t) ch);
	return ch;
}


/* Private function ------ -------------------------------------------------------*/
/**********************************************************************************
  * @brief  DMA_USART_RX_Config program.
  * @param  None
  * @note
  * @retval None
  *********************************************************************************
*/
static void DMA_USART_RX_Config(void)
{
	DMA_InitTypeDef DMA_InitStruct;
	RCC_AHBPeriphClockCmd(RCC_AHBPeriph_DMA1,ENABLE);
	
	DMA_InitStruct.DMA_BufferSize = RX_SIZE;
	DMA_InitStruct.DMA_DIR = DMA_DIR_PeripheralSRC;
	DMA_InitStruct.DMA_M2M = DMA_M2M_Disable;
	DMA_InitStruct.DMA_MemoryBaseAddr = (uint32_t)&usart_rx_buff[0];
	DMA_InitStruct.DMA_MemoryDataSize = 8;
	DMA_InitStruct.DMA_MemoryInc = DMA_MemoryInc_Enable;
	DMA_InitStruct.DMA_Mode = DMA_Mode_Normal;
	DMA_InitStruct.DMA_PeripheralBaseAddr = (uint32_t)&USART1->RDR;
	DMA_InitStruct.DMA_PeripheralDataSize = 8;
	DMA_InitStruct.DMA_PeripheralInc = DMA_PeripheralInc_Disable;
	DMA_InitStruct.DMA_Priority = DMA_Priority_Low;	
	DMA_Init(DMA1_Channel3,&DMA_InitStruct);
}


/************************* (C) COPYRIGHT FMD *****END OF FILE*********************/
