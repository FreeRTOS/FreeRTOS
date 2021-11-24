/**
  *********************************************************************************
  * @file    	    board.c
  * @author  	    FMD AE
  * @brief   		board program body 	
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
#include "board.h"

/* Private Constant --------------------------------------------------------------*/
/* Public Constant ---------------------------------------------------------------*/
/* Private typedef ---------------------------------------------------------------*/

/* Private variables -------------------------------------------------------------*/
__IO uint32_t TimingDelay;

/* Public variables --------------------------------------------------------------*/
/* Private function prototypes ---------------------------------------------------*/

/* Public function ------ --------------------------------------------------------*/

/**********************************************************************************
  * @brief  Led_Init program
  * @param  None
  * @note  
  * @retval None
  *********************************************************************************
*/
void Led_Init(void)
{
	GPIO_InitTypeDef	GPIO_InitStruct;
	RCC_AHBPeriphClockCmd(RCC_AHBPeriph_GPIOB,ENABLE);
	
	GPIO_InitStruct.GPIO_Pin = LED1_PIN | LED2_PIN | LED3_PIN | LED4_PIN;
	GPIO_InitStruct.GPIO_Mode = GPIO_Mode_OUT;
	GPIO_InitStruct.GPIO_OType = GPIO_OType_PP;
	GPIO_InitStruct.GPIO_PuPd = GPIO_PuPd_NOPULL;
	GPIO_InitStruct.GPIO_Speed = GPIO_Speed_50MHz;
	GPIO_Init(LED_PORT,&GPIO_InitStruct);		
	LED1_OFF;LED2_OFF;LED3_OFF;LED4_OFF;
}
/**********************************************************************************
  * @brief  LED_Toggle program
  * @param  GPIOx,GPIO_Pin
  * @note  
  * @retval None
  *********************************************************************************
*/
void LED_Toggle(GPIO_TypeDef* GPIOx,uint16_t GPIO_Pin)
{
	GPIO_WriteBit(GPIOx, GPIO_Pin, (BitAction)((1-GPIO_ReadOutputDataBit(GPIOx, GPIO_Pin))));
}

/**********************************************************************************
  * @brief  Key_Init program
  * @param  None
  * @note  
  * @retval None
  *********************************************************************************
*/
void Key_Init(void)
{
	GPIO_InitTypeDef	GPIO_InitStruct;
	RCC_AHBPeriphClockCmd(RCC_AHBPeriph_GPIOC,ENABLE);
	
	GPIO_InitStruct.GPIO_Pin = KEY1_PIN;
	GPIO_InitStruct.GPIO_Mode = GPIO_Mode_IN;
	GPIO_InitStruct.GPIO_PuPd = GPIO_PuPd_DOWN;
	GPIO_Init(KEY_PORT,&GPIO_InitStruct);		
	
	GPIO_InitStruct.GPIO_Pin = KEY2_PIN;
	GPIO_InitStruct.GPIO_PuPd = GPIO_PuPd_UP;
	GPIO_Init(KEY_PORT,&GPIO_InitStruct);		
}
/**********************************************************************************
  * @brief  Key_Scan program
  * @param  None
  * @note  
  * @retval KEY_DATA
  *********************************************************************************
*/
KEY_DATA Key_Scan(void)
{
	static uint8_t key_up=1;
	static uint8_t key_time=0;
	
	if(key_up&&(KEY1_PRES==1 || KEY2_PRES==0 ))
	{
		key_time++;
		if(key_time>=2)
		{
			key_up=0;
			if(KEY1_PRES==1) return KEY1_Data;
			if(KEY2_PRES==0) return KEY2_Data;
		}
	}
	else if(KEY1_PRES==0 && KEY2_PRES==1)
	{
		key_up=1;
		key_time=0;
	}
	return KEY_None;
}
/**********************************************************************************
  * @brief  SysTick_Configuration program
  * @param  None
  * @note  
  * @retval None
  *********************************************************************************
*/
void SysTick_Configuration(void)
{
	if(SysTick_Config(SystemCoreClock/TICK_RATE_HZ))
	{
		while(1);
	}
  SysTick_CLKSourceConfig(SysTick_CLKSource_HCLK);
  NVIC_SetPriority(SysTick_IRQn, 0x04);	
}

/**********************************************************************************
  * @brief  TimingDelay_Decrement program
  * @param  None
  * @note  
  * @retval None
  *********************************************************************************
*/
void TimingDelay_Decrement(void)
{
	if(TimingDelay != 0x00)
	{
		TimingDelay--;
	}
}

/**********************************************************************************
  * @brief  SysTick_Delay_Ms program
  * @param  nTime
  * @note  
  * @retval None
  *********************************************************************************
*/
void SysTick_Delay_Ms(__IO uint32_t nTime)
{
	TimingDelay = nTime/10;			
	while(TimingDelay != 0);	
}

/**********************************************************************************
  * @brief  SysCLK48M program
  * @param  None
  * @note  
  * @retval None
  *********************************************************************************
*/
void SysCLK48M(void)
{
  __IO uint32_t StartUpCounter = 0, HSIStatus = 0;

  /* Enable HSI */    
  RCC->CR |= ((uint32_t)RCC_CR_HSION);
 
  /* Wait till HSI is ready and if Time out is reached exit */
  do
  {
    HSIStatus = RCC->CR & RCC_CR_HSIRDY;
    StartUpCounter++;  
  } while((HSIStatus == 0) && (StartUpCounter != HSI_STARTUP_TIMEOUT));

  if ((RCC->CR & RCC_CR_HSIRDY) != RESET)
  {
    HSIStatus = (uint32_t)0x01;
  }
  else
  {
    HSIStatus = (uint32_t)0x00;
  }  

  if (HSIStatus == (uint32_t)0x01)
  {
    /* Enable Prefetch Buffer and set Flash Latency */
    FLASH->ACR = FLASH_ACR_PRFTBE | FLASH_ACR_LATENCY;
 
    /* HCLK = SYSCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_HPRE_DIV1;
      
    /* PCLK = HCLK */
    RCC->CFGR |= (uint32_t)RCC_CFGR_PPRE_DIV1;

    /* PLL configuration */
    RCC->CFGR &= (uint32_t)((uint32_t)~(RCC_CFGR_PLLSRC | RCC_CFGR_PLLXTPRE | RCC_CFGR_PLLMULL));
    RCC->CFGR |= (uint32_t)(RCC_CFGR_PLLSRC_HSI_PREDIV | RCC_CFGR_PLLXTPRE_PREDIV1 | RCC_CFGR_PLLMULL6);
            
    /* Enable PLL */
    RCC->CR |= RCC_CR_PLLON;

    /* Wait till PLL is ready */
    while((RCC->CR & RCC_CR_PLLRDY) == 0)
    {
    }

    /* Select PLL as system clock source */
    RCC->CFGR &= (uint32_t)((uint32_t)~(RCC_CFGR_SW));
    RCC->CFGR |= (uint32_t)RCC_CFGR_SW_PLL;    

    /* Wait till PLL is used as system clock source */
    while ((RCC->CFGR & (uint32_t)RCC_CFGR_SWS) != (uint32_t)RCC_CFGR_SWS_PLL)
    {
    }
  }
}

/* Private function ------ -------------------------------------------------------*/
/**
  * @}
  */

/************************ (C) COPYRIGHT FMD *****END OF FILE***********************/
