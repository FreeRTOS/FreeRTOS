/**
  ******************************************************************************
  * @file    	    board.h
  * @author  	    FMD AE
  * @brief   		board Header File.             	
  * @version 	    V1.0.0           
  * @data		    2021-09-27
  ******************************************************************************
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
  
#ifndef __BOARD_H
#define __BOARD_H

/* Includes ---------------------------------------------------------------------*/
#include "ft32f0xx.h"
#include "config.h"
#include "Peripheral.h"

/* Public Constant prototypes----------------------------------------------------*/

/* Public typedef ---------------------------------------------------------------*/
typedef enum
{
	KEY_None = 0,
  KEY1_Data,
  KEY2_Data,
}KEY_DATA;

/* Public define ----------------------------------------------------------------*/
#define	LED_PORT		GPIOB
#define	LED1_PIN		GPIO_Pin_0
#define	LED2_PIN		GPIO_Pin_1
#define	LED3_PIN		GPIO_Pin_2
#define	LED4_PIN		GPIO_Pin_3
#define	KEY_PORT		GPIOC
#define	KEY1_PIN		GPIO_Pin_13
#define	KEY2_PIN		GPIO_Pin_11

#define LED1_ON   	GPIO_ResetBits(LED_PORT,LED1_PIN)
#define LED1_OFF   	GPIO_SetBits(LED_PORT,LED1_PIN)
#define LED2_ON   	GPIO_ResetBits(LED_PORT,LED2_PIN)
#define LED2_OFF   	GPIO_SetBits(LED_PORT,LED2_PIN)
#define LED3_ON   	GPIO_SetBits(LED_PORT,LED3_PIN)
#define LED3_OFF   	GPIO_ResetBits(LED_PORT,LED3_PIN)
#define LED4_ON   	GPIO_SetBits(LED_PORT,LED4_PIN)
#define LED4_OFF   	GPIO_ResetBits(LED_PORT,LED4_PIN)

#define KEY1_PRES GPIO_ReadInputDataBit(KEY_PORT,KEY1_PIN)
#define KEY2_PRES GPIO_ReadInputDataBit(KEY_PORT,KEY2_PIN)

/* Public variables prototypes --------------------------------------------------*/

/* Public function prototypes----------------------------------------------------*/
void Led_Init(void);
void Key_Init(void);
void SysTick_Configuration(void);
void TimingDelay_Decrement(void);
void SysTick_Delay_Ms(__IO uint32_t nTime);
void SysCLK48M(void);
void LED_Toggle(GPIO_TypeDef* GPIOx,uint16_t GPIO_Pin);
KEY_DATA Key_Scan(void);

#endif /* __BOARD_H */

/************************* (C) COPYRIGHT FMD *****END OF FILE*********************/
