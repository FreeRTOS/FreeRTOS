/**
  ******************************************************************************
  * @file    	    Peripheral.h
  * @author  	    FMD AE
  * @brief   		Peripheral Header File.             	
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
  
#ifndef __PERIPHERALL_H
#define __PERIPHERALL_H

/* Includes ---------------------------------------------------------------------*/
#include "ft32f0xx.h"
#include "board.h"
/* Public Constant prototypes----------------------------------------------------*/
extern const uint16_t TICK_RATE_HZ;

/* Public typedef ---------------------------------------------------------------*/
typedef enum {FAILED = 0, PASSED = !FAILED} TestStatus;
/* Public define ----------------------------------------------------------------*/
#define  RX_SIZE   40
/* Public variables prototypes --------------------------------------------------*/
extern __IO uint32_t CaptureNumber, PeriodValue;
extern __IO uint16_t  ADC1ConvertedValue , ADC1ConvertedVoltage ;
extern __IO uint32_t Timecount;
extern __IO uint8_t usart_rx_buff[];

/* Public function prototypes----------------------------------------------------*/
void Usart_Init(void);
void ADC_Config(void);
void ADC_Measure(void);
void Iwdg_Init(void);
void LED_Flash(void);
void Key_Pro(uint8_t Key_Value);
void TIM_PWM_Init(void);
void KEY_Scan(uint8_t iKeyData);


#endif /* __PERIPHERALL_H */

/************************* (C) COPYRIGHT FMD *****END OF FILE*********************/
