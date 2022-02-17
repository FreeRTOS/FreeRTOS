/**
  *********************************************************************************
  * @file    	    main_standartest.c
  * @author  	    FMD AE
  * @brief   		main_standartest program body 	
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
#include "main.h"
#include "TestRunner.h"
/* Private Constant --------------------------------------------------------------*/
/* Public Constant ---------------------------------------------------------------*/
/* Private typedef ---------------------------------------------------------------*/
/* Private variables -------------------------------------------------------------*/
/* Public variables --------------------------------------------------------------*/
/* Private function prototypes ---------------------------------------------------*/
/* Public function ------ --------------------------------------------------------*/
/* Private function ------ -------------------------------------------------------*/
void main_standartest(void);
/**********************************************************************************
  * @brief  main program
  * @param  
  * @note  
  * @retval 
  *********************************************************************************
*/
void main_standartest(void)
{
	
	Usart_Init();
    vStartTests();

    /* Should never reach here. */
    for( ; ; );
}


///******************************************************************************
//  * @brief  Usart_Init program.
//  * @param  None
//  * @retval None
//  *****************************************************************************
//*/
//void Usart_Init(void)
//{
//	USART_InitTypeDef USART_InitStruct;
//	GPIO_InitTypeDef GPIO_InitStruct;
//	NVIC_InitTypeDef NVIC_InitStructure;
//	
//	RCC_AHBPeriphClockCmd(RCC_AHBPeriph_GPIOA,ENABLE);	
//	RCC_APB2PeriphClockCmd(RCC_APB2Periph_USART1,ENABLE);

//	/*GPIO INIT*/
//	GPIO_InitStruct.GPIO_Pin = GPIO_Pin_9;
//	GPIO_InitStruct.GPIO_Mode = GPIO_Mode_AF;
//	GPIO_InitStruct.GPIO_Speed = GPIO_Speed_50MHz;
//	GPIO_InitStruct.GPIO_OType = GPIO_OType_PP;
//	GPIO_InitStruct.GPIO_PuPd = GPIO_PuPd_NOPULL;
//	GPIO_Init(GPIOA,&GPIO_InitStruct);	
//	GPIO_PinAFConfig(GPIOA,GPIO_PinSource9,GPIO_AF_1);
//	
//	USART_InitStruct.USART_BaudRate = 115200;
//	USART_InitStruct.USART_WordLength = USART_WordLength_8b;
//	USART_InitStruct.USART_StopBits = USART_StopBits_1;
//	USART_InitStruct.USART_Parity = USART_Parity_No;
//	USART_InitStruct.USART_Mode = USART_Mode_Tx;
//	USART_InitStruct.USART_HardwareFlowControl = USART_HardwareFlowControl_None;
//	USART_Init(USART1,&USART_InitStruct);
//	USART_Cmd(USART1,ENABLE);
//}


/************************ (C) COPYRIGHT FMD *****END OF FILE***********************/




