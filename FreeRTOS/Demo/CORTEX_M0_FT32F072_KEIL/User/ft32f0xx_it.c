/**
  *********************************************************************************
  * @file    	    FT32F0xx_it.c
  * @author  	    FMD AE
  * @brief   		FT32F0xx_it program body 	
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
#include "ft32f0xx_it.h"
#include "IntQueueTimer.h"
/* Private Constant --------------------------------------------------------------*/
/* Public Constant ---------------------------------------------------------------*/
/* Private typedef ---------------------------------------------------------------*/
/* Private variables -------------------------------------------------------------*/
/* Public variables --------------------------------------------------------------*/
/* Private function prototypes ---------------------------------------------------*/
/* Public function ------ --------------------------------------------------------*/
/* Private function ------ -------------------------------------------------------*/

/**********************************************************************************
  * @brief  NMI_Handler program.
  * @param  None
  * @note
  * @retval None
  *********************************************************************************
*/
void NMI_Handler(void)
{
}

/**********************************************************************************
  * @brief  HardFault_Handler program.
  * @param  None
  * @note
  * @retval None
  *********************************************************************************
*/
void HardFault_Handler(void)
{

}



/**********************************************************************************
  * @brief  USART1_IRQHandler program.
  * @param  None
  * @note
  * @retval None
  *********************************************************************************
*/
void USART1_IRQHandler(void)
{
	uint16_t Len;
	if(USART_GetFlagStatus(USART1,USART_FLAG_IDLE) != RESET)	
	{
		USART_ClearFlag(USART1,USART_FLAG_IDLE);								
		DMA_Cmd(DMA1_Channel3,DISABLE);													
		DMA_ClearFlag(DMA1_FLAG_TC3);														
		Len = RX_SIZE - DMA_GetCurrDataCounter(DMA1_Channel3);		               
		DMA_SetCurrDataCounter(DMA1_Channel3,RX_SIZE);					
		DMA_Cmd(DMA1_Channel3,ENABLE);											
        if(Len != 0)
        SendMessageFromISR(xHighProTaskQueue,eMsg_UART1_SEND_DATA,Len);
	}
}
/**********************************************************************************
  * @brief  TIM1_BRK_UP_TRG_COM_IRQHandler program.
  * @param  None
  * @note
  * @retval None
  *********************************************************************************
*/
void TIM1_BRK_UP_TRG_COM_IRQHandler(void)
{
	if(TIM_GetITStatus(TIM1,TIM_IT_Update) != RESET)
	{
		TIM_ClearITPendingBit(TIM1, TIM_IT_Update);
	#if mainCREATE_DEMO_ONLY != 1
		IntQueueTestTimerHandler();
	#endif
	}
}

/**********************************************************************************
  * @brief  TIM16_IRQHandler program.
  * @param  None
  * @note
  * @retval None
  *********************************************************************************
*/
void TIM16_IRQHandler(void)
{
	uint8_t g_cKeyData;
	if(TIM_GetITStatus(TIM16,TIM_IT_Update) != RESET)
	{
		TIM_ClearITPendingBit(TIM16, TIM_IT_Update);	                
	}
}


/************************* (C) COPYRIGHT FMD *****END OF FILE*********************/
