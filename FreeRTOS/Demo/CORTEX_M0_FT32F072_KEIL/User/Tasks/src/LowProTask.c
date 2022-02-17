/**
  *********************************************************************************
  * @file    	    LowproTask.c
  * @author  	    FMD AE
  * @brief   		LowproTask program body 	
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
#include "LowProTask.h"
/* Private Constant --------------------------------------------------------------*/
/* Public Constant ---------------------------------------------------------------*/
/* Private typedef ---------------------------------------------------------------*/
/* Private variables -------------------------------------------------------------*/
/* Public variables --------------------------------------------------------------*/
xQueueHandle xLowProTaskQueue;

/* Private function prototypes ---------------------------------------------------*/
static void LowProTask(void *pvParameters);

/* Public function ------ --------------------------------------------------------*/
/**********************************************************************************
  * @brief  CreateLowProTask program.
  * @param  *pvParameters
  * @note
  * @retval None
  *********************************************************************************
*/
void CreateLowProTask(void)
{
  	xLowProTaskQueue = xQueueCreate(16, sizeof( unsigned portLONG ) );
	xTaskCreate(LowProTask, ( portCHAR const* ) "LowProTask", LOWPROTASK_STACK_SIZE, NULL, TASK_PRIO_LOW, NULL);
}

/* Private function ------ -------------------------------------------------------*/
/**********************************************************************************
  * @brief  LowProTask program.
  * @param  *pvParameters
  * @note
  * @retval None
  *********************************************************************************
*/
static void LowProTask(void *pvParameters)
{
    while(1)
    {	
        IWDG_ReloadCounter();
        portBASE_TYPE lRxNews = (uint32_t)eMsgOfLTaskIsNULL;

        xQueueReceive( xLowProTaskQueue, (void*)&( lRxNews), portMAX_DELAY );
		
		switch(lRxNews & 0xFF)
		{
			case eMsgHalfSecondTimeOut:  
				 LED_Flash();   
				 ADC_Measure();	
			break;
			case eMsgKeyPress:
				 Key_Pro(lRxNews>>8); 
			break;        
			default: 
			break;
        }		
        lRxNews = eMsgOfLTaskIsNULL;
    }
}
/************************* (C) COPYRIGHT FMD *****END OF FILE*********************/
