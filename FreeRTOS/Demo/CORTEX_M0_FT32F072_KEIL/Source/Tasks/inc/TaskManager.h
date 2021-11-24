/**
  ******************************************************************************
  * @file    	    TaskManager.h
  * @author  	    FMD AE
  * @brief   		TaskManager Header File.             	
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
#ifndef __TASK_MANAGER_H__
#define __TASK_MANAGER_H__
/* Includes ---------------------------------------------------------------------*/
#include "config.h"
#include "HighProTask.h"
#include "LowProTask.h"

/* Public Constant prototypes----------------------------------------------------*/
/* Public typedef ---------------------------------------------------------------*/
typedef enum            
{
	eMsgOfHTaskIsNULL = 1,    
	eMsgFromSystick10ms,            
    eMsg_UART1_SEND_DATA,          
    eMsg_TOUCH_PROCESS,
}HighProTaskMessage;

typedef enum 
{
  	eMsgOfLTaskIsNULL = 1,		
	eMsgHalfSecondTimeOut,          
    eMsgKeyPress,
}LowProTaskMessage;

/* Public define ----------------------------------------------------------------*/
/* Public variables prototypes --------------------------------------------------*/
/* Public function prototypes----------------------------------------------------*/
void SendMessage(xQueueHandle Queue, const uint32_t msgType, const uint32_t msgValue);
void SendMessageFromISR(xQueueHandle Queue, const uint32_t msgType, const uint32_t msgValue);
#ifdef __cplusplus
extern "C"
{
#endif
void vApplicationTickHook(void);
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
#ifdef __cplusplus
}
#endif

#endif          // __TASK_MANAGER_H__
/************************* (C) COPYRIGHT FMD *****END OF FILE*********************/

