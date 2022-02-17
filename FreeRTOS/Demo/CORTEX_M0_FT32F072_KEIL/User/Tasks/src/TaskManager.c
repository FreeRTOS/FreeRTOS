/**
  *********************************************************************************
  * @file    	    TaskManager.c
  * @author  	    FMD AE
  * @brief   		TaskManager program body 	
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
#include "TaskManager.h"
/* Private Constant --------------------------------------------------------------*/
/* Public Constant ---------------------------------------------------------------*/
/* Private typedef ---------------------------------------------------------------*/
/* Private variables -------------------------------------------------------------*/
static volatile uint32_t ulSystemTimeTickCount = 0;
/* Public variables --------------------------------------------------------------*/
/* Private function prototypes ---------------------------------------------------*/
void SendShortMessageFromISR(xQueueHandle Queue, const uint32_t msgType);
/* Public function ------ --------------------------------------------------------*/
/**********************************************************************************
  * @brief  SendMessage program.
  * @param  Queue,msgType,msgValue
  * @note
  * @retval None
  *********************************************************************************
*/
void SendMessage(xQueueHandle Queue, const uint32_t msgType, const uint32_t msgValue)
{                                                                           
	uint32_t macroMsg = msgType | (((uint32_t)msgValue) << 8 );                 
	xQueueSend( Queue, (const void*)&macroMsg, (portTickType)0);            
}
/**********************************************************************************
  * @brief  SendShortMessageFromISR program.
  * @param  Queue,msgType
  * @note
  * @retval None
  *********************************************************************************
*/
void SendShortMessageFromISR(xQueueHandle Queue, const uint32_t msgType)
{
	signed portBASE_TYPE needSchedule = FALSE;
	xQueueSendFromISR( Queue, (const void*)&msgType, &needSchedule);
	portEND_SWITCHING_ISR(needSchedule);  
}
/**********************************************************************************
  * @brief  SendMessageFromISR program.
  * @param  Queue,msgType,msgValue
  * @note
  * @retval None
  *********************************************************************************
*/
void SendMessageFromISR(xQueueHandle Queue, const uint32_t msgType, const uint32_t msgValue)
{                                                                               
	signed portBASE_TYPE needSchedule = FALSE;
	uint32_t macroMsg = msgType | (((uint32_t)msgValue) << 8 );
	xQueueSendFromISR( Queue, (const void*)&macroMsg, &needSchedule);
	portEND_SWITCHING_ISR(needSchedule);  
}

#ifdef __cplusplus
extern "C"
{
#endif
/**********************************************************************************
  * @brief  vApplicationTickHook program.
  * @param  None
  * @note
  * @retval None
  *********************************************************************************
*/
#if mainCREATE_DEMO_ONLY == 1
void vApplicationTickHook( void )  
{
	ulSystemTimeTickCount++;
	if ( (ulSystemTimeTickCount&0x0A) == 0 )    SendShortMessageFromISR(xHighProTaskQueue, eMsgFromSystick10ms);
	if ( (ulSystemTimeTickCount%500)   == 0 )    SendShortMessageFromISR(xLowProTaskQueue, eMsgHalfSecondTimeOut);
}
#endif
/**********************************************************************************
  * @brief  vApplicationMallocFailedHook program.
  * @param  None
  * @note
  * @retval None
  *********************************************************************************
*/
void vApplicationMallocFailedHook( void )
{
	/* vApplicationMallocFailedHook() will only be called if
	configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
	function that will get called if a call to pvPortMalloc() fails.
	pvPortMalloc() is called internally by the kernel whenever a task, queue,
	timer or semaphore is created.  It is also called by various parts of the
	demo application.  If heap_1.c or heap_2.c are used, then the size of the
	heap available to pvPortMalloc() is defined by configTOTAL_HEAP_SIZE in
	FreeRTOSConfig.h, and the xPortGetFreeHeapSize() API function can be used
	to query the size of free heap space that remains (although it does not
	provide information on how the remaining heap might be fragmented). */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/**********************************************************************************
  * @brief  vApplicationStackOverflowHook program.
  * @param  pxTask,*pcTaskName
  * @note
  * @retval None
  *********************************************************************************
*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}

/*-----------------------------------------------------------*/
#ifdef __cplusplus
}
#endif
/************************* (C) COPYRIGHT FMD *****END OF FILE*********************/
