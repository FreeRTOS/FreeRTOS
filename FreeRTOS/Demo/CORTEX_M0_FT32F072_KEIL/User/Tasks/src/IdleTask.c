/**
  *********************************************************************************
  * @file    	    IdleTask.c
  * @author  	    FMD AE
  * @brief   		IdleTask program body 	
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
#include "IdleTask.h"

/* Private Constant --------------------------------------------------------------*/
/* Public Constant ---------------------------------------------------------------*/
/* Private typedef ---------------------------------------------------------------*/
/* Private variables -------------------------------------------------------------*/
/* Public variables --------------------------------------------------------------*/
/* Private function prototypes ---------------------------------------------------*/
void Sleep(void);

/* Public function ------ --------------------------------------------------------*/
#ifdef __cplusplus
extern "C"
{
#endif
/**********************************************************************************
  * @brief  vApplicationIdleHook program.
  * @param  None
  * @note
  * @retval None
  *********************************************************************************
*/  
void vApplicationIdleHook(void)
{
	Sleep();
}

#ifdef __cplusplus
}
#endif

/* Private function ------ -------------------------------------------------------*/
/**********************************************************************************
  * @brief  Sleep program.
  * @param  None
  * @note
  * @retval None
  *********************************************************************************
*/  
void Sleep(void)
{
	
}
/************************* (C) COPYRIGHT FMD *****END OF FILE*********************/






