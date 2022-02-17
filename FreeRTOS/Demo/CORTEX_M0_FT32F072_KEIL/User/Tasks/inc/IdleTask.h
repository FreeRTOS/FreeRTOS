/**
  ******************************************************************************
  * @file    	    IdleTask.h
  * @author  	    FMD AE
  * @brief   		IdleTask Header File.             	
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

#ifndef __IDLETASK_H__
#define __IDLETASK_H__
/* Includes ---------------------------------------------------------------------*/
#include "config.h"
/* Public Constant prototypes----------------------------------------------------*/
/* Public typedef ---------------------------------------------------------------*/
/* Public define ----------------------------------------------------------------*/
/* Public variables prototypes --------------------------------------------------*/
/* Public function prototypes----------------------------------------------------*/
#ifdef __cplusplus
extern "C"
{
#endif
  
void vApplicationIdleHook(void);

#ifdef __cplusplus
}
#endif

#endif
/************************* (C) COPYRIGHT FMD *****END OF FILE*********************/
