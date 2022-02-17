/**
  ******************************************************************************
  * @file    	    HighProTask.h
  * @author  	    FMD AE
  * @brief   		HighProTask Header File.             	
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


#ifndef __HIGHPROTASK_H__
#define __HIGHPROTASK_H__
/* Includes ---------------------------------------------------------------------*/
#include "config.h"
#include "TaskManager.h"
#include "LowProTask.h"
/* Public Constant prototypes----------------------------------------------------*/
/* Public typedef ---------------------------------------------------------------*/
/* Public define ----------------------------------------------------------------*/
/* Public variables prototypes --------------------------------------------------*/
extern xQueueHandle xHighProTaskQueue;

/* Public function prototypes----------------------------------------------------*/
void CreateHighProTask(void);

#endif
/************************* (C) COPYRIGHT FMD *****END OF FILE*********************/
