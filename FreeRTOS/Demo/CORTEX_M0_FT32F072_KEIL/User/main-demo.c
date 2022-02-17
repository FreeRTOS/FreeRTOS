/**
  *********************************************************************************
  * @file    	    main_demo.c
  * @author  	    FMD AE
  * @brief   		main program body 	
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
/* Private Constant --------------------------------------------------------------*/
/* Public Constant ---------------------------------------------------------------*/
/* Private typedef ---------------------------------------------------------------*/
/* Private variables -------------------------------------------------------------*/
/* Public variables --------------------------------------------------------------*/
/* Private function prototypes ---------------------------------------------------*/
/* Public function ------ --------------------------------------------------------*/
/* Private function ------ -------------------------------------------------------*/
int main_demo(void);
/**********************************************************************************
  * @brief  main program
  * @param  
  * @note  
  * @retval 
  *********************************************************************************
*/
int main_demo(void)
{      
 	CreateInitTask();	
	vTaskStartScheduler();            // System scheduling
	return (0);       
}

/************************ (C) COPYRIGHT FMD *****END OF FILE***********************/




