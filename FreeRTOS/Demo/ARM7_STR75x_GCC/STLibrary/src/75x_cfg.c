/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_cfg.c
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file provides all the CFG software functions.
********************************************************************************
* History:
* 07/17/2006 : V1.0
* 03/10/2006 : V0.1
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Includes ------------------------------------------------------------------*/
#include "75x_cfg.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
#define CFG_SWBOOT_Mask	      0xFFFFFFFC
#define CFG_FLASHBusy_Mask    0x00000080

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : CFG_BootSpaceConfig
* Description    : Selects which memory space will be remapped at address 0x00.
* Input          : - CFG_BootSpace: specifies the memory space to be remapped
*                    at address 0x00.
*                    This parameter can be one of the following values:
*                          - CFG_BootSpace_FLASH
*                          - CFG_BootSpace_SRAM
*                          - CFG_BootSpace_ExtSMI
* Output         : None
* Return         : None
*******************************************************************************/
void CFG_BootSpaceConfig(u32 CFG_BootSpace)
{
  u32 Temp = 0;
  
  /* Clear SW_BOOT[1:0] bits */ 
  Temp = CFG->GLCONF & CFG_SWBOOT_Mask;
  
  /* Set SW_BOOT[1:0] bits according to CFG_BootSpace parameter value */ 
  Temp |= CFG_BootSpace;
  
  /* Store the new value */ 
  CFG->GLCONF = Temp;   
}

/*******************************************************************************
* Function Name  : CFG_FLASHBurstConfig
* Description    : Enables or disables the FLASH Burst mode.
* Input          : - CCFG_FLASHBurst: specifies the new state of the FLASH Burst
*                    mode.
*                    This parameter can be one of the following values:
*                          - CFG_FLASHBurst_Disable
*                          - CFG_FLASHBurst_Enable
* Output         : None
* Return         : None
*******************************************************************************/
void CFG_FLASHBurstConfig(u32 CFG_FLASHBurst)
{
  if(CFG_FLASHBurst == CFG_FLASHBurst_Enable)
  {
    CFG->GLCONF |= CFG_FLASHBurst_Enable;
  }
  else
  {
    CFG->GLCONF &= CFG_FLASHBurst_Disable;
  }
}

/*******************************************************************************
* Function Name  : CFG_USBFilterConfig
* Description    : Enables or disables the USB Filter.
* Input          : - CFG_USBFilter: specifies the new state of the USB Filter.
*                    This parameter can be one of the following values:
*                          - CFG_USBFilter_Disable
*                          - CFG_USBFilter_Enable
* Output         : None
* Return         : None
*******************************************************************************/
void CFG_USBFilterConfig(u32 CFG_USBFilter)
{
  if(CFG_USBFilter == CFG_USBFilter_Enable)
  {
    CFG->GLCONF |= CFG_USBFilter_Enable;
  }
  else
  {
    CFG->GLCONF &= CFG_USBFilter_Disable;
  }
}

/*******************************************************************************
* Function Name  : CFG_GetFlagStatus
* Description    : Checks whether the FLASH Busy flag is set or not.
* Input          : None
* Output         : None
* Return         : The new state of FLASH Busy flag (SET or RESET).
*******************************************************************************/
FlagStatus CFG_GetFlagStatus(void)
{
  if((CFG->GLCONF & CFG_FLASHBusy_Mask) != RESET)
  {
    return SET;
  }
  else
  {
    return RESET;
  }
}

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
