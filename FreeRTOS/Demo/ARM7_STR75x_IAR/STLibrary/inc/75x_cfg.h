/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 75x_cfg.h
* Author             : MCD Application Team
* Date First Issued  : 03/10/2006
* Description        : This file contains all the functions prototypes for the
*                      CFG software library.
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

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __75x_CFG_H
#define __75x_CFG_H

/* Includes ------------------------------------------------------------------*/
#include "75x_map.h"

/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/
#define CFG_BootSpace_FLASH     0x00000000
#define CFG_BootSpace_SRAM      0x00000002
#define CFG_BootSpace_ExtSMI    0x00000003

#define CFG_FLASHBurst_Disable    0xFFFFFEFF
#define CFG_FLASHBurst_Enable     0x00000100

#define CFG_USBFilter_Disable    0xFFFFFDFF
#define CFG_USBFilter_Enable     0x00000200

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
void CFG_BootSpaceConfig(u32 CFG_BootSpace);
void CFG_FLASHBurstConfig(u32 CFG_FLASHBurst);
void CFG_USBFilterConfig(u32 CFG_USBFilter);
FlagStatus CFG_GetFlagStatus(void);

#endif /* __75x_CFG_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/
