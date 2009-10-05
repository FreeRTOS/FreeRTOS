/******************** (C) COPYRIGHT 2008 STMicroelectronics ********************
* File Name          : stm32f_eth_conf.h
* Author             : MCD Application Team
* Version            : VX.Y.Z
* Date               : mm/dd/2008
* Description        : ETHERNET firmware library configuration file.
********************************************************************************
* THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32F_ETH_CONF_H
#define __STM32F_ETH_CONF_H

/* Includes ------------------------------------------------------------------*/
#include "stm32f10x_type.h"
/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/
/* Uncomment the line below to compile the ETHERNET firmware library in DEBUG mode,
   this will expanse the "assert_param" macro in the firmware library code (see 
   "Exported macro" section below) */
/*#define ETH_DEBUG    1*/

/* Comment the line below to disable the specific peripheral inclusion */
/************************************* ETHERNET *******************************/
#define _ETH_MAC
//#define _ETH_PTP
//#define _ETH_MMC
#define _ETH_DMA

/* Exported macro ------------------------------------------------------------*/
#ifdef  ETH_DEBUG
/*******************************************************************************
* Macro Name     : eth_assert_param
* Description    : The eth_assert_param macro is used for ethernet function's parameters
*                  check.
*                  It is used only if the ethernet library is compiled in DEBUG mode. 
* Input          : - expr: If expr is false, it calls assert_failed function
*                    which reports the name of the source file and the source
*                    line number of the call that failed. 
*                    If expr is true, it returns no value.
* Return         : None
*******************************************************************************/ 
  #define eth_assert_param(expr) ((expr) ? (void)0 : assert_failed((u8 *)__FILE__, __LINE__))
/* Exported functions ------------------------------------------------------- */
  void assert_failed(u8* file, u32 line);
#else
  #define eth_assert_param(expr) ((void)0)
#endif /* ETH_DEBUG */

#endif /* __STM32F_ETH_CONF_H */

/******************* (C) COPYRIGHT 2008 STMicroelectronics *****END OF FILE****/
