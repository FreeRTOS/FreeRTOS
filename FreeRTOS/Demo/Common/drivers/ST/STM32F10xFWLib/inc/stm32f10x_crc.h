/**
  ******************************************************************************
  * @file  stm32f10x_crc.h
  * @author  MCD Application Team
  * @version  V3.0.0
  * @date  04/06/2009
  * @brief  This file contains all the functions prototypes for the CRC firmware 
  *         library.
  ******************************************************************************
  * @copy
  *
  * THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
  * WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE
  * TIME. AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY
  * DIRECT, INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING
  * FROM THE CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE
  * CODING INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
  *
  * <h2><center>&copy; COPYRIGHT 2009 STMicroelectronics</center></h2>
  */ 

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32F10x_CRC_H
#define __STM32F10x_CRC_H

/* Includes ------------------------------------------------------------------*/
#include "stm32f10x.h"

/** @addtogroup StdPeriph_Driver
  * @{
  */

/** @addtogroup CRC
  * @{
  */

/** @defgroup CRC_Exported_Types
  * @{
  */

/**
  * @}
  */

/** @defgroup CRC_Exported_Constants
  * @{
  */

/**
  * @}
  */

/** @defgroup CRC_Exported_Macros
  * @{
  */

/**
  * @}
  */

/** @defgroup CRC_Exported_Functions
  * @{
  */

void CRC_ResetDR(void);
uint32_t CRC_CalcCRC(uint32_t Data);
uint32_t CRC_CalcBlockCRC(uint32_t pBuffer[], uint32_t BufferLength);
uint32_t CRC_GetCRC(void);
void CRC_SetIDRegister(uint8_t IDValue);
uint8_t CRC_GetIDRegister(void);

#endif /* __STM32F10x_CRC_H */
/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */

/******************* (C) COPYRIGHT 2009 STMicroelectronics *****END OF FILE****/
