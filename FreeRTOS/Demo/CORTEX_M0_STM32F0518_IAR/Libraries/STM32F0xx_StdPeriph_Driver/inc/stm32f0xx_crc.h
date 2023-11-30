/**
  ******************************************************************************
  * @file    stm32f0xx_crc.h
  * @author  MCD Application Team
  * @version V1.0.0RC1
  * @date    27-January-2012
  * @brief   This file contains all the functions prototypes for the CRC firmware 
  *          library.
  ******************************************************************************
  * @attention
  *
  * THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
  * WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE
  * TIME. AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY
  * DIRECT, INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING
  * FROM THE CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE
  * CODING INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
  *
  * FOR MORE INFORMATION PLEASE READ CAREFULLY THE LICENSE AGREEMENT FILE
  * LOCATED IN THE ROOT DIRECTORY OF THIS FIRMWARE PACKAGE.
  *
  * <h2><center>&copy; COPYRIGHT 2012 STMicroelectronics</center></h2>
  ******************************************************************************
  */

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32F0XX_CRC_H
#define __STM32F0XX_CRC_H

#ifdef __cplusplus
 extern "C" {
#endif

/*!< Includes ----------------------------------------------------------------*/
#include "stm32f0xx.h"

/** @addtogroup STM32F0xx_StdPeriph_Driver
  * @{
  */

/** @addtogroup CRC
  * @{
  */

/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/

/** @defgroup CRC_Exported_Constants
  * @{
  */
#define CRC_ReverseInputData_No             ((uint32_t)0x00000000) /*!< No reverse operation of Input Data */
#define CRC_ReverseInputData_8bits          CRC_CR_REV_IN_0        /*!< Reverse operation of Input Data on 8 bits */
#define CRC_ReverseInputData_16bits         CRC_CR_REV_IN_1        /*!< Reverse operation of Input Data on 16 bits */
#define CRC_ReverseInputData_32bits         CRC_CR_REV_IN          /*!< Reverse operation of Input Data on 32 bits */

#define IS_CRC_REVERSE_INPUT_DATA(DATA) (((DATA) == CRC_ReverseInputData_No)     || \
                                         ((DATA) == CRC_ReverseInputData_8bits)  || \
                                         ((DATA) == CRC_ReverseInputData_16bits) || \
                                         ((DATA) == CRC_ReverseInputData_32bits))

/**
  * @}
  */

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
/* Configuration of the CRC computation unit **********************************/
void CRC_DeInit(void);
void CRC_ResetDR(void);
void CRC_ReverseInputDataSelect(uint32_t CRC_ReverseInputData);
void CRC_ReverseOutputDataCmd(FunctionalState NewState);
void CRC_SetInitRegister(uint32_t CRC_InitValue);

/* CRC computation ************************************************************/
uint32_t CRC_CalcCRC(uint32_t CRC_Data);
uint32_t CRC_CalcBlockCRC(uint32_t pBuffer[], uint32_t BufferLength);
uint32_t CRC_GetCRC(void);

/* Independent register (IDR) access (write/read) *****************************/
void CRC_SetIDRegister(uint8_t CRC_IDValue);
uint8_t CRC_GetIDRegister(void);

#ifdef __cplusplus
}
#endif

#endif /* __STM32F0XX_CRC_H */

/**
  * @}
  */

/**
  * @}
  */

/******************* (C) COPYRIGHT 2012 STMicroelectronics *****END OF FILE****/
