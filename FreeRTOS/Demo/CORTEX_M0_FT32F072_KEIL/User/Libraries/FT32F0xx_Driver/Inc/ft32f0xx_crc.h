/**
  ******************************************************************************
  * @file    			ft32f0xx_crc.h
  * @author  			FMD AE
  * @brief   			This file contains all the functions prototypes for the CRC firmware 
  *          			library.	
  * @version 			V1.0.0           
  * @data		 			2021-07-01
  ******************************************************************************
  */

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __FT32F0XX_CRC_H
#define __FT32F0XX_CRC_H

#ifdef __cplusplus
 extern "C" {
#endif

/*!< Includes ----------------------------------------------------------------*/
#include "ft32f0xx.h"


/** @addtogroup CRC
  * @{
  */

/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/

/** @defgroup CRC_ReverseInputData
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

/** @defgroup CRC_PolynomialSize
  * @brief    Only applicable for FT32F042 and FT32F072 devices 
  * @{
  */
#define CRC_PolSize_7                       CRC_CR_POLSIZE        /*!< 7-bit polynomial for CRC calculation */
#define CRC_PolSize_8                       CRC_CR_POLSIZE_1      /*!< 8-bit polynomial for CRC calculation */
#define CRC_PolSize_16                      CRC_CR_POLSIZE_0      /*!< 16-bit polynomial for CRC calculation */
#define CRC_PolSize_32                      ((uint32_t)0x00000000)/*!< 32-bit polynomial for CRC calculation */

#define IS_CRC_POL_SIZE(SIZE) (((SIZE) == CRC_PolSize_7)  || \
                               ((SIZE) == CRC_PolSize_8)  || \
                               ((SIZE) == CRC_PolSize_16) || \
                               ((SIZE) == CRC_PolSize_32))
                               

/**
  * @}
  */

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
/* Configuration of the CRC computation unit **********************************/
void CRC_DeInit(void);
void CRC_ResetDR(void);
//void CRC_PolynomialSizeSelect(uint32_t CRC_PolSize); /*!< Only applicable for FT32F042 and FT32F072 devices */ 
void CRC_ReverseInputDataSelect(uint32_t CRC_ReverseInputData);
void CRC_ReverseOutputDataCmd(FunctionalState NewState);
void CRC_SetInitRegister(uint32_t CRC_InitValue); 
void CRC_SetPolynomial(uint32_t CRC_Pol);

/* CRC computation ************************************************************/
uint32_t CRC_CalcCRC(uint32_t CRC_Data);
uint32_t CRC_CalcCRC16bits(uint16_t CRC_Data); 
uint32_t CRC_CalcCRC8bits(uint8_t CRC_Data);
uint32_t CRC_CalcBlockCRC(uint32_t pBuffer[], uint32_t BufferLength);
uint32_t CRC_GetCRC(void);

/* Independent register (IDR) access (write/read) *****************************/
void CRC_SetIDRegister(uint8_t CRC_IDValue);
uint8_t CRC_GetIDRegister(void);

#ifdef __cplusplus
}
#endif

#endif /* __FT32F0XX_CRC_H */

/**
  * @}
  */

/**
  * @}
  */

/************************ (C) COPYRIGHT FMD *****END OF FILE****/
