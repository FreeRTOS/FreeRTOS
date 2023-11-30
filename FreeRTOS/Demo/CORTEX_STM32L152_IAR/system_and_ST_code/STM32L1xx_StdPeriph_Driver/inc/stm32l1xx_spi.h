/**
  ******************************************************************************
  * @file    stm32l1xx_spi.h
  * @author  MCD Application Team
  * @version V1.0.0RC1
  * @date    07/02/2010
  * @brief   This file contains all the functions prototypes for the SPI 
  *          firmware library.
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
  * <h2><center>&copy; COPYRIGHT 2010 STMicroelectronics</center></h2>
  */ 

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32L1xx_SPI_H
#define __STM32L1xx_SPI_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32l1xx.h"

/** @addtogroup STM32L1xx_StdPeriph_Driver
  * @{
  */

/** @addtogroup SPI
  * @{
  */ 

/** @defgroup SPI_Exported_Types
  * @{
  */

/** 
  * @brief  SPI Init structure definition  
  */

typedef struct
{
  uint16_t SPI_Direction;           /*!< Specifies the SPI unidirectional or bidirectional data mode.
                                         This parameter can be any combination of @ref SPI_data_direction */

  uint16_t SPI_Mode;                /*!< Specifies the SPI operating mode.
                                         This parameter can be any combination of @ref SPI_mode */

  uint16_t SPI_DataSize;            /*!< Specifies the SPI data size.
                                         This parameter can be any combination of @ref SPI_data_size */

  uint16_t SPI_CPOL;                /*!< Specifies the serial clock steady state.
                                         This parameter can be any combination of @ref SPI_Clock_Polarity */

  uint16_t SPI_CPHA;                /*!< Specifies the clock active edge for the bit capture.
                                         This parameter can be any combination of @ref SPI_Clock_Phase */

  uint16_t SPI_NSS;                 /*!< Specifies whether the NSS signal is managed by
                                         hardware (NSS pin) or by software using the SSI bit.
                                         This parameter can be any combination of @ref SPI_Slave_Select_management */
 
  uint16_t SPI_BaudRatePrescaler;   /*!< Specifies the Baud Rate prescaler value which will be
                                         used to configure the transmit and receive SCK clock.
                                         This parameter can be any combination of @ref SPI_BaudRate_Prescaler.
                                         @note The communication clock is derived from the master
                                               clock. The slave clock does not need to be set. */

  uint16_t SPI_FirstBit;            /*!< Specifies whether data transfers start from MSB or LSB bit.
                                         This parameter can be any combination of @ref SPI_MSB_LSB_transmission */

  uint16_t SPI_CRCPolynomial;       /*!< Specifies the polynomial used for the CRC calculation. */
}SPI_InitTypeDef;

/**
  * @}
  */

/** @defgroup SPI_Exported_Constants
  * @{
  */

#define IS_SPI_ALL_PERIPH(PERIPH) (((PERIPH) == SPI1) || \
                                   ((PERIPH) == SPI2))

/** @defgroup SPI_data_direction 
  * @{
  */
  
#define SPI_Direction_2Lines_FullDuplex ((uint16_t)0x0000)
#define SPI_Direction_2Lines_RxOnly     ((uint16_t)0x0400)
#define SPI_Direction_1Line_Rx          ((uint16_t)0x8000)
#define SPI_Direction_1Line_Tx          ((uint16_t)0xC000)
#define IS_SPI_DIRECTION_MODE(MODE) (((MODE) == SPI_Direction_2Lines_FullDuplex) || \
                                     ((MODE) == SPI_Direction_2Lines_RxOnly) || \
                                     ((MODE) == SPI_Direction_1Line_Rx) || \
                                     ((MODE) == SPI_Direction_1Line_Tx))
/**
  * @}
  */

/** @defgroup SPI_mode 
  * @{
  */

#define SPI_Mode_Master                 ((uint16_t)0x0104)
#define SPI_Mode_Slave                  ((uint16_t)0x0000)
#define IS_SPI_MODE(MODE) (((MODE) == SPI_Mode_Master) || \
                           ((MODE) == SPI_Mode_Slave))
/**
  * @}
  */

/** @defgroup SPI_data_size 
  * @{
  */

#define SPI_DataSize_16b                ((uint16_t)0x0800)
#define SPI_DataSize_8b                 ((uint16_t)0x0000)
#define IS_SPI_DATASIZE(DATASIZE) (((DATASIZE) == SPI_DataSize_16b) || \
                                   ((DATASIZE) == SPI_DataSize_8b))
/**
  * @}
  */ 

/** @defgroup SPI_Clock_Polarity 
  * @{
  */

#define SPI_CPOL_Low                    ((uint16_t)0x0000)
#define SPI_CPOL_High                   ((uint16_t)0x0002)
#define IS_SPI_CPOL(CPOL) (((CPOL) == SPI_CPOL_Low) || \
                           ((CPOL) == SPI_CPOL_High))
/**
  * @}
  */

/** @defgroup SPI_Clock_Phase 
  * @{
  */

#define SPI_CPHA_1Edge                  ((uint16_t)0x0000)
#define SPI_CPHA_2Edge                  ((uint16_t)0x0001)
#define IS_SPI_CPHA(CPHA) (((CPHA) == SPI_CPHA_1Edge) || \
                           ((CPHA) == SPI_CPHA_2Edge))
/**
  * @}
  */

/** @defgroup SPI_Slave_Select_management 
  * @{
  */

#define SPI_NSS_Soft                    ((uint16_t)0x0200)
#define SPI_NSS_Hard                    ((uint16_t)0x0000)
#define IS_SPI_NSS(NSS) (((NSS) == SPI_NSS_Soft) || \
                         ((NSS) == SPI_NSS_Hard))
/**
  * @}
  */ 

/** @defgroup SPI_BaudRate_Prescaler 
  * @{
  */

#define SPI_BaudRatePrescaler_2         ((uint16_t)0x0000)
#define SPI_BaudRatePrescaler_4         ((uint16_t)0x0008)
#define SPI_BaudRatePrescaler_8         ((uint16_t)0x0010)
#define SPI_BaudRatePrescaler_16        ((uint16_t)0x0018)
#define SPI_BaudRatePrescaler_32        ((uint16_t)0x0020)
#define SPI_BaudRatePrescaler_64        ((uint16_t)0x0028)
#define SPI_BaudRatePrescaler_128       ((uint16_t)0x0030)
#define SPI_BaudRatePrescaler_256       ((uint16_t)0x0038)
#define IS_SPI_BAUDRATE_PRESCALER(PRESCALER) (((PRESCALER) == SPI_BaudRatePrescaler_2) || \
                                              ((PRESCALER) == SPI_BaudRatePrescaler_4) || \
                                              ((PRESCALER) == SPI_BaudRatePrescaler_8) || \
                                              ((PRESCALER) == SPI_BaudRatePrescaler_16) || \
                                              ((PRESCALER) == SPI_BaudRatePrescaler_32) || \
                                              ((PRESCALER) == SPI_BaudRatePrescaler_64) || \
                                              ((PRESCALER) == SPI_BaudRatePrescaler_128) || \
                                              ((PRESCALER) == SPI_BaudRatePrescaler_256))
/**
  * @}
  */ 

/** @defgroup SPI_MSB_LSB_transmission 
  * @{
  */

#define SPI_FirstBit_MSB                ((uint16_t)0x0000)
#define SPI_FirstBit_LSB                ((uint16_t)0x0080)
#define IS_SPI_FIRST_BIT(BIT) (((BIT) == SPI_FirstBit_MSB) || \
                               ((BIT) == SPI_FirstBit_LSB))
/**
  * @}
  */

/** @defgroup SPI_DMA_transfer_requests 
  * @{
  */

#define SPI_DMAReq_Tx               ((uint16_t)0x0002)
#define SPI_DMAReq_Rx               ((uint16_t)0x0001)
#define IS_SPI_DMAREQ(DMAREQ) ((((DMAREQ) & (uint16_t)0xFFFC) == 0x00) && ((DMAREQ) != 0x00))
/**
  * @}
  */

/** @defgroup SPI_NSS_internal_software_mangement 
  * @{
  */

#define SPI_NSSInternalSoft_Set         ((uint16_t)0x0100)
#define SPI_NSSInternalSoft_Reset       ((uint16_t)0xFEFF)
#define IS_SPI_NSS_INTERNAL(INTERNAL) (((INTERNAL) == SPI_NSSInternalSoft_Set) || \
                                       ((INTERNAL) == SPI_NSSInternalSoft_Reset))
/**
  * @}
  */

/** @defgroup SPI_CRC_Transmit_Receive 
  * @{
  */

#define SPI_CRC_Tx                      ((uint8_t)0x00)
#define SPI_CRC_Rx                      ((uint8_t)0x01)
#define IS_SPI_CRC(CRC) (((CRC) == SPI_CRC_Tx) || ((CRC) == SPI_CRC_Rx))
/**
  * @}
  */

/** @defgroup SPI_direction_transmit_receive 
  * @{
  */

#define SPI_Direction_Rx                ((uint16_t)0xBFFF)
#define SPI_Direction_Tx                ((uint16_t)0x4000)
#define IS_SPI_DIRECTION(DIRECTION) (((DIRECTION) == SPI_Direction_Rx) || \
                                     ((DIRECTION) == SPI_Direction_Tx))
/**
  * @}
  */

/** @defgroup SPI_interrupts_definition 
  * @{
  */

#define SPI_IT_TXE                  ((uint8_t)0x71)
#define SPI_IT_RXNE                 ((uint8_t)0x60)
#define SPI_IT_ERR                  ((uint8_t)0x50)
#define IS_SPI_CONFIG_IT(IT) (((IT) == SPI_IT_TXE) || \
                                 ((IT) == SPI_IT_RXNE) || \
                                 ((IT) == SPI_IT_ERR))
#define SPI_IT_OVR                  ((uint8_t)0x56)
#define SPI_IT_MODF                     ((uint8_t)0x55)
#define SPI_IT_CRCERR                   ((uint8_t)0x54)
#define IS_SPI_CLEAR_IT(IT) (((IT) == SPI_IT_CRCERR))
#define IS_SPI_GET_IT(IT) (((IT) == SPI_IT_RXNE) || ((IT) == SPI_IT_TXE) || \
                               ((IT) == SPI_IT_CRCERR) || \
                               ((IT) == SPI_IT_MODF) || ((IT) == SPI_IT_OVR))
/**
  * @}
  */

/** @defgroup SPI_flags_definition 
  * @{
  */

#define SPI_FLAG_RXNE               ((uint16_t)0x0001)
#define SPI_FLAG_TXE                ((uint16_t)0x0002)
#define SPI_FLAG_CRCERR                 ((uint16_t)0x0010)
#define SPI_FLAG_MODF                   ((uint16_t)0x0020)
#define SPI_FLAG_OVR                ((uint16_t)0x0040)
#define SPI_FLAG_BSY                ((uint16_t)0x0080)
#define IS_SPI_CLEAR_FLAG(FLAG) (((FLAG) == SPI_FLAG_CRCERR))
#define IS_SPI_GET_FLAG(FLAG) (((FLAG) == SPI_FLAG_BSY) || ((FLAG) == SPI_FLAG_OVR) || \
                                   ((FLAG) == SPI_FLAG_MODF) || ((FLAG) == SPI_FLAG_CRCERR) || \
                                   ((FLAG) == SPI_FLAG_TXE) || ((FLAG) == SPI_FLAG_RXNE))
/**
  * @}
  */

/** @defgroup SPI_CRC_polynomial 
  * @{
  */

#define IS_SPI_CRC_POLYNOMIAL(POLYNOMIAL) ((POLYNOMIAL) >= 0x1)
/**
  * @}
  */

/** @defgroup SPI_Legacy 
  * @{
  */

#define SPI_I2S_DMAReq_Tx            SPI_DMAReq_Tx
#define SPI_I2S_DMAReq_Rx            SPI_DMAReq_Rx
#define SPI_I2S_IT_TXE               SPI_IT_TXE
#define SPI_I2S_IT_RXNE              SPI_IT_RXNE
#define SPI_I2S_IT_ERR               SPI_IT_ERR
#define SPI_I2S_IT_OVR               SPI_IT_OVR
#define SPI_I2S_FLAG_RXNE            SPI_FLAG_RXNE
#define SPI_I2S_FLAG_TXE             SPI_FLAG_TXE
#define SPI_I2S_FLAG_OVR             SPI_FLAG_OVR
#define SPI_I2S_FLAG_BSY             SPI_FLAG_BSY
#define SPI_I2S_DeInit               SPI_DeInit
#define SPI_I2S_ITConfig             SPI_ITConfig
#define SPI_I2S_DMACmd               SPI_DMACmd
#define SPI_I2S_SendData             SPI_SendData
#define SPI_I2S_ReceiveData          SPI_ReceiveData
#define SPI_I2S_GetFlagStatus        SPI_GetFlagStatus
#define SPI_I2S_ClearFlag            SPI_ClearFlag
#define SPI_I2S_GetITStatus          SPI_GetITStatus
#define SPI_I2S_ClearITPendingBit    SPI_ClearITPendingBit
/**
  * @}
  */
  
/**
  * @}
  */

/** @defgroup SPI_Exported_Macros
  * @{
  */

/**
  * @}
  */

/** @defgroup SPI_Exported_Functions
  * @{
  */

void SPI_DeInit(SPI_TypeDef* SPIx);
void SPI_Init(SPI_TypeDef* SPIx, SPI_InitTypeDef* SPI_InitStruct);
void SPI_StructInit(SPI_InitTypeDef* SPI_InitStruct);
void SPI_Cmd(SPI_TypeDef* SPIx, FunctionalState NewState);
void SPI_ITConfig(SPI_TypeDef* SPIx, uint8_t SPI_IT, FunctionalState NewState);
void SPI_DMACmd(SPI_TypeDef* SPIx, uint16_t SPI_DMAReq, FunctionalState NewState);
void SPI_SendData(SPI_TypeDef* SPIx, uint16_t Data);
uint16_t SPI_ReceiveData(SPI_TypeDef* SPIx);
void SPI_NSSInternalSoftwareConfig(SPI_TypeDef* SPIx, uint16_t SPI_NSSInternalSoft);
void SPI_SSOutputCmd(SPI_TypeDef* SPIx, FunctionalState NewState);
void SPI_DataSizeConfig(SPI_TypeDef* SPIx, uint16_t SPI_DataSize);
void SPI_TransmitCRC(SPI_TypeDef* SPIx);
void SPI_CalculateCRC(SPI_TypeDef* SPIx, FunctionalState NewState);
uint16_t SPI_GetCRC(SPI_TypeDef* SPIx, uint8_t SPI_CRC);
uint16_t SPI_GetCRCPolynomial(SPI_TypeDef* SPIx);
void SPI_BiDirectionalLineConfig(SPI_TypeDef* SPIx, uint16_t SPI_Direction);
FlagStatus SPI_GetFlagStatus(SPI_TypeDef* SPIx, uint16_t SPI_FLAG);
void SPI_ClearFlag(SPI_TypeDef* SPIx, uint16_t SPI_FLAG);
ITStatus SPI_GetITStatus(SPI_TypeDef* SPIx, uint8_t SPI_IT);
void SPI_ClearITPendingBit(SPI_TypeDef* SPIx, uint8_t SPI_IT);

#ifdef __cplusplus
}
#endif

#endif /*__STM32l15x_SPI_H */
/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */

/******************* (C) COPYRIGHT 2010 STMicroelectronics *****END OF FILE****/
