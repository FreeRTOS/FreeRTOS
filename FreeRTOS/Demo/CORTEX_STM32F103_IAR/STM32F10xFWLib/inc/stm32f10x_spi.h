/******************** (C) COPYRIGHT 2007 STMicroelectronics ********************
* File Name          : stm32f10x_spi.h
* Author             : MCD Application Team
* Date First Issued  : 09/29/2006
* Description        : This file contains all the functions prototypes for the
*                      SPI firmware library.
********************************************************************************
* History:
* 04/02/2007: V0.2
* 02/05/2007: V0.1
* 09/29/2006: V0.01
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
* WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
* AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT,
* INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE
* CONTENT OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING
* INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32F10x_SPI_H
#define __STM32F10x_SPI_H

/* Includes ------------------------------------------------------------------*/
#include "stm32f10x_map.h"

/* Exported types ------------------------------------------------------------*/
/* SPI Init structure definition */
typedef struct
{
  u16 SPI_Direction;
  u16 SPI_Mode;
  u16 SPI_DataSize;
  u16 SPI_CPOL;
  u16 SPI_CPHA;
  u16 SPI_NSS;
  u16 SPI_BaudRatePrescaler;
  u16 SPI_FirstBit;
  u16 SPI_CRCPolynomial;
}SPI_InitTypeDef;

/* Exported constants --------------------------------------------------------*/
/* SPI data direction mode */
#define SPI_Direction_2Lines_FullDuplex    ((u16)0x0000)
#define SPI_Direction_2Lines_RxOnly        ((u16)0x0400)
#define SPI_Direction_1Line_Rx             ((u16)0x8000)
#define SPI_Direction_1Line_Tx             ((u16)0xC000)

#define IS_SPI_DIRECTION_MODE(MODE) ((MODE == SPI_Direction_2Lines_FullDuplex) || \
                                     (MODE == SPI_Direction_2Lines_RxOnly) || \
                                     (MODE == SPI_Direction_1Line_Rx) || \
						             (MODE == SPI_Direction_1Line_Tx))

/* SPI master/slave mode */
#define SPI_Mode_Master                    ((u16)0x0104)
#define SPI_Mode_Slave                     ((u16)0x0000)

#define IS_SPI_MODE(MODE) ((MODE == SPI_Mode_Master) || \
                           (MODE == SPI_Mode_Slave))

/* SPI data size */
#define SPI_DataSize_16b                   ((u16)0x0800)
#define SPI_DataSize_8b                    ((u16)0x0000)

#define IS_SPI_DATASIZE(DATASIZE) ((DATASIZE == SPI_DataSize_16b) || \
                                   (DATASIZE == SPI_DataSize_8b))

/* SPI Clock Polarity */
#define SPI_CPOL_Low                       ((u16)0x0000)
#define SPI_CPOL_High                      ((u16)0x0002)

#define IS_SPI_CPOL(CPOL) ((CPOL == SPI_CPOL_Low) || \
                           (CPOL == SPI_CPOL_High))

/* SPI Clock Phase */
#define SPI_CPHA_1Edge                     ((u16)0x0000)
#define SPI_CPHA_2Edge                     ((u16)0x0001)

#define IS_SPI_CPHA(CPHA) ((CPHA == SPI_CPHA_1Edge) || \
                           (CPHA == SPI_CPHA_2Edge))

/* SPI Slave Select management */
#define SPI_NSS_Soft                       ((u16)0x0200)
#define SPI_NSS_Hard                       ((u16)0x0000)

#define IS_SPI_NSS(NSS) ((NSS == SPI_NSS_Soft) || \
                         (NSS == SPI_NSS_Hard))

/* SPI BaudRate Prescaler  */
#define SPI_BaudRatePrescaler_2            ((u16)0x0000)
#define SPI_BaudRatePrescaler_4            ((u16)0x0008)
#define SPI_BaudRatePrescaler_8            ((u16)0x0010)
#define SPI_BaudRatePrescaler_16           ((u16)0x0018)
#define SPI_BaudRatePrescaler_32           ((u16)0x0020)
#define SPI_BaudRatePrescaler_64           ((u16)0x0028)
#define SPI_BaudRatePrescaler_128          ((u16)0x0030)
#define SPI_BaudRatePrescaler_256          ((u16)0x0038)

#define IS_SPI_BAUDRATE_PRESCALER(PRESCALER) ((PRESCALER == SPI_BaudRatePrescaler_2) || \
                                              (PRESCALER == SPI_BaudRatePrescaler_4) || \
                                              (PRESCALER == SPI_BaudRatePrescaler_8) || \
                                              (PRESCALER == SPI_BaudRatePrescaler_16) || \
                                              (PRESCALER == SPI_BaudRatePrescaler_32) || \
                                              (PRESCALER == SPI_BaudRatePrescaler_64) || \
                                              (PRESCALER == SPI_BaudRatePrescaler_128) || \
                                              (PRESCALER == SPI_BaudRatePrescaler_256))

/* SPI MSB/LSB transmission */
#define SPI_FirstBit_MSB                   ((u16)0x0000)
#define SPI_FirstBit_LSB                   ((u16)0x0080)

#define IS_SPI_FIRST_BIT(BIT) ((BIT == SPI_FirstBit_MSB) || \
                               (BIT == SPI_FirstBit_LSB))

/* SPI DMA transfer requests */
#define SPI_DMAReq_Tx                      ((u16)0x0002)
#define SPI_DMAReq_Rx                      ((u16)0x0001)

#define IS_SPI_DMA_REQ(REQ) (((REQ & (u16)0xFFFC) == 0x00) && (REQ != 0x00))

/* SPI NSS internal software mangement */
#define SPI_NSSInternalSoft_Set            ((u16)0x0100)
#define SPI_NSSInternalSoft_Reset          ((u16)0xFEFF)

#define IS_SPI_NSS_INTERNAL(INTERNAL) ((INTERNAL == SPI_NSSInternalSoft_Set) || \
                                       (INTERNAL == SPI_NSSInternalSoft_Reset))

/* SPI CRC Transmit/Receive */
#define SPI_CRC_Tx                         ((u8)0x00)
#define SPI_CRC_Rx                         ((u8)0x01)

#define IS_SPI_CRC(CRC) ((CRC == SPI_CRC_Tx) || (CRC == SPI_CRC_Rx))

/* SPI direction transmit/receive */
#define SPI_Direction_Rx                   ((u16)0xBFFF)
#define SPI_Direction_Tx                   ((u16)0x4000)

#define IS_SPI_DIRECTION(DIRECTION) ((DIRECTION == SPI_Direction_Rx) || \
                                     (DIRECTION == SPI_Direction_Tx))

/* SPI interrupts definition */
#define SPI_IT_TXE                         ((u8)0x71)
#define SPI_IT_RXNE                        ((u8)0x60)
#define SPI_IT_ERR                         ((u8)0x50)

#define IS_SPI_CONFIG_IT(IT) ((IT == SPI_IT_TXE) || (IT == SPI_IT_RXNE) || \
                              (IT == SPI_IT_ERR))

#define SPI_IT_OVR                         ((u8)0x56)
#define SPI_IT_MODF                        ((u8)0x55)
#define SPI_IT_CRCERR                      ((u8)0x54)

#define IS_SPI_CLEAR_IT(IT) ((IT == SPI_IT_OVR) || (IT == SPI_IT_MODF) || \
                             (IT == SPI_IT_CRCERR))

#define IS_SPI_GET_IT(IT) ((IT == SPI_IT_TXE) || (IT == SPI_IT_RXNE) || \
                           (IT == SPI_IT_OVR) || (IT == SPI_IT_MODF) || \
                           (IT == SPI_IT_CRCERR))

/* SPI flags definition */
#define SPI_FLAG_RXNE                      ((u16)0x0001)
#define SPI_FLAG_TXE                       ((u16)0x0002)
#define SPI_FLAG_CRCERR                    ((u16)0x0010)
#define SPI_FLAG_MODF                      ((u16)0x0020)
#define SPI_FLAG_OVR                       ((u16)0x0040)
#define SPI_FLAG_BSY                       ((u16)0x0080)

#define IS_SPI_CLEAR_FLAG(FLAG) (((FLAG & (u16)0xFF8F) == 0x00) && (FLAG != 0x00))
#define IS_SPI_GET_FLAG(FLAG) ((FLAG == SPI_FLAG_BSY) || (FLAG == SPI_FLAG_OVR) || \
                               (FLAG == SPI_FLAG_MODF) || (FLAG == SPI_FLAG_CRCERR) || \
                               (FLAG == SPI_FLAG_TXE) || (FLAG == SPI_FLAG_RXNE))

/* SPI CRC polynomial --------------------------------------------------------*/
#define IS_SPI_CRC_POLYNOMIAL(POLYNOMIAL) (POLYNOMIAL >= 0x1)

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
void SPI_DeInit(SPI_TypeDef* SPIx);
void SPI_Init(SPI_TypeDef* SPIx, SPI_InitTypeDef* SPI_InitStruct);
void SPI_StructInit(SPI_InitTypeDef* SPI_InitStruct);
void SPI_Cmd(SPI_TypeDef* SPIx, FunctionalState NewState);
void SPI_ITConfig(SPI_TypeDef* SPIx, u8 SPI_IT, FunctionalState NewState);
void SPI_DMACmd(SPI_TypeDef* SPIx, u16 SPI_DMAReq, FunctionalState NewState);
void SPI_SendData(SPI_TypeDef* SPIx, u16 Data);
u16 SPI_ReceiveData(SPI_TypeDef* SPIx);
void SPI_NSSInternalSoftwareConfig(SPI_TypeDef* SPIx, u16 SPI_NSSInternalSoft);
void SPI_SSOutputCmd(SPI_TypeDef* SPIx, FunctionalState NewState);
void SPI_DataSizeConfig(SPI_TypeDef* SPIx, u16 SPI_DataSize);
void SPI_TransmitCRC(SPI_TypeDef* SPIx);
void SPI_CalculateCRC(SPI_TypeDef* SPIx, FunctionalState NewState);
u16 SPI_GetCRC(SPI_TypeDef* SPIx, u8 SPI_CRC);
u16 SPI_GetCRCPolynomial(SPI_TypeDef* SPIx);
void SPI_BiDirectionalLineConfig(SPI_TypeDef* SPIx, u16 SPI_Direction);
FlagStatus SPI_GetFlagStatus(SPI_TypeDef* SPIx, u16 SPI_FLAG);
void SPI_ClearFlag(SPI_TypeDef* SPIx, u16 SPI_FLAG);
ITStatus SPI_GetITStatus(SPI_TypeDef* SPIx, u8 SPI_IT);
void SPI_ClearITPendingBit(SPI_TypeDef* SPIx, u8 SPI_IT);

#endif /*__STM32F10x_SPI_H */

/******************* (C) COPYRIGHT 2007 STMicroelectronics *****END OF FILE****/
