 /**
  ******************************************************************************
  * @file    stm32f7xx_hal_spi.h
  * @author  MCD Application Team
  * @version V1.0.0
  * @date    12-May-2015
  * @brief   Header file of SPI HAL module.
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; COPYRIGHT(c) 2015 STMicroelectronics</center></h2>
  *
  * Redistribution and use in source and binary forms, with or without modification,
  * are permitted provided that the following conditions are met:
  *   1. Redistributions of source code must retain the above copyright notice,
  *      this list of conditions and the following disclaimer.
  *   2. Redistributions in binary form must reproduce the above copyright notice,
  *      this list of conditions and the following disclaimer in the documentation
  *      and/or other materials provided with the distribution.
  *   3. Neither the name of STMicroelectronics nor the names of its contributors
  *      may be used to endorse or promote products derived from this software
  *      without specific prior written permission.
  *
  * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
  * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
  * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
  * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
  * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
  * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
  * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
  * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
  * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
  * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
  *
  ******************************************************************************  
  */

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32F7xx_HAL_SPI_H
#define __STM32F7xx_HAL_SPI_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32f7xx_hal_def.h"

/** @addtogroup STM32F7xx_HAL_Driver
  * @{
  */

/** @addtogroup SPI
  * @{
  */

/* Exported types ------------------------------------------------------------*/
/** @defgroup SPI_Exported_Types SPI Exported Types
  * @{
  */

/**
  * @brief  SPI Configuration Structure definition
  */
typedef struct
{
  uint32_t Mode;                /*!< Specifies the SPI operating mode.
                                     This parameter can be a value of @ref SPI_Mode */

  uint32_t Direction;           /*!< Specifies the SPI bidirectional mode state.
                                     This parameter can be a value of @ref SPI_Direction */

  uint32_t DataSize;            /*!< Specifies the SPI data size.
                                     This parameter can be a value of @ref SPI_Data_Size */

  uint32_t CLKPolarity;         /*!< Specifies the serial clock steady state.
                                     This parameter can be a value of @ref SPI_Clock_Polarity */

  uint32_t CLKPhase;            /*!< Specifies the clock active edge for the bit capture.
                                     This parameter can be a value of @ref SPI_Clock_Phase */

  uint32_t NSS;                 /*!< Specifies whether the NSS signal is managed by
                                     hardware (NSS pin) or by software using the SSI bit.
                                     This parameter can be a value of @ref SPI_Slave_Select_management */

  uint32_t BaudRatePrescaler;   /*!< Specifies the Baud Rate prescaler value which will be
                                     used to configure the transmit and receive SCK clock.
                                     This parameter can be a value of @ref SPI_BaudRate_Prescaler
                                     @note The communication clock is derived from the master
                                     clock. The slave clock does not need to be set. */

  uint32_t FirstBit;            /*!< Specifies whether data transfers start from MSB or LSB bit.
                                     This parameter can be a value of @ref SPI_MSB_LSB_transmission */

  uint32_t TIMode;              /*!< Specifies if the TI mode is enabled or not .
                                     This parameter can be a value of @ref SPI_TI_mode */

  uint32_t CRCCalculation;      /*!< Specifies if the CRC calculation is enabled or not.
                                     This parameter can be a value of @ref SPI_CRC_Calculation */

  uint32_t CRCPolynomial;       /*!< Specifies the polynomial used for the CRC calculation.
                                     This parameter must be a number between Min_Data = 0 and Max_Data = 65535 */

  uint32_t CRCLength;           /*!< Specifies the CRC Length used for the CRC calculation.
                                     CRC Length is only used with Data8 and Data16, not other data size
                                     This parameter can be a value of @ref SPI_CRC_length */

  uint32_t NSSPMode;            /*!< Specifies whether the NSSP signal is enabled or not .
                                     This parameter can be a value of @ref SPI_NSSP_Mode
                                     This mode is activated by the NSSP bit in the SPIx_CR2 register and
                                     it takes effect only if the SPI interface is configured as Motorola SPI
                                     master (FRF=0) with capture on the first edge (SPIx_CR1 CPHA = 0,
                                     CPOL setting is ignored).. */
} SPI_InitTypeDef;

/**
  * @brief  HAL State structures definition
  */
typedef enum
{
  HAL_SPI_STATE_RESET      = 0x00,    /*!< Peripheral not Initialized                         */
  HAL_SPI_STATE_READY      = 0x01,    /*!< Peripheral Initialized and ready for use           */
  HAL_SPI_STATE_BUSY       = 0x02,    /*!< an internal process is ongoing                     */
  HAL_SPI_STATE_BUSY_TX    = 0x03,    /*!< Data Transmission process is ongoing               */
  HAL_SPI_STATE_BUSY_RX    = 0x04,    /*!< Data Reception process is ongoing                  */
  HAL_SPI_STATE_BUSY_TX_RX = 0x05,    /*!< Data Transmission and Reception process is ongoing*/
  HAL_SPI_STATE_ERROR      = 0x06     /*!< SPI error state                                   */
}HAL_SPI_StateTypeDef;

/**
  * @brief  SPI handle Structure definition
  */
typedef struct __SPI_HandleTypeDef
{
  SPI_TypeDef             *Instance;      /* SPI registers base address     */

  SPI_InitTypeDef         Init;           /* SPI communication parameters   */

  uint8_t                 *pTxBuffPtr;    /* Pointer to SPI Tx transfer Buffer */

  uint16_t                TxXferSize;     /* SPI Tx Transfer size */

  uint16_t                TxXferCount;    /* SPI Tx Transfer Counter */

  uint8_t                 *pRxBuffPtr;    /* Pointer to SPI Rx transfer Buffer */

  uint16_t                RxXferSize;     /* SPI Rx Transfer size */

  uint16_t                RxXferCount;    /* SPI Rx Transfer Counter */

  uint32_t                CRCSize;        /* SPI CRC size used for the transfer */

  void (*RxISR)(struct __SPI_HandleTypeDef *hspi); /* function pointer on Rx IRQ handler   */

  void (*TxISR)(struct __SPI_HandleTypeDef *hspi); /* function pointer on Tx IRQ handler   */

  DMA_HandleTypeDef       *hdmatx;        /* SPI Tx DMA Handle parameters   */

  DMA_HandleTypeDef       *hdmarx;        /* SPI Rx DMA Handle parameters   */

  HAL_LockTypeDef         Lock;           /* Locking object                 */

  HAL_SPI_StateTypeDef    State;          /* SPI communication state        */

  uint32_t                ErrorCode;      /* SPI Error code                 */

}SPI_HandleTypeDef;

/**
  * @}
  */

/* Exported constants --------------------------------------------------------*/

/** @defgroup SPI_Exported_Constants SPI Exported Constants
  * @{
  */

/** @defgroup SPI_Error_Code SPI Error Code
  * @{
  */
#define HAL_SPI_ERROR_NONE   (uint32_t)0x00000000  /*!< No error                          */
#define HAL_SPI_ERROR_MODF   (uint32_t)0x00000001  /*!< MODF error                        */
#define HAL_SPI_ERROR_CRC    (uint32_t)0x00000002  /*!< CRC error                         */
#define HAL_SPI_ERROR_OVR    (uint32_t)0x00000004  /*!< OVR error                         */
#define HAL_SPI_ERROR_FRE    (uint32_t)0x00000008  /*!< FRE error                         */
#define HAL_SPI_ERROR_DMA    (uint32_t)0x00000010  /*!< DMA transfer error                */
#define HAL_SPI_ERROR_FLAG   (uint32_t)0x00000020  /*!< Error on BSY/TXE/FTLVL/FRLVL Flag */
#define HAL_SPI_ERROR_UNKNOW (uint32_t)0x00000040  /*!< Unknow Error error                */
/**
  * @}
  */


/** @defgroup SPI_Mode SPI Mode
  * @{
  */
#define SPI_MODE_SLAVE                  ((uint32_t)0x00000000)
#define SPI_MODE_MASTER                 (SPI_CR1_MSTR | SPI_CR1_SSI)
/**
  * @}
  */

/** @defgroup SPI_Direction SPI Direction Mode
  * @{
  */
#define SPI_DIRECTION_2LINES            ((uint32_t)0x00000000)
#define SPI_DIRECTION_2LINES_RXONLY     SPI_CR1_RXONLY
#define SPI_DIRECTION_1LINE             SPI_CR1_BIDIMODE
/**
  * @}
  */

/** @defgroup SPI_Data_Size SPI Data Size
  * @{
  */
#define SPI_DATASIZE_4BIT               ((uint32_t)0x0300)
#define SPI_DATASIZE_5BIT               ((uint32_t)0x0400)
#define SPI_DATASIZE_6BIT               ((uint32_t)0x0500)
#define SPI_DATASIZE_7BIT               ((uint32_t)0x0600)
#define SPI_DATASIZE_8BIT               ((uint32_t)0x0700)
#define SPI_DATASIZE_9BIT               ((uint32_t)0x0800)
#define SPI_DATASIZE_10BIT              ((uint32_t)0x0900)
#define SPI_DATASIZE_11BIT              ((uint32_t)0x0A00)
#define SPI_DATASIZE_12BIT              ((uint32_t)0x0B00)
#define SPI_DATASIZE_13BIT              ((uint32_t)0x0C00)
#define SPI_DATASIZE_14BIT              ((uint32_t)0x0D00)
#define SPI_DATASIZE_15BIT              ((uint32_t)0x0E00)
#define SPI_DATASIZE_16BIT              ((uint32_t)0x0F00)
/**
  * @}
  */

/** @defgroup SPI_Clock_Polarity SPI Clock Polarity
  * @{
  */
#define SPI_POLARITY_LOW                ((uint32_t)0x00000000)
#define SPI_POLARITY_HIGH               SPI_CR1_CPOL
/**
  * @}
  */

/** @defgroup SPI_Clock_Phase SPI Clock Phase
  * @{
  */
#define SPI_PHASE_1EDGE                 ((uint32_t)0x00000000)
#define SPI_PHASE_2EDGE                 SPI_CR1_CPHA
/**
  * @}
  */

/** @defgroup SPI_Slave_Select_management SPI Slave Select management
  * @{
  */
#define SPI_NSS_SOFT                    SPI_CR1_SSM
#define SPI_NSS_HARD_INPUT              ((uint32_t)0x00000000)
#define SPI_NSS_HARD_OUTPUT             ((uint32_t)0x00040000)
/**
  * @}
  */

/** @defgroup SPI_NSSP_Mode SPI NSS Pulse Mode
  * @{
  */
#define SPI_NSS_PULSE_ENABLE            SPI_CR2_NSSP
#define SPI_NSS_PULSE_DISABLE           ((uint32_t)0x00000000)
/**
  * @}
  */

/** @defgroup SPI_BaudRate_Prescaler SPI BaudRate Prescaler
  * @{
  */
#define SPI_BAUDRATEPRESCALER_2         ((uint32_t)0x00000000)
#define SPI_BAUDRATEPRESCALER_4         ((uint32_t)0x00000008)
#define SPI_BAUDRATEPRESCALER_8         ((uint32_t)0x00000010)
#define SPI_BAUDRATEPRESCALER_16        ((uint32_t)0x00000018)
#define SPI_BAUDRATEPRESCALER_32        ((uint32_t)0x00000020)
#define SPI_BAUDRATEPRESCALER_64        ((uint32_t)0x00000028)
#define SPI_BAUDRATEPRESCALER_128       ((uint32_t)0x00000030)
#define SPI_BAUDRATEPRESCALER_256       ((uint32_t)0x00000038)
/**
  * @}
  */

/** @defgroup SPI_MSB_LSB_transmission SPI MSB LSB transmission
  * @{
  */
#define SPI_FIRSTBIT_MSB                ((uint32_t)0x00000000)
#define SPI_FIRSTBIT_LSB                SPI_CR1_LSBFIRST
/**
  * @}
  */

/** @defgroup SPI_TI_mode SPI TI mode
  * @{
  */
#define SPI_TIMODE_DISABLE              ((uint32_t)0x00000000)
#define SPI_TIMODE_ENABLE               SPI_CR2_FRF
/**
  * @}
  */

/** @defgroup SPI_CRC_Calculation SPI CRC Calculation
  * @{
  */
#define SPI_CRCCALCULATION_DISABLE      ((uint32_t)0x00000000)
#define SPI_CRCCALCULATION_ENABLE       SPI_CR1_CRCEN
/**
  * @}
  */

/** @defgroup SPI_CRC_length SPI CRC Length
  * @{
  * This parameter can be one of the following values:
  *     SPI_CRC_LENGTH_DATASIZE: aligned with the data size
  *     SPI_CRC_LENGTH_8BIT    : CRC 8bit
  *     SPI_CRC_LENGTH_16BIT   : CRC 16bit
  */
#define SPI_CRC_LENGTH_DATASIZE         ((uint32_t)0x00000000)
#define SPI_CRC_LENGTH_8BIT             ((uint32_t)0x00000001)
#define SPI_CRC_LENGTH_16BIT            ((uint32_t)0x00000002)
/**
  * @}
  */

/** @defgroup SPI_FIFO_reception_threshold SPI FIFO Reception Threshold
  * @{
  * This parameter can be one of the following values:
  *     SPI_RXFIFO_THRESHOLD or SPI_RXFIFO_THRESHOLD_QF :
  *          RXNE event is generated if the FIFO
  *          level is greater or equal to 1/2(16-bits).
  *     SPI_RXFIFO_THRESHOLD_HF: RXNE event is generated if the FIFO
  *          level is greater or equal to 1/4(8 bits). */
#define SPI_RXFIFO_THRESHOLD            SPI_CR2_FRXTH
#define SPI_RXFIFO_THRESHOLD_QF         SPI_CR2_FRXTH
#define SPI_RXFIFO_THRESHOLD_HF         ((uint32_t)0x00000000)

/**
  * @}
  */

/** @defgroup SPI_Interrupt_configuration_definition SPI Interrupt configuration definition
  * @brief SPI Interrupt definition
  *        Elements values convention: 0xXXXXXXXX
  *           - XXXXXXXX  : Interrupt control mask
  * @{
  */
#define SPI_IT_TXE                      SPI_CR2_TXEIE
#define SPI_IT_RXNE                     SPI_CR2_RXNEIE
#define SPI_IT_ERR                      SPI_CR2_ERRIE
/**
  * @}
  */


/** @defgroup SPI_Flag_definition SPI Flag definition
  * @brief Flag definition
  *        Elements values convention: 0xXXXXYYYY
  *           - XXXX  : Flag register Index
  *           - YYYY  : Flag mask
  * @{
  */
#define SPI_FLAG_RXNE                   SPI_SR_RXNE   /* SPI status flag: Rx buffer not empty flag */
#define SPI_FLAG_TXE                    SPI_SR_TXE    /* SPI status flag: Tx buffer empty flag */
#define SPI_FLAG_BSY                    SPI_SR_BSY    /* SPI status flag: Busy flag */
#define SPI_FLAG_CRCERR                 SPI_SR_CRCERR /* SPI Error flag: CRC error flag */
#define SPI_FLAG_MODF                   SPI_SR_MODF   /* SPI Error flag: Mode fault flag */
#define SPI_FLAG_OVR                    SPI_SR_OVR    /* SPI Error flag: Overrun flag */
#define SPI_FLAG_FRE                    SPI_SR_FRE    /* SPI Error flag: TI mode frame format error flag */
#define SPI_FLAG_FTLVL                  SPI_SR_FTLVL  /* SPI fifo transmission level */
#define SPI_FLAG_FRLVL                  SPI_SR_FRLVL  /* SPI fifo reception level */
/**
  * @}
  */

/** @defgroup SPI_transmission_fifo_status_level SPI Transmission FIFO Status Level
  * @{
  */
#define SPI_FTLVL_EMPTY           ((uint32_t)0x0000)
#define SPI_FTLVL_QUARTER_FULL    ((uint32_t)0x0800)
#define SPI_FTLVL_HALF_FULL       ((uint32_t)0x1000)
#define SPI_FTLVL_FULL            ((uint32_t)0x1800)

/**
  * @}
  */

/** @defgroup SPI_reception_fifo_status_level SPI Reception FIFO Status Level
  * @{
  */
#define SPI_FRLVL_EMPTY           ((uint32_t)0x0000)
#define SPI_FRLVL_QUARTER_FULL    ((uint32_t)0x0200)
#define SPI_FRLVL_HALF_FULL       ((uint32_t)0x0400)
#define SPI_FRLVL_FULL            ((uint32_t)0x0600)
/**
  * @}
  */

/**
  * @}
  */

/* Exported macros ------------------------------------------------------------*/
/** @defgroup SPI_Exported_Macros SPI Exported Macros
  * @{
  */

/** @brief  Reset SPI handle state
  * @param  __HANDLE__: SPI handle.
  * @retval None
  */
#define __HAL_SPI_RESET_HANDLE_STATE(__HANDLE__) ((__HANDLE__)->State = HAL_SPI_STATE_RESET)

/** @brief  Enables or disables the specified SPI interrupts.
  * @param  __HANDLE__ : specifies the SPI Handle.
  *         This parameter can be SPI where x: 1, 2, or 3 to select the SPI peripheral.
  * @param  __INTERRUPT__ : specifies the interrupt source to enable or disable.
  *        This parameter can be one of the following values:
  *            @arg SPI_IT_TXE: Tx buffer empty interrupt enable
  *            @arg SPI_IT_RXNE: RX buffer not empty interrupt enable
  *            @arg SPI_IT_ERR: Error interrupt enable
  * @retval None
  */
#define __HAL_SPI_ENABLE_IT(__HANDLE__, __INTERRUPT__)   ((__HANDLE__)->Instance->CR2 |= (__INTERRUPT__))
#define __HAL_SPI_DISABLE_IT(__HANDLE__, __INTERRUPT__)  ((__HANDLE__)->Instance->CR2 &= (~(__INTERRUPT__)))

/** @brief  Checks if the specified SPI interrupt source is enabled or disabled.
  * @param  __HANDLE__ : specifies the SPI Handle.
  *         This parameter can be SPI where x: 1, 2, or 3 to select the SPI peripheral.
  * @param  __INTERRUPT__ : specifies the SPI interrupt source to check.
  *          This parameter can be one of the following values:
  *            @arg SPI_IT_TXE: Tx buffer empty interrupt enable
  *            @arg SPI_IT_RXNE: RX buffer not empty interrupt enable
  *            @arg SPI_IT_ERR: Error interrupt enable
  * @retval The new state of __IT__ (TRUE or FALSE).
  */
#define __HAL_SPI_GET_IT_SOURCE(__HANDLE__, __INTERRUPT__) ((((__HANDLE__)->Instance->CR2 & (__INTERRUPT__)) == (__INTERRUPT__)) ? SET : RESET)

/** @brief  Checks whether the specified SPI flag is set or not.
  * @param  __HANDLE__ : specifies the SPI Handle.
  *         This parameter can be SPI where x: 1, 2, or 3 to select the SPI peripheral.
  * @param  __FLAG__ : specifies the flag to check.
  *        This parameter can be one of the following values:
  *            @arg SPI_FLAG_RXNE: Receive buffer not empty flag
  *            @arg SPI_FLAG_TXE: Transmit buffer empty flag
  *            @arg SPI_FLAG_CRCERR: CRC error flag
  *            @arg SPI_FLAG_MODF: Mode fault flag
  *            @arg SPI_FLAG_OVR: Overrun flag
  *            @arg SPI_FLAG_BSY: Busy flag
  *            @arg SPI_FLAG_FRE: Frame format error flag
  *            @arg SPI_FLAG_FTLVL: SPI fifo transmission level
  *            @arg SPI_FLAG_FRLVL: SPI fifo reception level
  * @retval The new state of __FLAG__ (TRUE or FALSE).
  */
#define __HAL_SPI_GET_FLAG(__HANDLE__, __FLAG__) ((((__HANDLE__)->Instance->SR) & (__FLAG__)) == (__FLAG__))

/** @brief  Clears the SPI CRCERR pending flag.
  * @param  __HANDLE__ : specifies the SPI Handle.
  *         This parameter can be SPI where x: 1, 2, or 3 to select the SPI peripheral.
  * @retval None
  */
#define __HAL_SPI_CLEAR_CRCERRFLAG(__HANDLE__) ((__HANDLE__)->Instance->SR = (uint16_t)(~SPI_FLAG_CRCERR))

/** @brief  Clears the SPI MODF pending flag.
  * @param  __HANDLE__ : specifies the SPI Handle.
  *         This parameter can be SPI where x: 1, 2, or 3 to select the SPI peripheral.
  *
  * @retval None
  */
#define __HAL_SPI_CLEAR_MODFFLAG(__HANDLE__)        \
   do{                                              \
     __IO uint32_t tmpreg;                          \
     tmpreg = (__HANDLE__)->Instance->SR;           \
     (__HANDLE__)->Instance->CR1 &= (~SPI_CR1_SPE); \
     UNUSED(tmpreg);                                \
   } while(0)

/** @brief  Clears the SPI OVR pending flag.
  * @param  __HANDLE__ : specifies the SPI Handle.
  *         This parameter can be SPI where x: 1, 2, or 3 to select the SPI peripheral.
  *
  * @retval None
  */
#define __HAL_SPI_CLEAR_OVRFLAG(__HANDLE__)         \
   do{                                              \
     __IO uint32_t tmpreg;                          \
     tmpreg = (__HANDLE__)->Instance->DR;           \
     tmpreg = (__HANDLE__)->Instance->SR;           \
     UNUSED(tmpreg);                                \
   } while(0)

/** @brief  Clears the SPI FRE pending flag.
  * @param  __HANDLE__ : specifies the SPI Handle.
  *         This parameter can be SPI where x: 1, 2, or 3 to select the SPI peripheral.
  *
  * @retval None
  */
#define __HAL_SPI_CLEAR_FREFLAG(__HANDLE__)         \
   do{                                              \
     __IO uint32_t tmpreg;                          \
     tmpreg = (__HANDLE__)->Instance->SR;           \
     UNUSED(tmpreg);                                \
   } while(0)

/** @brief  Enables the SPI.
  * @param  __HANDLE__ : specifies the SPI Handle.
  *         This parameter can be SPI where x: 1, 2, or 3 to select the SPI peripheral.
  * @retval None
  */
#define __HAL_SPI_ENABLE(__HANDLE__) ((__HANDLE__)->Instance->CR1 |=  SPI_CR1_SPE)

/** @brief  Disables the SPI.
  * @param  __HANDLE__ : specifies the SPI Handle.
  *         This parameter can be SPI where x: 1, 2, or 3 to select the SPI peripheral.
  * @retval None
  */
#define __HAL_SPI_DISABLE(__HANDLE__) ((__HANDLE__)->Instance->CR1 &= (~SPI_CR1_SPE))

/**
  * @}
  */

/* Private macros --------------------------------------------------------*/
/** @defgroup SPI_Private_Macros   SPI Private Macros
  * @{
  */

/** @brief  Sets the SPI transmit-only mode.
  * @param  __HANDLE__ : specifies the SPI Handle.
  *         This parameter can be SPI where x: 1, 2, or 3 to select the SPI peripheral.
  * @retval None
  */
#define SPI_1LINE_TX(__HANDLE__) ((__HANDLE__)->Instance->CR1 |= SPI_CR1_BIDIOE)

/** @brief  Sets the SPI receive-only mode.
  * @param  __HANDLE__ : specifies the SPI Handle.
  *         This parameter can be SPI where x: 1, 2, or 3 to select the SPI peripheral.
  * @retval None
  */
#define SPI_1LINE_RX(__HANDLE__) ((__HANDLE__)->Instance->CR1 &= (~SPI_CR1_BIDIOE))

/** @brief  Resets the CRC calculation of the SPI.
  * @param  __HANDLE__ : specifies the SPI Handle.
  *         This parameter can be SPI where x: 1, 2, or 3 to select the SPI peripheral.
  * @retval None
  */
#define SPI_RESET_CRC(__HANDLE__) do{(__HANDLE__)->Instance->CR1 &= (uint16_t)(~SPI_CR1_CRCEN);\
                                     (__HANDLE__)->Instance->CR1 |= SPI_CR1_CRCEN;}while(0)

#define IS_SPI_MODE(MODE) (((MODE) == SPI_MODE_SLAVE) || \
                           ((MODE) == SPI_MODE_MASTER))

#define IS_SPI_DIRECTION(MODE)   (((MODE) == SPI_DIRECTION_2LINES) || \
                                  ((MODE) == SPI_DIRECTION_2LINES_RXONLY) ||\
                                  ((MODE) == SPI_DIRECTION_1LINE))

#define IS_SPI_DIRECTION_2LINES(MODE) ((MODE) == SPI_DIRECTION_2LINES)

#define IS_SPI_DIRECTION_2LINES_OR_1LINE(MODE) (((MODE) == SPI_DIRECTION_2LINES)|| \
                                                 ((MODE) == SPI_DIRECTION_1LINE))

#define IS_SPI_DATASIZE(DATASIZE) (((DATASIZE) == SPI_DATASIZE_16BIT) || \
                                   ((DATASIZE) == SPI_DATASIZE_15BIT) || \
                                   ((DATASIZE) == SPI_DATASIZE_14BIT) || \
                                   ((DATASIZE) == SPI_DATASIZE_13BIT) || \
                                   ((DATASIZE) == SPI_DATASIZE_12BIT) || \
                                   ((DATASIZE) == SPI_DATASIZE_11BIT) || \
                                   ((DATASIZE) == SPI_DATASIZE_10BIT) || \
                                   ((DATASIZE) == SPI_DATASIZE_9BIT)  || \
                                   ((DATASIZE) == SPI_DATASIZE_8BIT)  || \
                                   ((DATASIZE) == SPI_DATASIZE_7BIT)  || \
                                   ((DATASIZE) == SPI_DATASIZE_6BIT)  || \
                                   ((DATASIZE) == SPI_DATASIZE_5BIT)  || \
                                   ((DATASIZE) == SPI_DATASIZE_4BIT))

#define IS_SPI_CPOL(CPOL) (((CPOL) == SPI_POLARITY_LOW) || \
                           ((CPOL) == SPI_POLARITY_HIGH))

#define IS_SPI_CPHA(CPHA) (((CPHA) == SPI_PHASE_1EDGE) || \
                           ((CPHA) == SPI_PHASE_2EDGE))

#define IS_SPI_NSS(NSS) (((NSS) == SPI_NSS_SOFT) || \
                         ((NSS) == SPI_NSS_HARD_INPUT) || \
                         ((NSS) == SPI_NSS_HARD_OUTPUT))

#define IS_SPI_NSSP(NSSP) (((NSSP) == SPI_NSS_PULSE_ENABLE) || \
                           ((NSSP) == SPI_NSS_PULSE_DISABLE))

#define IS_SPI_BAUDRATE_PRESCALER(PRESCALER) (((PRESCALER) == SPI_BAUDRATEPRESCALER_2) || \
                                              ((PRESCALER) == SPI_BAUDRATEPRESCALER_4) || \
                                              ((PRESCALER) == SPI_BAUDRATEPRESCALER_8) || \
                                              ((PRESCALER) == SPI_BAUDRATEPRESCALER_16) || \
                                              ((PRESCALER) == SPI_BAUDRATEPRESCALER_32) || \
                                              ((PRESCALER) == SPI_BAUDRATEPRESCALER_64) || \
                                              ((PRESCALER) == SPI_BAUDRATEPRESCALER_128) || \
                                              ((PRESCALER) == SPI_BAUDRATEPRESCALER_256))

#define IS_SPI_FIRST_BIT(BIT) (((BIT) == SPI_FIRSTBIT_MSB) || \
                               ((BIT) == SPI_FIRSTBIT_LSB))

#define IS_SPI_TIMODE(MODE) (((MODE) == SPI_TIMODE_DISABLE) || \
                             ((MODE) == SPI_TIMODE_ENABLE))

#define IS_SPI_CRC_CALCULATION(CALCULATION) (((CALCULATION) == SPI_CRCCALCULATION_DISABLE) || \
                                             ((CALCULATION) == SPI_CRCCALCULATION_ENABLE))

#define IS_SPI_CRC_LENGTH(LENGTH) (((LENGTH) == SPI_CRC_LENGTH_DATASIZE) ||\
                                   ((LENGTH) == SPI_CRC_LENGTH_8BIT)  ||   \
                                   ((LENGTH) == SPI_CRC_LENGTH_16BIT))

#define IS_SPI_CRC_POLYNOMIAL(POLYNOMIAL) (((POLYNOMIAL) >= 0x1) && ((POLYNOMIAL) <= 0xFFFF))


/**
  * @}
  */

/* Exported functions --------------------------------------------------------*/
/** @addtogroup SPI_Exported_Functions SPI Exported Functions
  * @{
  */

/** @addtogroup SPI_Exported_Functions_Group1 Initialization and de-initialization functions
  * @{
  */

/* Initialization and de-initialization functions  ****************************/
HAL_StatusTypeDef HAL_SPI_Init(SPI_HandleTypeDef *hspi);
HAL_StatusTypeDef HAL_SPI_DeInit (SPI_HandleTypeDef *hspi);
void HAL_SPI_MspInit(SPI_HandleTypeDef *hspi);
void HAL_SPI_MspDeInit(SPI_HandleTypeDef *hspi);
/**
  * @}
  */

/** @addtogroup SPI_Exported_Functions_Group2 IO operation functions
  * @{
  */

/* IO operation functions *****************************************************/
HAL_StatusTypeDef HAL_SPI_Transmit(SPI_HandleTypeDef *hspi, uint8_t *pData, uint16_t Size, uint32_t Timeout);
HAL_StatusTypeDef HAL_SPI_Receive(SPI_HandleTypeDef *hspi, uint8_t *pData, uint16_t Size, uint32_t Timeout);
HAL_StatusTypeDef HAL_SPI_TransmitReceive(SPI_HandleTypeDef *hspi, uint8_t *pTxData, uint8_t *pRxData, uint16_t Size, uint32_t Timeout);
HAL_StatusTypeDef HAL_SPI_Transmit_IT(SPI_HandleTypeDef *hspi, uint8_t *pData, uint16_t Size);
HAL_StatusTypeDef HAL_SPI_Receive_IT(SPI_HandleTypeDef *hspi, uint8_t *pData, uint16_t Size);
HAL_StatusTypeDef HAL_SPI_TransmitReceive_IT(SPI_HandleTypeDef *hspi, uint8_t *pTxData, uint8_t *pRxData, uint16_t Size);
HAL_StatusTypeDef HAL_SPI_Transmit_DMA(SPI_HandleTypeDef *hspi, uint8_t *pData, uint16_t Size);
HAL_StatusTypeDef HAL_SPI_Receive_DMA(SPI_HandleTypeDef *hspi, uint8_t *pData, uint16_t Size);
HAL_StatusTypeDef HAL_SPI_TransmitReceive_DMA(SPI_HandleTypeDef *hspi, uint8_t *pTxData, uint8_t *pRxData, uint16_t Size);
HAL_StatusTypeDef HAL_SPI_DMAPause(SPI_HandleTypeDef *hspi);
HAL_StatusTypeDef HAL_SPI_DMAResume(SPI_HandleTypeDef *hspi);
HAL_StatusTypeDef HAL_SPI_DMAStop(SPI_HandleTypeDef *hspi);

void HAL_SPI_IRQHandler(SPI_HandleTypeDef *hspi);
void HAL_SPI_TxCpltCallback(SPI_HandleTypeDef *hspi);
void HAL_SPI_RxCpltCallback(SPI_HandleTypeDef *hspi);
void HAL_SPI_TxRxCpltCallback(SPI_HandleTypeDef *hspi);
void HAL_SPI_TxHalfCpltCallback(SPI_HandleTypeDef *hspi);
void HAL_SPI_RxHalfCpltCallback(SPI_HandleTypeDef *hspi);
void HAL_SPI_TxRxHalfCpltCallback(SPI_HandleTypeDef *hspi);
void HAL_SPI_ErrorCallback(SPI_HandleTypeDef *hspi);
/**
  * @}
  */

/** @addtogroup SPI_Exported_Functions_Group3 Peripheral State and Errors functions
  * @{
  */

/* Peripheral State and Error functions ***************************************/
HAL_SPI_StateTypeDef HAL_SPI_GetState(SPI_HandleTypeDef *hspi);
uint32_t             HAL_SPI_GetError(SPI_HandleTypeDef *hspi);
/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */

#ifdef __cplusplus
}
#endif

#endif /* __STM32F7xx_HAL_SPI_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
