/**
  ******************************************************************************
  * @file    stm32l1xx_spi.c
  * @author  MCD Application Team
  * @version V1.0.0RC1
  * @date    07/02/2010
  * @brief   This file provides all the SPI firmware functions.
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

/* Includes ------------------------------------------------------------------*/
#include "stm32l1xx_spi.h"
#include "stm32l1xx_rcc.h"

/** @addtogroup STM32L1xx_StdPeriph_Driver
  * @{
  */

/** @defgroup SPI 
  * @brief SPI driver modules
  * @{
  */ 

/** @defgroup SPI_Private_TypesDefinitions
  * @{
  */

/**
  * @}
  */ 


/** @defgroup SPI_Private_Defines
  * @{
  */

/* SPI registers Masks */
#define CR1_CLEAR_MASK       ((uint16_t)0x3040)

/**
  * @}
  */

/** @defgroup SPI_Private_Macros
  * @{
  */

/**
  * @}
  */

/** @defgroup SPI_Private_Variables
  * @{
  */

/**
  * @}
  */

/** @defgroup SPI_Private_FunctionPrototypes
  * @{
  */

/**
  * @}
  */

/** @defgroup SPI_Private_Functions
  * @{
  */

/**
  * @brief  Deinitializes the SPIx peripheral registers to their default
  *         reset values.
  * @param  SPIx: where x can be 1 or 2 to select the SPI peripheral.
  * @retval None
  */
void SPI_DeInit(SPI_TypeDef* SPIx)
{
  /* Check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));

  if (SPIx == SPI1)
  {
    /* Enable SPI1 reset state */
    RCC_APB2PeriphResetCmd(RCC_APB2Periph_SPI1, ENABLE);
    /* Release SPI1 from reset state */
    RCC_APB2PeriphResetCmd(RCC_APB2Periph_SPI1, DISABLE);
  }
  else
  {
    if (SPIx == SPI2)
    {
      /* Enable SPI2 reset state */
      RCC_APB1PeriphResetCmd(RCC_APB1Periph_SPI2, ENABLE);
      /* Release SPI2 from reset state */
      RCC_APB1PeriphResetCmd(RCC_APB1Periph_SPI2, DISABLE);
    }
  }
}

/**
  * @brief  Initializes the SPIx peripheral according to the specified 
  *   parameters in the SPI_InitStruct.
  * @param  SPIx: where x can be 1 or 2 to select the SPI peripheral.
  * @param  SPI_InitStruct: pointer to a SPI_InitTypeDef structure that
  *   contains the configuration information for the specified SPI peripheral.
  * @retval None
  */
void SPI_Init(SPI_TypeDef* SPIx, SPI_InitTypeDef* SPI_InitStruct)
{
  uint16_t tmpreg = 0;
  
  /* check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));   
  
  /* Check the SPI parameters */
  assert_param(IS_SPI_DIRECTION_MODE(SPI_InitStruct->SPI_Direction));
  assert_param(IS_SPI_MODE(SPI_InitStruct->SPI_Mode));
  assert_param(IS_SPI_DATASIZE(SPI_InitStruct->SPI_DataSize));
  assert_param(IS_SPI_CPOL(SPI_InitStruct->SPI_CPOL));
  assert_param(IS_SPI_CPHA(SPI_InitStruct->SPI_CPHA));
  assert_param(IS_SPI_NSS(SPI_InitStruct->SPI_NSS));
  assert_param(IS_SPI_BAUDRATE_PRESCALER(SPI_InitStruct->SPI_BaudRatePrescaler));
  assert_param(IS_SPI_FIRST_BIT(SPI_InitStruct->SPI_FirstBit));
  assert_param(IS_SPI_CRC_POLYNOMIAL(SPI_InitStruct->SPI_CRCPolynomial));

/*---------------------------- SPIx CR1 Configuration ------------------------*/
  /* Get the SPIx CR1 value */
  tmpreg = SPIx->CR1;
  /* Clear BIDIMode, BIDIOE, RxONLY, SSM, SSI, LSBFirst, BR, MSTR, CPOL and CPHA bits */
  tmpreg &= CR1_CLEAR_MASK;
  /* Configure SPIx: direction, NSS management, first transmitted bit, BaudRate prescaler
     master/salve mode, CPOL and CPHA */
  /* Set BIDImode, BIDIOE and RxONLY bits according to SPI_Direction value */
  /* Set SSM, SSI and MSTR bits according to SPI_Mode and SPI_NSS values */
  /* Set LSBFirst bit according to SPI_FirstBit value */
  /* Set BR bits according to SPI_BaudRatePrescaler value */
  /* Set CPOL bit according to SPI_CPOL value */
  /* Set CPHA bit according to SPI_CPHA value */
  tmpreg |= (uint16_t)((uint32_t)SPI_InitStruct->SPI_Direction | SPI_InitStruct->SPI_Mode |
                  SPI_InitStruct->SPI_DataSize | SPI_InitStruct->SPI_CPOL |  
                  SPI_InitStruct->SPI_CPHA | SPI_InitStruct->SPI_NSS |  
                  SPI_InitStruct->SPI_BaudRatePrescaler | SPI_InitStruct->SPI_FirstBit);
  /* Write to SPIx CR1 */
  SPIx->CR1 = tmpreg;
  
/*---------------------------- SPIx CRCPOLY Configuration --------------------*/
  /* Write to SPIx CRCPOLY */
  SPIx->CRCPR = SPI_InitStruct->SPI_CRCPolynomial;
}

/**
  * @brief  Fills each SPI_InitStruct member with its default value.
  * @param  SPI_InitStruct : pointer to a SPI_InitTypeDef structure which will be initialized.
  * @retval None
  */
void SPI_StructInit(SPI_InitTypeDef* SPI_InitStruct)
{
/*--------------- Reset SPI init structure parameters values -----------------*/
  /* Initialize the SPI_Direction member */
  SPI_InitStruct->SPI_Direction = SPI_Direction_2Lines_FullDuplex;
  /* initialize the SPI_Mode member */
  SPI_InitStruct->SPI_Mode = SPI_Mode_Slave;
  /* initialize the SPI_DataSize member */
  SPI_InitStruct->SPI_DataSize = SPI_DataSize_8b;
  /* Initialize the SPI_CPOL member */
  SPI_InitStruct->SPI_CPOL = SPI_CPOL_Low;
  /* Initialize the SPI_CPHA member */
  SPI_InitStruct->SPI_CPHA = SPI_CPHA_1Edge;
  /* Initialize the SPI_NSS member */
  SPI_InitStruct->SPI_NSS = SPI_NSS_Hard;
  /* Initialize the SPI_BaudRatePrescaler member */
  SPI_InitStruct->SPI_BaudRatePrescaler = SPI_BaudRatePrescaler_2;
  /* Initialize the SPI_FirstBit member */
  SPI_InitStruct->SPI_FirstBit = SPI_FirstBit_MSB;
  /* Initialize the SPI_CRCPolynomial member */
  SPI_InitStruct->SPI_CRCPolynomial = 7;
}


/**
  * @brief  Enables or disables the specified SPI peripheral.
  * @param  SPIx: where x can be 1 or 2 to select the SPI peripheral.
  * @param  NewState: new state of the SPIx peripheral. 
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void SPI_Cmd(SPI_TypeDef* SPIx, FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  if (NewState != DISABLE)
  {
    /* Enable the selected SPI peripheral */
    SPIx->CR1 |= SPI_CR1_SPE;
  }
  else
  {
    /* Disable the selected SPI peripheral */
    SPIx->CR1 &= (uint16_t)~((uint16_t)SPI_CR1_SPE);
  }
}

/**
  * @brief  Enables or disables the specified SPI interrupts.
  * @param  SPIx: where x can be 1 or 2 in SPI mode 
  * @param  SPI_IT: specifies the SPI interrupt source to be enabled or disabled. 
  *   This parameter can be one of the following values:
  *     @arg SPI_IT_TXE: Tx buffer empty interrupt mask
  *     @arg SPI_IT_RXNE: Rx buffer not empty interrupt mask
  *     @arg SPI_IT_ERR: Error interrupt mask
  * @param  NewState: new state of the specified SPI interrupt.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void SPI_ITConfig(SPI_TypeDef* SPIx, uint8_t SPI_IT, FunctionalState NewState)
{
  uint16_t itpos = 0, itmask = 0 ;
  /* Check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  assert_param(IS_SPI_CONFIG_IT(SPI_IT));

  /* Get the SPI IT index */
  itpos = SPI_IT >> 4;

  /* Set the IT mask */
  itmask = (uint16_t)1 << (uint16_t)itpos;

  if (NewState != DISABLE)
  {
    /* Enable the selected SPI interrupt */
    SPIx->CR2 |= itmask;
  }
  else
  {
    /* Disable the selected SPI interrupt */
    SPIx->CR2 &= (uint16_t)~itmask;
  }
}

/**
  * @brief  Enables or disables the SPIx DMA interface.
  * @param  SPIx: where x can be 1 or 2 in SPI mode 
  * @param  SPI_DMAReq: specifies the SPI DMA transfer request to be enabled or disabled. 
  *   This parameter can be any combination of the following values:
  *     @arg SPI_DMAReq_Tx: Tx buffer DMA transfer request
  *     @arg SPI_DMAReq_Rx: Rx buffer DMA transfer request
  * @param  NewState: new state of the selected SPI DMA transfer request.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void SPI_DMACmd(SPI_TypeDef* SPIx, uint16_t SPI_DMAReq, FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  assert_param(IS_SPI_DMAREQ(SPI_DMAReq));
  if (NewState != DISABLE)
  {
    /* Enable the selected SPI DMA requests */
    SPIx->CR2 |= SPI_DMAReq;
  }
  else
  {
    /* Disable the selected SPI DMA requests */
    SPIx->CR2 &= (uint16_t)~SPI_DMAReq;
  }
}

/**
  * @brief  Transmits a Data through the SPIx peripheral.
  * @param  SPIx: where x can be 1 or 2 in SPI mode 
  * @param  Data : Data to be transmitted.
  * @retval None
  */
void SPI_SendData(SPI_TypeDef* SPIx, uint16_t Data)
{
  /* Check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));
  
  /* Write in the DR register the data to be sent */
  SPIx->DR = Data;
}

/**
  * @brief  Returns the most recent received data by the SPIx peripheral. 
  * @param  SPIx: where x can be 1 or 2 in SPI mode 
  * @retval The value of the received data.
  */
uint16_t SPI_ReceiveData(SPI_TypeDef* SPIx)
{
  /* Check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));
  
  /* Return the data in the DR register */
  return SPIx->DR;
}

/**
  * @brief  Configures internally by software the NSS pin for the selected SPI.
  * @param  SPIx: where x can be 1 or 2 to select the SPI peripheral.
  * @param  SPI_NSSInternalSoft: specifies the SPI NSS internal state.
  *   This parameter can be one of the following values:
  *     @arg SPI_NSSInternalSoft_Set: Set NSS pin internally
  *     @arg SPI_NSSInternalSoft_Reset: Reset NSS pin internally
  * @retval None
  */
void SPI_NSSInternalSoftwareConfig(SPI_TypeDef* SPIx, uint16_t SPI_NSSInternalSoft)
{
  /* Check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));
  assert_param(IS_SPI_NSS_INTERNAL(SPI_NSSInternalSoft));
  if (SPI_NSSInternalSoft != SPI_NSSInternalSoft_Reset)
  {
    /* Set NSS pin internally by software */
    SPIx->CR1 |= SPI_NSSInternalSoft_Set;
  }
  else
  {
    /* Reset NSS pin internally by software */
    SPIx->CR1 &= SPI_NSSInternalSoft_Reset;
  }
}

/**
  * @brief  Enables or disables the SS output for the selected SPI.
  * @param  SPIx: where x can be 1 or 2 to select the SPI peripheral.
  * @param  NewState: new state of the SPIx SS output. 
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void SPI_SSOutputCmd(SPI_TypeDef* SPIx, FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  if (NewState != DISABLE)
  {
    /* Enable the selected SPI SS output */
    SPIx->CR2 |= (uint16_t)SPI_CR2_SSOE;
  }
  else
  {
    /* Disable the selected SPI SS output */
    SPIx->CR2 &= (uint16_t)~((uint16_t)SPI_CR2_SSOE);
  }
}

/**
  * @brief  Configures the data size for the selected SPI.
  * @param  SPIx: where x can be 1 or 2  to select the SPI peripheral.
  * @param  SPI_DataSize: specifies the SPI data size.
  *   This parameter can be one of the following values:
  *     @arg SPI_DataSize_16b: Set data frame format to 16bit
  *     @arg SPI_DataSize_8b: Set data frame format to 8bit
  * @retval None
  */
void SPI_DataSizeConfig(SPI_TypeDef* SPIx, uint16_t SPI_DataSize)
{
  /* Check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));
  assert_param(IS_SPI_DATASIZE(SPI_DataSize));
  /* Clear DFF bit */
  SPIx->CR1 &= (uint16_t)~SPI_DataSize_16b;
  /* Set new DFF bit value */
  SPIx->CR1 |= SPI_DataSize;
}

/**
  * @brief  Transmit the SPIx CRC value.
  * @param  SPIx: where x can be 1 or 2  to select the SPI peripheral.
  * @retval None
  */
void SPI_TransmitCRC(SPI_TypeDef* SPIx)
{
  /* Check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));
  
  /* Enable the selected SPI CRC transmission */
  SPIx->CR1 |= SPI_CR1_CRCNEXT;
}

/**
  * @brief  Enables or disables the CRC value calculation of the transfered bytes.
  * @param  SPIx: where x can be 1 or 2  to select the SPI peripheral.
  * @param  NewState: new state of the SPIx CRC value calculation.
  *   This parameter can be: ENABLE or DISABLE.
  * @retval None
  */
void SPI_CalculateCRC(SPI_TypeDef* SPIx, FunctionalState NewState)
{
  /* Check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));
  assert_param(IS_FUNCTIONAL_STATE(NewState));
  if (NewState != DISABLE)
  {
    /* Enable the selected SPI CRC calculation */
    SPIx->CR1 |= SPI_CR1_CRCEN;
  }
  else
  {
    /* Disable the selected SPI CRC calculation */
    SPIx->CR1 &= (uint16_t)~((uint16_t)SPI_CR1_CRCEN);
  }
}

/**
  * @brief  Returns the transmit or the receive CRC register value for the specified SPI.
  * @param  SPIx: where x can be 1 or 2  to select the SPI peripheral.
  * @param  SPI_CRC: specifies the CRC register to be read.
  *   This parameter can be one of the following values:
  *     @arg SPI_CRC_Tx: Selects Tx CRC register
  *     @arg SPI_CRC_Rx: Selects Rx CRC register
  * @retval The selected CRC register value..
  */
uint16_t SPI_GetCRC(SPI_TypeDef* SPIx, uint8_t SPI_CRC)
{
  uint16_t crcreg = 0;
  /* Check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));
  assert_param(IS_SPI_CRC(SPI_CRC));
  if (SPI_CRC != SPI_CRC_Rx)
  {
    /* Get the Tx CRC register */
    crcreg = SPIx->TXCRCR;
  }
  else
  {
    /* Get the Rx CRC register */
    crcreg = SPIx->RXCRCR;
  }
  /* Return the selected CRC register */
  return crcreg;
}

/**
  * @brief  Returns the CRC Polynomial register value for the specified SPI.
  * @param  SPIx: where x can be 1 or 2  to select the SPI peripheral.
  * @retval The CRC Polynomial register value.
  */
uint16_t SPI_GetCRCPolynomial(SPI_TypeDef* SPIx)
{
  /* Check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));
  
  /* Return the CRC polynomial register */
  return SPIx->CRCPR;
}

/**
  * @brief  Selects the data transfer direction in bi-directional mode for the specified SPI.
  * @param  SPIx: where x can be 1 or 2  to select the SPI peripheral.
  * @param  SPI_Direction: specifies the data transfer direction in bi-directional mode. 
  *   This parameter can be one of the following values:
  *     @arg SPI_Direction_Tx: Selects Tx transmission direction
  *     @arg SPI_Direction_Rx: Selects Rx receive direction
  * @retval None
  */
void SPI_BiDirectionalLineConfig(SPI_TypeDef* SPIx, uint16_t SPI_Direction)
{
  /* Check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));
  assert_param(IS_SPI_DIRECTION(SPI_Direction));
  if (SPI_Direction == SPI_Direction_Tx)
  {
    /* Set the Tx only mode */
    SPIx->CR1 |= SPI_Direction_Tx;
  }
  else
  {
    /* Set the Rx only mode */
    SPIx->CR1 &= SPI_Direction_Rx;
  }
}

/**
  * @brief  Checks whether the specified SPI flag is set or not.
  * @param  SPIx: where x can be 1 or 2 in SPI mode 
  * @param  SPI_FLAG: specifies the SPI flag to check. 
  *   This parameter can be one of the following values:
  *     @arg SPI_FLAG_TXE: Transmit buffer empty flag.
  *     @arg SPI_FLAG_RXNE: Receive buffer not empty flag.
  *     @arg SPI_FLAG_BSY: Busy flag.
  *     @arg SPI_FLAG_OVR: Overrun flag.
  *     @arg SPI_FLAG_MODF: Mode Fault flag.
  *     @arg SPI_FLAG_CRCERR: CRC Error flag.
  * @retval The new state of SPI_FLAG (SET or RESET).
  */
FlagStatus SPI_GetFlagStatus(SPI_TypeDef* SPIx, uint16_t SPI_FLAG)
{
  FlagStatus bitstatus = RESET;
  /* Check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));
  assert_param(IS_SPI_GET_FLAG(SPI_FLAG));
  /* Check the status of the specified SPI flag */
  if ((SPIx->SR & SPI_FLAG) != (uint16_t)RESET)
  {
    /* SPI_FLAG is set */
    bitstatus = SET;
  }
  else
  {
    /* SPI_FLAG is reset */
    bitstatus = RESET;
  }
  /* Return the SPI_FLAG status */
  return  bitstatus;
}

/**
  * @brief  Clears the SPIx CRC Error (CRCERR) flag.
  * @param  SPIx: where x can be 1 or 2 in SPI mode 
  * @param  SPI_FLAG: specifies the SPI flag to clear. 
  *   This function clears only CRCERR flag.
  * @note
  *   - OVR (OverRun error) flag is cleared by software sequence: a read 
  *     operation to SPI_DR register (SPI_ReceiveData()) followed by a read 
  *     operation to SPI_SR register (SPI_GetFlagStatus()).
  *   - UDR (UnderRun error) flag is cleared by a read operation to 
  *     SPI_SR register (SPI_GetFlagStatus()).
  *   - MODF (Mode Fault) flag is cleared by software sequence: a read/write 
  *     operation to SPI_SR register (SPI_GetFlagStatus()) followed by a 
  *     write operation to SPI_CR1 register (SPI_Cmd() to enable the SPI).
  * @retval None
  */
void SPI_ClearFlag(SPI_TypeDef* SPIx, uint16_t SPI_FLAG)
{
  /* Check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));
  assert_param(IS_SPI_CLEAR_FLAG(SPI_FLAG));
    
    /* Clear the selected SPI CRC Error (CRCERR) flag */
    SPIx->SR = (uint16_t)~SPI_FLAG;
}

/**
  * @brief  Checks whether the specified SPI interrupt has occurred or not.
  * @param  SPIx: where x can be
  *   - 1 or 2 in SPI mode 
  * @param  SPI_IT: specifies the SPI interrupt source to check. 
  *   This parameter can be one of the following values:
  *     @arg SPI_IT_TXE: Transmit buffer empty interrupt.
  *     @arg SPI_IT_RXNE: Receive buffer not empty interrupt.
  *     @arg SPI_IT_OVR: Overrun interrupt.
  *     @arg SPI_IT_MODF: Mode Fault interrupt.
  *     @arg SPI_IT_CRCERR: CRC Error interrupt.
  * @retval The new state of SPI_IT (SET or RESET).
  */
ITStatus SPI_GetITStatus(SPI_TypeDef* SPIx, uint8_t SPI_IT)
{
  ITStatus bitstatus = RESET;
  uint16_t itpos = 0, itmask = 0, enablestatus = 0;

  /* Check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));
  assert_param(IS_SPI_GET_IT(SPI_IT));

  /* Get the SPI IT index */
  itpos = 0x01 << (SPI_IT & 0x0F);

  /* Get the SPI IT mask */
  itmask = SPI_IT >> 4;

  /* Set the IT mask */
  itmask = 0x01 << itmask;

  /* Get the SPI_IT enable bit status */
  enablestatus = (SPIx->CR2 & itmask) ;

  /* Check the status of the specified SPI interrupt */
  if (((SPIx->SR & itpos) != (uint16_t)RESET) && enablestatus)
  {
    /* SPI_IT is set */
    bitstatus = SET;
  }
  else
  {
    /* SPI_IT is reset */
    bitstatus = RESET;
  }
  /* Return the SPI_IT status */
  return bitstatus;
}

/**
  * @brief  Clears the SPIx CRC Error (CRCERR) interrupt pending bit.
  * @param  SPIx: where x can be
  *   - 1 or 2 in SPI mode 
  * @param  SPI_IT: specifies the SPI interrupt pending bit to clear.
  *   This function clears only CRCERR intetrrupt pending bit.   
  * @note
  *   - OVR (OverRun Error) interrupt pending bit is cleared by software 
  *     sequence: a read operation to SPI_DR register (SPI_ReceiveData()) 
  *     followed by a read operation to SPI_SR register (SPI_GetITStatus()).
  *   - UDR (UnderRun Error) interrupt pending bit is cleared by a read 
  *     operation to SPI_SR register (SPI_GetITStatus()).
  *   - MODF (Mode Fault) interrupt pending bit is cleared by software sequence:
  *     a read/write operation to SPI_SR register (SPI_GetITStatus()) 
  *     followed by a write operation to SPI_CR1 register (SPI_Cmd() to enable 
  *     the SPI).
  * @retval None
  */
void SPI_ClearITPendingBit(SPI_TypeDef* SPIx, uint8_t SPI_IT)
{
  uint16_t itpos = 0;
  /* Check the parameters */
  assert_param(IS_SPI_ALL_PERIPH(SPIx));
  assert_param(IS_SPI_CLEAR_IT(SPI_IT));

  /* Get the SPI IT index */
  itpos = 0x01 << (SPI_IT & 0x0F);

  /* Clear the selected SPI CRC Error (CRCERR) interrupt pending bit */
  SPIx->SR = (uint16_t)~itpos;
}
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
