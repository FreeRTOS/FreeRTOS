/******************** (C) COPYRIGHT 2007 STMicroelectronics ********************
* File Name          : stm32f10x_spi.c
* Author             : MCD Application Team
* Date First Issued  : 09/29/2006
* Description        : This file provides all the SPI firmware functions.
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

/* Includes ------------------------------------------------------------------*/
#include "stm32f10x_spi.h"
#include "stm32f10x_rcc.h"

/* Private typedef -----------------------------------------------------------*/
/* Private define ------------------------------------------------------------*/
/* SPI SPE mask */
#define CR1_SPE_Set          ((u16)0x0040)
#define CR1_SPE_Reset        ((u16)0xFFBF)

/* SPI CRCNext mask */
#define CR1_CRCNext_Set      ((u16)0x1000)

/* SPI CRCEN mask */
#define CR1_CRCEN_Set        ((u16)0x2000)
#define CR1_CRCEN_Reset      ((u16)0xDFFF)

/* SPI SSOE mask */
#define CR2_SSOE_Set        ((u16)0x0004)
#define CR2_SSOE_Reset      ((u16)0xFFFB)

/* SPI registers Masks */
#define CR1_CLEAR_Mask       ((u16)0x3040)

/* Private macro -------------------------------------------------------------*/
/* Private variables ---------------------------------------------------------*/
/* Private function prototypes -----------------------------------------------*/
/* Private functions ---------------------------------------------------------*/

/*******************************************************************************
* Function Name  : SPI_DeInit
* Description    : Deinitializes the SPIx peripheral registers to their default
*                  reset values.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void SPI_DeInit(SPI_TypeDef* SPIx)
{
  switch (*(u32*)&SPIx)
  {
    case SPI1_BASE:
      /* Enable SPI1 reset state */
      RCC_APB2PeriphResetCmd(RCC_APB2Periph_SPI1, ENABLE);
      /* Release SPI1 from reset state */
      RCC_APB2PeriphResetCmd(RCC_APB2Periph_SPI1, DISABLE);
      break;

    case SPI2_BASE:
      /* Enable SPI2 reset state */
      RCC_APB1PeriphResetCmd(RCC_APB1Periph_SPI2, ENABLE);
      /* Release SPI2 from reset state */
      RCC_APB1PeriphResetCmd(RCC_APB1Periph_SPI2, DISABLE);
      break;

    default:
      break;
  }
}

/*******************************************************************************
* Function Name  : SPI_Init
* Description    : Initializes the SPIx according to the specified parameters
*                  in the SPI_InitStruct.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
*                  - SPI_InitStruct: pointer to a SPI_InitTypeDef structure that
*                    contains the configuration information for the specified
*                    SPI peripheral.
* Output         : None
* Return         : None
******************************************************************************/
void SPI_Init(SPI_TypeDef* SPIx, SPI_InitTypeDef* SPI_InitStruct)
{
  u16 tmpreg = 0;

  /* Check the parameters */
  assert(IS_SPI_DIRECTION_MODE(SPI_InitStruct->SPI_Direction));
  assert(IS_SPI_MODE(SPI_InitStruct->SPI_Mode));
  assert(IS_SPI_DATASIZE(SPI_InitStruct->SPI_DataSize));
  assert(IS_SPI_CPOL(SPI_InitStruct->SPI_CPOL));
  assert(IS_SPI_CPHA(SPI_InitStruct->SPI_CPHA));
  assert(IS_SPI_NSS(SPI_InitStruct->SPI_NSS));
  assert(IS_SPI_BAUDRATE_PRESCALER(SPI_InitStruct->SPI_BaudRatePrescaler));
  assert(IS_SPI_FIRST_BIT(SPI_InitStruct->SPI_FirstBit));
  assert(IS_SPI_CRC_POLYNOMIAL(SPI_InitStruct->SPI_CRCPolynomial));

/*---------------------------- SPIx CR1 Configuration ------------------------*/
  /* Get the SPIx CR1 value */
  tmpreg = SPIx->CR1;
  /* Clear BIDIMode, BIDIOE, RxONLY, SSM, SSI, LSBFirst, BR, MSTR, CPOL and CPHA bits */
  tmpreg &= CR1_CLEAR_Mask;
  /* Configure SPIx: direction, NSS management, first transmitted bit, BaudRate prescaler
     master/salve mode, CPOL and CPHA */
  /* Set BIDImode, BIDIOE and RxONLY bits according to SPI_Direction value */
  /* Set SSM, SSI and MSTR bits according to SPI_Mode and SPI_NSS values */
  /* Set LSBFirst bit according to SPI_FirstBit value */
  /* Set BR bits according to SPI_BaudRatePrescaler value */
  /* Set CPOL bit according to SPI_CPOL value */
  /* Set CPHA bit according to SPI_CPHA value */
  tmpreg |= (u16)((u32)SPI_InitStruct->SPI_Direction | SPI_InitStruct->SPI_Mode |
                  SPI_InitStruct->SPI_DataSize | SPI_InitStruct->SPI_CPOL |  
                  SPI_InitStruct->SPI_CPHA | SPI_InitStruct->SPI_NSS |  
                  SPI_InitStruct->SPI_BaudRatePrescaler | SPI_InitStruct->SPI_FirstBit);
  /* Write to SPIx CR1 */
  SPIx->CR1 = tmpreg;

/*---------------------------- SPIx CRCPOLY Configuration --------------------*/
  /* Write to SPIx CRCPOLY */
  SPIx->CRCPR = SPI_InitStruct->SPI_CRCPolynomial;
}

/*******************************************************************************
* Function Name  : SPI_StructInit
* Description    : Fills each SPI_InitStruct member with its default value.
* Input          : - SPI_InitStruct : pointer to a SPI_InitTypeDef structure
*                    which will be initialized.
* Output         : None
* Return         : None
*******************************************************************************/
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

/*******************************************************************************
* Function Name  : SPI_Cmd
* Description    : Enables or disables the specified SPI peripheral.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
*                  - NewState: new state of the SPIx peripheral. 
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void SPI_Cmd(SPI_TypeDef* SPIx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the selected SPI peripheral */
    SPIx->CR1 |= CR1_SPE_Set;
  }
  else
  {
    /* Disable the selected SPI peripheral */
    SPIx->CR1 &= CR1_SPE_Reset;
  }
}

/*******************************************************************************
* Function Name  : SPI_ITConfig
* Description    : Enables or disables the specified SPI interrupts.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
*                  - SPI_IT: specifies the SPI interrupts sources to be enabled
*                    or disabled. 
*                    This parameter can be one of the following values:
*                       - SPI_IT_TXE: Tx buffer empty interrupt mask
*                       - SPI_IT_RXNE: Rx buffer not empty interrupt mask
*                       - SPI_IT_ERR: Error interrupt mask
*                  - NewState: new state of the specified SPI interrupts.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void SPI_ITConfig(SPI_TypeDef* SPIx, u8 SPI_IT, FunctionalState NewState)
{
  u16 itpos = 0, itmask = 0 ;

  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));
  assert(IS_SPI_CONFIG_IT(SPI_IT));

  /* Get the SPI IT index */
  itpos = SPI_IT >> 4;
  /* Set the IT mask */
  itmask = (u16)((u16)1 << itpos);

  if (NewState != DISABLE)
  {
    /* Enable the selected SPI interrupt */
    SPIx->CR2 |= itmask;
  }
  else
  {
    /* Disable the selected SPI interrupt */
    SPIx->CR2 &= (u16)~itmask;
  }
}

/*******************************************************************************
* Function Name  : SPI_DMACmd
* Description    : Enables or disables the SPIx’s DMA interface.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
*                  - SPI_DMAReq: specifies the SPI DMA transfer request to be
*                    enabled or disabled. 
*                    This parameter can be any combination of the following values:
*                       - SPI_DMAReq_Tx: Tx buffer DMA transfer request
*                       - SPI_DMAReq_Rx: Rx buffer DMA transfer request
*                  - NewState: new state of the selected SPI DMA transfer request.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void SPI_DMACmd(SPI_TypeDef* SPIx, u16 SPI_DMAReq, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));
  assert(IS_SPI_DMA_REQ(SPI_DMAReq));

  if (NewState != DISABLE)
  {
    /* Enable the selected SPI DMA requests */
    SPIx->CR2 |= SPI_DMAReq;
  }
  else
  {
    /* Disable the selected SPI DMA requests */
    SPIx->CR2 &= (u16)~SPI_DMAReq;
  }
}

/*******************************************************************************
* Function Name  : SPI_SendData
* Description    : Transmits a Data through the SPIx peripheral.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
*                  - Data : Data to be transmitted..
* Output         : None
* Return         : None
*******************************************************************************/
void SPI_SendData(SPI_TypeDef* SPIx, u16 Data)
{
  /* Write in the DR register the data to be sent */
  SPIx->DR = Data;
}

/*******************************************************************************
* Function Name  : SPI_ReceiveData
* Description    : Returns the most recent received data by the SPIx peripheral.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
* Output         : None
* Return         : The value of the received data.
*******************************************************************************/
u16 SPI_ReceiveData(SPI_TypeDef* SPIx)
{
  /* Return the data in the DR register */
  return SPIx->DR;
}

/*******************************************************************************
* Function Name  : SPI_NSSInternalSoftwareConfig
* Description    : Configures internally by software the NSS pin for the selected 
*                  SPI.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
*                  - SPI_NSSInternalSoft: specifies the SPI NSS internal state.
*                    This parameter can be one of the following values:
*                       - SPI_NSSInternalSoft_Set: Set NSS pin internally
*                       - SPI_NSSInternalSoft_Reset: Reset NSS pin internally
* Output         : None
* Return         : None
*******************************************************************************/
void SPI_NSSInternalSoftwareConfig(SPI_TypeDef* SPIx, u16 SPI_NSSInternalSoft)
{
  /* Check the parameters */
  assert(IS_SPI_NSS_INTERNAL(SPI_NSSInternalSoft));

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

/*******************************************************************************
* Function Name  : SPI_SSOutputCmd
* Description    : Enables or disables the SS output for the selected SPI.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
*                  - NewState: new state of the SPIx SS output. 
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void SPI_SSOutputCmd(SPI_TypeDef* SPIx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the selected SPI SS output */
    SPIx->CR2 |= CR2_SSOE_Set;
  }
  else
  {
    /* Disable the selected SPI SS output */
    SPIx->CR2 &= CR2_SSOE_Reset;
  }
}

/*******************************************************************************
* Function Name  : SPI_DataSizeConfig
* Description    : Configures the data size for the selected SPI.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
*                  - SPI_DataSize: specifies the SPI data size.
*                    This parameter can be one of the following values:
*                       - SPI_DataSize_16b: Set data frame format to 16bit
*                       - SPI_DataSize_8b: Set data frame format to 8bit
* Output         : None
* Return         : None
*******************************************************************************/
void SPI_DataSizeConfig(SPI_TypeDef* SPIx, u16 SPI_DataSize)
{
  /* Check the parameters */
  assert(IS_SPI_DATASIZE(SPI_DataSize));

  if (SPI_DataSize != SPI_DataSize_8b)
  {
    /* Set data frame format to 16bit */
    SPIx->CR1 |= SPI_DataSize_16b;
  }
  else
  {
    /* Set data frame format to 8bit */
    SPIx->CR1 &= SPI_DataSize_8b;
  }
}

/*******************************************************************************
* Function Name  : SPI_TransmitCRC
* Description    : Transmit the SPIx CRC value.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
* Output         : None
* Return         : None
*******************************************************************************/
void SPI_TransmitCRC(SPI_TypeDef* SPIx)
{
  /* Enable the selected SPI CRC transmission */
  SPIx->CR1 |= CR1_CRCNext_Set;
}

/*******************************************************************************
* Function Name  : SPI_CalculateCRC
* Description    : Enables or disables the CRC value calculation of the
*                  transfered bytes.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
*                  - NewState: new state of the SPIx CRC value calculation.
*                    This parameter can be: ENABLE or DISABLE.
* Output         : None
* Return         : None
*******************************************************************************/
void SPI_CalculateCRC(SPI_TypeDef* SPIx, FunctionalState NewState)
{
  /* Check the parameters */
  assert(IS_FUNCTIONAL_STATE(NewState));

  if (NewState != DISABLE)
  {
    /* Enable the selected SPI CRC calculation */
    SPIx->CR1 |= CR1_CRCEN_Set;
  }
  else
  {
    /* Disable the selected SPI CRC calculation */
    SPIx->CR1 &= CR1_CRCEN_Reset;
  }
}

/*******************************************************************************
* Function Name  : SPI_GetCRC
* Description    : Returns the transmit or the receive CRC register value for
*                  the specified SPI.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
*                  - SPI_CRC: specifies the CRC register to be read.
*                    This parameter can be one of the following values:
*                       - SPI_CRC_Tx: Selects Tx CRC register
*                       - SPI_CRC_Rx: Selects Rx CRC register
* Output         : None
* Return         : The selected CRC register value..
*******************************************************************************/
u16 SPI_GetCRC(SPI_TypeDef* SPIx, u8 SPI_CRC)
{
  u16 crcreg = 0;

  /* Check the parameters */
  assert(IS_SPI_CRC(SPI_CRC));

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

/*******************************************************************************
* Function Name  : SPI_GetCRCPolynomial
* Description    : Returns the CRC Polynomial register value for the specified SPI.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
* Output         : None
* Return         : The CRC Polynomial register value.
*******************************************************************************/
u16 SPI_GetCRCPolynomial(SPI_TypeDef* SPIx)
{
  /* Return the CRC polynomial register */
  return SPIx->CRCPR;
}

/*******************************************************************************
* Function Name  : SPI_BiDirectionalLineConfig
* Description    : Selects the data transfer direction in bi-directional mode
*                  for the specified SPI.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
*                  - SPI_Direction: specifies the data transfer direction in
*                    bi-directional mode. 
*                    This parameter can be one of the following values:
*                       - SPI_Direction_Tx: Selects Tx transmission direction
*                       - SPI_Direction_Rx: Selects Rx receive direction
* Output         : None
* Return         : None
*******************************************************************************/
void SPI_BiDirectionalLineConfig(SPI_TypeDef* SPIx, u16 SPI_Direction)
{
  /* Check the parameters */
  assert(IS_SPI_DIRECTION(SPI_Direction));

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

/*******************************************************************************
* Function Name  : SPI_GetFlagStatus
* Description    : Checks whether the specified SPI flag is set or not.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
*                  - SPI_FLAG: specifies the flag to check. 
*                    This parameter can be one of the following values:
*                       - SPI_FLAG_BSY: Busy flag.
*                       - SPI_FLAG_OVR: Overrun flag.
*                       - SPI_FLAG_MODF: Mode Fault flag.
*                       - SPI_FLAG_CRCERR: CRC Error flag.
*                       - SPI_FLAG_TXE: Transmit buffer empty flag.
*                       - SPI_FLAG_RXNE: Receive buffer not empty flag.
* Output         : None
* Return         : The new state of SPI_FLAG (SET or RESET).
*******************************************************************************/
FlagStatus SPI_GetFlagStatus(SPI_TypeDef* SPIx, u16 SPI_FLAG)
{
  FlagStatus bitstatus = RESET;

  /* Check the parameters */
  assert(IS_SPI_GET_FLAG(SPI_FLAG));

  /* Check the status of the specified SPI flag */
  if ((SPIx->SR & SPI_FLAG) != (u16)RESET)
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

/*******************************************************************************
* Function Name  : SPI_ClearFlag
* Description    : Clears the SPIx's pending flags.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
*                  - SPI_FLAG: specifies the flag to clear. 
*                    This parameter can be any combination of the following values:
*                       - SPI_FLAG_OVR: Overrun flag.
*                       - SPI_FLAG_MODF: Mode Fault flag.
*                       - SPI_FLAG_CRCERR: CRC Error flag.
* Output         : None
* Return         : None
*******************************************************************************/
void SPI_ClearFlag(SPI_TypeDef* SPIx, u16 SPI_FLAG)
{
  /* Check the parameters */
  assert(IS_SPI_CLEAR_FLAG(SPI_FLAG));
    
  /* SPI_FLAG_MODF flag clear */
  if(SPI_FLAG == SPI_FLAG_MODF)
  {
    /* Read SR register */
    (void)SPIx->SR;
    /* Write on CR1 register */
    SPIx->CR1 |= CR1_SPE_Set; 
  }
  /* SPI_FLAG_OVR flag clear */
  else if(SPI_FLAG == SPI_FLAG_OVR)  
  {
    /* Read SR register */
    (void)SPIx->SR;
  }
  else /* SPI_FLAG_CRCERR flag clear */
  {
    /* Clear the selected SPI flag */
    SPIx->SR &= (u16)~SPI_FLAG;
  }
}

/*******************************************************************************
* Function Name  : SPI_GetITStatus
* Description    : Checks whether the specified SPI interrupt has occurred or not.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
*                  - SPI_IT: specifies the SPI interrupt source to check. 
*                    This parameter can be one of the following values:
*                       - SPI_IT_OVR: Overrun interrupt.
*                       - SPI_IT_MODF: Mode Fault interrupt.
*                       - SPI_IT_CRCERR: CRC Error interrupt.
*                       - SPI_IT_TXE: Transmit buffer empty interrupt.
*                       - SPI_IT_RXNE: Receive buffer not empty interrupt.
* Output         : None
* Return         : The new state of SPI_IT (SET or RESET).
*******************************************************************************/
ITStatus SPI_GetITStatus(SPI_TypeDef* SPIx, u8 SPI_IT)
{
  ITStatus bitstatus = RESET;
  u16 itpos = 0, itmask = 0, enablestatus = 0;

  /* Check the parameters */
  assert(IS_SPI_GET_IT(SPI_IT));

  /* Get the SPI IT index */
  itpos = (u16)((u16)0x01 << (SPI_IT & (u8)0x0F));

  /* Get the SPI IT index */
  itmask = SPI_IT >> 4;
  /* Set the IT mask */
  itmask = (u16)((u16)0x01 << itmask);
  /* Get the SPI_IT enable bit status */
  enablestatus = (SPIx->CR2 & itmask) ;

  /* Check the status of the specified SPI interrupt */
  if (((SPIx->SR & itpos) != (u16)RESET) && enablestatus)
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

/*******************************************************************************
* Function Name  : SPI_ClearITPendingBit
* Description    : Clears the SPI’s interrupt pending bits.
* Input          : - SPIx: where x can be 1 or 2 to select the SPI peripheral.
*                  - SPI_IT: specifies the SPI interrupt pending bit to clear.
*                    This parameter can be one of the following values:
*                       - SPI_IT_OVR: Overrun interrupt.
*                       - SPI_IT_MODF: Mode Fault interrupt.
*                       - SPI_IT_CRCERR: CRC Error interrupt.
* Output         : None
* Return         : None
*******************************************************************************/
void SPI_ClearITPendingBit(SPI_TypeDef* SPIx, u8 SPI_IT)
{
  u16 itpos = 0;

  /* Check the parameters */
  assert(IS_SPI_CLEAR_IT(SPI_IT));

  /* SPI_IT_MODF pending bit clear */
  if(SPI_IT == SPI_IT_MODF)
  {
    /* Read SR register */
    (void)SPIx->SR;
    /* Write on CR1 register */
    SPIx->CR1 |= CR1_SPE_Set; 
  }
  else if(SPI_IT == SPI_IT_OVR)   /* SPI_IT_OVR pending bit clear */ 
  {
    /* Read SR register */
    (void)(SPIx->SR);
  }
  else   /* SPI_IT_CRCERR pending bit clear */
  {
    /* Get the SPI IT index */
    itpos = (u16)((u16)0x01 << (SPI_IT & (u8)0x0F));
    /* Clear the selected SPI interrupt pending bits */
    SPIx->SR &= (u16)~itpos;
  }
}

/******************* (C) COPYRIGHT 2007 STMicroelectronics *****END OF FILE****/
