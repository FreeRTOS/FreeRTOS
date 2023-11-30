/****************************************************************************//**
 * @file     usci_spi.c
 * @version  V3.00
 * @brief    M2351 series USCI_SPI driver source file
 *
 * @copyright (C) 2016 Nuvoton Technology Corp. All rights reserved.
*****************************************************************************/
#include "NuMicro.h"

/** @addtogroup Standard_Driver Standard Driver
  @{
*/

/** @addtogroup USCI_SPI_Driver USCI_SPI Driver
  @{
*/


/** @addtogroup USCI_SPI_EXPORTED_FUNCTIONS USCI_SPI Exported Functions
  @{
*/

/**
  * @brief  This function make USCI_SPI module be ready to transfer.
  *         By default, the USCI_SPI transfer sequence is MSB first, the slave selection
  *         signal is active low and the automatic slave select function is disabled. In
  *         Slave mode, the u32BusClock must be NULL and the USCI_SPI clock
  *         divider setting will be 0.
  * @param[in]  uspi The pointer of the specified USCI_SPI module.
  * @param[in]  u32MasterSlave Decide the USCI_SPI module is operating in master mode or in slave mode. Valid values are:
  *                    - \ref USPI_SLAVE
  *                    - \ref USPI_MASTER
  * @param[in]  u32SPIMode Decide the transfer timing. Valid values are:
  *                    - \ref USPI_MODE_0
  *                    - \ref USPI_MODE_1
  *                    - \ref USPI_MODE_2
  *                    - \ref USPI_MODE_3
  * @param[in]  u32DataWidth The data width of a USCI_SPI transaction.
  * @param[in]  u32BusClock The expected frequency of USCI_SPI bus clock in Hz.
  * @return Actual frequency of USCI_SPI peripheral clock.
  */
uint32_t USPI_Open(USPI_T *uspi, uint32_t u32MasterSlave, uint32_t u32SPIMode,  uint32_t u32DataWidth, uint32_t u32BusClock)
{
    uint32_t u32ClkDiv = 0UL;
    uint32_t u32Pclk;
    uint32_t u32RetValue = 0UL;

    if((uspi == USPI0) || (uspi == USPI0_NS))
    {
        u32Pclk = CLK_GetPCLK0Freq();
    }
    else
    {
        u32Pclk = CLK_GetPCLK1Freq();
    }

    if(u32BusClock != 0UL)
    {
        u32ClkDiv = (uint32_t)((((((u32Pclk / 2UL) * 10UL) / (u32BusClock)) + 5UL) / 10UL) - 1UL); /* Compute proper divider for USCI_SPI clock */
    }

    /* Enable USCI_SPI protocol */
    uspi->CTL &= ~USPI_CTL_FUNMODE_Msk;
    uspi->CTL = 1UL << USPI_CTL_FUNMODE_Pos;

    /* Data format configuration */
    if(u32DataWidth == 16UL)
    {
        u32DataWidth = 0UL;
    }
    uspi->LINECTL &= ~USPI_LINECTL_DWIDTH_Msk;
    uspi->LINECTL |= (u32DataWidth << USPI_LINECTL_DWIDTH_Pos);

    /* MSB data format */
    uspi->LINECTL &= ~USPI_LINECTL_LSB_Msk;

    /* Set slave selection signal active low */
    if(u32MasterSlave == USPI_MASTER)
    {
        uspi->LINECTL |= USPI_LINECTL_CTLOINV_Msk;
    }
    else
    {
        uspi->CTLIN0 |= USPI_CTLIN0_ININV_Msk;
    }

    /* Set operating mode and transfer timing */
    uspi->PROTCTL &= ~(USPI_PROTCTL_SCLKMODE_Msk | USPI_PROTCTL_AUTOSS_Msk | USPI_PROTCTL_SLAVE_Msk);
    uspi->PROTCTL |= (u32MasterSlave | u32SPIMode);

    /* Set USCI_SPI bus clock */
    uspi->BRGEN &= ~USPI_BRGEN_CLKDIV_Msk;
    uspi->BRGEN |= (u32ClkDiv << USPI_BRGEN_CLKDIV_Pos);
    uspi->PROTCTL |=  USPI_PROTCTL_PROTEN_Msk;

    if(u32BusClock != 0UL)
    {
        u32RetValue = (u32Pclk / ((u32ClkDiv + 1UL) << 1UL));
    }
    else
    {
        u32RetValue = 0UL;
    }

    return u32RetValue;
}

/**
  * @brief Disable USCI_SPI function mode.
  * @param[in]  uspi The pointer of the specified USCI_SPI module.
  * @return None
  */
void USPI_Close(USPI_T *uspi)
{
    uspi->CTL &= ~USPI_CTL_FUNMODE_Msk;
}

/**
  * @brief Clear Rx buffer.
  * @param[in]  uspi The pointer of the specified USCI_SPI module.
  * @return None
  */
void USPI_ClearRxBuf(USPI_T *uspi)
{
    uspi->BUFCTL |= USPI_BUFCTL_RXCLR_Msk;
}

/**
  * @brief Clear Tx buffer.
  * @param[in]  uspi The pointer of the specified USCI_SPI module.
  * @return None
  */
void USPI_ClearTxBuf(USPI_T *uspi)
{
    uspi->BUFCTL |= USPI_BUFCTL_TXCLR_Msk;
}

/**
  * @brief Disable the automatic slave select function.
  * @param[in]  uspi The pointer of the specified USCI_SPI module.
  * @return None
  */
void USPI_DisableAutoSS(USPI_T *uspi)
{
    uspi->PROTCTL &= ~(USPI_PROTCTL_AUTOSS_Msk | USPI_PROTCTL_SS_Msk);
}

/**
  * @brief Enable the automatic slave select function. Only available in Master mode.
  * @param[in]  uspi The pointer of the specified USCI_SPI module.
  * @param[in]  u32SSPinMask This parameter is not used.
  * @param[in]  u32ActiveLevel The active level of slave select signal. Valid values are:
  *                     - \ref USPI_SS_ACTIVE_HIGH
  *                     - \ref USPI_SS_ACTIVE_LOW
  * @return None
  */
void USPI_EnableAutoSS(USPI_T *uspi, uint32_t u32SSPinMask, uint32_t u32ActiveLevel)
{
    uspi->LINECTL = (uspi->LINECTL & ~USPI_LINECTL_CTLOINV_Msk) | u32ActiveLevel;
    uspi->PROTCTL |= USPI_PROTCTL_AUTOSS_Msk;
}

/**
  * @brief Set the USCI_SPI bus clock. Only available in Master mode.
  * @param[in]  uspi The pointer of the specified USCI_SPI module.
  * @param[in]  u32BusClock The expected frequency of USCI_SPI bus clock.
  * @return Actual frequency of USCI_SPI peripheral clock.
  */
uint32_t USPI_SetBusClock(USPI_T *uspi, uint32_t u32BusClock)
{
    uint32_t u32ClkDiv;
    uint32_t u32Pclk;

    if((uspi == USPI0) || (uspi == USPI0_NS))
    {
        u32Pclk = CLK_GetPCLK0Freq();
    }
    else
    {
        u32Pclk = CLK_GetPCLK1Freq();
    }

    u32ClkDiv = (uint32_t)((((((u32Pclk / 2UL) * 10UL) / (u32BusClock)) + 5UL) / 10UL) - 1UL); /* Compute proper divider for USCI_SPI clock */

    /* Set USCI_SPI bus clock */
    uspi->BRGEN &= ~USPI_BRGEN_CLKDIV_Msk;
    uspi->BRGEN |= (u32ClkDiv << USPI_BRGEN_CLKDIV_Pos);

    return (u32Pclk / ((u32ClkDiv + 1UL) << 1UL));
}

/**
  * @brief Get the actual frequency of USCI_SPI bus clock. Only available in Master mode.
  * @param[in]  uspi The pointer of the specified USCI_SPI module.
  * @return Actual USCI_SPI bus clock frequency.
  */
uint32_t USPI_GetBusClock(USPI_T *uspi)
{
    uint32_t u32ClkDiv, u32BusClk;

    u32ClkDiv = (uspi->BRGEN & USPI_BRGEN_CLKDIV_Msk) >> USPI_BRGEN_CLKDIV_Pos;

    if((uspi == USPI0) || (uspi == USPI0_NS))
    {
        u32BusClk = (CLK_GetPCLK0Freq() / ((u32ClkDiv + 1UL) << 1UL));
    }
    else
    {
        u32BusClk = (CLK_GetPCLK1Freq() / ((u32ClkDiv + 1UL) << 1UL));
    }

    return u32BusClk;
}

/**
  * @brief Enable related interrupts specified by u32Mask parameter.
  * @param[in]  uspi The pointer of the specified USCI_SPI module.
  * @param[in]  u32Mask The combination of all related interrupt enable bits.
  *         Each bit corresponds to a interrupt bit.
  *         This parameter decides which interrupts will be enabled. Valid values are:
  *           - \ref USPI_SSINACT_INT_MASK
  *           - \ref USPI_SSACT_INT_MASK
  *           - \ref USPI_SLVTO_INT_MASK
  *           - \ref USPI_SLVBE_INT_MASK
  *           - \ref USPI_TXUDR_INT_MASK
  *           - \ref USPI_RXOV_INT_MASK
  *           - \ref USPI_TXST_INT_MASK
  *           - \ref USPI_TXEND_INT_MASK
  *           - \ref USPI_RXST_INT_MASK
  *           - \ref USPI_RXEND_INT_MASK
  * @return None
  */
void USPI_EnableInt(USPI_T *uspi, uint32_t u32Mask)
{
    /* Enable slave selection signal inactive interrupt flag */
    if((u32Mask & USPI_SSINACT_INT_MASK) == USPI_SSINACT_INT_MASK)
    {
        uspi->PROTIEN |= USPI_PROTIEN_SSINAIEN_Msk;
    }

    /* Enable slave selection signal active interrupt flag */
    if((u32Mask & USPI_SSACT_INT_MASK) == USPI_SSACT_INT_MASK)
    {
        uspi->PROTIEN |= USPI_PROTIEN_SSACTIEN_Msk;
    }

    /* Enable slave time-out interrupt flag */
    if((u32Mask & USPI_SLVTO_INT_MASK) == USPI_SLVTO_INT_MASK)
    {
        uspi->PROTIEN |= USPI_PROTIEN_SLVTOIEN_Msk;
    }

    /* Enable slave bit count error interrupt flag */
    if((u32Mask & USPI_SLVBE_INT_MASK) == USPI_SLVBE_INT_MASK)
    {
        uspi->PROTIEN |= USPI_PROTIEN_SLVBEIEN_Msk;
    }

    /* Enable TX under run interrupt flag */
    if((u32Mask & USPI_TXUDR_INT_MASK) == USPI_TXUDR_INT_MASK)
    {
        uspi->BUFCTL |= USPI_BUFCTL_TXUDRIEN_Msk;
    }

    /* Enable RX overrun interrupt flag */
    if((u32Mask & USPI_RXOV_INT_MASK) == USPI_RXOV_INT_MASK)
    {
        uspi->BUFCTL |= USPI_BUFCTL_RXOVIEN_Msk;
    }

    /* Enable TX start interrupt flag */
    if((u32Mask & USPI_TXST_INT_MASK) == USPI_TXST_INT_MASK)
    {
        uspi->INTEN |= USPI_INTEN_TXSTIEN_Msk;
    }

    /* Enable TX end interrupt flag */
    if((u32Mask & USPI_TXEND_INT_MASK) == USPI_TXEND_INT_MASK)
    {
        uspi->INTEN |= USPI_INTEN_TXENDIEN_Msk;
    }

    /* Enable RX start interrupt flag */
    if((u32Mask & USPI_RXST_INT_MASK) == USPI_RXST_INT_MASK)
    {
        uspi->INTEN |= USPI_INTEN_RXSTIEN_Msk;
    }

    /* Enable RX end interrupt flag */
    if((u32Mask & USPI_RXEND_INT_MASK) == USPI_RXEND_INT_MASK)
    {
        uspi->INTEN |= USPI_INTEN_RXENDIEN_Msk;
    }
}

/**
  * @brief Disable related interrupts specified by u32Mask parameter.
  * @param[in]  uspi The pointer of the specified USCI_SPI module.
  * @param[in]  u32Mask The combination of all related interrupt enable bits.
  *         Each bit corresponds to a interrupt bit.
  *         This parameter decides which interrupts will be disabled. Valid values are:
  *           - \ref USPI_SSINACT_INT_MASK
  *           - \ref USPI_SSACT_INT_MASK
  *           - \ref USPI_SLVTO_INT_MASK
  *           - \ref USPI_SLVBE_INT_MASK
  *           - \ref USPI_TXUDR_INT_MASK
  *           - \ref USPI_RXOV_INT_MASK
  *           - \ref USPI_TXST_INT_MASK
  *           - \ref USPI_TXEND_INT_MASK
  *           - \ref USPI_RXST_INT_MASK
  *           - \ref USPI_RXEND_INT_MASK
  * @return None
  */
void USPI_DisableInt(USPI_T *uspi, uint32_t u32Mask)
{
    /* Disable slave selection signal inactive interrupt flag */
    if((u32Mask & USPI_SSINACT_INT_MASK) == USPI_SSINACT_INT_MASK)
    {
        uspi->PROTIEN &= ~USPI_PROTIEN_SSINAIEN_Msk;
    }

    /* Disable slave selection signal active interrupt flag */
    if((u32Mask & USPI_SSACT_INT_MASK) == USPI_SSACT_INT_MASK)
    {
        uspi->PROTIEN &= ~USPI_PROTIEN_SSACTIEN_Msk;
    }

    /* Disable slave time-out interrupt flag */
    if((u32Mask & USPI_SLVTO_INT_MASK) == USPI_SLVTO_INT_MASK)
    {
        uspi->PROTIEN &= ~USPI_PROTIEN_SLVTOIEN_Msk;
    }

    /* Disable slave bit count error interrupt flag */
    if((u32Mask & USPI_SLVBE_INT_MASK) == USPI_SLVBE_INT_MASK)
    {
        uspi->PROTIEN &= ~USPI_PROTIEN_SLVBEIEN_Msk;
    }

    /* Disable TX under run interrupt flag */
    if((u32Mask & USPI_TXUDR_INT_MASK) == USPI_TXUDR_INT_MASK)
    {
        uspi->BUFCTL &= ~USPI_BUFCTL_TXUDRIEN_Msk;
    }

    /* Disable RX overrun interrupt flag */
    if((u32Mask & USPI_RXOV_INT_MASK) == USPI_RXOV_INT_MASK)
    {
        uspi->BUFCTL &= ~USPI_BUFCTL_RXOVIEN_Msk;
    }

    /* Disable TX start interrupt flag */
    if((u32Mask & USPI_TXST_INT_MASK) == USPI_TXST_INT_MASK)
    {
        uspi->INTEN &= ~USPI_INTEN_TXSTIEN_Msk;
    }

    /* Disable TX end interrupt flag */
    if((u32Mask & USPI_TXEND_INT_MASK) == USPI_TXEND_INT_MASK)
    {
        uspi->INTEN &= ~USPI_INTEN_TXENDIEN_Msk;
    }

    /* Disable RX start interrupt flag */
    if((u32Mask & USPI_RXST_INT_MASK) == USPI_RXST_INT_MASK)
    {
        uspi->INTEN &= ~USPI_INTEN_RXSTIEN_Msk;
    }

    /* Disable RX end interrupt flag */
    if((u32Mask & USPI_RXEND_INT_MASK) == USPI_RXEND_INT_MASK)
    {
        uspi->INTEN &= ~USPI_INTEN_RXENDIEN_Msk;
    }
}

/**
  * @brief  Get interrupt flag.
  * @param[in]  uspi The pointer of the specified USCI_SPI module.
  * @param[in]  u32Mask The combination of all related interrupt sources.
  *         Each bit corresponds to a interrupt source.
  *         This parameter decides which interrupt flags will be read. It is combination of:
  *           - \ref USPI_SSINACT_INT_MASK
  *           - \ref USPI_SSACT_INT_MASK
  *           - \ref USPI_SLVTO_INT_MASK
  *           - \ref USPI_SLVBE_INT_MASK
  *           - \ref USPI_TXUDR_INT_MASK
  *           - \ref USPI_RXOV_INT_MASK
  *           - \ref USPI_TXST_INT_MASK
  *           - \ref USPI_TXEND_INT_MASK
  *           - \ref USPI_RXST_INT_MASK
  *           - \ref USPI_RXEND_INT_MASK
  * @return Interrupt flags of selected sources.
  */
uint32_t USPI_GetIntFlag(USPI_T *uspi, uint32_t u32Mask)
{
    uint32_t u32ProtStatus, u32BufStatus;
    uint32_t u32IntFlag = 0UL;

    u32ProtStatus = uspi->PROTSTS;
    u32BufStatus = uspi->BUFSTS;

    /* Check slave selection signal inactive interrupt flag */
    if((u32Mask & USPI_SSINACT_INT_MASK) && (u32ProtStatus & USPI_PROTSTS_SSINAIF_Msk))
    {
        u32IntFlag |= USPI_SSINACT_INT_MASK;
    }

    /* Check slave selection signal active interrupt flag */
    if((u32Mask & USPI_SSACT_INT_MASK) && (u32ProtStatus & USPI_PROTSTS_SSACTIF_Msk))
    {
        u32IntFlag |= USPI_SSACT_INT_MASK;
    }

    /* Check slave time-out interrupt flag */
    if((u32Mask & USPI_SLVTO_INT_MASK) && (u32ProtStatus & USPI_PROTSTS_SLVTOIF_Msk))
    {
        u32IntFlag |= USPI_SLVTO_INT_MASK;
    }

    /* Check slave bit count error interrupt flag */
    if((u32Mask & USPI_SLVBE_INT_MASK) && (u32ProtStatus & USPI_PROTSTS_SLVBEIF_Msk))
    {
        u32IntFlag |= USPI_SLVBE_INT_MASK;
    }

    /* Check TX under run interrupt flag */
    if((u32Mask & USPI_TXUDR_INT_MASK) && (u32BufStatus & USPI_BUFSTS_TXUDRIF_Msk))
    {
        u32IntFlag |= USPI_TXUDR_INT_MASK;
    }

    /* Check RX overrun interrupt flag */
    if((u32Mask & USPI_RXOV_INT_MASK) && (u32BufStatus & USPI_BUFSTS_RXOVIF_Msk))
    {
        u32IntFlag |= USPI_RXOV_INT_MASK;
    }

    /* Check TX start interrupt flag */
    if((u32Mask & USPI_TXST_INT_MASK) && (u32ProtStatus & USPI_PROTSTS_TXSTIF_Msk))
    {
        u32IntFlag |= USPI_TXST_INT_MASK;
    }

    /* Check TX end interrupt flag */
    if((u32Mask & USPI_TXEND_INT_MASK) && (u32ProtStatus & USPI_PROTSTS_TXENDIF_Msk))
    {
        u32IntFlag |= USPI_TXEND_INT_MASK;
    }

    /* Check RX start interrupt flag */
    if((u32Mask & USPI_RXST_INT_MASK) && (u32ProtStatus & USPI_PROTSTS_RXSTIF_Msk))
    {
        u32IntFlag |= USPI_RXST_INT_MASK;
    }

    /* Check RX end interrupt flag */
    if((u32Mask & USPI_RXEND_INT_MASK) && (u32ProtStatus & USPI_PROTSTS_RXENDIF_Msk))
    {
        u32IntFlag |= USPI_RXEND_INT_MASK;
    }

    return u32IntFlag;
}

/**
  * @brief  Clear interrupt flag.
  * @param[in]  uspi The pointer of the specified USCI_SPI module.
  * @param[in]  u32Mask The combination of all related interrupt sources.
  *         Each bit corresponds to a interrupt source.
  *         This parameter decides which interrupt flags will be cleared. It could be the combination of:
  *           - \ref USPI_SSINACT_INT_MASK
  *           - \ref USPI_SSACT_INT_MASK
  *           - \ref USPI_SLVTO_INT_MASK
  *           - \ref USPI_SLVBE_INT_MASK
  *           - \ref USPI_TXUDR_INT_MASK
  *           - \ref USPI_RXOV_INT_MASK
  *           - \ref USPI_TXST_INT_MASK
  *           - \ref USPI_TXEND_INT_MASK
  *           - \ref USPI_RXST_INT_MASK
  *           - \ref USPI_RXEND_INT_MASK
  * @return None
  */
void USPI_ClearIntFlag(USPI_T *uspi, uint32_t u32Mask)
{
    /* Clear slave selection signal inactive interrupt flag */
    if(u32Mask & USPI_SSINACT_INT_MASK)
    {
        uspi->PROTSTS = USPI_PROTSTS_SSINAIF_Msk;
    }

    /* Clear slave selection signal active interrupt flag */
    if(u32Mask & USPI_SSACT_INT_MASK)
    {
        uspi->PROTSTS = USPI_PROTSTS_SSACTIF_Msk;
    }

    /* Clear slave time-out interrupt flag */
    if(u32Mask & USPI_SLVTO_INT_MASK)
    {
        uspi->PROTSTS = USPI_PROTSTS_SLVTOIF_Msk;
    }

    /* Clear slave bit count error interrupt flag */
    if(u32Mask & USPI_SLVBE_INT_MASK)
    {
        uspi->PROTSTS = USPI_PROTSTS_SLVBEIF_Msk;
    }

    /* Clear TX under run interrupt flag */
    if(u32Mask & USPI_TXUDR_INT_MASK)
    {
        uspi->BUFSTS = USPI_BUFSTS_TXUDRIF_Msk;
    }

    /* Clear RX overrun interrupt flag */
    if(u32Mask & USPI_RXOV_INT_MASK)
    {
        uspi->BUFSTS = USPI_BUFSTS_RXOVIF_Msk;
    }

    /* Clear TX start interrupt flag */
    if(u32Mask & USPI_TXST_INT_MASK)
    {
        uspi->PROTSTS = USPI_PROTSTS_TXSTIF_Msk;
    }

    /* Clear TX end interrupt flag */
    if(u32Mask & USPI_TXEND_INT_MASK)
    {
        uspi->PROTSTS = USPI_PROTSTS_TXENDIF_Msk;
    }

    /* Clear RX start interrupt flag */
    if(u32Mask & USPI_RXST_INT_MASK)
    {
        uspi->PROTSTS = USPI_PROTSTS_RXSTIF_Msk;
    }

    /* Clear RX end interrupt flag */
    if(u32Mask & USPI_RXEND_INT_MASK)
    {
        uspi->PROTSTS = USPI_PROTSTS_RXENDIF_Msk;
    }
}

/**
  * @brief  Get USCI_SPI status.
  * @param[in]  uspi The pointer of the specified USCI_SPI module.
  * @param[in]  u32Mask The combination of all related sources.
  *         Each bit corresponds to a source.
  *         This parameter decides which flags will be read. It is combination of:
  *           - \ref USPI_BUSY_MASK
  *           - \ref USPI_RX_EMPTY_MASK
  *           - \ref USPI_RX_FULL_MASK
  *           - \ref USPI_TX_EMPTY_MASK
  *           - \ref USPI_TX_FULL_MASK
  *           - \ref USPI_SSLINE_STS_MASK
  * @return Flags of selected sources.
  */
uint32_t USPI_GetStatus(USPI_T *uspi, uint32_t u32Mask)
{
    uint32_t u32ProtStatus, u32BufStatus;
    uint32_t u32Flag = 0UL;

    u32ProtStatus = uspi->PROTSTS;
    u32BufStatus = uspi->BUFSTS;

    /* Check busy status */
    if((u32Mask & USPI_BUSY_MASK) && (u32ProtStatus & USPI_PROTSTS_BUSY_Msk))
    {
        u32Flag |= USPI_BUSY_MASK;
    }

    /* Check RX empty flag */
    if((u32Mask & USPI_RX_EMPTY_MASK) && (u32BufStatus & USPI_BUFSTS_RXEMPTY_Msk))
    {
        u32Flag |= USPI_RX_EMPTY_MASK;
    }

    /* Check RX full flag */
    if((u32Mask & USPI_RX_FULL_MASK) && (u32BufStatus & USPI_BUFSTS_RXFULL_Msk))
    {
        u32Flag |= USPI_RX_FULL_MASK;
    }

    /* Check TX empty flag */
    if((u32Mask & USPI_TX_EMPTY_MASK) && (u32BufStatus & USPI_BUFSTS_TXEMPTY_Msk))
    {
        u32Flag |= USPI_TX_EMPTY_MASK;
    }

    /* Check TX full flag */
    if((u32Mask & USPI_TX_FULL_MASK) && (u32BufStatus & USPI_BUFSTS_TXFULL_Msk))
    {
        u32Flag |= USPI_TX_FULL_MASK;
    }

    /* Check USCI_SPI_SS line status */
    if((u32Mask & USPI_SSLINE_STS_MASK) && (u32ProtStatus & USPI_PROTSTS_SSLINE_Msk))
    {
        u32Flag |= USPI_SSLINE_STS_MASK;
    }

    return u32Flag;
}

/**
  * @brief  Enable USCI_SPI Wake-up Function.
  * @param[in]  uspi The pointer of the specified USCI_SPI module.
  * @return None
  */
void USPI_EnableWakeup(USPI_T *uspi)
{
    uspi->WKCTL |= USPI_WKCTL_WKEN_Msk;
}

/**
  * @brief  Disable USCI_SPI Wake-up Function.
  * @param[in]  uspi The pointer of the specified USCI_SPI module.
  * @return None
  */
void USPI_DisableWakeup(USPI_T *uspi)
{
    uspi->WKCTL &= ~USPI_WKCTL_WKEN_Msk;
}

/*@}*/ /* end of group USCI_SPI_EXPORTED_FUNCTIONS */

/*@}*/ /* end of group USCI_SPI_Driver */

/*@}*/ /* end of group Standard_Driver */

/*** (C) COPYRIGHT 2016 Nuvoton Technology Corp. ***/
