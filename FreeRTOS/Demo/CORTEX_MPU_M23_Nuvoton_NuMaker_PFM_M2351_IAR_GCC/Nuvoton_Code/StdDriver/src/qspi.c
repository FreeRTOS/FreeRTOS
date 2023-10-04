/**************************************************************************//**
 * @file     qspi.c
 * @version  V3.00
 * @brief    M2351 series QSPI driver source file
 *
 * @copyright (C) 2017 Nuvoton Technology Corp. All rights reserved.
 *****************************************************************************/
#include "NuMicro.h"

/** @addtogroup Standard_Driver Standard Driver
 * @{
 */

/** @addtogroup QSPI_Driver QSPI Driver
 * @{
 */


/** @addtogroup QSPI_EXPORTED_FUNCTIONS QSPI Exported Functions
 * @{
 */

/**
 * @brief  This function make QSPI module be ready to transfer.
 * @param[in]  qspi The pointer of the specified QSPI module.
 * @param[in]  u32MasterSlave Decides the QSPI module is operating in master mode or in slave mode. (QSPI_SLAVE, QSPI_MASTER)
 * @param[in]  u32QSPIMode Decides the transfer timing. (QSPI_MODE_0, QSPI_MODE_1, QSPI_MODE_2, QSPI_MODE_3)
 * @param[in]  u32DataWidth Decides the data width of a QSPI transaction.
 * @param[in]  u32BusClock The expected frequency of QSPI bus clock in Hz.
 * @return Actual frequency of QSPI peripheral clock.
 * @details By default, the QSPI transfer sequence is MSB first, the slave selection signal is active low and the automatic
 *          slave selection function is disabled.
 *          In Slave mode, the u32BusClock shall be NULL and the QSPI clock divider setting will be 0.
 *          The actual clock rate may be different from the target QSPI clock rate.
 *          For example, if the QSPI source clock rate is 12 MHz and the target QSPI bus clock rate is 7 MHz, the
 *          actual QSPI clock rate will be 6MHz.
 * @note   If u32BusClock = 0, DIVIDER setting will be set to the maximum value.
 * @note   If u32BusClock >= system clock frequency for Secure, QSPI peripheral clock source will be set to APB clock and DIVIDER will be set to 0.
 * @note   If u32BusClock >= system clock frequency for Non-Secure, this function does not do anything to avoid the situation that the frequency of
 *         QSPI bus clock cannot be faster than the system clock rate. User should set up carefully.
 * @note   If u32BusClock >= QSPI peripheral clock source, DIVIDER will be set to 0.
 * @note   In slave mode for Secure, the QSPI peripheral clock rate will equal to APB clock rate.
 * @note   In slave mode for Non-Secure, the QSPI peripheral clock rate will equal to the clock rate set in secure mode.
 */
uint32_t QSPI_Open( QSPI_T * qspi,
                    uint32_t u32MasterSlave,
                    uint32_t u32QSPIMode,
                    uint32_t u32DataWidth,
                    uint32_t u32BusClock )
{
    uint32_t u32ClkSrc = 0UL, u32Div, u32HCLKFreq, u32PCLK0Freq, u32RetValue = 0UL;

    if( u32DataWidth == 32UL )
    {
        u32DataWidth = 0UL;
    }

    /* Get system clock frequency */
    u32HCLKFreq = CLK_GetHCLKFreq();
    /* Get APB0 clock frequency */
    u32PCLK0Freq = CLK_GetPCLK0Freq();

    if( u32MasterSlave == QSPI_MASTER )
    {
        /* Default setting: slave selection signal is active low; disable automatic slave selection function. */
        qspi->SSCTL = QSPI_SS_ACTIVE_LOW;

        /* Default setting: MSB first, disable unit transfer interrupt, SP_CYCLE = 0. */
        qspi->CTL = u32MasterSlave | ( u32DataWidth << QSPI_CTL_DWIDTH_Pos ) | ( u32QSPIMode ) | QSPI_CTL_SPIEN_Msk;

        if( u32BusClock >= u32HCLKFreq )
        {
            if( !( __PC() & ( 1UL << 28UL ) ) )
            {
                /* Select PCLK as the clock source of QSPI */
                if( ( qspi == QSPI0 ) || ( qspi == QSPI0_NS ) )
                {
                    CLK->CLKSEL2 = ( CLK->CLKSEL2 & ( ~CLK_CLKSEL2_QSPI0SEL_Msk ) ) | CLK_CLKSEL2_QSPI0SEL_PCLK0;
                }
            }
        }

        /* Check clock source of QSPI */
        if( ( qspi == QSPI0 ) || ( qspi == QSPI0_NS ) )
        {
            if( ( CLK_GetModuleClockSource( QSPI0_MODULE ) << CLK_CLKSEL2_QSPI0SEL_Pos ) == CLK_CLKSEL2_QSPI0SEL_HXT )
            {
                u32ClkSrc = __HXT; /* Clock source is HXT */
            }
            else if( ( CLK_GetModuleClockSource( QSPI0_MODULE ) << CLK_CLKSEL2_QSPI0SEL_Pos ) == CLK_CLKSEL2_QSPI0SEL_PLL )
            {
                u32ClkSrc = CLK_GetPLLClockFreq(); /* Clock source is PLL */
            }
            else if( ( CLK_GetModuleClockSource( QSPI0_MODULE ) << CLK_CLKSEL2_QSPI0SEL_Pos ) == CLK_CLKSEL2_QSPI0SEL_PCLK0 )
            {
                u32ClkSrc = CLK_GetPCLK0Freq(); /* Clock source is PCLK0 */
            }
            else
            {
                u32ClkSrc = __HIRC; /* Clock source is HIRC */
            }
        }

        if( u32BusClock >= u32HCLKFreq )
        {
            /* Set DIVIDER = 0 */
            qspi->CLKDIV = 0UL;
            /* Return master peripheral clock rate */
            u32RetValue = u32ClkSrc;
        }
        else if( u32BusClock >= u32ClkSrc )
        {
            /* Set DIVIDER = 0 */
            qspi->CLKDIV = 0UL;
            /* Return master peripheral clock rate */
            u32RetValue = u32ClkSrc;
        }
        else if( u32BusClock == 0UL )
        {
            /* Set DIVIDER to the maximum value 0x1FF. f_spi = f_spi_clk_src / (DIVIDER + 1) */
            qspi->CLKDIV |= QSPI_CLKDIV_DIVIDER_Msk;
            /* Return master peripheral clock rate */
            u32RetValue = ( u32ClkSrc / ( 0x1FFUL + 1UL ) );
        }
        else
        {
            u32Div = ( ( ( u32ClkSrc * 10UL ) / u32BusClock + 5UL ) / 10UL ) - 1UL; /* Round to the nearest integer */

            if( u32Div > 0x1FFUL )
            {
                u32Div = 0x1FFUL;
                qspi->CLKDIV |= QSPI_CLKDIV_DIVIDER_Msk;
                /* Return master peripheral clock rate */
                u32RetValue = ( u32ClkSrc / ( 0x1FFUL + 1UL ) );
            }
            else
            {
                qspi->CLKDIV = ( qspi->CLKDIV & ( ~QSPI_CLKDIV_DIVIDER_Msk ) ) | ( u32Div << QSPI_CLKDIV_DIVIDER_Pos );
                /* Return master peripheral clock rate */
                u32RetValue = ( u32ClkSrc / ( u32Div + 1UL ) );
            }
        }
    }
    else /* For slave mode, force the QSPI peripheral clock rate to equal APB clock rate. */
    {
        /* Default setting: slave selection signal is low level active. */
        qspi->SSCTL = QSPI_SS_ACTIVE_LOW;

        /* Default setting: MSB first, disable unit transfer interrupt, SP_CYCLE = 0. */
        qspi->CTL = u32MasterSlave | ( u32DataWidth << QSPI_CTL_DWIDTH_Pos ) | ( u32QSPIMode ) | QSPI_CTL_SPIEN_Msk;

        /* Set DIVIDER = 0 */
        qspi->CLKDIV = 0UL;

        if( !( __PC() & ( 1UL << 28UL ) ) )
        {
            /* Select PCLK as the clock source of QSPI */
            if( ( qspi == QSPI0 ) || ( qspi == QSPI0_NS ) )
            {
                CLK->CLKSEL2 = ( CLK->CLKSEL2 & ( ~CLK_CLKSEL2_QSPI0SEL_Msk ) ) | CLK_CLKSEL2_QSPI0SEL_PCLK0;
                /* Return slave peripheral clock rate */
                u32RetValue = u32PCLK0Freq;
            }
        }
        else
        {
            /* Check clock source of QSPI */
            if( ( qspi == QSPI0 ) || ( qspi == QSPI0_NS ) )
            {
                if( ( CLK_GetModuleClockSource( QSPI0_MODULE ) << CLK_CLKSEL2_QSPI0SEL_Pos ) == CLK_CLKSEL2_QSPI0SEL_HXT )
                {
                    u32RetValue = __HXT; /* Clock source is HXT */
                }
                else if( ( CLK_GetModuleClockSource( QSPI0_MODULE ) << CLK_CLKSEL2_QSPI0SEL_Pos ) == CLK_CLKSEL2_QSPI0SEL_PLL )
                {
                    u32RetValue = CLK_GetPLLClockFreq(); /* Clock source is PLL */
                }
                else if( ( CLK_GetModuleClockSource( QSPI0_MODULE ) << CLK_CLKSEL2_QSPI0SEL_Pos ) == CLK_CLKSEL2_QSPI0SEL_PCLK0 )
                {
                    u32RetValue = u32PCLK0Freq; /* Clock source is PCLK0 */
                }
                else
                {
                    u32RetValue = __HIRC; /* Clock source is HIRC */
                }
            }
        }
    }

    return u32RetValue;
}

/**
 * @brief  Disable QSPI controller.
 * @param[in]  qspi The pointer of the specified QSPI module.
 * @return None
 * @details Clear SPIEN bit of QSPI_CTL register to disable QSPI transfer control.
 */
void QSPI_Close( QSPI_T * qspi )
{
    qspi->CTL &= ~QSPI_CTL_SPIEN_Msk;
}

/**
 * @brief  Clear RX FIFO buffer.
 * @param[in]  qspi The pointer of the specified QSPI module.
 * @return None
 * @details This function will clear QSPI RX FIFO buffer. The RXEMPTY (QSPI_STATUS[8]) will be set to 1.
 */
void QSPI_ClearRxFIFO( QSPI_T * qspi )
{
    qspi->FIFOCTL |= QSPI_FIFOCTL_RXFBCLR_Msk;
}

/**
 * @brief  Clear TX FIFO buffer.
 * @param[in]  qspi The pointer of the specified QSPI module.
 * @return None
 * @details This function will clear QSPI TX FIFO buffer. The TXEMPTY (QSPI_STATUS[16]) will be set to 1.
 * @note The TX shift register will not be cleared.
 */
void QSPI_ClearTxFIFO( QSPI_T * qspi )
{
    qspi->FIFOCTL |= QSPI_FIFOCTL_TXFBCLR_Msk;
}

/**
 * @brief  Disable the automatic slave selection function.
 * @param[in]  qspi The pointer of the specified QSPI module.
 * @return None
 * @details This function will disable the automatic slave selection function and set slave selection signal to inactive state.
 */
void QSPI_DisableAutoSS( QSPI_T * qspi )
{
    qspi->SSCTL &= ~( QSPI_SSCTL_AUTOSS_Msk | QSPI_SSCTL_SS_Msk );
}

/**
 * @brief  Enable the automatic slave selection function.
 * @param[in]  qspi The pointer of the specified QSPI module.
 * @param[in]  u32SSPinMask Specifies slave selection pins. (QSPI_SS)
 * @param[in]  u32ActiveLevel Specifies the active level of slave selection signal. (QSPI_SS_ACTIVE_HIGH, QSPI_SS_ACTIVE_LOW)
 * @return None
 * @details This function will enable the automatic slave selection function. Only available in Master mode.
 *          The slave selection pin and the active level will be set in this function.
 */
void QSPI_EnableAutoSS( QSPI_T * qspi,
                        uint32_t u32SSPinMask,
                        uint32_t u32ActiveLevel )
{
    qspi->SSCTL = ( qspi->SSCTL & ( ~( QSPI_SSCTL_AUTOSS_Msk | QSPI_SSCTL_SSACTPOL_Msk | QSPI_SSCTL_SS_Msk ) ) ) | ( u32SSPinMask | u32ActiveLevel | QSPI_SSCTL_AUTOSS_Msk );
}

/**
 * @brief  Set the QSPI bus clock.
 * @param[in]  qspi The pointer of the specified QSPI module.
 * @param[in]  u32BusClock The expected frequency of QSPI bus clock in Hz.
 * @return Actual frequency of QSPI bus clock.
 * @details This function is only available in Master mode. The actual clock rate may be different from the target QSPI bus clock rate.
 *          For example, if the QSPI source clock rate is 12 MHz and the target QSPI bus clock rate is 7 MHz, the actual QSPI bus clock
 *          rate will be 6 MHz.
 * @note   If u32BusClock = 0, DIVIDER setting will be set to the maximum value.
 * @note   If u32BusClock >= system clock frequency for Secure, QSPI peripheral clock source will be set to APB clock and DIVIDER will be set to 0.
 * @note   If u32BusClock >= system clock frequency for Non-Secure, this function does not do anything to avoid the situation that the frequency of
 *         QSPI bus clock cannot be faster than the system clock rate. User should set up carefully.
 * @note   If u32BusClock >= QSPI peripheral clock source, DIVIDER will be set to 0.
 */
uint32_t QSPI_SetBusClock( QSPI_T * qspi,
                           uint32_t u32BusClock )
{
    uint32_t u32ClkSrc, u32HCLKFreq;
    uint32_t u32Div, u32RetValue;

    /* Get system clock frequency */
    u32HCLKFreq = CLK_GetHCLKFreq();

    if( u32BusClock >= u32HCLKFreq )
    {
        if( !( __PC() & ( 1UL << 28UL ) ) )
        {
            /* Select PCLK as the clock source of QSPI */
            if( ( qspi == QSPI0 ) || ( qspi == QSPI0_NS ) )
            {
                CLK->CLKSEL2 = ( CLK->CLKSEL2 & ( ~CLK_CLKSEL2_QSPI0SEL_Msk ) ) | CLK_CLKSEL2_QSPI0SEL_PCLK0;
            }
        }
    }

    /* Check clock source of QSPI */
    if( ( qspi == QSPI0 ) || ( qspi == QSPI0_NS ) )
    {
        if( ( CLK_GetModuleClockSource( QSPI0_MODULE ) << CLK_CLKSEL2_QSPI0SEL_Pos ) == CLK_CLKSEL2_QSPI0SEL_HXT )
        {
            u32ClkSrc = __HXT; /* Clock source is HXT */
        }
        else if( ( CLK_GetModuleClockSource( QSPI0_MODULE ) << CLK_CLKSEL2_QSPI0SEL_Pos ) == CLK_CLKSEL2_QSPI0SEL_PLL )
        {
            u32ClkSrc = CLK_GetPLLClockFreq(); /* Clock source is PLL */
        }
        else if( ( CLK_GetModuleClockSource( QSPI0_MODULE ) << CLK_CLKSEL2_QSPI0SEL_Pos ) == CLK_CLKSEL2_QSPI0SEL_PCLK0 )
        {
            u32ClkSrc = CLK_GetPCLK0Freq(); /* Clock source is PCLK0 */
        }
        else
        {
            u32ClkSrc = __HIRC; /* Clock source is HIRC */
        }
    }

    if( u32BusClock >= u32HCLKFreq )
    {
        /* Set DIVIDER = 0 */
        qspi->CLKDIV = 0UL;
        /* Return master peripheral clock rate */
        u32RetValue = u32ClkSrc;
    }
    else if( u32BusClock >= u32ClkSrc )
    {
        /* Set DIVIDER = 0 */
        qspi->CLKDIV = 0UL;
        /* Return master peripheral clock rate */
        u32RetValue = u32ClkSrc;
    }
    else if( u32BusClock == 0UL )
    {
        /* Set DIVIDER to the maximum value 0x1FF. f_spi = f_spi_clk_src / (DIVIDER + 1) */
        qspi->CLKDIV |= QSPI_CLKDIV_DIVIDER_Msk;
        /* Return master peripheral clock rate */
        u32RetValue = ( u32ClkSrc / ( 0x1FFUL + 1UL ) );
    }
    else
    {
        u32Div = ( ( ( u32ClkSrc * 10UL ) / u32BusClock + 5UL ) / 10UL ) - 1UL; /* Round to the nearest integer */

        if( u32Div > 0x1FFUL )
        {
            u32Div = 0x1FFUL;
            qspi->CLKDIV |= QSPI_CLKDIV_DIVIDER_Msk;
            /* Return master peripheral clock rate */
            u32RetValue = ( u32ClkSrc / ( 0x1FFUL + 1UL ) );
        }
        else
        {
            qspi->CLKDIV = ( qspi->CLKDIV & ( ~QSPI_CLKDIV_DIVIDER_Msk ) ) | ( u32Div << QSPI_CLKDIV_DIVIDER_Pos );
            /* Return master peripheral clock rate */
            u32RetValue = ( u32ClkSrc / ( u32Div + 1UL ) );
        }
    }

    return u32RetValue;
}

/**
 * @brief  Configure FIFO threshold setting.
 * @param[in]  qspi The pointer of the specified QSPI module.
 * @param[in]  u32TxThreshold Decides the TX FIFO threshold. It could be 0 ~ 7.
 * @param[in]  u32RxThreshold Decides the RX FIFO threshold. It could be 0 ~ 7.
 * @return None
 * @details Set TX FIFO threshold and RX FIFO threshold configurations.
 */
void QSPI_SetFIFO( QSPI_T * qspi,
                   uint32_t u32TxThreshold,
                   uint32_t u32RxThreshold )
{
    qspi->FIFOCTL = ( qspi->FIFOCTL & ~( QSPI_FIFOCTL_TXTH_Msk | QSPI_FIFOCTL_RXTH_Msk ) ) |
                    ( u32TxThreshold << QSPI_FIFOCTL_TXTH_Pos ) |
                    ( u32RxThreshold << QSPI_FIFOCTL_RXTH_Pos );
}

/**
 * @brief  Get the actual frequency of QSPI bus clock. Only available in Master mode.
 * @param[in]  qspi The pointer of the specified QSPI module.
 * @return Actual QSPI bus clock frequency in Hz.
 * @details This function will calculate the actual QSPI bus clock rate according to the QQSPISEL/QSPIxSEL and DIVIDER settings. Only available in Master mode.
 */
uint32_t QSPI_GetBusClock( QSPI_T * qspi )
{
    uint32_t u32Div;
    uint32_t u32ClkSrc;

    /* Get DIVIDER setting */
    u32Div = ( qspi->CLKDIV & QSPI_CLKDIV_DIVIDER_Msk ) >> QSPI_CLKDIV_DIVIDER_Pos;

    /* Check clock source of QSPI */
    if( ( qspi == QSPI0 ) || ( qspi == QSPI0_NS ) )
    {
        if( ( CLK_GetModuleClockSource( QSPI0_MODULE ) << CLK_CLKSEL2_QSPI0SEL_Pos ) == CLK_CLKSEL2_QSPI0SEL_HXT )
        {
            u32ClkSrc = __HXT; /* Clock source is HXT */
        }
        else if( ( CLK_GetModuleClockSource( QSPI0_MODULE ) << CLK_CLKSEL2_QSPI0SEL_Pos ) == CLK_CLKSEL2_QSPI0SEL_PLL )
        {
            u32ClkSrc = CLK_GetPLLClockFreq(); /* Clock source is PLL */
        }
        else if( ( CLK_GetModuleClockSource( QSPI0_MODULE ) << CLK_CLKSEL2_QSPI0SEL_Pos ) == CLK_CLKSEL2_QSPI0SEL_PCLK0 )
        {
            u32ClkSrc = CLK_GetPCLK0Freq(); /* Clock source is PCLK0 */
        }
        else
        {
            u32ClkSrc = __HIRC; /* Clock source is HIRC */
        }
    }

    /* Return QSPI bus clock rate */
    return( u32ClkSrc / ( u32Div + 1UL ) );
}

/**
 * @brief  Enable interrupt function.
 * @param[in]  qspi The pointer of the specified QSPI module.
 * @param[in]  u32Mask The combination of all related interrupt enable bits.
 *                     Each bit corresponds to a interrupt enable bit.
 *                     This parameter decides which interrupts will be enabled. It is combination of:
 *                       - \ref QSPI_UNIT_INT_MASK
 *                       - \ref QSPI_SSACT_INT_MASK
 *                       - \ref QSPI_SSINACT_INT_MASK
 *                       - \ref QSPI_SLVUR_INT_MASK
 *                       - \ref QSPI_SLVBE_INT_MASK
 *                       - \ref QSPI_SLVTO_INT_MASK
 *                       - \ref QSPI_TXUF_INT_MASK
 *                       - \ref QSPI_FIFO_TXTH_INT_MASK
 *                       - \ref QSPI_FIFO_RXTH_INT_MASK
 *                       - \ref QSPI_FIFO_RXOV_INT_MASK
 *                       - \ref QSPI_FIFO_RXTO_INT_MASK
 *
 * @return None
 * @details Enable QSPI related interrupts specified by u32Mask parameter.
 */
void QSPI_EnableInt( QSPI_T * qspi,
                     uint32_t u32Mask )
{
    /* Enable unit transfer interrupt flag */
    if( ( u32Mask & QSPI_UNIT_INT_MASK ) == QSPI_UNIT_INT_MASK )
    {
        qspi->CTL |= QSPI_CTL_UNITIEN_Msk;
    }

    /* Enable slave selection signal active interrupt flag */
    if( ( u32Mask & QSPI_SSACT_INT_MASK ) == QSPI_SSACT_INT_MASK )
    {
        qspi->SSCTL |= QSPI_SSCTL_SSACTIEN_Msk;
    }

    /* Enable slave selection signal inactive interrupt flag */
    if( ( u32Mask & QSPI_SSINACT_INT_MASK ) == QSPI_SSINACT_INT_MASK )
    {
        qspi->SSCTL |= QSPI_SSCTL_SSINAIEN_Msk;
    }

    /* Enable slave TX under run interrupt flag */
    if( ( u32Mask & QSPI_SLVUR_INT_MASK ) == QSPI_SLVUR_INT_MASK )
    {
        qspi->SSCTL |= QSPI_SSCTL_SLVURIEN_Msk;
    }

    /* Enable slave bit count error interrupt flag */
    if( ( u32Mask & QSPI_SLVBE_INT_MASK ) == QSPI_SLVBE_INT_MASK )
    {
        qspi->SSCTL |= QSPI_SSCTL_SLVBEIEN_Msk;
    }

    /* Enable slave mode time-out interrupt flag */
    if( ( u32Mask & QSPI_SLVTO_INT_MASK ) == QSPI_SLVTO_INT_MASK )
    {
        qspi->SSCTL |= QSPI_SSCTL_SLVTOIEN_Msk;
    }

    /* Enable slave TX underflow interrupt flag */
    if( ( u32Mask & QSPI_TXUF_INT_MASK ) == QSPI_TXUF_INT_MASK )
    {
        qspi->FIFOCTL |= QSPI_FIFOCTL_TXUFIEN_Msk;
    }

    /* Enable TX threshold interrupt flag */
    if( ( u32Mask & QSPI_FIFO_TXTH_INT_MASK ) == QSPI_FIFO_TXTH_INT_MASK )
    {
        qspi->FIFOCTL |= QSPI_FIFOCTL_TXTHIEN_Msk;
    }

    /* Enable RX threshold interrupt flag */
    if( ( u32Mask & QSPI_FIFO_RXTH_INT_MASK ) == QSPI_FIFO_RXTH_INT_MASK )
    {
        qspi->FIFOCTL |= QSPI_FIFOCTL_RXTHIEN_Msk;
    }

    /* Enable RX overrun interrupt flag */
    if( ( u32Mask & QSPI_FIFO_RXOV_INT_MASK ) == QSPI_FIFO_RXOV_INT_MASK )
    {
        qspi->FIFOCTL |= QSPI_FIFOCTL_RXOVIEN_Msk;
    }

    /* Enable RX time-out interrupt flag */
    if( ( u32Mask & QSPI_FIFO_RXTO_INT_MASK ) == QSPI_FIFO_RXTO_INT_MASK )
    {
        qspi->FIFOCTL |= QSPI_FIFOCTL_RXTOIEN_Msk;
    }
}

/**
 * @brief  Disable interrupt function.
 * @param[in]  qspi The pointer of the specified QSPI module.
 * @param[in]  u32Mask The combination of all related interrupt enable bits.
 *                     Each bit corresponds to a interrupt bit.
 *                     This parameter decides which interrupts will be disabled. It is combination of:
 *                       - \ref QSPI_UNIT_INT_MASK
 *                       - \ref QSPI_SSACT_INT_MASK
 *                       - \ref QSPI_SSINACT_INT_MASK
 *                       - \ref QSPI_SLVUR_INT_MASK
 *                       - \ref QSPI_SLVBE_INT_MASK
 *                       - \ref QSPI_SLVTO_INT_MASK
 *                       - \ref QSPI_TXUF_INT_MASK
 *                       - \ref QSPI_FIFO_TXTH_INT_MASK
 *                       - \ref QSPI_FIFO_RXTH_INT_MASK
 *                       - \ref QSPI_FIFO_RXOV_INT_MASK
 *                       - \ref QSPI_FIFO_RXTO_INT_MASK
 *
 * @return None
 * @details Disable QSPI related interrupts specified by u32Mask parameter.
 */
void QSPI_DisableInt( QSPI_T * qspi,
                      uint32_t u32Mask )
{
    /* Disable unit transfer interrupt flag */
    if( ( u32Mask & QSPI_UNIT_INT_MASK ) == QSPI_UNIT_INT_MASK )
    {
        qspi->CTL &= ~QSPI_CTL_UNITIEN_Msk;
    }

    /* Disable slave selection signal active interrupt flag */
    if( ( u32Mask & QSPI_SSACT_INT_MASK ) == QSPI_SSACT_INT_MASK )
    {
        qspi->SSCTL &= ~QSPI_SSCTL_SSACTIEN_Msk;
    }

    /* Disable slave selection signal inactive interrupt flag */
    if( ( u32Mask & QSPI_SSINACT_INT_MASK ) == QSPI_SSINACT_INT_MASK )
    {
        qspi->SSCTL &= ~QSPI_SSCTL_SSINAIEN_Msk;
    }

    /* Disable slave TX under run interrupt flag */
    if( ( u32Mask & QSPI_SLVUR_INT_MASK ) == QSPI_SLVUR_INT_MASK )
    {
        qspi->SSCTL &= ~QSPI_SSCTL_SLVURIEN_Msk;
    }

    /* Disable slave bit count error interrupt flag */
    if( ( u32Mask & QSPI_SLVBE_INT_MASK ) == QSPI_SLVBE_INT_MASK )
    {
        qspi->SSCTL &= ~QSPI_SSCTL_SLVBEIEN_Msk;
    }

    /* Disable slave mode time-out interrupt flag */
    if( ( u32Mask & QSPI_SLVTO_INT_MASK ) == QSPI_SLVTO_INT_MASK )
    {
        qspi->SSCTL &= ~QSPI_SSCTL_SLVTOIEN_Msk;
    }

    /* Disable slave TX underflow interrupt flag */
    if( ( u32Mask & QSPI_TXUF_INT_MASK ) == QSPI_TXUF_INT_MASK )
    {
        qspi->FIFOCTL &= ~QSPI_FIFOCTL_TXUFIEN_Msk;
    }

    /* Disable TX threshold interrupt flag */
    if( ( u32Mask & QSPI_FIFO_TXTH_INT_MASK ) == QSPI_FIFO_TXTH_INT_MASK )
    {
        qspi->FIFOCTL &= ~QSPI_FIFOCTL_TXTHIEN_Msk;
    }

    /* Disable RX threshold interrupt flag */
    if( ( u32Mask & QSPI_FIFO_RXTH_INT_MASK ) == QSPI_FIFO_RXTH_INT_MASK )
    {
        qspi->FIFOCTL &= ~QSPI_FIFOCTL_RXTHIEN_Msk;
    }

    /* Disable RX overrun interrupt flag */
    if( ( u32Mask & QSPI_FIFO_RXOV_INT_MASK ) == QSPI_FIFO_RXOV_INT_MASK )
    {
        qspi->FIFOCTL &= ~QSPI_FIFOCTL_RXOVIEN_Msk;
    }

    /* Disable RX time-out interrupt flag */
    if( ( u32Mask & QSPI_FIFO_RXTO_INT_MASK ) == QSPI_FIFO_RXTO_INT_MASK )
    {
        qspi->FIFOCTL &= ~QSPI_FIFOCTL_RXTOIEN_Msk;
    }
}

/**
 * @brief  Get interrupt flag.
 * @param[in]  qspi The pointer of the specified QSPI module.
 * @param[in]  u32Mask The combination of all related interrupt sources.
 *                     Each bit corresponds to a interrupt source.
 *                     This parameter decides which interrupt flags will be read. It is combination of:
 *                       - \ref QSPI_UNIT_INT_MASK
 *                       - \ref QSPI_SSACT_INT_MASK
 *                       - \ref QSPI_SSINACT_INT_MASK
 *                       - \ref QSPI_SLVUR_INT_MASK
 *                       - \ref QSPI_SLVBE_INT_MASK
 *                       - \ref QSPI_SLVTO_INT_MASK
 *                       - \ref QSPI_TXUF_INT_MASK
 *                       - \ref QSPI_FIFO_TXTH_INT_MASK
 *                       - \ref QSPI_FIFO_RXTH_INT_MASK
 *                       - \ref QSPI_FIFO_RXOV_INT_MASK
 *                       - \ref QSPI_FIFO_RXTO_INT_MASK
 *
 * @return Interrupt flags of selected sources.
 * @details Get QSPI related interrupt flags specified by u32Mask parameter.
 */
uint32_t QSPI_GetIntFlag( QSPI_T * qspi,
                          uint32_t u32Mask )
{
    uint32_t u32IntStatus;
    uint32_t u32IntFlag = 0UL;

    u32IntStatus = qspi->STATUS;

    /* Check unit transfer interrupt flag */
    if( ( u32Mask & QSPI_UNIT_INT_MASK ) && ( u32IntStatus & QSPI_STATUS_UNITIF_Msk ) )
    {
        u32IntFlag |= QSPI_UNIT_INT_MASK;
    }

    /* Check slave selection signal active interrupt flag */
    if( ( u32Mask & QSPI_SSACT_INT_MASK ) && ( u32IntStatus & QSPI_STATUS_SSACTIF_Msk ) )
    {
        u32IntFlag |= QSPI_SSACT_INT_MASK;
    }

    /* Check slave selection signal inactive interrupt flag */
    if( ( u32Mask & QSPI_SSINACT_INT_MASK ) && ( u32IntStatus & QSPI_STATUS_SSINAIF_Msk ) )
    {
        u32IntFlag |= QSPI_SSINACT_INT_MASK;
    }

    /* Check slave TX under run interrupt flag */
    if( ( u32Mask & QSPI_SLVUR_INT_MASK ) && ( u32IntStatus & QSPI_STATUS_SLVURIF_Msk ) )
    {
        u32IntFlag |= QSPI_SLVUR_INT_MASK;
    }

    /* Check slave bit count error interrupt flag */
    if( ( u32Mask & QSPI_SLVBE_INT_MASK ) && ( u32IntStatus & QSPI_STATUS_SLVBEIF_Msk ) )
    {
        u32IntFlag |= QSPI_SLVBE_INT_MASK;
    }

    /* Check slave mode time-out interrupt flag */
    if( ( u32Mask & QSPI_SLVTO_INT_MASK ) && ( u32IntStatus & QSPI_STATUS_SLVTOIF_Msk ) )
    {
        u32IntFlag |= QSPI_SLVTO_INT_MASK;
    }

    /* Check slave TX underflow interrupt flag */
    if( ( u32Mask & QSPI_TXUF_INT_MASK ) && ( u32IntStatus & QSPI_STATUS_TXUFIF_Msk ) )
    {
        u32IntFlag |= QSPI_TXUF_INT_MASK;
    }

    /* Check TX threshold interrupt flag */
    if( ( u32Mask & QSPI_FIFO_TXTH_INT_MASK ) && ( u32IntStatus & QSPI_STATUS_TXTHIF_Msk ) )
    {
        u32IntFlag |= QSPI_FIFO_TXTH_INT_MASK;
    }

    /* Check RX threshold interrupt flag */
    if( ( u32Mask & QSPI_FIFO_RXTH_INT_MASK ) && ( u32IntStatus & QSPI_STATUS_RXTHIF_Msk ) )
    {
        u32IntFlag |= QSPI_FIFO_RXTH_INT_MASK;
    }

    /* Check RX overrun interrupt flag */
    if( ( u32Mask & QSPI_FIFO_RXOV_INT_MASK ) && ( u32IntStatus & QSPI_STATUS_RXOVIF_Msk ) )
    {
        u32IntFlag |= QSPI_FIFO_RXOV_INT_MASK;
    }

    /* Check RX time-out interrupt flag */
    if( ( u32Mask & QSPI_FIFO_RXTO_INT_MASK ) && ( u32IntStatus & QSPI_STATUS_RXTOIF_Msk ) )
    {
        u32IntFlag |= QSPI_FIFO_RXTO_INT_MASK;
    }

    return u32IntFlag;
}

/**
 * @brief  Clear interrupt flag.
 * @param[in]  qspi The pointer of the specified QSPI module.
 * @param[in]  u32Mask The combination of all related interrupt sources.
 *                     Each bit corresponds to a interrupt source.
 *                     This parameter decides which interrupt flags will be cleared. It could be the combination of:
 *                       - \ref QSPI_UNIT_INT_MASK
 *                       - \ref QSPI_SSACT_INT_MASK
 *                       - \ref QSPI_SSINACT_INT_MASK
 *                       - \ref QSPI_SLVUR_INT_MASK
 *                       - \ref QSPI_SLVBE_INT_MASK
 *                       - \ref QSPI_SLVTO_INT_MASK
 *                       - \ref QSPI_TXUF_INT_MASK
 *                       - \ref QSPI_FIFO_RXOV_INT_MASK
 *                       - \ref QSPI_FIFO_RXTO_INT_MASK
 *
 * @return None
 * @details Clear QSPI related interrupt flags specified by u32Mask parameter.
 */
void QSPI_ClearIntFlag( QSPI_T * qspi,
                        uint32_t u32Mask )
{
    if( u32Mask & QSPI_UNIT_INT_MASK )
    {
        qspi->STATUS = QSPI_STATUS_UNITIF_Msk; /* Clear unit transfer interrupt flag */
    }

    if( u32Mask & QSPI_SSACT_INT_MASK )
    {
        qspi->STATUS = QSPI_STATUS_SSACTIF_Msk; /* Clear slave selection signal active interrupt flag */
    }

    if( u32Mask & QSPI_SSINACT_INT_MASK )
    {
        qspi->STATUS = QSPI_STATUS_SSINAIF_Msk; /* Clear slave selection signal inactive interrupt flag */
    }

    if( u32Mask & QSPI_SLVUR_INT_MASK )
    {
        qspi->STATUS = QSPI_STATUS_SLVURIF_Msk; /* Clear slave TX under run interrupt flag */
    }

    if( u32Mask & QSPI_SLVBE_INT_MASK )
    {
        qspi->STATUS = QSPI_STATUS_SLVBEIF_Msk; /* Clear slave bit count error interrupt flag */
    }

    if( u32Mask & QSPI_SLVTO_INT_MASK )
    {
        qspi->STATUS = QSPI_STATUS_SLVTOIF_Msk; /* Clear slave mode time-out interrupt flag */
    }

    if( u32Mask & QSPI_TXUF_INT_MASK )
    {
        qspi->STATUS = QSPI_STATUS_TXUFIF_Msk; /* Clear slave TX underflow interrupt flag */
    }

    if( u32Mask & QSPI_FIFO_RXOV_INT_MASK )
    {
        qspi->STATUS = QSPI_STATUS_RXOVIF_Msk; /* Clear RX overrun interrupt flag */
    }

    if( u32Mask & QSPI_FIFO_RXTO_INT_MASK )
    {
        qspi->STATUS = QSPI_STATUS_RXTOIF_Msk; /* Clear RX time-out interrupt flag */
    }
}

/**
 * @brief  Get QSPI status.
 * @param[in]  qspi The pointer of the specified QSPI module.
 * @param[in]  u32Mask The combination of all related sources.
 *                     Each bit corresponds to a source.
 *                     This parameter decides which flags will be read. It is combination of:
 *                       - \ref QSPI_BUSY_MASK
 *                       - \ref QSPI_RX_EMPTY_MASK
 *                       - \ref QSPI_RX_FULL_MASK
 *                       - \ref QSPI_TX_EMPTY_MASK
 *                       - \ref QSPI_TX_FULL_MASK
 *                       - \ref QSPI_TXRX_RESET_MASK
 *                       - \ref QSPI_SPIEN_STS_MASK
 *                       - \ref QSPI_SSLINE_STS_MASK
 *
 * @return Flags of selected sources.
 * @details Get QSPI related status specified by u32Mask parameter.
 */
uint32_t QSPI_GetStatus( QSPI_T * qspi,
                         uint32_t u32Mask )
{
    uint32_t u32TmpStatus;
    uint32_t u32Flag = 0UL;

    u32TmpStatus = qspi->STATUS;

    /* Check busy status */
    if( ( u32Mask & QSPI_BUSY_MASK ) && ( u32TmpStatus & QSPI_STATUS_BUSY_Msk ) )
    {
        u32Flag |= QSPI_BUSY_MASK;
    }

    /* Check RX empty flag */
    if( ( u32Mask & QSPI_RX_EMPTY_MASK ) && ( u32TmpStatus & QSPI_STATUS_RXEMPTY_Msk ) )
    {
        u32Flag |= QSPI_RX_EMPTY_MASK;
    }

    /* Check RX full flag */
    if( ( u32Mask & QSPI_RX_FULL_MASK ) && ( u32TmpStatus & QSPI_STATUS_RXFULL_Msk ) )
    {
        u32Flag |= QSPI_RX_FULL_MASK;
    }

    /* Check TX empty flag */
    if( ( u32Mask & QSPI_TX_EMPTY_MASK ) && ( u32TmpStatus & QSPI_STATUS_TXEMPTY_Msk ) )
    {
        u32Flag |= QSPI_TX_EMPTY_MASK;
    }

    /* Check TX full flag */
    if( ( u32Mask & QSPI_TX_FULL_MASK ) && ( u32TmpStatus & QSPI_STATUS_TXFULL_Msk ) )
    {
        u32Flag |= QSPI_TX_FULL_MASK;
    }

    /* Check TX/RX reset flag */
    if( ( u32Mask & QSPI_TXRX_RESET_MASK ) && ( u32TmpStatus & QSPI_STATUS_TXRXRST_Msk ) )
    {
        u32Flag |= QSPI_TXRX_RESET_MASK;
    }

    /* Check SPIEN flag */
    if( ( u32Mask & QSPI_SPIEN_STS_MASK ) && ( u32TmpStatus & QSPI_STATUS_SPIENSTS_Msk ) )
    {
        u32Flag |= QSPI_SPIEN_STS_MASK;
    }

    /* Check QSPIx_SS line status */
    if( ( u32Mask & QSPI_SSLINE_STS_MASK ) && ( u32TmpStatus & QSPI_STATUS_SSLINE_Msk ) )
    {
        u32Flag |= QSPI_SSLINE_STS_MASK;
    }

    return u32Flag;
}

/*@}*/ /* end of group QSPI_EXPORTED_FUNCTIONS */

/*@}*/ /* end of group QSPI_Driver */

/*@}*/ /* end of group Standard_Driver */

/*** (C) COPYRIGHT 2017 Nuvoton Technology Corp. ***/
