/*
 * Copyright (c) 2015-2016, Freescale Semiconductor, Inc.
 * Copyright 2016-2017 NXP
 * All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "fsl_lpuart.h"

/*******************************************************************************
 * Definitions
 ******************************************************************************/
/* LPUART transfer state. */
enum _lpuart_transfer_states
{
    kLPUART_TxIdle, /*!< TX idle. */
    kLPUART_TxBusy, /*!< TX busy. */
    kLPUART_RxIdle, /*!< RX idle. */
    kLPUART_RxBusy  /*!< RX busy. */
};

/* Typedef for interrupt handler. */
typedef void (*lpuart_isr_t)(LPUART_Type *base, lpuart_handle_t *handle);

/*******************************************************************************
 * Prototypes
 ******************************************************************************/
/*!
 * @brief Get the LPUART instance from peripheral base address.
 *
 * @param base LPUART peripheral base address.
 * @return LPUART instance.
 */
uint32_t LPUART_GetInstance(LPUART_Type *base);

/*!
 * @brief Get the length of received data in RX ring buffer.
 *
 * @userData handle LPUART handle pointer.
 * @return Length of received data in RX ring buffer.
 */
static size_t LPUART_TransferGetRxRingBufferLength(LPUART_Type *base, lpuart_handle_t *handle);

/*!
 * @brief Check whether the RX ring buffer is full.
 *
 * @userData handle LPUART handle pointer.
 * @retval true  RX ring buffer is full.
 * @retval false RX ring buffer is not full.
 */
static bool LPUART_TransferIsRxRingBufferFull(LPUART_Type *base, lpuart_handle_t *handle);

/*!
 * @brief Write to TX register using non-blocking method.
 *
 * This function writes data to the TX register directly, upper layer must make
 * sure the TX register is empty or TX FIFO has empty room before calling this function.
 *
 * @note This function does not check whether all the data has been sent out to bus,
 * so before disable TX, check kLPUART_TransmissionCompleteFlag to ensure the TX is
 * finished.
 *
 * @param base LPUART peripheral base address.
 * @param data Start addresss of the data to write.
 * @param length Size of the buffer to be sent.
 */
static void LPUART_WriteNonBlocking(LPUART_Type *base, const uint8_t *data, size_t length);

/*!
 * @brief Read RX register using non-blocking method.
 *
 * This function reads data from the TX register directly, upper layer must make
 * sure the RX register is full or TX FIFO has data before calling this function.
 *
 * @param base LPUART peripheral base address.
 * @param data Start addresss of the buffer to store the received data.
 * @param length Size of the buffer.
 */
static void LPUART_ReadNonBlocking(LPUART_Type *base, uint8_t *data, size_t length);

/*******************************************************************************
 * Variables
 ******************************************************************************/
/* Array of LPUART handle. */
static lpuart_handle_t *s_lpuartHandle[FSL_FEATURE_SOC_LPUART_COUNT];
/* Array of LPUART peripheral base address. */
static LPUART_Type *const s_lpuartBases[] = LPUART_BASE_PTRS;
/* Array of LPUART IRQ number. */
#if defined(FSL_FEATURE_LPUART_HAS_SEPARATE_RX_TX_IRQ) && FSL_FEATURE_LPUART_HAS_SEPARATE_RX_TX_IRQ
static const IRQn_Type s_lpuartRxIRQ[] = LPUART_RX_IRQS;
static const IRQn_Type s_lpuartTxIRQ[] = LPUART_TX_IRQS;
#else
static const IRQn_Type s_lpuartIRQ[] = LPUART_RX_TX_IRQS;
#endif
#if !(defined(FSL_SDK_DISABLE_DRIVER_CLOCK_CONTROL) && FSL_SDK_DISABLE_DRIVER_CLOCK_CONTROL)
/* Array of LPUART clock name. */
static const clock_ip_name_t s_lpuartClock[] = LPUART_CLOCKS;

#if defined(LPUART_PERIPH_CLOCKS)
/* Array of LPUART functional clock name. */
static const clock_ip_name_t s_lpuartPeriphClocks[] = LPUART_PERIPH_CLOCKS;
#endif

#endif /* FSL_SDK_DISABLE_DRIVER_CLOCK_CONTROL */

/* LPUART ISR for transactional APIs. */
static lpuart_isr_t s_lpuartIsr;

/*******************************************************************************
 * Code
 ******************************************************************************/
uint32_t LPUART_GetInstance(LPUART_Type *base)
{
    uint32_t instance;

    /* Find the instance index from base address mappings. */
    for (instance = 0; instance < ARRAY_SIZE(s_lpuartBases); instance++)
    {
        if (s_lpuartBases[instance] == base)
        {
            break;
        }
    }

    assert(instance < ARRAY_SIZE(s_lpuartBases));

    return instance;
}

static size_t LPUART_TransferGetRxRingBufferLength(LPUART_Type *base, lpuart_handle_t *handle)
{
    assert(handle);

    size_t size;

    if (handle->rxRingBufferTail > handle->rxRingBufferHead)
    {
        size = (size_t)(handle->rxRingBufferHead + handle->rxRingBufferSize - handle->rxRingBufferTail);
    }
    else
    {
        size = (size_t)(handle->rxRingBufferHead - handle->rxRingBufferTail);
    }

    return size;
}

static bool LPUART_TransferIsRxRingBufferFull(LPUART_Type *base, lpuart_handle_t *handle)
{
    assert(handle);

    bool full;

    if (LPUART_TransferGetRxRingBufferLength(base, handle) == (handle->rxRingBufferSize - 1U))
    {
        full = true;
    }
    else
    {
        full = false;
    }
    return full;
}

static void LPUART_WriteNonBlocking(LPUART_Type *base, const uint8_t *data, size_t length)
{
    assert(data);

    size_t i;

    /* The Non Blocking write data API assume user have ensured there is enough space in
    peripheral to write. */
    for (i = 0; i < length; i++)
    {
        base->DATA = data[i];
    }
}

static void LPUART_ReadNonBlocking(LPUART_Type *base, uint8_t *data, size_t length)
{
    assert(data);

    size_t i;
#if defined(FSL_FEATURE_LPUART_HAS_7BIT_DATA_SUPPORT) && FSL_FEATURE_LPUART_HAS_7BIT_DATA_SUPPORT
    uint32_t ctrl = base->CTRL;
    bool isSevenDataBits =
        ((ctrl & LPUART_CTRL_M7_MASK) ||
         ((!(ctrl & LPUART_CTRL_M7_MASK)) && (!(ctrl & LPUART_CTRL_M_MASK)) && (ctrl & LPUART_CTRL_PE_MASK)));
#endif

    /* The Non Blocking read data API assume user have ensured there is enough space in
    peripheral to write. */
    for (i = 0; i < length; i++)
    {
#if defined(FSL_FEATURE_LPUART_HAS_7BIT_DATA_SUPPORT) && FSL_FEATURE_LPUART_HAS_7BIT_DATA_SUPPORT
        if (isSevenDataBits)
        {
            data[i] = (base->DATA & 0x7F);
        }
        else
        {
            data[i] = base->DATA;
        }
#else
        data[i] = base->DATA;
#endif
    }
}

status_t LPUART_Init(LPUART_Type *base, const lpuart_config_t *config, uint32_t srcClock_Hz)
{
    assert(config);
    assert(config->baudRate_Bps);
#if defined(FSL_FEATURE_LPUART_HAS_FIFO) && FSL_FEATURE_LPUART_HAS_FIFO
    assert(FSL_FEATURE_LPUART_FIFO_SIZEn(base) >= config->txFifoWatermark);
    assert(FSL_FEATURE_LPUART_FIFO_SIZEn(base) >= config->rxFifoWatermark);
#endif

    uint32_t temp;
    uint16_t sbr, sbrTemp;
    uint32_t osr, osrTemp, tempDiff, calculatedBaud, baudDiff;

    /* This LPUART instantiation uses a slightly different baud rate calculation
     * The idea is to use the best OSR (over-sampling rate) possible
     * Note, OSR is typically hard-set to 16 in other LPUART instantiations
     * loop to find the best OSR value possible, one that generates minimum baudDiff
     * iterate through the rest of the supported values of OSR */

    baudDiff = config->baudRate_Bps;
    osr = 0;
    sbr = 0;
    for (osrTemp = 4; osrTemp <= 32; osrTemp++)
    {
        /* calculate the temporary sbr value   */
        sbrTemp = (srcClock_Hz / (config->baudRate_Bps * osrTemp));
        /*set sbrTemp to 1 if the sourceClockInHz can not satisfy the desired baud rate*/
        if (sbrTemp == 0)
        {
            sbrTemp = 1;
        }
        /* Calculate the baud rate based on the temporary OSR and SBR values */
        calculatedBaud = (srcClock_Hz / (osrTemp * sbrTemp));

        tempDiff = calculatedBaud - config->baudRate_Bps;

        /* Select the better value between srb and (sbr + 1) */
        if (tempDiff > (config->baudRate_Bps - (srcClock_Hz / (osrTemp * (sbrTemp + 1)))))
        {
            tempDiff = config->baudRate_Bps - (srcClock_Hz / (osrTemp * (sbrTemp + 1)));
            sbrTemp++;
        }

        if (tempDiff <= baudDiff)
        {
            baudDiff = tempDiff;
            osr = osrTemp; /* update and store the best OSR value calculated */
            sbr = sbrTemp; /* update store the best SBR value calculated */
        }
    }

    /* Check to see if actual baud rate is within 3% of desired baud rate
     * based on the best calculate OSR value */
    if (baudDiff > ((config->baudRate_Bps / 100) * 3))
    {
        /* Unacceptable baud rate difference of more than 3%*/
        return kStatus_LPUART_BaudrateNotSupport;
    }

#if !(defined(FSL_SDK_DISABLE_DRIVER_CLOCK_CONTROL) && FSL_SDK_DISABLE_DRIVER_CLOCK_CONTROL)

    uint32_t instance = LPUART_GetInstance(base);

    /* Enable lpuart clock */
    CLOCK_EnableClock(s_lpuartClock[instance]);
#if defined(LPUART_PERIPH_CLOCKS)
    CLOCK_EnableClock(s_lpuartPeriphClocks[instance]);
#endif

#endif /* FSL_SDK_DISABLE_DRIVER_CLOCK_CONTROL */

#if defined(FSL_FEATURE_LPUART_HAS_GLOBAL) && FSL_FEATURE_LPUART_HAS_GLOBAL
    /*Reset all internal logic and registers, except the Global Register */
    LPUART_SoftwareReset(base);
#else
    /* Disable LPUART TX RX before setting. */
    base->CTRL &= ~(LPUART_CTRL_TE_MASK | LPUART_CTRL_RE_MASK);
#endif

    temp = base->BAUD;

    /* Acceptable baud rate, check if OSR is between 4x and 7x oversampling.
     * If so, then "BOTHEDGE" sampling must be turned on */
    if ((osr > 3) && (osr < 8))
    {
        temp |= LPUART_BAUD_BOTHEDGE_MASK;
    }

    /* program the osr value (bit value is one less than actual value) */
    temp &= ~LPUART_BAUD_OSR_MASK;
    temp |= LPUART_BAUD_OSR(osr - 1);

    /* write the sbr value to the BAUD registers */
    temp &= ~LPUART_BAUD_SBR_MASK;
    base->BAUD = temp | LPUART_BAUD_SBR(sbr);

    /* Set bit count and parity mode. */
    base->BAUD &= ~LPUART_BAUD_M10_MASK;

    temp = base->CTRL &
           ~(LPUART_CTRL_PE_MASK | LPUART_CTRL_PT_MASK | LPUART_CTRL_M_MASK | LPUART_CTRL_ILT_MASK |
             LPUART_CTRL_IDLECFG_MASK);

    temp |=
        (uint8_t)config->parityMode | LPUART_CTRL_IDLECFG(config->rxIdleConfig) | LPUART_CTRL_ILT(config->rxIdleType);

#if defined(FSL_FEATURE_LPUART_HAS_7BIT_DATA_SUPPORT) && FSL_FEATURE_LPUART_HAS_7BIT_DATA_SUPPORT
    if (kLPUART_SevenDataBits == config->dataBitsCount)
    {
        if (kLPUART_ParityDisabled != config->parityMode)
        {
            temp &= ~LPUART_CTRL_M7_MASK; /* Seven data bits and one parity bit */
        }
        else
        {
            temp |= LPUART_CTRL_M7_MASK;
        }
    }
    else
#endif
    {
        if (kLPUART_ParityDisabled != config->parityMode)
        {
            temp |= LPUART_CTRL_M_MASK; /* Eight data bits and one parity bit */
        }
    }

    base->CTRL = temp;

#if defined(FSL_FEATURE_LPUART_HAS_STOP_BIT_CONFIG_SUPPORT) && FSL_FEATURE_LPUART_HAS_STOP_BIT_CONFIG_SUPPORT
    /* set stop bit per char */
    temp = base->BAUD & ~LPUART_BAUD_SBNS_MASK;
    base->BAUD = temp | LPUART_BAUD_SBNS((uint8_t)config->stopBitCount);
#endif

#if defined(FSL_FEATURE_LPUART_HAS_FIFO) && FSL_FEATURE_LPUART_HAS_FIFO
    /* Set tx/rx WATER watermark
       Note:
       Take care of the RX FIFO, RX interrupt request only assert when received bytes
       equal or more than RX water mark, there is potential issue if RX water
       mark larger than 1.
       For example, if RX FIFO water mark is 2, upper layer needs 5 bytes and
       5 bytes are received. the last byte will be saved in FIFO but not trigger
       RX interrupt because the water mark is 2.
     */
    base->WATER = (((uint32_t)(config->rxFifoWatermark) << 16) | config->txFifoWatermark);

    /* Enable tx/rx FIFO */
    base->FIFO |= (LPUART_FIFO_TXFE_MASK | LPUART_FIFO_RXFE_MASK);

    /* Flush FIFO */
    base->FIFO |= (LPUART_FIFO_TXFLUSH_MASK | LPUART_FIFO_RXFLUSH_MASK);
#endif

    /* Clear all status flags */
    temp = (LPUART_STAT_RXEDGIF_MASK | LPUART_STAT_IDLE_MASK | LPUART_STAT_OR_MASK | LPUART_STAT_NF_MASK |
            LPUART_STAT_FE_MASK | LPUART_STAT_PF_MASK);

#if defined(FSL_FEATURE_LPUART_HAS_LIN_BREAK_DETECT) && FSL_FEATURE_LPUART_HAS_LIN_BREAK_DETECT
    temp |= LPUART_STAT_LBKDIF_MASK;
#endif

#if defined(FSL_FEATURE_LPUART_HAS_ADDRESS_MATCHING) && FSL_FEATURE_LPUART_HAS_ADDRESS_MATCHING
    temp |= (LPUART_STAT_MA1F_MASK | LPUART_STAT_MA2F_MASK);
#endif

#if defined(FSL_FEATURE_LPUART_HAS_MODEM_SUPPORT) && FSL_FEATURE_LPUART_HAS_MODEM_SUPPORT
    /* Set the CTS configuration/TX CTS source. */
    base->MODIR |= LPUART_MODIR_TXCTSC(config->txCtsConfig) | LPUART_MODIR_TXCTSSRC(config->txCtsSource);
    if (config->enableRxRTS)
    {
        /* Enable the receiver RTS(request-to-send) function. */
        base->MODIR |= LPUART_MODIR_RXRTSE_MASK;
    }
    if (config->enableTxCTS)
    {
        /* Enable the CTS(clear-to-send) function. */
        base->MODIR |= LPUART_MODIR_TXCTSE_MASK;
    }
#endif

    /* Set data bits order. */
    if (config->isMsb)
    {
        temp |= LPUART_STAT_MSBF_MASK;
    }
    else
    {
        temp &= ~LPUART_STAT_MSBF_MASK;
    }

    base->STAT |= temp;

    /* Enable TX/RX base on configure structure. */
    temp = base->CTRL;
    if (config->enableTx)
    {
        temp |= LPUART_CTRL_TE_MASK;
    }

    if (config->enableRx)
    {
        temp |= LPUART_CTRL_RE_MASK;
    }

    base->CTRL = temp;

    return kStatus_Success;
}
void LPUART_Deinit(LPUART_Type *base)
{
    uint32_t temp;

#if defined(FSL_FEATURE_LPUART_HAS_FIFO) && FSL_FEATURE_LPUART_HAS_FIFO
    /* Wait tx FIFO send out*/
    while (0 != ((base->WATER & LPUART_WATER_TXCOUNT_MASK) >> LPUART_WATER_TXWATER_SHIFT))
    {
    }
#endif
    /* Wait last char shoft out */
    while (0 == (base->STAT & LPUART_STAT_TC_MASK))
    {
    }

    /* Clear all status flags */
    temp = (LPUART_STAT_RXEDGIF_MASK | LPUART_STAT_IDLE_MASK | LPUART_STAT_OR_MASK | LPUART_STAT_NF_MASK |
            LPUART_STAT_FE_MASK | LPUART_STAT_PF_MASK);

#if defined(FSL_FEATURE_LPUART_HAS_LIN_BREAK_DETECT) && FSL_FEATURE_LPUART_HAS_LIN_BREAK_DETECT
    temp |= LPUART_STAT_LBKDIF_MASK;
#endif

#if defined(FSL_FEATURE_LPUART_HAS_ADDRESS_MATCHING) && FSL_FEATURE_LPUART_HAS_ADDRESS_MATCHING
    temp |= (LPUART_STAT_MA1F_MASK | LPUART_STAT_MA2F_MASK);
#endif

    base->STAT |= temp;

    /* Disable the module. */
    base->CTRL = 0;

#if !(defined(FSL_SDK_DISABLE_DRIVER_CLOCK_CONTROL) && FSL_SDK_DISABLE_DRIVER_CLOCK_CONTROL)
    uint32_t instance = LPUART_GetInstance(base);

    /* Disable lpuart clock */
    CLOCK_DisableClock(s_lpuartClock[instance]);

#if defined(LPUART_PERIPH_CLOCKS)
    CLOCK_DisableClock(s_lpuartPeriphClocks[instance]);
#endif

#endif /* FSL_SDK_DISABLE_DRIVER_CLOCK_CONTROL */
}

void LPUART_GetDefaultConfig(lpuart_config_t *config)
{
    assert(config);

    config->baudRate_Bps = 115200U;
    config->parityMode = kLPUART_ParityDisabled;
    config->dataBitsCount = kLPUART_EightDataBits;
    config->isMsb = false;
#if defined(FSL_FEATURE_LPUART_HAS_STOP_BIT_CONFIG_SUPPORT) && FSL_FEATURE_LPUART_HAS_STOP_BIT_CONFIG_SUPPORT
    config->stopBitCount = kLPUART_OneStopBit;
#endif
#if defined(FSL_FEATURE_LPUART_HAS_FIFO) && FSL_FEATURE_LPUART_HAS_FIFO
    config->txFifoWatermark = 0;
    config->rxFifoWatermark = 0;
#endif
#if defined(FSL_FEATURE_LPUART_HAS_MODEM_SUPPORT) && FSL_FEATURE_LPUART_HAS_MODEM_SUPPORT
    config->enableRxRTS = false;
    config->enableTxCTS = false;
    config->txCtsConfig = kLPUART_CtsSampleAtStart;
    config->txCtsSource = kLPUART_CtsSourcePin;
#endif
    config->rxIdleType = kLPUART_IdleTypeStartBit;
    config->rxIdleConfig = kLPUART_IdleCharacter1;
    config->enableTx = false;
    config->enableRx = false;
}

status_t LPUART_SetBaudRate(LPUART_Type *base, uint32_t baudRate_Bps, uint32_t srcClock_Hz)
{
    assert(baudRate_Bps);

    uint32_t temp, oldCtrl;
    uint16_t sbr, sbrTemp;
    uint32_t osr, osrTemp, tempDiff, calculatedBaud, baudDiff;

    /* This LPUART instantiation uses a slightly different baud rate calculation
     * The idea is to use the best OSR (over-sampling rate) possible
     * Note, OSR is typically hard-set to 16 in other LPUART instantiations
     * loop to find the best OSR value possible, one that generates minimum baudDiff
     * iterate through the rest of the supported values of OSR */

    baudDiff = baudRate_Bps;
    osr = 0;
    sbr = 0;
    for (osrTemp = 4; osrTemp <= 32; osrTemp++)
    {
        /* calculate the temporary sbr value   */
        sbrTemp = (srcClock_Hz / (baudRate_Bps * osrTemp));
        /*set sbrTemp to 1 if the sourceClockInHz can not satisfy the desired baud rate*/
        if (sbrTemp == 0)
        {
            sbrTemp = 1;
        }
        /* Calculate the baud rate based on the temporary OSR and SBR values */
        calculatedBaud = (srcClock_Hz / (osrTemp * sbrTemp));

        tempDiff = calculatedBaud - baudRate_Bps;

        /* Select the better value between srb and (sbr + 1) */
        if (tempDiff > (baudRate_Bps - (srcClock_Hz / (osrTemp * (sbrTemp + 1)))))
        {
            tempDiff = baudRate_Bps - (srcClock_Hz / (osrTemp * (sbrTemp + 1)));
            sbrTemp++;
        }

        if (tempDiff <= baudDiff)
        {
            baudDiff = tempDiff;
            osr = osrTemp; /* update and store the best OSR value calculated */
            sbr = sbrTemp; /* update store the best SBR value calculated */
        }
    }

    /* Check to see if actual baud rate is within 3% of desired baud rate
     * based on the best calculate OSR value */
    if (baudDiff < ((baudRate_Bps / 100) * 3))
    {
        /* Store CTRL before disable Tx and Rx */
        oldCtrl = base->CTRL;

        /* Disable LPUART TX RX before setting. */
        base->CTRL &= ~(LPUART_CTRL_TE_MASK | LPUART_CTRL_RE_MASK);

        temp = base->BAUD;

        /* Acceptable baud rate, check if OSR is between 4x and 7x oversampling.
         * If so, then "BOTHEDGE" sampling must be turned on */
        if ((osr > 3) && (osr < 8))
        {
            temp |= LPUART_BAUD_BOTHEDGE_MASK;
        }

        /* program the osr value (bit value is one less than actual value) */
        temp &= ~LPUART_BAUD_OSR_MASK;
        temp |= LPUART_BAUD_OSR(osr - 1);

        /* write the sbr value to the BAUD registers */
        temp &= ~LPUART_BAUD_SBR_MASK;
        base->BAUD = temp | LPUART_BAUD_SBR(sbr);

        /* Restore CTRL. */
        base->CTRL = oldCtrl;

        return kStatus_Success;
    }
    else
    {
        /* Unacceptable baud rate difference of more than 3%*/
        return kStatus_LPUART_BaudrateNotSupport;
    }
}

void LPUART_EnableInterrupts(LPUART_Type *base, uint32_t mask)
{
    base->BAUD |= ((mask << 8) & (LPUART_BAUD_LBKDIE_MASK | LPUART_BAUD_RXEDGIE_MASK));
#if defined(FSL_FEATURE_LPUART_HAS_FIFO) && FSL_FEATURE_LPUART_HAS_FIFO
    base->FIFO = (base->FIFO & ~(LPUART_FIFO_TXOF_MASK | LPUART_FIFO_RXUF_MASK)) |
                 ((mask << 8) & (LPUART_FIFO_TXOFE_MASK | LPUART_FIFO_RXUFE_MASK));
#endif
    mask &= 0xFFFFFF00U;
    base->CTRL |= mask;
}

void LPUART_DisableInterrupts(LPUART_Type *base, uint32_t mask)
{
    base->BAUD &= ~((mask << 8) & (LPUART_BAUD_LBKDIE_MASK | LPUART_BAUD_RXEDGIE_MASK));
#if defined(FSL_FEATURE_LPUART_HAS_FIFO) && FSL_FEATURE_LPUART_HAS_FIFO
    base->FIFO = (base->FIFO & ~(LPUART_FIFO_TXOF_MASK | LPUART_FIFO_RXUF_MASK)) &
                 ~((mask << 8) & (LPUART_FIFO_TXOFE_MASK | LPUART_FIFO_RXUFE_MASK));
#endif
    mask &= 0xFFFFFF00U;
    base->CTRL &= ~mask;
}

uint32_t LPUART_GetEnabledInterrupts(LPUART_Type *base)
{
    uint32_t temp;
    temp = (base->BAUD & (LPUART_BAUD_LBKDIE_MASK | LPUART_BAUD_RXEDGIE_MASK)) >> 8;
#if defined(FSL_FEATURE_LPUART_HAS_FIFO) && FSL_FEATURE_LPUART_HAS_FIFO
    temp |= (base->FIFO & (LPUART_FIFO_TXOFE_MASK | LPUART_FIFO_RXUFE_MASK)) >> 8;
#endif
    temp |= (base->CTRL & 0xFF0C000);

    return temp;
}

uint32_t LPUART_GetStatusFlags(LPUART_Type *base)
{
    uint32_t temp;
    temp = base->STAT;
#if defined(FSL_FEATURE_LPUART_HAS_FIFO) && FSL_FEATURE_LPUART_HAS_FIFO
    temp |= (base->FIFO &
             (LPUART_FIFO_TXEMPT_MASK | LPUART_FIFO_RXEMPT_MASK | LPUART_FIFO_TXOF_MASK | LPUART_FIFO_RXUF_MASK)) >>
            16;
#endif
    return temp;
}

status_t LPUART_ClearStatusFlags(LPUART_Type *base, uint32_t mask)
{
    uint32_t temp;
    status_t status;
#if defined(FSL_FEATURE_LPUART_HAS_FIFO) && FSL_FEATURE_LPUART_HAS_FIFO
    temp = (uint32_t)base->FIFO;
    temp &= (uint32_t)(~(LPUART_FIFO_TXOF_MASK | LPUART_FIFO_RXUF_MASK));
    temp |= (mask << 16) & (LPUART_FIFO_TXOF_MASK | LPUART_FIFO_RXUF_MASK);
    base->FIFO = temp;
#endif
    temp = (uint32_t)base->STAT;
#if defined(FSL_FEATURE_LPUART_HAS_LIN_BREAK_DETECT) && FSL_FEATURE_LPUART_HAS_LIN_BREAK_DETECT
    temp &= (uint32_t)(~(LPUART_STAT_LBKDIF_MASK));
    temp |= mask & LPUART_STAT_LBKDIF_MASK;
#endif
    temp &= (uint32_t)(~(LPUART_STAT_RXEDGIF_MASK | LPUART_STAT_IDLE_MASK | LPUART_STAT_OR_MASK | LPUART_STAT_NF_MASK |
                         LPUART_STAT_FE_MASK | LPUART_STAT_PF_MASK));
    temp |= mask & (LPUART_STAT_RXEDGIF_MASK | LPUART_STAT_IDLE_MASK | LPUART_STAT_OR_MASK | LPUART_STAT_NF_MASK |
                    LPUART_STAT_FE_MASK | LPUART_STAT_PF_MASK);
#if defined(FSL_FEATURE_LPUART_HAS_ADDRESS_MATCHING) && FSL_FEATURE_LPUART_HAS_ADDRESS_MATCHING
    temp &= (uint32_t)(~(LPUART_STAT_MA2F_MASK | LPUART_STAT_MA1F_MASK));
    temp |= mask & (LPUART_STAT_MA2F_MASK | LPUART_STAT_MA1F_MASK);
#endif
    base->STAT = temp;
    /* If some flags still pending. */
    if (mask & LPUART_GetStatusFlags(base))
    {
        /* Some flags can only clear or set by the hardware itself, these flags are: kLPUART_TxDataRegEmptyFlag,
        kLPUART_TransmissionCompleteFlag, kLPUART_RxDataRegFullFlag, kLPUART_RxActiveFlag,
        kLPUART_NoiseErrorInRxDataRegFlag, kLPUART_ParityErrorInRxDataRegFlag,
        kLPUART_TxFifoEmptyFlag, kLPUART_RxFifoEmptyFlag. */
        status = kStatus_LPUART_FlagCannotClearManually; /* flags can not clear manually */
    }
    else
    {
        status = kStatus_Success;
    }

    return status;
}

void LPUART_WriteBlocking(LPUART_Type *base, const uint8_t *data, size_t length)
{
    assert(data);

    /* This API can only ensure that the data is written into the data buffer but can't
    ensure all data in the data buffer are sent into the transmit shift buffer. */
    while (length--)
    {
        while (!(base->STAT & LPUART_STAT_TDRE_MASK))
        {
        }
        base->DATA = *(data++);
    }
}

status_t LPUART_ReadBlocking(LPUART_Type *base, uint8_t *data, size_t length)
{
    assert(data);

    uint32_t statusFlag;
#if defined(FSL_FEATURE_LPUART_HAS_7BIT_DATA_SUPPORT) && FSL_FEATURE_LPUART_HAS_7BIT_DATA_SUPPORT
    uint32_t ctrl = base->CTRL;
    bool isSevenDataBits =
        ((ctrl & LPUART_CTRL_M7_MASK) ||
         ((!(ctrl & LPUART_CTRL_M7_MASK)) && (!(ctrl & LPUART_CTRL_M_MASK)) && (ctrl & LPUART_CTRL_PE_MASK)));
#endif

    while (length--)
    {
#if defined(FSL_FEATURE_LPUART_HAS_FIFO) && FSL_FEATURE_LPUART_HAS_FIFO
        while (0 == ((base->WATER & LPUART_WATER_RXCOUNT_MASK) >> LPUART_WATER_RXCOUNT_SHIFT))
#else
        while (!(base->STAT & LPUART_STAT_RDRF_MASK))
#endif
        {
            statusFlag = LPUART_GetStatusFlags(base);

            if (statusFlag & kLPUART_RxOverrunFlag)
            {
                LPUART_ClearStatusFlags(base, kLPUART_RxOverrunFlag);
                return kStatus_LPUART_RxHardwareOverrun;
            }

            if (statusFlag & kLPUART_NoiseErrorFlag)
            {
                LPUART_ClearStatusFlags(base, kLPUART_NoiseErrorFlag);
                return kStatus_LPUART_NoiseError;
            }

            if (statusFlag & kLPUART_FramingErrorFlag)
            {
                LPUART_ClearStatusFlags(base, kLPUART_FramingErrorFlag);
                return kStatus_LPUART_FramingError;
            }

            if (statusFlag & kLPUART_ParityErrorFlag)
            {
                LPUART_ClearStatusFlags(base, kLPUART_ParityErrorFlag);
                return kStatus_LPUART_ParityError;
            }
        }
#if defined(FSL_FEATURE_LPUART_HAS_7BIT_DATA_SUPPORT) && FSL_FEATURE_LPUART_HAS_7BIT_DATA_SUPPORT
        if (isSevenDataBits)
        {
            *(data++) = (base->DATA & 0x7F);
        }
        else
        {
            *(data++) = base->DATA;
        }
#else
        *(data++) = base->DATA;
#endif
    }

    return kStatus_Success;
}

void LPUART_TransferCreateHandle(LPUART_Type *base,
                                 lpuart_handle_t *handle,
                                 lpuart_transfer_callback_t callback,
                                 void *userData)
{
    assert(handle);

    uint32_t instance;
#if defined(FSL_FEATURE_LPUART_HAS_7BIT_DATA_SUPPORT) && FSL_FEATURE_LPUART_HAS_7BIT_DATA_SUPPORT
    uint32_t ctrl = base->CTRL;
    bool isSevenDataBits =
        ((ctrl & LPUART_CTRL_M7_MASK) ||
         ((!(ctrl & LPUART_CTRL_M7_MASK)) && (!(ctrl & LPUART_CTRL_M_MASK)) && (ctrl & LPUART_CTRL_PE_MASK)));
#endif

    /* Zero the handle. */
    memset(handle, 0, sizeof(lpuart_handle_t));

    /* Set the TX/RX state. */
    handle->rxState = kLPUART_RxIdle;
    handle->txState = kLPUART_TxIdle;

    /* Set the callback and user data. */
    handle->callback = callback;
    handle->userData = userData;

#if defined(FSL_FEATURE_LPUART_HAS_7BIT_DATA_SUPPORT) && FSL_FEATURE_LPUART_HAS_7BIT_DATA_SUPPORT
    /* Initial seven data bits flag */
    handle->isSevenDataBits = isSevenDataBits;
#endif

    /* Get instance from peripheral base address. */
    instance = LPUART_GetInstance(base);

    /* Save the handle in global variables to support the double weak mechanism. */
    s_lpuartHandle[instance] = handle;

    s_lpuartIsr = LPUART_TransferHandleIRQ;

/* Enable interrupt in NVIC. */
#if defined(FSL_FEATURE_LPUART_HAS_SEPARATE_RX_TX_IRQ) && FSL_FEATURE_LPUART_HAS_SEPARATE_RX_TX_IRQ
    EnableIRQ(s_lpuartRxIRQ[instance]);
    EnableIRQ(s_lpuartTxIRQ[instance]);
#else
    EnableIRQ(s_lpuartIRQ[instance]);
#endif
}

void LPUART_TransferStartRingBuffer(LPUART_Type *base,
                                    lpuart_handle_t *handle,
                                    uint8_t *ringBuffer,
                                    size_t ringBufferSize)
{
    assert(handle);
    assert(ringBuffer);

    /* Setup the ring buffer address */
    handle->rxRingBuffer = ringBuffer;
    handle->rxRingBufferSize = ringBufferSize;
    handle->rxRingBufferHead = 0U;
    handle->rxRingBufferTail = 0U;

    /* Enable the interrupt to accept the data when user need the ring buffer. */
    LPUART_EnableInterrupts(base, kLPUART_RxDataRegFullInterruptEnable | kLPUART_RxOverrunInterruptEnable);
}

void LPUART_TransferStopRingBuffer(LPUART_Type *base, lpuart_handle_t *handle)
{
    assert(handle);

    if (handle->rxState == kLPUART_RxIdle)
    {
        LPUART_DisableInterrupts(base, kLPUART_RxDataRegFullInterruptEnable | kLPUART_RxOverrunInterruptEnable);
    }

    handle->rxRingBuffer = NULL;
    handle->rxRingBufferSize = 0U;
    handle->rxRingBufferHead = 0U;
    handle->rxRingBufferTail = 0U;
}

status_t LPUART_TransferSendNonBlocking(LPUART_Type *base, lpuart_handle_t *handle, lpuart_transfer_t *xfer)
{
    assert(handle);
    assert(xfer);
    assert(xfer->data);
    assert(xfer->dataSize);

    status_t status;

    /* Return error if current TX busy. */
    if (kLPUART_TxBusy == handle->txState)
    {
        status = kStatus_LPUART_TxBusy;
    }
    else
    {
        handle->txData = xfer->data;
        handle->txDataSize = xfer->dataSize;
        handle->txDataSizeAll = xfer->dataSize;
        handle->txState = kLPUART_TxBusy;

        /* Enable transmiter interrupt. */
        LPUART_EnableInterrupts(base, kLPUART_TxDataRegEmptyInterruptEnable);

        status = kStatus_Success;
    }

    return status;
}

void LPUART_TransferAbortSend(LPUART_Type *base, lpuart_handle_t *handle)
{
    assert(handle);

    LPUART_DisableInterrupts(base, kLPUART_TxDataRegEmptyInterruptEnable | kLPUART_TransmissionCompleteInterruptEnable);

    handle->txDataSize = 0;
    handle->txState = kLPUART_TxIdle;
}

status_t LPUART_TransferGetSendCount(LPUART_Type *base, lpuart_handle_t *handle, uint32_t *count)
{
    assert(handle);
    assert(count);

    if (kLPUART_TxIdle == handle->txState)
    {
        return kStatus_NoTransferInProgress;
    }

    *count = handle->txDataSizeAll - handle->txDataSize;

    return kStatus_Success;
}

status_t LPUART_TransferReceiveNonBlocking(LPUART_Type *base,
                                           lpuart_handle_t *handle,
                                           lpuart_transfer_t *xfer,
                                           size_t *receivedBytes)
{
    assert(handle);
    assert(xfer);
    assert(xfer->data);
    assert(xfer->dataSize);

    uint32_t i;
    status_t status;
    /* How many bytes to copy from ring buffer to user memory. */
    size_t bytesToCopy = 0U;
    /* How many bytes to receive. */
    size_t bytesToReceive;
    /* How many bytes currently have received. */
    size_t bytesCurrentReceived;

    /* How to get data:
       1. If RX ring buffer is not enabled, then save xfer->data and xfer->dataSize
          to lpuart handle, enable interrupt to store received data to xfer->data. When
          all data received, trigger callback.
       2. If RX ring buffer is enabled and not empty, get data from ring buffer first.
          If there are enough data in ring buffer, copy them to xfer->data and return.
          If there are not enough data in ring buffer, copy all of them to xfer->data,
          save the xfer->data remained empty space to lpuart handle, receive data
          to this empty space and trigger callback when finished. */

    if (kLPUART_RxBusy == handle->rxState)
    {
        status = kStatus_LPUART_RxBusy;
    }
    else
    {
        bytesToReceive = xfer->dataSize;
        bytesCurrentReceived = 0;

        /* If RX ring buffer is used. */
        if (handle->rxRingBuffer)
        {
            /* Disable LPUART RX IRQ, protect ring buffer. */
            LPUART_DisableInterrupts(base, kLPUART_RxDataRegFullInterruptEnable);

            /* How many bytes in RX ring buffer currently. */
            bytesToCopy = LPUART_TransferGetRxRingBufferLength(base, handle);

            if (bytesToCopy)
            {
                bytesToCopy = MIN(bytesToReceive, bytesToCopy);

                bytesToReceive -= bytesToCopy;

                /* Copy data from ring buffer to user memory. */
                for (i = 0U; i < bytesToCopy; i++)
                {
                    xfer->data[bytesCurrentReceived++] = handle->rxRingBuffer[handle->rxRingBufferTail];

                    /* Wrap to 0. Not use modulo (%) because it might be large and slow. */
                    if (handle->rxRingBufferTail + 1U == handle->rxRingBufferSize)
                    {
                        handle->rxRingBufferTail = 0U;
                    }
                    else
                    {
                        handle->rxRingBufferTail++;
                    }
                }
            }

            /* If ring buffer does not have enough data, still need to read more data. */
            if (bytesToReceive)
            {
                /* No data in ring buffer, save the request to LPUART handle. */
                handle->rxData = xfer->data + bytesCurrentReceived;
                handle->rxDataSize = bytesToReceive;
                handle->rxDataSizeAll = bytesToReceive;
                handle->rxState = kLPUART_RxBusy;
            }
            /* Enable LPUART RX IRQ if previously enabled. */
            LPUART_EnableInterrupts(base, kLPUART_RxDataRegFullInterruptEnable);

            /* Call user callback since all data are received. */
            if (0 == bytesToReceive)
            {
                if (handle->callback)
                {
                    handle->callback(base, handle, kStatus_LPUART_RxIdle, handle->userData);
                }
            }
        }
        /* Ring buffer not used. */
        else
        {
            handle->rxData = xfer->data + bytesCurrentReceived;
            handle->rxDataSize = bytesToReceive;
            handle->rxDataSizeAll = bytesToReceive;
            handle->rxState = kLPUART_RxBusy;

            /* Enable RX interrupt. */
            LPUART_EnableInterrupts(base, kLPUART_RxDataRegFullInterruptEnable | kLPUART_RxOverrunInterruptEnable |
                                              kLPUART_IdleLineInterruptEnable);
        }

        /* Return the how many bytes have read. */
        if (receivedBytes)
        {
            *receivedBytes = bytesCurrentReceived;
        }

        status = kStatus_Success;
    }

    return status;
}

void LPUART_TransferAbortReceive(LPUART_Type *base, lpuart_handle_t *handle)
{
    assert(handle);

    /* Only abort the receive to handle->rxData, the RX ring buffer is still working. */
    if (!handle->rxRingBuffer)
    {
        /* Disable RX interrupt. */
        LPUART_DisableInterrupts(base, kLPUART_RxDataRegFullInterruptEnable | kLPUART_RxOverrunInterruptEnable |
                                           kLPUART_IdleLineInterruptEnable);
    }

    handle->rxDataSize = 0U;
    handle->rxState = kLPUART_RxIdle;
}

status_t LPUART_TransferGetReceiveCount(LPUART_Type *base, lpuart_handle_t *handle, uint32_t *count)
{
    assert(handle);
    assert(count);

    if (kLPUART_RxIdle == handle->rxState)
    {
        return kStatus_NoTransferInProgress;
    }

    *count = handle->rxDataSizeAll - handle->rxDataSize;

    return kStatus_Success;
}

void LPUART_TransferHandleIRQ(LPUART_Type *base, lpuart_handle_t *handle)
{
    assert(handle);

    uint8_t count;
    uint8_t tempCount;

    /* If RX overrun. */
    if (LPUART_STAT_OR_MASK & base->STAT)
    {
        /* Clear overrun flag, otherwise the RX does not work. */
        base->STAT = ((base->STAT & 0x3FE00000U) | LPUART_STAT_OR_MASK);

        /* Trigger callback. */
        if (handle->callback)
        {
            handle->callback(base, handle, kStatus_LPUART_RxHardwareOverrun, handle->userData);
        }
    }

    /* If IDLE flag is set and the IDLE interrupt is enabled. */
    if ((LPUART_STAT_IDLE_MASK & base->STAT) && (LPUART_CTRL_ILIE_MASK & base->CTRL))
    {
#if defined(FSL_FEATURE_LPUART_HAS_FIFO) && FSL_FEATURE_LPUART_HAS_FIFO
        count = ((uint8_t)((base->WATER & LPUART_WATER_RXCOUNT_MASK) >> LPUART_WATER_RXCOUNT_SHIFT));

        while ((count) && (handle->rxDataSize))
        {
            tempCount = MIN(handle->rxDataSize, count);

            /* Using non block API to read the data from the registers. */
            LPUART_ReadNonBlocking(base, handle->rxData, tempCount);
            handle->rxData += tempCount;
            handle->rxDataSize -= tempCount;
            count -= tempCount;

            /* If rxDataSize is 0, disable idle line interrupt.*/
            if (!(handle->rxDataSize))
            {
                handle->rxState = kLPUART_RxIdle;

                LPUART_DisableInterrupts(base, kLPUART_RxDataRegFullInterruptEnable | kLPUART_RxOverrunInterruptEnable);
                if (handle->callback)
                {
                    handle->callback(base, handle, kStatus_LPUART_RxIdle, handle->userData);
                }
            }
        }
#endif
        /* Clear IDLE flag.*/
        base->STAT |= LPUART_STAT_IDLE_MASK;

        /* If rxDataSize is 0, disable idle line interrupt.*/
        if (!(handle->rxDataSize))
        {
            LPUART_DisableInterrupts(base, kLPUART_IdleLineInterruptEnable);
        }
        /* If callback is not NULL and rxDataSize is not 0. */
        if ((handle->callback) && (handle->rxDataSize))
        {
            handle->callback(base, handle, kStatus_LPUART_IdleLineDetected, handle->userData);
        }
    }
    /* Receive data register full */
    if ((LPUART_STAT_RDRF_MASK & base->STAT) && (LPUART_CTRL_RIE_MASK & base->CTRL))
    {
/* Get the size that can be stored into buffer for this interrupt. */
#if defined(FSL_FEATURE_LPUART_HAS_FIFO) && FSL_FEATURE_LPUART_HAS_FIFO
        count = ((uint8_t)((base->WATER & LPUART_WATER_RXCOUNT_MASK) >> LPUART_WATER_RXCOUNT_SHIFT));
#else
        count = 1;
#endif

        /* If handle->rxDataSize is not 0, first save data to handle->rxData. */
        while ((count) && (handle->rxDataSize))
        {
#if defined(FSL_FEATURE_LPUART_HAS_FIFO) && FSL_FEATURE_LPUART_HAS_FIFO
            tempCount = MIN(handle->rxDataSize, count);
#else
            tempCount = 1;
#endif

            /* Using non block API to read the data from the registers. */
            LPUART_ReadNonBlocking(base, handle->rxData, tempCount);
            handle->rxData += tempCount;
            handle->rxDataSize -= tempCount;
            count -= tempCount;

            /* If all the data required for upper layer is ready, trigger callback. */
            if (!handle->rxDataSize)
            {
                handle->rxState = kLPUART_RxIdle;

                if (handle->callback)
                {
                    handle->callback(base, handle, kStatus_LPUART_RxIdle, handle->userData);
                }
            }
        }

        /* If use RX ring buffer, receive data to ring buffer. */
        if (handle->rxRingBuffer)
        {
            while (count--)
            {
                /* If RX ring buffer is full, trigger callback to notify over run. */
                if (LPUART_TransferIsRxRingBufferFull(base, handle))
                {
                    if (handle->callback)
                    {
                        handle->callback(base, handle, kStatus_LPUART_RxRingBufferOverrun, handle->userData);
                    }
                }

                /* If ring buffer is still full after callback function, the oldest data is overrided. */
                if (LPUART_TransferIsRxRingBufferFull(base, handle))
                {
                    /* Increase handle->rxRingBufferTail to make room for new data. */
                    if (handle->rxRingBufferTail + 1U == handle->rxRingBufferSize)
                    {
                        handle->rxRingBufferTail = 0U;
                    }
                    else
                    {
                        handle->rxRingBufferTail++;
                    }
                }

/* Read data. */
#if defined(FSL_FEATURE_LPUART_HAS_7BIT_DATA_SUPPORT) && FSL_FEATURE_LPUART_HAS_7BIT_DATA_SUPPORT
                if (handle->isSevenDataBits)
                {
                    handle->rxRingBuffer[handle->rxRingBufferHead] = (base->DATA & 0x7F);
                }
                else
                {
                    handle->rxRingBuffer[handle->rxRingBufferHead] = base->DATA;
                }
#else
                handle->rxRingBuffer[handle->rxRingBufferHead] = base->DATA;
#endif

                /* Increase handle->rxRingBufferHead. */
                if (handle->rxRingBufferHead + 1U == handle->rxRingBufferSize)
                {
                    handle->rxRingBufferHead = 0U;
                }
                else
                {
                    handle->rxRingBufferHead++;
                }
            }
        }
        /* If no receive requst pending, stop RX interrupt. */
        else if (!handle->rxDataSize)
        {
            LPUART_DisableInterrupts(base, kLPUART_RxDataRegFullInterruptEnable | kLPUART_RxOverrunInterruptEnable);
        }
        else
        {
        }
    }

    /* Send data register empty and the interrupt is enabled. */
    if ((base->STAT & LPUART_STAT_TDRE_MASK) && (base->CTRL & LPUART_CTRL_TIE_MASK))
    {
/* Get the bytes that available at this moment. */
#if defined(FSL_FEATURE_LPUART_HAS_FIFO) && FSL_FEATURE_LPUART_HAS_FIFO
        count = FSL_FEATURE_LPUART_FIFO_SIZEn(base) -
                ((base->WATER & LPUART_WATER_TXCOUNT_MASK) >> LPUART_WATER_TXCOUNT_SHIFT);
#else
        count = 1;
#endif

        while ((count) && (handle->txDataSize))
        {
#if defined(FSL_FEATURE_LPUART_HAS_FIFO) && FSL_FEATURE_LPUART_HAS_FIFO
            tempCount = MIN(handle->txDataSize, count);
#else
            tempCount = 1;
#endif

            /* Using non block API to write the data to the registers. */
            LPUART_WriteNonBlocking(base, handle->txData, tempCount);
            handle->txData += tempCount;
            handle->txDataSize -= tempCount;
            count -= tempCount;

            /* If all the data are written to data register, notify user with the callback, then TX finished. */
            if (!handle->txDataSize)
            {
                handle->txState = kLPUART_TxIdle;

                /* Disable TX register empty interrupt. */
                base->CTRL = (base->CTRL & ~LPUART_CTRL_TIE_MASK);

                /* Trigger callback. */
                if (handle->callback)
                {
                    handle->callback(base, handle, kStatus_LPUART_TxIdle, handle->userData);
                }
            }
        }
    }
}

void LPUART_TransferHandleErrorIRQ(LPUART_Type *base, lpuart_handle_t *handle)
{
    /* To be implemented by User. */
}
#if defined(FSL_FEATURE_LPUART_HAS_SHARED_IRQ0_IRQ1) && FSL_FEATURE_LPUART_HAS_SHARED_IRQ0_IRQ1
#if defined(FSL_FEATURE_LPUART_HAS_SEPARATE_RX_TX_IRQ) && FSL_FEATURE_LPUART_HAS_SEPARATE_RX_TX_IRQ
void LPUART0_LPUART1_RX_DriverIRQHandler(void)
{
    if (CLOCK_isEnabledClock(s_lpuartClock[0]))
    {
        if ((LPUART_STAT_OR_MASK & LPUART0->STAT) ||
            ((LPUART_STAT_RDRF_MASK & LPUART0->STAT) && (LPUART_CTRL_RIE_MASK & LPUART0->CTRL)))
        {
            s_lpuartIsr(LPUART0, s_lpuartHandle[0]);
        }
    }
    if (CLOCK_isEnabledClock(s_lpuartClock[1]))
    {
        if ((LPUART_STAT_OR_MASK & LPUART1->STAT) ||
            ((LPUART_STAT_RDRF_MASK & LPUART1->STAT) && (LPUART_CTRL_RIE_MASK & LPUART1->CTRL)))
        {
            s_lpuartIsr(LPUART1, s_lpuartHandle[1]);
        }
    }
}
void LPUART0_LPUART1_TX_DriverIRQHandler(void)
{
    if (CLOCK_isEnabledClock(s_lpuartClock[0]))
    {
        if ((LPUART_STAT_OR_MASK & LPUART0->STAT) ||
            ((LPUART0->STAT & LPUART_STAT_TDRE_MASK) && (LPUART0->CTRL & LPUART_CTRL_TIE_MASK)))
        {
            s_lpuartIsr(LPUART0, s_lpuartHandle[0]);
        }
    }
    if (CLOCK_isEnabledClock(s_lpuartClock[1]))
    {
        if ((LPUART_STAT_OR_MASK & LPUART1->STAT) ||
            ((LPUART1->STAT & LPUART_STAT_TDRE_MASK) && (LPUART1->CTRL & LPUART_CTRL_TIE_MASK)))
        {
            s_lpuartIsr(LPUART1, s_lpuartHandle[1]);
        }
    }
}
#else
void LPUART0_LPUART1_DriverIRQHandler(void)
{
    if (CLOCK_isEnabledClock(s_lpuartClock[0]))
    {
        if ((LPUART_STAT_OR_MASK & LPUART0->STAT) ||
            ((LPUART_STAT_RDRF_MASK & LPUART0->STAT) && (LPUART_CTRL_RIE_MASK & LPUART0->CTRL)) ||
            ((LPUART0->STAT & LPUART_STAT_TDRE_MASK) && (LPUART0->CTRL & LPUART_CTRL_TIE_MASK)))
        {
            s_lpuartIsr(LPUART0, s_lpuartHandle[0]);
        }
    }
    if (CLOCK_isEnabledClock(s_lpuartClock[1]))
    {
        if ((LPUART_STAT_OR_MASK & LPUART1->STAT) ||
            ((LPUART_STAT_RDRF_MASK & LPUART1->STAT) && (LPUART_CTRL_RIE_MASK & LPUART1->CTRL)) ||
            ((LPUART1->STAT & LPUART_STAT_TDRE_MASK) && (LPUART1->CTRL & LPUART_CTRL_TIE_MASK)))
        {
            s_lpuartIsr(LPUART1, s_lpuartHandle[1]);
        }
    }
}
#endif
#endif

#if defined(LPUART0)
#if !(defined(FSL_FEATURE_LPUART_HAS_SHARED_IRQ0_IRQ1) && FSL_FEATURE_LPUART_HAS_SHARED_IRQ0_IRQ1)
#if defined(FSL_FEATURE_LPUART_HAS_SEPARATE_RX_TX_IRQ) && FSL_FEATURE_LPUART_HAS_SEPARATE_RX_TX_IRQ
void LPUART0_TX_DriverIRQHandler(void)
{
    s_lpuartIsr(LPUART0, s_lpuartHandle[0]);
}
void LPUART0_RX_DriverIRQHandler(void)
{
    s_lpuartIsr(LPUART0, s_lpuartHandle[0]);
}
#else
void LPUART0_DriverIRQHandler(void)
{
    s_lpuartIsr(LPUART0, s_lpuartHandle[0]);
}
#endif
#endif
#endif

#if defined(LPUART1)
#if !(defined(FSL_FEATURE_LPUART_HAS_SHARED_IRQ0_IRQ1) && FSL_FEATURE_LPUART_HAS_SHARED_IRQ0_IRQ1)
#if defined(FSL_FEATURE_LPUART_HAS_SEPARATE_RX_TX_IRQ) && FSL_FEATURE_LPUART_HAS_SEPARATE_RX_TX_IRQ
void LPUART1_TX_DriverIRQHandler(void)
{
    s_lpuartIsr(LPUART1, s_lpuartHandle[1]);
}
void LPUART1_RX_DriverIRQHandler(void)
{
    s_lpuartIsr(LPUART1, s_lpuartHandle[1]);
}
#else
void LPUART1_DriverIRQHandler(void)
{
    s_lpuartIsr(LPUART1, s_lpuartHandle[1]);
}
#endif
#endif
#endif

#if defined(LPUART2)
#if defined(FSL_FEATURE_LPUART_HAS_SEPARATE_RX_TX_IRQ) && FSL_FEATURE_LPUART_HAS_SEPARATE_RX_TX_IRQ
void LPUART2_TX_DriverIRQHandler(void)
{
    s_lpuartIsr(LPUART2, s_lpuartHandle[2]);
}
void LPUART2_RX_DriverIRQHandler(void)
{
    s_lpuartIsr(LPUART2, s_lpuartHandle[2]);
}
#else
void LPUART2_DriverIRQHandler(void)
{
    s_lpuartIsr(LPUART2, s_lpuartHandle[2]);
}
#endif
#endif

#if defined(LPUART3)
#if defined(FSL_FEATURE_LPUART_HAS_SEPARATE_RX_TX_IRQ) && FSL_FEATURE_LPUART_HAS_SEPARATE_RX_TX_IRQ
void LPUART3_TX_DriverIRQHandler(void)
{
    s_lpuartIsr(LPUART3, s_lpuartHandle[3]);
}
void LPUART3_RX_DriverIRQHandler(void)
{
    s_lpuartIsr(LPUART3, s_lpuartHandle[3]);
}
#else
void LPUART3_DriverIRQHandler(void)
{
    s_lpuartIsr(LPUART3, s_lpuartHandle[3]);
}
#endif
#endif

#if defined(LPUART4)
#if defined(FSL_FEATURE_LPUART_HAS_SEPARATE_RX_TX_IRQ) && FSL_FEATURE_LPUART_HAS_SEPARATE_RX_TX_IRQ
void LPUART4_TX_DriverIRQHandler(void)
{
    s_lpuartIsr(LPUART4, s_lpuartHandle[4]);
}
void LPUART4_RX_DriverIRQHandler(void)
{
    s_lpuartIsr(LPUART4, s_lpuartHandle[4]);
}
#else
void LPUART4_DriverIRQHandler(void)
{
    s_lpuartIsr(LPUART4, s_lpuartHandle[4]);
}
#endif
#endif

#if defined(LPUART5)
#if defined(FSL_FEATURE_LPUART_HAS_SEPARATE_RX_TX_IRQ) && FSL_FEATURE_LPUART_HAS_SEPARATE_RX_TX_IRQ
void LPUART5_TX_DriverIRQHandler(void)
{
    s_lpuartIsr(LPUART5, s_lpuartHandle[5]);
}
void LPUART5_RX_DriverIRQHandler(void)
{
    s_lpuartIsr(LPUART5, s_lpuartHandle[5]);
}
#else
void LPUART5_DriverIRQHandler(void)
{
    s_lpuartIsr(LPUART5, s_lpuartHandle[5]);
}
#endif
#endif

#if defined(CM4_0_LPUART)
void M4_0_LPUART_DriverIRQHandler(void)
{
    s_lpuartIsr(CM4_0_LPUART, s_lpuartHandle[LPUART_GetInstance(CM4_0_LPUART)]);
}
#endif

#if defined(CM4_1_LPUART)
void M4_1_LPUART_DriverIRQHandler(void)
{
    s_lpuartIsr(CM4_1_LPUART, s_lpuartHandle[LPUART_GetInstance(CM4_1_LPUART)]);
}
#endif

#if defined(DMA_LPUART0)
void DMA_UART0_INT_IRQHandler(void)
{
    s_lpuartIsr(DMA_LPUART0, s_lpuartHandle[LPUART_GetInstance(DMA_LPUART0)]);
}
#endif

#if defined(DMA_LPUART1)
void DMA_UART1_INT_IRQHandler(void)
{
    s_lpuartIsr(DMA_LPUART1, s_lpuartHandle[LPUART_GetInstance(DMA_LPUART1)]);
}
#endif

#if defined(DMA_LPUART2)
void DMA_UART2_INT_IRQHandler(void)
{
    s_lpuartIsr(DMA_LPUART2, s_lpuartHandle[LPUART_GetInstance(DMA_LPUART2)]);
}
#endif

#if defined(DMA_LPUART3)
void DMA_UART3_INT_IRQHandler(void)
{
    s_lpuartIsr(DMA_LPUART3, s_lpuartHandle[LPUART_GetInstance(DMA_LPUART3)]);
}
#endif

#if defined(DMA_LPUART4)
void DMA_UART4_INT_IRQHandler(void)
{
    s_lpuartIsr(DMA_LPUART4, s_lpuartHandle[LPUART_GetInstance(DMA_LPUART4)]);
}
#endif
