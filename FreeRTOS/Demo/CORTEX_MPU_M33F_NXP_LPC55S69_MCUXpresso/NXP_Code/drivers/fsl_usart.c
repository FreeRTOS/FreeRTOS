/*
 * Copyright (c) 2016, Freescale Semiconductor, Inc.
 * Copyright 2016-2019 NXP
 * All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "fsl_usart.h"
#include "fsl_device_registers.h"
#include "fsl_flexcomm.h"

/*******************************************************************************
 * Definitions
 ******************************************************************************/

/* Component ID definition, used by tools. */
#ifndef FSL_COMPONENT_ID
#define FSL_COMPONENT_ID "platform.drivers.flexcomm_usart"
#endif

/*!
 * @brief Used for conversion from `flexcomm_usart_irq_handler_t` to `flexcomm_irq_handler_t`
 */
typedef union usart_to_flexcomm
{
    flexcomm_usart_irq_handler_t usart_master_handler;
    flexcomm_irq_handler_t flexcomm_handler;
} usart_to_flexcomm_t;

enum
{
    kUSART_TxIdle, /* TX idle. */
    kUSART_TxBusy, /* TX busy. */
    kUSART_RxIdle, /* RX idle. */
    kUSART_RxBusy  /* RX busy. */
};

/*******************************************************************************
 * Variables
 ******************************************************************************/

/*! @brief IRQ name array */
static const IRQn_Type s_usartIRQ[] = USART_IRQS;

/*! @brief Array to map USART instance number to base address. */
static const uint32_t s_usartBaseAddrs[FSL_FEATURE_SOC_USART_COUNT] = USART_BASE_ADDRS;

/*******************************************************************************
 * Code
 ******************************************************************************/

/* Get the index corresponding to the USART */
/*! brief Returns instance number for USART peripheral base address. */
uint32_t USART_GetInstance(USART_Type *base)
{
    uint32_t i;

    for (i = 0; i < (uint32_t)FSL_FEATURE_SOC_USART_COUNT; i++)
    {
        if ((uint32_t)base == s_usartBaseAddrs[i])
        {
            break;
        }
    }

    assert(i < FSL_FEATURE_SOC_USART_COUNT);
    return i;
}

/*!
 * brief Get the length of received data in RX ring buffer.
 *
 * param handle USART handle pointer.
 * return Length of received data in RX ring buffer.
 */
size_t USART_TransferGetRxRingBufferLength(usart_handle_t *handle)
{
    size_t size;

    /* Check arguments */
    assert(NULL != handle);
    uint16_t rxRingBufferHead = handle->rxRingBufferHead;
    uint16_t rxRingBufferTail = handle->rxRingBufferTail;

    if (rxRingBufferTail > rxRingBufferHead)
    {
        size = (size_t)rxRingBufferHead + handle->rxRingBufferSize - (size_t)rxRingBufferTail;
    }
    else
    {
        size = (size_t)rxRingBufferHead - (size_t)rxRingBufferTail;
    }
    return size;
}

static bool USART_TransferIsRxRingBufferFull(usart_handle_t *handle)
{
    bool full;

    /* Check arguments */
    assert(NULL != handle);

    if (USART_TransferGetRxRingBufferLength(handle) == (handle->rxRingBufferSize - 1U))
    {
        full = true;
    }
    else
    {
        full = false;
    }
    return full;
}

/*!
 * brief Sets up the RX ring buffer.
 *
 * This function sets up the RX ring buffer to a specific USART handle.
 *
 * When the RX ring buffer is used, data received are stored into the ring buffer even when the
 * user doesn't call the USART_TransferReceiveNonBlocking() API. If there is already data received
 * in the ring buffer, the user can get the received data from the ring buffer directly.
 *
 * note When using the RX ring buffer, one byte is reserved for internal use. In other
 * words, if p ringBufferSize is 32, then only 31 bytes are used for saving data.
 *
 * param base USART peripheral base address.
 * param handle USART handle pointer.
 * param ringBuffer Start address of the ring buffer for background receiving. Pass NULL to disable the ring buffer.
 * param ringBufferSize size of the ring buffer.
 */
void USART_TransferStartRingBuffer(USART_Type *base, usart_handle_t *handle, uint8_t *ringBuffer, size_t ringBufferSize)
{
    /* Check arguments */
    assert(NULL != base);
    assert(NULL != handle);
    assert(NULL != ringBuffer);

    /* Setup the ringbuffer address */
    handle->rxRingBuffer     = ringBuffer;
    handle->rxRingBufferSize = ringBufferSize;
    handle->rxRingBufferHead = 0U;
    handle->rxRingBufferTail = 0U;
    /* ring buffer is ready we can start receiving data */
    base->FIFOINTENSET |= USART_FIFOINTENSET_RXLVL_MASK | USART_FIFOINTENSET_RXERR_MASK;
}

/*!
 * brief Aborts the background transfer and uninstalls the ring buffer.
 *
 * This function aborts the background transfer and uninstalls the ring buffer.
 *
 * param base USART peripheral base address.
 * param handle USART handle pointer.
 */
void USART_TransferStopRingBuffer(USART_Type *base, usart_handle_t *handle)
{
    /* Check arguments */
    assert(NULL != base);
    assert(NULL != handle);

    if (handle->rxState == (uint8_t)kUSART_RxIdle)
    {
        base->FIFOINTENCLR = USART_FIFOINTENCLR_RXLVL_MASK | USART_FIFOINTENCLR_RXERR_MASK;
    }
    handle->rxRingBuffer     = NULL;
    handle->rxRingBufferSize = 0U;
    handle->rxRingBufferHead = 0U;
    handle->rxRingBufferTail = 0U;
}

/*!
 * brief Initializes a USART instance with user configuration structure and peripheral clock.
 *
 * This function configures the USART module with the user-defined settings. The user can configure the configuration
 * structure and also get the default configuration by using the USART_GetDefaultConfig() function.
 * Example below shows how to use this API to configure USART.
 * code
 *  usart_config_t usartConfig;
 *  usartConfig.baudRate_Bps = 115200U;
 *  usartConfig.parityMode = kUSART_ParityDisabled;
 *  usartConfig.stopBitCount = kUSART_OneStopBit;
 *  USART_Init(USART1, &usartConfig, 20000000U);
 * endcode
 *
 * param base USART peripheral base address.
 * param config Pointer to user-defined configuration structure.
 * param srcClock_Hz USART clock source frequency in HZ.
 * retval kStatus_USART_BaudrateNotSupport Baudrate is not support in current clock source.
 * retval kStatus_InvalidArgument USART base address is not valid
 * retval kStatus_Success Status USART initialize succeed
 */
status_t USART_Init(USART_Type *base, const usart_config_t *config, uint32_t srcClock_Hz)
{
    int result;

    /* check arguments */
    assert(!((NULL == base) || (NULL == config) || (0U == srcClock_Hz)));
    if ((NULL == base) || (NULL == config) || (0U == srcClock_Hz))
    {
        return kStatus_InvalidArgument;
    }

    /* initialize flexcomm to USART mode */
    result = FLEXCOMM_Init(base, FLEXCOMM_PERIPH_USART);
    if (kStatus_Success != result)
    {
        return result;
    }

    if (config->enableTx)
    {
        /* empty and enable txFIFO */
        base->FIFOCFG |= USART_FIFOCFG_EMPTYTX_MASK | USART_FIFOCFG_ENABLETX_MASK;
        /* setup trigger level */
        base->FIFOTRIG &= ~(USART_FIFOTRIG_TXLVL_MASK);
        base->FIFOTRIG |= USART_FIFOTRIG_TXLVL(config->txWatermark);
        /* enable trigger interrupt */
        base->FIFOTRIG |= USART_FIFOTRIG_TXLVLENA_MASK;
    }

    /* empty and enable rxFIFO */
    if (config->enableRx)
    {
        base->FIFOCFG |= USART_FIFOCFG_EMPTYRX_MASK | USART_FIFOCFG_ENABLERX_MASK;
        /* setup trigger level */
        base->FIFOTRIG &= ~(USART_FIFOTRIG_RXLVL_MASK);
        base->FIFOTRIG |= USART_FIFOTRIG_RXLVL(config->rxWatermark);
        /* enable trigger interrupt */
        base->FIFOTRIG |= USART_FIFOTRIG_RXLVLENA_MASK;
    }
    /* setup configuration and enable USART */
    base->CFG = USART_CFG_PARITYSEL(config->parityMode) | USART_CFG_STOPLEN(config->stopBitCount) |
                USART_CFG_DATALEN(config->bitCountPerChar) | USART_CFG_LOOP(config->loopback) |
                USART_CFG_SYNCEN((uint32_t)config->syncMode >> 1) | USART_CFG_SYNCMST((uint8_t)config->syncMode) |
                USART_CFG_CLKPOL(config->clockPolarity) | USART_CFG_ENABLE_MASK;

    /* Setup baudrate */
    result = USART_SetBaudRate(base, config->baudRate_Bps, srcClock_Hz);
    if (kStatus_Success != result)
    {
        return result;
    }
    /* Setting continuous Clock configuration. used for synchronous mode. */
    USART_EnableContinuousSCLK(base, config->enableContinuousSCLK);

    return kStatus_Success;
}

/*!
 * brief Deinitializes a USART instance.
 *
 * This function waits for TX complete, disables TX and RX, and disables the USART clock.
 *
 * param base USART peripheral base address.
 */
void USART_Deinit(USART_Type *base)
{
    /* Check arguments */
    assert(NULL != base);
    while (0U == (base->STAT & USART_STAT_TXIDLE_MASK))
    {
    }
    /* Disable interrupts, disable dma requests, disable peripheral */
    base->FIFOINTENCLR = USART_FIFOINTENCLR_TXERR_MASK | USART_FIFOINTENCLR_RXERR_MASK | USART_FIFOINTENCLR_TXLVL_MASK |
                         USART_FIFOINTENCLR_RXLVL_MASK;
    base->FIFOCFG &= ~(USART_FIFOCFG_DMATX_MASK | USART_FIFOCFG_DMARX_MASK);
    base->CFG &= ~(USART_CFG_ENABLE_MASK);
}

/*!
 * brief Gets the default configuration structure.
 *
 * This function initializes the USART configuration structure to a default value. The default
 * values are:
 *   usartConfig->baudRate_Bps = 115200U;
 *   usartConfig->parityMode = kUSART_ParityDisabled;
 *   usartConfig->stopBitCount = kUSART_OneStopBit;
 *   usartConfig->bitCountPerChar = kUSART_8BitsPerChar;
 *   usartConfig->loopback = false;
 *   usartConfig->enableTx = false;
 *   usartConfig->enableRx = false;
 *
 * param config Pointer to configuration structure.
 */
void USART_GetDefaultConfig(usart_config_t *config)
{
    /* Check arguments */
    assert(NULL != config);

    /* Initializes the configure structure to zero. */
    (void)memset(config, 0, sizeof(*config));

    /* Set always all members ! */
    config->baudRate_Bps         = 115200U;
    config->parityMode           = kUSART_ParityDisabled;
    config->stopBitCount         = kUSART_OneStopBit;
    config->bitCountPerChar      = kUSART_8BitsPerChar;
    config->loopback             = false;
    config->enableRx             = false;
    config->enableTx             = false;
    config->txWatermark          = kUSART_TxFifo0;
    config->rxWatermark          = kUSART_RxFifo1;
    config->syncMode             = kUSART_SyncModeDisabled;
    config->enableContinuousSCLK = false;
    config->clockPolarity        = kUSART_RxSampleOnFallingEdge;
}

/*!
 * brief Sets the USART instance baud rate.
 *
 * This function configures the USART module baud rate. This function is used to update
 * the USART module baud rate after the USART module is initialized by the USART_Init.
 * code
 *  USART_SetBaudRate(USART1, 115200U, 20000000U);
 * endcode
 *
 * param base USART peripheral base address.
 * param baudrate_Bps USART baudrate to be set.
 * param srcClock_Hz USART clock source frequency in HZ.
 * retval kStatus_USART_BaudrateNotSupport Baudrate is not support in current clock source.
 * retval kStatus_Success Set baudrate succeed.
 * retval kStatus_InvalidArgument One or more arguments are invalid.
 */
status_t USART_SetBaudRate(USART_Type *base, uint32_t baudrate_Bps, uint32_t srcClock_Hz)
{
    uint32_t best_diff = (uint32_t)-1, best_osrval = 0xf, best_brgval = (uint32_t)-1;
    uint32_t osrval, brgval, diff, baudrate;

    /* check arguments */
    assert(!((NULL == base) || (0 == baudrate_Bps) || (0 == srcClock_Hz)));
    if ((NULL == base) || (0U == baudrate_Bps) || (0U == srcClock_Hz))
    {
        return kStatus_InvalidArgument;
    }

    /* If synchronous master mode is enabled, only configure the BRG value. */
    if ((base->CFG & USART_CFG_SYNCEN_MASK) != 0U)
    {
        if ((base->CFG & USART_CFG_SYNCMST_MASK) != 0U)
        {
            brgval    = srcClock_Hz / baudrate_Bps;
            base->BRG = brgval - 1U;
        }
    }
    else
    {
        /*
         * Smaller values of OSR can make the sampling position within a data bit less accurate and may
         * potentially cause more noise errors or incorrect data.
         */
        for (osrval = best_osrval; osrval >= 8U; osrval--)
        {
            brgval = (((srcClock_Hz * 10U) / ((osrval + 1U) * baudrate_Bps)) - 5U) / 10U;
            if (brgval > 0xFFFFU)
            {
                continue;
            }
            baudrate = srcClock_Hz / ((osrval + 1U) * (brgval + 1U));
            diff     = baudrate_Bps < baudrate ? baudrate - baudrate_Bps : baudrate_Bps - baudrate;
            if (diff < best_diff)
            {
                best_diff   = diff;
                best_osrval = osrval;
                best_brgval = brgval;
            }
        }

        /* value over range */
        if (best_brgval > 0xFFFFU)
        {
            return kStatus_USART_BaudrateNotSupport;
        }

        base->OSR = best_osrval;
        base->BRG = best_brgval;
    }

    return kStatus_Success;
}

/*!
 * brief Writes to the TX register using a blocking method.
 *
 * This function polls the TX register, waits for the TX register to be empty or for the TX FIFO
 * to have room and writes data to the TX buffer.
 *
 * param base USART peripheral base address.
 * param data Start address of the data to write.
 * param length Size of the data to write.
 */
void USART_WriteBlocking(USART_Type *base, const uint8_t *data, size_t length)
{
    /* Check arguments */
    assert(!((NULL == base) || (NULL == data)));
    if ((NULL == base) || (NULL == data))
    {
        return;
    }
    /* Check whether txFIFO is enabled */
    if (0U == (base->FIFOCFG & USART_FIFOCFG_ENABLETX_MASK))
    {
        return;
    }
    for (; length > 0U; length--)
    {
        /* Loop until txFIFO get some space for new data */
        while (0U == (base->FIFOSTAT & USART_FIFOSTAT_TXNOTFULL_MASK))
        {
        }
        base->FIFOWR = *data;
        data++;
    }
    /* Wait to finish transfer */
    while (0U == (base->STAT & USART_STAT_TXIDLE_MASK))
    {
    }
}

/*!
 * brief Read RX data register using a blocking method.
 *
 * This function polls the RX register, waits for the RX register to be full or for RX FIFO to
 * have data and read data from the TX register.
 *
 * param base USART peripheral base address.
 * param data Start address of the buffer to store the received data.
 * param length Size of the buffer.
 * retval kStatus_USART_FramingError Receiver overrun happened while receiving data.
 * retval kStatus_USART_ParityError Noise error happened while receiving data.
 * retval kStatus_USART_NoiseError Framing error happened while receiving data.
 * retval kStatus_USART_RxError Overflow or underflow rxFIFO happened.
 * retval kStatus_Success Successfully received all data.
 */
status_t USART_ReadBlocking(USART_Type *base, uint8_t *data, size_t length)
{
    uint32_t statusFlag;
    status_t status = kStatus_Success;

    /* check arguments */
    assert(!((NULL == base) || (NULL == data)));
    if ((NULL == base) || (NULL == data))
    {
        return kStatus_InvalidArgument;
    }

    /* Check whether rxFIFO is enabled */
    if ((base->FIFOCFG & USART_FIFOCFG_ENABLERX_MASK) == 0U)
    {
        return kStatus_Fail;
    }
    for (; length > 0U; length--)
    {
        /* loop until rxFIFO have some data to read */
        while ((base->FIFOSTAT & USART_FIFOSTAT_RXNOTEMPTY_MASK) == 0U)
        {
        }
        /* check rxFIFO statusFlag */
        if ((base->FIFOSTAT & USART_FIFOSTAT_RXERR_MASK) != 0U)
        {
            base->FIFOCFG |= USART_FIFOCFG_EMPTYRX_MASK;
            base->FIFOSTAT |= USART_FIFOSTAT_RXERR_MASK;
            status = kStatus_USART_RxError;
            break;
        }
        /* check receive statusFlag */
        statusFlag = base->STAT;
        /* Clear all status flags */
        base->STAT |= statusFlag;
        if ((statusFlag & USART_STAT_PARITYERRINT_MASK) != 0U)
        {
            status = kStatus_USART_ParityError;
        }
        if ((statusFlag & USART_STAT_FRAMERRINT_MASK) != 0U)
        {
            status = kStatus_USART_FramingError;
        }
        if ((statusFlag & USART_STAT_RXNOISEINT_MASK) != 0U)
        {
            status = kStatus_USART_NoiseError;
        }

        if (kStatus_Success == status)
        {
            *data = (uint8_t)base->FIFORD;
            data++;
        }
        else
        {
            break;
        }
    }
    return status;
}

/*!
 * brief Initializes the USART handle.
 *
 * This function initializes the USART handle which can be used for other USART
 * transactional APIs. Usually, for a specified USART instance,
 * call this API once to get the initialized handle.
 *
 * param base USART peripheral base address.
 * param handle USART handle pointer.
 * param callback The callback function.
 * param userData The parameter of the callback function.
 */
status_t USART_TransferCreateHandle(USART_Type *base,
                                    usart_handle_t *handle,
                                    usart_transfer_callback_t callback,
                                    void *userData)
{
    /* Check 'base' */
    assert(!((NULL == base) || (NULL == handle)));

    uint32_t instance = 0;
    usart_to_flexcomm_t handler;
    handler.usart_master_handler = USART_TransferHandleIRQ;

    if ((NULL == base) || (NULL == handle))
    {
        return kStatus_InvalidArgument;
    }

    instance = USART_GetInstance(base);

    (void)memset(handle, 0, sizeof(*handle));
    /* Set the TX/RX state. */
    handle->rxState = (uint8_t)kUSART_RxIdle;
    handle->txState = (uint8_t)kUSART_TxIdle;
    /* Set the callback and user data. */
    handle->callback    = callback;
    handle->userData    = userData;
    handle->rxWatermark = (uint8_t)USART_FIFOTRIG_RXLVL_GET(base);
    handle->txWatermark = (uint8_t)USART_FIFOTRIG_TXLVL_GET(base);

    FLEXCOMM_SetIRQHandler(base, handler.flexcomm_handler, handle);

    /* Enable interrupt in NVIC. */
    (void)EnableIRQ(s_usartIRQ[instance]);

    return kStatus_Success;
}

/*!
 * brief Transmits a buffer of data using the interrupt method.
 *
 * This function sends data using an interrupt method. This is a non-blocking function, which
 * returns directly without waiting for all data to be written to the TX register. When
 * all data is written to the TX register in the IRQ handler, the USART driver calls the callback
 * function and passes the ref kStatus_USART_TxIdle as status parameter.
 *
 * note The kStatus_USART_TxIdle is passed to the upper layer when all data is written
 * to the TX register. However it does not ensure that all data are sent out. Before disabling the TX,
 * check the kUSART_TransmissionCompleteFlag to ensure that the TX is finished.
 *
 * param base USART peripheral base address.
 * param handle USART handle pointer.
 * param xfer USART transfer structure. See  #usart_transfer_t.
 * retval kStatus_Success Successfully start the data transmission.
 * retval kStatus_USART_TxBusy Previous transmission still not finished, data not all written to TX register yet.
 * retval kStatus_InvalidArgument Invalid argument.
 */
status_t USART_TransferSendNonBlocking(USART_Type *base, usart_handle_t *handle, usart_transfer_t *xfer)
{
    /* Check arguments */
    assert(!((NULL == base) || (NULL == handle) || (NULL == xfer)));
    if ((NULL == base) || (NULL == handle) || (NULL == xfer))
    {
        return kStatus_InvalidArgument;
    }
    /* Check xfer members */
    assert(!((0 == xfer->dataSize) || (NULL == xfer->data)));
    if ((0U == xfer->dataSize) || (NULL == xfer->data))
    {
        return kStatus_InvalidArgument;
    }

    /* Return error if current TX busy. */
    if ((uint8_t)kUSART_TxBusy == handle->txState)
    {
        return kStatus_USART_TxBusy;
    }
    else
    {
        handle->txData        = xfer->data;
        handle->txDataSize    = xfer->dataSize;
        handle->txDataSizeAll = xfer->dataSize;
        handle->txState       = (uint8_t)kUSART_TxBusy;
        /* Enable transmiter interrupt. */
        base->FIFOINTENSET |= USART_FIFOINTENSET_TXLVL_MASK;
    }
    return kStatus_Success;
}

/*!
 * brief Aborts the interrupt-driven data transmit.
 *
 * This function aborts the interrupt driven data sending. The user can get the remainBtyes to find out
 * how many bytes are still not sent out.
 *
 * param base USART peripheral base address.
 * param handle USART handle pointer.
 */
void USART_TransferAbortSend(USART_Type *base, usart_handle_t *handle)
{
    assert(NULL != handle);

    /* Disable interrupts */
    USART_DisableInterrupts(base, (uint32_t)kUSART_TxLevelInterruptEnable);
    /* Empty txFIFO */
    base->FIFOCFG |= USART_FIFOCFG_EMPTYTX_MASK;

    handle->txDataSize = 0U;
    handle->txState    = (uint8_t)kUSART_TxIdle;
}

/*!
 * brief Get the number of bytes that have been written to USART TX register.
 *
 * This function gets the number of bytes that have been written to USART TX
 * register by interrupt method.
 *
 * param base USART peripheral base address.
 * param handle USART handle pointer.
 * param count Send bytes count.
 * retval kStatus_NoTransferInProgress No send in progress.
 * retval kStatus_InvalidArgument Parameter is invalid.
 * retval kStatus_Success Get successfully through the parameter \p count;
 */
status_t USART_TransferGetSendCount(USART_Type *base, usart_handle_t *handle, uint32_t *count)
{
    assert(NULL != handle);
    assert(NULL != count);

    if ((uint8_t)kUSART_TxIdle == handle->txState)
    {
        return kStatus_NoTransferInProgress;
    }

    *count = handle->txDataSizeAll - handle->txDataSize;

    return kStatus_Success;
}

/*!
 * brief Receives a buffer of data using an interrupt method.
 *
 * This function receives data using an interrupt method. This is a non-blocking function, which
 *  returns without waiting for all data to be received.
 * If the RX ring buffer is used and not empty, the data in the ring buffer is copied and
 * the parameter p receivedBytes shows how many bytes are copied from the ring buffer.
 * After copying, if the data in the ring buffer is not enough to read, the receive
 * request is saved by the USART driver. When the new data arrives, the receive request
 * is serviced first. When all data is received, the USART driver notifies the upper layer
 * through a callback function and passes the status parameter ref kStatus_USART_RxIdle.
 * For example, the upper layer needs 10 bytes but there are only 5 bytes in the ring buffer.
 * The 5 bytes are copied to the xfer->data and this function returns with the
 * parameter p receivedBytes set to 5. For the left 5 bytes, newly arrived data is
 * saved from the xfer->data[5]. When 5 bytes are received, the USART driver notifies the upper layer.
 * If the RX ring buffer is not enabled, this function enables the RX and RX interrupt
 * to receive data to the xfer->data. When all data is received, the upper layer is notified.
 *
 * param base USART peripheral base address.
 * param handle USART handle pointer.
 * param xfer USART transfer structure, see #usart_transfer_t.
 * param receivedBytes Bytes received from the ring buffer directly.
 * retval kStatus_Success Successfully queue the transfer into transmit queue.
 * retval kStatus_USART_RxBusy Previous receive request is not finished.
 * retval kStatus_InvalidArgument Invalid argument.
 */
status_t USART_TransferReceiveNonBlocking(USART_Type *base,
                                          usart_handle_t *handle,
                                          usart_transfer_t *xfer,
                                          size_t *receivedBytes)
{
    uint32_t i;
    /* How many bytes to copy from ring buffer to user memory. */
    size_t bytesToCopy = 0U;
    /* How many bytes to receive. */
    size_t bytesToReceive;
    /* How many bytes currently have received. */
    size_t bytesCurrentReceived;
    uint32_t regPrimask = 0U;

    /* Check arguments */
    assert(!((NULL == base) || (NULL == handle) || (NULL == xfer)));
    if ((NULL == base) || (NULL == handle) || (NULL == xfer))
    {
        return kStatus_InvalidArgument;
    }
    /* Check xfer members */
    assert(!((0 == xfer->dataSize) || (NULL == xfer->data)));
    if ((0U == xfer->dataSize) || (NULL == xfer->data))
    {
        return kStatus_InvalidArgument;
    }

    /* How to get data:
       1. If RX ring buffer is not enabled, then save xfer->data and xfer->dataSize
          to uart handle, enable interrupt to store received data to xfer->data. When
          all data received, trigger callback.
       2. If RX ring buffer is enabled and not empty, get data from ring buffer first.
          If there are enough data in ring buffer, copy them to xfer->data and return.
          If there are not enough data in ring buffer, copy all of them to xfer->data,
          save the xfer->data remained empty space to uart handle, receive data
          to this empty space and trigger callback when finished. */
    if ((uint8_t)kUSART_RxBusy == handle->rxState)
    {
        return kStatus_USART_RxBusy;
    }
    else
    {
        bytesToReceive       = xfer->dataSize;
        bytesCurrentReceived = 0U;
        /* If RX ring buffer is used. */
        if (handle->rxRingBuffer != NULL)
        {
            /* Disable IRQ, protect ring buffer. */
            regPrimask = DisableGlobalIRQ();
            /* How many bytes in RX ring buffer currently. */
            bytesToCopy = USART_TransferGetRxRingBufferLength(handle);
            if (bytesToCopy != 0U)
            {
                bytesToCopy = MIN(bytesToReceive, bytesToCopy);
                bytesToReceive -= bytesToCopy;
                /* Copy data from ring buffer to user memory. */
                for (i = 0U; i < bytesToCopy; i++)
                {
                    xfer->data[bytesCurrentReceived++] = handle->rxRingBuffer[handle->rxRingBufferTail];
                    /* Wrap to 0. Not use modulo (%) because it might be large and slow. */
                    if ((size_t)handle->rxRingBufferTail + 1U == handle->rxRingBufferSize)
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
            if (bytesToReceive != 0U)
            {
                /* No data in ring buffer, save the request to UART handle. */
                handle->rxData        = xfer->data + bytesCurrentReceived;
                handle->rxDataSize    = bytesToReceive;
                handle->rxDataSizeAll = bytesToReceive;
                handle->rxState       = (uint8_t)kUSART_RxBusy;
            }
            /* Enable IRQ if previously enabled. */
            EnableGlobalIRQ(regPrimask);
            /* Call user callback since all data are received. */
            if (0U == bytesToReceive)
            {
                if (handle->callback != NULL)
                {
                    handle->callback(base, handle, kStatus_USART_RxIdle, handle->userData);
                }
            }
        }
        /* Ring buffer not used. */
        else
        {
            handle->rxData        = xfer->data + bytesCurrentReceived;
            handle->rxDataSize    = bytesToReceive;
            handle->rxDataSizeAll = bytesToReceive;
            handle->rxState       = (uint8_t)kUSART_RxBusy;

            /* Enable RX interrupt. */
            base->FIFOINTENSET |= USART_FIFOINTENSET_RXLVL_MASK;
        }
        /* Return the how many bytes have read. */
        if (receivedBytes != NULL)
        {
            *receivedBytes = bytesCurrentReceived;
        }
    }
    return kStatus_Success;
}

/*!
 * brief Aborts the interrupt-driven data receiving.
 *
 * This function aborts the interrupt-driven data receiving. The user can get the remainBytes to find out
 * how many bytes not received yet.
 *
 * param base USART peripheral base address.
 * param handle USART handle pointer.
 */
void USART_TransferAbortReceive(USART_Type *base, usart_handle_t *handle)
{
    assert(NULL != handle);

    /* Only abort the receive to handle->rxData, the RX ring buffer is still working. */
    if (NULL == handle->rxRingBuffer)
    {
        /* Disable interrupts */
        USART_DisableInterrupts(base, (uint32_t)kUSART_RxLevelInterruptEnable);
        /* Empty rxFIFO */
        base->FIFOCFG |= USART_FIFOCFG_EMPTYRX_MASK;
    }

    handle->rxDataSize = 0U;
    handle->rxState    = (uint8_t)kUSART_RxIdle;
}

/*!
 * brief Get the number of bytes that have been received.
 *
 * This function gets the number of bytes that have been received.
 *
 * param base USART peripheral base address.
 * param handle USART handle pointer.
 * param count Receive bytes count.
 * retval kStatus_NoTransferInProgress No receive in progress.
 * retval kStatus_InvalidArgument Parameter is invalid.
 * retval kStatus_Success Get successfully through the parameter \p count;
 */
status_t USART_TransferGetReceiveCount(USART_Type *base, usart_handle_t *handle, uint32_t *count)
{
    assert(NULL != handle);
    assert(NULL != count);

    if ((uint8_t)kUSART_RxIdle == handle->rxState)
    {
        return kStatus_NoTransferInProgress;
    }

    *count = handle->rxDataSizeAll - handle->rxDataSize;

    return kStatus_Success;
}

/*!
 * brief USART IRQ handle function.
 *
 * This function handles the USART transmit and receive IRQ request.
 *
 * param base USART peripheral base address.
 * param handle USART handle pointer.
 */
void USART_TransferHandleIRQ(USART_Type *base, usart_handle_t *handle)
{
    /* Check arguments */
    assert((NULL != base) && (NULL != handle));

    bool receiveEnabled = ((handle->rxDataSize != 0U) || (handle->rxRingBuffer != NULL));
    bool sendEnabled    = (handle->txDataSize != 0U);
    uint8_t rxdata;
    size_t tmpsize;

    /* If RX overrun. */
    if ((base->FIFOSTAT & USART_FIFOSTAT_RXERR_MASK) != 0U)
    {
        /* Clear rx error state. */
        base->FIFOSTAT |= USART_FIFOSTAT_RXERR_MASK;
        /* clear rxFIFO */
        base->FIFOCFG |= USART_FIFOCFG_EMPTYRX_MASK;
        /* Trigger callback. */
        if (handle->callback != NULL)
        {
            handle->callback(base, handle, kStatus_USART_RxError, handle->userData);
        }
    }
    while ((receiveEnabled && ((base->FIFOSTAT & USART_FIFOSTAT_RXNOTEMPTY_MASK) != 0U)) ||
           (sendEnabled && ((base->FIFOSTAT & USART_FIFOSTAT_TXNOTFULL_MASK) != 0U)))
    {
        /* Receive data */
        if (receiveEnabled && ((base->FIFOSTAT & USART_FIFOSTAT_RXNOTEMPTY_MASK) != 0U))
        {
            /* Receive to app bufffer if app buffer is present */
            if (handle->rxDataSize != 0U)
            {
                rxdata          = (uint8_t)base->FIFORD;
                *handle->rxData = rxdata;
                handle->rxDataSize--;
                handle->rxData++;
                receiveEnabled = ((handle->rxDataSize != 0U) || (handle->rxRingBuffer != NULL));
                if (0U == handle->rxDataSize)
                {
                    if (NULL == handle->rxRingBuffer)
                    {
                        base->FIFOINTENCLR = USART_FIFOINTENCLR_RXLVL_MASK | USART_FIFOINTENSET_RXERR_MASK;
                    }
                    handle->rxState = (uint8_t)kUSART_RxIdle;
                    if (handle->callback != NULL)
                    {
                        handle->callback(base, handle, kStatus_USART_RxIdle, handle->userData);
                    }
                }
            }
            /* Otherwise receive to ring buffer if ring buffer is present */
            else
            {
                if (handle->rxRingBuffer != NULL)
                {
                    /* If RX ring buffer is full, trigger callback to notify over run. */
                    if (USART_TransferIsRxRingBufferFull(handle))
                    {
                        if (handle->callback != NULL)
                        {
                            handle->callback(base, handle, kStatus_USART_RxRingBufferOverrun, handle->userData);
                        }
                    }
                    /* If ring buffer is still full after callback function, the oldest data is overridden. */
                    if (USART_TransferIsRxRingBufferFull(handle))
                    {
                        /* Increase handle->rxRingBufferTail to make room for new data. */
                        if ((size_t)handle->rxRingBufferTail + 1U == handle->rxRingBufferSize)
                        {
                            handle->rxRingBufferTail = 0U;
                        }
                        else
                        {
                            handle->rxRingBufferTail++;
                        }
                    }
                    /* Read data. */
                    rxdata                                         = (uint8_t)base->FIFORD;
                    handle->rxRingBuffer[handle->rxRingBufferHead] = rxdata;
                    /* Increase handle->rxRingBufferHead. */
                    if ((size_t)handle->rxRingBufferHead + 1U == handle->rxRingBufferSize)
                    {
                        handle->rxRingBufferHead = 0U;
                    }
                    else
                    {
                        handle->rxRingBufferHead++;
                    }
                }
            }
        }
        /* Send data */
        if (sendEnabled && ((base->FIFOSTAT & USART_FIFOSTAT_TXNOTFULL_MASK) != 0U))
        {
            base->FIFOWR = *handle->txData;
            handle->txDataSize--;
            handle->txData++;
            sendEnabled = handle->txDataSize != 0U;
            if (!sendEnabled)
            {
                base->FIFOINTENCLR = USART_FIFOINTENCLR_TXLVL_MASK;
                handle->txState    = (uint8_t)kUSART_TxIdle;

                base->INTENSET |= USART_INTENSET_TXIDLEEN_MASK;
            }
        }
    }

    /* Tx idle and the interrupt is enabled. */
    if ((0U != (base->INTENSET & USART_INTENSET_TXIDLEEN_MASK)) &&
        (0U != (base->INTSTAT & USART_INTSTAT_TXIDLE_MASK)) && (handle->txState == (uint8_t)kUSART_TxIdle))
    {
        /* Disable tx idle interrupt */
        base->INTENCLR |= USART_INTENCLR_TXIDLECLR_MASK;
        /* Trigger callback. */
        if (handle->callback != NULL)
        {
            handle->callback(base, handle, kStatus_USART_TxIdle, handle->userData);
        }
    }

    /* ring buffer is not used */
    if (NULL == handle->rxRingBuffer)
    {
        tmpsize = handle->rxDataSize;

        /* restore if rx transfer ends and rxLevel is different from default value */
        if ((tmpsize == 0U) && (USART_FIFOTRIG_RXLVL_GET(base) != handle->rxWatermark))
        {
            base->FIFOTRIG =
                (base->FIFOTRIG & (~USART_FIFOTRIG_RXLVL_MASK)) | USART_FIFOTRIG_RXLVL(handle->rxWatermark);
        }
        /* decrease level if rx transfer is bellow */
        if ((tmpsize != 0U) && (tmpsize < (USART_FIFOTRIG_RXLVL_GET(base) + 1U)))
        {
            base->FIFOTRIG = (base->FIFOTRIG & (~USART_FIFOTRIG_RXLVL_MASK)) | (USART_FIFOTRIG_RXLVL(tmpsize - 1U));
        }
    }
}
