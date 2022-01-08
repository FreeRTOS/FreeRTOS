/*
 * Copyright 2018 NXP
 * All rights reserved.
 *
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "fsl_component_serial_manager.h"
#include "fsl_component_serial_port_internal.h"

#if (defined(SERIAL_PORT_TYPE_UART) && (SERIAL_PORT_TYPE_UART > 0U))
#include "fsl_adapter_uart.h"

#include "fsl_component_serial_port_uart.h"

/*******************************************************************************
 * Definitions
 ******************************************************************************/
#ifndef NDEBUG
#if (defined(DEBUG_CONSOLE_ASSERT_DISABLE) && (DEBUG_CONSOLE_ASSERT_DISABLE > 0U))
#undef assert
#define assert(n)
#else
/* MISRA C-2012 Rule 17.2 */
#undef assert
#define assert(n) \
    while (!(n))  \
    {             \
        ;         \
    }
#endif
#endif

#if (defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
#define SERIAL_PORT_UART_RECEIVE_DATA_LENGTH 1U
#define SERIAL_MANAGER_BLOCK_OFFSET          (12U)
typedef struct _serial_uart_send_state
{
    uint8_t *buffer;
    uint32_t length;
    serial_manager_callback_t callback;
    void *callbackParam;
    volatile uint8_t busy;
} serial_uart_send_state_t;

typedef struct _serial_uart_recv_state
{
    serial_manager_callback_t callback;
    void *callbackParam;
    volatile uint8_t busy;
    volatile uint8_t rxEnable;
    uint8_t readBuffer[SERIAL_PORT_UART_RECEIVE_DATA_LENGTH];
} serial_uart_recv_state_t;
typedef struct _serial_uart_block_state
{
    UART_HANDLE_DEFINE(usartHandleBuffer);
} serial_uart_block_state_t;
#endif

typedef struct _serial_uart_state
{
    UART_HANDLE_DEFINE(usartHandleBuffer);
#if (defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
    serial_uart_send_state_t tx;
    serial_uart_recv_state_t rx;
#endif
} serial_uart_state_t;

/*******************************************************************************
 * Prototypes
 ******************************************************************************/

/*******************************************************************************
 * Code
 ******************************************************************************/

#if (defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
static serial_manager_status_t Serial_UartEnableReceiving(serial_uart_state_t *serialUartHandle)
{
#if (defined(HAL_UART_TRANSFER_MODE) && (HAL_UART_TRANSFER_MODE > 0U))
    hal_uart_transfer_t transfer;
#endif
    if (1U == serialUartHandle->rx.rxEnable)
    {
        serialUartHandle->rx.busy = 1U;
#if (defined(HAL_UART_TRANSFER_MODE) && (HAL_UART_TRANSFER_MODE > 0U))
        transfer.data     = &serialUartHandle->rx.readBuffer[0];
        transfer.dataSize = sizeof(serialUartHandle->rx.readBuffer);
        if (kStatus_HAL_UartSuccess !=
            HAL_UartTransferReceiveNonBlocking(((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]), &transfer))
#else
        if (kStatus_HAL_UartSuccess !=
            HAL_UartReceiveNonBlocking(((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]),
                                       &serialUartHandle->rx.readBuffer[0], sizeof(serialUartHandle->rx.readBuffer)))
#endif
        {
            serialUartHandle->rx.busy = 0U;
            return kStatus_SerialManager_Error;
        }
    }
    return kStatus_SerialManager_Success;
}

/* UART user callback */
static void Serial_UartCallback(hal_uart_handle_t handle, hal_uart_status_t status, void *userData)
{
    serial_uart_state_t *serialUartHandle;
    serial_manager_callback_message_t msg;
#if (defined(HAL_UART_TRANSFER_MODE) && (HAL_UART_TRANSFER_MODE > 0U))
    hal_uart_transfer_t transfer;
#endif

    assert(userData);
    serialUartHandle = (serial_uart_state_t *)userData;

    if ((hal_uart_status_t)kStatus_HAL_UartRxIdle == status)
    {
        if ((NULL != serialUartHandle->rx.callback))
        {
            msg.buffer = &serialUartHandle->rx.readBuffer[0];
            msg.length = sizeof(serialUartHandle->rx.readBuffer);
            serialUartHandle->rx.callback(serialUartHandle->rx.callbackParam, &msg, kStatus_SerialManager_Success);
        }
#if (defined(HAL_UART_TRANSFER_MODE) && (HAL_UART_TRANSFER_MODE > 0U))
        transfer.data             = &serialUartHandle->rx.readBuffer[0];
        transfer.dataSize         = sizeof(serialUartHandle->rx.readBuffer);
        serialUartHandle->rx.busy = 0U;
        if (kStatus_HAL_UartSuccess ==
            HAL_UartTransferReceiveNonBlocking(((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]), &transfer))
#else
        if ((hal_uart_status_t)kStatus_HAL_UartSuccess ==
            HAL_UartReceiveNonBlocking(((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]),
                                       &serialUartHandle->rx.readBuffer[0], sizeof(serialUartHandle->rx.readBuffer)))
#endif
        {
            serialUartHandle->rx.busy = 1U;
        }
    }
    else if ((hal_uart_status_t)kStatus_HAL_UartTxIdle == status)
    {
        if (0U != serialUartHandle->tx.busy)
        {
            serialUartHandle->tx.busy = 0U;
            if ((NULL != serialUartHandle->tx.callback))
            {
                msg.buffer = serialUartHandle->tx.buffer;
                msg.length = serialUartHandle->tx.length;
                serialUartHandle->tx.callback(serialUartHandle->tx.callbackParam, &msg, kStatus_SerialManager_Success);
            }
        }
    }
    else
    {
    }
}
#endif

serial_manager_status_t Serial_UartInit(serial_handle_t serialHandle, void *serialConfig)
{
    serial_uart_state_t *serialUartHandle;
#if (defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
    serial_port_uart_config_t *uartConfig = (serial_port_uart_config_t *)serialConfig;
#endif
    serial_manager_status_t serialManagerStatus = kStatus_SerialManager_Success;
#if (defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
#if (defined(HAL_UART_TRANSFER_MODE) && (HAL_UART_TRANSFER_MODE > 0U))
#if 0 /* Not used below! */
    hal_uart_transfer_t transfer;
#endif
#endif
#endif

    assert(serialConfig);
    assert(serialHandle);
    assert(SERIAL_PORT_UART_HANDLE_SIZE >= sizeof(serial_uart_state_t));

    serialUartHandle    = (serial_uart_state_t *)serialHandle;
    serialManagerStatus = (serial_manager_status_t)HAL_UartInit(
        ((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]), (const hal_uart_config_t *)serialConfig);
    assert(kStatus_SerialManager_Success == serialManagerStatus);
    (void)serialManagerStatus;

#if (defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
#if (defined(SERIAL_MANAGER_NON_BLOCKING_DUAL_MODE) && (SERIAL_MANAGER_NON_BLOCKING_DUAL_MODE > 0U))
    serial_manager_type_t type = *(serial_manager_type_t *)((uint32_t)serialHandle - SERIAL_MANAGER_BLOCK_OFFSET);
    if (type == kSerialManager_Blocking)
    {
        return serialManagerStatus;
    }
#endif /* SERIAL_MANAGER_NON_BLOCKING_DUAL_MODE */
    serialUartHandle->rx.rxEnable = uartConfig->enableRx;
#if (defined(HAL_UART_TRANSFER_MODE) && (HAL_UART_TRANSFER_MODE > 0U))

    (void)HAL_UartTransferInstallCallback(((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]),
                                          Serial_UartCallback, serialUartHandle);
#else
    (void)HAL_UartInstallCallback(((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]), Serial_UartCallback,
                                  serialUartHandle);
#endif
#endif
#if (defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
    serialManagerStatus = Serial_UartEnableReceiving(serialUartHandle);
#endif

    return serialManagerStatus;
}

serial_manager_status_t Serial_UartDeinit(serial_handle_t serialHandle)
{
    serial_uart_state_t *serialUartHandle;

    assert(serialHandle);

    serialUartHandle = (serial_uart_state_t *)serialHandle;

#if (defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
#if (defined(HAL_UART_TRANSFER_MODE) && (HAL_UART_TRANSFER_MODE > 0U))
    (void)HAL_UartTransferAbortReceive(((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]));
#else
    (void)HAL_UartAbortReceive(((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]));
#endif
#endif
    (void)HAL_UartDeinit(((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]));

#if (defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
    serialUartHandle->tx.busy = 0U;
    serialUartHandle->rx.busy = 0U;
#endif

    return kStatus_SerialManager_Success;
}

#if (defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))

serial_manager_status_t Serial_UartWrite(serial_handle_t serialHandle, uint8_t *buffer, uint32_t length)
{
    serial_uart_state_t *serialUartHandle;
    hal_uart_status_t uartstatus;
#if (defined(HAL_UART_TRANSFER_MODE) && (HAL_UART_TRANSFER_MODE > 0U))
    hal_uart_transfer_t transfer;
#endif

    assert(serialHandle);
    assert(buffer);
    assert(length);

    serialUartHandle = (serial_uart_state_t *)serialHandle;
#if (defined(SERIAL_MANAGER_NON_BLOCKING_DUAL_MODE) && (SERIAL_MANAGER_NON_BLOCKING_DUAL_MODE > 0U))
    serial_manager_type_t type = *(serial_manager_type_t *)((uint32_t)serialHandle - SERIAL_MANAGER_BLOCK_OFFSET);
    if (type == kSerialManager_Blocking)
    {
        return (serial_manager_status_t)HAL_UartSendBlocking(
            ((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]), buffer, length);
    }
#endif /* SERIAL_MANAGER_NON_BLOCKING_DUAL_MODE */
    if (0U != serialUartHandle->tx.busy)
    {
        return kStatus_SerialManager_Busy;
    }
    serialUartHandle->tx.busy = 1U;

    serialUartHandle->tx.buffer = buffer;
    serialUartHandle->tx.length = length;

#if (defined(HAL_UART_TRANSFER_MODE) && (HAL_UART_TRANSFER_MODE > 0U))
    transfer.data     = buffer;
    transfer.dataSize = length;
    uartstatus =
        HAL_UartTransferSendNonBlocking(((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]), &transfer);
#else

    uartstatus = HAL_UartSendNonBlocking(((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]), buffer, length);
#endif
    assert(kStatus_HAL_UartSuccess == uartstatus);
    (void)uartstatus;

    return kStatus_SerialManager_Success;
}
serial_manager_status_t Serial_UartWriteBlocking(serial_handle_t serialHandle, uint8_t *buffer, uint32_t length)
{
    serial_uart_state_t *serialUartHandle;

    assert(serialHandle);
    assert(buffer);
    assert(length);

    serialUartHandle = (serial_uart_state_t *)serialHandle;

    return (serial_manager_status_t)HAL_UartSendBlocking(((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]),
                                                         buffer, length);
}
#if (defined(SERIAL_MANAGER_NON_BLOCKING_DUAL_MODE) && (SERIAL_MANAGER_NON_BLOCKING_DUAL_MODE > 0U))
serial_manager_status_t Serial_UartRead(serial_handle_t serialHandle, uint8_t *buffer, uint32_t length)
{
    serial_uart_state_t *serialUartHandle;

    assert(serialHandle);
    assert(buffer);
    assert(length);

    serialUartHandle = (serial_uart_state_t *)serialHandle;

    return (serial_manager_status_t)HAL_UartReceiveBlocking(
        ((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]), buffer, length);
}
#endif /* SERIAL_MANAGER_NON_BLOCKING_DUAL_MODE */
#else

serial_manager_status_t Serial_UartWrite(serial_handle_t serialHandle, uint8_t *buffer, uint32_t length)
{
    serial_uart_state_t *serialUartHandle;

    assert(serialHandle);
    assert(buffer);
    assert(length);

    serialUartHandle = (serial_uart_state_t *)serialHandle;

    return (serial_manager_status_t)HAL_UartSendBlocking(((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]),
                                                         buffer, length);
}

serial_manager_status_t Serial_UartRead(serial_handle_t serialHandle, uint8_t *buffer, uint32_t length)
{
    serial_uart_state_t *serialUartHandle;

    assert(serialHandle);
    assert(buffer);
    assert(length);

    serialUartHandle = (serial_uart_state_t *)serialHandle;

    return (serial_manager_status_t)HAL_UartReceiveBlocking(
        ((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]), buffer, length);
}

#endif

#if (defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
serial_manager_status_t Serial_UartCancelWrite(serial_handle_t serialHandle)
{
    serial_uart_state_t *serialUartHandle;
    serial_manager_callback_message_t msg;
    uint32_t primask;
    uint8_t isBusy = 0U;

    assert(serialHandle);

    serialUartHandle = (serial_uart_state_t *)serialHandle;

    primask                   = DisableGlobalIRQ();
    isBusy                    = serialUartHandle->tx.busy;
    serialUartHandle->tx.busy = 0U;
    EnableGlobalIRQ(primask);

#if (defined(HAL_UART_TRANSFER_MODE) && (HAL_UART_TRANSFER_MODE > 0U))
    (void)HAL_UartTransferAbortSend(((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]));
#else
    (void)HAL_UartAbortSend(((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]));
#endif
    if (0U != isBusy)
    {
        if ((NULL != serialUartHandle->tx.callback))
        {
            msg.buffer = serialUartHandle->tx.buffer;
            msg.length = serialUartHandle->tx.length;
            serialUartHandle->tx.callback(serialUartHandle->tx.callbackParam, &msg, kStatus_SerialManager_Canceled);
        }
    }
    return kStatus_SerialManager_Success;
}

serial_manager_status_t Serial_UartInstallTxCallback(serial_handle_t serialHandle,
                                                     serial_manager_callback_t callback,
                                                     void *callbackParam)
{
    serial_uart_state_t *serialUartHandle;

    assert(serialHandle);

    serialUartHandle = (serial_uart_state_t *)serialHandle;

    serialUartHandle->tx.callback      = callback;
    serialUartHandle->tx.callbackParam = callbackParam;

    return kStatus_SerialManager_Success;
}

serial_manager_status_t Serial_UartInstallRxCallback(serial_handle_t serialHandle,
                                                     serial_manager_callback_t callback,
                                                     void *callbackParam)
{
    serial_uart_state_t *serialUartHandle;

    assert(serialHandle);

    serialUartHandle = (serial_uart_state_t *)serialHandle;

    serialUartHandle->rx.callback      = callback;
    serialUartHandle->rx.callbackParam = callbackParam;

    return kStatus_SerialManager_Success;
}

void Serial_UartIsrFunction(serial_handle_t serialHandle)
{
    serial_uart_state_t *serialUartHandle;

    assert(serialHandle);

    serialUartHandle = (serial_uart_state_t *)serialHandle;

    HAL_UartIsrFunction(((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]));
}
#endif

serial_manager_status_t Serial_UartEnterLowpower(serial_handle_t serialHandle)
{
    serial_uart_state_t *serialUartHandle;
    hal_uart_status_t uartstatus;

    assert(serialHandle);

    serialUartHandle = (serial_uart_state_t *)serialHandle;

    uartstatus = HAL_UartEnterLowpower(((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]));
    assert(kStatus_HAL_UartSuccess == uartstatus);
    (void)uartstatus;

    return kStatus_SerialManager_Success;
}

serial_manager_status_t Serial_UartExitLowpower(serial_handle_t serialHandle)
{
    serial_uart_state_t *serialUartHandle;
    serial_manager_status_t status = kStatus_SerialManager_Success;
    hal_uart_status_t uartstatus;

    assert(serialHandle);

    serialUartHandle = (serial_uart_state_t *)serialHandle;

    uartstatus = HAL_UartExitLowpower(((hal_uart_handle_t)&serialUartHandle->usartHandleBuffer[0]));
    assert(kStatus_HAL_UartSuccess == uartstatus);
    (void)uartstatus;

#if (defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
    serial_manager_type_t type =
        *(serial_manager_type_t *)(void *)((uint8_t *)serialHandle - SERIAL_MANAGER_BLOCK_OFFSET);
    if (type != kSerialManager_Blocking)
    {
        status = Serial_UartEnableReceiving(serialUartHandle);
    }
#endif

    return status;
}

#endif
