/*
 * Copyright 2018 NXP
 * All rights reserved.
 *
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef __SERIAL_PORT_UART_H__
#define __SERIAL_PORT_UART_H__

/*******************************************************************************
 * Definitions
 ******************************************************************************/

#if (defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
#define SERIAL_PORT_UART_HANDLE_SIZE          (166U)
#else
#define SERIAL_PORT_UART_HANDLE_SIZE          (4U)
#endif

typedef enum _serial_port_uart_parity_mode
{
    kSerialManager_UartParityDisabled = 0x0U, /*!< Parity disabled */
    kSerialManager_UartParityEven = 0x1U,     /*!< Parity even enabled */
    kSerialManager_UartParityOdd = 0x2U,      /*!< Parity odd enabled */
} serial_port_uart_parity_mode_t;

typedef enum _serial_port_uart_stop_bit_count
{
    kSerialManager_UartOneStopBit = 0U, /*!< One stop bit */
    kSerialManager_UartTwoStopBit = 1U, /*!< Two stop bits */
} serial_port_uart_stop_bit_count_t;

typedef struct _serial_port_uart_config
{
    uint32_t clockRate;                                 /*!< clock rate  */
    uint32_t baudRate;                                  /*!< baud rate  */
    serial_port_uart_parity_mode_t parityMode;          /*!< Parity mode, disabled (default), even, odd */
    serial_port_uart_stop_bit_count_t stopBitCount;     /*!< Number of stop bits, 1 stop bit (default) or 2 stop bits  */
    uint8_t instance;                                   /*!< Instance (0 - UART0, 1 - UART1, ...), detail information
                                                             please refer to the SOC corresponding RM. */
    uint8_t enableRx;                                   /*!< Enable RX */
    uint8_t enableTx;                                   /*!< Enable TX */
} serial_port_uart_config_t;

#endif /* __SERIAL_PORT_UART_H__ */
