/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#ifndef METAL__UART_H
#define METAL__UART_H

/*!
 * @file uart.h
 * @brief API for UART serial ports
 */

#include <metal/interrupt.h>

struct metal_uart;

struct metal_uart_vtable {
    void (*init)(struct metal_uart *uart, int baud_rate);
    int (*putc)(struct metal_uart *uart, unsigned char c);
    int (*getc)(struct metal_uart *uart, unsigned char *c);
    int (*get_baud_rate)(struct metal_uart *uart);
    int (*set_baud_rate)(struct metal_uart *uart, int baud_rate);
    struct metal_interrupt* (*controller_interrupt)(struct metal_uart *uart);
    int (*get_interrupt_id)(struct metal_uart *uart);
};

/*!
 * @brief Handle for a UART serial device
 */
struct metal_uart {
    const struct metal_uart_vtable *vtable;
};

/*!
 * @brief Initialize UART device
 
 * Initialize the UART device described by the UART handle. This function must be called before any
 * other method on the UART can be invoked. It is invalid to initialize a UART more than once.
 *
 * @param uart The UART device handle
 * @param baud_rate the baud rate to set the UART to
 */
inline void metal_uart_init(struct metal_uart *uart, int baud_rate) { return uart->vtable->init(uart, baud_rate); }

/*!
 * @brief Output a character over the UART
 * @param uart The UART device handle
 * @param c The character to send over the UART
 * @return 0 upon success
 */
inline int metal_uart_putc(struct metal_uart *uart, unsigned char c) { return uart->vtable->putc(uart, c); }

/*!
 * @brief Read a character sent over the UART
 * @param uart The UART device handle
 * @param c The varible to hold the read character
 * @return 0 upon success
 */
inline int metal_uart_getc(struct metal_uart *uart, unsigned char *c) { return uart->vtable->getc(uart, c); }

/*!
 * @brief Get the baud rate of the UART peripheral
 * @param uart The UART device handle
 * @return The current baud rate of the UART
 */
inline int metal_uart_get_baud_rate(struct metal_uart *uart) { return uart->vtable->get_baud_rate(uart); }

/*!
 * @brief Set the baud rate of the UART peripheral
 * @param uart The UART device handle
 * @param baud_rate The baud rate to configure
 * @return the new baud rate of the UART
 */
inline int metal_uart_set_baud_rate(struct metal_uart *uart, int baud_rate) { return uart->vtable->set_baud_rate(uart, baud_rate); }

/*!
 * @brief Get the interrupt controller of the UART peripheral
 *
 * Get the interrupt controller for the UART peripheral. The interrupt
 * controller must be initialized before any interrupts can be registered
 * or enabled with it.
 *
 * @param uart The UART device handle
 * @return The handle for the UART interrupt controller
 */
inline struct metal_interrupt* metal_uart_interrupt_controller(struct metal_uart *uart) { return uart->vtable->controller_interrupt(uart); }

/*!
 * @brief Get the interrupt ID of the UART controller
 * @param uart The UART device handle
 * @return The UART interrupt id
 */
inline int metal_uart_get_interrupt_id(struct metal_uart *uart) { return uart->vtable->get_interrupt_id(uart); }

#endif
