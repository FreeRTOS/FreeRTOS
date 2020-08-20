/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/uart.h>

extern __inline__ void metal_uart_init(struct metal_uart *uart, int baud_rate);
extern __inline__ int metal_uart_putc(struct metal_uart *uart, int c);
extern __inline__ int metal_uart_txready(struct metal_uart *uart);
extern __inline__ int metal_uart_getc(struct metal_uart *uart, int *c);
extern __inline__ int metal_uart_get_baud_rate(struct metal_uart *uart);
extern __inline__ int metal_uart_set_baud_rate(struct metal_uart *uart, int baud_rate);
