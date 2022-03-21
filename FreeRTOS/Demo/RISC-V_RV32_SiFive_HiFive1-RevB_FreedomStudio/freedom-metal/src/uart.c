/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine.h>
#include <metal/uart.h>

extern __inline__ void metal_uart_init(struct metal_uart *uart, int baud_rate);
extern __inline__ int metal_uart_putc(struct metal_uart *uart, int c);
extern __inline__ int metal_uart_txready(struct metal_uart *uart);
extern __inline__ int metal_uart_getc(struct metal_uart *uart, int *c);
extern __inline__ int metal_uart_get_baud_rate(struct metal_uart *uart);
extern __inline__ int metal_uart_set_baud_rate(struct metal_uart *uart,
                                               int baud_rate);
extern __inline__ struct metal_interrupt *
metal_uart_interrupt_controller(struct metal_uart *uart);
extern __inline__ int metal_uart_get_interrupt_id(struct metal_uart *uart);
extern __inline__ int
metal_uart_transmit_interrupt_enable(struct metal_uart *uart);
extern __inline__ int
metal_uart_transmit_interrupt_disable(struct metal_uart *uart);
extern __inline__ int
metal_uart_receive_interrupt_enable(struct metal_uart *uart);
extern __inline__ int
metal_uart_receive_interrupt_disable(struct metal_uart *uart);
extern __inline__ int metal_uart_set_transmit_watermark(struct metal_uart *uart,
                                                        size_t level);
extern __inline__ size_t
metal_uart_get_transmit_watermark(struct metal_uart *uart);
extern __inline__ int metal_uart_set_receive_watermark(struct metal_uart *uart,
                                                       size_t level);
extern __inline__ size_t
metal_uart_get_receive_watermark(struct metal_uart *uart);

struct metal_uart *metal_uart_get_device(unsigned int device_num) {
#if __METAL_DT_MAX_UARTS > 0
    if (device_num < __METAL_DT_MAX_UARTS) {
        return (struct metal_uart *)__metal_uart_table[device_num];
    }
#endif

    return NULL;
}
