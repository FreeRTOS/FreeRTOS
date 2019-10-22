/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/uart.h>
#include <metal/machine.h>

#if defined(__METAL_DT_STDOUT_UART_HANDLE)
/* This implementation serves as a small shim that interfaces with the first
 * UART on a system. */
int metal_tty_putc(unsigned char c)
{
    if (c == '\n') {
        int out = metal_uart_putc(__METAL_DT_STDOUT_UART_HANDLE, '\r');
        if (out != 0)
            return out;
    }
    return metal_uart_putc(__METAL_DT_STDOUT_UART_HANDLE, c);
}

#ifndef __METAL_DT_STDOUT_UART_BAUD
#define __METAL_DT_STDOUT_UART_BAUD 115200
#endif

static void metal_tty_init(void) __attribute__((constructor));
static void metal_tty_init(void)
{
    metal_uart_init(__METAL_DT_STDOUT_UART_HANDLE, __METAL_DT_STDOUT_UART_BAUD);
}
#else
/* This implementation of putc doesn't actually do anything, it's just there to
 * provide a shim that eats all the characters so we can ensure that everything
 * can link to metal_tty_putc. */
int nop_putc(unsigned char c) __attribute__((section(".text.metal.nop.putc")));
int nop_putc(unsigned char c) { return -1; }
int metal_tty_putc(unsigned char c) __attribute__((weak, alias("nop_putc")));
#warning "There is no default output device, metal_tty_putc() will throw away all input."
#endif
