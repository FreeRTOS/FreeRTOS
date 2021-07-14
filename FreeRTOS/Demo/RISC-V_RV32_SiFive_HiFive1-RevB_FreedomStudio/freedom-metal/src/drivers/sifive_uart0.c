/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_SIFIVE_UART0

#include <metal/drivers/sifive_uart0.h>
#include <metal/machine.h>

/* TXDATA Fields */
#define UART_TXEN (1 << 0)
#define UART_TXFULL (1 << 31)

/* RXDATA Fields */
#define UART_RXEN (1 << 0)
#define UART_RXEMPTY (1 << 31)

/* TXCTRL Fields */
#define UART_NSTOP (1 << 1)
#define UART_TXCNT(count) ((0x7 & count) << 16)

/* RXCTRL Fields */
#define UART_RXCNT(count) ((0x7 & count) << 16)

/* IP Fields */
#define UART_TXWM (1 << 0)
#define UART_RXWM (1 << 1)

#define UART_REG(offset) (((unsigned long)control_base + offset))
#define UART_REGB(offset)                                                      \
    (__METAL_ACCESS_ONCE((__metal_io_u8 *)UART_REG(offset)))
#define UART_REGW(offset)                                                      \
    (__METAL_ACCESS_ONCE((__metal_io_u32 *)UART_REG(offset)))

struct metal_interrupt *
__metal_driver_sifive_uart0_interrupt_controller(struct metal_uart *uart) {
    return __metal_driver_sifive_uart0_interrupt_parent(uart);
}

int __metal_driver_sifive_uart0_get_interrupt_id(struct metal_uart *uart) {
    return __metal_driver_sifive_uart0_interrupt_line(uart);
}

int __metal_driver_sifive_uart0_tx_interrupt_enable(struct metal_uart *uart) {
    long control_base = __metal_driver_sifive_uart0_control_base(uart);

    UART_REGW(METAL_SIFIVE_UART0_IE) |= UART_TXWM;
    return 0;
}

int __metal_driver_sifive_uart0_tx_interrupt_disable(struct metal_uart *uart) {
    long control_base = __metal_driver_sifive_uart0_control_base(uart);

    UART_REGW(METAL_SIFIVE_UART0_IE) &= ~UART_TXWM;
    return 0;
}

int __metal_driver_sifive_uart0_rx_interrupt_enable(struct metal_uart *uart) {
    long control_base = __metal_driver_sifive_uart0_control_base(uart);

    UART_REGW(METAL_SIFIVE_UART0_IE) |= UART_RXWM;
    return 0;
}

int __metal_driver_sifive_uart0_rx_interrupt_disable(struct metal_uart *uart) {
    long control_base = __metal_driver_sifive_uart0_control_base(uart);

    UART_REGW(METAL_SIFIVE_UART0_IE) &= ~UART_RXWM;
    return 0;
}

int __metal_driver_sifive_uart0_txready(struct metal_uart *uart) {
    long control_base = __metal_driver_sifive_uart0_control_base(uart);

    return !!((UART_REGW(METAL_SIFIVE_UART0_TXDATA) & UART_TXFULL));
}

int __metal_driver_sifive_uart0_set_tx_watermark(struct metal_uart *uart,
                                                 size_t level) {
    long control_base = __metal_driver_sifive_uart0_control_base(uart);

    UART_REGW(METAL_SIFIVE_UART0_TXCTRL) |= UART_TXCNT(level);
    return 0;
}

size_t __metal_driver_sifive_uart0_get_tx_watermark(struct metal_uart *uart) {
    long control_base = __metal_driver_sifive_uart0_control_base(uart);

    return ((UART_REGW(METAL_SIFIVE_UART0_TXCTRL) >> 16) & 0x7);
}

int __metal_driver_sifive_uart0_set_rx_watermark(struct metal_uart *uart,
                                                 size_t level) {
    long control_base = __metal_driver_sifive_uart0_control_base(uart);

    UART_REGW(METAL_SIFIVE_UART0_RXCTRL) |= UART_RXCNT(level);
    return 0;
}

size_t __metal_driver_sifive_uart0_get_rx_watermark(struct metal_uart *uart) {
    long control_base = __metal_driver_sifive_uart0_control_base(uart);

    return ((UART_REGW(METAL_SIFIVE_UART0_RXCTRL) >> 16) & 0x7);
}

int __metal_driver_sifive_uart0_putc(struct metal_uart *uart, int c) {
    long control_base = __metal_driver_sifive_uart0_control_base(uart);

    while (__metal_driver_sifive_uart0_txready(uart) != 0) {
        /* wait */
    }
    UART_REGW(METAL_SIFIVE_UART0_TXDATA) = c;
    return 0;
}

int __metal_driver_sifive_uart0_getc(struct metal_uart *uart, int *c) {
    uint32_t ch;
    long control_base = __metal_driver_sifive_uart0_control_base(uart);
    /* No seperate status register, we get status and the byte at same time */
    ch = UART_REGW(METAL_SIFIVE_UART0_RXDATA);
    ;
    if (ch & UART_RXEMPTY) {
        *c = -1; /* aka: EOF in most of the world */
    } else {
        *c = ch & 0x0ff;
    }
    return 0;
}

int __metal_driver_sifive_uart0_get_baud_rate(struct metal_uart *guart) {
    struct __metal_driver_sifive_uart0 *uart = (void *)guart;
    return uart->baud_rate;
}

int __metal_driver_sifive_uart0_set_baud_rate(struct metal_uart *guart,
                                              int baud_rate) {
    struct __metal_driver_sifive_uart0 *uart = (void *)guart;
    long control_base = __metal_driver_sifive_uart0_control_base(guart);
    struct metal_clock *clock = __metal_driver_sifive_uart0_clock(guart);

    uart->baud_rate = baud_rate;

    if (clock != NULL) {
        long clock_rate = clock->vtable->get_rate_hz(clock);
        UART_REGW(METAL_SIFIVE_UART0_DIV) = clock_rate / baud_rate - 1;
        UART_REGW(METAL_SIFIVE_UART0_TXCTRL) |= UART_TXEN;
        UART_REGW(METAL_SIFIVE_UART0_RXCTRL) |= UART_RXEN;
    }
    return 0;
}

static void pre_rate_change_callback_func(void *priv) {
    struct __metal_driver_sifive_uart0 *uart = priv;
    long control_base =
        __metal_driver_sifive_uart0_control_base((struct metal_uart *)priv);
    struct metal_clock *clock =
        __metal_driver_sifive_uart0_clock((struct metal_uart *)priv);

    /* Detect when the TXDATA is empty by setting the transmit watermark count
     * to one and waiting until an interrupt is pending */

    UART_REGW(METAL_SIFIVE_UART0_TXCTRL) &= ~(UART_TXCNT(0x7));
    UART_REGW(METAL_SIFIVE_UART0_TXCTRL) |= UART_TXCNT(1);

    while ((UART_REGW(METAL_SIFIVE_UART0_IP) & UART_TXWM) == 0)
        ;

    /* When the TXDATA clears, the UART is still shifting out the last byte.
     * Calculate the time we must drain to finish transmitting and then wait
     * that long. */

    long bits_per_symbol =
        (UART_REGW(METAL_SIFIVE_UART0_TXCTRL) & (1 << 1)) ? 9 : 10;
    long clk_freq = clock->vtable->get_rate_hz(clock);
    long cycles_to_wait = bits_per_symbol * clk_freq / uart->baud_rate;

    for (volatile long x = 0; x < cycles_to_wait; x++)
        __asm__("nop");
}

static void post_rate_change_callback_func(void *priv) {
    struct __metal_driver_sifive_uart0 *uart = priv;
    metal_uart_set_baud_rate(&uart->uart, uart->baud_rate);
}

void __metal_driver_sifive_uart0_init(struct metal_uart *guart, int baud_rate) {
    struct __metal_driver_sifive_uart0 *uart = (void *)(guart);
    struct metal_clock *clock = __metal_driver_sifive_uart0_clock(guart);
    struct __metal_driver_sifive_gpio0 *pinmux =
        __metal_driver_sifive_uart0_pinmux(guart);

    if (clock != NULL) {
        uart->pre_rate_change_callback.callback =
            &pre_rate_change_callback_func;
        uart->pre_rate_change_callback.priv = guart;
        metal_clock_register_pre_rate_change_callback(
            clock, &(uart->pre_rate_change_callback));

        uart->post_rate_change_callback.callback =
            &post_rate_change_callback_func;
        uart->post_rate_change_callback.priv = guart;
        metal_clock_register_post_rate_change_callback(
            clock, &(uart->post_rate_change_callback));
    }

    metal_uart_set_baud_rate(&(uart->uart), baud_rate);

    if (pinmux != NULL) {
        long pinmux_output_selector =
            __metal_driver_sifive_uart0_pinmux_output_selector(guart);
        long pinmux_source_selector =
            __metal_driver_sifive_uart0_pinmux_source_selector(guart);
        pinmux->gpio.vtable->enable_io((struct metal_gpio *)pinmux,
                                       pinmux_output_selector,
                                       pinmux_source_selector);
    }
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_sifive_uart0) = {
    .uart.init = __metal_driver_sifive_uart0_init,
    .uart.putc = __metal_driver_sifive_uart0_putc,
    .uart.getc = __metal_driver_sifive_uart0_getc,
    .uart.txready = __metal_driver_sifive_uart0_txready,
    .uart.get_baud_rate = __metal_driver_sifive_uart0_get_baud_rate,
    .uart.set_baud_rate = __metal_driver_sifive_uart0_set_baud_rate,
    .uart.controller_interrupt =
        __metal_driver_sifive_uart0_interrupt_controller,
    .uart.get_interrupt_id = __metal_driver_sifive_uart0_get_interrupt_id,
    .uart.tx_interrupt_enable = __metal_driver_sifive_uart0_tx_interrupt_enable,
    .uart.tx_interrupt_disable =
        __metal_driver_sifive_uart0_tx_interrupt_disable,
    .uart.rx_interrupt_enable = __metal_driver_sifive_uart0_rx_interrupt_enable,
    .uart.rx_interrupt_disable =
        __metal_driver_sifive_uart0_rx_interrupt_disable,
    .uart.set_tx_watermark = __metal_driver_sifive_uart0_set_tx_watermark,
    .uart.get_tx_watermark = __metal_driver_sifive_uart0_get_tx_watermark,
    .uart.set_rx_watermark = __metal_driver_sifive_uart0_set_rx_watermark,
    .uart.get_rx_watermark = __metal_driver_sifive_uart0_get_rx_watermark,
};

#endif /* METAL_SIFIVE_UART0 */

typedef int no_empty_translation_units;
