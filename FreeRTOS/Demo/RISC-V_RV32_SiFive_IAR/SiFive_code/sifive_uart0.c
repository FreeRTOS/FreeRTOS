/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_SIFIVE_UART0

#include <metal/drivers/sifive_uart0.h>
#include <metal/machine.h>

/* TXDATA Fields */
#define UART_TXEN               (1 <<  0)
#define UART_TXFULL             (1 << 31)

/* RXDATA Fields */
#define UART_RXEN               (1 <<  0)
#define UART_RXEMPTY            (1 << 31)

/* TXCTRL Fields */
#define UART_NSTOP              (1 <<  1)
#define UART_TXCNT(count)       ((0x7 & count) << 16)

/* IP Fields */
#define UART_TXWM               (1 <<  0)

#define UART_REG(offset)   (((unsigned long)control_base + offset))
#define UART_REGB(offset)  (__METAL_ACCESS_ONCE((__metal_io_u8  *)UART_REG(offset)))
#define UART_REGW(offset)  (__METAL_ACCESS_ONCE((__metal_io_u32 *)UART_REG(offset)))

struct metal_interrupt *
__metal_driver_sifive_uart0_interrupt_controller(struct metal_uart *uart)
{
    return __metal_driver_sifive_uart0_interrupt_parent(uart);
}

int __metal_driver_sifive_uart0_get_interrupt_id(struct metal_uart *uart)
{
    return (__metal_driver_sifive_uart0_interrupt_line(uart) + METAL_INTERRUPT_ID_GL0);
}

int __metal_driver_sifive_uart0_putc(struct metal_uart *uart, unsigned char c)
{
    long control_base = __metal_driver_sifive_uart0_control_base(uart);

    while ((UART_REGW(METAL_SIFIVE_UART0_TXDATA) & UART_TXFULL) != 0) { }
    UART_REGW(METAL_SIFIVE_UART0_TXDATA) = c;
    return 0;
}

int __metal_driver_sifive_uart0_getc(struct metal_uart *uart, unsigned char *c)
{
    uint32_t ch = UART_RXEMPTY;
    long control_base = __metal_driver_sifive_uart0_control_base(uart);

    while (ch & UART_RXEMPTY) {
        ch = UART_REGW(METAL_SIFIVE_UART0_RXDATA);
    }
    *c = ch & 0xff;
    return 0;
}

int __metal_driver_sifive_uart0_get_baud_rate(struct metal_uart *guart)
{
    struct __metal_driver_sifive_uart0 *uart = (void *)guart;
    return uart->baud_rate;
}

int __metal_driver_sifive_uart0_set_baud_rate(struct metal_uart *guart, int baud_rate)
{
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

static void pre_rate_change_callback(void *priv)
{
    struct __metal_driver_sifive_uart0 *uart = priv;
    long control_base = __metal_driver_sifive_uart0_control_base((struct metal_uart *)priv);
    struct metal_clock *clock = __metal_driver_sifive_uart0_clock((struct metal_uart *)priv);

    /* Detect when the TXDATA is empty by setting the transmit watermark count
     * to one and waiting until an interrupt is pending */

    UART_REGW(METAL_SIFIVE_UART0_TXCTRL) &= ~(UART_TXCNT(0x7));
    UART_REGW(METAL_SIFIVE_UART0_TXCTRL) |= UART_TXCNT(1);

    while((UART_REGW(METAL_SIFIVE_UART0_IP) & UART_TXWM) == 0) ;

    /* When the TXDATA clears, the UART is still shifting out the last byte.
     * Calculate the time we must drain to finish transmitting and then wait
     * that long. */

    long bits_per_symbol = (UART_REGW(METAL_SIFIVE_UART0_TXCTRL) & (1 << 1)) ? 9 : 10;
    long clk_freq = clock->vtable->get_rate_hz(clock);
    long cycles_to_wait = bits_per_symbol * clk_freq / uart->baud_rate;

    for(volatile long x = 0; x < cycles_to_wait; x++)
        asm("nop");
}

static void post_rate_change_callback(void *priv)
{
    struct __metal_driver_sifive_uart0 *uart = priv;
    metal_uart_set_baud_rate(&uart->uart, uart->baud_rate);
}

void __metal_driver_sifive_uart0_init(struct metal_uart *guart, int baud_rate)
{
    struct __metal_driver_sifive_uart0 *uart = (void *)(guart);
    struct metal_clock *clock = __metal_driver_sifive_uart0_clock(guart);
    struct __metal_driver_sifive_gpio0 *pinmux = __metal_driver_sifive_uart0_pinmux(guart);

    if(clock != NULL) {
        metal_clock_register_pre_rate_change_callback(clock, &pre_rate_change_callback, guart);
        metal_clock_register_post_rate_change_callback(clock, &post_rate_change_callback, guart);
    }

    metal_uart_set_baud_rate(&(uart->uart), baud_rate);

    if (pinmux != NULL) {
        long pinmux_output_selector = __metal_driver_sifive_uart0_pinmux_output_selector(guart);
        long pinmux_source_selector = __metal_driver_sifive_uart0_pinmux_source_selector(guart);
        pinmux->gpio.vtable->enable_io(
            (struct metal_gpio *) pinmux,
            pinmux_output_selector,
            pinmux_source_selector
        );
    }
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_sifive_uart0) = {
    .uart.init          = __metal_driver_sifive_uart0_init,
    .uart.putc          = __metal_driver_sifive_uart0_putc,
    .uart.getc          = __metal_driver_sifive_uart0_getc,
    .uart.get_baud_rate = __metal_driver_sifive_uart0_get_baud_rate,
    .uart.set_baud_rate = __metal_driver_sifive_uart0_set_baud_rate,
    .uart.controller_interrupt = __metal_driver_sifive_uart0_interrupt_controller,
    .uart.get_interrupt_id     = __metal_driver_sifive_uart0_get_interrupt_id,
};

#endif /* METAL_SIFIVE_UART0 */
