/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_UCB_HTIF0

#include <metal/drivers/ucb_htif0.h>
#include <metal/io.h>
#include <stddef.h>
#include <stdint.h>

#define FINISHER_OFFSET 0

volatile uint64_t fromhost __attribute__((aligned(4096)));
volatile uint64_t tohost __attribute__((aligned(4096)));

#if __riscv_xlen == 64
#define TOHOST_CMD(dev, cmd, payload)                                          \
    (((uint64_t)(dev) << 56) | ((uint64_t)(cmd) << 48) | (uint64_t)(payload))
#else
#define TOHOST_CMD(dev, cmd, payload)                                          \
    ({                                                                         \
        if ((dev) || (cmd))                                                    \
            __builtin_trap();                                                  \
        (payload);                                                             \
    })
#endif
#define FROMHOST_DEV(fromhost_value) ((uint64_t)(fromhost_value) >> 56)
#define FROMHOST_CMD(fromhost_value) ((uint64_t)(fromhost_value) << 8 >> 56)
#define FROMHOST_DATA(fromhost_value) ((uint64_t)(fromhost_value) << 16 >> 16)

static void __check_fromhost() {
    uint64_t fh = fromhost;
    if (!fh)
        return;
    fromhost = 0;
}

static void __set_tohost(uintptr_t dev, uintptr_t cmd, uintptr_t data) {
    while (tohost)
        __check_fromhost();
    tohost = TOHOST_CMD(dev, cmd, data);
}

static void do_tohost_fromhost(uintptr_t dev, uintptr_t cmd, uintptr_t data) {
    __set_tohost(dev, cmd, data);

    while (1) {
        uint64_t fh = fromhost;
        if (fh) {
            if (FROMHOST_DEV(fh) == dev && FROMHOST_CMD(fh) == cmd) {
                fromhost = 0;
                break;
            }
            __check_fromhost();
        }
    }
}

void __metal_driver_ucb_htif0_init(struct metal_uart *uart, int baud_rate) {}

void __metal_driver_ucb_htif0_exit(const struct __metal_shutdown *sd,
                                   int code) {
    volatile uint64_t magic_mem[8];
    magic_mem[0] = 93; // SYS_exit
    magic_mem[1] = code;
    magic_mem[2] = 0;
    magic_mem[3] = 0;

    do_tohost_fromhost(0, 0, (uintptr_t)magic_mem);

    while (1) {
        // loop forever
    }
}

int __metal_driver_ucb_htif0_putc(struct metal_uart *htif, int c) {
    volatile uint64_t magic_mem[8];
    magic_mem[0] = 64; // SYS_write
    magic_mem[1] = 1;
    magic_mem[2] = (uintptr_t)&c;
    magic_mem[3] = 1;

    do_tohost_fromhost(0, 0, (uintptr_t)magic_mem);

    return 0;
}

int __metal_driver_ucb_htif0_getc(struct metal_uart *htif, int *c) {
    return -1;
}

int __metal_driver_ucb_htif0_get_baud_rate(struct metal_uart *guart) {
    return 0;
}

int __metal_driver_ucb_htif0_set_baud_rate(struct metal_uart *guart,
                                           int baud_rate) {
    return 0;
}

struct metal_interrupt *
__metal_driver_ucb_htif0_interrupt_controller(struct metal_uart *uart) {
    return NULL;
}

int __metal_driver_ucb_htif0_get_interrupt_id(struct metal_uart *uart) {
    return -1;
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_ucb_htif0_shutdown) = {
    .shutdown.exit = &__metal_driver_ucb_htif0_exit,
};

__METAL_DEFINE_VTABLE(__metal_driver_vtable_ucb_htif0_uart) = {
    .uart.init = __metal_driver_ucb_htif0_init,
    .uart.putc = __metal_driver_ucb_htif0_putc,
    .uart.getc = __metal_driver_ucb_htif0_getc,
    .uart.get_baud_rate = __metal_driver_ucb_htif0_get_baud_rate,
    .uart.set_baud_rate = __metal_driver_ucb_htif0_set_baud_rate,
    .uart.controller_interrupt = __metal_driver_ucb_htif0_interrupt_controller,
    .uart.get_interrupt_id = __metal_driver_ucb_htif0_get_interrupt_id,
};

#endif /* METAL_UCB_HTIF0 */

typedef int no_empty_translation_units;
