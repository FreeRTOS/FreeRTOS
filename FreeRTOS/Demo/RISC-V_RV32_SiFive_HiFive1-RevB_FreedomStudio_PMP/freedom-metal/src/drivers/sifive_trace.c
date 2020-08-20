/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_SIFIVE_TRACE

#include <metal/drivers/sifive_trace.h>
#include <metal/machine.h>

#define TRACE_REG(offset) (((unsigned long)base + (offset)))
#define TRACE_REG8(offset)                                                     \
    (__METAL_ACCESS_ONCE((__metal_io_u8 *)TRACE_REG(offset)))
#define TRACE_REG16(offset)                                                    \
    (__METAL_ACCESS_ONCE((__metal_io_u16 *)TRACE_REG(offset)))
#define TRACE_REG32(offset)                                                    \
    (__METAL_ACCESS_ONCE((__metal_io_u32 *)TRACE_REG(offset)))

static void write_itc_uint32(struct metal_uart *trace, uint32_t data) {
    long base = __metal_driver_sifive_trace_base(trace);

    TRACE_REG32(METAL_SIFIVE_TRACE_ITCSTIMULUS) = data;
}

static void write_itc_uint16(struct metal_uart *trace, uint16_t data) {
    long base = __metal_driver_sifive_trace_base(trace);

    TRACE_REG16(METAL_SIFIVE_TRACE_ITCSTIMULUS + 2) = data;
}

static void write_itc_uint8(struct metal_uart *trace, uint8_t data) {
    long base = __metal_driver_sifive_trace_base(trace);

    TRACE_REG8(METAL_SIFIVE_TRACE_ITCSTIMULUS + 3) = data;
}

int __metal_driver_sifive_trace_putc(struct metal_uart *trace,
                                     unsigned char c) {
    static uint32_t buffer = 0;
    static int bytes_in_buffer = 0;

    buffer |= (((uint32_t)c) << (bytes_in_buffer * 8));

    bytes_in_buffer += 1;

    if (bytes_in_buffer >= 4) {
        write_itc_uint32(trace, buffer);

        buffer = 0;
        bytes_in_buffer = 0;
    } else if ((c == '\n') || (c == '\r')) { // partial write
        switch (bytes_in_buffer) {
        case 3: // do a full word write
            write_itc_uint16(trace, (uint16_t)(buffer));
            write_itc_uint8(trace, (uint8_t)(buffer >> 16));
            break;
        case 2: // do a 16 bit write
            write_itc_uint16(trace, (uint16_t)buffer);
            break;
        case 1: // do a 1 byte write
            write_itc_uint8(trace, (uint8_t)buffer);
            break;
        }

        buffer = 0;
        bytes_in_buffer = 0;
    }

    return (int)c;
}

void __metal_driver_sifive_trace_init(struct metal_uart *trace, int baud_rate) {
    // The only init we do here is to make sure ITC 0 is enabled. It is up to
    // Freedom Studio or other mechanisms to make sure tracing is enabled. If we
    // try to enable tracing here, it will likely conflict with Freedom Studio,
    // and they will just fight with each other.

    long base = __metal_driver_sifive_trace_base(trace);

    TRACE_REG32(METAL_SIFIVE_TRACE_ITCTRACEENABLE) |= 0x00000001;
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_sifive_trace) = {
    .uart.init = __metal_driver_sifive_trace_init,
    .uart.putc = __metal_driver_sifive_trace_putc,
    .uart.getc = NULL,

    .uart.get_baud_rate = NULL,
    .uart.set_baud_rate = NULL,

    .uart.controller_interrupt = NULL,
    .uart.get_interrupt_id = NULL,
};

#endif /* METAL_SIFIVE_TRACE */
