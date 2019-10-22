/* Copyright 2018 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */

#include <metal/machine/platform.h>

#ifdef METAL_SIFIVE_GPIO0

#include <metal/drivers/sifive_gpio0.h>
#include <metal/io.h>
#include <metal/machine.h>

int __metal_driver_sifive_gpio0_disable_input(struct metal_gpio *ggpio, long source)
{
    long base = __metal_driver_sifive_gpio0_base(ggpio);

    __METAL_ACCESS_ONCE((__metal_io_u32 *)(base + METAL_SIFIVE_GPIO0_INPUT_EN))  &= ~source;

    return 0;
}

long __metal_driver_sifive_gpio0_output(struct metal_gpio *ggpio)
{
    long base = __metal_driver_sifive_gpio0_base(ggpio);

    return __METAL_ACCESS_ONCE((__metal_io_u32 *)(base + METAL_SIFIVE_GPIO0_PORT));
}

int __metal_driver_sifive_gpio0_enable_output(struct metal_gpio *ggpio, long source)
{
    long base = __metal_driver_sifive_gpio0_base(ggpio);

    __METAL_ACCESS_ONCE((__metal_io_u32 *)(base + METAL_SIFIVE_GPIO0_OUTPUT_EN))  |= source;

    return 0;
}

int __metal_driver_sifive_gpio0_output_set(struct metal_gpio *ggpio, long value)
{
    long base = __metal_driver_sifive_gpio0_base(ggpio);

    __METAL_ACCESS_ONCE((__metal_io_u32 *)(base + METAL_SIFIVE_GPIO0_PORT)) |= value;

    return 0;
}

int __metal_driver_sifive_gpio0_output_clear(struct metal_gpio *ggpio, long value)
{
    long base = __metal_driver_sifive_gpio0_base(ggpio);

    __METAL_ACCESS_ONCE((__metal_io_u32 *)(base + METAL_SIFIVE_GPIO0_PORT)) &= ~value;

    return 0;
}

int __metal_driver_sifive_gpio0_output_toggle(struct metal_gpio *ggpio, long value)
{
    long base = __metal_driver_sifive_gpio0_base(ggpio);

    __METAL_ACCESS_ONCE((__metal_io_u32 *)(base + METAL_SIFIVE_GPIO0_PORT)) =
	__METAL_ACCESS_ONCE((__metal_io_u32 *)(base + METAL_SIFIVE_GPIO0_PORT)) ^ value;

    return 0;
}

int __metal_driver_sifive_gpio0_enable_io(struct metal_gpio *ggpio, long source, long dest)
{
    long base = __metal_driver_sifive_gpio0_base(ggpio);

    __METAL_ACCESS_ONCE((__metal_io_u32 *)(base + METAL_SIFIVE_GPIO0_IOF_SEL)) &= ~source;
    __METAL_ACCESS_ONCE((__metal_io_u32 *)(base + METAL_SIFIVE_GPIO0_IOF_EN))  |= dest;

    return 0;
}

__METAL_DEFINE_VTABLE(__metal_driver_vtable_sifive_gpio0) = {
    .gpio.disable_input = __metal_driver_sifive_gpio0_disable_input,
    .gpio.output        = __metal_driver_sifive_gpio0_output,
    .gpio.enable_output = __metal_driver_sifive_gpio0_enable_output,
    .gpio.output_set    = __metal_driver_sifive_gpio0_output_set,
    .gpio.output_clear  = __metal_driver_sifive_gpio0_output_clear,
    .gpio.output_toggle = __metal_driver_sifive_gpio0_output_toggle,
    .gpio.enable_io = __metal_driver_sifive_gpio0_enable_io,
};

#endif /* METAL_SIFIVE_GPIO0 */
