/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */
/* ----------------------------------- */
/* ----------------------------------- */

#ifndef ASSEMBLY

#ifndef SIFIVE_HIFIVE1_REVB____METAL_INLINE_H
#define SIFIVE_HIFIVE1_REVB____METAL_INLINE_H

#include <metal/machine.h>


/* --------------------- fixed_clock ------------ */
extern inline unsigned long __metal_driver_fixed_clock_rate(const struct metal_clock *clock);


/* --------------------- fixed_factor_clock ------------ */


/* --------------------- sifive_clint0 ------------ */
extern inline unsigned long __metal_driver_sifive_clint0_control_base(struct metal_interrupt *controller);
extern inline unsigned long __metal_driver_sifive_clint0_control_size(struct metal_interrupt *controller);
extern inline int __metal_driver_sifive_clint0_num_interrupts(struct metal_interrupt *controller);
extern inline struct metal_interrupt * __metal_driver_sifive_clint0_interrupt_parents(struct metal_interrupt *controller, int idx);
extern inline int __metal_driver_sifive_clint0_interrupt_lines(struct metal_interrupt *controller, int idx);


/* --------------------- cpu ------------ */
extern inline int __metal_driver_cpu_hartid(struct metal_cpu *cpu);
extern inline int __metal_driver_cpu_timebase(struct metal_cpu *cpu);
extern inline struct metal_interrupt * __metal_driver_cpu_interrupt_controller(struct metal_cpu *cpu);
extern inline int __metal_driver_cpu_num_pmp_regions(struct metal_cpu *cpu);


/* --------------------- sifive_plic0 ------------ */
extern inline unsigned long __metal_driver_sifive_plic0_control_base(struct metal_interrupt *controller);
extern inline unsigned long __metal_driver_sifive_plic0_control_size(struct metal_interrupt *controller);
extern inline int __metal_driver_sifive_plic0_num_interrupts(struct metal_interrupt *controller);
extern inline int __metal_driver_sifive_plic0_max_priority(struct metal_interrupt *controller);
extern inline struct metal_interrupt * __metal_driver_sifive_plic0_interrupt_parents(struct metal_interrupt *controller, int idx);
extern inline int __metal_driver_sifive_plic0_interrupt_lines(struct metal_interrupt *controller, int idx);


/* --------------------- sifive_clic0 ------------ */


/* --------------------- sifive_local_external_interrupts0 ------------ */
extern inline struct metal_interrupt * __metal_driver_sifive_local_external_interrupts0_interrupt_parent(struct metal_interrupt *controller);
extern inline int __metal_driver_sifive_local_external_interrupts0_num_interrupts(struct metal_interrupt *controller);
extern inline int __metal_driver_sifive_local_external_interrupts0_interrupt_lines(struct metal_interrupt *controller, int idx);


/* --------------------- sifive_global_external_interrupts0 ------------ */


/* --------------------- sifive_gpio0 ------------ */
extern inline unsigned long __metal_driver_sifive_gpio0_base(struct metal_gpio *gpio);
extern inline unsigned long __metal_driver_sifive_gpio0_size(struct metal_gpio *gpio);
extern inline int __metal_driver_sifive_gpio0_num_interrupts(struct metal_gpio *gpio);
extern inline struct metal_interrupt * __metal_driver_sifive_gpio0_interrupt_parent(struct metal_gpio *gpio);
extern inline int __metal_driver_sifive_gpio0_interrupt_lines(struct metal_gpio *gpio, int idx);


/* --------------------- sifive_gpio_button ------------ */


/* --------------------- sifive_gpio_led ------------ */
extern inline struct metal_gpio * __metal_driver_sifive_gpio_led_gpio(struct metal_led *led);
extern inline int __metal_driver_sifive_gpio_led_pin(struct metal_led *led);
extern inline char * __metal_driver_sifive_gpio_led_label(struct metal_led *led);


/* --------------------- sifive_gpio_switch ------------ */


/* --------------------- sifive_spi0 ------------ */
extern inline unsigned long __metal_driver_sifive_spi0_control_base(struct metal_spi *spi);
extern inline unsigned long __metal_driver_sifive_spi0_control_size(struct metal_spi *spi);
extern inline struct __metal_driver_sifive_gpio0 * __metal_driver_sifive_spi0_pinmux(struct metal_spi *spi);
extern inline unsigned long __metal_driver_sifive_spi0_pinmux_output_selector(struct metal_spi *spi);
extern inline unsigned long __metal_driver_sifive_spi0_pinmux_source_selector(struct metal_spi *spi);


/* --------------------- sifive_test0 ------------ */


/* --------------------- sifive_uart0 ------------ */
extern inline unsigned long __metal_driver_sifive_uart0_control_base(struct metal_uart *uart);
extern inline unsigned long __metal_driver_sifive_uart0_control_size(struct metal_uart *uart);
extern inline int __metal_driver_sifive_uart0_num_interrupts(struct metal_uart *uart);
extern inline struct metal_interrupt * __metal_driver_sifive_uart0_interrupt_parent(struct metal_uart *uart);
extern inline int __metal_driver_sifive_uart0_interrupt_line(struct metal_uart *uart);
extern inline struct metal_clock * __metal_driver_sifive_uart0_clock(struct metal_uart *uart);
extern inline struct __metal_driver_sifive_gpio0 * __metal_driver_sifive_uart0_pinmux(struct metal_uart *uart);
extern inline unsigned long __metal_driver_sifive_uart0_pinmux_output_selector(struct metal_uart *uart);
extern inline unsigned long __metal_driver_sifive_uart0_pinmux_source_selector(struct metal_uart *uart);


/* --------------------- sifive_fe310_g000_hfrosc ------------ */
extern inline struct metal_clock * __metal_driver_sifive_fe310_g000_hfrosc_ref(const struct metal_clock *clock);
extern inline struct __metal_driver_sifive_fe310_g000_prci * __metal_driver_sifive_fe310_g000_hfrosc_config_base(const struct metal_clock *clock);
extern inline const struct __metal_driver_vtable_sifive_fe310_g000_prci * __metal_driver_sifive_fe310_g000_hfrosc_config_vtable(struct metal_clock *clock);
extern inline long __metal_driver_sifive_fe310_g000_hfrosc_config_offset(const struct metal_clock *clock);


/* --------------------- sifive_fe310_g000_hfxosc ------------ */
extern inline struct metal_clock * __metal_driver_sifive_fe310_g000_hfxosc_ref(const struct metal_clock *clock);
extern inline struct __metal_driver_sifive_fe310_g000_prci * __metal_driver_sifive_fe310_g000_hfxosc_config_base(const struct metal_clock *clock);
extern inline long __metal_driver_sifive_fe310_g000_hfxosc_config_offset(const struct metal_clock *clock);


/* --------------------- sifive_fe310_g000_pll ------------ */
extern inline struct metal_clock * __metal_driver_sifive_fe310_g000_pll_pllsel0(const struct metal_clock *clock);
extern inline struct metal_clock * __metal_driver_sifive_fe310_g000_pll_pllref(const struct metal_clock *clock);
extern inline struct __metal_driver_sifive_fe310_g000_prci * __metal_driver_sifive_fe310_g000_pll_config_base( );
extern inline long __metal_driver_sifive_fe310_g000_pll_config_offset( );
extern inline struct __metal_driver_sifive_fe310_g000_prci * __metal_driver_sifive_fe310_g000_pll_divider_base(const struct metal_clock *clock);
extern inline long __metal_driver_sifive_fe310_g000_pll_divider_offset(const struct metal_clock *clock);
extern inline long __metal_driver_sifive_fe310_g000_pll_init_rate( );


/* --------------------- fe310_g000_prci ------------ */
extern inline long __metal_driver_sifive_fe310_g000_prci_base( );
extern inline long __metal_driver_sifive_fe310_g000_prci_size( );
extern inline const struct __metal_driver_vtable_sifive_fe310_g000_prci * __metal_driver_sifive_fe310_g000_prci_vtable( );


/* --------------------- sifive_fu540_c000_l2 ------------ */


/* From clock@0 */
struct __metal_driver_fixed_clock __metal_dt_clock_0 = {
    .clock.vtable = &__metal_driver_vtable_fixed_clock.clock,
};

/* From clock@2 */
struct __metal_driver_fixed_clock __metal_dt_clock_2 = {
    .clock.vtable = &__metal_driver_vtable_fixed_clock.clock,
};

/* From clock@5 */
struct __metal_driver_fixed_clock __metal_dt_clock_5 = {
    .clock.vtable = &__metal_driver_vtable_fixed_clock.clock,
};

struct metal_memory __metal_dt_mem_dtim_80000000 = {
    ._base_address = 2147483648UL,
    ._size = 16384UL,
    ._attrs = {
        .R = 1,
        .W = 1,
        .X = 1,
        .C = 1,
        .A = 1},
};

struct metal_memory __metal_dt_mem_spi_10014000 = {
    ._base_address = 536870912UL,
    ._size = 500000UL,
    ._attrs = {
        .R = 1,
        .W = 1,
        .X = 1,
        .C = 1,
        .A = 1},
};

/* From clint@2000000 */
struct __metal_driver_riscv_clint0 __metal_dt_clint_2000000 = {
    .controller.vtable = &__metal_driver_vtable_riscv_clint0.clint_vtable,
    .init_done = 0,
};

/* From cpu@0 */
struct __metal_driver_cpu __metal_dt_cpu_0 = {
    .cpu.vtable = &__metal_driver_vtable_cpu.cpu_vtable,
};

/* From interrupt_controller */
struct __metal_driver_riscv_cpu_intc __metal_dt_cpu_0_interrupt_controller = {
    .controller.vtable = &__metal_driver_vtable_riscv_cpu_intc.controller_vtable,
    .init_done = 0,
};

/* From interrupt_controller@c000000 */
struct __metal_driver_riscv_plic0 __metal_dt_interrupt_controller_c000000 = {
    .controller.vtable = &__metal_driver_vtable_riscv_plic0.plic_vtable,
    .init_done = 0,
};

/* From local_external_interrupts_0 */
struct __metal_driver_sifive_local_external_interrupts0 __metal_dt_local_external_interrupts_0 = {
    .irc.vtable = &__metal_driver_vtable_sifive_local_external_interrupts0.local0_vtable,
    .init_done = 0,
};

/* From gpio@10012000 */
struct __metal_driver_sifive_gpio0 __metal_dt_gpio_10012000 = {
    .gpio.vtable = &__metal_driver_vtable_sifive_gpio0.gpio,
};

/* From led@0red */
struct __metal_driver_sifive_gpio_led __metal_dt_led_0red = {
    .led.vtable = &__metal_driver_vtable_sifive_led.led_vtable,
};

/* From led@0green */
struct __metal_driver_sifive_gpio_led __metal_dt_led_0green = {
    .led.vtable = &__metal_driver_vtable_sifive_led.led_vtable,
};

/* From led@0blue */
struct __metal_driver_sifive_gpio_led __metal_dt_led_0blue = {
    .led.vtable = &__metal_driver_vtable_sifive_led.led_vtable,
};

/* From spi@10014000 */
struct __metal_driver_sifive_spi0 __metal_dt_spi_10014000 = {
    .spi.vtable = &__metal_driver_vtable_sifive_spi0.spi,
};

/* From serial@10013000 */
struct __metal_driver_sifive_uart0 __metal_dt_serial_10013000 = {
    .uart.vtable = &__metal_driver_vtable_sifive_uart0.uart,
};

/* From clock@3 */
struct __metal_driver_sifive_fe310_g000_hfrosc __metal_dt_clock_3 = {
    .clock.vtable = &__metal_driver_vtable_sifive_fe310_g000_hfrosc.clock,
};

/* From clock@1 */
struct __metal_driver_sifive_fe310_g000_hfxosc __metal_dt_clock_1 = {
    .clock.vtable = &__metal_driver_vtable_sifive_fe310_g000_hfxosc.clock,
};

/* From clock@4 */
struct __metal_driver_sifive_fe310_g000_pll __metal_dt_clock_4 = {
    .clock.vtable = &__metal_driver_vtable_sifive_fe310_g000_pll.clock,
};

/* From prci@10008000 */
struct __metal_driver_sifive_fe310_g000_prci __metal_dt_prci_10008000 = {
};


#endif /* SIFIVE_HIFIVE1_REVB____METAL_INLINE_H*/
#endif /* ! ASSEMBLY */
