/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */
/* ----------------------------------- */
/* ----------------------------------- */

#ifndef ASSEMBLY

#include <metal/machine/platform.h>

#ifdef __METAL_MACHINE_MACROS

#ifndef MACROS_IF_SIFIVE_HIFIVE1_REVB____METAL_H
#define MACROS_IF_SIFIVE_HIFIVE1_REVB____METAL_H

#define __METAL_CLINT_NUM_PARENTS 2

#ifndef __METAL_CLINT_NUM_PARENTS
#define __METAL_CLINT_NUM_PARENTS 0
#endif
#define __METAL_PLIC_SUBINTERRUPTS 27

#define __METAL_PLIC_NUM_PARENTS 1

#ifndef __METAL_PLIC_SUBINTERRUPTS
#define __METAL_PLIC_SUBINTERRUPTS 0
#endif
#ifndef __METAL_PLIC_NUM_PARENTS
#define __METAL_PLIC_NUM_PARENTS 0
#endif
#ifndef __METAL_CLIC_SUBINTERRUPTS
#define __METAL_CLIC_SUBINTERRUPTS 0
#endif

#endif /* MACROS_IF_SIFIVE_HIFIVE1_REVB____METAL_H*/

#else /* ! __METAL_MACHINE_MACROS */

#ifndef MACROS_ELSE_SIFIVE_HIFIVE1_REVB____METAL_H
#define MACROS_ELSE_SIFIVE_HIFIVE1_REVB____METAL_H

#define __METAL_CLINT_2000000_INTERRUPTS 2

#define METAL_MAX_CLINT_INTERRUPTS 2

#define __METAL_CLINT_NUM_PARENTS 2

#define __METAL_INTERRUPT_CONTROLLER_C000000_INTERRUPTS 1

#define __METAL_PLIC_SUBINTERRUPTS 27

#define METAL_MAX_PLIC_INTERRUPTS 1

#define __METAL_PLIC_NUM_PARENTS 1

#define __METAL_CLIC_SUBINTERRUPTS 0
#define METAL_MAX_CLIC_INTERRUPTS 0

#define __METAL_LOCAL_EXTERNAL_INTERRUPTS_0_INTERRUPTS 16

#define METAL_MAX_LOCAL_EXT_INTERRUPTS 16

#define METAL_MAX_GLOBAL_EXT_INTERRUPTS 0

#define __METAL_GPIO_10012000_INTERRUPTS 16

#define METAL_MAX_GPIO_INTERRUPTS 16

#define __METAL_SERIAL_10013000_INTERRUPTS 1

#define METAL_MAX_UART_INTERRUPTS 1


#include <metal/drivers/fixed-clock.h>
#include <metal/memory.h>
#include <metal/drivers/riscv_clint0.h>
#include <metal/drivers/riscv_cpu.h>
#include <metal/drivers/riscv_plic0.h>
#include <metal/pmp.h>
#include <metal/drivers/sifive_local-external-interrupts0.h>
#include <metal/drivers/sifive_gpio0.h>
#include <metal/drivers/sifive_gpio-leds.h>
#include <metal/drivers/sifive_spi0.h>
#include <metal/drivers/sifive_uart0.h>
#include <metal/drivers/sifive_fe310-g000_hfrosc.h>
#include <metal/drivers/sifive_fe310-g000_hfxosc.h>
#include <metal/drivers/sifive_fe310-g000_pll.h>
#include <metal/drivers/sifive_fe310-g000_prci.h>

/* From clock@0 */
struct __metal_driver_fixed_clock __metal_dt_clock_0;

/* From clock@2 */
struct __metal_driver_fixed_clock __metal_dt_clock_2;

/* From clock@5 */
struct __metal_driver_fixed_clock __metal_dt_clock_5;

struct metal_memory __metal_dt_mem_dtim_80000000;

struct metal_memory __metal_dt_mem_spi_10014000;

/* From clint@2000000 */
struct __metal_driver_riscv_clint0 __metal_dt_clint_2000000;

/* From cpu@0 */
struct __metal_driver_cpu __metal_dt_cpu_0;

struct __metal_driver_riscv_cpu_intc __metal_dt_cpu_0_interrupt_controller;

/* From interrupt_controller@c000000 */
struct __metal_driver_riscv_plic0 __metal_dt_interrupt_controller_c000000;

struct metal_pmp __metal_dt_pmp;

/* From local_external_interrupts_0 */
struct __metal_driver_sifive_local_external_interrupts0 __metal_dt_local_external_interrupts_0;

/* From gpio@10012000 */
struct __metal_driver_sifive_gpio0 __metal_dt_gpio_10012000;

/* From led@0red */
struct __metal_driver_sifive_gpio_led __metal_dt_led_0red;

/* From led@0green */
struct __metal_driver_sifive_gpio_led __metal_dt_led_0green;

/* From led@0blue */
struct __metal_driver_sifive_gpio_led __metal_dt_led_0blue;

/* From spi@10014000 */
struct __metal_driver_sifive_spi0 __metal_dt_spi_10014000;

/* From serial@10013000 */
struct __metal_driver_sifive_uart0 __metal_dt_serial_10013000;

/* From clock@3 */
struct __metal_driver_sifive_fe310_g000_hfrosc __metal_dt_clock_3;

/* From clock@1 */
struct __metal_driver_sifive_fe310_g000_hfxosc __metal_dt_clock_1;

/* From clock@4 */
struct __metal_driver_sifive_fe310_g000_pll __metal_dt_clock_4;

/* From prci@10008000 */
struct __metal_driver_sifive_fe310_g000_prci __metal_dt_prci_10008000;



/* --------------------- fixed_clock ------------ */
static inline unsigned long __metal_driver_fixed_clock_rate(const struct metal_clock *clock)
{
	if ((uintptr_t)clock == (uintptr_t)&__metal_dt_clock_0) {
		return METAL_FIXED_CLOCK_0_CLOCK_FREQUENCY;
	}
	else if ((uintptr_t)clock == (uintptr_t)&__metal_dt_clock_2) {
		return METAL_FIXED_CLOCK_2_CLOCK_FREQUENCY;
	}
	else if ((uintptr_t)clock == (uintptr_t)&__metal_dt_clock_5) {
		return METAL_FIXED_CLOCK_5_CLOCK_FREQUENCY;
	}
	else {
		return 0;
	}
}



/* --------------------- fixed_factor_clock ------------ */


/* --------------------- sifive_clint0 ------------ */
static inline unsigned long __metal_driver_sifive_clint0_control_base(struct metal_interrupt *controller)
{
	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_clint_2000000) {
		return METAL_RISCV_CLINT0_2000000_BASE_ADDRESS;
	}
	else {
		return 0;
	}
}

static inline unsigned long __metal_driver_sifive_clint0_control_size(struct metal_interrupt *controller)
{
	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_clint_2000000) {
		return METAL_RISCV_CLINT0_2000000_SIZE;
	}
	else {
		return 0;
	}
}

static inline int __metal_driver_sifive_clint0_num_interrupts(struct metal_interrupt *controller)
{
	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_clint_2000000) {
		return METAL_MAX_CLINT_INTERRUPTS;
	}
	else {
		return 0;
	}
}

static inline struct metal_interrupt * __metal_driver_sifive_clint0_interrupt_parents(struct metal_interrupt *controller, int idx)
{
	if (idx == 0) {
		return (struct metal_interrupt *)&__metal_dt_cpu_0_interrupt_controller.controller;
	}
	else if (idx == 1) {
		return (struct metal_interrupt *)&__metal_dt_cpu_0_interrupt_controller.controller;
	}
	else {
		return NULL;
	}
}

static inline int __metal_driver_sifive_clint0_interrupt_lines(struct metal_interrupt *controller, int idx)
{
	if (idx == 0) {
		return 3;
	}
	else if (idx == 1) {
		return 7;
	}
	else {
		return 0;
	}
}



/* --------------------- cpu ------------ */
static inline int __metal_driver_cpu_hartid(struct metal_cpu *cpu)
{
	if ((uintptr_t)cpu == (uintptr_t)&__metal_dt_cpu_0) {
		return 0;
	}
	else {
		return -1;
	}
}

static inline int __metal_driver_cpu_timebase(struct metal_cpu *cpu)
{
	if ((uintptr_t)cpu == (uintptr_t)&__metal_dt_cpu_0) {
		return 1000000;
	}
	else {
		return 0;
	}
}

static inline struct metal_interrupt * __metal_driver_cpu_interrupt_controller(struct metal_cpu *cpu)
{
	if ((uintptr_t)cpu == (uintptr_t)&__metal_dt_cpu_0) {
		return &__metal_dt_cpu_0_interrupt_controller.controller;
	}
	else {
		return NULL;
	}
}

static inline int __metal_driver_cpu_num_pmp_regions(struct metal_cpu *cpu)
{
	if ((uintptr_t)cpu == (uintptr_t)&__metal_dt_cpu_0) {
		return 8;
	}
	else {
		return 0;
	}
}



/* --------------------- sifive_plic0 ------------ */
static inline unsigned long __metal_driver_sifive_plic0_control_base(struct metal_interrupt *controller)
{
	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_interrupt_controller_c000000) {
		return METAL_RISCV_PLIC0_C000000_BASE_ADDRESS;
	}
	else {
		return 0;
	}
}

static inline unsigned long __metal_driver_sifive_plic0_control_size(struct metal_interrupt *controller)
{
	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_interrupt_controller_c000000) {
		return METAL_RISCV_PLIC0_C000000_SIZE;
	}
	else {
		return 0;
	}
}

static inline int __metal_driver_sifive_plic0_num_interrupts(struct metal_interrupt *controller)
{
	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_interrupt_controller_c000000) {
		return METAL_RISCV_PLIC0_C000000_RISCV_NDEV;
	}
	else {
		return 0;
	}
}

static inline int __metal_driver_sifive_plic0_max_priority(struct metal_interrupt *controller)
{
	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_interrupt_controller_c000000) {
		return METAL_RISCV_PLIC0_C000000_RISCV_MAX_PRIORITY;
	}
	else {
		return 0;
	}
}

static inline struct metal_interrupt * __metal_driver_sifive_plic0_interrupt_parents(struct metal_interrupt *controller, int idx)
{
	if (idx == 0) {
		return (struct metal_interrupt *)&__metal_dt_cpu_0_interrupt_controller.controller;
	}
	else if (idx == 0) {
		return (struct metal_interrupt *)&__metal_dt_cpu_0_interrupt_controller.controller;
	}
	else {
		return NULL;
	}
}

static inline int __metal_driver_sifive_plic0_interrupt_lines(struct metal_interrupt *controller, int idx)
{
	if (idx == 0) {
		return 11;
	}
	else if (idx == 0) {
		return 11;
	}
	else {
		return 0;
	}
}



/* --------------------- sifive_clic0 ------------ */


/* --------------------- sifive_local_external_interrupts0 ------------ */
static inline struct metal_interrupt * __metal_driver_sifive_local_external_interrupts0_interrupt_parent(struct metal_interrupt *controller)
{
	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_local_external_interrupts_0) {
		return (struct metal_interrupt *)&__metal_dt_cpu_0_interrupt_controller.controller;
	}
	else {
		return NULL;
	}
}

static inline int __metal_driver_sifive_local_external_interrupts0_num_interrupts(struct metal_interrupt *controller)
{
	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_local_external_interrupts_0) {
		return METAL_MAX_LOCAL_EXT_INTERRUPTS;
	}
	else {
		return 0;
	}
}

static inline int __metal_driver_sifive_local_external_interrupts0_interrupt_lines(struct metal_interrupt *controller, int idx)
{
	if (idx == 0) {
		return 16;
	}
	else if (idx == 1) {
		return 17;
	}
	else if (idx == 2) {
		return 18;
	}
	else if (idx == 3) {
		return 19;
	}
	else if (idx == 4) {
		return 20;
	}
	else if (idx == 5) {
		return 21;
	}
	else if (idx == 6) {
		return 22;
	}
	else if (idx == 7) {
		return 23;
	}
	else if (idx == 8) {
		return 24;
	}
	else if (idx == 9) {
		return 25;
	}
	else if (idx == 10) {
		return 26;
	}
	else if (idx == 11) {
		return 27;
	}
	else if (idx == 12) {
		return 28;
	}
	else if (idx == 13) {
		return 29;
	}
	else if (idx == 14) {
		return 30;
	}
	else if (idx == 15) {
		return 31;
	}
	else {
		return 0;
	}
}



/* --------------------- sifive_global_external_interrupts0 ------------ */


/* --------------------- sifive_gpio0 ------------ */
static inline unsigned long __metal_driver_sifive_gpio0_base(struct metal_gpio *gpio)
{
	if ((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) {
		return METAL_SIFIVE_GPIO0_10012000_BASE_ADDRESS;
	}
	else {
		return 0;
	}
}

static inline unsigned long __metal_driver_sifive_gpio0_size(struct metal_gpio *gpio)
{
	if ((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) {
		return METAL_SIFIVE_GPIO0_10012000_SIZE;
	}
	else {
		return 0;
	}
}

static inline int __metal_driver_sifive_gpio0_num_interrupts(struct metal_gpio *gpio)
{
	if ((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) {
		return METAL_MAX_GPIO_INTERRUPTS;
	}
	else {
		return 0;
	}
}

static inline struct metal_interrupt * __metal_driver_sifive_gpio0_interrupt_parent(struct metal_gpio *gpio)
{
	if ((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) {
		return (struct metal_interrupt *)&__metal_dt_interrupt_controller_c000000.controller;
	}
	else {
		return 0;
	}
}

static inline int __metal_driver_sifive_gpio0_interrupt_lines(struct metal_gpio *gpio, int idx)
{
	if (((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 0)) {
		return 7;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 1))) {
		return 8;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 2))) {
		return 9;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 3))) {
		return 10;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 4))) {
		return 11;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 5))) {
		return 12;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 6))) {
		return 13;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 7))) {
		return 14;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 8))) {
		return 15;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 9))) {
		return 16;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 10))) {
		return 17;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 11))) {
		return 18;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 12))) {
		return 19;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 13))) {
		return 20;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 14))) {
		return 21;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 15))) {
		return 22;
	}
	else {
		return 0;
	}
}



/* --------------------- sifive_gpio_button ------------ */


/* --------------------- sifive_gpio_led ------------ */
static inline struct metal_gpio * __metal_driver_sifive_gpio_led_gpio(struct metal_led *led)
{
	if ((uintptr_t)led == (uintptr_t)&__metal_dt_led_0red) {
		return (struct metal_gpio *)&__metal_dt_gpio_10012000;
	}
	else if ((uintptr_t)led == (uintptr_t)&__metal_dt_led_0green) {
		return (struct metal_gpio *)&__metal_dt_gpio_10012000;
	}
	else if ((uintptr_t)led == (uintptr_t)&__metal_dt_led_0blue) {
		return (struct metal_gpio *)&__metal_dt_gpio_10012000;
	}
	else {
		return NULL;
	}
}

static inline int __metal_driver_sifive_gpio_led_pin(struct metal_led *led)
{
	if ((uintptr_t)led == (uintptr_t)&__metal_dt_led_0red) {
		return 22;
	}
	else if ((uintptr_t)led == (uintptr_t)&__metal_dt_led_0green) {
		return 19;
	}
	else if ((uintptr_t)led == (uintptr_t)&__metal_dt_led_0blue) {
		return 21;
	}
	else {
		return 0;
	}
}

static inline char * __metal_driver_sifive_gpio_led_label(struct metal_led *led)
{
	if ((uintptr_t)led == (uintptr_t)&__metal_dt_led_0red) {
		return "LD0red";
	}
	else if ((uintptr_t)led == (uintptr_t)&__metal_dt_led_0green) {
		return "LD0green";
	}
	else if ((uintptr_t)led == (uintptr_t)&__metal_dt_led_0blue) {
		return "LD0blue";
	}
	else {
		return "";
	}
}



/* --------------------- sifive_gpio_switch ------------ */


/* --------------------- sifive_spi0 ------------ */
static inline unsigned long __metal_driver_sifive_spi0_control_base(struct metal_spi *spi)
{
	if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10014000) {
		return METAL_SIFIVE_SPI0_10014000_BASE_ADDRESS;
	}
	else {
		return 0;
	}
}

static inline unsigned long __metal_driver_sifive_spi0_control_size(struct metal_spi *spi)
{
	if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10014000) {
		return METAL_SIFIVE_SPI0_10014000_SIZE;
	}
	else {
		return 0;
	}
}

static inline struct metal_clock * __metal_driver_sifive_spi0_clock(struct metal_spi *spi)
{
		return (struct metal_clock *)&__metal_dt_clock_4.clock;
}

static inline struct __metal_driver_sifive_gpio0 * __metal_driver_sifive_spi0_pinmux(struct metal_spi *spi)
{
		return (struct __metal_driver_sifive_gpio0 *)&__metal_dt_gpio_10012000;
}

static inline unsigned long __metal_driver_sifive_spi0_pinmux_output_selector(struct metal_spi *spi)
{
		return 60;
}

static inline unsigned long __metal_driver_sifive_spi0_pinmux_source_selector(struct metal_spi *spi)
{
		return 60;
}



/* --------------------- sifive_test0 ------------ */


/* --------------------- sifive_uart0 ------------ */
static inline unsigned long __metal_driver_sifive_uart0_control_base(struct metal_uart *uart)
{
	if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10013000) {
		return METAL_SIFIVE_UART0_10013000_BASE_ADDRESS;
	}
	else {
		return 0;
	}
}

static inline unsigned long __metal_driver_sifive_uart0_control_size(struct metal_uart *uart)
{
	if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10013000) {
		return METAL_SIFIVE_UART0_10013000_SIZE;
	}
	else {
		return 0;
	}
}

static inline int __metal_driver_sifive_uart0_num_interrupts(struct metal_uart *uart)
{
	if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10013000) {
		return METAL_MAX_UART_INTERRUPTS;
	}
	else {
		return 0;
	}
}

static inline struct metal_interrupt * __metal_driver_sifive_uart0_interrupt_parent(struct metal_uart *uart)
{
	if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10013000) {
		return (struct metal_interrupt *)&__metal_dt_interrupt_controller_c000000.controller;
	}
	else {
		return NULL;
	}
}

static inline int __metal_driver_sifive_uart0_interrupt_line(struct metal_uart *uart)
{
		return 5;
}

static inline struct metal_clock * __metal_driver_sifive_uart0_clock(struct metal_uart *uart)
{
		return (struct metal_clock *)&__metal_dt_clock_4.clock;
}

static inline struct __metal_driver_sifive_gpio0 * __metal_driver_sifive_uart0_pinmux(struct metal_uart *uart)
{
		return (struct __metal_driver_sifive_gpio0 *)&__metal_dt_gpio_10012000;
}

static inline unsigned long __metal_driver_sifive_uart0_pinmux_output_selector(struct metal_uart *uart)
{
		return 196608;
}

static inline unsigned long __metal_driver_sifive_uart0_pinmux_source_selector(struct metal_uart *uart)
{
		return 196608;
}



/* --------------------- sifive_fe310_g000_hfrosc ------------ */
static inline struct metal_clock * __metal_driver_sifive_fe310_g000_hfrosc_ref(const struct metal_clock *clock)
{
		return (struct metal_clock *)&__metal_dt_clock_2.clock;
}

static inline struct __metal_driver_sifive_fe310_g000_prci * __metal_driver_sifive_fe310_g000_hfrosc_config_base(const struct metal_clock *clock)
{
		return (struct __metal_driver_sifive_fe310_g000_prci *)&__metal_dt_prci_10008000;
}

static inline const struct __metal_driver_vtable_sifive_fe310_g000_prci * __metal_driver_sifive_fe310_g000_hfrosc_config_vtable(struct metal_clock *clock)
{
		return &__metal_driver_vtable_sifive_fe310_g000_prci;
}

static inline long __metal_driver_sifive_fe310_g000_hfrosc_config_offset(const struct metal_clock *clock)
{
		return METAL_SIFIVE_FE310_G000_PRCI_HFROSCCFG;
}



/* --------------------- sifive_fe310_g000_hfxosc ------------ */
static inline struct metal_clock * __metal_driver_sifive_fe310_g000_hfxosc_ref(const struct metal_clock *clock)
{
		return (struct metal_clock *)&__metal_dt_clock_0.clock;
}

static inline struct __metal_driver_sifive_fe310_g000_prci * __metal_driver_sifive_fe310_g000_hfxosc_config_base(const struct metal_clock *clock)
{
		return (struct __metal_driver_sifive_fe310_g000_prci *)&__metal_dt_prci_10008000;
}

static inline long __metal_driver_sifive_fe310_g000_hfxosc_config_offset(const struct metal_clock *clock)
{
		return METAL_SIFIVE_FE310_G000_PRCI_HFXOSCCFG;
}



/* --------------------- sifive_fe310_g000_pll ------------ */
static inline struct metal_clock * __metal_driver_sifive_fe310_g000_pll_pllsel0(const struct metal_clock *clock)
{
		return (struct metal_clock *)&__metal_dt_clock_3.clock;
}

static inline struct metal_clock * __metal_driver_sifive_fe310_g000_pll_pllref(const struct metal_clock *clock)
{
		return (struct metal_clock *)&__metal_dt_clock_1.clock;
}

static inline struct __metal_driver_sifive_fe310_g000_prci * __metal_driver_sifive_fe310_g000_pll_divider_base(const struct metal_clock *clock)
{
		return (struct __metal_driver_sifive_fe310_g000_prci *)&__metal_dt_prci_10008000;
}

static inline long __metal_driver_sifive_fe310_g000_pll_divider_offset(const struct metal_clock *clock)
{
		return METAL_SIFIVE_FE310_G000_PRCI_PLLOUTDIV;
}

static inline struct __metal_driver_sifive_fe310_g000_prci * __metal_driver_sifive_fe310_g000_pll_config_base( )
{
		return (struct __metal_driver_sifive_fe310_g000_prci *)&__metal_dt_prci_10008000;
}

static inline long __metal_driver_sifive_fe310_g000_pll_config_offset( )
{
		return METAL_SIFIVE_FE310_G000_PRCI_PLLCFG;
}

static inline long __metal_driver_sifive_fe310_g000_pll_init_rate( )
{
		return 16000000;
}



/* --------------------- sifive_fe310_g000_prci ------------ */
static inline long __metal_driver_sifive_fe310_g000_prci_base( )
{
		return METAL_SIFIVE_FE310_G000_PRCI_10008000_BASE_ADDRESS;
}

static inline long __metal_driver_sifive_fe310_g000_prci_size( )
{
		return METAL_SIFIVE_FE310_G000_PRCI_10008000_SIZE;
}

static inline const struct __metal_driver_vtable_sifive_fe310_g000_prci * __metal_driver_sifive_fe310_g000_prci_vtable( )
{
		return &__metal_driver_vtable_sifive_fe310_g000_prci;
}



/* --------------------- sifive_fu540_c000_l2 ------------ */


#define __METAL_DT_MAX_MEMORIES 2

asm (".weak __metal_memory_table");
struct metal_memory *__metal_memory_table[] = {
					&__metal_dt_mem_dtim_80000000,
					&__metal_dt_mem_spi_10014000};

/* From serial@10013000 */
#define __METAL_DT_STDOUT_UART_HANDLE (&__metal_dt_serial_10013000.uart)

#define __METAL_DT_SERIAL_10013000_HANDLE (&__metal_dt_serial_10013000.uart)

#define __METAL_DT_STDOUT_UART_BAUD 115200

/* From clint@2000000 */
#define __METAL_DT_RISCV_CLINT0_HANDLE (&__metal_dt_clint_2000000.controller)

#define __METAL_DT_CLINT_2000000_HANDLE (&__metal_dt_clint_2000000.controller)

#define __METAL_DT_MAX_HARTS 1

asm (".weak __metal_cpu_table");
struct __metal_driver_cpu *__metal_cpu_table[] = {
					&__metal_dt_cpu_0};

/* From interrupt_controller@c000000 */
#define __METAL_DT_RISCV_PLIC0_HANDLE (&__metal_dt_interrupt_controller_c000000.controller)

#define __METAL_DT_INTERRUPT_CONTROLLER_C000000_HANDLE (&__metal_dt_interrupt_controller_c000000.controller)

#define __METAL_DT_PMP_HANDLE (&__metal_dt_pmp)

/* From local_external_interrupts_0 */
#define __METAL_DT_SIFIVE_LOCAL_EXINTR0_HANDLE (&__metal_dt_local_external_interrupts_0.irc)

#define __METAL_DT_LOCAL_EXTERNAL_INTERRUPTS_0_HANDLE (&__metal_dt_local_external_interrupts_0.irc)

#define __MEE_DT_MAX_GPIOS 1

asm (".weak __metal_gpio_table");
struct __metal_driver_sifive_gpio0 *__metal_gpio_table[] = {
					&__metal_dt_gpio_10012000};

#define __METAL_DT_MAX_BUTTONS 0

asm (".weak __metal_button_table");
struct __metal_driver_sifive_gpio_button *__metal_button_table[] = {
					NULL };
#define __METAL_DT_MAX_LEDS 3

asm (".weak __metal_led_table");
struct __metal_driver_sifive_gpio_led *__metal_led_table[] = {
					&__metal_dt_led_0red,
					&__metal_dt_led_0green,
					&__metal_dt_led_0blue};

#define __METAL_DT_MAX_SWITCHES 0

asm (".weak __metal_switch_table");
struct __metal_driver_sifive_gpio_switch *__metal_switch_table[] = {
					NULL };
#define __METAL_DT_MAX_SPIS 1

asm (".weak __metal_spi_table");
struct __metal_driver_sifive_spi0 *__metal_spi_table[] = {
					&__metal_dt_spi_10014000};

/* From clock@4 */
#define __METAL_DT_SIFIVE_FE310_G000_PLL_HANDLE (&__metal_dt_clock_4)

#define __METAL_DT_CLOCK_4_HANDLE (&__metal_dt_clock_4)

#endif /* MACROS_ELSE_SIFIVE_HIFIVE1_REVB____METAL_H*/

#endif /* ! __METAL_MACHINE_MACROS */

#endif /* ! ASSEMBLY */
