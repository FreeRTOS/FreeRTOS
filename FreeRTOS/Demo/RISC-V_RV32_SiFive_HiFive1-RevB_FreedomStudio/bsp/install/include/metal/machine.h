/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */
/* ----------------------------------- */
/* ----------------------------------- */

#ifndef ASSEMBLY

#include <metal/machine/platform.h>

#ifdef __METAL_MACHINE_MACROS

#ifndef MACROS_IF_METAL_H
#define MACROS_IF_METAL_H

#define __METAL_CLINT_NUM_PARENTS 2

#ifndef __METAL_CLINT_NUM_PARENTS
#define __METAL_CLINT_NUM_PARENTS 0
#endif
#define __METAL_PLIC_SUBINTERRUPTS 53

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

#endif /* MACROS_IF_METAL_H*/

#else /* ! __METAL_MACHINE_MACROS */

#ifndef MACROS_ELSE_METAL_H
#define MACROS_ELSE_METAL_H

#define __METAL_CLINT_2000000_INTERRUPTS 2

#define METAL_MAX_CLINT_INTERRUPTS 2

#define __METAL_CLINT_NUM_PARENTS 2

#define __METAL_INTERRUPT_CONTROLLER_C000000_INTERRUPTS 1

#define __METAL_PLIC_SUBINTERRUPTS 53

#define METAL_MAX_PLIC_INTERRUPTS 1

#define __METAL_PLIC_NUM_PARENTS 1

#define __METAL_CLIC_SUBINTERRUPTS 0
#define METAL_MAX_CLIC_INTERRUPTS 0

#define METAL_MAX_LOCAL_EXT_INTERRUPTS 0

#define METAL_MAX_GLOBAL_EXT_INTERRUPTS 0

#define __METAL_GPIO_10012000_INTERRUPTS 32

#define METAL_MAX_GPIO_INTERRUPTS 32

#define __METAL_I2C_10016000_INTERRUPTS 1

#define METAL_MAX_I2C0_INTERRUPTS 1

#define __METAL_PWM_10015000_INTERRUPTS 4

#define __METAL_PWM_10025000_INTERRUPTS 4

#define __METAL_PWM_10035000_INTERRUPTS 4

#define METAL_MAX_PWM0_INTERRUPTS 4

#define METAL_MAX_PWM0_NCMP 4

#define __METAL_SERIAL_10013000_INTERRUPTS 1

#define __METAL_SERIAL_10023000_INTERRUPTS 1

#define METAL_MAX_UART_INTERRUPTS 1

#define METAL_MAX_SIMUART_INTERRUPTS 0


#include <metal/drivers/fixed-clock.h>
#include <metal/memory.h>
#include <metal/drivers/riscv_clint0.h>
#include <metal/drivers/riscv_cpu.h>
#include <metal/drivers/riscv_plic0.h>
#include <metal/pmp.h>
#include <metal/drivers/sifive_gpio0.h>
#include <metal/drivers/sifive_gpio-leds.h>
#include <metal/drivers/sifive_i2c0.h>
#include <metal/drivers/sifive_pwm0.h>
#include <metal/drivers/sifive_rtc0.h>
#include <metal/drivers/sifive_spi0.h>
#include <metal/drivers/sifive_uart0.h>
#include <metal/drivers/sifive_wdog0.h>
#include <metal/drivers/sifive_fe310-g000_hfrosc.h>
#include <metal/drivers/sifive_fe310-g000_hfxosc.h>
#include <metal/drivers/sifive_fe310-g000_lfrosc.h>
#include <metal/drivers/sifive_fe310-g000_pll.h>
#include <metal/drivers/sifive_fe310-g000_prci.h>

/* From clock@0 */
extern struct __metal_driver_fixed_clock __metal_dt_clock_0;

/* From clock@2 */
extern struct __metal_driver_fixed_clock __metal_dt_clock_2;

/* From clock@5 */
extern struct __metal_driver_fixed_clock __metal_dt_clock_5;

/* From clock@6 */
extern struct __metal_driver_fixed_clock __metal_dt_clock_6;

extern struct metal_memory __metal_dt_mem_dtim_80000000;

extern struct metal_memory __metal_dt_mem_itim_8000000;

extern struct metal_memory __metal_dt_mem_spi_10014000;

extern struct metal_memory __metal_dt_mem_spi_10024000;

extern struct metal_memory __metal_dt_mem_spi_10034000;

/* From clint@2000000 */
extern struct __metal_driver_riscv_clint0 __metal_dt_clint_2000000;

/* From cpu@0 */
extern struct __metal_driver_cpu __metal_dt_cpu_0;

extern struct __metal_driver_riscv_cpu_intc __metal_dt_cpu_0_interrupt_controller;

/* From interrupt_controller@c000000 */
extern struct __metal_driver_riscv_plic0 __metal_dt_interrupt_controller_c000000;

extern struct metal_pmp __metal_dt_pmp;

/* From gpio@10012000 */
extern struct __metal_driver_sifive_gpio0 __metal_dt_gpio_10012000;

/* From led@0 */
extern struct __metal_driver_sifive_gpio_led __metal_dt_led_0;

/* From led@1 */
extern struct __metal_driver_sifive_gpio_led __metal_dt_led_1;

/* From led@2 */
extern struct __metal_driver_sifive_gpio_led __metal_dt_led_2;

/* From i2c@10016000 */
extern struct __metal_driver_sifive_i2c0 __metal_dt_i2c_10016000;

/* From pwm@10015000 */
extern struct __metal_driver_sifive_pwm0 __metal_dt_pwm_10015000;

/* From pwm@10025000 */
extern struct __metal_driver_sifive_pwm0 __metal_dt_pwm_10025000;

/* From pwm@10035000 */
extern struct __metal_driver_sifive_pwm0 __metal_dt_pwm_10035000;

/* From aon@10000000 */
extern struct __metal_driver_sifive_rtc0 __metal_dt_rtc_10000000;

/* From spi@10014000 */
extern struct __metal_driver_sifive_spi0 __metal_dt_spi_10014000;

/* From spi@10024000 */
extern struct __metal_driver_sifive_spi0 __metal_dt_spi_10024000;

/* From spi@10034000 */
extern struct __metal_driver_sifive_spi0 __metal_dt_spi_10034000;

/* From serial@10013000 */
extern struct __metal_driver_sifive_uart0 __metal_dt_serial_10013000;

/* From serial@10023000 */
extern struct __metal_driver_sifive_uart0 __metal_dt_serial_10023000;

/* From aon@10000000 */
extern struct __metal_driver_sifive_wdog0 __metal_dt_aon_10000000;

/* From clock@3 */
extern struct __metal_driver_sifive_fe310_g000_hfrosc __metal_dt_clock_3;

/* From clock@1 */
extern struct __metal_driver_sifive_fe310_g000_hfxosc __metal_dt_clock_1;

/* From clock@7 */
extern struct __metal_driver_sifive_fe310_g000_lfrosc __metal_dt_clock_7;

/* From clock@4 */
extern struct __metal_driver_sifive_fe310_g000_pll __metal_dt_clock_4;

/* From prci@10008000 */
extern struct __metal_driver_sifive_fe310_g000_prci __metal_dt_prci_10008000;



/* --------------------- fixed_clock ------------ */
static __inline__ unsigned long __metal_driver_fixed_clock_rate(const struct metal_clock *clock)
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
	else if ((uintptr_t)clock == (uintptr_t)&__metal_dt_clock_6) {
		return METAL_FIXED_CLOCK_6_CLOCK_FREQUENCY;
	}
	else {
		return 0;
	}
}



/* --------------------- fixed_factor_clock ------------ */


/* --------------------- sifive_clint0 ------------ */
static __inline__ unsigned long __metal_driver_sifive_clint0_control_base(struct metal_interrupt *controller)
{
	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_clint_2000000) {
		return METAL_RISCV_CLINT0_2000000_BASE_ADDRESS;
	}
	else {
		return 0;
	}
}

static __inline__ unsigned long __metal_driver_sifive_clint0_control_size(struct metal_interrupt *controller)
{
	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_clint_2000000) {
		return METAL_RISCV_CLINT0_2000000_SIZE;
	}
	else {
		return 0;
	}
}

static __inline__ int __metal_driver_sifive_clint0_num_interrupts(struct metal_interrupt *controller)
{
	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_clint_2000000) {
		return METAL_MAX_CLINT_INTERRUPTS;
	}
	else {
		return 0;
	}
}

static __inline__ struct metal_interrupt * __metal_driver_sifive_clint0_interrupt_parents(struct metal_interrupt *controller, int idx)
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

static __inline__ int __metal_driver_sifive_clint0_interrupt_lines(struct metal_interrupt *controller, int idx)
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
static __inline__ int __metal_driver_cpu_hartid(struct metal_cpu *cpu)
{
	if ((uintptr_t)cpu == (uintptr_t)&__metal_dt_cpu_0) {
		return 0;
	}
	else {
		return -1;
	}
}

static __inline__ int __metal_driver_cpu_timebase(struct metal_cpu *cpu)
{
	if ((uintptr_t)cpu == (uintptr_t)&__metal_dt_cpu_0) {
		return 16000000;
	}
	else {
		return 0;
	}
}

static __inline__ struct metal_interrupt * __metal_driver_cpu_interrupt_controller(struct metal_cpu *cpu)
{
	if ((uintptr_t)cpu == (uintptr_t)&__metal_dt_cpu_0) {
		return &__metal_dt_cpu_0_interrupt_controller.controller;
	}
	else {
		return NULL;
	}
}

static __inline__ int __metal_driver_cpu_num_pmp_regions(struct metal_cpu *cpu)
{
	if ((uintptr_t)cpu == (uintptr_t)&__metal_dt_cpu_0) {
		return 8;
	}
	else {
		return 0;
	}
}

static __inline__ struct metal_buserror * __metal_driver_cpu_buserror(struct metal_cpu *cpu)
{
	if ((uintptr_t)cpu == (uintptr_t)&__metal_dt_cpu_0) {
		return NULL;
	}
	else {
		return NULL;
	}
}



/* --------------------- sifive_plic0 ------------ */
static __inline__ unsigned long __metal_driver_sifive_plic0_control_base(struct metal_interrupt *controller)
{
	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_interrupt_controller_c000000) {
		return METAL_RISCV_PLIC0_C000000_BASE_ADDRESS;
	}
	else {
		return 0;
	}
}

static __inline__ unsigned long __metal_driver_sifive_plic0_control_size(struct metal_interrupt *controller)
{
	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_interrupt_controller_c000000) {
		return METAL_RISCV_PLIC0_C000000_SIZE;
	}
	else {
		return 0;
	}
}

static __inline__ int __metal_driver_sifive_plic0_num_interrupts(struct metal_interrupt *controller)
{
	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_interrupt_controller_c000000) {
		return METAL_RISCV_PLIC0_C000000_RISCV_NDEV;
	}
	else {
		return 0;
	}
}

static __inline__ int __metal_driver_sifive_plic0_max_priority(struct metal_interrupt *controller)
{
	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_interrupt_controller_c000000) {
		return METAL_RISCV_PLIC0_C000000_RISCV_MAX_PRIORITY;
	}
	else {
		return 0;
	}
}

static __inline__ struct metal_interrupt * __metal_driver_sifive_plic0_interrupt_parents(struct metal_interrupt *controller, int idx)
{
	if (idx == 0) {
		return (struct metal_interrupt *)&__metal_dt_cpu_0_interrupt_controller.controller;
	}
	else {
		return NULL;
	}
}

static __inline__ int __metal_driver_sifive_plic0_interrupt_lines(struct metal_interrupt *controller, int idx)
{
	if (idx == 0) {
		return 11;
	}
	else {
		return 0;
	}
}

static __inline__ int __metal_driver_sifive_plic0_context_ids(int hartid)
{
	if (hartid == 0) {
		return 0;
	}
	else {
		return -1;
	}
}



/* --------------------- sifive_buserror0 ------------ */


/* --------------------- sifive_clic0 ------------ */


/* --------------------- sifive_local_external_interrupts0 ------------ */


/* --------------------- sifive_global_external_interrupts0 ------------ */


/* --------------------- sifive_gpio0 ------------ */
static __inline__ unsigned long __metal_driver_sifive_gpio0_base(struct metal_gpio *gpio)
{
	if ((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) {
		return METAL_SIFIVE_GPIO0_10012000_BASE_ADDRESS;
	}
	else {
		return 0;
	}
}

static __inline__ unsigned long __metal_driver_sifive_gpio0_size(struct metal_gpio *gpio)
{
	if ((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) {
		return METAL_SIFIVE_GPIO0_10012000_SIZE;
	}
	else {
		return 0;
	}
}

static __inline__ int __metal_driver_sifive_gpio0_num_interrupts(struct metal_gpio *gpio)
{
	if ((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) {
		return METAL_MAX_GPIO_INTERRUPTS;
	}
	else {
		return 0;
	}
}

static __inline__ struct metal_interrupt * __metal_driver_sifive_gpio0_interrupt_parent(struct metal_gpio *gpio)
{
	if ((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) {
		return (struct metal_interrupt *)&__metal_dt_interrupt_controller_c000000.controller;
	}
	else {
		return 0;
	}
}

static __inline__ int __metal_driver_sifive_gpio0_interrupt_lines(struct metal_gpio *gpio, int idx)
{
	if (((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 0)) {
		return 8;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 1))) {
		return 9;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 2))) {
		return 10;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 3))) {
		return 11;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 4))) {
		return 12;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 5))) {
		return 13;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 6))) {
		return 14;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 7))) {
		return 15;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 8))) {
		return 16;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 9))) {
		return 17;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 10))) {
		return 18;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 11))) {
		return 19;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 12))) {
		return 20;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 13))) {
		return 21;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 14))) {
		return 22;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 15))) {
		return 23;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 16))) {
		return 24;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 17))) {
		return 25;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 18))) {
		return 26;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 19))) {
		return 27;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 20))) {
		return 28;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 21))) {
		return 29;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 22))) {
		return 30;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 23))) {
		return 31;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 24))) {
		return 32;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 25))) {
		return 33;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 26))) {
		return 34;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 27))) {
		return 35;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 28))) {
		return 36;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 29))) {
		return 27;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 30))) {
		return 28;
	}
	else if ((((uintptr_t)gpio == (uintptr_t)&__metal_dt_gpio_10012000) && (idx == 31))) {
		return 29;
	}
	else {
		return 0;
	}
}



/* --------------------- sifive_gpio_button ------------ */


/* --------------------- sifive_gpio_led ------------ */
static __inline__ struct metal_gpio * __metal_driver_sifive_gpio_led_gpio(struct metal_led *led)
{
	if ((uintptr_t)led == (uintptr_t)&__metal_dt_led_0) {
		return (struct metal_gpio *)&__metal_dt_gpio_10012000;
	}
	else if ((uintptr_t)led == (uintptr_t)&__metal_dt_led_1) {
		return (struct metal_gpio *)&__metal_dt_gpio_10012000;
	}
	else if ((uintptr_t)led == (uintptr_t)&__metal_dt_led_2) {
		return (struct metal_gpio *)&__metal_dt_gpio_10012000;
	}
	else {
		return NULL;
	}
}

static __inline__ int __metal_driver_sifive_gpio_led_pin(struct metal_led *led)
{
	if ((uintptr_t)led == (uintptr_t)&__metal_dt_led_0) {
		return 22;
	}
	else if ((uintptr_t)led == (uintptr_t)&__metal_dt_led_1) {
		return 19;
	}
	else if ((uintptr_t)led == (uintptr_t)&__metal_dt_led_2) {
		return 21;
	}
	else {
		return 0;
	}
}

static __inline__ char * __metal_driver_sifive_gpio_led_label(struct metal_led *led)
{
	if ((uintptr_t)led == (uintptr_t)&__metal_dt_led_0) {
		return "LD0red";
	}
	else if ((uintptr_t)led == (uintptr_t)&__metal_dt_led_1) {
		return "LD0green";
	}
	else if ((uintptr_t)led == (uintptr_t)&__metal_dt_led_2) {
		return "LD0blue";
	}
	else {
		return "";
	}
}



/* --------------------- sifive_gpio_switch ------------ */


/* --------------------- sifive_i2c0 ------------ */
static __inline__ unsigned long __metal_driver_sifive_i2c0_control_base(struct metal_i2c *i2c)
{
	if ((uintptr_t)i2c == (uintptr_t)&__metal_dt_i2c_10016000) {
		return METAL_SIFIVE_I2C0_10016000_BASE_ADDRESS;
	}
	else {
		return 0;
	}
}

static __inline__ unsigned long __metal_driver_sifive_i2c0_control_size(struct metal_i2c *i2c)
{
	if ((uintptr_t)i2c == (uintptr_t)&__metal_dt_i2c_10016000) {
		return METAL_SIFIVE_I2C0_10016000_SIZE;
	}
	else {
		return 0;
	}
}

static __inline__ struct metal_clock * __metal_driver_sifive_i2c0_clock(struct metal_i2c *i2c)
{
	if ((uintptr_t)i2c == (uintptr_t)&__metal_dt_i2c_10016000) {
		return (struct metal_clock *)&__metal_dt_clock_4.clock;
	}
	else {
		return NULL;
	}
}

static __inline__ struct __metal_driver_sifive_gpio0 * __metal_driver_sifive_i2c0_pinmux(struct metal_i2c *i2c)
{
	if ((uintptr_t)i2c == (uintptr_t)&__metal_dt_i2c_10016000) {
		return (struct __metal_driver_sifive_gpio0 *)&__metal_dt_gpio_10012000;
	}
	else {
		return NULL;
	}
}

static __inline__ unsigned long __metal_driver_sifive_i2c0_pinmux_output_selector(struct metal_i2c *i2c)
{
	if ((uintptr_t)i2c == (uintptr_t)&__metal_dt_i2c_10016000) {
		return 0;
	}
	else {
		return 0;
	}
}

static __inline__ unsigned long __metal_driver_sifive_i2c0_pinmux_source_selector(struct metal_i2c *i2c)
{
	if ((uintptr_t)i2c == (uintptr_t)&__metal_dt_i2c_10016000) {
		return 12288;
	}
	else {
		return 0;
	}
}

static __inline__ int __metal_driver_sifive_i2c0_num_interrupts(struct metal_i2c *i2c)
{
		return METAL_MAX_I2C0_INTERRUPTS;
}

static __inline__ struct metal_interrupt * __metal_driver_sifive_i2c0_interrupt_parent(struct metal_i2c *i2c)
{
		return (struct metal_interrupt *)&__metal_dt_interrupt_controller_c000000.controller;
}

static __inline__ int __metal_driver_sifive_i2c0_interrupt_line(struct metal_i2c *i2c)
{
	if ((uintptr_t)i2c == (uintptr_t)&__metal_dt_i2c_10016000) {
		return 52;
	}
	else {
		return 0;
	}
}



/* --------------------- sifive_pwm0 ------------ */
static __inline__ unsigned long __metal_driver_sifive_pwm0_control_base(struct metal_pwm *pwm)
{
	if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10015000) {
		return METAL_SIFIVE_PWM0_10015000_BASE_ADDRESS;
	}
	else if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10025000) {
		return METAL_SIFIVE_PWM0_10025000_BASE_ADDRESS;
	}
	else if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10035000) {
		return METAL_SIFIVE_PWM0_10035000_BASE_ADDRESS;
	}
	else {
		return 0;
	}
}

static __inline__ unsigned long __metal_driver_sifive_pwm0_control_size(struct metal_pwm *pwm)
{
	if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10015000) {
		return METAL_SIFIVE_PWM0_10015000_SIZE;
	}
	else if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10025000) {
		return METAL_SIFIVE_PWM0_10025000_SIZE;
	}
	else if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10035000) {
		return METAL_SIFIVE_PWM0_10035000_SIZE;
	}
	else {
		return 0;
	}
}

static __inline__ struct metal_clock * __metal_driver_sifive_pwm0_clock(struct metal_pwm *pwm)
{
	if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10015000) {
		return (struct metal_clock *)&__metal_dt_clock_4.clock;
	}
	else if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10025000) {
		return (struct metal_clock *)&__metal_dt_clock_4.clock;
	}
	else if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10035000) {
		return (struct metal_clock *)&__metal_dt_clock_4.clock;
	}
	else {
		return NULL;
	}
}

static __inline__ struct __metal_driver_sifive_gpio0 * __metal_driver_sifive_pwm0_pinmux(struct metal_pwm *pwm)
{
	if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10015000) {
		return (struct __metal_driver_sifive_gpio0 *)&__metal_dt_gpio_10012000;
	}
	else if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10025000) {
		return (struct __metal_driver_sifive_gpio0 *)&__metal_dt_gpio_10012000;
	}
	else if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10035000) {
		return (struct __metal_driver_sifive_gpio0 *)&__metal_dt_gpio_10012000;
	}
	else {
		return NULL;
	}
}

static __inline__ unsigned long __metal_driver_sifive_pwm0_pinmux_output_selector(struct metal_pwm *pwm)
{
	if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10015000) {
		return 15;
	}
	else if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10025000) {
		return 7864320;
	}
	else if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10035000) {
		return 15360;
	}
	else {
		return 0;
	}
}

static __inline__ unsigned long __metal_driver_sifive_pwm0_pinmux_source_selector(struct metal_pwm *pwm)
{
	if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10015000) {
		return 15;
	}
	else if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10025000) {
		return 7864320;
	}
	else if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10035000) {
		return 15360;
	}
	else {
		return 0;
	}
}

static __inline__ int __metal_driver_sifive_pwm0_num_interrupts(struct metal_pwm *pwm)
{
	if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10015000) {
		return __METAL_PWM_10015000_INTERRUPTS;
	}
	else if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10025000) {
		return __METAL_PWM_10025000_INTERRUPTS;
	}
	else if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10035000) {
		return __METAL_PWM_10035000_INTERRUPTS;
	}
	else {
		return 0;
	}
}

static __inline__ struct metal_interrupt * __metal_driver_sifive_pwm0_interrupt_parent(struct metal_pwm *pwm)
{
		return (struct metal_interrupt *)&__metal_dt_interrupt_controller_c000000.controller;
}

static __inline__ int __metal_driver_sifive_pwm0_interrupt_lines(struct metal_pwm *pwm, int idx)
{
	if (((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10015000) && (idx == 0)) {
		return 40;
	}
	else if ((((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10015000) && (idx == 1))) {
		return 41;
	}
	else if ((((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10015000) && (idx == 2))) {
		return 42;
	}
	else if ((((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10015000) && (idx == 3))) {
		return 43;
	}
	else if ((((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10025000) && (idx == 0))) {
		return 44;
	}
	else if ((((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10025000) && (idx == 1))) {
		return 45;
	}
	else if ((((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10025000) && (idx == 2))) {
		return 46;
	}
	else if ((((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10025000) && (idx == 3))) {
		return 47;
	}
	else if ((((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10035000) && (idx == 0))) {
		return 48;
	}
	else if ((((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10035000) && (idx == 1))) {
		return 49;
	}
	else if ((((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10035000) && (idx == 2))) {
		return 50;
	}
	else if ((((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10035000) && (idx == 3))) {
		return 51;
	}
	else {
		return 0;
	}
}

static __inline__ int __metal_driver_sifive_pwm0_compare_width(struct metal_pwm *pwm)
{
	if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10015000) {
		return 8;
	}
	else if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10025000) {
		return 16;
	}
	else if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10035000) {
		return 16;
	}
	else {
		return 0;
	}
}

static __inline__ int __metal_driver_sifive_pwm0_comparator_count(struct metal_pwm *pwm)
{
	if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10015000) {
		return 4;
	}
	else if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10025000) {
		return 4;
	}
	else if ((uintptr_t)pwm == (uintptr_t)&__metal_dt_pwm_10035000) {
		return 4;
	}
	else {
		return 0;
	}
}



/* --------------------- sifive_rtc0 ------------ */
static __inline__ unsigned long __metal_driver_sifive_rtc0_control_base(const struct metal_rtc *const rtc)
{
	if ((uintptr_t)rtc == (uintptr_t)&__metal_dt_rtc_10000000) {
		return METAL_SIFIVE_AON0_10000000_BASE_ADDRESS;
	}
	else {
		return 0;
	}
}

static __inline__ unsigned long __metal_driver_sifive_rtc0_control_size(const struct metal_rtc *const rtc)
{
	if ((uintptr_t)rtc == (uintptr_t)&__metal_dt_rtc_10000000) {
		return METAL_SIFIVE_AON0_10000000_SIZE;
	}
	else {
		return 0;
	}
}

static __inline__ struct metal_interrupt * __metal_driver_sifive_rtc0_interrupt_parent(const struct metal_rtc *const rtc)
{
	if ((uintptr_t)rtc == (uintptr_t)&__metal_dt_rtc_10000000) {
		return (struct metal_interrupt *)&__metal_dt_interrupt_controller_c000000.controller;
	}
	else {
		return 0;
	}
}

static __inline__ int __metal_driver_sifive_rtc0_interrupt_line(const struct metal_rtc *const rtc)
{
	if ((uintptr_t)rtc == (uintptr_t)&__metal_dt_rtc_10000000) {
		return 2;
	}
	else {
		return 0;
	}
}

static __inline__ struct metal_clock * __metal_driver_sifive_rtc0_clock(const struct metal_rtc *const rtc)
{
	if ((uintptr_t)rtc == (uintptr_t)&__metal_dt_rtc_10000000) {
		return (struct metal_clock *)&__metal_dt_clock_7.clock;
	}
	else {
		return 0;
	}
}


static __inline__ unsigned long __metal_driver_sifive_spi0_control_base(struct metal_spi *spi)
{
	if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10014000) {
		return METAL_SIFIVE_SPI0_10014000_BASE_ADDRESS;
	}
	else if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10024000) {
		return METAL_SIFIVE_SPI0_10024000_BASE_ADDRESS;
	}
	else if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10034000) {
		return METAL_SIFIVE_SPI0_10034000_BASE_ADDRESS;
	}
	else {
		return 0;
	}
}

static __inline__ unsigned long __metal_driver_sifive_spi0_control_size(struct metal_spi *spi)
{
	if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10014000) {
		return METAL_SIFIVE_SPI0_10014000_SIZE;
	}
	else if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10024000) {
		return METAL_SIFIVE_SPI0_10024000_SIZE;
	}
	else if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10034000) {
		return METAL_SIFIVE_SPI0_10034000_SIZE;
	}
	else {
		return 0;
	}
}

static __inline__ struct metal_clock * __metal_driver_sifive_spi0_clock(struct metal_spi *spi)
{
	if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10014000) {
		return (struct metal_clock *)&__metal_dt_clock_4.clock;
	}
	else if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10024000) {
		return (struct metal_clock *)&__metal_dt_clock_4.clock;
	}
	else if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10034000) {
		return (struct metal_clock *)&__metal_dt_clock_4.clock;
	}
	else {
		return 0;
	}
}

static __inline__ struct __metal_driver_sifive_gpio0 * __metal_driver_sifive_spi0_pinmux(struct metal_spi *spi)
{
	if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10014000) {
		return (struct __metal_driver_sifive_gpio0 *)&__metal_dt_gpio_10012000;
	}
	else if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10024000) {
		return (struct __metal_driver_sifive_gpio0 *)&__metal_dt_gpio_10012000;
	}
	else if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10034000) {
		return (struct __metal_driver_sifive_gpio0 *)&__metal_dt_gpio_10012000;
	}
	else {
		return 0;
	}
}

static __inline__ unsigned long __metal_driver_sifive_spi0_pinmux_output_selector(struct metal_spi *spi)
{
	if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10014000) {
		return 0;
	}
	else if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10024000) {
		return 0;
	}
	else if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10034000) {
		return 0;
	}
	else {
		return 0;
	}
}

static __inline__ unsigned long __metal_driver_sifive_spi0_pinmux_source_selector(struct metal_spi *spi)
{
	if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10014000) {
		return 0;
	}
	else if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10024000) {
		return 60;
	}
	else if ((uintptr_t)spi == (uintptr_t)&__metal_dt_spi_10034000) {
		return 4227858432;
	}
	else {
		return 0;
	}
}



/* --------------------- sifive_test0 ------------ */


/* --------------------- sifive_trace ------------ */

/* --------------------- sifive_uart0 ------------ */
static __inline__ unsigned long __metal_driver_sifive_uart0_control_base(struct metal_uart *uart)
{
	if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10013000) {
		return METAL_SIFIVE_UART0_10013000_BASE_ADDRESS;
	}
	else if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10023000) {
		return METAL_SIFIVE_UART0_10023000_BASE_ADDRESS;
	}
	else {
		return 0;
	}
}

static __inline__ unsigned long __metal_driver_sifive_uart0_control_size(struct metal_uart *uart)
{
	if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10013000) {
		return METAL_SIFIVE_UART0_10013000_SIZE;
	}
	else if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10023000) {
		return METAL_SIFIVE_UART0_10023000_SIZE;
	}
	else {
		return 0;
	}
}

static __inline__ int __metal_driver_sifive_uart0_num_interrupts(struct metal_uart *uart)
{
	if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10013000) {
		return METAL_MAX_UART_INTERRUPTS;
	}
	else if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10023000) {
		return METAL_MAX_UART_INTERRUPTS;
	}
	else {
		return 0;
	}
}

static __inline__ struct metal_interrupt * __metal_driver_sifive_uart0_interrupt_parent(struct metal_uart *uart)
{
	if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10013000) {
		return (struct metal_interrupt *)&__metal_dt_interrupt_controller_c000000.controller;
	}
	else if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10023000) {
		return (struct metal_interrupt *)&__metal_dt_interrupt_controller_c000000.controller;
	}
	else {
		return 0;
	}
}

static __inline__ int __metal_driver_sifive_uart0_interrupt_line(struct metal_uart *uart)
{
	if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10013000) {
		return 3;
	}
	else if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10023000) {
		return 4;
	}
	else {
		return 0;
	}
}

static __inline__ struct metal_clock * __metal_driver_sifive_uart0_clock(struct metal_uart *uart)
{
	if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10013000) {
		return (struct metal_clock *)&__metal_dt_clock_4.clock;
	}
	else if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10023000) {
		return (struct metal_clock *)&__metal_dt_clock_4.clock;
	}
	else {
		return 0;
	}
}

static __inline__ struct __metal_driver_sifive_gpio0 * __metal_driver_sifive_uart0_pinmux(struct metal_uart *uart)
{
	if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10013000) {
		return (struct __metal_driver_sifive_gpio0 *)&__metal_dt_gpio_10012000;
	}
	else if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10023000) {
		return (struct __metal_driver_sifive_gpio0 *)&__metal_dt_gpio_10012000;
	}
	else {
		return 0;
	}
}

static __inline__ unsigned long __metal_driver_sifive_uart0_pinmux_output_selector(struct metal_uart *uart)
{
	if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10013000) {
		return 0;
	}
	else if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10023000) {
		return 0;
	}
	else {
		return 0;
	}
}

static __inline__ unsigned long __metal_driver_sifive_uart0_pinmux_source_selector(struct metal_uart *uart)
{
	if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10013000) {
		return 196608;
	}
	else if ((uintptr_t)uart == (uintptr_t)&__metal_dt_serial_10023000) {
		return 8650752;
	}
	else {
		return 0;
	}
}



/* --------------------- sifive_simuart0 ------------ */


/* --------------------- sifive_wdog0 ------------ */
static __inline__ unsigned long __metal_driver_sifive_wdog0_control_base(const struct metal_watchdog *const watchdog)
{
	if ((uintptr_t)watchdog == (uintptr_t)&__metal_dt_aon_10000000) {
		return METAL_SIFIVE_AON0_10000000_BASE_ADDRESS;
	}
	else {
		return 0;
	}
}

static __inline__ unsigned long __metal_driver_sifive_wdog0_control_size(const struct metal_watchdog *const watchdog)
{
	if ((uintptr_t)watchdog == (uintptr_t)&__metal_dt_aon_10000000) {
		return METAL_SIFIVE_AON0_10000000_SIZE;
	}
	else {
		return 0;
	}
}

static __inline__ struct metal_interrupt * __metal_driver_sifive_wdog0_interrupt_parent(const struct metal_watchdog *const watchdog)
{
	if ((uintptr_t)watchdog == (uintptr_t)&__metal_dt_aon_10000000) {
		return (struct metal_interrupt *)&__metal_dt_interrupt_controller_c000000.controller;
	}
	else {
		return 0;
	}
}

static __inline__ int __metal_driver_sifive_wdog0_interrupt_line(const struct metal_watchdog *const watchdog)
{
	if ((uintptr_t)watchdog == (uintptr_t)&__metal_dt_aon_10000000) {
		return 1;
	}
	else {
		return 0;
	}
}

static __inline__ struct metal_clock * __metal_driver_sifive_wdog0_clock(const struct metal_watchdog *const watchdog)
{
	if ((uintptr_t)watchdog == (uintptr_t)&__metal_dt_aon_10000000) {
		return (struct metal_clock *)&__metal_dt_clock_7.clock;
	}
	else {
		return 0;
	}
}



/* --------------------- sifive_fe310_g000_hfrosc ------------ */
static __inline__ struct metal_clock * __metal_driver_sifive_fe310_g000_hfrosc_ref(const struct metal_clock *clock)
{
		return (struct metal_clock *)&__metal_dt_clock_2.clock;
}

static __inline__ struct __metal_driver_sifive_fe310_g000_prci * __metal_driver_sifive_fe310_g000_hfrosc_config_base(const struct metal_clock *clock)
{
		return (struct __metal_driver_sifive_fe310_g000_prci *)&__metal_dt_prci_10008000;
}

static __inline__ const struct __metal_driver_vtable_sifive_fe310_g000_prci * __metal_driver_sifive_fe310_g000_hfrosc_config_vtable(struct metal_clock *clock)
{
		return &__metal_driver_vtable_sifive_fe310_g000_prci;
}

static __inline__ long __metal_driver_sifive_fe310_g000_hfrosc_config_offset(const struct metal_clock *clock)
{
		return METAL_SIFIVE_FE310_G000_PRCI_HFROSCCFG;
}



/* --------------------- sifive_fe310_g000_hfxosc ------------ */
static __inline__ struct metal_clock * __metal_driver_sifive_fe310_g000_hfxosc_ref(const struct metal_clock *clock)
{
		return (struct metal_clock *)&__metal_dt_clock_0.clock;
}

static __inline__ struct __metal_driver_sifive_fe310_g000_prci * __metal_driver_sifive_fe310_g000_hfxosc_config_base(const struct metal_clock *clock)
{
		return (struct __metal_driver_sifive_fe310_g000_prci *)&__metal_dt_prci_10008000;
}

static __inline__ long __metal_driver_sifive_fe310_g000_hfxosc_config_offset(const struct metal_clock *clock)
{
		return METAL_SIFIVE_FE310_G000_PRCI_HFXOSCCFG;
}



/* --------------------- sifive_fe310_g000_lfrosc ------------ */
static __inline__ struct metal_clock * __metal_driver_sifive_fe310_g000_lfrosc_lfrosc(const struct metal_clock *clock)
{
	if ((uintptr_t)clock == (uintptr_t)&__metal_dt_clock_7) {
		return (struct metal_clock *)&__metal_dt_clock_5.clock;
	}
	else {
		return NULL;
	}
}

static __inline__ struct metal_clock * __metal_driver_sifive_fe310_g000_lfrosc_psdlfaltclk(const struct metal_clock *clock)
{
	if ((uintptr_t)clock == (uintptr_t)&__metal_dt_clock_7) {
		return (struct metal_clock *)&__metal_dt_clock_6.clock;
	}
	else {
		return NULL;
	}
}

static __inline__ unsigned long int __metal_driver_sifive_fe310_g000_lfrosc_config_reg(const struct metal_clock *clock)
{
	if ((uintptr_t)clock == (uintptr_t)&__metal_dt_clock_7) {
		return 112;
	}
	else {
		return 0;
	}
}

static __inline__ unsigned long int __metal_driver_sifive_fe310_g000_lfrosc_mux_reg(const struct metal_clock *clock)
{
	if ((uintptr_t)clock == (uintptr_t)&__metal_dt_clock_7) {
		return 124;
	}
	else {
		return 0;
	}
}



/* --------------------- sifive_fe310_g000_pll ------------ */
static __inline__ struct metal_clock * __metal_driver_sifive_fe310_g000_pll_pllsel0(const struct metal_clock *clock)
{
		return (struct metal_clock *)&__metal_dt_clock_3.clock;
}

static __inline__ struct metal_clock * __metal_driver_sifive_fe310_g000_pll_pllref(const struct metal_clock *clock)
{
		return (struct metal_clock *)&__metal_dt_clock_1.clock;
}

static __inline__ struct __metal_driver_sifive_fe310_g000_prci * __metal_driver_sifive_fe310_g000_pll_divider_base(const struct metal_clock *clock)
{
		return (struct __metal_driver_sifive_fe310_g000_prci *)&__metal_dt_prci_10008000;
}

static __inline__ long __metal_driver_sifive_fe310_g000_pll_divider_offset(const struct metal_clock *clock)
{
		return METAL_SIFIVE_FE310_G000_PRCI_PLLOUTDIV;
}

static __inline__ struct __metal_driver_sifive_fe310_g000_prci * __metal_driver_sifive_fe310_g000_pll_config_base( )
{
		return (struct __metal_driver_sifive_fe310_g000_prci *)&__metal_dt_prci_10008000;
}

static __inline__ long __metal_driver_sifive_fe310_g000_pll_config_offset( )
{
		return METAL_SIFIVE_FE310_G000_PRCI_PLLCFG;
}

static __inline__ long __metal_driver_sifive_fe310_g000_pll_init_rate( )
{
		return 16000000;
}



/* --------------------- sifive_fe310_g000_prci ------------ */
static __inline__ long __metal_driver_sifive_fe310_g000_prci_base( )
{
		return METAL_SIFIVE_FE310_G000_PRCI_10008000_BASE_ADDRESS;
}

static __inline__ long __metal_driver_sifive_fe310_g000_prci_size( )
{
		return METAL_SIFIVE_FE310_G000_PRCI_10008000_SIZE;
}

static __inline__ const struct __metal_driver_vtable_sifive_fe310_g000_prci * __metal_driver_sifive_fe310_g000_prci_vtable( )
{
		return &__metal_driver_vtable_sifive_fe310_g000_prci;
}



#define __METAL_DT_MAX_MEMORIES 3

__asm__ (".weak __metal_memory_table");
struct metal_memory *__metal_memory_table[] = {
					&__metal_dt_mem_dtim_80000000,
					&__metal_dt_mem_itim_8000000,
					&__metal_dt_mem_spi_10014000};

/* From serial@10013000 */
#define __METAL_DT_STDOUT_UART_HANDLE (&__metal_dt_serial_10013000.uart)

#define __METAL_DT_SERIAL_10013000_HANDLE (&__metal_dt_serial_10013000.uart)

#define __METAL_DT_STDOUT_UART_BAUD 115200

/* From clint@2000000 */
#define __METAL_DT_RISCV_CLINT0_HANDLE (&__metal_dt_clint_2000000.controller)

#define __METAL_DT_CLINT_2000000_HANDLE (&__metal_dt_clint_2000000.controller)

#define __METAL_DT_MAX_HARTS 1

#define __METAL_CPU_0_ICACHE_HANDLE 1

__asm__ (".weak __metal_cpu_table");
struct __metal_driver_cpu *__metal_cpu_table[] = {
					&__metal_dt_cpu_0};

/* From interrupt_controller@c000000 */
#define __METAL_DT_RISCV_PLIC0_HANDLE (&__metal_dt_interrupt_controller_c000000.controller)

#define __METAL_DT_INTERRUPT_CONTROLLER_C000000_HANDLE (&__metal_dt_interrupt_controller_c000000.controller)

#define __METAL_DT_PMP_HANDLE (&__metal_dt_pmp)

#define __MEE_DT_MAX_GPIOS 1

__asm__ (".weak __metal_gpio_table");
struct __metal_driver_sifive_gpio0 *__metal_gpio_table[] = {
					&__metal_dt_gpio_10012000};

#define __METAL_DT_MAX_BUTTONS 0

__asm__ (".weak __metal_button_table");
struct __metal_driver_sifive_gpio_button *__metal_button_table[] = {
					NULL };
#define __METAL_DT_MAX_LEDS 3

__asm__ (".weak __metal_led_table");
struct __metal_driver_sifive_gpio_led *__metal_led_table[] = {
					&__metal_dt_led_0,
					&__metal_dt_led_1,
					&__metal_dt_led_2};

#define __METAL_DT_MAX_SWITCHES 0

__asm__ (".weak __metal_switch_table");
struct __metal_driver_sifive_gpio_switch *__metal_switch_table[] = {
					NULL };
#define __METAL_DT_MAX_I2CS 1

__asm__ (".weak __metal_i2c_table");
struct __metal_driver_sifive_i2c0 *__metal_i2c_table[] = {
					&__metal_dt_i2c_10016000};

#define __METAL_DT_MAX_PWMS 3

__asm__ (".weak __metal_pwm_table");
struct __metal_driver_sifive_pwm0 *__metal_pwm_table[] = {
					&__metal_dt_pwm_10015000,
					&__metal_dt_pwm_10025000,
					&__metal_dt_pwm_10035000};

#define __METAL_DT_MAX_RTCS 1

__asm__ (".weak __metal_rtc_table");
struct __metal_driver_sifive_rtc0 *__metal_rtc_table[] = {
					&__metal_dt_rtc_10000000};

#define __METAL_DT_MAX_SPIS 3

__asm__ (".weak __metal_spi_table");
struct __metal_driver_sifive_spi0 *__metal_spi_table[] = {
					&__metal_dt_spi_10014000,
					&__metal_dt_spi_10024000,
					&__metal_dt_spi_10034000};

#define __METAL_DT_MAX_UARTS 2

__asm__ (".weak __metal_uart_table");
struct __metal_driver_sifive_uart0 *__metal_uart_table[] = {
					&__metal_dt_serial_10013000,
					&__metal_dt_serial_10023000};

#define __METAL_DT_MAX_SIMUARTS 0

__asm__ (".weak __metal_simuart_table");
struct __metal_driver_sifive_simuart0 *__metal_simuart_table[] = {
					NULL };
#define __METAL_DT_MAX_WDOGS 1

__asm__ (".weak __metal_wdog_table");
struct __metal_driver_sifive_wdog0 *__metal_wdog_table[] = {
					&__metal_dt_aon_10000000};

/* From clock@4 */
#define __METAL_DT_SIFIVE_FE310_G000_PLL_HANDLE (&__metal_dt_clock_4)

#define __METAL_DT_CLOCK_4_HANDLE (&__metal_dt_clock_4)

#endif /* MACROS_ELSE_METAL_H*/

#endif /* ! __METAL_MACHINE_MACROS */

#endif /* ! ASSEMBLY */
