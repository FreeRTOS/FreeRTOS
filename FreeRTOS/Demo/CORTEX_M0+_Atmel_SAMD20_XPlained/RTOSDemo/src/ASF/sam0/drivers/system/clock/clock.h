/**
 * \file
 *
 * \brief SAM D20 Clock Driver
 *
 * Copyright (C) 2012-2013 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */
#ifndef SYSTEM_CLOCK_H_INCLUDED
#define SYSTEM_CLOCK_H_INCLUDED

/**
 * \defgroup asfdoc_samd20_system_clock_group SAM D20 System Clock Management Driver (SYSTEM CLOCK)
 *
 * This driver for SAM D20 devices provides an interface for the configuration
 * and management of the device's clocking related functions. This includes
 * the various clock sources, bus clocks and generic clocks within the device,
 * with functions to manage the enabling, disabling, source selection and
 * prescaling of clocks to various internal peripherals.
 *
 * The following peripherals are used by this module:
 *
 * - GCLK (Generic Clock Management)
 * - PM (Power Management)
 * - SYSCTRL (Clock Source Control)
 *
 * The outline of this documentation is as follows:
 *  - \ref asfdoc_samd20_system_clock_prerequisites
 *  - \ref asfdoc_samd20_system_clock_module_overview
 *  - \ref asfdoc_samd20_system_clock_special_considerations
 *  - \ref asfdoc_samd20_system_clock_extra_info
 *  - \ref asfdoc_samd20_system_clock_examples
 *  - \ref asfdoc_samd20_system_clock_api_overview
 *
 *
 * \section asfdoc_samd20_system_clock_prerequisites Prerequisites
 *
 * There are no prerequisites for this module.
 *
 *
 * \section asfdoc_samd20_system_clock_module_overview Module Overview
 * The SAM D20 devices contain a sophisticated clocking system, which is designed
 * to give the maximum flexibility to the user application. This system allows
 * a system designer to tune the performance and power consumption of the device
 * in a dynamic manner, to achieve the best trade-off between the two for a
 * particular application.
 *
 * This driver provides a set of functions for the configuration and management
 * of the various clock related functionality within the device.
 *
 * \subsection asfdoc_samd20_system_clock_module_overview_clock_sources Clock Sources
 * The SAM D20 devices have a number of master clock source modules, each of
 * which being capable of producing a stabilized output frequency which can then
 * be fed into the various peripherals and modules within the device.
 *
 * Possible clock source modules include internal R/C oscillators, internal
 * DFLL modules, as well as external crystal oscillators and/or clock inputs.
 *
 * \subsection asfdoc_samd20_system_clock_module_overview_cpu_clock CPU / Bus Clocks
 * The CPU and AHB/APBx buses are clocked by the same physical clock source
 * (referred in this module as the Main Clock), however the APBx buses may
 * have additional prescaler division ratios set to give each peripheral bus a
 * different clock speed.
 *
 * The general main clock tree for the CPU and associated buses is shown in
 * \ref asfdoc_samd20_system_clock_module_clock_tree "the figure below".
 *
 * \anchor asfdoc_samd20_system_clock_module_clock_tree
 * \dot
 * digraph overview {
 *   rankdir=LR;
 *   clk_src [label="Clock Sources", shape=none, height=0];
 *   node [label="CPU Bus" shape=ellipse] cpu_bus;
 *   node [label="AHB Bus" shape=ellipse] ahb_bus;
 *   node [label="APBA Bus" shape=ellipse] apb_a_bus;
 *   node [label="APBB Bus" shape=ellipse] apb_b_bus;
 *   node [label="APBC Bus" shape=ellipse] apb_c_bus;
 *   node [label="Main Bus\nPrescaler" shape=square] main_prescaler;
 *   node [label="APBA Bus\nPrescaler" shape=square] apb_a_prescaler;
 *   node [label="APBB Bus\nPrescaler" shape=square] apb_b_prescaler;
 *   node [label="APBC Bus\nPrescaler" shape=square] apb_c_prescaler;
 *   node [label="", shape=polygon, sides=4, distortion=0.6, orientation=90, style=filled, fillcolor=black, height=0.9, width=0.2] main_clock_mux;
 *
 *   clk_src         -> main_clock_mux;
 *   main_clock_mux  -> main_prescaler;
 *   main_prescaler  -> cpu_bus;
 *   main_prescaler  -> ahb_bus;
 *   main_prescaler  -> apb_a_prescaler;
 *   main_prescaler  -> apb_b_prescaler;
 *   main_prescaler  -> apb_c_prescaler;
 *   apb_a_prescaler -> apb_a_bus;
 *   apb_b_prescaler -> apb_b_bus;
 *   apb_c_prescaler -> apb_c_bus;
 * }
 * \enddot
 *
 * \subsection asfdoc_samd20_system_clock_module_overview_clock_masking Clock Masking
 * To save power, the input clock to one or more peripherals on the AHB and APBx
 * busses can be masked away - when masked, no clock is passed into the module.
 * Disabling of clocks of unused modules will prevent all access to the masked
 * module, but will reduce the overall device power consumption.
 *
 * \subsection asfdoc_samd20_system_clock_module_overview_gclk Generic Clocks
 * Within the SAM D20 devices are a number of Generic Clocks; these are used to
 * provide clocks to the various peripheral clock domains in the device in a
 * standardized manner. One or more master source clocks can be selected as the
 * input clock to a Generic Clock Generator, which can prescale down the input
 * frequency to a slower rate for use in a peripheral.
 *
 * Additionally, a number of individually selectable Generic Clock Channels are
 * provided, which multiplex and gate the various generator outputs for one or
 * more peripherals within the device. This setup allows for a single common
 * generator to feed one or more channels, which can then be enabled or disabled
 * individually as required.
 *
 * \anchor asfdoc_samd20_system_clock_module_chain_overview
 * \dot
 * digraph overview {
 *   rankdir=LR;
 *   node [label="Clock\nSource a" shape=square] system_clock_source;
 *   node [label="Generator 1" shape=square] clock_gen;
 *   node [label="Channel x" shape=square] clock_chan0;
 *   node [label="Channel y" shape=square] clock_chan1;
 *   node [label="Peripheral x" shape=ellipse style=filled fillcolor=lightgray] peripheral0;
 *   node [label="Peripheral y" shape=ellipse style=filled fillcolor=lightgray] peripheral1;
 *
 *   system_clock_source -> clock_gen;
 *   clock_gen   -> clock_chan0;
 *   clock_chan0 -> peripheral0;
 *   clock_gen   -> clock_chan1;
 *   clock_chan1 -> peripheral1;
 * }
 * \enddot
 *
 * \subsubsection asfdoc_samd20_system_clock_module_chain_example Clock Chain Example
 * An example setup of a complete clock chain within the device is shown in
 * \ref asfdoc_samd20_system_clock_module_chain_example_fig "the figure below".
 *
 * \anchor asfdoc_samd20_system_clock_module_chain_example_fig
 * \dot
 * digraph overview {
 *   rankdir=LR;
 *   node [label="External\nOscillator" shape=square] system_clock_source0;
 *   node [label="Generator 0" shape=square] clock_gen0;
 *   node [label="Channel x" shape=square] clock_chan0;
 *   node [label="Core CPU" shape=ellipse  style=filled fillcolor=lightgray] peripheral0;
 *
 *   system_clock_source0 -> clock_gen0;
 *   clock_gen0    -> clock_chan0;
 *   clock_chan0   -> peripheral0;
 *   node [label="8MHz R/C\nOscillator (OSC8M)" shape=square fillcolor=white] system_clock_source1;
 *   node [label="Generator 1" shape=square] clock_gen1;
 *   node [label="Channel y" shape=square] clock_chan1;
 *   node [label="Channel z" shape=square] clock_chan2;
 *   node [label="SERCOM\nModule" shape=ellipse  style=filled fillcolor=lightgray] peripheral1;
 *   node [label="Timer\nModule" shape=ellipse  style=filled fillcolor=lightgray] peripheral2;
 *
 *   system_clock_source1 -> clock_gen1;
 *   clock_gen1    -> clock_chan1;
 *   clock_gen1    -> clock_chan2;
 *   clock_chan1   -> peripheral1;
 *   clock_chan2   -> peripheral2;
 * }
 * \enddot
 *
 * \subsubsection asfdoc_samd20_system_clock_module_overview_gclk_generators Generic Clock Generators
 * Each Generic Clock generator within the device can source its input clock
 * from one of the provided Source Clocks, and prescale the output for one or
 * more Generic Clock Channels in a one-to-many relationship. The generators
 * thus allow for several clocks to be generated of different frequencies,
 * power usages and accuracies, which can be turned on and off individually to
 * disable the clocks to multiple peripherals as a group.
 *
 * \subsubsection asfdoc_samd20_system_clock_module_overview_gclk_channels Generic Clock Channels
 * To connect a Generic Clock Generator to a peripheral within the
 * device, a Generic Clock Channel is used. Each peripheral or
 * peripheral group has an associated Generic Clock Channel, which serves as the
 * clock input for the peripheral(s). To supply a clock to the peripheral
 * module(s), the associated channel must be connected to a running Generic
 * Clock Generator and the channel enabled.
 *
 * \section asfdoc_samd20_system_clock_special_considerations Special Considerations
 *
 * There are no special considerations for this module.
 *
 *
 * \section asfdoc_samd20_system_clock_extra_info Extra Information
 *
 * For extra information see \ref asfdoc_samd20_system_clock_extra. This includes:
 *  - \ref asfdoc_samd20_system_clock_extra_acronyms
 *  - \ref asfdoc_samd20_system_clock_extra_dependencies
 *  - \ref asfdoc_samd20_system_clock_extra_errata
 *  - \ref asfdoc_samd20_system_clock_extra_history
 *
 *
 * \section asfdoc_samd20_system_clock_examples Examples
 *
 * For a list of examples related to this driver, see
 * \ref asfdoc_samd20_system_clock_exqsg.
 *
 *
 * \section asfdoc_samd20_system_clock_api_overview API Overview
 * @{
 */

#include <compiler.h>
#include <gclk.h>

/**
 * \brief Available start-up times for the XOSC32K
 *
 * Available external 32KHz oscillator start-up times, as a number of external
 * clock cycles.
 */
enum system_xosc32k_startup {
	/** Wait 0 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC32K_STARTUP_0,
	/** Wait 32 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC32K_STARTUP_32,
	/** Wait 2048 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC32K_STARTUP_2048,
	/** Wait 4096 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC32K_STARTUP_4096,
	/** Wait 16384 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC32K_STARTUP_16384,
	/** Wait 32768 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC32K_STARTUP_32768,
	/** Wait 65536 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC32K_STARTUP_65536,
	/** Wait 131072 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC32K_STARTUP_131072,
};

/**
 * \brief Available start-up times for the XOSC
 *
 * Available external oscillator start-up times, as a number of external clock
 * cycles.
 */
enum system_xosc_startup {
	/** Wait 1 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC_STARTUP_1,
	/** Wait 2 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC_STARTUP_2,
	/** Wait 4 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC_STARTUP_4,
	/** Wait 8 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC_STARTUP_8,
	/** Wait 16 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC_STARTUP_16,
	/** Wait 32 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC_STARTUP_32,
	/** Wait 64 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC_STARTUP_64,
	/** Wait 128 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC_STARTUP_128,
	/** Wait 256 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC_STARTUP_256,
	/** Wait 512 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC_STARTUP_512,
	/** Wait 1024 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC_STARTUP_1024,
	/** Wait 2048 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC_STARTUP_2048,
	/** Wait 4096 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC_STARTUP_4096,
	/** Wait 8192 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC_STARTUP_8192,
	/** Wait 16384 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC_STARTUP_16384,
	/** Wait 32768 clock cycles until the clock source is considered stable */
	SYSTEM_XOSC_STARTUP_32768,
};

/**
 * \brief Available start-up times for the OSC32K
 *
 * Available internal 32KHz oscillator start-up times, as a number of internal
 * OSC32K clock cycles.
 */
enum system_osc32k_startup {
	/** Wait 0 clock cycles until the clock source is considered stable */
	SYSTEM_OSC32K_STARTUP_0,
	/** Wait 2 clock cycles until the clock source is considered stable */
	SYSTEM_OSC32K_STARTUP_2,
	/** Wait 4 clock cycles until the clock source is considered stable */
	SYSTEM_OSC32K_STARTUP_4,
	/** Wait 8 clock cycles until the clock source is considered stable */
	SYSTEM_OSC32K_STARTUP_8,
	/** Wait 16 clock cycles until the clock source is considered stable */
	SYSTEM_OSC32K_STARTUP_16,
	/** Wait 32 clock cycles until the clock source is considered stable */
	SYSTEM_OSC32K_STARTUP_32,
	/** Wait 64 clock cycles until the clock source is considered stable */
	SYSTEM_OSC32K_STARTUP_64,
	/** Wait 128 clock cycles until the clock source is considered stable */
	SYSTEM_OSC32K_STARTUP_128,
};

/**
 * \brief Division prescalers for the internal 8MHz system clock
 *
 * Available prescalers for the internal 8MHz (nominal) system clock.
 */
enum system_osc8m_div {
	/** Do not divide the 8MHz RC oscillator output */
	SYSTEM_OSC8M_DIV_1,
	/** Divide the 8MHz RC oscillator output by 2 */
	SYSTEM_OSC8M_DIV_2,
	/** Divide the 8MHz RC oscillator output by 4 */
	SYSTEM_OSC8M_DIV_4,
	/** Divide the 8MHz RC oscillator output by 8 */
	SYSTEM_OSC8M_DIV_8,
};

/**
 * \brief Main CPU and APB/AHB bus clock source prescaler values
 *
 * Available division ratios for the CPU and APB/AHB bus clocks.
 */
enum system_main_clock_div {
	/** Divide Main clock by 1 */
	SYSTEM_MAIN_CLOCK_DIV_1,
	/** Divide Main clock by 2 */
	SYSTEM_MAIN_CLOCK_DIV_2,
	/** Divide Main clock by 4 */
	SYSTEM_MAIN_CLOCK_DIV_4,
	/** Divide Main clock by 8 */
	SYSTEM_MAIN_CLOCK_DIV_8,
	/** Divide Main clock by 16 */
	SYSTEM_MAIN_CLOCK_DIV_16,
	/** Divide Main clock by 32 */
	SYSTEM_MAIN_CLOCK_DIV_32,
	/** Divide Main clock by 64 */
	SYSTEM_MAIN_CLOCK_DIV_64,
	/** Divide Main clock by 128 */
	SYSTEM_MAIN_CLOCK_DIV_128,
};

/**
 * \brief External clock source types.
 *
 * Available external clock source types.
 */
enum system_clock_external {
	/** The external clock source is a crystal oscillator */
	SYSTEM_CLOCK_EXTERNAL_CRYSTAL,
	/** The connected clock source is an external logic level clock signal */
	SYSTEM_CLOCK_EXTERNAL_CLOCK,
};

/**
 * \brief Operating modes of the DFLL clock source.
 *
 * Available operating modes of the DFLL clock source module,
 */
enum system_clock_dfll_loop_mode {
	/** The DFLL is operating in open loop mode with no feedback */
	SYSTEM_CLOCK_DFLL_LOOP_MODE_OPEN,
	/** The DFLL is operating in closed loop mode with frequency feedback from
	 *  a low frequency reference clock
	 */
	SYSTEM_CLOCK_DFLL_LOOP_MODE_CLOSED = SYSCTRL_DFLLCTRL_MODE,
};

/**
 * \brief Locking behavior for the DFLL during device wake-up
 *
 * DFLL lock behavior modes on device wake-up from sleep.
 */
enum system_clock_dfll_wakeup_lock {
	/** Keep DFLL lock when the device wakes from sleep */
	SYSTEM_CLOCK_DFLL_WAKEUP_LOCK_KEEP,
	/** Lose DFLL lock when the devices wakes from sleep */
	SYSTEM_CLOCK_DFLL_WAKEUP_LOCK_LOSE = SYSCTRL_DFLLCTRL_LLAW,
};

/**
 * \brief Fine tracking behavior for the DFLL once a lock has been acquired
 *
 * DFLL fine tracking behavior modes after a lock has been acquired.
 */
enum system_clock_dfll_stable_tracking {
	/** Keep tracking after the DFLL has gotten a fine lock */
	SYSTEM_CLOCK_DFLL_STABLE_TRACKING_TRACK_AFTER_LOCK,
	/** Stop tracking after the DFLL has gotten a fine lock */
	SYSTEM_CLOCK_DFLL_STABLE_TRACKING_FIX_AFTER_LOCK = SYSCTRL_DFLLCTRL_STABLE,
};

/**
 * \brief Chill-cycle behavior of the DFLL module
 *
 * DFLL chill-cycle behavior modes of the DFLL module. A chill cycle is a period
 * of time when the DFLL output frequency is not measured by the unit, to allow
 * the output to stabilize after a change in the input clock source.
 */
enum system_clock_dfll_chill_cycle {
	/** Enable a chill cycle, where the DFLL output frequency is not measured */
	SYSTEM_CLOCK_DFLL_CHILL_CYCLE_ENABLE,
	/** Disable a chill cycle, where the DFLL output frequency is not measured */
	SYSTEM_CLOCK_DFLL_CHILL_CYCLE_DISABLE = SYSCTRL_DFLLCTRL_CCDIS,
};

/**
 * \brief QuickLock settings for the DFLL module
 *
 * DFLL QuickLock settings for the DFLL module, to allow for a faster lock of
 * the DFLL output frequency at the expense of accuracy.
 */
enum system_clock_dfll_quick_lock {
	/** Enable the QuickLock feature for looser lock requirements on the DFLL */
	SYSTEM_CLOCK_DFLL_QUICK_LOCK_ENABLE,
	/** Disable the QuickLock feature for strict lock requirements on the DFLL */
	SYSTEM_CLOCK_DFLL_QUICK_LOCK_DISABLE = SYSCTRL_DFLLCTRL_QLDIS,
};

/**
 * \brief List of APB peripheral buses
 *
 * Available bus clock domains on the APB bus.
 */
enum system_clock_apb_bus {
	/** Peripheral bus A on the APB bus. */
	SYSTEM_CLOCK_APB_APBA,
	/** Peripheral bus B on the APB bus. */
	SYSTEM_CLOCK_APB_APBB,
	/** Peripheral bus C on the APB bus. */
	SYSTEM_CLOCK_APB_APBC,
};

/**
 * \brief Available clock sources in the system
 *
 * Clock sources available to the GCLK generators
 */
enum system_clock_source {
	/** Internal 8MHz RC oscillator */
	SYSTEM_CLOCK_SOURCE_OSC8M    = GCLK_SOURCE_OSC8M,
	/** Internal 32kHz RC oscillator */
	SYSTEM_CLOCK_SOURCE_OSC32K   = GCLK_SOURCE_OSC32K,
	/** External oscillator */
	SYSTEM_CLOCK_SOURCE_XOSC     = GCLK_SOURCE_XOSC ,
	/** External 32kHz oscillator */
	SYSTEM_CLOCK_SOURCE_XOSC32K  = GCLK_SOURCE_XOSC32K,
	/** Digital Frequency Locked Loop (DFLL) */
	SYSTEM_CLOCK_SOURCE_DFLL     = GCLK_SOURCE_DFLL48M,
	/** Internal Ultra Low Power 32kHz oscillator */
	SYSTEM_CLOCK_SOURCE_ULP32K   = GCLK_SOURCE_OSCULP32K,
};

/**
 * \brief Configuration structure for XOSC
 *
 * External oscillator clock configuration structure.
 */
struct system_clock_source_xosc_config {
	/** External clock type */
	enum system_clock_external external_clock;
	/** Crystal oscillator start-up time */
	enum system_xosc_startup startup_time;
	/** Enable automatic amplitude gain control */
	bool auto_gain_control;
	/** External clock/crystal frequency */
	uint32_t frequency;
	/** Keep the XOSC enabled in standby sleep mode */
	bool run_in_standby;
	/** Run On Demand. If this is set the XOSC won't run
	 * until requested by a peripheral */
	bool on_demand;
};

/**
 * \brief Configuration structure for XOSC32K
 *
 * External 32KHz oscillator clock configuration structure.
 */
struct system_clock_source_xosc32k_config {
	/** External clock type */
	enum system_clock_external external_clock;
	/** Crystal oscillator start-up time */
	enum system_xosc32k_startup startup_time;
	/** Enable automatic amplitude control */
	bool auto_gain_control;
	/** Enable 1kHz output */
	bool enable_1khz_output;
	/** Enable 32kHz output */
	bool enable_32khz_output;
	/** External clock/crystal frequency */
	uint32_t frequency;
	/** Keep the XOSC32K enabled in standby sleep mode */
	bool run_in_standby;
	/** Run On Demand. If this is set the XOSC32K won't run
	 * until requested by a peripheral */
	bool on_demand;
};

/**
 * \brief Configuration structure for OSC8M
 *
 * Internal 8MHz (nominal) oscillator configuration structure.
 */
struct system_clock_source_osc8m_config {
	/* Internal 8MHz RC oscillator prescaler */
	enum system_osc8m_div prescaler;
	/** Keep the OSC8M enabled in standby sleep mode */
	bool run_in_standby;
	/** Run On Demand. If this is set the OSC8M won't run
	 * until requested by a peripheral */
	bool on_demand;
};

/**
 * \brief Configuration structure for OSC32K
 *
 * Internal 32KHz (nominal) oscillator configuration structure.
 */
struct system_clock_source_osc32k_config {
	/** Startup time */
	enum system_osc32k_startup startup_time;
	/** Enable 1kHz output */
	bool enable_1khz_output;
	/** Enable 32kHz output */
	bool enable_32khz_output;
	/** Keep the OSC32K enabled in standby sleep mode */
	bool run_in_standby;
	/** Run On Demand. If this is set the OSC32K won't run
	 * until requested by a peripheral */
	bool on_demand;
};

/**
 * \brief Configuration structure for DFLL
 *
 * DFLL oscillator configuration structure.
 */
struct system_clock_source_dfll_config {
	/** Loop mode */
	enum system_clock_dfll_loop_mode loop_mode;
	/** Keep the DFLL enabled in standby sleep mode */
	bool run_in_standby;
	/** Run On Demand. If this is set the DFLL won't run
	 * until requested by a peripheral */
	bool on_demand;
	/** Enable Quick Lock */
	enum system_clock_dfll_quick_lock quick_lock;
	/** Enable Chill Cycle */
	enum system_clock_dfll_chill_cycle chill_cycle;
	/** DFLL lock state on wakeup */
	enum system_clock_dfll_wakeup_lock wakeup_lock;
	/** DFLL tracking after fine lock */
	enum system_clock_dfll_stable_tracking stable_tracking;
	/** Coarse calibration value (Open loop mode) */
	uint8_t coarse_value;
	/** Fine calibration value (Open loop mode) */
	uint8_t fine_value;
	/** Coarse adjustment max step size (Closed loop mode) */
	uint8_t coarse_max_step;
	/** Fine adjustment max step size (Closed loop mode) */
	uint8_t fine_max_step;
	/** DFLL multiply factor (Closed loop mode */
	uint16_t multiply_factor;
};

/**
 * \name External Oscillator management
 * @{
 */

/**
 * \brief Retrieve the default configuration for XOSC
 *
 * Fills a configuration structure with the default configuration for an
 * external oscillator module:
 *   - External Crystal
 *   - Start-up time of 16384 external clock cycles
 *   - Automatic crystal gain control mode enabled
 *   - Frequency of 12MHz
 *   - Don't run in STANDBY sleep mode
 *   - Run only when requested by peripheral (on demand)
 *
 * \param[out] config  Configuration structure to fill with default values
 */
static inline void system_clock_source_xosc_get_config_defaults(
		struct system_clock_source_xosc_config *const config)
{
	Assert(config);

	config->external_clock    = SYSTEM_CLOCK_EXTERNAL_CRYSTAL;
	config->startup_time      = SYSTEM_XOSC_STARTUP_16384;
	config->auto_gain_control = true;
	config->frequency         = 12000000UL;
	config->run_in_standby    = false;
	config->on_demand         = true;
}

void system_clock_source_xosc_set_config(
		struct system_clock_source_xosc_config *const config);

/**
 * @}
 */


/**
 * \name External 32KHz Oscillator management
 * @{
 */

/**
 * \brief Retrieve the default configuration for XOSC32K
 *
 * Fills a configuration structure with the default configuration for an
 * external 32KHz oscillator module:
 *   - External Crystal
 *   - Start-up time of 16384 external clock cycles
 *   - Automatic crystal gain control mode enabled
 *   - Frequency of 32.768KHz
 *   - 1KHz clock output disabled
 *   - 32KHz clock output enabled
 *   - Don't run in STANDBY sleep mode
 *   - Run only when requested by peripheral (on demand)
 *
 * \param[out] config  Configuration structure to fill with default values
 */
static inline void system_clock_source_xosc32k_get_config_defaults(
		struct system_clock_source_xosc32k_config *const config)
{
	Assert(config);

	config->external_clock      = SYSTEM_CLOCK_EXTERNAL_CRYSTAL;
	config->startup_time        = SYSTEM_XOSC32K_STARTUP_16384;
	config->auto_gain_control   = true;
	config->frequency           = 32768UL;
	config->enable_1khz_output  = false;
	config->enable_32khz_output = true;
	config->run_in_standby      = false;
	config->on_demand           = true;
}

void system_clock_source_xosc32k_set_config(
		struct system_clock_source_xosc32k_config *const config);
/**
 * @}
 */


/**
 * \name Internal 32KHz Oscillator management
 * @{
 */

/**
 * \brief Retrieve the default configuration for OSC32K
 *
 * Fills a configuration structure with the default configuration for an
 * internal 32KHz oscillator module:
 *   - 1KHz clock output enabled
 *   - 32KHz clock output enabled
 *   - Don't run in STANDBY sleep mode
 *   - Run only when requested by peripheral (on demand)
 *
 * \param[out] config  Configuration structure to fill with default values
 */
static inline void system_clock_source_osc32k_get_config_defaults(
		struct system_clock_source_osc32k_config *const config)
{
	Assert(config);

	config->enable_1khz_output  = true;
	config->enable_32khz_output = true;
	config->run_in_standby      = false;
	config->on_demand           = true;
}

void system_clock_source_osc32k_set_config(
		struct system_clock_source_osc32k_config *const config);

/**
 * @}
 */


/**
 * \name Internal 8MHz Oscillator management
 * @{
 */

/**
 * \brief Retrieve the default configuration for OSC8M
 *
 * Fills a configuration structure with the default configuration for an
 * internal 8MHz (nominal) oscillator module:
 *   - Clock output frequency divided by a factor of 8
 *   - Don't run in STANDBY sleep mode
 *   - Run only when requested by peripheral (on demand)
 *
 * \param[out] config  Configuration structure to fill with default values
 */
static inline void system_clock_source_osc8m_get_config_defaults(
		struct system_clock_source_osc8m_config *const config)
{
	Assert(config);

	config->prescaler      = SYSTEM_OSC8M_DIV_8;
	config->run_in_standby = false;
	config->on_demand      = true;
}

void system_clock_source_osc8m_set_config(
		struct system_clock_source_osc8m_config *const config);

/**
 * @}
 */


/**
 * \name Internal DFLL management
 * @{
 */

/**
 * \brief Retrieve the default configuration for DFLL
 *
 * Fills a configuration structure with the default configuration for a
 * DFLL oscillator module:
 *   - Open loop mode
 *   - QuickLock mode enabled
 *   - Chill cycle enabled
 *   - Output frequency lock maintained during device wake-up
 *   - Continuous tracking of the output frequency
 *   - Default tracking values at the mid-points for both coarse and fine
 *     tracking parameters
 *   - Don't run in STANDBY sleep mode
 *   - Run only when requested by peripheral (on demand)
 *
 * \param[out] config  Configuration structure to fill with default values
 */
static inline void system_clock_source_dfll_get_config_defaults(
		struct system_clock_source_dfll_config *const config)
{
	Assert(config);

	config->loop_mode       = SYSTEM_CLOCK_DFLL_LOOP_MODE_OPEN;
	config->quick_lock      = SYSTEM_CLOCK_DFLL_QUICK_LOCK_ENABLE;
	config->chill_cycle     = SYSTEM_CLOCK_DFLL_CHILL_CYCLE_ENABLE;
	config->wakeup_lock     = SYSTEM_CLOCK_DFLL_WAKEUP_LOCK_KEEP;
	config->stable_tracking = SYSTEM_CLOCK_DFLL_STABLE_TRACKING_TRACK_AFTER_LOCK;
	config->run_in_standby  = false;
	config->on_demand       = true;

	/* Open loop mode calibration value */
	config->coarse_value    = 0x1f / 4; /* Midpoint */
	config->fine_value      = 0xff / 4; /* Midpoint */

	/* Closed loop mode */
	config->coarse_max_step = 1;
	config->fine_max_step   = 1;
	config->multiply_factor = 6; /* Multiply 8MHz by 6 to get 48MHz */
}

void system_clock_source_dfll_set_config(
		struct system_clock_source_dfll_config *const config);

/**
 * @}
 */

/**
 * \name Clock source management
 * @{
 */
enum status_code system_clock_source_write_calibration(
		const enum system_clock_source system_clock_source,
		const uint16_t calibration_value,
		const uint8_t freq_range);

enum status_code system_clock_source_enable(
		const enum system_clock_source system_clock_source);

enum status_code system_clock_source_disable(
		const enum system_clock_source clk_source);

bool system_clock_source_is_ready(
		const enum system_clock_source clk_source);

uint32_t system_clock_source_get_hz(
		const enum system_clock_source clk_source);

/**
 * @}
 */

/**
 * \name Main clock management
 * @{
 */

/**
 * \brief Enable or disable the main clock failure detection.
 *
 * This mechanism allows switching automatically the main clock to the safe
 * RCSYS clock, when the main clock source is considered off.
 *
 * This may happen for instance when an external crystal is selected as the
 * clock source of the main clock and the crystal dies. The mechanism is to
 * detect, during a RCSYS period, at least one rising edge of the main clock.
 * If no rising edge is seen the clock is considered failed.
 * As soon as the detector is enabled, the clock failure detector
 * CFD) will monitor the divided main clock. When a clock failure is detected,
 * the main clock automatically switches to the RCSYS clock and the CFD
 * interrupt is generated if enabled.
 *
 * \note The failure detect must be disabled if the system clock is the same or
 *       slower than 32kHz as it will believe the system clock has failed with
 *       a too-slow clock.
 *
 * \param[in] enable  Boolean \c true to enable, \c false to disable detection
 */
static inline void system_main_clock_set_failure_detect(
		const bool enable)
{
	if (enable) {
		PM->CTRL.reg |=  PM_CTRL_CFDEN;
	} else {
		PM->CTRL.reg &= ~PM_CTRL_CFDEN;
	}
}

/**
 * \brief Set main CPU clock divider.
 *
 * Sets the clock divider used on the main clock to provide the CPU clock.
 *
 * \param[in] divider  CPU clock divider to set
 */
static inline void system_cpu_clock_set_divider(
		const enum system_main_clock_div divider)
{
	Assert(((uint32_t)divider & PM_CPUSEL_CPUDIV_Msk) == divider);
	PM->CPUSEL.reg = (uint32_t)divider;
}

/**
 * \brief Retrieves the current frequency of the CPU core.
 *
 * Retrieves the operating frequency of the CPU core, obtained from the main
 * generic clock and the set CPU bus divider.
 *
 * \return Current CPU frequency in Hz.
 */
static inline uint32_t system_cpu_clock_get_hz(void)
{
	return (system_gclk_gen_get_hz(GCLK_GENERATOR_0) >> PM->CPUSEL.reg);
}

/**
 * \brief Set APBx clock divider.
 *
 * Set the clock divider used on the main clock to provide the clock for the
 * given APBx bus.
 *
 * \param[in] divider  APBx bus divider to set
 * \param[in] bus      APBx bus to set divider for
 *
 * \returns Status of the clock division change operation.
 *
 * \retval STATUS_ERR_INVALID_ARG  Invalid bus ID was given
 * \retval STATUS_OK               The APBx clock was set successfully
 */
static inline enum status_code system_apb_clock_set_divider(
		const enum system_clock_apb_bus bus,
		const enum system_main_clock_div divider)
{
	switch (bus) {
		case SYSTEM_CLOCK_APB_APBA:
			PM->APBASEL.reg = (uint32_t)divider;
			break;
		case SYSTEM_CLOCK_APB_APBB:
			PM->APBBSEL.reg = (uint32_t)divider;
			break;
		case SYSTEM_CLOCK_APB_APBC:
			PM->APBCSEL.reg = (uint32_t)divider;
			break;
		default:
			Assert(false);
			return STATUS_ERR_INVALID_ARG;
	}

	return STATUS_OK;
}

/**
 * \brief Retrieves the current frequency of a ABPx.
 *
 * Retrieves the operating frequency of an APBx bus, obtained from the main
 * generic clock and the set APBx bus divider.
 *
 * \return Current APBx bus frequency in Hz.
 */
static inline uint32_t system_apb_clock_get_hz(
		const enum system_clock_apb_bus bus)
{
	uint16_t bus_divider = 0;

	switch (bus) {
		case SYSTEM_CLOCK_APB_APBA:
			bus_divider = PM->APBASEL.reg;
			break;
		case SYSTEM_CLOCK_APB_APBB:
			bus_divider = PM->APBBSEL.reg;
			break;
		case SYSTEM_CLOCK_APB_APBC:
			bus_divider = PM->APBCSEL.reg;
			break;
		default:
			Assert(false);
			return 0;
	}

	return (system_gclk_gen_get_hz(GCLK_GENERATOR_0) >> bus_divider);
}


/**
 * @}
 */

/**
 * \name Bus clock masking
 * @{
 */

/**
 * \brief Set bits in the clock mask for the AHB bus.
 *
 * This function will set bits in the clock mask for the AHB bus.
 * Any bits set to 1 will enable that clock, 0 bits in the mask
 * will be ignored
 *
 * \param[in] ahb_mask  AHB clock mask to enable
 */
static inline void system_ahb_clock_set_mask(
		const uint32_t ahb_mask)
{
	PM->AHBMASK.reg |= ahb_mask;
}

/**
 * \brief Clear bits in the clock mask for the AHB bus.
 *
 * This function will clear bits in the clock mask for the AHB bus.
 * Any bits set to 1 will disable that clock, 0 bits in the mask
 * will be ignored.
 *
 * \param[in] ahb_mask  AHB clock mask to disable
 */
static inline void system_ahb_clock_clear_mask(
		const uint32_t ahb_mask)
{
	PM->AHBMASK.reg &= ~ahb_mask;
}

/**
 * \brief Set bits in the clock mask for an APBx bus.
 *
 * This function will set bits in the clock mask for an APBx bus.
 * Any bits set to 1 will enable the corresponding module clock, zero bits in
 * the mask will be ignored.
 *
 * \param[in] mask  APBx clock mask, a \c SYSTEM_CLOCK_APB_APBx constant from
 *                  the device header files
 * \param[in] bus   Bus to set clock mask bits for, a mask of \c PM_APBxMASK_*
 *                  constants from the device header files
 *
 * \returns Status indicating the result of the clock mask change operation.
 *
 * \retval STATUS_ERR_INVALID_ARG  Invalid bus given
 * \retval STATUS_OK               The clock mask was set successfully
 */
static inline enum status_code system_apb_clock_set_mask(
		const enum system_clock_apb_bus bus,
		const uint32_t mask)
{
	switch (bus) {
		case SYSTEM_CLOCK_APB_APBA:
			PM->APBAMASK.reg |= mask;
			break;

		case SYSTEM_CLOCK_APB_APBB:
			PM->APBBMASK.reg |= mask;
			break;

		case SYSTEM_CLOCK_APB_APBC:
			PM->APBCMASK.reg |= mask;
			break;

		default:
			Assert(false);
			return STATUS_ERR_INVALID_ARG;

	}

	return STATUS_OK;
}

/**
 * \brief Clear bits in the clock mask for an APBx bus.
 *
 * This function will clear bits in the clock mask for an APBx bus.
 * Any bits set to 1 will disable the corresponding module clock, zero bits in
 * the mask will be ignored.
 *
 * \param[in] mask  APBx clock mask, a \c SYSTEM_CLOCK_APB_APBx constant from
 *                  the device header files
 * \param[in] bus   Bus to clear clock mask bits for
 *
 * \returns Status indicating the result of the clock mask change operation.
 *
 * \retval STATUS_ERR_INVALID_ARG  Invalid bus ID was given.
 * \retval STATUS_OK               The clock mask was changed successfully.
 */
static inline enum status_code system_apb_clock_clear_mask(
		const enum system_clock_apb_bus bus,
		const uint32_t mask)
{
	switch (bus) {
		case SYSTEM_CLOCK_APB_APBA:
			PM->APBAMASK.reg &= ~mask;
			break;

		case SYSTEM_CLOCK_APB_APBB:
			PM->APBBMASK.reg &= ~mask;
			break;

		case SYSTEM_CLOCK_APB_APBC:
			PM->APBCMASK.reg &= ~mask;
			break;

		default:
			Assert(false);
			return STATUS_ERR_INVALID_ARG;
	}

	return STATUS_OK;
}

/**
 * @}
 */

/**
 * \name System Clock Initialization
 * @{
 */

void system_clock_init(void);

/**
 * @}
 */

/**
 * \name System Flash Wait States
 * @{
 */

/**
 * \brief Set flash controller wait states
 *
 * Will set the number of wait states that are used by the onboard
 * flash memory. The number of wait states depend on both device
 * supply voltage and CPU speed. The required number of wait states
 * can be found in the electrical characteristics of the device.
 *
 * \param[in] wait_states Number of wait states to use for internal flash
 */
static inline void system_flash_set_waitstates(uint8_t wait_states)
{
	Assert((wait_states & NVMCTRL_CTRLB_RWS_Msk) == wait_states);
	NVMCTRL->CTRLB.bit.RWS = wait_states;
}
/**
 * @}
 */

/**
 * @}
 */

/**
 * \page asfdoc_samd20_system_clock_extra Extra Information for SYSTEM CLOCK Driver
 *
 * \section asfdoc_samd20_system_clock_extra_acronyms Acronyms
 * Below is a table listing the acronyms used in this module, along with their
 * intended meanings.
 *
 * <table>
 *	<tr>
 *		<th>Acronym</th>
 *		<th>Description</th>
 *	</tr>
 *	<tr>
 *		<td>DFLL</td>
 *		<td>Digital Frequency Locked Loop</td>
 *	</tr>
 *	<tr>
 *		<td>MUX</td>
 *		<td>Multiplexer</td>
 *	</tr>
 *	<tr>
 *		<td>OSC32K</td>
 *		<td>Internal 32KHz Oscillator</td>
 *	</tr>
 *	<tr>
 *		<td>OSC8M</td>
 *		<td>Internal 8MHz Oscillator</td>
 *	</tr>
 *	<tr>
 *		<td>PLL</td>
 *		<td>Phase Locked Loop</td>
 *	</tr>
 *	<tr>
 *		<td>OSC</td>
 *		<td>Oscillator</td>
 *	</tr>
 *	<tr>
 *		<td>XOSC</td>
 *		<td>External Oscillator</td>
 *	</tr>
 *	<tr>
 *		<td>XOSC32K</td>
 *		<td>External 32KHz Oscillator</td>
 *	</tr>
 *	<tr>
 *		<td>AHB</td>
 *		<td>Advanced High-performance Bus</td>
 *	</tr>
 *	<tr>
 *		<td>APB</td>
 *		<td>Advanced Peripheral Bus</td>
 *	</tr>
 * </table>
 *
 *
 * \section asfdoc_samd20_system_clock_extra_dependencies Dependencies
 * This driver has the following dependencies:
 *
 *  - None
 *
 *
 * \section asfdoc_samd20_system_clock_extra_errata Errata
 *	<tr>
 *	<td>
 *	 \li This driver implements workaround for errata 10558
 *	     "Several reset values of SYSCTRL.INTFLAG are wrong (BOD and DFLL)"<br>
 *	     When system_init is called it will reset these interrupts flags before they are used.
 *	</td>
 *	</tr>
 *
 *	<tr>
 *	<td>
 *	 \li This driver implements experimental workaround for errata 9905<br>
 *	     "The DFLL clock must be requested before being configured otherwise a
 *	     write access to a DFLL register can freeze the device."<br>
 *	     This driver will enable and configure the DFLL before the ONDEMAND bit is set.
 *	</td>
 *	</tr>
 *	
 *
 *
 * \section asfdoc_samd20_system_clock_extra_history Module History
 * An overview of the module history is presented in the table below, with
 * details on the enhancements and fixes made to the module since its first
 * release. The current version of this corresponds to the newest version in
 * the table.
 *
 * <table>
 *	<tr>
 *		<th>Changelog</th>
 *	</tr>
 *	<tr>
 *		<td>
 *			\li Changed default value for CONF_CLOCK_DFLL_ON_DEMAND from true to false
 *		</td>
 *	</tr>
 *	<tr>
 *		<td>\li Updated dfll configuration function to implement workaround for errata 9905 in the DFLL module.
 *		    \li Updated \c system_clock_init() to reset interrupt flags before they are used, errata 10558.
 *		    \li Fixed \c system_clock_source_get_hz() to return correcy DFLL frequency number.
 *		</td>
 *	</tr>
 *	<tr>
 *		<td>\li Fixed \c system_clock_source_is_ready not returning the correct
 *              state for \c SYSTEM_CLOCK_SOURCE_OSC8M.
 *          \li Renamed the various \c system_clock_source_*_get_default_config()
 *              functions to \c system_clock_source_*_get_config_defaults() to
 *              match the remainder of ASF.
 *          \li Added OSC8M calibration constant loading from the device signature
 *              row when the oscillator is initialized.</td>
 *	</tr>
 *	<tr>
 *		<td>Initial Release</td>
 *	</tr>
 * </table>
 */

/**
 * \page asfdoc_samd20_system_clock_exqsg Examples for System Clock Driver
 *
 * This is a list of the available Quick Start guides (QSGs) and example
 * applications for \ref asfdoc_samd20_system_clock_group. QSGs are simple
 * examples with step-by-step instructions to configure and use this driver in
 * a selection of use cases. Note that QSGs can be compiled as a standalone
 * application or be added to the user application.
 *
 *  - \subpage asfdoc_samd20_system_clock_basic_use_case
 *  - \subpage asfdoc_samd20_system_gclk_basic_use_case
 *
 * \page asfdoc_samd20_system_clock_document_revision_history Document Revision History
 *
 * <table>
 *	<tr>
 *		<th>Doc. Rev.</td>
 *		<th>Date</td>
 *		<th>Comments</td>
 *	</tr>
 *	<tr>
 *		<td>B</td>
 *		<td>06/2013</td>
 *		<td>Corrected documentation typos.</td>
 *	</tr>
 *	<tr>
 *		<td>A</td>
 *		<td>06/2013</td>
 *		<td>Initial release</td>
 *	</tr>
 * </table>
 */

#endif /* SYSTEM_CLOCK_H_INCLUDED */
