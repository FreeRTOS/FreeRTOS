/**
 * \file
 *
 * \brief BPM driver.
 *
 * Copyright (C) 2012 - 2013 Atmel Corporation. All rights reserved.
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

#ifndef BPM_H_INCLUDED
#define BPM_H_INCLUDED

#include "compiler.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * \defgroup group_sam_drivers_bpm BPM - Backup Power Manager
 *
 * Driver for the BPM (Backup Power Manager).
 * This driver provides access to the main features of the BPM controller.
 * It provides functions for different power mode management.
 *
 * @{
 */

/** BPM unlock macro */
#define BPM_UNLOCK(reg) \
	do { \
		BPM->BPM_UNLOCK = BPM_UNLOCK_KEY(0xAAu)                          \
			| BPM_UNLOCK_ADDR((uint32_t)&BPM->BPM_##reg - (uint32_t)BPM);\
	} while (0)

/** \name Sleep mode definitions */
/* @{ */
#define BPM_SM_ACTIVE    0    /**< Active mode */
#define BPM_SM_SLEEP_0   1    /**< Sleep mode 0 */
#define BPM_SM_SLEEP_1   2    /**< Sleep mode 1 */
#define BPM_SM_SLEEP_2   3    /**< Sleep mode 2 */
#define BPM_SM_SLEEP_3   4    /**< Sleep mode 3 */
#define BPM_SM_WAIT      5    /**< Wait mode */
#define BPM_SM_RET       6    /**< Retention mode */
#define BPM_SM_BACKUP    7    /**< Backup mode */
/* @} */

/** \anchor power_scaling_change_mode */
/** \name Power scaling change mode */
/* @{ */
/** Power scaling change mode: halting the CPU execution */
#define BPM_PSCM_CPU_HALT           0
/** Power scaling change mode: CPU execution not halted */
#define BPM_PSCM_CPU_NOT_HALT       1
/* @} */

/** \anchor power_scaling_mode_value */
/** \name Power scaling mode value */
/* @{ */
/** Power scaling mode 0 */
#define BPM_PS_0    0
/** Power scaling mode 1 */
#define BPM_PS_1    1
/** Power scaling mode 2 */
#define BPM_PS_2    2
/* @} */

/** \anchor CLK32_32Khz_1Khz */
/** \name CLK32 32Khz-1Khz clock source selection */
/* @{ */
/** OSC32K : Low frequency crystal oscillator */
#define BPM_CLK32_SOURCE_OSC32K  0
/** RC32K : Internal Low frequency RC oscillator */
#define BPM_CLK32_SOURCE_RC32K   1
/* @} */

/** \anchor backup_wake_up_sources */
/** \name Backup wake up sources */
/* @{ */
/** EIC wake up */
#define BPM_BKUP_WAKEUP_SRC_EIC       (1UL << BPM_BKUPWEN_EIC)
/** AST wake up */
#define BPM_BKUP_WAKEUP_SRC_AST       (1UL << BPM_BKUPWEN_AST)
/** WDT wake up */
#define BPM_BKUP_WAKEUP_SRC_WDT       (1UL << BPM_BKUPWEN_WDT)
/** BOD33 wake up */
#define BPM_BKUP_WAKEUP_SRC_BOD33     (1UL << BPM_BKUPWEN_BOD33)
/** BOD18 wake up */
#define BPM_BKUP_WAKEUP_SRC_BOD18     (1UL << BPM_BKUPWEN_BOD18)
/** PICOUART wake up */
#define BPM_BKUP_WAKEUP_SRC_PICOUART  (1UL << BPM_BKUPWEN_PICOUART)
/* @} */

/** \anchor backup_pin_muxing */
/** \name Backup pin muxing */
/* @{ */
#define BPM_BKUP_PIN_PB01_EIC0    BPM_BKUPPMUX_BKUPPMUX(0)
#define BPM_BKUP_PIN_PA06_EIC1    BPM_BKUPPMUX_BKUPPMUX(1)
#define BPM_BKUP_PIN_PA04_EIC2    BPM_BKUPPMUX_BKUPPMUX(2)
#define BPM_BKUP_PIN_PA05_EIC3    BPM_BKUPPMUX_BKUPPMUX(3)
#define BPM_BKUP_PIN_PA07_EIC4    BPM_BKUPPMUX_BKUPPMUX(4)
#define BPM_BKUP_PIN_PC03_EIC5    BPM_BKUPPMUX_BKUPPMUX(5)
#define BPM_BKUP_PIN_PC04_EIC6    BPM_BKUPPMUX_BKUPPMUX(6)
#define BPM_BKUP_PIN_PC05_EIC7    BPM_BKUPPMUX_BKUPPMUX(7)
#define BPM_BKUP_PIN_PC06_EIC8    BPM_BKUPPMUX_BKUPPMUX(8)
/* @} */

/**
 * \name Power management
 */
/* @{ */

/**
 * \brief Change Power Scaling mode
 *
 * PSOK is not checked while switching PS mode.
 *
 * \param bpm  Base address of the BPM instance.
 * \param ps_value  Power scaling value, see \ref power_scaling_mode_value.
 *
 */
void bpm_power_scaling_cpu(Bpm *bpm, uint32_t ps_value);

/**
 * \brief Change Power Scaling mode and check results
 *
 * Wait for a while to check if PSOK is ready.
 *
 * \param bpm  Base address of the BPM instance.
 * \param ps_value  Power scaling value, see \ref power_scaling_mode_value.
 *
 * \param timeout Timeout, in number of processor clocks, max 0xFFFFFF.
 * \return true if PSOK is ready.
 */
bool bpm_power_scaling_cpu_failsafe(Bpm *bpm, uint32_t ps_value,
		uint32_t timeout);

/**
 * \brief Configure power scaling mode.
 *
 * While checking PSOK in power safe (no halt) mode, timeout is set to
 * 240000 by default, which takes 20ms when 12MHz clock is used.
 *
 * \param bpm  Base address of the BPM instance.
 * \param ps_value  Power scaling value, see \ref power_scaling_mode_value.
 *
 * \param no_halt   No halt or Fail safe, see \c bpm_power_scaling_cpu()
 *                  and bpm_power_scaling_cpu_failsafe()
 * \return true if no error.
 */
__always_inline static
bool bpm_configure_power_scaling(Bpm *bpm, uint32_t ps_value, uint32_t no_halt)
{
	if (!no_halt) {
		bpm_power_scaling_cpu(bpm, ps_value);
		return true;
	}

	return bpm_power_scaling_cpu_failsafe(bpm, ps_value, 240000);
}

/**
 * \brief Enable fast wakeup for analog modules.
 *
 * \param bpm  Base address of the BPM instance.
 */
void bpm_enable_fast_wakeup(Bpm *bpm);

/**
 * \brief Disable fast wakeup for analog modules.
 *
 * \param bpm  Base address of the BPM instance.
 */
void bpm_disable_fast_wakeup(Bpm *bpm);

/**
 * \brief Set clock source for 32KHz clock.
 *
 * \param bpm  Base address of the BPM instance.
 * \param source  Clock source, see \ref CLK32_32Khz_1Khz.
 */
void bpm_set_clk32_source(Bpm *bpm, uint32_t source);

/**
 * \brief Get wakeup cause from backup mode.
 *
 * \param bpm  Base address of the BPM instance.
 */
uint32_t bpm_get_backup_wakeup_cause(Bpm *bpm);

/**
 * \brief Enable wakeup source.
 *
 * \param bpm  Base address of the BPM instance.
 * \param sources  Wakeup source mask, see \ref backup_wake_up_sources.
 */
void bpm_enable_wakeup_source(Bpm *bpm, uint32_t sources);

/**
 * \brief Disable wakeup source.
 *
 * \param bpm  Base address of the BPM instance.
 * \param sources  Wakeup source mask, see \ref backup_wake_up_sources.
 */
void bpm_disable_wakeup_source(Bpm *bpm, uint32_t sources);

/**
 * \brief Enable backup pin for wakeup.
 *
 * \param bpm  Base address of the BPM instance.
 * \param backup_pins  Backup pin mask, see \ref backup_pin_muxing.
 */
void bpm_enable_backup_pin(Bpm *bpm, uint32_t backup_pins);

/**
 * \brief Disable backup pin for wakeup.
 *
 * \param bpm  Base address of the BPM instance.
 * \param backup_pins  Backup pin mask, see \ref backup_pin_muxing.
 */
void bpm_disable_backup_pin(Bpm *bpm, uint32_t backup_pins);

/**
 * \brief Enable IO retention for backup mode.
 *
 * \param bpm  Base address of the BPM instance.
 */
void bpm_enable_io_retention(Bpm *bpm);

/**
 * \brief Disable IO retention for backup mode.
 *
 * \param bpm  Base address of the BPM instance.
 */
void bpm_disable_io_retention(Bpm *bpm);
/* @} */

/**
 * \name Interrupt and status management
 */
/* @{ */

/**
 * \brief Enable interrupt with given sources mask.
 *
 * \param bpm  Base address of the BPM instance.
 * \param sources BPM interrupt source mask.
 */
void bpm_enable_interrupt(Bpm *bpm, uint32_t sources);

/**
 * \brief Disable interrupt with given sources mask.
 *
 * \param bpm  Base address of the BPM instance.
 * \param sources BPM interrupt source mask.
 */
void bpm_disable_interrupt(Bpm *bpm, uint32_t sources);

/**
 * \brief Get BPM interrupt mask.
 *
 * \param bpm  Base address of the BPM instance.
 *
 * \return BPM interrupt mask.
 */
uint32_t bpm_get_interrupt_mask(Bpm *bpm);

/**
 * \brief Get BPM interrupt status.
 *
 * \param bpm  Base address of the BPM instance.
 *
 * \return BPM interrupt status.
 */
uint32_t bpm_get_interrupt_status(Bpm *bpm);

/**
 * \brief Clear BPM interrupt.
 *
 * \param bpm  Base address of the BPM instance.
 * \param sources BPM interrupt source mask.
 */
void bpm_clear_interrupt(Bpm *bpm, uint32_t sources);

/**
 * \brief Get BPM status.
 *
 * \param bpm  Base address of the BPM instance.
 *
 * \return BPM status.
 */
uint32_t bpm_get_status(Bpm *bpm);

/**
 * \brief Get version of BPM module.
 *
 * \param bpm  Base address of the BPM instance.
 *
 * \return Version of BPM module.
 */
uint32_t bpm_get_version(Bpm *bpm);
/* @} */

/* @} */
#ifdef __cplusplus
}
#endif

/**
 * \page sam_bpm_quickstart Quick start guide for the SAM BPM module
 *
 * This is the quick start guide for the
 * \ref group_sam_drivers_bpm "BPM Module", with step-by-step instructions on
 * how to configure and use the driver in a selection of use cases.
 *
 * The use cases contain several code fragments. The code fragments in the
 * steps for setup can be copied into a custom initialization function, while
 * the steps for usage can be copied into, e.g., the main application function.
 *
 * \section bpm_use_cases BPM use cases
 * - \ref bpm_use_case_1 Basic use case - Entering Sleep Modes
 * - \ref bpm_use_case_2 Advanced use case - Switch Power Scaling Modes
 *
 * \section bpm_use_case_1 Basic use case - Entering Sleep Modes
 * In this use case, the BPM module can put system into different power saving
 * modes. Check the current of the system to see consumptions.
 *
 * \section bpm_use_case_1_setup Setup
 *
 * \subsection bpm_use_case_1_setup_prereq Prerequisites
 * Sleep mode itself does not require any IO input, but to wakeup an interrupt
 * is needed.
 * -# \ref ioport_group "Common IOPORT (for GPIO)"
 * -# \ref sam_drivers_eic_group "External Interrupt Controller (EIC)"
 *
 * \subsection bpm_use_case_1_setup_prereq_code Code
 *
 * \code
 * #define EIC_INT5_ENABLE
 * \endcode
 *
 * The following code needs to be added to the user application, to wakeup
 * system and switch to next power mode.
 * \code
 * static void push_button_eic_handler()
 * {
 *    eic_line_clear_interrupt(EIC, GPIO_PUSH_BUTTON_EIC_LINE);
 * }
 * \endcode
 * \code
 * my_eic_init()
 * {
 *   struct eic_line_config eic_opt={
 *     EIC_MODE_EDGE_TRIGGERED,
 *     EIC_EDGE_FALLING_EDGE,
 *     EIC_LEVEL_LOW_LEVEL,
 *     EIC_FILTER_DISABLED,
 *     EIC_ASYNCH_MODE
 *   };
 *   eic_enable(EIC);
 *   eic_line_set_config(EIC, GPIO_PUSH_BUTTON_EIC_LINE, &eic_opt);
 *   eic_line_set_callback(EIC, GPIO_PUSH_BUTTON_EIC_LINE,
 *     push_button_eic_handler, EIC_5_IRQn, 1);
 *   eic_line_enable(EIC, GPIO_PUSH_BUTTON_EIC_LINE);
 * }
 * \endcode
 *
 * \subsection bpm_use_case_1_setup_prereq_flow Workflow
 * -# Ensure that ioport and eic driver is available.
 * -# Ensure that push button is configured as external interrupt in
 *    conf_board.h:
 *    \code #define CONF_BOARD_EIC \endcode
 * -# Add EIC initialize to application C-file:
 *    \code my_eic_init(); \endcode
 *
 * \section bpm_use_case_1_usage Use case
 *
 * \subsection bpm_use_case_1_usage_code Example code
 * Add to application C-file:
 * \code
 *    // Enable wakeup by EIC
 *    bpm_enable_wakeup_source(BPM, 1 << BPM_BKUPWEN_EIC);
 *    // Enable backup wakeup by Push button EIC line
 *    bpm_enable_backup_pin(BPM, 1 << GPIO_PUSH_BUTTON_EIC_LINE);
 *    // Retain I/O lines after wakeup from backup mode
 *    bpm_enable_io_retention(BPM);
 *    // Enable fast wakeup
 *    bpm_enable_fast_wakeup(BPM);
 *    // Enter wait mode
 *    // critical section when going to sleep
 *    cpu_irq_disable();
 *    bpm_sleep(BPM, BPM_SM_WAIT);
 *    // Enter retention mode
 *    cpu_irq_disable();
 *    bpm_sleep(BPM, BPM_SM_RET);
 *    // Enter backup mode
 *    cpu_irq_disable();
 *    bpm_sleep(BPM, BPM_SM_BACKUP);
 *    while(1);
 * \endcode
 *
 * \subsection bpm_use_case_1_usage_flow Workflow
 * -# Enable wakeup by EIC:
 *    \code
 *      bpm_enable_wakeup_source(BPM, 1 << BPM_BKUPWEN_EIC);
 *      bpm_enable_backup_pin(BPM, 1 << GPIO_PUSH_BUTTON_EIC_LINE);
 *    \endcode
 * -# Setup IO retention:
 *    \code bpm_enable_io_retention(BPM); \endcode
 * -# Setup fast wakeup:
 *    \code bpm_enable_fast_wakeup(BPM); \endcode
 * -# Enter sleep/wait/backup mode:
 *    \code
 *      // critical section when going to sleep
 *      cpu_irq_disable();
 *      bpm_sleep(BPM, BPM_SM_WAIT);
 *    \endcode
 */

/**
 * \page bpm_use_case_2 Advanced use case - Switch Power Scaling Modes
 * In this use case, the BPM module can switch the power scaling modes of the
 * system. Check the current of the system to see consumptions.
 *
 * \section bpm_use_case_2_setup Setup
 * \subsection bpm_use_case_2_setup_prereq Prerequisites
 * Some power scaling modes only work on limited system clock frequency (The
 * maximum CPU frequency under PS1 is 12MHz, other peripherals also have speed
 * limitations), please refer to the electrical characteristics for more
 * details.
 * -# \ref clk_group "Clock management"
 *
 * \subsection bpm_use_case_2_setup_code Code
 * Content of conf_clock.h
 * \code
 * #define CONFIG_SYSCLK_SOURCE        SYSCLK_SRC_RCFAST // Uses Fast RC
 * #define CONFIG_RCFAST_FRANGE        2                 // Fast RC is 12MHz
 * \endcode
 *
 * \subsection bpm_use_case_2_setup_workflow Workflow
 * -# Ensure that conf_clock.h is available and contains the following
 * parameters which configure system clock to 12MHz fast RC:
 * \code
 *   #define CONFIG_SYSCLK_SOURCE        SYSCLK_SRC_RCFAST // Uses Fast RC
 *   #define CONFIG_RCFAST_FRANGE        2                 // Fast RC is 12MHz
 * \endcode
 * -# Initialize system clock with \c sysclk_init().
 *
 * \section bpm_use_case_2_usage Use case
 *
 * \subsection bpm_use_case_2_usage_code Example code
 * Add to application C-file:
 * \code
 * bpm_power_scaling_cpu(BPM, BPM_PMCON_PS(BPM_PS_1));
 * while((bpm_get_status(BPM) & BPM_SR_PSOK) == 0);
 * while(1);
 * \endcode
 *
 * \subsection bpm_use_case_2_usage_workflow Workflow
 * -# Switch the power scaling mode:
 *    \code bpm_power_scaling_cpu(BPM, BPM_PMCON_PS(BPM_PS_1));
 *    \endcode
 * -# Wait power scaling done:
 *    \code while((bpm_get_status(BPM) & BPM_SR_PSOK) == 0); \endcode
 */

#endif /* BPM_H_INCLUDED */
