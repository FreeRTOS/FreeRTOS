/*******************************************************************************
 * (c) Copyright 2016-2018 Microsemi SoC Products Group. All rights reserved.
 *
 * @file riscv_hal.h
 * @author Microsemi SoC Products Group
 * @brief Hardware Abstraction Layer functions for Mi-V soft processors
 *
 * SVN $Revision: 9835 $
 * SVN $Date: 2018-03-19 19:11:35 +0530 (Mon, 19 Mar 2018) $
 */

#ifndef RISCV_HAL_H
#define RISCV_HAL_H

#include "riscv_plic.h"

#ifdef __cplusplus
extern "C" {
#endif

/*
 *Return value from External IRQ handler. This will be used to disable the External
 *interrupt.
 */
#define EXT_IRQ_KEEP_ENABLED                0U
#define EXT_IRQ_DISABLE                     1U

/*------------------------------------------------------------------------------
 * Interrupt enable/disable.
 */
void __disable_irq(void);
void __enable_irq(void);

/*------------------------------------------------------------------------------
 *  System tick handler. This is generated from the RISC-V machine timer.
 */
void SysTick_Handler(void);

/*------------------------------------------------------------------------------
 * System tick configuration.
 * Configures the machine timer to generate a system tick interrupt at regular
 * intervals.
 * Takes the number of system clock ticks between interrupts.
 *
 * Returns 0 if successful.
 * Returns 1 if the interrupt interval cannot be achieved.
 */
uint32_t SysTick_Config(uint32_t ticks);

#ifdef __cplusplus
}
#endif

#endif  /* RISCV_HAL_H */

