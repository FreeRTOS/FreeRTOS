/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

#ifndef _ACT_8945A_H_
#define _ACT_8945A_H_

#include <stdint.h>
#include <stdbool.h>

#include "peripherals/twid.h"

/*------------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

enum _act8945a_charge_level
{
	ACT8945A_CHARGE_LEVEL_100MA,
	ACT8945A_CHARGE_LEVEL_450MA,
};

enum _act8945a_interrupt
{
	CHARGE_STATE_OUT_EOC_STATE,
	INPUT_VOLTAGE_OUT_VALID_RANGE,
	BATTERY_TEMPERATURE_OUT_RANGE,
	PRECHARGE_TIME_OUT,
	CHARGE_STATE_INTO_EOC_STATE,
	INPUT_VOLTAGE_INTO_VALID_RANGE,
	BATTERY_TEMPERATURE_INTO_RANGE,
	TOTAL_CHARGE_TIME_OUT,
};

struct _act8945a_desc {
	const struct _pin pin_chglev;
	const struct _pin pin_irq;
	const struct _pin pin_lbo;
};

struct _act8945a {
	struct _twi_desc* twid;
	struct _act8945a_desc desc;

	uint8_t sys0;
	uint8_t apch78;
	uint8_t apch79;
	uint8_t apch7a;
	uint8_t lbo_count;
};

/*------------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

extern bool act8945a_configure(struct _act8945a *act8945a,
		struct _twi_desc *twid);

extern void act8945a_set_charge_level(struct _act8945a *act8945a,
		enum _act8945a_charge_level level);

extern bool act8945a_configure_apch_interrupt(struct _act8945a *act8945a,
		enum _act8945a_interrupt interrupt, bool enable);

extern bool act8945a_disable_all_apch_interrupts(struct _act8945a *act8945a);

// Set the Programmable System Voltage Monitor
// Input: Value in mv from 2300mv to 3800mv
extern bool act8945a_set_system_voltage_detect_threshold(struct _act8945a *act8945a,
		uint16_t threshold);

// System Voltage Level Interrupt Mask. SYSLEV interrupt is masked by default,
// set to 1 to unmask this interrupt.
extern bool act8945a_enable_system_voltage_level_interrupt(
		struct _act8945a *act8945a, bool enable);

extern bool act8945a_set_regulator_voltage(struct _act8945a *act8945a,
		uint8_t reg, uint16_t vout);

extern bool act8945a_enable_regulator(struct _act8945a *act8945a,
		uint8_t reg, bool enable);

// Regulator Fault Mask Control.
// Set bit to 1 enable fault-interrupts, clear bit to 0 to disable fault-interrupts
// Input: regulator (1-7)
bool act8945a_enable_regulator_fault_interrupt(struct _act8945a *act8945a,
		uint8_t reg, bool enable);

extern bool act8945a_get_lbo_pin_state(struct _act8945a *act8945a);

extern void act8945a_display_voltage_settings(struct _act8945a *act8945a);

extern void act8945a_dump_registers(struct _act8945a *act8945a);

extern void act8945a_display_apch_registers(struct _act8945a *act8945a);

extern void act8945a_display_system_registers(struct _act8945a *act8945a);

extern void act8945a_display_charge_state(struct _act8945a *act8945a);

#endif /* _ACT_8945A_H_ */
