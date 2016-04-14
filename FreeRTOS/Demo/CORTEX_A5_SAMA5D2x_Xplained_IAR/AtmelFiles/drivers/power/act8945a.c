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

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"
#include "chip.h"

#include "peripherals/pio.h"
#include "peripherals/pmc.h"
#include "peripherals/flexcom.h"
#include "peripherals/twi.h"
#include "peripherals/twid.h"

#include "power/act8945a.h"

#include "trace.h"

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>

/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

#define STATE_VSEL 1 // HW config DDR3L

// SYS @0x00
union _sys0 {
	struct {
		uint8_t
			trst:       1,  // Reset time out 0->260 1->65ms
			nsysmode:   1,  // response of SYSLEV voltage detector, 1->int 0>shutdown
			nsyslevmsk: 1,  // 1->unmask int
			nsysstat:   1,  // 1 if vsys < syslev voltage threshold
			syslev:     4;  // defines SYSLEV voltage threshold
	} bits;
	uint8_t u8;
};

// SYS @0x01
union _sys1 {
	struct {
		uint8_t
			scratch: 4, // user area to store system status information
			ruf4:    1,
			mstroff: 1, // Set bit to 1 to turn off all regulators
			ruf67:   2;
	} bits;
	uint8_t u8;
};

// REG1 @0x20, REG2 @0x30, REG3 @0x40
union _vset1 {
	struct {
		uint8_t
			vset1:  6,
			ruf_67: 2;
	} bits;
	uint8_t u8;
};

// REG1 @0x21, REG2 @0x31, REG3 @0x41
union _vset2 {
	struct {
		uint8_t
			vset2:  6,
			ruf_67: 2;
	} bits;
	uint8_t u8;
};

// REG1 @0x22, REG2 @0x32, REG3 @0x42
union _ctrl1 {
	struct {
		uint8_t
			ok:      1,
			nfltmsk: 1,
			delay:   3,
			mode:    1,
			phase:   1,
			on:      1;
	} bits;
	uint8_t u8;
};

// REG4 @0x51, REG5 @0x55, REG6 @0x61, REG7 @0x65
union _ctrl2 {
	struct {
		uint8_t
			ok:      1,
			nfltmsk: 1,
			delay:   3,
			lowiq:   1,
			dis:     1,
			on:      1;
	} bits;
	uint8_t u8;
};

union _apch_70 {
	struct {
		uint8_t
			ruf_0:  1,
			ruf_1:  1,
			ruf_2:  1,
			ruf_3:  1,
			ruf_45: 2,
			ruf_67: 2;
	} bits;
	uint8_t u8;
};

union _apch_71 {
	struct {
		uint8_t
			ovpset:  2,
			pretimo: 2,
			tottimo: 2,
			ruf6:    1,
			suschg:  1;
	} bits;
	uint8_t u8;
};

union _apch_78 {
	struct {
		uint8_t
			chgdat:   1,
			indat:    1,
			tempdat:  1,
			timrdat:  1,
			chgstat:  1,
			instat:   1,
			tempstat: 1,
			timrstat: 1;
	} bits;
	uint8_t u8;
};

union _apch_79 {
	struct {
		uint8_t
			chgeocout: 1,
			indis:     1,
			tempout:   1,
			timrpre:   1,
			chgeocin:  1,
			incon:     1,
			tempin:    1,
			timrtot:   1;
	} bits;
	uint8_t u8;
};

union _apch_7a {
	struct {
		uint8_t
			ruf0:     1,
			acinstat: 1,
			ruf32:    2,
			cstate:   2,
			ruf76:    2;
	} bits;
	uint8_t u8;
};

/*----------------------------------------------------------------------------
 *        Constants
 *----------------------------------------------------------------------------*/

/// Slave address
#define ACT8945A_TWI_ADDRESS 0x5B

#define NUM_REGULATORS 7

#define IADDR_SYS0   0x00
#define IADDR_SYS1   0x01
#define IADDR_REG1      0x20
#define IADDR_REG2      0x30
#define IADDR_REG3      0x40
#define IADDR_REG4      0x50
#define IADDR_REG5      0x54
#define IADDR_REG6      0x60
#define IADDR_REG7      0x64
#define IADDR_APCH_70   0x70
#define IADDR_APCH_71   0x71
#define IADDR_APCH_78   0x78
#define IADDR_APCH_79   0x79
#define IADDR_APCH_7A   0x7a

static const uint8_t _iaddr_reg[] = {
	IADDR_REG1, IADDR_REG2, IADDR_REG3, IADDR_REG4,
	IADDR_REG5, IADDR_REG6, IADDR_REG7,
};

static const char* _charging_states[4] = {
	"Suspend/Disable/Fault",
	"End of charge",
	"Fast charge/Top-off",
	"Precondition",
};

struct _reg
{
	const char* name;
	uint8_t iaddr;
};

static const struct _reg _regs[] = {
	{ "SYS0   ", IADDR_SYS0 },
	{ "SYS1   ", IADDR_SYS1 },
	{ "REG1_20", IADDR_REG1 },
	{ "REG1_21", IADDR_REG1 + 1 },
	{ "REG1_22", IADDR_REG1 + 2 },
	{ "REG2_30", IADDR_REG2 },
	{ "REG2_31", IADDR_REG2 + 1 },
	{ "REG2_32", IADDR_REG2 + 2 },
	{ "REG3_40", IADDR_REG3 },
	{ "REG3_41", IADDR_REG3 + 1 },
	{ "REG3_42", IADDR_REG3 + 2 },
	{ "REG4_50", IADDR_REG4 },
	{ "REG4_51", IADDR_REG4 + 1 },
	{ "REG5_54", IADDR_REG5 },
	{ "REG5_55", IADDR_REG5 + 1 },
	{ "REG6_60", IADDR_REG6 },
	{ "REG6_61", IADDR_REG6 + 1 },
	{ "REG7_64", IADDR_REG7 },
	{ "REG7_65", IADDR_REG7 + 1 },
	{ "APCH_70", IADDR_APCH_70 },
	{ "APCH_71", IADDR_APCH_71 },
	{ "APCH_78", IADDR_APCH_78 },
	{ "APCH_79", IADDR_APCH_79 },
	{ "APCH_7A", IADDR_APCH_7A },
};

static const char *_ovp_setting[4] = {
	"6.6V", "7.0V", "7.5V", "8.0V",
} ;

/*------------------------------------------------------------------------------
 *         Local functions
 *----------------------------------------------------------------------------*/

static bool _act8945a_read_reg(struct _act8945a* act8945a, uint32_t iaddr,
		uint8_t* value)
{
	uint32_t status;
	struct _buffer in = {
		.data = value,
		.size = 1
	};
	act8945a->twid->slave_addr = ACT8945A_TWI_ADDRESS;
	act8945a->twid->iaddr = iaddr;
	act8945a->twid->isize = 1;
	status = twid_transfert(act8945a->twid, &in, 0,
			twid_finish_transfert_callback, 0);
	if (status != TWID_SUCCESS)
		return false;
	twid_wait_transfert(act8945a->twid);
	return true;
}

static bool _act8945a_write_reg(struct _act8945a* act8945a, uint32_t iaddr,
		uint8_t value)
{
	uint32_t status;
	struct _buffer out = {
		.data = (uint8_t*)&value,
		.size = 1
	};
	act8945a->twid->slave_addr = ACT8945A_TWI_ADDRESS;
	act8945a->twid->iaddr = iaddr;
	act8945a->twid->isize = 1;
	status = twid_transfert(act8945a->twid, 0, &out,
			twid_finish_transfert_callback, 0);
	if (status != TWID_SUCCESS)
		return false;
	twid_wait_transfert(act8945a->twid);
	return true;
}

static bool _act8945a_update_cached_registers(struct _act8945a *act8945a)
{
	return _act8945a_read_reg(act8945a, IADDR_SYS0, &act8945a->sys0) &&
		_act8945a_read_reg(act8945a, IADDR_APCH_78, &act8945a->apch78) &&
		_act8945a_read_reg(act8945a, IADDR_APCH_79, &act8945a->apch79) &&
		_act8945a_read_reg(act8945a, IADDR_APCH_7A, &act8945a->apch7a);
}

static void _act8945a_irq_handler(uint32_t group, uint32_t status, void* user_arg)
{
	struct _act8945a *act8945a = (struct _act8945a*)user_arg;

	if (status & act8945a->desc.pin_irq.mask) {
		union _sys0 sys0;
		union _apch_78 apch78;
		union _apch_79 apch79;
		union _apch_7a apch7a;

		// save previous values
		sys0.u8 = act8945a->sys0;
		apch78.u8 = act8945a->apch78;
		apch79.u8 = act8945a->apch79;
		apch7a.u8 = act8945a->apch7a;

		// update values
		_act8945a_update_cached_registers(act8945a);

		// show changes
		if (sys0.u8 != act8945a->sys0) {
			trace_debug("PMIC IRQ: SYST0 changed\r\n");
		}
		if (apch78.u8 != act8945a->apch78) {
			if (apch78.bits.chgdat == 0x01)
				trace_debug("PMIC IRQ: charger state machine, END-OF-CHARGE state\r\n");
		}
		if (apch79.u8 != act8945a->apch79) {
			printf("PMIC IRQ: APCH79 changed\r\n");
		}
		if (apch7a.u8 != act8945a->apch7a) {
			trace_debug("PMIC IRQ: %s\r\n", _charging_states[apch7a.bits.cstate]);
		}
	}
}

static void _act8945a_lbo_handler(uint32_t group, uint32_t status, void* user_arg)
{
	struct _act8945a *act8945a = (struct _act8945a*)user_arg;

	if (status & act8945a->desc.pin_lbo.mask) {
		trace_debug("PMIC LBO: Low Battery Output\r\n");
		if(	act8945a->lbo_count++ >= 10)
			pio_disable_it(&act8945a->desc.pin_lbo);
	}
}

// Enable interrupt on nIRQ pin to MPU
static void _act8945a_enable_interrupt_handlers(struct _act8945a *act8945a)
{
	/* Configure PMIC line interrupts. */
	pio_configure_it(&act8945a->desc.pin_irq);
	pio_add_handler_to_group(act8945a->desc.pin_irq.group,
				 act8945a->desc.pin_irq.mask,
				 &_act8945a_irq_handler,
				 act8945a);
	pio_enable_it(&act8945a->desc.pin_irq);

	/* Configure LBO line interrupts. */
	act8945a->lbo_count = 0;
	pio_configure_it(&act8945a->desc.pin_lbo);
	pio_add_handler_to_group(act8945a->desc.pin_lbo.group,
				 act8945a->desc.pin_lbo.mask,
				 &_act8945a_lbo_handler,
				 act8945a);
	pio_enable_it(&act8945a->desc.pin_lbo);
}

static uint16_t _act8945a_convert_voltage_setting(uint8_t setting)
{
	uint8_t mul20, mul53;

	mul20 = (setting & 0x07) >> 0;
	mul53 = (setting & 0x38) >> 3;

	if (setting <= 0x17)
		return (uint16_t)(1000 * (0.6 + (0.2 * mul53) + (0.025 * mul20)));
	else if (setting <= 0x2F)
		return (uint16_t)(1000 * (1.2 + (0.4 * (mul53 - 3)) + (0.050 * mul20)));
	else
		return (uint16_t)(1000 * (2.4 + (0.8 * (mul53 - 6)) + (0.1 * mul20)));
}

/*------------------------------------------------------------------------------
 *         Exported functions
 *----------------------------------------------------------------------------*/

bool act8945a_configure(struct _act8945a *act8945a, struct _twi_desc *twid)
{
	uint8_t data = 0;

	act8945a->twid = twid;
	twid_configure(twid);

	pio_configure(&act8945a->desc.pin_chglev, 1);
	pio_configure(&act8945a->desc.pin_irq, 1);
	pio_configure(&act8945a->desc.pin_lbo, 1);

	if (!_act8945a_read_reg(act8945a, IADDR_SYS0, &data))
		return false;

	/* Set Charge Level */
	act8945a_set_charge_level(act8945a, ACT8945A_CHARGE_LEVEL_450MA);

	/* Set level interrupt */
	act8945a_disable_all_apch_interrupts(act8945a);
	act8945a_configure_apch_interrupt(act8945a, CHARGE_STATE_INTO_EOC_STATE, true);
	act8945a_configure_apch_interrupt(act8945a, CHARGE_STATE_OUT_EOC_STATE, true);
	act8945a_configure_apch_interrupt(act8945a, PRECHARGE_TIME_OUT, true);
	act8945a_configure_apch_interrupt(act8945a, TOTAL_CHARGE_TIME_OUT, true);
	act8945a_enable_system_voltage_level_interrupt(act8945a, true);

	/* Update cached register values */
	if (!_act8945a_update_cached_registers(act8945a))
		return false;

	act8945a_enable_regulator_fault_interrupt(act8945a, 1, true);
	act8945a_enable_regulator_fault_interrupt(act8945a, 5, true);

	/* Enable interrupts */
	_act8945a_enable_interrupt_handlers(act8945a);

	return true;
}

// Charge Current Selection Input
// In USB-Mode: CHGLEV = 1 -> I charge 450mA
//              CHGLEV = 0 -> I charge 100mA
void act8945a_set_charge_level(struct _act8945a *act8945a,
		enum _act8945a_charge_level level)
{
	switch (level) {
	case ACT8945A_CHARGE_LEVEL_100MA:
		pio_clear(&act8945a->desc.pin_chglev);
		trace_debug("Charge Level: 100mA\r\n");
		break;
	case ACT8945A_CHARGE_LEVEL_450MA:
		pio_set(&act8945a->desc.pin_chglev);
		trace_debug("Charge Level: 450mA\r\n");
		break;
	default:
		trace_warning("Invalid charge level requested: %d\r\n",
				(int)level)
		break;
	}
}

// Set or Clear an APCH interrupt
// Set bit to 1 enable interrupt,
// Clear bit to 0 to disable interrupt
bool act8945a_configure_apch_interrupt(struct _act8945a *act8945a,
		enum _act8945a_interrupt interrupt, bool enable)
{
	bool status;
	union _apch_78 apch78;
	union _apch_79 apch79;

	if (!_act8945a_read_reg(act8945a, IADDR_APCH_78, &apch78.u8) ||
		!_act8945a_read_reg(act8945a, IADDR_APCH_79, &apch79.u8))
		return false;

	switch (interrupt)
	{
	// Interrupt generated any time the input supply is disconnected when
	// INSTAT[] bit is set to 1 and the INDIS[] bit is set to 1.
	case INPUT_VOLTAGE_OUT_VALID_RANGE: // Interrupt
		apch78.bits.instat = enable ? 1 : 0;
		apch79.bits.indis = enable ? 1 : 0;
		break;

	// Interrupt generated any time the input supply is connected when
	// INSTAT[] bit is set to 1 and the INCON[] bit is set to 1.
	case INPUT_VOLTAGE_INTO_VALID_RANGE:
		apch78.bits.instat = enable ? 1 : 0;
		apch79.bits.incon = enable ? 1 : 0;
		break;

	// Interrupts based upon the status of the battery temperature.
	// Set the TEMPOUT[] bit to 1 and TEMPSTAT[] bit to 1 to generate
	// an interrupt when battery temperature goes out of the valid
	// temperature range.
	case BATTERY_TEMPERATURE_OUT_RANGE:
		apch78.bits.tempstat = enable ? 1 : 0;
		apch79.bits.tempout = enable ? 1 : 0;
		break;

	// Interrupts based upon the status of the battery temperature.
	// Set the TEMPIN[] bit to 1 and TEMPSTAT[] bit to 1 to generate
	// an interrupt when battery temperature returns to the valid range.
	case BATTERY_TEMPERATURE_INTO_RANGE:
		apch78.bits.tempstat = enable ? 1 : 0;
		apch79.bits.tempin = enable ? 1 : 0;
		break;

	// Interrupt when the charger state machine goes into the
	// END-OF-CHARGE (EOC). Set CHGEOCIN[] bit to 1 and CHGSTAT[] bit
	// to 1 to generate an interrupt when the charger state machine goes
	// into the END-OF-CHARGE (EOC)state.
	case CHARGE_STATE_INTO_EOC_STATE:
		apch78.bits.chgstat = enable ? 1 : 0;
		apch79.bits.chgeocin = enable ? 1 : 0;
		break;

	// Interrupt when the charger state machine exit the
	// END-OF-CHARGE (EOC). Set CHGEOCOUT[] bit to 1 and CHGSTAT[] bit
	// to 1 to generate an interrupt when the charger state machine exits
	// the EOC state.
	case CHARGE_STATE_OUT_EOC_STATE:
		apch78.bits.chgstat = enable ? 1 : 0;
		apch79.bits.chgeocout = enable ? 1 : 0;
		break;

	// Interrupts based upon the status of the charge timers.
	// Set the TIMRPRE[] bit to 1 and TIMRSTAT[] bit to 1 to generate an
	// interrupt when the Precondition Timer expires.
	case PRECHARGE_TIME_OUT:
		apch78.bits.timrstat = enable ? 1 : 0;
		apch79.bits.timrpre = enable ? 1 : 0;
		break;

	// Set the TIMRTOT[] bit to 1 and TIMRSTAT[] bit to 1 to generate an
	// interrupt when the Total-Charge Timer expires.
	case TOTAL_CHARGE_TIME_OUT:
		apch78.bits.timrstat = enable ? 1 : 0;
		apch79.bits.timrtot = enable ? 1 : 0;
		break;

	default:
		trace_warning("Unknown interrupt %d\r\n", interrupt);
		return false;
	}

	// Write configuration to registers
	status = _act8945a_write_reg(act8945a, IADDR_APCH_78, apch78.u8);
	status |= _act8945a_write_reg(act8945a, IADDR_APCH_79, apch79.u8);
	return status;

}

// Disable all interrupt from APCH
bool act8945a_disable_all_apch_interrupts(struct _act8945a *act8945a)
{
	return act8945a_configure_apch_interrupt(act8945a, CHARGE_STATE_OUT_EOC_STATE, false) &&
		act8945a_configure_apch_interrupt(act8945a, INPUT_VOLTAGE_OUT_VALID_RANGE, false) &&
		act8945a_configure_apch_interrupt(act8945a, BATTERY_TEMPERATURE_OUT_RANGE, false) &&
		act8945a_configure_apch_interrupt(act8945a, PRECHARGE_TIME_OUT, false) &&
		act8945a_configure_apch_interrupt(act8945a, CHARGE_STATE_INTO_EOC_STATE, false) &&
		act8945a_configure_apch_interrupt(act8945a, INPUT_VOLTAGE_INTO_VALID_RANGE, false) &&
		act8945a_configure_apch_interrupt(act8945a, BATTERY_TEMPERATURE_INTO_RANGE, false) &&
		act8945a_configure_apch_interrupt(act8945a, TOTAL_CHARGE_TIME_OUT, false);
}

extern bool act8945a_set_system_voltage_detect_threshold(struct _act8945a *act8945a,
		uint16_t threshold)
{
	union _sys0 sys0;

	if (threshold < 2300 || threshold > 3800)
		return false;
	if (!_act8945a_read_reg(act8945a, IADDR_SYS0, &sys0.u8))
		return false;
	sys0.bits.syslev = (threshold - 2300) / 100;
	return _act8945a_write_reg(act8945a, IADDR_SYS0, sys0.u8);
}

bool act8945a_enable_system_voltage_level_interrupt(struct _act8945a *act8945a,
		bool enable)
{
	union _sys0 sys0;

	if (!_act8945a_read_reg(act8945a, IADDR_SYS0, &sys0.u8))
		return false;
	sys0.bits.nsyslevmsk = enable ? 1 : 0;

	sys0.bits.nsysmode = 1; //*************

	return _act8945a_write_reg(act8945a, IADDR_SYS0, sys0.u8);
}

bool act8945a_set_regulator_voltage(struct _act8945a *act8945a,
		uint8_t reg, uint16_t vout)
{
	// minimum is 600mV
	if (vout < 600) {
		trace_warning("Cannot set regulator %d voltage to %dmV, using 600mV instead\r\n", reg, vout);
		vout = 600;
	}
	// maximum is 3900mV
	if (vout > 3900) {
		trace_warning("Cannot set regulator %d voltage to %dmV, using 3900mV instead\r\n", reg, vout);
		vout = 3900;
	}

	// can only set voltage for regulators 4 to 7
	if (reg < 4 || reg > 7) {
		trace_error("Cannot change voltage of regulator %d\r\n", reg);
		return false;
	};

	uint8_t value = 0;
	if (vout < 1200) {
		value = (vout - 600) / 25;
	} else if (vout < 2400) {
		value = 0x18 + (vout - 1200) / 50;
	} else if (vout <= 3900) {
		value = 0x30 + (vout - 2400) / 100;
	}

	uint32_t iaddr = _iaddr_reg[reg - 1];
	return _act8945a_write_reg(act8945a, iaddr, value & 0x3f);
}

bool act8945a_enable_regulator(struct _act8945a *act8945a,
		uint8_t reg, bool enable)
{
	if (reg >= 1 && reg <= 3) {
		union _ctrl1 ctrl1;
		uint32_t iaddr = _iaddr_reg[reg - 1] + 1;

		if (!_act8945a_read_reg(act8945a, iaddr, &ctrl1.u8))
			return false;

		ctrl1.bits.on = enable ? 1 : 0;

		if (!_act8945a_write_reg(act8945a, iaddr, ctrl1.u8))
			return false;
	} else if (reg >= 4 && reg <= 7) {
		union _ctrl2 ctrl2;
		uint32_t iaddr = _iaddr_reg[reg - 1] + 1;

		if (!_act8945a_read_reg(act8945a, iaddr, &ctrl2.u8))
			return false;

		ctrl2.bits.on = enable ? 1 : 0;

		if (!_act8945a_write_reg(act8945a, iaddr, ctrl2.u8))
			return false;
	} else {
		trace_error("Invalid regulator number %d\r\n", reg);
		return false;
	}

	return true;
}

bool act8945a_enable_regulator_fault_interrupt(struct _act8945a *act8945a,
		uint8_t reg, bool enable)
{
	if (reg >= 1 && reg <= 3) {
		union _ctrl1 ctrl1;
		uint8_t iaddr = (_iaddr_reg[reg-1]) + 2;


		if (!_act8945a_read_reg(act8945a, iaddr, &ctrl1.u8))
			return false;

		ctrl1.bits.nfltmsk = enable ? 1 : 0;

		if (!_act8945a_write_reg(act8945a, iaddr, ctrl1.u8))
			return false;
	} else if (reg >= 4 && reg <= 7) {
		union _ctrl2 ctrl2;
		uint8_t iaddr = (_iaddr_reg[reg-1]) + 1;

		if (!_act8945a_read_reg(act8945a, iaddr, &ctrl2.u8))
			return false;

		ctrl2.bits.nfltmsk = enable ? 1 : 0;

		if (!_act8945a_write_reg(act8945a, iaddr, ctrl2.u8))
			return false;
	} else {
		trace_error("Invalid regulator number %d\r\n", reg);
		return false;
	}

	return true;
}

extern bool act8945a_get_lbo_pin_state(struct _act8945a *act8945a)
{
	return pio_get(&act8945a->desc.pin_lbo) ? true : false;
}



extern void act8945a_display_voltage_settings(struct _act8945a *act8945a)
{
	int reg;

	trace_info_wp("\r\n-- ACT8945A - Voltage Settings & State --\r\n");

	for (reg = 0; reg < NUM_REGULATORS; reg++)
	{
		uint8_t iadd_reg, setting, ctrl;
		uint16_t u;

		/* Warning VSEL state */
		iadd_reg = _iaddr_reg[reg];
		if( (iadd_reg < IADDR_REG4) && (STATE_VSEL == 1) )
			iadd_reg ++;

		if (!_act8945a_read_reg(act8945a, iadd_reg, &setting))
			return;

		if (!_act8945a_read_reg(act8945a, iadd_reg + 1, &ctrl))
			return;

		u = _act8945a_convert_voltage_setting(setting);
		trace_info_wp(" - VOUT_%d (0x%02x) = %dmV", reg + 1, ctrl, u);
		if (reg <= 3) {
			union _ctrl1 *ctrl1 = (union _ctrl1*)&ctrl;
			trace_info_wp(" %s", ctrl1->bits.on ? "on" : "off");
			trace_info_wp(" %s", ctrl1->bits.phase ? "180" : "osc");
			trace_info_wp(" %s", ctrl1->bits.mode ? "pwm" : "pow-saving");
			trace_info_wp(" delay:0x%02x", ctrl1->bits.delay);
			trace_info_wp(" %s", ctrl1->bits.nfltmsk ? "en" : "dis");
			trace_info_wp(" %s", ctrl1->bits.ok ? "OK" : "<tresh");
		} else {
			union _ctrl2 *ctrl2 = (union _ctrl2*)&ctrl;
			trace_info_wp(" %s", ctrl2->bits.on ? "on": "off");
			trace_info_wp(" %s", ctrl2->bits.dis ? "off" : "on");
			trace_info_wp(" %s", ctrl2->bits.lowiq ? "normal" : "low-power");
			trace_info_wp(" delay:0x%02x", ctrl2->bits.delay);
			trace_info_wp(" %s", ctrl2->bits.nfltmsk ? "en" : "dis");
			trace_info_wp(" %s", ctrl2->bits.ok ? "OK" : "<tresh");
		}
		trace_info_wp("\r\n");
	}

	union _sys0 sys0;
	if (!_act8945a_read_reg(act8945a, IADDR_SYS0, &sys0.u8))
		return;
	trace_info_wp(" - SYSLEV Failing Treshold (0x%02x) = %dmV\r\n", sys0.u8,
			2300 + sys0.bits.syslev * 100);
}

void act8945a_dump_registers(struct _act8945a *act8945a)
{
	uint8_t reg, data, mask, i;


	trace_info_wp("\r\n-- ACT8945A - Registers Dump --\r\n");
	for (reg = 0; reg < ARRAY_SIZE(_regs); reg++) {
		if (!_act8945a_read_reg(act8945a, _regs[reg].iaddr, &data))
			return;
		trace_info_wp(" - %s: 0x%02X  b:", _regs[reg].name, data);
		mask = 0x80;
		for (i=0; i<8; i++, mask>>=1) {
			printf ("%x", (data&mask) ? 1 : 0);
		}
		trace_info_wp("\r\n");
	}
	trace_info_wp("\r\n");
}

void act8945a_display_apch_registers(struct _act8945a *act8945a)
{
	union _apch_71 apch71;
	union _apch_78 apch78;
	union _apch_79 apch79;
	union _apch_7a apch7a;

	trace_info_wp("\r\n-- ACT8945A - APCH Registers --\r\n");

//	if (!_act8945a_read_reg(act8945a, IADDR_APCH_70, &data))
//		return;
//	trace_info_wp(" - APCH @0x70: 0x%02x (reserved)\r\n", data);

	if (!_act8945a_read_reg(act8945a, IADDR_APCH_71, &apch71.u8))
		return;
	trace_info_wp(" - APCH @0x71: 0x%02x\r\n", apch71.u8);
	trace_info_wp("     Charge Suspend Control Input:          %x\r\n",
			apch71.bits.suschg);
	trace_info_wp("     Total Charge Time-out Selection:       %x\r\n",
			apch71.bits.tottimo);
	trace_info_wp("     Precondition Charge Time-out Sel:      %x\r\n",
			apch71.bits.pretimo);
	trace_info_wp("     Input Over-Volt Prot.Threshold Sel:    %x (%s)\r\n",
			apch71.bits.ovpset, _ovp_setting[apch71.bits.ovpset]);

	if (!_act8945a_read_reg(act8945a, IADDR_APCH_78, &apch78.u8))
		return;
	trace_info_wp(" - APCH @0x78: 0x%02x\r\n", apch78.u8);
	trace_info_wp("     Charge Time-out Interrupt Status:      %x\r\n",
			apch78.bits.timrstat);
	trace_info_wp("     Battery Temperature Interrupt Status:  %x\r\n",
			apch78.bits.tempstat);
	trace_info_wp("     Input Voltage Interrupt Status:        %x\r\n",
			apch78.bits.instat);
	trace_info_wp("     Charge State Interrupt Status:         %x\r\n",
			apch78.bits.chgstat);
	trace_info_wp("     Charge Timer Status                    %x\r\n",
			apch78.bits.timrdat);
	trace_info_wp("     Temperature Status                     %x\r\n",
			apch78.bits.tempdat);
	trace_info_wp("     Input Voltage Status                   %x\r\n",
			apch78.bits.indat);
	trace_info_wp("     Charge State Machine Status            %x\r\n",
			apch78.bits.chgdat);

	if (!_act8945a_read_reg(act8945a, IADDR_APCH_79, &apch79.u8))
		return;
	trace_info_wp(" - APCH @0x79: 0x%02x\r\n", apch79.u8);
	trace_info_wp("     Total Charge Time-out Int Control:     %x\r\n",
			apch79.bits.timrtot);
	trace_info_wp("     Batt.Temp.Int.Ctrl into valid range:   %x\r\n",
			apch79.bits.tempin);
	trace_info_wp("     Inp.Voltage Int.Ctrl into valid range: %x\r\n",
			apch79.bits.incon);
	trace_info_wp("     Charge State Int Ctrl into EOC state:  %x\r\n",
			apch79.bits.chgeocin);
	trace_info_wp("     Precharge Time-out Int Ctrl:           %x\r\n",
			apch79.bits.timrpre);
	trace_info_wp("     Batt.Temp.Int.Ctrl. out valid range:   %x\r\n",
			apch79.bits.tempout);
	trace_info_wp("     Inp.Voltage Int.Ctrl. out valid range: %x\r\n",
			apch79.bits.indis);
	trace_info_wp("     Charge State Int.Ctrl. out EOC state:  %x\r\n",
			apch79.bits.chgeocout);

	if (!_act8945a_read_reg(act8945a, IADDR_APCH_7A, &apch7a.u8))
		return;
	trace_info_wp(" - APCH @0x7a: 0x%02x\r\n", apch7a.u8);
	trace_info_wp("     Charge State:                          %x (%s)\r\n",
			apch7a.bits.cstate, _charging_states[apch7a.bits.cstate]);
	trace_info_wp("     ACIN Status:                           %x\r\n",
			apch7a.bits.acinstat);
}

void act8945a_display_system_registers(struct _act8945a *act8945a)
{
	union _sys0 sys0;
	union _sys1 sys1;

	trace_info_wp("\r\n-- ACT8945A - System Registers --\r\n");

	if (!_act8945a_read_reg(act8945a, IADDR_SYS0, &sys0.u8))
		return;
	trace_info_wp(" - SYS0 @0x00: 0x%02x\r\n", sys0.u8);
	trace_info_wp("     Reset Timer Setting:                   %s\r\n",
			sys0.bits.trst ? "64ms" : "260ms");
	trace_info_wp("     SYSLEV Mode Select:                    %s\r\n",
			sys0.bits.nsysmode ?"int" : "shutdown");
	trace_info_wp("     System Voltage Level Int.Mask:         %s\r\n",
			sys0.bits.nsyslevmsk ?"int" : "noint");
	trace_info_wp("     System Voltage Status:                 %s\r\n",
			sys0.bits.nsysstat ? "vsys<syslev" : "vsys>syslev");
	trace_info_wp("     SYSLEV Failing Treshold value:         %dmV\r\n",
			2300 + sys0.bits.syslev * 100);

	if (!_act8945a_read_reg(act8945a, IADDR_SYS1, &sys1.u8))
		return;
	trace_info_wp(" - SYS1 @0x01: 0x%02x\r\n", sys1.u8);
	trace_info_wp("     Master Off Ctrl, All regul:            %s\r\n",
			sys1.bits.mstroff ? "off" : "on");
	trace_info_wp("     Scratchpad Bits, free user:            %x\r\n",
			sys1.bits.scratch);
}

void act8945a_display_charge_state(struct _act8945a *act8945a)
{
	union _apch_7a apch7a;
	if (!_act8945a_read_reg(act8945a, IADDR_APCH_7A, &apch7a.u8)) return;

	if (act8945a->apch7a != apch7a.u8) {
		trace_info_wp(" Charge State: %x (%s)\r\n", apch7a.bits.cstate, _charging_states[apch7a.bits.cstate]);
		act8945a->apch7a = apch7a.u8;
	}
}