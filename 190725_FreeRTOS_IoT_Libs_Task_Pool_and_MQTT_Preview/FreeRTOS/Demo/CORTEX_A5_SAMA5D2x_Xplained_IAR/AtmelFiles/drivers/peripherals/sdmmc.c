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

/** \addtogroup sdmmc_module Working with Multi Media Cards and
 * Secure Digital Memory Cards
 * \ingroup peripherals_module
 * The SDMMC driver provides the interface to configure and use
 * the SDMMC peripheral.
 * \n
 *
 * For more accurate information, please look at the SDMMC
 * section of the Datasheet.
 *
 * Related files:\n
 * \ref sdmmc.c\n
 * \ref sdmmc.h\n
 */
/*@{*/
/*@}*/
/**
 * \file
 *
 * Driver for MMC and SD Cards using the SDMMC IP.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"
#include "trace.h"
#include "intmath.h"
#include "timer.h"
#include "peripherals/pmc.h"
#include "peripherals/tc.h"
#include "peripherals/l2cc.h"
#include "peripherals/sdmmc.h"
#include "libsdmmc/sdmmc_hal.h"
#include "libsdmmc/sdmmc_api.h"   /* Included for debug functions only */

#include <assert.h>
#include <string.h>

/*----------------------------------------------------------------------------
 *        Local definitions
 *----------------------------------------------------------------------------*/

/** Device status */
#define STAT_ADDRESS_OUT_OF_RANGE     (1UL << 31)
#define STAT_ADDRESS_MISALIGN         (1UL << 30)
#define STAT_BLOCK_LEN_ERROR          (1UL << 29)
#define STAT_ERASE_SEQ_ERROR          (1UL << 28)
#define STAT_ERASE_PARAM              (1UL << 27)
#define STAT_WP_VIOLATION             (1UL << 26)
#define STAT_DEVICE_IS_LOCKED         (1UL << 25)
#define STAT_LOCK_UNLOCK_FAILED       (1UL << 24)
#define STAT_COM_CRC_ERROR            (1UL << 23)
#define STAT_ILLEGAL_COMMAND          (1UL << 22)
#define STAT_DEVICE_ECC_FAILED        (1UL << 21)
#define STAT_CC_ERROR                 (1UL << 20)
#define STAT_ERROR                    (1UL << 19)
#define STAT_CID_OVERWRITE            (1UL << 16)
#define STAT_ERASE_SKIP               (1UL << 15)
#define STAT_CARD_ECC_DISABLED        (1UL << 14)
#define STAT_ERASE_RESET              (1UL << 13)
#define STAT_CURRENT_STATE            (0xfUL << 9)
#define STAT_READY_FOR_DATA           (1UL << 8)
#define STAT_SWITCH_ERROR             (1UL << 7)
#define STAT_EXCEPTION_EVENT          (1UL << 6)
#define STAT_APP_CMD                  (1UL << 5)

/** Device state */
#define STATE_TRANSFER                0x4
#define STATE_SENDING_DATA            0x5
#define STATE_RECEIVE_DATA            0x6
#define STATE_PROGRAMMING             0x7

/** Driver state */
#define MCID_OFF    0	    /**< Device not powered */
#define MCID_IDLE   1	    /**< Idle */
#define MCID_LOCKED 2	    /**< Locked for specific slot */
#define MCID_CMD    3	    /**< Processing the command */
#define MCID_ERROR  4	    /**< Command error */

/** A software event, never raised by the hardware, specific to this driver */
#define SDMMC_NISTR_CUSTOM_EVT        (0x1u << 13)

union uint32_u {
	uint32_t word;
	uint8_t bytes[4];
};

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

static uint32_t sdmmc_send_command(void *set, sSdmmcCommand *cmd);
static uint8_t sdmmc_cancel_command(struct sdmmc_set *set);

static void sdmmc_reset_peripheral(struct sdmmc_set *set)
{
	assert(set);

	Sdmmc *regs = set->regs;
	uint8_t mc1r, tcr;

	/* First, save the few settings we'll want to restore. */
	mc1r = regs->SDMMC_MC1R;
	tcr = regs->SDMMC_TCR;

	/* Reset the peripheral. This will reset almost all registers. */
	regs->SDMMC_SRR |= SDMMC_SRR_SWRSTALL;
	while (regs->SDMMC_SRR & SDMMC_SRR_SWRSTALL) ;

	/* Restore specific register fields */
	if (mc1r & SDMMC_MC1R_FCD)
		regs->SDMMC_MC1R |= SDMMC_MC1R_FCD;
	regs->SDMMC_TCR = (regs->SDMMC_TCR & ~SDMMC_TCR_DTCVAL_Msk)
	    | (tcr & SDMMC_TCR_DTCVAL_Msk);

	/* Apply our unconditional custom settings */
	/* When using DMA, use the 32-bit Advanced DMA 2 mode */
	regs->SDMMC_HC1R = (regs->SDMMC_HC1R & ~SDMMC_HC1R_DMASEL_Msk)
	    | SDMMC_HC1R_DMASEL_ADMA32;
	/* Configure maximum AHB burst size */
	regs->SDMMC_ACR = (regs->SDMMC_ACR & ~SDMMC_ACR_BMAX_Msk)
	    | SDMMC_ACR_BMAX_INCR16;
}

static void sdmmc_power_device(struct sdmmc_set *set, bool on)
{
	assert(set);

	Sdmmc *regs = set->regs;
	uint32_t timer_res_prv, usec = 0;
	uint8_t mc1r;

	if ((on && set->state != MCID_OFF) || (!on && set->state == MCID_OFF))
		return;
	if (on) {
		trace_debug("Power the device on\n\r");
		/* Power the signals to/from the device */
		regs->SDMMC_PCR |= SDMMC_PCR_SDBPWR;
		set->state = MCID_IDLE;
		return;
	}
	trace_debug("Release and power the device off\n\r");
	if (set->state == MCID_CMD)
		sdmmc_cancel_command(set);

	/* Hardware-reset the e.MMC, move it to the pre-idle state.
	 * Note that this will only be effective on systems where
	 * 1) the RST_n e.MMC input is wired to the SDMMCx_RSTN PIO, and
	 * 2) the hardware reset functionality of the device has been
	 *    enabled by software (!) Refer to ECSD register byte 162. */
	timer_res_prv = timer_get_resolution();
	/* Generate a pulse on SDMMCx_RSTN. Satisfy tRSTW >= 1 usec.
	 * The timer driver can't cope with periodic interrupts triggered as
	 * frequently as one interrupt per microsecond. Extend to 10 usec. */
	timer_configure(10);
	mc1r = regs->SDMMC_MC1R;
	regs->SDMMC_MC1R = mc1r | SDMMC_MC1R_RSTN;
	timer_sleep(1);
	regs->SDMMC_MC1R = mc1r;
	/* Wait for either tRSCA = 200 usec or 74 device clock cycles, as per
	 * the e.MMC Electrical Standard. */
	if (set->dev_freq != 0)
		usec = ROUND_INT_DIV(74 * 1000000UL / 10UL, set->dev_freq);
	usec = usec < 20 ? 20 : usec;
	timer_sleep(usec);
	timer_configure(timer_res_prv);

	/* Stop both the output clock and the SDMMC internal clock */
	regs->SDMMC_CCR &= ~(SDMMC_CCR_SDCLKEN | SDMMC_CCR_INTCLKEN);
	set->dev_freq = 0;
	/* Cut the power rail supplying signals to/from the device */
	regs->SDMMC_PCR &= ~SDMMC_PCR_SDBPWR;
	/* Reset the peripheral. This will reset almost all registers. */
	sdmmc_reset_peripheral(set);

	set->state = MCID_OFF;
}

static uint8_t sdmmc_get_bus_width(struct sdmmc_set *set)
{
	assert(set);

	const uint8_t hc1r = set->regs->SDMMC_HC1R;

	if (hc1r & SDMMC_HC1R_EXTDW)
		return 8;
	else if (hc1r & SDMMC_HC1R_DW)
		return 4;
	else
		return 1;
}

static uint8_t sdmmc_set_bus_width(struct sdmmc_set *set, uint8_t bits)
{
	assert(set);

	Sdmmc *regs = set->regs;
	uint8_t hc1r_prv, hc1r;

	if (bits != 1 && bits != 4 && bits != 8)
		return SDMMC_PARAM;
	if (bits == 8 && !(regs->SDMMC_CA0R & SDMMC_CA0R_ED8SUP)) {
		trace_error("This slot doesn't support an 8-bit data bus\n\r");
		return SDMMC_PARAM;
	}

	hc1r = hc1r_prv = regs->SDMMC_HC1R;
	if (bits == 8 && hc1r & SDMMC_HC1R_EXTDW)
		return SDMMC_OK;
	else if (bits == 8)
		hc1r |= SDMMC_HC1R_EXTDW;
	else {
		hc1r &= ~SDMMC_HC1R_EXTDW;
		if (bits == 4)
			hc1r |= SDMMC_HC1R_DW;
		else
			hc1r &= ~SDMMC_HC1R_DW;
		if (hc1r == hc1r_prv)
			return SDMMC_OK;
	}
	regs->SDMMC_HC1R = hc1r;
	return SDMMC_OK;
}

static bool sdmmc_get_speed_mode(struct sdmmc_set *set)
{
	assert(set);

	if (set->regs->SDMMC_MC1R & SDMMC_MC1R_DDR)
		return true;
	if (set->regs->SDMMC_HC1R & SDMMC_HC1R_HSEN)
		return true;
	return false;
}

static uint8_t sdmmc_set_speed_mode(struct sdmmc_set *set, bool high_speed)
{
	assert(set);

	Sdmmc *regs = set->regs;
	uint8_t hc1r, mc1r;
	bool enable_dev_clock;

	if (high_speed && !(regs->SDMMC_CA0R & SDMMC_CA0R_HSSUP)) {
		trace_error("This slot doesn't support High Speed Mode\n\r");
		return SDMMC_PARAM;
	}
#ifndef NDEBUG
	if (high_speed && !(regs->SDMMC_CCR & (SDMMC_CCR_USDCLKFSEL_Msk
	    | SDMMC_CCR_SDCLKFSEL_Msk))) {
		trace_error("Incompatible with the current clock config\n\r");
		return SDMMC_STATE;
	}
#endif
	mc1r = regs->SDMMC_MC1R;
	if (high_speed && mc1r & SDMMC_MC1R_DDR)
		return SDMMC_OK;
	if (!high_speed && mc1r & SDMMC_MC1R_DDR)
		regs->SDMMC_MC1R = mc1r & ~SDMMC_MC1R_DDR;

	hc1r = regs->SDMMC_HC1R;
	if ((hc1r & SDMMC_HC1R_HSEN) == (high_speed ? SDMMC_HC1R_HSEN : 0))
		return SDMMC_OK;
	hc1r ^= SDMMC_HC1R_HSEN;
	/* Avoid generating glitches on the device clock */
	enable_dev_clock = regs->SDMMC_HC2R & SDMMC_HC2R_PVALEN
	    && regs->SDMMC_CCR & SDMMC_CCR_SDCLKEN;
	if (enable_dev_clock)
		regs->SDMMC_CCR &= ~SDMMC_CCR_SDCLKEN;
	/* Now change the Speed Mode */
	regs->SDMMC_HC1R = hc1r;
	if (enable_dev_clock)
		regs->SDMMC_CCR |= SDMMC_CCR_SDCLKEN;
	return SDMMC_OK;
}

static void sdmmc_set_device_clock(struct sdmmc_set *set, uint32_t freq)
{
	assert(set);
	assert(freq);

	Sdmmc *regs = set->regs;
	uint32_t base_freq, div, low_freq, up_freq, new_freq;
	uint32_t mult_freq, p_div, p_mode_freq;
	uint16_t shval;
	bool use_prog_mode = false;

#ifndef NDEBUG
	if (regs->SDMMC_HC2R & SDMMC_HC2R_PVALEN)
		trace_error("Preset values enabled though not implemented\n\r");
#endif
	/* In the Divided Clock Mode scenario, compute the divider */
	base_freq = (regs->SDMMC_CA0R & SDMMC_CA0R_BASECLKF_Msk) >> SDMMC_CA0R_BASECLKF_Pos;
	base_freq *= 1000000UL;
	/* DIV = FBASECLK / (2 * FSDCLK) */
	div = base_freq / (2 * freq);
	if (div >= 0x3ff)
		div = 0x3ff;
	else {
		up_freq = base_freq / (div == 0 ? 1UL : 2 * div);
		low_freq = base_freq / (2 * (div + 1UL));
		if (up_freq > freq && (up_freq - freq) > (freq - low_freq))
			div += 1;
	}
	new_freq = base_freq / (div == 0 ? 1UL : 2 * div);

	/* Now, in the Programmable Clock Mode scenario, compute the divider.
	 * First, retrieve the frequency of the Generated Clock feeding this
	 * peripheral. */
	/* TODO fix CLKMULT value in CA1R capability register: the default value
	 * is 32 whereas the real value is 40.5 */
	mult_freq = (regs->SDMMC_CA1R & SDMMC_CA1R_CLKMULT_Msk) >> SDMMC_CA1R_CLKMULT_Pos;
	if (mult_freq != 0)
#if 0
		mult_freq = base_freq * (mult_freq + 1);
#else
		mult_freq = pmc_get_gck_clock(set->id);
#endif
	if (mult_freq != 0) {
		/* DIV = FMULTCLK / FSDCLK - 1 */
		p_div = ROUND_INT_DIV(mult_freq, freq);
		if (p_div > 0x3ff)
			p_div = 0x3ff;
		else if (p_div != 0)
			p_div = p_div - 1;
		p_mode_freq = mult_freq / (p_div + 1);
		if (ABS_DIFF(freq, p_mode_freq) < ABS_DIFF(freq, new_freq)) {
			use_prog_mode = true;
			div = p_div;
			new_freq = p_mode_freq;
		}
	}

	/* Stop both the output clock and the SDMMC internal clock */
	shval = regs->SDMMC_CCR & ~SDMMC_CCR_SDCLKEN & ~SDMMC_CCR_INTCLKEN;
	regs->SDMMC_CCR = shval;
	set->dev_freq = new_freq;
	/* Select the clock mode */
	if (use_prog_mode)
		shval |= SDMMC_CCR_CLKGSEL;
	else
		shval &= ~SDMMC_CCR_CLKGSEL;
	/* Set the clock divider, and start the SDMMC internal clock */
	shval = (shval & ~SDMMC_CCR_USDCLKFSEL_Msk & ~SDMMC_CCR_SDCLKFSEL_Msk)
	    | SDMMC_CCR_USDCLKFSEL(div >> 8) | SDMMC_CCR_SDCLKFSEL(div & 0xff)
	    | SDMMC_CCR_INTCLKEN;
	regs->SDMMC_CCR = shval;
	while (!(regs->SDMMC_CCR & SDMMC_CCR_INTCLKS)) ;
	/* Now start the output clock */
	regs->SDMMC_CCR |= SDMMC_CCR_SDCLKEN;
}

static uint8_t sdmmc_build_dma_table(struct sdmmc_set *set, sSdmmcCommand *cmd)
{
	assert(set);
	assert(set->table);
	assert(set->table_size);
	assert(cmd->pData);
	assert(cmd->wBlockSize);
	assert(cmd->wNbBlocks);

	uint32_t *line = NULL;
	uint32_t data_len = (uint32_t)cmd->wNbBlocks
	    * (uint32_t)cmd->wBlockSize;
	uint32_t ram_addr = (uint32_t)cmd->pData;
	uint32_t ram_bound = ram_addr + data_len;
	uint32_t line_ix, line_cnt;
	uint8_t rc = SDMMC_OK;

#if 0 && !defined(NDEBUG)
	trace_debug("Configuring DMA for a %luB transfer %s %p\n\r",
	    data_len, cmd->cmdOp.bmBits.xfrData == SDMMC_CMD_TX ? "from" : "to",
	    cmd->pData);
#endif
	/* Verify that cmd->pData is word-aligned */
	if ((uint32_t)cmd->pData & 0x3)
		return SDMMC_PARAM;
	/* Compute the size of the descriptor table for this transfer */
	line_cnt = (data_len - 1 + SDMMC_DMADL_TRAN_LEN_MAX)
	    / SDMMC_DMADL_TRAN_LEN_MAX;
	/* If it won't fit into the allocated buffer, resize the transfer */
	if (line_cnt > set->table_size) {
		line_cnt = set->table_size;
		data_len = line_cnt * SDMMC_DMADL_TRAN_LEN_MAX;
		data_len /= cmd->wBlockSize;
		if (data_len == 0)
			return SDMMC_NOT_SUPPORTED;
		cmd->wNbBlocks = (uint16_t)data_len;
		data_len *= cmd->wBlockSize;
		ram_bound = ram_addr + data_len;
		rc = SDMMC_CHANGED;
	}
	/* Fill the table */
	for (line_ix = 0, line = set->table; line_ix < line_cnt;
	    line_ix++, line += SDMMC_DMADL_SIZE) {
		if (line_ix + 1 < line_cnt) {
			line[0] = SDMMC_DMA0DL_LEN_MAX
			    | SDMMC_DMA0DL_ATTR_ACT_TRAN
			    | SDMMC_DMA0DL_ATTR_VALID;
			line[1] = SDMMC_DMA1DL_ADDR(ram_addr);
			ram_addr += SDMMC_DMADL_TRAN_LEN_MAX;
		}
		else {
			line[0] = ram_bound - ram_addr
			    < SDMMC_DMADL_TRAN_LEN_MAX
			    ? SDMMC_DMA0DL_LEN(ram_bound - ram_addr)
			    : SDMMC_DMA0DL_LEN_MAX;
			line[0] |= SDMMC_DMA0DL_ATTR_ACT_TRAN
			    | SDMMC_DMA0DL_ATTR_END | SDMMC_DMA0DL_ATTR_VALID;
			line[1] = SDMMC_DMA1DL_ADDR(ram_addr);
		}
#if 0 && !defined(NDEBUG)
		trace_debug("DMA descriptor: %luB @ 0x%lx%c\n\r",
		    (line[0] & SDMMC_DMA0DL_LEN_Msk) >> SDMMC_DMA0DL_LEN_Pos,
		    line[1], line[0] & SDMMC_DMA0DL_ATTR_END ? '.' : ' ');
#endif
	}
	/* Clean the underlying cache lines, to ensure the DMA gets our table
	 * when it reads from RAM.
	 * CPU access to the table is write-only, peripheral/DMA access is read-
	 * only, hence there is no need to invalidate. */
	l2cc_clean_region((uint32_t)set->table, (uint32_t)line);

	return rc;
}

/**
 * \brief Retrieve command response from the SDMMC peripheral.
 * The response may be retrieved once per command.
 */
static void sdmmc_get_response(struct sdmmc_set *set, sSdmmcCommand *cmd,
    bool complete, uint32_t *out)
{
	assert(set);
	assert(cmd);
	assert(cmd->cmdOp.bmBits.respType <= 7);
	assert(out);

	const bool first_call = set->resp_len == 0;
	const bool has_data = cmd->cmdOp.bmBits.xfrData == SDMMC_CMD_TX
	    || cmd->cmdOp.bmBits.xfrData == SDMMC_CMD_RX;
	uint32_t resp;
	uint8_t ix;

	if (first_call) {
		switch (cmd->cmdOp.bmBits.respType) {
		case 2:
			/* R2 response is 120-bit long, split in
			 * 32+32+32+24 bits this way:
			 * RR[0] =    R[ 39:  8]
			 * RR[1] =    R[ 71: 40]
			 * RR[2] =    R[103: 72]
			 * RR[3] =    R[127:104]
			 * Shift data the way libsdmmc expects it,
			 * that is:
			 * pResp[0] = R[127: 96]
			 * pResp[1] = R[ 95: 64]
			 * pResp[2] = R[ 63: 32]
			 * pResp[3] = R[ 31:  0]
			 * The CRC7 and the end bit aren't provided,
			 * just hard-code their default values. */
			out[3] = 0x000000ff;
			for (ix = 0; ix < 4; ix++) {
				resp = set->regs->SDMMC_RR[ix];
				if (ix < 3)
					out[2 - ix] = resp >> 24 & 0xff;
				out[3 - ix] |= resp << 8 & 0xffffff00;
			}
			set->resp_len = 4;
			break;
		case 1: case 3: case 4: case 5: case 6: case 7:
			/* The nominal response is 32-bit long */
			out[0] = set->regs->SDMMC_RR[0];
			set->resp_len = 1;
			break;
		case 0:
		default:
			break;
		}
	}

	if (has_data && (cmd->bCmd == 18 || cmd->bCmd == 25) && ((first_call
	    && set->use_set_blk_cnt) || (complete && !set->use_set_blk_cnt))) {
		resp = set->regs->SDMMC_RR[3];
#if 0 && !defined(NDEBUG)
		trace_debug("Auto CMD%d returned status 0x%lx\n\r",
		    set->use_set_blk_cnt ? 23 : 12, resp);
#endif
		if (!set->use_set_blk_cnt)
			/* We return a single response to the application: the
			 * device status returned by CMD18 or CMD25, combined
			 * with the device status just returned by Auto CMD12.
			 * Retain the status bits from only CMD18 or CMD25, and
			 * combine the exception bits from both. */
			out[0] |= resp & ~STAT_DEVICE_IS_LOCKED
			    & ~STAT_CARD_ECC_DISABLED & ~STAT_CURRENT_STATE
			    & ~STAT_READY_FOR_DATA & ~STAT_EXCEPTION_EVENT
			    & ~STAT_APP_CMD;
#ifndef NDEBUG
		resp = (resp & STAT_CURRENT_STATE) >> 9;
		if (set->use_set_blk_cnt && resp != STATE_TRANSFER)
			trace_warning("Auto CMD23 returned state %lx\n\r", resp)
		else if (!set->use_set_blk_cnt && cmd->bCmd == 18
		    && resp != STATE_SENDING_DATA)
			trace_warning("CMD18 switched to state %lx\n\r", resp)
		else if (!set->use_set_blk_cnt && cmd->bCmd == 25
		    && resp != STATE_RECEIVE_DATA && resp != STATE_PROGRAMMING)
			trace_warning("CMD25 switched to state %lx\n\r", resp)
#endif
	}
}

/**
 * \brief Fetch events from the SDMMC peripheral, handle them, and proceed to
 * the subsequent step, w.r.t. the SD/MMC command being processed.
 * \warning This implementation suits LITTLE ENDIAN hosts only.
 */
static void sdmmc_poll(struct sdmmc_set *set)
{
	assert(set);
	assert(set->state != MCID_OFF);

	Sdmmc *regs = set->regs;
	sSdmmcCommand *cmd = set->cmd;
	uint16_t events, errors, acesr;
	bool has_data;

	if (set->state != MCID_CMD)
		return;
	assert(cmd);
	has_data = cmd->cmdOp.bmBits.xfrData == SDMMC_CMD_TX
	    || cmd->cmdOp.bmBits.xfrData == SDMMC_CMD_RX;

Fetch:
	/* Fetch normal events */
	events = regs->SDMMC_NISTR;
	if (set->expect_auto_end && !(set->timer->TC_SR & TC_SR_CLKSTA))
		events |= SDMMC_NISTR_CUSTOM_EVT;
	if (!events)
		return;

	errors = 0;
	/* Check the global error flag */
	if (events & SDMMC_NISTR_ERRINT) {
		errors = regs->SDMMC_EISTR;
		events &= ~SDMMC_NISTR_ERRINT;
		/* Clear error interrupts */
		regs->SDMMC_EISTR = errors;
		if (errors & SDMMC_EISTR_CURLIM)
			cmd->bStatus = SDMMC_NOT_INITIALIZED;
		else if (errors & SDMMC_EISTR_CMDCRC)
			cmd->bStatus = SDMMC_ERR_IO;
		else if (errors & SDMMC_EISTR_CMDTEO)
			cmd->bStatus = SDMMC_NO_RESPONSE;
		else if (errors & (SDMMC_EISTR_CMDEND | SDMMC_EISTR_CMDIDX))
			cmd->bStatus = SDMMC_ERR_IO;
		/* TODO if SDMMC_NISTR_TRFC and only SDMMC_EISTR_DATTEO then
		 * ignore SDMMC_EISTR_DATTEO */
		else if (errors & SDMMC_EISTR_DATTEO)
			cmd->bStatus = SDMMC_ERR_IO;
		else if (errors & (SDMMC_EISTR_DATCRC | SDMMC_EISTR_DATEND))
			cmd->bStatus = SDMMC_ERR_IO;
		else if (errors & SDMMC_EISTR_ACMD) {
			acesr = regs->SDMMC_ACESR;
			if (acesr & SDMMC_ACESR_ACMD12NE)
				cmd->bStatus = SDMMC_ERR;
			else if (acesr & SDMMC_ACESR_ACMDCRC)
				cmd->bStatus = SDMMC_ERR_IO;
			else if (acesr & SDMMC_ACESR_ACMDTEO)
				cmd->bStatus = SDMMC_NO_RESPONSE;
			else if (acesr & (SDMMC_ACESR_ACMDEND | SDMMC_ACESR_ACMDIDX))
				cmd->bStatus = SDMMC_ERR_IO;
			else
				cmd->bStatus = SDMMC_ERR;
		}
		else if (errors & SDMMC_EISTR_ADMA) {
			cmd->bStatus = SDMMC_PARAM;
			trace_error("ADMA error 0x%x at desc. line[%lu]\n\r",
			    regs->SDMMC_AESR, (regs->SDMMC_ASA0R -
			    (uint32_t)set->table) / (SDMMC_DMADL_SIZE * 4UL));
		}
		else if (errors & SDMMC_EISTR_BOOTAE)
			cmd->bStatus = SDMMC_STATE;
		else
			cmd->bStatus = SDMMC_ERR;
		set->state = cmd->bCmd == 12 ? MCID_LOCKED : MCID_ERROR;
		/* Reset CMD and DAT lines.
		 * Resetting DAT lines also aborts the DMA transfer - if any -
		 * and resets the DMA circuit. */
		regs->SDMMC_SRR |= SDMMC_SRR_SWRSTDAT | SDMMC_SRR_SWRSTCMD;
		while (regs->SDMMC_SRR & (SDMMC_SRR_SWRSTDAT
		    | SDMMC_SRR_SWRSTCMD)) ;
		trace_warning("CMD%u ended with error flags %04x, cmd status "
		    "%s\n\r", cmd->bCmd, errors, SD_StringifyRetCode(cmd->bStatus));
		goto End;
	}

	/* No error. Give priority to the low-latency event that signals the
	 * completion of the Auto CMD12 command, hence of the whole multiple-
	 * block data transfer. */
	if (events & SDMMC_NISTR_CUSTOM_EVT) {
#ifndef NDEBUG
		if (!(set->regs->SDMMC_PSR & SDMMC_PSR_CMDLL))
			trace_warning("Command still ongoing\n\r");
#endif
		if (cmd->pResp)
			sdmmc_get_response(set, cmd, true, cmd->pResp);
		goto Succeed;
	}

	/* First, expect completion of the command */
	if (events & SDMMC_NISTR_CMDC) {
		/* Clear this normal interrupt */
		regs->SDMMC_NISTR = SDMMC_NISTR_CMDC;
		events &= ~SDMMC_NISTR_CMDC;
#ifndef NDEBUG
		if (cmd->cmdOp.bmBits.xfrData == SDMMC_CMD_TX
		    && !set->table && set->blk_index != cmd->wNbBlocks
		    && !(regs->SDMMC_PSR & SDMMC_PSR_WTACT))
			trace_warning("Write transfer not started\n\r")
		else if (cmd->cmdOp.bmBits.xfrData == SDMMC_CMD_RX
		    && !set->table && set->blk_index != cmd->wNbBlocks
		    && !(regs->SDMMC_PSR & SDMMC_PSR_RTACT))
			trace_warning("Read transfer not started\n\r")
#endif
		/* Retrieve command response */
		if (cmd->pResp)
			sdmmc_get_response(set, cmd, false, cmd->pResp);
		if (!has_data && !cmd->cmdOp.bmBits.checkBsy)
			goto Succeed;
	}

	/* Expect the next incoming block of data */
	if (events & SDMMC_NISTR_BRDRDY
	    && cmd->cmdOp.bmBits.xfrData == SDMMC_CMD_RX && !set->table) {
		/* FIXME may be optimized by looping while PSR.BUFRDEN == 1 */
		uint8_t *in, *out, *bound;
		union uint32_u val;
		uint16_t count;

		/* Clear this normal interrupt */
		regs->SDMMC_NISTR = SDMMC_NISTR_BRDRDY;
		events &= ~SDMMC_NISTR_BRDRDY;

		if (set->blk_index >= cmd->wNbBlocks) {
			trace_error("Excess of incoming data\n\r");
			cmd->bStatus = SDMMC_ERR_IO;
			set->state = MCID_ERROR;
			goto End;
		}
		out = cmd->pData + set->blk_index * (uint32_t)cmd->wBlockSize;
		count = cmd->wBlockSize & ~0x3;
		for (bound = out + count; out < bound; out += 4) {
#ifndef NDEBUG
			if (!(regs->SDMMC_PSR & SDMMC_PSR_BUFRDEN))
				trace_error("Unexpected Buffer Read Disable status\n\r");
#endif
			val.word = regs->SDMMC_BDPR;
			out[0] = val.bytes[0];
			out[1] = val.bytes[1];
			out[2] = val.bytes[2];
			out[3] = val.bytes[3];
		}
		if (count < cmd->wBlockSize) {
#ifndef NDEBUG
			if (!(regs->SDMMC_PSR & SDMMC_PSR_BUFRDEN))
				trace_error("Unexpected Buffer Read Disable status\n\r");
#endif
			val.word = regs->SDMMC_BDPR;
			count = cmd->wBlockSize - count;
			for (in = val.bytes, bound = out + count;
			    out < bound; in++, out++)
				*out = *in;
		}
#if 0 && !defined(NDEBUG)
		if (regs->SDMMC_PSR & SDMMC_PSR_BUFRDEN)
			trace_warning("Renewed Buffer Read Enable status\n\r");
#endif
		set->blk_index++;
	}

	/* Expect the Buffer Data Port to be ready to accept the next
	 * outgoing block of data */
	if (events & SDMMC_NISTR_BWRRDY
	    && cmd->cmdOp.bmBits.xfrData == SDMMC_CMD_TX && !set->table
	    && set->blk_index < cmd->wNbBlocks) {
		/* FIXME may be optimized by looping while PSR.BUFWREN == 1 */
		uint8_t *in, *out, *bound;
		union uint32_u val;
		uint16_t count;

		/* Clear this normal interrupt */
		regs->SDMMC_NISTR = SDMMC_NISTR_BWRRDY;
		events &= ~SDMMC_NISTR_BWRRDY;

		in = cmd->pData + set->blk_index * (uint32_t)cmd->wBlockSize;
		count = cmd->wBlockSize & ~0x3;
		for (bound = in + count; in < bound; in += 4) {
			val.bytes[0] = in[0];
			val.bytes[1] = in[1];
			val.bytes[2] = in[2];
			val.bytes[3] = in[3];
#ifndef NDEBUG
			if (!(regs->SDMMC_PSR & SDMMC_PSR_BUFWREN))
				trace_error("Unexpected Buffer Write Disable status\n\r");
#endif
			regs->SDMMC_BDPR = val.word;
		}
		if (count < cmd->wBlockSize) {
			count = cmd->wBlockSize - count;
			for (val.word = 0, out = val.bytes, bound = in + count;
			    in < bound; in++, out++)
				*out = *in;
#ifndef NDEBUG
			if (!(regs->SDMMC_PSR & SDMMC_PSR_BUFWREN))
				trace_error("Unexpected Buffer Write Disable status\n\r");
#endif
			regs->SDMMC_BDPR = val.word;
		}
#if 0 && !defined(NDEBUG)
		if (regs->SDMMC_PSR & SDMMC_PSR_BUFWREN)
			trace_warning("Renewed Buffer Write Enable status\n\r");
#endif
		set->blk_index++;
	}
#ifndef NDEBUG
	else if (events & SDMMC_NISTR_BWRRDY
	    && cmd->cmdOp.bmBits.xfrData == SDMMC_CMD_TX && !set->table
	    && set->blk_index >= cmd->wNbBlocks)
		trace_warning("Excess Buffer Write Ready status\n\r");
#endif

	/* Expect completion of either the data transfer or the busy state. */
	if (events & SDMMC_NISTR_TRFC) {
		/* Deviation from the SD Host Controller Specification:
		 * the Auto CMD12 command/response (when enabled) is still in
		 * progress. We are on our own to figure out when CMD12 will
		 * have completed.
		 * In the meantime:
		 * 1. errors affecting the CMD12 command - essentially
		 *    SDMMC_EISTR_ACMD - have not been detected yet.
		 * 2. SDMMC_RR[3] is not yet valid.
		 * Our workaround here consists in generating a third event
		 * further to Transfer Complete, after a predefined amount of
		 * time, sufficient for CMD12 to complete.
		 * Refer to sdmmc_send_command(), which has prepared our Timer/
		 * Counter for this purpose. */
		if (has_data && (cmd->bCmd == 18 || cmd->bCmd == 25)
		    && !set->use_set_blk_cnt) {
			set->timer->TC_CCR = TC_CCR_CLKEN | TC_CCR_SWTRG;
			set->expect_auto_end = true;
		}
		/* Clear this normal interrupt */
		regs->SDMMC_NISTR = SDMMC_NISTR_TRFC;
		events &= ~SDMMC_NISTR_TRFC;
		/* Deviation from the SD Host Controller Specification:
		 * there are cases, notably CMD7 with address and R1b, where the
		 * Command Complete interrupt does not occur. In such cases,
		 * the command response has not been retrieved yet. */
		if (!set->expect_auto_end && cmd->pResp)
			sdmmc_get_response(set, cmd, true, cmd->pResp);
#ifndef NDEBUG
		if (regs->SDMMC_PSR & SDMMC_PSR_WTACT)
			trace_error("Write transfer still active\n\r");
		if (regs->SDMMC_PSR & SDMMC_PSR_RTACT)
			trace_error("Read transfer still active\n\r");
#endif
		if (has_data && !set->table
		    && set->blk_index != cmd->wNbBlocks) {
			trace_error("Incomplete data transfer\n\r");
			cmd->bStatus = SDMMC_ERR_IO;
			set->state = MCID_ERROR;
			goto End;
		}
		else if (has_data && set->table
		    && cmd->cmdOp.bmBits.xfrData == SDMMC_CMD_RX)
			l2cc_invalidate_region((uint32_t)cmd->pData,
			    (uint32_t)cmd->pData + (uint32_t)cmd->wNbBlocks
			    * (uint32_t)cmd->wBlockSize);
		if (!set->expect_auto_end)
			goto Succeed;
	}

#ifndef NDEBUG
	if (events)
		trace_warning("Unhandled NISTR events: 0x%04x\n\r", events);
#endif
	if (events)
		regs->SDMMC_NISTR = events;
	goto Fetch;

Succeed:
	set->state = MCID_LOCKED;
End:
	/* Clear residual normal interrupts, if any */
	if (events)
		regs->SDMMC_NISTR = events;
#if 0 && !defined(NDEBUG)
	if (set->resp_len == 1)
		trace_debug("CMD%u got response %08lx\n\r", cmd->bCmd,
		    cmd->pResp[0])
	else if (set->resp_len == 4)
		trace_debug("CMD%u got response %08lx %08lx %08lx %08lx\n\r",
		    cmd->bCmd, cmd->pResp[0], cmd->pResp[1], cmd->pResp[2],
		    cmd->pResp[3])
#endif
	/* Release command */
	set->cmd = NULL;
	set->resp_len = 0;
	set->blk_index = 0;
	set->expect_auto_end = false;
	/* Invoke the end-of-command fSdmmcCallback function, if provided */
	if (cmd->fCallback)
		(cmd->fCallback)(cmd->bStatus, cmd->pArg);
}

/**
 * \brief Check if the command is finished.
 */
static bool sdmmc_is_busy(struct sdmmc_set *set)
{
	assert(set->state != MCID_OFF);

	if (set->use_polling)
		sdmmc_poll(set);
	if (set->state == MCID_CMD)
		return true;
	return false;
}

static uint8_t sdmmc_cancel_command(struct sdmmc_set *set)
{
	assert(set);
	assert(set->state != MCID_OFF);

	Sdmmc *regs = set->regs;
	sSdmmcCommand *cmd = set->cmd;
	uint32_t response;   /* The R1 response is 32-bit long */
	uint32_t timer_res_prv, usec, rc;
	sSdmmcCommand stop_cmd = {
		.pResp = &response,
		.cmdOp.wVal = SDMMC_CMD_CSTOP | SDMMC_CMD_bmBUSY,
		.bCmd = 12,
	};

	if (set->state != MCID_CMD && set->state != MCID_ERROR)
		return SDMMC_STATE;
	trace_debug("Requested to cancel CMD%u\n\r", set->cmd ? set->cmd->bCmd : 99);
	if (set->state == MCID_ERROR) {
		set->state = MCID_LOCKED;
		return SDMMC_OK;
	}
	assert(cmd);
	/* Asynchronous Abort, if a data transfer has been started */
	if (cmd->cmdOp.bmBits.xfrData == SDMMC_CMD_TX
	    || cmd->cmdOp.bmBits.xfrData == SDMMC_CMD_RX) {
		/* May the CMD line still be busy, reset it */
		if (regs->SDMMC_PSR & SDMMC_PSR_CMDINHC) {
			regs->SDMMC_SRR |= SDMMC_SRR_SWRSTCMD;
			while (regs->SDMMC_SRR & SDMMC_SRR_SWRSTCMD) ;
		}
		/* Issue the STOP_TRANSMISSION command. */
		set->state = MCID_LOCKED;
		set->cmd = NULL;
		set->resp_len = 0;
		set->blk_index = 0;
		set->expect_auto_end = false;
		rc = sdmmc_send_command(set, &stop_cmd);
		if (rc == SDMMC_OK) {
			timer_res_prv = timer_get_resolution();
			timer_configure(10);
			for (usec = 0; set->state == MCID_CMD && usec < 500000; usec+= 10) {
				timer_sleep(1);
				sdmmc_poll(set);
			}
			timer_configure(timer_res_prv);
		}
	}
	/* Reset CMD and DATn lines */
	regs->SDMMC_SRR |= SDMMC_SRR_SWRSTDAT | SDMMC_SRR_SWRSTCMD;
	while (regs->SDMMC_SRR & (SDMMC_SRR_SWRSTDAT | SDMMC_SRR_SWRSTCMD)) ;
	/* Release command */
	cmd->bStatus = SDMMC_ERROR_USER_CANCEL;
	set->state = MCID_LOCKED;
	set->cmd = NULL;
	set->resp_len = 0;
	set->blk_index = 0;
	set->expect_auto_end = false;
	/* Invoke the end-of-command fSdmmcCallback function, if provided */
	if (cmd->fCallback)
		(cmd->fCallback)(cmd->bStatus, cmd->pArg);
	return SDMMC_OK;
}

/*----------------------------------------------------------------------------
 *        HAL for the SD/MMC library
 *----------------------------------------------------------------------------*/

/**
 * Here is the fSdmmcLock-type callback.
 * Lock the driver for slot N access.
 * TODO implement, once used by the library.
 */
static uint32_t sdmmc_lock(void *_set, uint8_t slot)
{
	assert(_set);

	if (slot > 0) {
		return SDMMC_ERROR_PARAM;
	}
	return SDMMC_OK;
}

/**
 * Here is the fSdmmcRelease-type callback.
 * Release the driver.
 * TODO implement, once used by the library.
 */
static uint32_t sdmmc_release(void *_set)
{
	assert(_set);

	return SDMMC_OK;
}

/** 
 * Here is the fSdmmcIOCtrl-type callback.
 * IO control functions.
 * \param _set  Pointer to driver instance data (struct sdmmc_set).
 * \param bCtl  IO control code.
 * \param param  IO control parameter. Optional, depends on the IO control code.
 * \return Return code, from the eSDMMC_RC enumeration.
 */
static uint32_t sdmmc_control(void *_set, uint32_t bCtl, uint32_t param)
{
	assert(_set);

	struct sdmmc_set *set = (struct sdmmc_set *)_set;
	uint32_t rc = SDMMC_OK, *param_u32 = (uint32_t *)param;
	uint8_t byte;

#ifndef NDEBUG
	if (bCtl != SDMMC_IOCTL_BUSY_CHECK && bCtl != SDMMC_IOCTL_GET_DEVICE)
		trace_debug("%s(%lu)\n\r", SD_StringifyIOCtrl(bCtl),
		    param ? *param_u32 : 0);
#endif

	switch (bCtl) {
	case SDMMC_IOCTL_GET_DEVICE:
		if (!param)
			return SDMMC_ERROR_PARAM;
		*param_u32 = set->regs->SDMMC_PSR & SDMMC_PSR_CARDINS ? 1 : 0;
		break;

	case SDMMC_IOCTL_POWER:
		if (!param)
			return SDMMC_ERROR_PARAM;
		sdmmc_power_device(set, *param_u32 ? true : false);
		break;

	case SDMMC_IOCTL_RESET:
		/* Release the device. The device may have been removed. */
		sdmmc_power_device(set, false);
		break;

	case SDMMC_IOCTL_GET_BUSMODE:
		if (!param)
			return SDMMC_ERROR_PARAM;
		byte = sdmmc_get_bus_width(set);
		*param_u32 = byte;
		break;

	case SDMMC_IOCTL_SET_BUSMODE:
		if (!param)
			return SDMMC_ERROR_PARAM;
		if (*param_u32 > 0xff)
			return SDMMC_ERROR_PARAM;
		rc = sdmmc_set_bus_width(set, (uint8_t)*param_u32);
		byte = sdmmc_get_bus_width(set);
		trace_debug("Using a %u-bit data bus\n\r", byte);
		break;

	case SDMMC_IOCTL_GET_HSMODE:
		if (!param)
			return SDMMC_ERROR_PARAM;
		*param_u32 = set->regs->SDMMC_CA0R & SDMMC_CA0R_HSSUP ? 1 : 0;
		break;

	case SDMMC_IOCTL_SET_HSMODE:
		if (!param)
			return SDMMC_ERROR_PARAM;
		rc = sdmmc_set_speed_mode(set, *param_u32 ? true : false);
		*param_u32 = sdmmc_get_speed_mode(set) ? 1 : 0;
		trace_debug("Using %s mode\n\r", *param_u32 ? "High Speed" : "Default Speed");
		break;

	case SDMMC_IOCTL_SET_CLOCK:
		if (!param)
			return SDMMC_ERROR_PARAM;
		if (*param_u32 == 0)
			return SDMMC_ERROR_PARAM;
		sdmmc_set_device_clock(set, *param_u32);
		trace_debug("Clocking the device at %lu Hz\n\r", set->dev_freq);
		if (set->dev_freq != *param_u32) {
			rc = SDMMC_CHANGED;
			*param_u32 = set->dev_freq;
		}
		break;

	case SDMMC_IOCTL_SET_LENPREFIX:
		if (!param)
			return SDMMC_ERROR_PARAM;
		set->use_set_blk_cnt = *param_u32 ? true : false;
		*param_u32 = set->use_set_blk_cnt ? 1 : 0;
		break;

	case SDMMC_IOCTL_GET_XFERCOMPL:
		if (!param)
			return SDMMC_ERROR_PARAM;
		*param_u32 = 1;
		break;

	case SDMMC_IOCTL_BUSY_CHECK:
		if (!param)
			return SDMMC_ERROR_PARAM;
		if (set->state == MCID_OFF)
			*param_u32 = 0;
		else
			*param_u32 = sdmmc_is_busy(set) ? 1 : 0;
		break;

	case SDMMC_IOCTL_CANCEL_CMD:
		if (set->state == MCID_OFF)
			rc = SDMMC_STATE;
		else
			rc = sdmmc_cancel_command(set);
		break;

	case SDMMC_IOCTL_GET_CLOCK:
	case SDMMC_IOCTL_SET_BOOTMODE:
	case SDMMC_IOCTL_GET_BOOTMODE:
	default:
		rc = SDMMC_ERROR_NOT_SUPPORT;
		break;
	}
#ifndef NDEBUG
	if (rc != SDMMC_OK && rc != SDMMC_CHANGED && bCtl != SDMMC_IOCTL_BUSY_CHECK)
		trace_error("%s ended with %s\n\r", SD_StringifyIOCtrl(bCtl), SD_StringifyRetCode(rc));
#endif
	return rc;
}

/**
 * Here is the fSdmmcSendCommand-type callback.
 * SD/MMC command.
 * \param _set  Pointer to driver instance data (struct sdmmc_set).
 * \param cmd  Pointer to the command to be sent. Owned by the caller. Shall
 * remain valid until the command is completed or stopped. For commands which
 * transfer data, mind the peripheral and DMA alignment requirements that the
 * external data buffer shall meet. Especially when DMA is used to read from the
 * device, in which case the buffer shall be aligned on entire cache lines.
 * \return Return code, from the eSDMMC_RC enumeration. If SDMMC_OK, the command
 * has been issued and the caller should:
 *   1. poll on sdmmc_is_busy(),
 *   2. once finished, check the result of the command in cmd->bStatus.
 * TODO in future when libsdmmc will set it: call sSdmmcCommand::fCallback.
 */
static uint32_t sdmmc_send_command(void *_set, sSdmmcCommand *cmd)
{
	assert(_set);
	assert(cmd);
	assert(cmd->bCmd <= 63);

	struct sdmmc_set *set = (struct sdmmc_set *)_set;
	Sdmmc *regs = set->regs;
	const bool stop_xfer = cmd->cmdOp.bmBits.xfrData == SDMMC_CMD_STOPXFR;
	const bool has_data = cmd->cmdOp.bmBits.xfrData == SDMMC_CMD_TX
	    || cmd->cmdOp.bmBits.xfrData == SDMMC_CMD_RX;
	const bool multiple_xfer = cmd->bCmd == 18 || cmd->bCmd == 25;
	const bool blk_count_prefix = (cmd->bCmd == 18 || cmd->bCmd == 25)
	    && set->use_set_blk_cnt;
	const bool stop_xfer_suffix = (cmd->bCmd == 18 || cmd->bCmd == 25)
	    && !set->use_set_blk_cnt;
	uint32_t timer_res_prv, usec, eister, mask, cycles;
	uint16_t cr, tmr;
	uint8_t rc = SDMMC_OK, mc1r;

	if (set->state == MCID_OFF)
		return SDMMC_STATE;
	if (cmd->cmdOp.bmBits.powerON == cmd->cmdOp.bmBits.sendCmd) {
		trace_error("Invalid command\n\r");
		return SDMMC_ERROR_PARAM;
	}
	if (stop_xfer && cmd->bCmd != 12 && cmd->bCmd != 52) {
		trace_error("Inconsistent abort command\n\r");
		return SDMMC_ERROR_PARAM;
	}
	if (cmd->cmdOp.bmBits.powerON) {
		/* Special call, no command to send this time */
		/* Wait for 74 SD Clock cycles, as per SD Card specification.
		 * The e.MMC Electrical Standard specifies tRSCA >= 200 usec. */
		if (set->dev_freq == 0) {
			trace_error("Shall enable the device clock first\n\r");
			return SDMMC_ERROR_STATE;
		}
		timer_res_prv = timer_get_resolution();
		usec = ROUND_INT_DIV(74 * 1000000UL, set->dev_freq);
		timer_configure(usec < 200 ? 200 : usec);
		timer_sleep(1);
		timer_configure(timer_res_prv);
		return SDMMC_OK;
	}

	if (has_data && (cmd->wNbBlocks == 0 || cmd->wBlockSize == 0
	    || cmd->pData == NULL)) {
		trace_error("Invalid data\n\r");
		return SDMMC_ERROR_PARAM;
	}
	if (has_data && cmd->wBlockSize > set->blk_size) {
		trace_error("%u-byte data block size not supported\n\r", cmd->wBlockSize);
		return SDMMC_ERROR_PARAM;
	}
	if (has_data && set->table) {
		/* Using DMA. Prepare the descriptor table. */
		rc = sdmmc_build_dma_table(set, cmd);
		if (rc != SDMMC_OK && rc != SDMMC_CHANGED)
			return rc;
		if (cmd->cmdOp.bmBits.xfrData == SDMMC_CMD_TX)
			/* Ensure the outgoing data can be fetched directly from
			 * RAM */
			l2cc_clean_region((uint32_t)cmd->pData,
			    (uint32_t)cmd->pData + (uint32_t)cmd->wNbBlocks
			    * (uint32_t)cmd->wBlockSize);
	}
	if (multiple_xfer && !has_data)
		trace_warning("Inconsistent data\n\r");
	if (sdmmc_is_busy(set)) {
		trace_error("Concurrent command\n\r");
		return SDMMC_ERROR_BUSY;
	}
	set->state = MCID_CMD;
	set->cmd = cmd;
	set->resp_len = 0;
	set->blk_index = 0;
	set->expect_auto_end = false;
	cmd->bStatus = rc;

	tmr = (regs->SDMMC_TMR & ~SDMMC_TMR_MSBSEL & ~SDMMC_TMR_DTDSEL
	    & ~SDMMC_TMR_ACMDEN_Msk & ~SDMMC_TMR_BCEN & ~SDMMC_TMR_DMAEN)
	    | SDMMC_TMR_ACMDEN_DIS;
	mc1r = (regs->SDMMC_MC1R & ~SDMMC_MC1R_OPD & ~SDMMC_MC1R_CMDTYP_Msk)
	    | SDMMC_MC1R_CMDTYP_NORMAL;
	cr = (regs->SDMMC_CR & ~SDMMC_CR_CMDIDX_Msk & ~SDMMC_CR_CMDTYP_Msk
	    & ~SDMMC_CR_DPSEL & ~SDMMC_CR_RESPTYP_Msk)
	    | SDMMC_CR_CMDIDX(cmd->bCmd) | SDMMC_CR_CMDTYP_NORMAL
	    | SDMMC_CR_CMDICEN | SDMMC_CR_CMDCCEN;
	eister = SDMMC_EISTER_BOOTAE | SDMMC_EISTER_ADMA
	    | SDMMC_EISTER_ACMD | SDMMC_EISTER_CURLIM | SDMMC_EISTER_DATEND
	    | SDMMC_EISTER_DATCRC | SDMMC_EISTER_DATTEO | SDMMC_EISTER_CMDIDX
	    | SDMMC_EISTER_CMDEND | SDMMC_EISTER_CMDCRC | SDMMC_EISTER_CMDTEO;

	if (cmd->cmdOp.bmBits.odON)
		mc1r |= SDMMC_MC1R_OPD;
	switch (cmd->cmdOp.bmBits.respType) {
	case 2:
		cr |= SDMMC_CR_RESPTYP_RL136;
		/* R2 response doesn't include the command index */
		eister &= ~SDMMC_EISTER_CMDIDX;
		break;
	case 3:
		/* R3 response includes neither the command index nor the CRC */
		eister &= ~(SDMMC_EISTER_CMDIDX | SDMMC_EISTER_CMDCRC);
	case 1:
	case 4:
		if (cmd->cmdOp.bmBits.respType == 4 && cmd->cmdOp.bmBits.ioCmd)
			/* SDIO R4 response includes neither the command index nor the CRC */
			eister &= ~(SDMMC_EISTER_CMDIDX | SDMMC_EISTER_CMDCRC);
	case 5:
	case 6:
	case 7:
		cr |= cmd->cmdOp.bmBits.checkBsy ? SDMMC_CR_RESPTYP_RL48BUSY
		    : SDMMC_CR_RESPTYP_RL48;
		break;
	default:
		/* No response, ignore response time-out error */
		cr |= SDMMC_CR_RESPTYP_NORESP;
		eister &= ~SDMMC_EISTER_CMDTEO;
		break;
	}
	if (stop_xfer) {
		tmr |= SDMMC_TMR_MSBSEL | SDMMC_TMR_BCEN;
		/* TODO consider BGCR:STPBGR (pause) */
		/* TODO in case of SDIO consider CR:CMDTYP = ABORT */
		/* Ignore data errors */
		eister = eister & ~SDMMC_EISTER_ADMA & ~SDMMC_EISTER_DATEND
		    & ~SDMMC_EISTER_DATCRC & ~SDMMC_EISTER_DATTEO;
	}
	else if (has_data) {
		cr |= SDMMC_CR_DPSEL;
		tmr |= cmd->cmdOp.bmBits.xfrData == SDMMC_CMD_TX
		    ? SDMMC_TMR_DTDSEL_WR : SDMMC_TMR_DTDSEL_RD;
		if (blk_count_prefix)
			tmr = (tmr & ~SDMMC_TMR_ACMDEN_Msk)
			    | SDMMC_TMR_ACMDEN_ACMD23;
		else if (stop_xfer_suffix)
			tmr = (tmr & ~SDMMC_TMR_ACMDEN_Msk)
			    | SDMMC_TMR_ACMDEN_ACMD12;
		/* TODO check if this is fine for SDIO too (byte or block transfer) (cmd->cmdOp.bmBits.ioCmd, cmd->wBlockSize) */
		if (multiple_xfer || cmd->wNbBlocks > 1)
			tmr |= SDMMC_TMR_MSBSEL | SDMMC_TMR_BCEN;
		if (set->table)
			tmr |= SDMMC_TMR_DMAEN;
	}

	/* Enable normal interrupts */
	regs->SDMMC_NISTER |= SDMMC_NISTER_BRDRDY | SDMMC_NISTER_BWRRDY
	    | SDMMC_NISTER_TRFC | SDMMC_NISTER_CMDC;
	assert(!(regs->SDMMC_NISTER & SDMMC_NISTR_CUSTOM_EVT));
	/* Enable error interrupts */
	regs->SDMMC_EISTER = eister;
	/* Clear all interrupt status flags */
	regs->SDMMC_NISTR = SDMMC_NISTR_ERRINT | SDMMC_NISTR_BOOTAR
	    | SDMMC_NISTR_CINT | SDMMC_NISTR_CREM | SDMMC_NISTR_CINS
	    | SDMMC_NISTR_BRDRDY | SDMMC_NISTR_BWRRDY | SDMMC_NISTR_DMAINT
	    | SDMMC_NISTR_BLKGE | SDMMC_NISTR_TRFC | SDMMC_NISTR_CMDC;
	regs->SDMMC_EISTR = SDMMC_EISTR_BOOTAE | SDMMC_EISTR_ADMA
	    | SDMMC_EISTR_ACMD | SDMMC_EISTR_CURLIM | SDMMC_EISTR_DATEND
	    | SDMMC_EISTR_DATCRC | SDMMC_EISTR_DATTEO | SDMMC_EISTR_CMDIDX
	    | SDMMC_EISTR_CMDEND | SDMMC_EISTR_CMDCRC | SDMMC_EISTR_CMDTEO;

	/* Wait for the CMD and DATn lines to be ready */
	mask = SDMMC_PSR_CMDINHC;
	if (has_data || (cmd->cmdOp.bmBits.checkBsy && !stop_xfer))
		mask |= SDMMC_PSR_CMDINHD;
	while (regs->SDMMC_PSR & mask) ;

	/* Issue the command */
	if (has_data) {
		if (blk_count_prefix)
			regs->SDMMC_SSAR = SDMMC_SSAR_ARG2(cmd->wNbBlocks);
		if (set->table)
			regs->SDMMC_ASA0R =
			    SDMMC_ASA0R_ADMASA((uint32_t)set->table);
		regs->SDMMC_BSR = (regs->SDMMC_BSR & ~SDMMC_BSR_BLKSIZE_Msk)
		    | SDMMC_BSR_BLKSIZE(cmd->wBlockSize);
	}
	if (stop_xfer)
		regs->SDMMC_BCR = SDMMC_BCR_BLKCNT(0);
	else if (has_data && (multiple_xfer || cmd->wNbBlocks > 1))
		regs->SDMMC_BCR = SDMMC_BCR_BLKCNT(cmd->wNbBlocks);
	regs->SDMMC_ARG1R = cmd->dwArg;
	if (has_data || stop_xfer)
		regs->SDMMC_TMR = tmr;
	regs->SDMMC_MC1R = mc1r;
	regs->SDMMC_CR = cr;

	/* In the case of Auto CMD12, we'll need to generate an extra event.
	 * Have our Timer/Counter ready for this. */
	if (has_data && stop_xfer_suffix) {
		/* Considering the multiple block read mode,
		 * 1. Assuming Transfer Complete is raised upon successful
		 *    reception of the End bit of the last data packet,
		 * 2. A SD/eMMC protocol analyzer shows that the CMD12 command
		 *    token is fully transmitted 1 or 2 device clock cycles
		 *    later,
		 * 3. The device may take up to 64 clock cycles (NCR) before
		 *    initiating the CMD12 response token,
		 * 4. The code length of the CMD12 response token (R1) is 48
		 *    bits, hence 48 device clock cycles.
		 * The sum of the above timings is the maximum time CMD12 will
		 * take to complete. */
		cycles = pmc_get_peripheral_clock(set->tc_id)
		    / (set->dev_freq / (2ul + 64ul + 48ul));
		/* The Timer operates with RC >= 1 */
		set->timer->TC_RC = cycles ? cycles : 1;
	}

	return SDMMC_OK;
}

static sSdHalFunctions sdHal = {
	.fLock = sdmmc_lock,
	.fRelease = sdmmc_release,
	.fCommand = sdmmc_send_command,
	.fIOCtrl = sdmmc_control,
};

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

bool sdmmc_initialize(struct sdmmc_set *set, Sdmmc *regs, uint32_t periph_id,
    uint32_t tc_id, uint32_t tc_ch, uint32_t *dma_buf, uint32_t dma_buf_size)
{
	assert(set);
	assert(regs);
	assert(periph_id <= 0xff);
	assert(tc_ch < TCCHANNEL_NUMBER);

	Tc * const tc_module = get_tc_addr_from_id(tc_id);
	uint32_t base_freq, power, val;
	const uint8_t max_exp = (SDMMC_TCR_DTCVAL_Msk >> SDMMC_TCR_DTCVAL_Pos) - 1;
	uint8_t exp;

	assert(tc_module);
	memset(set, 0, sizeof(*set));
	set->id = periph_id;
	set->regs = regs;
	set->tc_id = tc_id;
	set->timer = &tc_module->TC_CHANNEL[tc_ch];
	set->table_size = dma_buf ? dma_buf_size / SDMMC_DMADL_SIZE : 0;
	set->table = set->table_size ? dma_buf : NULL;
	set->use_polling = true;
	set->use_set_blk_cnt = false;
	set->state = MCID_OFF;

	val = (regs->SDMMC_CA0R & SDMMC_CA0R_MAXBLKL_Msk) >> SDMMC_CA0R_MAXBLKL_Pos;
	set->blk_size = val <= 0x2 ? 512 << val : 512;

	/* Prepare our Timer/Counter */
	tc_configure(tc_module, tc_ch, TC_CMR_WAVE | TC_CMR_WAVSEL_UP
	    | TC_CMR_CPCDIS | TC_CMR_BURST_NONE | TC_CMR_TCCLKS_TIMER_CLOCK2);
	set->timer->TC_EMR |= TC_EMR_NODIVCLK;

	/* Perform the initial I/O calibration sequence, manually.
	 * Allow tSTARTUP = 2 usec for the analog circuitry to start up.
	 * CNTVAL = fHCLOCK / (4 * (1 / tSTARTUP)) */
	val = pmc_get_peripheral_clock(periph_id);
	val = ROUND_INT_DIV(val, 4 * 500000UL);
	assert(!(val << SDMMC_CALCR_CNTVAL_Pos & ~SDMMC_CALCR_CNTVAL_Msk));
	regs->SDMMC_CALCR = (regs->SDMMC_CALCR & ~SDMMC_CALCR_CNTVAL_Msk) | SDMMC_CALCR_CNTVAL(val);
	regs->SDMMC_CALCR |= SDMMC_CALCR_EN;
	while (regs->SDMMC_CALCR & SDMMC_CALCR_EN) ;
	val = regs->SDMMC_CALCR;
	trace_info("Result of output impedance calibration: CALN=%lu, CALP=%lu.\n\r",
	    (val & SDMMC_CALCR_CALN_Msk) >> SDMMC_CALCR_CALN_Pos,
	    (val & SDMMC_CALCR_CALP_Msk) >> SDMMC_CALCR_CALP_Pos);

	/* Set DAT line timeout error to occur after 500 ms waiting delay.
	 * 500 ms is the timeout value to implement when writing to SDXC cards.
	 */
	base_freq = (regs->SDMMC_CA0R & SDMMC_CA0R_TEOCLKF_Msk) >> SDMMC_CA0R_TEOCLKF_Pos;
	base_freq *= regs->SDMMC_CA0R & SDMMC_CA0R_TEOCLKU ? 1000000UL : 1000UL;
	/* 2 ^ (DTCVAL + 13) = TIMEOUT * FTEOCLK = FTEOCLK / 2 */
	val = base_freq / 2;
	for (exp = 31, power = 1UL << 31; !(val & power) && power != 0;
	    exp--, power >>= 1) ;
	if (power == 0) {
		trace_warning("FTEOCLK is unknown\n\r");
		exp = max_exp;
	}
	else {
		exp = exp + 1 - 13;
		exp = exp <= max_exp ? exp : max_exp;
	}
	regs->SDMMC_TCR = (regs->SDMMC_TCR & ~SDMMC_TCR_DTCVAL_Msk)
	    | SDMMC_TCR_DTCVAL(exp);
	trace_debug("Set DAT line timeout to %lu ms\n\r", (10UL << (exp + 13UL))
	    / (base_freq / 100UL));

	/* Reset the peripheral. This will reset almost all registers.
	 * It doesn't affect I/O calibration however. */
	sdmmc_reset_peripheral(set);
	/* As sdmmc_reset_peripheral deliberately preserves MC1R.FCD, this field
	 * has yet to be initialized. */
	regs->SDMMC_MC1R &= ~SDMMC_MC1R_FCD;

	return true;
}

/**
 * \brief Initialize the SD/MMC library instance for SD/MMC bus mode (versus
 * SPI mode, not supported by this driver). Provide it with the HAL callback
 * functions implemented here.
 * \param pSd   Pointer to SD/MMC library instance data.
 * \param pDrv  Pointer to driver instance data (struct sdmmc_set).
 * \param bSlot Slot number.
 */
void SDD_InitializeSdmmcMode(sSdCard *pSd, void *pDrv, uint8_t bSlot)
{
	SDD_Initialize(pSd, pDrv, bSlot, &sdHal);
}
