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

/** \file
 *  Implements functions for Controller Area Network with Flexible Data-rate,
 *  relying on the MCAN peripheral.
 */
/** \addtogroup can_module
 *@{*/

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"
#include "chip.h"
#include "mcan.h"
#include "pmc.h"

#include <assert.h>
#include <string.h>

/*---------------------------------------------------------------------------
 *      Local definitions
 *---------------------------------------------------------------------------*/

enum mcan_dlc
{
	CAN_DLC_0 = 0,
	CAN_DLC_1 = 1,
	CAN_DLC_2 = 2,
	CAN_DLC_3 = 3,
	CAN_DLC_4 = 4,
	CAN_DLC_5 = 5,
	CAN_DLC_6 = 6,
	CAN_DLC_7 = 7,
	CAN_DLC_8 = 8,
	CAN_DLC_12 = 9,
	CAN_DLC_16 = 10,
	CAN_DLC_20 = 11,
	CAN_DLC_24 = 12,
	CAN_DLC_32 = 13,
	CAN_DLC_48 = 14,
	CAN_DLC_64 = 15
};

/*---------------------------------------------------------------------------
 *        Local functions
 *---------------------------------------------------------------------------*/

/**
 * \brief Convert data length to Data Length Code.
 * \param len  length, in bytes
 * \param dlc  address where the matching Data Length Code will be written
 * \return true if a code matched the provided length, false if this exact
 * length is not supported.
 */
static bool get_length_code(uint8_t len, enum mcan_dlc *dlc)
{
	assert(dlc);

	if (len <= 8) {
		*dlc = (enum mcan_dlc)len;
		return true;
	}
	if (len % 4)
		return false;
	len /= 4;
	if (len <= 6) {
		*dlc = (enum mcan_dlc)(len + 6);
		return true;
	}
	if (len % 4)
		return false;
	len /= 4;
	if (len > 4)
		return false;
	*dlc = (enum mcan_dlc)(len + 11);
	return true;
}

/**
 * \brief Convert Data Length Code to actual data length.
 * \param dlc  CAN_DLC_xx enum value
 * \return Data length, expressed in bytes.
 */
static uint8_t get_data_length(enum mcan_dlc dlc)
{
	assert((dlc == CAN_DLC_0 || dlc > CAN_DLC_0) && dlc <= CAN_DLC_64);

	if (dlc <= CAN_DLC_8)
		return (uint8_t)dlc;
	if (dlc <= CAN_DLC_24)
		return ((uint8_t)dlc - 6) * 4;
	return ((uint8_t)dlc - 11) * 16;
}

/**
 * \brief Compute the size of the Message RAM, depending on the application.
 * \param set  Pointer to a MCAN instance that will be setup accordingly.
 * \param cfg  MCAN configuration to be considered. Only integer size parameters
 * need to be configured. The other parameters can be left blank at this stage.
 * \param size  address where the required size of the Message RAM will be
 * written, expressed in (32-bit) words.
 * \return true if successful, false if a parameter is set to an unsupported
 * value.
 */
static bool configure_ram(struct mcan_set *set,
                          const struct mcan_config *cfg, uint32_t *size)
{
	if (cfg->array_size_filt_std > 128 || cfg->array_size_filt_ext > 64
	    || cfg->fifo_size_rx0 > 64 || cfg->fifo_size_rx1 > 64
	    || cfg->array_size_rx > 64 || cfg->fifo_size_tx_evt > 32
	    || cfg->array_size_tx > 32 || cfg->fifo_size_tx > 32
	    || cfg->array_size_tx + cfg->fifo_size_tx > 32
	    || cfg->buf_size_rx_fifo0 > 64 || cfg->buf_size_rx_fifo1 > 64
	    || cfg->buf_size_rx > 64 || cfg->buf_size_tx > 64)
		return false;

	set->ram_filt_std = cfg->msg_ram;
	*size = (uint32_t)cfg->array_size_filt_std * MCAN_RAM_FILT_STD_SIZE;
	set->ram_filt_ext = cfg->msg_ram + *size;
	*size += (uint32_t)cfg->array_size_filt_ext * MCAN_RAM_FILT_EXT_SIZE;
	set->ram_fifo_rx0 = cfg->msg_ram + *size;
	*size += (uint32_t)cfg->fifo_size_rx0 * (MCAN_RAM_BUF_HDR_SIZE
	    + cfg->buf_size_rx_fifo0 / 4);
	set->ram_fifo_rx1 = cfg->msg_ram + *size;
	*size += (uint32_t)cfg->fifo_size_rx1 * (MCAN_RAM_BUF_HDR_SIZE
	    + cfg->buf_size_rx_fifo1 / 4);
	set->ram_array_rx = cfg->msg_ram + *size;
	*size += (uint32_t)cfg->array_size_rx * (MCAN_RAM_BUF_HDR_SIZE
	    + cfg->buf_size_rx / 4);
	set->ram_fifo_tx_evt = cfg->msg_ram + *size;
	*size += (uint32_t)cfg->fifo_size_tx_evt * MCAN_RAM_TX_EVT_SIZE;
	set->ram_array_tx = cfg->msg_ram + *size;
	*size += (uint32_t)cfg->array_size_tx * (MCAN_RAM_BUF_HDR_SIZE
	    + cfg->buf_size_tx / 4);
	*size += (uint32_t)cfg->fifo_size_tx * (MCAN_RAM_BUF_HDR_SIZE
	    + cfg->buf_size_tx / 4);
	return true;
}

/*---------------------------------------------------------------------------
 *      Exported Functions
 *---------------------------------------------------------------------------*/

bool mcan_configure_msg_ram(const struct mcan_config *cfg, uint32_t *size)
{
	assert(cfg);
	assert(size);

	struct mcan_set tmp_set = { .cfg = { 0 } };

	return configure_ram(&tmp_set, cfg, size);
}

bool mcan_initialize(struct mcan_set *set, const struct mcan_config *cfg)
{
	assert(set);
	assert(cfg);
	assert(cfg->regs);
	assert(cfg->msg_ram);

	Mcan *mcan = cfg->regs;
	uint32_t *element = NULL, *elem_end = NULL;
	uint32_t freq, regVal32;
	enum mcan_dlc dlc;

	memset(set, 0, sizeof(*set));
	if (!configure_ram(set, cfg, &regVal32))
		return false;
	set->cfg = *cfg;

	/* Configure the MSB of the Message RAM Base Address */
	regVal32 = (uint32_t)cfg->msg_ram >> 16;
	if (cfg->id == ID_CAN0_INT0 || cfg->id == ID_CAN0_INT1)
		regVal32 = (SFR->SFR_CAN & ~SFR_CAN_EXT_MEM_CAN0_ADDR_Msk)
		    | SFR_CAN_EXT_MEM_CAN0_ADDR(regVal32);
	else
		regVal32 = (SFR->SFR_CAN & ~SFR_CAN_EXT_MEM_CAN1_ADDR_Msk)
		    | SFR_CAN_EXT_MEM_CAN1_ADDR(regVal32);
	SFR->SFR_CAN = regVal32;

	/* Reset the CC Control Register */
	mcan->MCAN_CCCR = 0 | MCAN_CCCR_INIT_ENABLED;

	mcan_disable(set);
	mcan_reconfigure(set);

	/* Global Filter Configuration: Reject remote frames, reject non-matching frames */
	mcan->MCAN_GFC = MCAN_GFC_RRFE_REJECT | MCAN_GFC_RRFS_REJECT
	    | MCAN_GFC_ANFE(2) | MCAN_GFC_ANFS(2);

	/* Extended ID Filter AND mask */
	mcan->MCAN_XIDAM = 0x1FFFFFFF;

	/* Interrupt configuration - leave initialization with all interrupts off
	 * Disable all interrupts */
	mcan->MCAN_IE = 0;
	mcan->MCAN_TXBTIE = 0x00000000;
	/* All interrupts directed to Line 0 */
	mcan->MCAN_ILS = 0x00000000;
	/* Disable both interrupt LINE 0 & LINE 1 */
	mcan->MCAN_ILE = 0x00;
	/* Clear all interrupt flags */
	mcan->MCAN_IR = 0xFFCFFFFF;

	/* Configure CAN bit timing */
	if (cfg->bit_rate == 0
	    || cfg->quanta_before_sp < 3 || cfg->quanta_before_sp > 257
	    || cfg->quanta_after_sp < 1 || cfg->quanta_after_sp > 128
	    || cfg->quanta_sync_jump < 1 || cfg->quanta_sync_jump > 128)
		return false;
	/* Retrieve the frequency of the CAN core clock i.e. the Generated Clock */
	freq = pmc_get_gck_clock(cfg->id);
	/* Compute the Nominal Baud Rate Prescaler */
	regVal32 = ROUND_INT_DIV(freq, cfg->bit_rate
	    * (cfg->quanta_before_sp + cfg->quanta_after_sp));
	if (regVal32 < 1 || regVal32 > 512)
		return false;
	/* Apply bit timing configuration */
	mcan->MCAN_NBTP = MCAN_NBTP_NBRP(regVal32 - 1)
	    | MCAN_NBTP_NTSEG1(cfg->quanta_before_sp - 1 - 1)
	    | MCAN_NBTP_NTSEG2(cfg->quanta_after_sp - 1)
	    | MCAN_NBTP_NSJW(cfg->quanta_sync_jump - 1);

	/* Configure fast CAN FD bit timing */
	if (cfg->bit_rate_fd < cfg->bit_rate
	    || cfg->quanta_before_sp_fd < 3 || cfg->quanta_before_sp_fd > 33
	    || cfg->quanta_after_sp_fd < 1 || cfg->quanta_after_sp_fd > 16
	    || cfg->quanta_sync_jump_fd < 1 || cfg->quanta_sync_jump_fd > 8)
		return false;
	/* Compute the Fast Baud Rate Prescaler */
	regVal32 = ROUND_INT_DIV(freq, cfg->bit_rate_fd
	    * (cfg->quanta_before_sp_fd + cfg->quanta_after_sp_fd));
	if (regVal32 < 1 || regVal32 > 32)
		return false;
	/* Apply bit timing configuration */
	mcan->MCAN_DBTP = MCAN_DBTP_FBRP(regVal32 - 1)
	    | MCAN_DBTP_DTSEG1(cfg->quanta_before_sp_fd - 1 - 1)
	    | MCAN_DBTP_DTSEG2(cfg->quanta_after_sp_fd - 1)
	    | MCAN_DBTP_DSJW(cfg->quanta_sync_jump_fd - 1);

	/* Configure Message RAM starting addresses and element count */
	/* 11-bit Message ID Rx Filters */
	mcan->MCAN_SIDFC =
	    MCAN_SIDFC_FLSSA((uint32_t)set->ram_filt_std >> 2)
	    | MCAN_SIDFC_LSS(cfg->array_size_filt_std);
	/* 29-bit Message ID Rx Filters */
	mcan->MCAN_XIDFC =
	    MCAN_XIDFC_FLESA((uint32_t)set->ram_filt_ext >> 2)
	    | MCAN_XIDFC_LSE(cfg->array_size_filt_ext);
	/* Rx FIFO 0 */
	mcan->MCAN_RXF0C =
	    MCAN_RXF0C_F0SA((uint32_t)set->ram_fifo_rx0 >> 2)
	    | MCAN_RXF0C_F0S(cfg->fifo_size_rx0)
	    | MCAN_RXF0C_F0WM(0)
	    | 0;   /* clear MCAN_RXF0C_F0OM */
	/* Rx FIFO 1 */
	mcan->MCAN_RXF1C =
	    MCAN_RXF1C_F1SA((uint32_t)set->ram_fifo_rx1 >> 2)
	    | MCAN_RXF1C_F1S(cfg->fifo_size_rx1)
	    | MCAN_RXF1C_F1WM(0)
	    | 0;   /* clear MCAN_RXF1C_F1OM */
	/* Dedicated Rx Buffers
	 * Note: the HW does not know (and does not care about) how many
	 * dedicated Rx Buffers are used by the application. */
	mcan->MCAN_RXBC =
	    MCAN_RXBC_RBSA((uint32_t)set->ram_array_rx >> 2);
	/* Tx Event FIFO */
	mcan->MCAN_TXEFC =
	    MCAN_TXEFC_EFSA((uint32_t)set->ram_fifo_tx_evt >> 2)
	    | MCAN_TXEFC_EFS(cfg->fifo_size_tx_evt)
	    | MCAN_TXEFC_EFWM(0);
	/* Tx Buffers */
	mcan->MCAN_TXBC =
	    MCAN_TXBC_TBSA((uint32_t)set->ram_array_tx >> 2)
	    | MCAN_TXBC_NDTB(cfg->array_size_tx)
	    | MCAN_TXBC_TFQS(cfg->fifo_size_tx)
	    | 0;   /* clear MCAN_TXBC_TFQM */

	/* Configure the size of data fields in Rx and Tx Buffer Elements */
	if (!get_length_code(cfg->buf_size_rx_fifo0, &dlc))
		return false;
	regVal32 = MCAN_RXESC_F0DS(dlc < CAN_DLC_8 ? 0 : dlc - CAN_DLC_8);
	if (!get_length_code(cfg->buf_size_rx_fifo1, &dlc))
		return false;
	regVal32 |= MCAN_RXESC_F1DS(dlc < CAN_DLC_8 ? 0 : dlc - CAN_DLC_8);
	if (!get_length_code(cfg->buf_size_rx, &dlc))
		return false;
	regVal32 |= MCAN_RXESC_RBDS(dlc < CAN_DLC_8 ? 0 : dlc - CAN_DLC_8);
	mcan->MCAN_RXESC = regVal32;
	if (!get_length_code(cfg->buf_size_tx, &dlc))
		return false;
	mcan->MCAN_TXESC =
	    MCAN_TXESC_TBDS(dlc < CAN_DLC_8 ? 0 : dlc - CAN_DLC_8);

	/* Configure Message ID Filters
	 * ...Disable all standard filters */
	for (element = set->ram_filt_std, elem_end = set->ram_filt_std
	    + (uint32_t)cfg->array_size_filt_std * MCAN_RAM_FILT_STD_SIZE;
	    element < elem_end;
	    element += MCAN_RAM_FILT_STD_SIZE)
		element[0] = MCAN_RAM_FILT_SFEC_DIS;
	/* ...Disable all extended filters */
	for (element = set->ram_filt_ext, elem_end = set->ram_filt_ext
	    + (uint32_t)cfg->array_size_filt_ext * MCAN_RAM_FILT_EXT_SIZE;
	    element < elem_end;
	    element += MCAN_RAM_FILT_EXT_SIZE)
		element[0] = MCAN_RAM_FILT_EFEC_DIS;

	mcan->MCAN_NDAT1 = 0xFFFFFFFF;   /* clear new (rx) data flags */
	mcan->MCAN_NDAT2 = 0xFFFFFFFF;   /* clear new (rx) data flags */

	regVal32 = mcan->MCAN_CCCR & ~(MCAN_CCCR_BRSE | MCAN_CCCR_FDOE);
	mcan->MCAN_CCCR = regVal32 | MCAN_CCCR_PXHD | MCAN_CCCR_BRSE_DISABLED
	    | MCAN_CCCR_FDOE_DISABLED;

	DSB();
	ISB();
	return true;
}

void mcan_reconfigure(struct mcan_set *set)
{
	Mcan *mcan = set->cfg.regs;
	uint32_t regVal32;

	regVal32 = mcan->MCAN_CCCR & ~MCAN_CCCR_CCE;
	assert((regVal32 & MCAN_CCCR_INIT) == MCAN_CCCR_INIT_ENABLED);
	/* Enable writing to configuration registers */
	mcan->MCAN_CCCR = regVal32 | MCAN_CCCR_CCE_CONFIGURABLE;
}

void mcan_set_mode(struct mcan_set *set, enum mcan_can_mode mode)
{
	Mcan *mcan = set->cfg.regs;
	uint32_t regVal32;

	regVal32 = mcan->MCAN_CCCR & ~(MCAN_CCCR_BRSE | MCAN_CCCR_FDOE);
	switch (mode) {
	case MCAN_MODE_CAN:
		regVal32 |= MCAN_CCCR_BRSE_DISABLED | MCAN_CCCR_FDOE_DISABLED;
		break;
	case MCAN_MODE_EXT_LEN_CONST_RATE:
		regVal32 |= MCAN_CCCR_BRSE_DISABLED | MCAN_CCCR_FDOE_ENABLED;
		break;
	case MCAN_MODE_EXT_LEN_DUAL_RATE:
		regVal32 |= MCAN_CCCR_BRSE_ENABLED | MCAN_CCCR_FDOE_ENABLED;
		break;
	default:
		return;
	}
	mcan->MCAN_CCCR = regVal32;
}

enum mcan_can_mode mcan_get_mode(const struct mcan_set *set)
{
	const uint32_t cccr = set->cfg.regs->MCAN_CCCR;

	if ((cccr & MCAN_CCCR_FDOE) == MCAN_CCCR_FDOE_DISABLED)
		return MCAN_MODE_CAN;
	if ((cccr & MCAN_CCCR_BRSE) == MCAN_CCCR_BRSE_DISABLED)
		return MCAN_MODE_EXT_LEN_CONST_RATE;
	return MCAN_MODE_EXT_LEN_DUAL_RATE;
}

void mcan_init_loopback(struct mcan_set *set)
{
	Mcan *mcan = set->cfg.regs;

	mcan->MCAN_CCCR |= MCAN_CCCR_TEST_ENABLED;
#if 0
	mcan->MCAN_CCCR |= MCAN_CCCR_MON_ENABLED;   /* for internal loop back */
#endif
	mcan->MCAN_TEST |= MCAN_TEST_LBCK_ENABLED;
}

void mcan_set_tx_queue_mode(struct mcan_set *set)
{
	Mcan *mcan = set->cfg.regs;
	mcan->MCAN_TXBC |= MCAN_TXBC_TFQM;
}

void mcan_enable(struct mcan_set *set)
{
	uint32_t index, val;

	/* Depending on bus condition, the HW may switch back to the
	 * Initialization state, by itself. Therefore, upon timeout, return.
	 * [Using an arbitrary timeout criterion.] */
	for (index = 0; index < 1024; index++) {
		val = set->cfg.regs->MCAN_CCCR;
		if ((val & MCAN_CCCR_INIT) == MCAN_CCCR_INIT_DISABLED)
			break;
		if (index == 0)
			set->cfg.regs->MCAN_CCCR = (val & ~MCAN_CCCR_INIT)
			    | MCAN_CCCR_INIT_DISABLED;
	}
}

void mcan_disable(struct mcan_set *set)
{
	uint32_t val;
	bool initial;

	for (initial = true; true; initial = false) {
		val = set->cfg.regs->MCAN_CCCR;
		if ((val & MCAN_CCCR_INIT) == MCAN_CCCR_INIT_ENABLED)
			break;
		if (initial)
			set->cfg.regs->MCAN_CCCR = (val & ~MCAN_CCCR_INIT)
			    | MCAN_CCCR_INIT_ENABLED;
	}
}

void mcan_loopback_on(struct mcan_set *set)
{
	Mcan *mcan = set->cfg.regs;
	mcan->MCAN_TEST |= MCAN_TEST_LBCK_ENABLED;
}

void mcan_loopback_off(struct mcan_set *set)
{
	Mcan *mcan = set->cfg.regs;
	mcan->MCAN_TEST &= ~MCAN_TEST_LBCK_ENABLED;
}

void mcan_enable_rx_array_flag(struct mcan_set *set, uint8_t line)
{
	assert(line == 0 || line == 1);

	Mcan *mcan = set->cfg.regs;
	if (line) {
		mcan->MCAN_ILS |= MCAN_ILS_DRXL;
		mcan->MCAN_ILE |= MCAN_ILE_EINT1;
	} else {
		mcan->MCAN_ILS &= ~MCAN_ILS_DRXL;
		mcan->MCAN_ILE |= MCAN_ILE_EINT0;
	}
	mcan->MCAN_IR = MCAN_IR_DRX;   /* clear previous flag */
	mcan->MCAN_IE |= MCAN_IE_DRXE;   /* enable it */
}

uint8_t * mcan_prepare_tx_buffer(struct mcan_set *set, uint8_t buf_idx,
				 uint32_t id, uint8_t len)
{
	assert(buf_idx < set->cfg.array_size_tx);
	assert(len <= set->cfg.buf_size_tx);

	Mcan *mcan = set->cfg.regs;
	uint32_t *pThisTxBuf = 0;
	uint32_t val;
	const enum mcan_can_mode mode = mcan_get_mode(set);
	enum mcan_dlc dlc;

	if (buf_idx >= set->cfg.array_size_tx)
		return NULL;
	if (!get_length_code(len, &dlc))
		dlc = CAN_DLC_0;
	pThisTxBuf = set->ram_array_tx + buf_idx
	    * (MCAN_RAM_BUF_HDR_SIZE + set->cfg.buf_size_tx / 4);
	if (mcan_is_extended_id(id))
		*pThisTxBuf++ = MCAN_RAM_BUF_XTD | MCAN_RAM_BUF_ID_XTD(id);
	else
		*pThisTxBuf++ = MCAN_RAM_BUF_ID_STD(id);
	val = MCAN_RAM_BUF_MM(0) | MCAN_RAM_BUF_DLC((uint32_t)dlc);
	if (mode == MCAN_MODE_EXT_LEN_CONST_RATE)
		val |= MCAN_RAM_BUF_FDF;
	else if (mode == MCAN_MODE_EXT_LEN_DUAL_RATE)
		val |= MCAN_RAM_BUF_FDF | MCAN_RAM_BUF_BRS;
	*pThisTxBuf++ = val;
	/* enable transmit from buffer to set TC interrupt bit in IR,
	 * but interrupt will not happen unless TC interrupt is enabled */
	mcan->MCAN_TXBTIE = (1 << buf_idx);
	return (uint8_t *)pThisTxBuf;   /* now it points to the data field */
}

void mcan_send_tx_buffer(struct mcan_set *set, uint8_t buf_idx)
{
	Mcan *mcan = set->cfg.regs;

	if (buf_idx < set->cfg.array_size_tx)
		mcan->MCAN_TXBAR = (1 << buf_idx);
}

uint8_t mcan_enqueue_outgoing_msg(struct mcan_set *set, uint32_t id,
			          uint8_t len, const uint8_t *data)
{
	assert(len <= set->cfg.buf_size_tx);

	Mcan *mcan = set->cfg.regs;
	uint32_t val;
	uint32_t *pThisTxBuf = 0;
	const enum mcan_can_mode mode = mcan_get_mode(set);
	enum mcan_dlc dlc;
	uint8_t putIdx = 255;

	if (!get_length_code(len, &dlc))
		dlc = CAN_DLC_0;
	/* Configured for FifoQ and FifoQ not full? */
	if (set->cfg.fifo_size_tx == 0 || (mcan->MCAN_TXFQS & MCAN_TXFQS_TFQF))
		return putIdx;
	putIdx = (uint8_t)((mcan->MCAN_TXFQS & MCAN_TXFQS_TFQPI_Msk)
	    >> MCAN_TXFQS_TFQPI_Pos);
	pThisTxBuf = set->ram_array_tx + (uint32_t)
	    putIdx * (MCAN_RAM_BUF_HDR_SIZE + set->cfg.buf_size_tx / 4);
	if (mcan_is_extended_id(id))
		*pThisTxBuf++ = MCAN_RAM_BUF_XTD | MCAN_RAM_BUF_ID_XTD(id);
	else
		*pThisTxBuf++ = MCAN_RAM_BUF_ID_STD(id);
	val = MCAN_RAM_BUF_MM(0) | MCAN_RAM_BUF_DLC((uint32_t)dlc);
	if (mode == MCAN_MODE_EXT_LEN_CONST_RATE)
		val |= MCAN_RAM_BUF_FDF;
	else if (mode == MCAN_MODE_EXT_LEN_DUAL_RATE)
		val |= MCAN_RAM_BUF_FDF | MCAN_RAM_BUF_BRS;
	*pThisTxBuf++ = val;
	memcpy(pThisTxBuf, data, len);
	/* enable transmit from buffer to set TC interrupt bit in IR,
	 * but interrupt will not happen unless TC interrupt is enabled
	 */
	mcan->MCAN_TXBTIE = (1 << putIdx);
	/* request to send */
	mcan->MCAN_TXBAR = (1 << putIdx);
	return putIdx;
}

bool mcan_is_buffer_sent(const struct mcan_set *set, uint8_t buf_idx)
{
	Mcan *mcan = set->cfg.regs;
	return mcan->MCAN_TXBTO & (1 << buf_idx) ? true : false;
}

void mcan_filter_single_id(struct mcan_set *set,
			       uint8_t buf_idx, uint8_t filter, uint32_t id)
{
	assert(buf_idx < set->cfg.array_size_rx);
	assert(id & CAN_EXT_MSG_ID ? filter < set->cfg.array_size_filt_ext
	    : filter < set->cfg.array_size_filt_std);
	assert(id & CAN_EXT_MSG_ID ? (id & ~CAN_EXT_MSG_ID) <= 0x1fffffff :
	    id <= 0x7ff);

	uint32_t *pThisRxFilt = 0;

	if (buf_idx >= set->cfg.array_size_rx)
		return;
	if (mcan_is_extended_id(id)) {
		pThisRxFilt = set->ram_filt_ext + filter
		    * MCAN_RAM_FILT_EXT_SIZE;
		*pThisRxFilt++ = MCAN_RAM_FILT_EFEC_BUF
		    | MCAN_RAM_FILT_EFID1(id);
		*pThisRxFilt = MCAN_RAM_FILT_EFID2_BUF
		    | MCAN_RAM_FILT_EFID2_BUF_IDX(buf_idx);
	} else {
		pThisRxFilt = set->ram_filt_std + filter
		    * MCAN_RAM_FILT_STD_SIZE;
		*pThisRxFilt = MCAN_RAM_FILT_SFEC_BUF
		    | MCAN_RAM_FILT_SFID1(id)
		    | MCAN_RAM_FILT_SFID2_BUF
		    | MCAN_RAM_FILT_SFID2_BUF_IDX(buf_idx);
	}
}

void mcan_filter_id_mask(struct mcan_set *set, uint8_t fifo, uint8_t filter,
                         uint32_t id, uint32_t mask)
{
	assert(fifo == 0 || fifo == 1);
	assert(id & CAN_EXT_MSG_ID ? filter < set->cfg.array_size_filt_ext
	    : filter < set->cfg.array_size_filt_std);
	assert(id & CAN_EXT_MSG_ID ? (id & ~CAN_EXT_MSG_ID) <= 0x1fffffff :
	    id <= 0x7ff);
	assert(id & CAN_EXT_MSG_ID ? mask <= 0x1fffffff : mask <= 0x7ff);

	uint32_t *pThisRxFilt = 0;
	uint32_t val;

	if (mcan_is_extended_id(id)) {
		pThisRxFilt = set->ram_filt_ext + filter
		    * MCAN_RAM_FILT_EXT_SIZE;
		*pThisRxFilt++ = (fifo ? MCAN_RAM_FILT_EFEC_FIFO1
		    : MCAN_RAM_FILT_EFEC_FIFO0) | MCAN_RAM_FILT_EFID1(id);
		*pThisRxFilt = MCAN_RAM_FILT_EFT_CLASSIC
		    | MCAN_RAM_FILT_EFID2(mask);
	} else {
		pThisRxFilt = set->ram_filt_std + filter
		    * MCAN_RAM_FILT_STD_SIZE;
		val = MCAN_RAM_FILT_SFT_CLASSIC
		    | MCAN_RAM_FILT_SFID1(id)
		    | MCAN_RAM_FILT_SFID2(mask);
		*pThisRxFilt = (fifo ? MCAN_RAM_FILT_SFEC_FIFO1
		    : MCAN_RAM_FILT_SFEC_FIFO0) | val;
	}
}

bool mcan_rx_buffer_data(const struct mcan_set *set, uint8_t buf_idx)
{
	Mcan *mcan = set->cfg.regs;

	if (buf_idx < 32)
		return mcan->MCAN_NDAT1 & (1 << buf_idx) ? true : false;
	else if (buf_idx < 64)
		return mcan->MCAN_NDAT2 & (1 << (buf_idx - 32)) ? true : false;
	else
		return false;
}

void mcan_read_rx_buffer(struct mcan_set *set, uint8_t buf_idx,
                         struct mcan_msg_info *msg)
{
	assert(buf_idx < set->cfg.array_size_rx);

	Mcan *mcan = set->cfg.regs;
	const uint32_t *pThisRxBuf = 0;
	uint32_t tempRy;   /* temp copy of RX buffer word */
	uint8_t len;

	if (buf_idx >= set->cfg.array_size_rx) {
		msg->id = 0;
		msg->timestamp = 0;
		msg->full_len = 0;
		msg->data_len = 0;
		return;
	}
	pThisRxBuf = set->ram_array_rx + (buf_idx
	    * (MCAN_RAM_BUF_HDR_SIZE + set->cfg.buf_size_rx / 4));
	tempRy = *pThisRxBuf++;   /* word R0 contains ID */
	if (tempRy & MCAN_RAM_BUF_XTD)
		msg->id = CAN_EXT_MSG_ID | (tempRy & MCAN_RAM_BUF_ID_XTD_Msk)
		    >> MCAN_RAM_BUF_ID_XTD_Pos;
	else
		msg->id = (tempRy & MCAN_RAM_BUF_ID_STD_Msk)
		    >> MCAN_RAM_BUF_ID_STD_Pos;
	tempRy = *pThisRxBuf++;   /* word R1 contains DLC & time stamp */
	msg->full_len = len = get_data_length((enum mcan_dlc)
	    ((tempRy & MCAN_RAM_BUF_DLC_Msk) >> MCAN_RAM_BUF_DLC_Pos));
	msg->timestamp = (tempRy & MCAN_RAM_BUF_RXTS_Msk)
	    >> MCAN_RAM_BUF_RXTS_Pos;
	if (msg->data) {
		/* copy the data from the Rx Buffer Element to the
		 * application-owned buffer */
		if (len > set->cfg.buf_size_rx)
			len = set->cfg.buf_size_rx;
		if (len > msg->data_len)
			len = msg->data_len;
		memcpy(msg->data, pThisRxBuf, len);
		msg->data_len = len;
	}
	else
		msg->data_len = 0;
	/* clear the new data flag for the buffer */
	if (buf_idx < 32)
		mcan->MCAN_NDAT1 = (1 << buf_idx);
	else
		mcan->MCAN_NDAT2 = (1 << (buf_idx - 32));
}

uint8_t mcan_dequeue_received_msg(struct mcan_set *set, uint8_t fifo,
                                 struct mcan_msg_info *msg)
{
	assert(fifo == 0 || fifo == 1);

	Mcan *mcan = set->cfg.regs;
	uint32_t *pThisRxBuf = 0;
	uint32_t tempRy;   /* temp copy of RX buffer word */
	uint8_t buf_elem_data_size, len;
	uint32_t *fifo_ack_reg;
	uint32_t get_index;
	uint8_t fill_level = 0;   /* default: fifo empty */

	if (fifo) {
		get_index = (mcan->MCAN_RXF1S & MCAN_RXF1S_F1GI_Msk) >>
		    MCAN_RXF1S_F1GI_Pos;
		fill_level = (uint8_t)((mcan->MCAN_RXF1S & MCAN_RXF1S_F1FL_Msk)
		    >> MCAN_RXF1S_F1FL_Pos);
		pThisRxBuf = set->ram_fifo_rx1;
		buf_elem_data_size = set->cfg.buf_size_rx_fifo1;
		fifo_ack_reg = (uint32_t *) & mcan->MCAN_RXF1A;
	} else {
		get_index = (mcan->MCAN_RXF0S & MCAN_RXF0S_F0GI_Msk)
		    >> MCAN_RXF0S_F0GI_Pos;
		fill_level = (uint8_t)((mcan->MCAN_RXF0S & MCAN_RXF0S_F0FL_Msk)
		    >> MCAN_RXF0S_F0FL_Pos);
		pThisRxBuf = set->ram_fifo_rx0;
		buf_elem_data_size = set->cfg.buf_size_rx_fifo0;
		fifo_ack_reg = (uint32_t *) & mcan->MCAN_RXF0A;
	}

	if (fill_level == 0)
		return 0;

	pThisRxBuf += get_index * (MCAN_RAM_BUF_HDR_SIZE + buf_elem_data_size
	    / 4);
	tempRy = *pThisRxBuf++;	  /* word R0 contains ID */
	if (tempRy & MCAN_RAM_BUF_XTD)
		msg->id = CAN_EXT_MSG_ID | (tempRy & MCAN_RAM_BUF_ID_XTD_Msk)
		    >> MCAN_RAM_BUF_ID_XTD_Pos;
	else
		msg->id = (tempRy & MCAN_RAM_BUF_ID_STD_Msk)
		    >> MCAN_RAM_BUF_ID_STD_Pos;
	tempRy = *pThisRxBuf++;   /* word R1 contains DLC & timestamps */
	msg->full_len = len = get_data_length((enum mcan_dlc)
	    ((tempRy & MCAN_RAM_BUF_DLC_Msk) >> MCAN_RAM_BUF_DLC_Pos));
	msg->timestamp = (tempRy & MCAN_RAM_BUF_RXTS_Msk)
	    >> MCAN_RAM_BUF_RXTS_Pos;
	if (msg->data) {
		/* copy the data from the Rx Buffer Element to the
		 * application-owned buffer */
		if (len > buf_elem_data_size)
			len = buf_elem_data_size;
		if (len > msg->data_len)
			len = msg->data_len;
		memcpy(msg->data, pThisRxBuf, len);
		msg->data_len = len;
	}
	else
		msg->data_len = 0;
	/* acknowledge reading the fifo entry */
	*fifo_ack_reg = get_index;
	/* return entries remaining in FIFO */
	return (fill_level);
}

/**@}*/
