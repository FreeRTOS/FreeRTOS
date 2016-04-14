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

/**
 * \file
 *
 * \section Purpose
 *
 * Controller Area Network with Flexible Data-rate.
 * Interface for configuring and using the MCAN peripheral.
 */

#ifndef _MCAN_H_
#define _MCAN_H_

/*----------------------------------------------------------------------------
 *         Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"

#include <assert.h>

#ifdef __cplusplus
extern "C" {
#endif

/*----------------------------------------------------------------------------
 *         Definitions
 *----------------------------------------------------------------------------*/

enum mcan_can_mode
{
	/* ISO 11898-1 CAN mode */
	MCAN_MODE_CAN,

	/* Long CAN FD frame.
	 * - TX and RX payloads up to 64 bytes.
	 * - Slow transmitter: TX frames are sent at constant bit rate.
	 * - Fast receiver: both constant-rate (slow) and dual-rate (fast)
	 *   RX frames are supported and received. */
	MCAN_MODE_EXT_LEN_CONST_RATE,

	/* Long and fast CAN FD frame.
	 * - TX and RX payloads up to 64 bytes.
	 * - Fast transmitter: control, data and CRC fields are transmitted at a
	 *   higher bit rate.
	 * - Fast receiver. */
	MCAN_MODE_EXT_LEN_DUAL_RATE,
};

/* Flag signalling a standard (11-bit) message identifiers */
#define CAN_STD_MSG_ID (0x0u << 30)
/* Flag to be bitwise or'ed to extended (29-bit) message identifiers */
#define CAN_EXT_MSG_ID (0x1u << 30)

struct mcan_msg_info
{
	uint32_t id;
	uint32_t timestamp;
	uint8_t *data;
	uint8_t full_len;
	uint8_t data_len;
};

struct mcan_config
{
	uint32_t id;                  /* peripheral ID (ID_xxx) */
	Mcan *regs;                   /* set of MCAN hardware registers */
	uint32_t *msg_ram;            /* base address of the Message RAM to be
	                               * assigned to this MCAN instance */

	uint8_t array_size_filt_std;  /* # of 11-bit Message ID Rx Filters */
	uint8_t array_size_filt_ext;  /* # of 29-bit Message ID Rx Filters */
	uint8_t fifo_size_rx0;        /* # of Rx Buffers in Rx FIFO 0 */
	uint8_t fifo_size_rx1;        /* # of Rx Buffers in Rx FIFO 1 */
	uint8_t array_size_rx;        /* # of dedicated Rx Buffers */
	uint8_t fifo_size_tx_evt;     /* # of Tx Event Elements in the Tx Event
	                               * FIFO */
	uint8_t array_size_tx;        /* # of dedicated Tx Buffers */
	uint8_t fifo_size_tx;         /* # of Tx Buffers in the Tx FIFO or Tx
	                               * Queue */

	uint8_t buf_size_rx_fifo0;    /* size of the data field in each Rx
	                               * Buffer of Rx FIFO 0, in bytes */
	uint8_t buf_size_rx_fifo1;    /* size of the data field in each Rx
	                               * Buffer of Rx FIFO 1, in bytes */
	uint8_t buf_size_rx;          /* size of the data field in each
	                               * dedicated Rx Buffer, in bytes */
	uint8_t buf_size_tx;          /* size of the data field in each Tx
	                               * Buffer, in bytes. Applies to all Tx
	                               * Buffers, dedicated and in Tx FIFO /
	                               * Queue. */

	uint32_t bit_rate;            /* requested CAN bit rate in CAN mode,
	                               * in bps */
	uint16_t quanta_before_sp;    /* duration of the time segment before the
	                               * sample point (Sync_Seg + Prop_Seg +
	                               * Phase_Seg1), while in CAN mode,
	                               * expressed in CAN time quanta */
	uint8_t quanta_after_sp;      /* duration of the time segment after the
	                               * sample point (Phase_Seg2), while in CAN
	                               * mode, expressed in CAN time quanta */

	uint32_t bit_rate_fd;         /* requested CAN bit rate in fast CAN FD
	                               * mode, in bps */
	uint8_t quanta_before_sp_fd;  /* duration of the time segment before the
	                               * sample point (Sync_Seg + Prop_Seg +
	                               * Phase_Seg1), while in fast CAN FD mode,
	                               * expressed in CAN time quanta */
	uint8_t quanta_after_sp_fd;   /* duration of the time segment after the
	                               * sample point (Phase_Seg2), while in
	                               * fast CAN FD mode, expressed in CAN time
	                               * quanta */

	uint8_t quanta_sync_jump;     /* duration of a (re)synchronization jump,
	                               * while in CAN mode, expressed in CAN
	                               * time quanta */
	uint8_t quanta_sync_jump_fd;  /* duration of a (re)synchronization jump,
	                               * while in fast CAN FD mode, expressed in
	                               * CAN time quanta */
};

/* This structure is private to the MCAN Driver.
 * Allocate it but ignore its members. */
struct mcan_set
{
	struct mcan_config cfg;
	uint32_t *ram_filt_std;
	uint32_t *ram_filt_ext;
	uint32_t *ram_fifo_rx0;
	uint32_t *ram_fifo_rx1;
	uint32_t *ram_array_rx;
	uint32_t *ram_fifo_tx_evt;
	uint32_t *ram_array_tx;
};

/*----------------------------------------------------------------------------
 *         Exported symbols
 *----------------------------------------------------------------------------*/

static inline bool mcan_is_enabled(const struct mcan_set *set)
{
	Mcan *mcan = set->cfg.regs;
	return ((mcan->MCAN_CCCR & MCAN_CCCR_INIT) == MCAN_CCCR_INIT_DISABLED);
}

static inline bool mcan_is_extended_id(uint32_t msg_id)
{
	return msg_id & CAN_EXT_MSG_ID ? true : false;
}

static inline uint32_t mcan_get_id(uint32_t msg_id)
{
	return msg_id & CAN_EXT_MSG_ID ? msg_id & 0x1fffffff : msg_id & 0x7ff;
}

static inline bool mcan_is_tx_complete(const struct mcan_set *set)
{
	Mcan *mcan = set->cfg.regs;
	return mcan->MCAN_IR & MCAN_IR_TC ? true : false;
}

static inline void mcan_clear_tx_flag(const struct mcan_set *set)
{
	Mcan *mcan = set->cfg.regs;
	mcan->MCAN_IR = MCAN_IR_TC;
}

static inline bool mcan_rx_array_data(const struct mcan_set *set)
{
	Mcan *mcan = set->cfg.regs;
	return mcan->MCAN_IR & MCAN_IR_DRX ? true : false;
}

static inline void mcan_clear_rx_array_flag(const struct mcan_set *set)
{
	Mcan *mcan = set->cfg.regs;
	mcan->MCAN_IR = MCAN_IR_DRX;
}

static inline bool mcan_rx_fifo_data(const struct mcan_set *set, uint8_t fifo)
{
	assert(fifo == 0 || fifo == 1);

	Mcan *mcan = set->cfg.regs;

	return mcan->MCAN_IR & (fifo ? MCAN_IR_RF1N : MCAN_IR_RF0N) ? true
	    : false;
}

static inline void mcan_clear_rx_fifo_flag(const struct mcan_set *set,
    uint8_t fifo)
{
	assert(fifo == 0 || fifo == 1);

	Mcan *mcan = set->cfg.regs;

	mcan->MCAN_IR = fifo ? MCAN_IR_RF1N : MCAN_IR_RF0N;
}

/**
 * \brief Compute the size of the Message RAM to be assigned to the MCAN.
 * \param cfg  MCAN configuration to be considered. Only integer size parameters
 * need to be configured. The other parameters can be left blank at this stage.
 * \param size  address where the required size of the Message RAM will be
 * written, expressed in (32-bit) words.
 * \return true if successful, false if a parameter is set to an unsupported
 * value.
 */
bool mcan_configure_msg_ram(const struct mcan_config *cfg, uint32_t *size);

/**
 * \brief Initialize the MCAN hardware for the given peripheral.
 * Default: Non-FD, ISO 11898-1 CAN mode; mixed mode TX Buffer + FIFO.
 * \param set  Pointer to uninitialized driver instance data.
 * \param cfg  MCAN configuration to be used.
 * \return true if successful, false if a parameter is set to an unsupported
 * value.
 */
bool mcan_initialize(struct mcan_set *set, const struct mcan_config *cfg);

/**
 * \brief Unlock the peripheral configuration so it can be altered.
 * Prerequisite: the peripheral shall be disabled. In case the device has been
 * enabled, call mcan_disable.
 * \param set  Pointer to driver instance data.
 */
void mcan_reconfigure(struct mcan_set *set);

/**
 * \brief Select either the legacy ISO 11898-1 CAN mode or the CAN-FD mode,
 * along with the FD variant in the latter case.
 * Should be called further to mcan_initialize() or mcan_reconfigure(), before
 * mcan_enable().
 * \param set  Pointer to driver instance data.
 * \param mode  CAN mode, and FD variant in case of FD mode.
 */
void mcan_set_mode(struct mcan_set *set, enum mcan_can_mode mode);

/**
 * \brief Query the current CAN mode.
 * \param set  Pointer to driver instance data.
 * \return Currently selected CAN mode, and FD variant in case of CAN FD mode.
 */
enum mcan_can_mode mcan_get_mode(const struct mcan_set *set);

/**
 * \brief Select the TX Queue mode, disable TX FIFO mode.
 * INIT must be set - so this should be called between mcan_initialize() and
 * mcan_enable().
 * \param set  Pointer to driver instance data.
 */
void mcan_set_tx_queue_mode(struct mcan_set *set);

/**
 * \brief Initialize the MCAN in loop back mode.
 * INIT must be set - so this should be called between mcan_initialize() and
 * mcan_enable().
 * \param set  Pointer to driver instance data.
 */
void mcan_init_loopback(struct mcan_set *set);

/**
 * \brief Enable the peripheral I/O stage. Synchronize with the bus.
 * INIT must be set - so this should be called after mcan_initialize().
 * \param set  Pointer to driver instance data.
 */
void mcan_enable(struct mcan_set *set);

/**
 * \brief Disable the peripheral I/O stage. Go Bus_Off.
 * \note Subsequent operations may include reconfiguring the peripheral
 * (mcan_reconfigure) and/or re-enabling it (mcan_enable).
 * \param set  Pointer to driver instance data.
 */
void mcan_disable(struct mcan_set *set);

/**
 * \brief Turn the loop-back mode ON.
 * \note TEST must be set in MCAN_CCCR. This mode should have been enabled upon
 * initialization.
 * \param set  Pointer to driver instance data.
 */
void mcan_loopback_on(struct mcan_set *set);

/**
 * \brief Turn the loop-back mode OFF.
 * \param set  Pointer to driver instance data.
 */
void mcan_loopback_off(struct mcan_set *set);

/**
 * \brief Select either the m_can_int0 or the m_can_int1 interrupt line.
 * Also, enable the 'Message stored to Dedicated Receive Buffer' specific
 * interrupt.
 * \param set  Pointer to driver instance data.
 * \param int_line  The interrupt line to be enabled:
 *    0   -> m_can_int0
 *    1   -> m_can_int1.
 */
void mcan_enable_rx_array_flag(struct mcan_set *set, uint8_t int_line);

/**
 * \brief Configure a Dedicated TX Buffer.
 * \param set  Pointer to driver instance data.
 * \param buf_idx  Index of the dedicated transmit buffer to be used.
 * \param id  Message ID.
 * \param len  Data length, in bytes.
 * \return Address of data byte 0, part of the transmit buffer.
 */
uint8_t * mcan_prepare_tx_buffer(struct mcan_set *set, uint8_t buf_idx,
    uint32_t id, uint8_t len);

/**
 * \brief Start the transmission of a Dedicated TX Buffer.
 * \param set  Pointer to driver instance data.
 * \param buf_idx  Index of the dedicated transmit buffer to be used.
 */
void mcan_send_tx_buffer(struct mcan_set *set, uint8_t buf_idx);

/**
 * \brief Append the provided message to the TX FIFO, or to the TX Queue,
 * depending on whether mcan_set_tx_queue_mode() has been invoked or not.
 * \param set  Pointer to driver instance data.
 * \param id  Message ID.
 * \param len  Data length, in bytes.
 * \param data  Pointer to data.
 * \return Index of the assigned transmit buffer, part of the FIFO / queue.
 * Or 0xff if the TX FIFO / queue was full, or an error occurred.
 */
uint8_t mcan_enqueue_outgoing_msg(struct mcan_set *set, uint32_t id,
     uint8_t len, const uint8_t *data);

/**
 * \brief Check if message transmitted from the specified TX Buffer, either
 * dedicated or part of the TX FIFO or TX Queue.
 * \param set  Pointer to driver instance data.
 * \param buf_idx  Index of the transmit buffer to be queried.
 * \return true if the message has been successfully transmitted, false
 * otherwise.
 */
bool mcan_is_buffer_sent(const struct mcan_set *set, uint8_t buf_idx);

/**
 * \brief Configure RX buffer filter.
 * \param set  Pointer to driver instance data.
 * \param buf_idx  Index of the receive buffer to be used as the recipient.
 * \param filter  Index of the filter to be configured.
 * \param id  Single message identifier. Incoming message need to match exactly
 * to be accepted.
 */
void mcan_filter_single_id(struct mcan_set *set, uint8_t buf_idx,
    uint8_t filter, uint32_t id);

/**
 * \brief Configure classic RX filter.
 * The classic filters direct the accepted messages to a FIFO, and include both
 * an ID and an ID mask.
 * \param set  Pointer to driver instance data.
 * \param fifo  Index of the RX FIFO to be used as the recipient.
 * \param filter  Index of the filter to be configured.
 * \param id  Message identifier.
 * \param mask  Message identifier mask to be matched.
 */
void mcan_filter_id_mask(struct mcan_set *set, uint8_t fifo, uint8_t filter,
    uint32_t id, uint32_t mask);

/**
 * \brief Check whether some data has been received into the specified RX
 * Buffer.
 * \param set  Pointer to driver instance data.
 * \param buf_idx  Index of the receive buffer to be queried.
 * \return true if the receive buffer is flagged as containing an unfetched
 * frame, and false otherwise.
 */
bool mcan_rx_buffer_data(const struct mcan_set *set, uint8_t buf_idx);

/**
 * \brief Get RX buffer.
 * \param set  Pointer to driver instance data.
 * \param buf_idx  Index of the receive buffer to be read.
 * \param msg  Address where the CAN message properties will be written.
 * The msg->data and msg->data_len parameters shall be initialized prior to
 * calling this function. Message contents will be copied to msg->data if
 * msg->data is not null and if msg->data_len is large enough.
 */
void mcan_read_rx_buffer(struct mcan_set *set, uint8_t buf_idx,
    struct mcan_msg_info *msg);

/**
 * \brief Detach one received message from the specified RX FIFO, and copy it to
 * a buffer owned by the application.
 * \param set  Pointer to driver instance data.
 * \param fifo  Index of the RX FIFO to dequeue from.
 * \param msg  Address where the CAN message properties will be written.
 * The msg->data and msg->data_len parameters shall be initialized prior to
 * calling this function. Message contents will be copied to msg->data if
 * msg->data is not null and if msg->data_len is large enough.
 * \return: # of FIFO entries at the time the function was entered:
 *    0       -> The FIFO was initially empty.
 *    1       -> The FIFO had 1 entry upon entry, but is empty upon exit.
 *    2 to 64 -> The FIFO had several entries upon entry, and still holds one
 *               or more entries upon exit.
 */
uint8_t mcan_dequeue_received_msg(struct mcan_set *set, uint8_t fifo,
    struct mcan_msg_info *msg);

#ifdef __cplusplus
}
#endif

#endif /* #ifndef _MCAN_H_ */
