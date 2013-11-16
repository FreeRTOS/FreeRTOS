 /**
 * \file
 *
 * \brief GMAC (Ethernet MAC) driver for SAM.
 *
 * Copyright (c) 2013 Atmel Corporation. All rights reserved.
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

#ifndef GMAC_H_INCLUDED
#define GMAC_H_INCLUDED

#include "compiler.h"

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/// @endcond

/** The buffer addresses written into the descriptors must be aligned, so the
    last few bits are zero.  These bits have special meaning for the GMAC
    peripheral and cannot be used as part of the address. */
#define GMAC_RXD_ADDR_MASK      0xFFFFFFFC
#define GMAC_RXD_WRAP         (1ul << 1)  /**< Wrap bit */
#define GMAC_RXD_OWNERSHIP    (1ul << 0)  /**< Ownership bit */

#define GMAC_RXD_BROADCAST    (1ul << 31) /**< Broadcast detected */
#define GMAC_RXD_MULTIHASH    (1ul << 30) /**< Multicast hash match */
#define GMAC_RXD_UNIHASH      (1ul << 29) /**< Unicast hash match */
#define GMAC_RXD_ADDR_FOUND      (1ul << 27) /**< Specific address match found */
#define GMAC_RXD_ADDR        (3ul << 25) /**< Address match */
#define GMAC_RXD_RXCOEN        (1ul << 24) /**< RXCOEN related function */
#define GMAC_RXD_TYPE         (3ul << 22) /**< Type ID match */
#define GMAC_RXD_VLAN         (1ul << 21) /**< VLAN tag detected */
#define GMAC_RXD_PRIORITY     (1ul << 20) /**< Priority tag detected */
#define GMAC_RXD_PRIORITY_MASK  (3ul << 17) /**< VLAN priority */
#define GMAC_RXD_CFI          (1ul << 16) /**< Concatenation Format Indicator only if bit 21 is set */
#define GMAC_RXD_EOF          (1ul << 15) /**< End of frame */
#define GMAC_RXD_SOF          (1ul << 14) /**< Start of frame */
#define GMAC_RXD_FCS          (1ul << 13) /**< Frame check sequence */
#define GMAC_RXD_OFFSET_MASK                /**< Receive buffer offset */
#define GMAC_RXD_LEN_MASK       (0xFFF)     /**< Length of frame including FCS (if selected) */
#define GMAC_RXD_LENJUMBO_MASK  (0x3FFF)    /**< Jumbo frame length */

#define GMAC_TXD_USED         (1ul << 31) /**< Frame is transmitted */
#define GMAC_TXD_WRAP         (1ul << 30) /**< Last descriptor */
#define GMAC_TXD_ERROR        (1ul << 29) /**< Retry limit exceeded, error */
#define GMAC_TXD_UNDERRUN     (1ul << 28) /**< Transmit underrun */
#define GMAC_TXD_EXHAUSTED    (1ul << 27) /**< Buffer exhausted */
#define GMAC_TXD_LATE    (1ul << 26) /**< Late collision,transmit  error  */
#define GMAC_TXD_CHECKSUM_ERROR   (7ul << 20) /**< Checksum error */
#define GMAC_TXD_NOCRC        (1ul << 16) /**< No CRC */
#define GMAC_TXD_LAST         (1ul << 15) /**< Last buffer in frame */
#define GMAC_TXD_LEN_MASK       (0x1FFF)     /**< Length of buffer */

/** The MAC can support frame lengths up to 1536 bytes */
#define GMAC_FRAME_LENTGH_MAX       1536

#define GMAC_RX_UNITSIZE            128     /**< Fixed size for RX buffer  */
#define GMAC_TX_UNITSIZE            1518    /**< Size for ETH frame length */

/** GMAC clock speed */
#define GMAC_MCK_SPEED_240MHZ        (240*1000*1000)
#define GMAC_MCK_SPEED_160MHZ        (160*1000*1000)
#define GMAC_MCK_SPEED_120MHZ        (120*1000*1000)
#define GMAC_MCK_SPEED_80MHZ          (80*1000*1000)
#define GMAC_MCK_SPEED_40MHZ          (40*1000*1000)
#define GMAC_MCK_SPEED_20MHZ          (20*1000*1000)

/** GMAC maintain code default value*/
#define GMAC_MAN_CODE_VALUE    (10)

/** GMAC maintain start of frame default value*/
#define GMAC_MAN_SOF_VALUE     (1)

/** GMAC maintain read/write*/
#define GMAC_MAN_RW_TYPE       (2)

/** GMAC maintain read only*/
#define GMAC_MAN_READ_ONLY     (1)

/** GMAC address length */
#define GMAC_ADDR_LENGTH       (6)


#define GMAC_DUPLEX_HALF 0
#define GMAC_DUPLEX_FULL 1

#define GMAC_SPEED_10M      0
#define GMAC_SPEED_100M     1

/**
 * \brief Return codes for GMAC APIs.
 */
typedef enum {
	GMAC_OK = 0,         /** Operation OK */
	GMAC_TIMEOUT = 1,    /** GMAC operation timeout */
	GMAC_TX_BUSY,        /** TX in progress */
	GMAC_RX_NULL,        /** No data received */
	GMAC_SIZE_TOO_SMALL, /** Buffer size not enough */
	GMAC_PARAM,          /** Parameter error, TX packet invalid or RX size too small */
	GMAC_INVALID = 0xFF, /* Invalid */
} gmac_status_t;

/**
 * \brief Media Independent Interface (MII) type.
 */
typedef enum {
	GMAC_PHY_MII = 0,         /** MII mode */
	GMAC_PHY_RMII = 1,    /** Reduced MII mode */
	GMAC_PHY_INVALID = 0xFF, /* Invalid mode*/
} gmac_mii_mode_t;

/** Receive buffer descriptor struct */
COMPILER_PACK_SET(8)
typedef struct gmac_rx_descriptor {
	union gmac_rx_addr {
		uint32_t val;
		struct gmac_rx_addr_bm {
			uint32_t b_ownership:1, /**< User clear, GMAC sets this to 1 once it has successfully written a frame to memory */
			b_wrap:1,   /**< Marks last descriptor in receive buffer */
			addr_dw:30; /**< Address in number of DW */
		} bm;
	} addr; /**< Address, Wrap & Ownership */
	union gmac_rx_status {
		uint32_t val;
		struct gmac_rx_status_bm {
			uint32_t len:13,       /** Length of frame including FCS */
			b_fcs:1,              /** Receive buffer offset,  bits 13:12 of frame length for jumbo frame */
			b_sof:1,               /** Start of frame */
			b_eof:1,               /** End of frame */
			b_cfi:1,               /** Concatenation Format Indicator */
			vlan_priority:3,       /** VLAN priority (if VLAN detected) */
			b_priority_detected:1, /** Priority tag detected */
			b_vlan_detected:1,     /**< VLAN tag detected */
			b_type_id_match:2,     /**< Type ID match */
			b_checksumoffload:1,        /**< Checksum offload specific function */
			b_addrmatch:2,        /**< Address register match */
			b_ext_addr_match:1,    /**< External address match found */
			reserved:1,
			b_uni_hash_match:1,    /**< Unicast hash match */
			b_multi_hash_match:1,  /**< Multicast hash match */
			b_boardcast_detect:1;  /**< Global broadcast address detected */
		} bm;
	} status;
} gmac_rx_descriptor_t;

/** Transmit buffer descriptor struct */
COMPILER_PACK_SET(8)
typedef struct gmac_tx_descriptor {
	uint32_t addr;
	union gmac_tx_status {
		uint32_t val;
		struct gmac_tx_status_bm {
			uint32_t len:14, /**< Length of buffer */
			reserved:1,
			b_last_buffer:1, /**< Last buffer (in the current frame) */
			b_no_crc:1,      /**< No CRC */
			reserved1:3,
			b_checksumoffload:3,    /**< Transmit checksum generation offload errors */
			reserved2:3,
			b_lco:1,         /**< Late collision, transmit error detected */
			b_exhausted:1,   /**< Buffer exhausted in mid frame */
			b_underrun:1,    /**< Transmit underrun */
			b_error:1,       /**< Retry limit exceeded, error detected */
			b_wrap:1,        /**< Marks last descriptor in TD list */
			b_used:1;        /**< User clear, GMAC sets this to 1 once a frame has been successfully transmitted */
		} bm;
	} status;
} gmac_tx_descriptor_t;

COMPILER_PACK_RESET()

/**
 * \brief Input parameters when initializing the gmac module mode.
 */
typedef struct gmac_options {
	/*  Enable/Disable CopyAllFrame */
	uint8_t uc_copy_all_frame;
	/* Enable/Disable NoBroadCast */
	uint8_t uc_no_boardcast;
	/* MAC address */
	uint8_t uc_mac_addr[GMAC_ADDR_LENGTH];
} gmac_options_t;

/** RX callback */
typedef void (*gmac_dev_tx_cb_t) (uint32_t ul_status);
/** Wakeup callback */
typedef void (*gmac_dev_wakeup_cb_t) (void);

/**
 * GMAC driver structure.
 */
typedef struct gmac_device {

	/** Pointer to HW register base */
	Gmac *p_hw;
	/**
	 * Pointer to allocated TX buffer.
	 * Section 3.6 of AMBA 2.0 spec states that burst should not cross
	 * 1K Boundaries.
	 * Receive buffer manager writes are burst of 2 words => 3 lsb bits
	 * of the address shall be set to 0.
	 */
	uint8_t *p_tx_buffer;
	/** Pointer to allocated RX buffer */
	uint8_t *p_rx_buffer;
	/** Pointer to Rx TDs (must be 8-byte aligned) */
	gmac_rx_descriptor_t *p_rx_dscr;
	/** Pointer to Tx TDs (must be 8-byte aligned) */
	gmac_tx_descriptor_t *p_tx_dscr;
	/** Optional callback to be invoked once a frame has been received */
	gmac_dev_tx_cb_t func_rx_cb;
	/** Optional callback to be invoked once several TDs have been released */
	gmac_dev_wakeup_cb_t func_wakeup_cb;
	/** Optional callback list to be invoked once TD has been processed */
	gmac_dev_tx_cb_t *func_tx_cb_list;
	/** RX TD list size */
	uint16_t us_rx_list_size;
	/** RX index for current processing TD */
	uint16_t us_rx_idx;
	/** TX TD list size */
	uint16_t us_tx_list_size;
	/** Circular buffer head pointer by upper layer (buffer to be sent) */
	uint16_t us_tx_head;
	/** Circular buffer tail pointer incremented by handlers (buffer sent) */
	uint16_t us_tx_tail;

	/** Number of free TD before wakeup callback is invoked */
	uint8_t uc_wakeup_threshold;
} gmac_device_t;

/**
 * \brief Write network control value.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param ul_ncr   Network control value.
 */
static inline void gmac_network_control(Gmac* p_gmac, uint32_t ul_ncr)
{
	p_gmac->GMAC_NCR = ul_ncr;
}

/**
 * \brief Get network control value.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 */

static inline uint32_t gmac_get_network_control(Gmac* p_gmac)
{
	return p_gmac->GMAC_NCR;
}

/**
 * \brief Enable/Disable GMAC receive.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to disable GMAC receiver, else to enable it.
 */
static inline void gmac_enable_receive(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCR |= GMAC_NCR_RXEN;
	} else {
		p_gmac->GMAC_NCR &= ~GMAC_NCR_RXEN;
	}
}

/**
 * \brief Enable/Disable GMAC transmit.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to disable GMAC transmit, else to enable it.
 */
static inline void gmac_enable_transmit(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCR |= GMAC_NCR_TXEN;
	} else {
		p_gmac->GMAC_NCR &= ~GMAC_NCR_TXEN;
	}
}

/**
 * \brief Enable/Disable GMAC management.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to disable GMAC management, else to enable it.
 */
static inline void gmac_enable_management(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCR |= GMAC_NCR_MPE;
	} else {
		p_gmac->GMAC_NCR &= ~GMAC_NCR_MPE;
	}
}

/**
 * \brief Clear all statistics registers.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 */
static inline void gmac_clear_statistics(Gmac* p_gmac)
{
	p_gmac->GMAC_NCR |= GMAC_NCR_CLRSTAT;
}

/**
 * \brief Increase all statistics registers.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 */
static inline void gmac_increase_statistics(Gmac* p_gmac)
{
	p_gmac->GMAC_NCR |= GMAC_NCR_INCSTAT;
}

/**
 * \brief Enable/Disable statistics registers writing.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to disable the statistics registers writing, else to enable it.
 */
static inline void gmac_enable_statistics_write(Gmac* p_gmac,
		uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCR |= GMAC_NCR_WESTAT;
	} else {
		p_gmac->GMAC_NCR &= ~GMAC_NCR_WESTAT;
	}
}

/**
 * \brief In half-duplex mode, forces collisions on all received frames.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to disable the back pressure, else to enable it.
 */
static inline void gmac_enable_back_pressure(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCR |= GMAC_NCR_BP;
	} else {
		p_gmac->GMAC_NCR &= ~GMAC_NCR_BP;
	}
}

/**
 * \brief Start transmission.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 */
static inline void gmac_start_transmission(Gmac* p_gmac)
{
	p_gmac->GMAC_NCR |= GMAC_NCR_TSTART;
}

/**
 * \brief Halt transmission.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 */
static inline void gmac_halt_transmission(Gmac* p_gmac)
{
	p_gmac->GMAC_NCR |= GMAC_NCR_THALT;
}

/**
 * \brief Transmit pause frame.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 */
static inline void gmac_tx_pause_frame(Gmac* p_gmac)
{
	p_gmac->GMAC_NCR |= GMAC_NCR_TXPF;
}

/**
 * \brief Transmit zero quantum pause frame.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 */
static inline void gmac_tx_pause_zero_quantum_frame(Gmac* p_gmac)
{
	p_gmac->GMAC_NCR |= GMAC_NCR_TXZQPF;
}

/**
 * \brief Read snapshot.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 */
static inline void gmac_read_snapshot(Gmac* p_gmac)
{
	p_gmac->GMAC_NCR |= GMAC_NCR_RDS;
}

/**
 * \brief Store receivetime stamp to memory.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to normal operation, else to enable the store.
 */
static inline void gmac_store_rx_time_stamp(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCR |= GMAC_NCR_SRTSM;
	} else {
		p_gmac->GMAC_NCR &= ~GMAC_NCR_SRTSM;
	}
}

/**
 * \brief Enable PFC priority-based pause reception.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   1 to set the reception, 0 to disable.
 */
static inline void gmac_enable_pfc_pause_frame(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCR |= GMAC_NCR_ENPBPR;
	} else {
		p_gmac->GMAC_NCR &= ~GMAC_NCR_ENPBPR;
	}
}

/**
 * \brief Transmit PFC priority-based pause reception.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 */
static inline void gmac_transmit_pfc_pause_frame(Gmac* p_gmac)
{
		p_gmac->GMAC_NCR |= GMAC_NCR_TXPBPF;
}

/**
 * \brief Flush next packet.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 */
static inline void gmac_flush_next_packet(Gmac* p_gmac)
{
		p_gmac->GMAC_NCR |= GMAC_NCR_FNP;
}

/**
 * \brief Set up network configuration register.
 *
 * \param p_gmac   Pointer to the GMAC instance.
  * \param ul_cfg   Network configuration value.
 */
static inline void gmac_set_configure(Gmac* p_gmac, uint32_t ul_cfg)
{
	p_gmac->GMAC_NCFGR = ul_cfg;
}

/**
 * \brief Get network configuration.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 *
 * \return Network configuration.
 */
static inline uint32_t gmac_get_configure(Gmac* p_gmac)
{
	return p_gmac->GMAC_NCFGR;
}

/**
 * \brief Set speed.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_speed 1 to indicate 100Mbps, 0 to 10Mbps.
 */
static inline void gmac_set_speed(Gmac* p_gmac, uint8_t uc_speed)
{
	if (uc_speed) {
		p_gmac->GMAC_NCFGR |= GMAC_NCFGR_SPD;
	} else {
		p_gmac->GMAC_NCFGR &= ~GMAC_NCFGR_SPD;
	}
}

/**
 * \brief Enable/Disable Full-Duplex mode.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to disable the Full-Duplex mode, else to enable it.
 */
static inline void gmac_enable_full_duplex(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCFGR |= GMAC_NCFGR_FD;
	} else {
		p_gmac->GMAC_NCFGR &= ~GMAC_NCFGR_FD;
	}
}

/**
 * \brief Enable/Disable Copy(Receive) All Valid Frames.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to disable copying all valid frames, else to enable it.
 */
static inline void gmac_enable_copy_all(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCFGR |= GMAC_NCFGR_CAF;
	} else {
		p_gmac->GMAC_NCFGR &= ~GMAC_NCFGR_CAF;
	}
}

/**
 * \brief Enable/Disable jumbo frames (up to 10240 bytes).
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to disable the jumbo frames, else to enable it.
 */
static inline void gmac_enable_jumbo_frames(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCFGR |= GMAC_NCFGR_JFRAME;
	} else {
		p_gmac->GMAC_NCFGR &= ~GMAC_NCFGR_JFRAME;
	}
}

/**
 * \brief Disable/Enable broadcast receiving.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   1 to disable the broadcast, else to enable it.
 */
static inline void gmac_disable_broadcast(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCFGR |= GMAC_NCFGR_NBC;
	} else {
		p_gmac->GMAC_NCFGR &= ~GMAC_NCFGR_NBC;
	}
}

/**
 * \brief Enable/Disable multicast hash.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to disable the multicast hash, else to enable it.
 */
static inline void gmac_enable_multicast_hash(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCFGR |= GMAC_NCFGR_UNIHEN;
	} else {
		p_gmac->GMAC_NCFGR &= ~GMAC_NCFGR_UNIHEN;
	}
}

/**
 * \brief Enable/Disable big frames (over 1518, up to 1536).
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to disable big frames else to enable it.
 */
static inline void gmac_enable_big_frame(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCFGR |= GMAC_NCFGR_MAXFS;
	} else {
		p_gmac->GMAC_NCFGR &= ~GMAC_NCFGR_MAXFS;
	}
}

/**
 * \brief Set MDC clock divider.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param ul_mck   GMAC MCK.
 *
 * \return GMAC_OK if successfully.
 */
static inline uint8_t gmac_set_mdc_clock(Gmac* p_gmac, uint32_t ul_mck)
{
	uint32_t ul_clk;
	
	if (ul_mck > GMAC_MCK_SPEED_240MHZ) {
		return GMAC_INVALID;
	} else if (ul_mck > GMAC_MCK_SPEED_160MHZ) {
		ul_clk = GMAC_NCFGR_CLK_MCK_96;
	} else if (ul_mck > GMAC_MCK_SPEED_120MHZ) {
		ul_clk = GMAC_NCFGR_CLK_MCK_64;
	} else if (ul_mck > GMAC_MCK_SPEED_80MHZ) {
		ul_clk = GMAC_NCFGR_CLK_MCK_48;
	} else if (ul_mck > GMAC_MCK_SPEED_40MHZ) {
		ul_clk = GMAC_NCFGR_CLK_MCK_32;
	} else if (ul_mck > GMAC_MCK_SPEED_20MHZ) {
		ul_clk = GMAC_NCFGR_CLK_MCK_16;
	} else {
		ul_clk = GMAC_NCFGR_CLK_MCK_8;
	}
	p_gmac->GMAC_NCFGR &= ~GMAC_NCFGR_CLK_Msk;
	p_gmac->GMAC_NCFGR |= ul_clk;
	return GMAC_OK;
}

/**
 * \brief Enable/Disable retry test.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to disable the GMAC receiver, else to enable it.
 */
static inline void gmac_enable_retry_test(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCFGR |= GMAC_NCFGR_RTY;
	} else {
		p_gmac->GMAC_NCFGR &= ~GMAC_NCFGR_RTY;
	}
}

/**
 * \brief Enable/Disable pause (when a valid pause frame is received).
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to disable pause frame, else to enable it.
 */
static inline void gmac_enable_pause_frame(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCFGR |= GMAC_NCFGR_PEN;
	} else {
		p_gmac->GMAC_NCFGR &= ~GMAC_NCFGR_PEN;
	}
}

/**
 * \brief Set receive buffer offset to 0 ~ 3.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 */
static inline void gmac_set_rx_buffer_offset(Gmac* p_gmac, uint8_t uc_offset)
{
	p_gmac->GMAC_NCFGR &= ~GMAC_NCFGR_RXBUFO_Msk;
	p_gmac->GMAC_NCFGR |= GMAC_NCFGR_RXBUFO(uc_offset);
}

/**
 * \brief Enable/Disable receive length field checking.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to disable receive length field checking, else to enable it.
 */
static inline void gmac_enable_rx_length_check(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCFGR |= GMAC_NCFGR_LFERD;
	} else {
		p_gmac->GMAC_NCFGR &= ~GMAC_NCFGR_LFERD;
	}
}

/**
 * \brief Enable/Disable discarding FCS field of received frames.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to disable discarding FCS field of received frames, else to enable it.
 */
static inline void gmac_enable_discard_fcs(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCFGR |= GMAC_NCFGR_RFCS;
	} else {
		p_gmac->GMAC_NCFGR &= ~GMAC_NCFGR_RFCS;
	}
}


/**
 * \brief Enable/Disable frames to be received in half-duplex mode
 * while transmitting.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to disable the received in half-duplex mode, else to enable it.
 */
static inline void gmac_enable_efrhd(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCFGR |= GMAC_NCFGR_EFRHD;
	} else {
		p_gmac->GMAC_NCFGR &= ~GMAC_NCFGR_EFRHD;
	}
}

/**
 * \brief Enable/Disable ignore RX FCS.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to disable ignore RX FCS, else to enable it.
 */
static inline void gmac_enable_ignore_rx_fcs(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_NCFGR |= GMAC_NCFGR_IRXFCS;
	} else {
		p_gmac->GMAC_NCFGR &= ~GMAC_NCFGR_IRXFCS;
	}
}

/**
 * \brief Get Network Status.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 *
 * \return Network status.
 */
static inline uint32_t gmac_get_status(Gmac* p_gmac)
{
	return p_gmac->GMAC_NSR;
}

/**
 * \brief Get MDIO IN pin status.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 *
 * \return MDIO IN pin status.
 */
static inline uint8_t gmac_get_MDIO(Gmac* p_gmac)
{
	return ((p_gmac->GMAC_NSR & GMAC_NSR_MDIO) > 0);
}

/**
 * \brief Check if PHY is idle.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 *
 * \return  1 if PHY is idle.
 */
static inline uint8_t gmac_is_phy_idle(Gmac* p_gmac)
{
	return ((p_gmac->GMAC_NSR & GMAC_NSR_IDLE) > 0);
}

/**
 * \brief Return transmit status.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 *
 * \return  Transmit status.
 */
static inline uint32_t gmac_get_tx_status(Gmac* p_gmac)
{
	return p_gmac->GMAC_TSR;
}

/**
 * \brief Clear transmit status.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param ul_status   Transmit status.
 */
static inline void gmac_clear_tx_status(Gmac* p_gmac, uint32_t ul_status)
{
	p_gmac->GMAC_TSR = ul_status;
}

/**
 * \brief Return receive status.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 */
static inline uint32_t gmac_get_rx_status(Gmac* p_gmac)
{
	return p_gmac->GMAC_RSR;
}

/**
 * \brief Clear receive status.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param ul_status   Receive status.
 */
static inline void gmac_clear_rx_status(Gmac* p_gmac, uint32_t ul_status)
{
	p_gmac->GMAC_RSR = ul_status;
}

/**
 * \brief Set Rx Queue.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param ul_addr   Rx queue address.
 */
static inline void gmac_set_rx_queue(Gmac* p_gmac, uint32_t ul_addr)
{
	p_gmac->GMAC_RBQB = GMAC_RBQB_ADDR_Msk & ul_addr;
}

/**
 * \brief Get Rx Queue Address.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 *
 * \return  Rx queue address.
 */
static inline uint32_t gmac_get_rx_queue(Gmac* p_gmac)
{
	return p_gmac->GMAC_RBQB;
}

/**
 * \brief Set Tx Queue.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param ul_addr  Tx queue address.
 */
static inline void gmac_set_tx_queue(Gmac* p_gmac, uint32_t ul_addr)
{
	p_gmac->GMAC_TBQB = GMAC_TBQB_ADDR_Msk & ul_addr;
}

/**
 * \brief Get Tx Queue.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 *
 * \return  Rx queue address.
 */
static inline uint32_t gmac_get_tx_queue(Gmac* p_gmac)
{
	return p_gmac->GMAC_TBQB;
}

/**
 * \brief Enable interrupt(s).
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param ul_source   Interrupt source(s) to be enabled.
 */
static inline void gmac_enable_interrupt(Gmac* p_gmac, uint32_t ul_source)
{
	p_gmac->GMAC_IER = ul_source;
}

/**
 * \brief Disable interrupt(s).
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param ul_source   Interrupt source(s) to be disabled.
 */
static inline void gmac_disable_interrupt(Gmac* p_gmac, uint32_t ul_source)
{
	p_gmac->GMAC_IDR = ul_source;
}

/**
 * \brief Return interrupt status.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 *
 * \return Interrupt status.
 */
static inline uint32_t gmac_get_interrupt_status(Gmac* p_gmac)
{
	return p_gmac->GMAC_ISR;
}

/**
 * \brief Return interrupt mask.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 *
 * \return Interrupt mask.
 */
static inline uint32_t gmac_get_interrupt_mask(Gmac* p_gmac)
{
	return p_gmac->GMAC_IMR;
}

/**
 * \brief Execute PHY maintenance command.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_phy_addr   PHY address.
 * \param uc_reg_addr   Register address.
 * \param uc_rw   1 to Read, 0 to write.
 * \param us_data   Data to be performed, write only.
 */
static inline void gmac_maintain_phy(Gmac* p_gmac,
		uint8_t uc_phy_addr, uint8_t uc_reg_addr, uint8_t uc_rw,
		uint16_t us_data)
{
	/* Wait until bus idle */
	while ((p_gmac->GMAC_NSR & GMAC_NSR_IDLE) == 0);
	/* Write maintain register */
	p_gmac->GMAC_MAN = GMAC_MAN_WTN(GMAC_MAN_CODE_VALUE)
			| GMAC_MAN_CLTTO 
			| GMAC_MAN_PHYA(uc_phy_addr)
			| GMAC_MAN_REGA(uc_reg_addr)
			| GMAC_MAN_OP((uc_rw ? GMAC_MAN_RW_TYPE : GMAC_MAN_READ_ONLY))
			| GMAC_MAN_DATA(us_data);
}

/**
 * \brief Get PHY maintenance data returned.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 *
 * \return Get PHY data.
 */
static inline uint16_t gmac_get_phy_data(Gmac* p_gmac)
{
	/* Wait until bus idle */
	while ((p_gmac->GMAC_NSR & GMAC_NSR_IDLE) == 0);
	/* Return data */
	return (uint16_t) (p_gmac->GMAC_MAN & GMAC_MAN_DATA_Msk);
}

/**
 * \brief Set Hash.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param ul_hash_top   Hash top.
 * \param ul_hash_bottom   Hash bottom.
 */
static inline void gmac_set_hash(Gmac* p_gmac, uint32_t ul_hash_top,
		uint32_t ul_hash_bottom)
{
	p_gmac->GMAC_HRB = ul_hash_bottom;
	p_gmac->GMAC_HRT = ul_hash_top;
}

/**
 * \brief Set 64 bits Hash.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param ull_hash   64 bits hash value.
 */
static inline void gmac_set_hash64(Gmac* p_gmac, uint64_t ull_hash)
{
	p_gmac->GMAC_HRB = (uint32_t) ull_hash;
	p_gmac->GMAC_HRT = (uint32_t) (ull_hash >> 32);
}

/**
 * \brief Set MAC Address.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_index  GMAC specific address register index.
 * \param p_mac_addr  GMAC address.
 */
static inline void gmac_set_address(Gmac* p_gmac, uint8_t uc_index,
		uint8_t* p_mac_addr)
{
	p_gmac->GMAC_SA[uc_index].GMAC_SAB = (p_mac_addr[3] << 24)
			| (p_mac_addr[2] << 16)
			| (p_mac_addr[1] << 8)
			| (p_mac_addr[0]);
	p_gmac->GMAC_SA[uc_index].GMAC_SAT = (p_mac_addr[5] << 8)
			| (p_mac_addr[4]);
}

/**
 * \brief Set MAC Address via 2 dword.
  *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_index  GMAC specific address register index.
 * \param ul_mac_top  GMAC top address.
 * \param ul_mac_bottom  GMAC bottom address.
 */
static inline void gmac_set_address32(Gmac* p_gmac, uint8_t uc_index,
		uint32_t ul_mac_top, uint32_t ul_mac_bottom)
{
	p_gmac->GMAC_SA[uc_index].GMAC_SAB = ul_mac_bottom;
	p_gmac->GMAC_SA[uc_index].GMAC_SAT = ul_mac_top;
}

/**
 * \brief Set MAC Address via int64.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_index  GMAC specific address register index.
 * \param ull_mac  64-bit GMAC address.
 */
static inline void gmac_set_address64(Gmac* p_gmac, uint8_t uc_index,
		uint64_t ull_mac)
{
	p_gmac->GMAC_SA[uc_index].GMAC_SAB = (uint32_t) ull_mac;
	p_gmac->GMAC_SA[uc_index].GMAC_SAT = (uint32_t) (ull_mac >> 32);
}

/**
 * \brief Select media independent interface mode.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param mode   Media independent interface mode.
 */
static inline void gmac_select_mii_mode(Gmac* p_gmac, gmac_mii_mode_t mode)
{
	switch (mode) {
		case GMAC_PHY_MII:
		case GMAC_PHY_RMII:
			p_gmac->GMAC_UR |= GMAC_UR_RMIIMII;
		break;

		default:
			p_gmac->GMAC_UR &= ~GMAC_UR_RMIIMII;
		break;
	}
}

uint8_t gmac_phy_read(Gmac* p_gmac, uint8_t uc_phy_address, uint8_t uc_address,
		uint32_t* p_value);
uint8_t gmac_phy_write(Gmac* p_gmac, uint8_t uc_phy_address,
		uint8_t uc_address, uint32_t ul_value);
void gmac_dev_init(Gmac* p_gmac, gmac_device_t* p_gmac_dev,
		gmac_options_t* p_opt);
uint32_t gmac_dev_read(gmac_device_t* p_gmac_dev, uint8_t* p_frame,
		uint32_t ul_frame_size, uint32_t* p_rcv_size);
uint32_t gmac_dev_write(gmac_device_t* p_gmac_dev, void *p_buffer,
		uint32_t ul_size, gmac_dev_tx_cb_t func_tx_cb);
uint32_t gmac_dev_get_tx_load(gmac_device_t* p_gmac_dev);
void gmac_dev_set_rx_callback(gmac_device_t* p_gmac_dev,
		gmac_dev_tx_cb_t func_rx_cb);
uint8_t gmac_dev_set_tx_wakeup_callback(gmac_device_t* p_gmac_dev,
		gmac_dev_wakeup_cb_t func_wakeup, uint8_t uc_threshold);
void gmac_dev_reset(gmac_device_t* p_gmac_dev);
void gmac_handler(gmac_device_t* p_gmac_dev);

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/// @endcond

/**
 * \page gmac_quickstart Quickstart guide for GMAC driver.
 *
 * This is the quickstart guide for the \ref gmac_group "Ethernet MAC",
 * with step-by-step instructions on how to configure and use the driver in a
 * selection of use cases.
 *
 * The use cases contain several code fragments. The code fragments in the
 * steps for setup can be copied into a custom initialization function, while
 * the steps for usage can be copied into, e.g., the main application function.
 *
 * \section gmac_basic_use_case Basic use case
 * In the basic use case, the GMAC driver are configured for:
 * - PHY component KSZ8051MNL is used
 * - GMAC uses MII mode
 * - The number of receive buffer is 16
 * - The number of transfer buffer is 8
 * - MAC address is set to 00-04-25-1c-a0-02
 * - IP address is set to 192.168.0.2
 * - IP address is set to 192.168.0.2
 * - Gateway is set to 192.168.0.1
 * - Network mask is 255.255.255.0
 * - PHY operation max retry count is 1000000
 * - GMAC is configured to not support copy all frame and support broadcast
 * - The data will be read from the ethernet
 *
 * \section gmac_basic_use_case_setup Setup steps
 *
 * \subsection gmac_basic_use_case_setup_prereq Prerequisites
 * -# \ref sysclk_group "System Clock Management (sysclock)"
 * -# \ref pmc_group "Power Management Controller (pmc)"
 * -# \ref ksz8051mnl_ethernet_phy_group "PHY component (KSZ8051MNL)"
 *
 * \subsection gmac_basic_use_case_setup_code Example code
 * Content of conf_eth.h
 * \code
 * #define GMAC_RX_BUFFERS                               16
 * #define GMAC_TX_BUFFERS                               8
 * #define MAC_PHY_RETRY_MAX                             1000000
 * #define ETHERNET_CONF_ETHADDR0                        0x00
 * #define ETHERNET_CONF_ETHADDR0                        0x00
 * #define ETHERNET_CONF_ETHADDR1                        0x04
 * #define ETHERNET_CONF_ETHADDR2                        0x25
 * #define ETHERNET_CONF_ETHADDR3                        0x1C
 * #define ETHERNET_CONF_ETHADDR4                        0xA0
 * #define ETHERNET_CONF_ETHADDR5                        0x02
 * #define ETHERNET_CONF_IPADDR0                         192
 * #define ETHERNET_CONF_IPADDR1                         168
 * #define ETHERNET_CONF_IPADDR2                         0
 * #define ETHERNET_CONF_IPADDR3                         2
 * #define ETHERNET_CONF_GATEWAY_ADDR0                   192
 * #define ETHERNET_CONF_GATEWAY_ADDR1                   168
 * #define ETHERNET_CONF_GATEWAY_ADDR2                   0
 * #define ETHERNET_CONF_GATEWAY_ADDR3                   1
 * #define ETHERNET_CONF_NET_MASK0                       255
 * #define ETHERNET_CONF_NET_MASK1                       255
 * #define ETHERNET_CONF_NET_MASK2                       255
 * #define ETHERNET_CONF_NET_MASK3                       0
 * #define ETH_PHY_MODE                                  ETH_PHY_MODE
 * \endcode
 *
 * A specific gmac device and the receive data buffer must be defined; another ul_frm_size should be defined
 * to trace the actual size of the data received.
 * \code
 * static gmac_device_t gs_gmac_dev;
 * static volatile uint8_t gs_uc_eth_buffer[GMAC_FRAME_LENTGH_MAX];
 *
 * uint32_t ul_frm_size;
 * \endcode
 *
 * Add to application C-file:
 * \code
 *   void gmac_init(void)
 *   {
 *       sysclk_init();
 *
 *       board_init();
 *
 *       pmc_enable_periph_clk(ID_GMAC);
 *
 *       gmac_option.uc_copy_all_frame = 0;
 *       gmac_option.uc_no_boardcast = 0;
 *       memcpy(gmac_option.uc_mac_addr, gs_uc_mac_address, sizeof(gs_uc_mac_address));
 *       gs_gmac_dev.p_hw = GMAC;
 *
 *       gmac_dev_init(GMAC, &gs_gmac_dev, &gmac_option);
 *
 *       NVIC_EnableIRQ(GMAC_IRQn);
 *
 *       ethernet_phy_init(GMAC, BOARD_GMAC_PHY_ADDR, sysclk_get_cpu_hz());
 * 
 *       ethernet_phy_auto_negotiate(GMAC, BOARD_GMAC_PHY_ADDR);
 *
 *       ethernet_phy_set_link(GMAC, BOARD_GMAC_PHY_ADDR, 1);
 * \endcode
 *
 * \subsection gmac_basic_use_case_setup_flow Workflow
 * -# Ensure that conf_eth.h is present and contains the
 * following configuration symbol. This configuration file is used
 * by the driver and should not be included by the user.
 *   - \code
 *        #define GMAC_RX_BUFFERS                               16
 *        #define GMAC_TX_BUFFERS                               8
 *        #define MAC_PHY_RETRY_MAX                             1000000
 *        #define ETHERNET_CONF_ETHADDR0                        0x00
 *        #define ETHERNET_CONF_ETHADDR0                        0x00
 *        #define ETHERNET_CONF_ETHADDR1                        0x04
 *        #define ETHERNET_CONF_ETHADDR2                        0x25
 *        #define ETHERNET_CONF_ETHADDR3                        0x1C
 *        #define ETHERNET_CONF_ETHADDR4                        0xA0
 *        #define ETHERNET_CONF_ETHADDR5                        0x02
 *        #define ETHERNET_CONF_IPADDR0                         192
 *        #define ETHERNET_CONF_IPADDR1                         168
 *        #define ETHERNET_CONF_IPADDR2                         0
 *        #define ETHERNET_CONF_IPADDR3                         2
 *        #define ETHERNET_CONF_GATEWAY_ADDR0                   192
 *        #define ETHERNET_CONF_GATEWAY_ADDR1                   168
 *        #define ETHERNET_CONF_GATEWAY_ADDR2                   0
 *        #define ETHERNET_CONF_GATEWAY_ADDR3                   1
 *        #define ETHERNET_CONF_NET_MASK0                       255
 *        #define ETHERNET_CONF_NET_MASK1                       255
 *        #define ETHERNET_CONF_NET_MASK2                       255
 *        #define ETHERNET_CONF_NET_MASK3                       0
 *        #define ETH_PHY_MODE                                  GMAC_PHY_MII
 *   \endcode
 * -# Enable the system clock:
 *   - \code sysclk_init(); \endcode
 * -# Enable PIO configurations for GMAC:
 *   - \code board_init(); \endcode
 * -# Enable PMC clock for GMAC:
 *   - \code pmc_enable_periph_clk(ID_GMAC); \endcode
 * -# Set the GMAC options; it's set to copy all frame and support broadcast:
 *   - \code
 *         gmac_option.uc_copy_all_frame = 0;
 *         gmac_option.uc_no_boardcast = 0;
 *         memcpy(gmac_option.uc_mac_addr, gs_uc_mac_address, sizeof(gs_uc_mac_address));
 *         gs_gmac_dev.p_hw = GMAC;
 * \endcode
 * -# Initialize GMAC device with the filled option:
 *   - \code
 *         gmac_dev_init(GMAC, &gs_gmac_dev, &gmac_option);
 * \endcode
 * -# Enable the interrupt service for GMAC:
 *   - \code
 *         NVIC_EnableIRQ(GMAC_IRQn);
 * \endcode
 * -# Initialize the PHY component:
 *   - \code
 *         ethernet_phy_init(GMAC, BOARD_GMAC_PHY_ADDR, sysclk_get_cpu_hz());
 * \endcode
  * -# The link will be established based on auto negotiation.
 *   - \code
 *         ethernet_phy_auto_negotiate(GMAC, BOARD_GMAC_PHY_ADDR);
 * \endcode
 * -# Establish the ethernet link; the network can be worked from now on:
 *   - \code
 *         ethernet_phy_set_link(GMAC, BOARD_GMAC_PHY_ADDR, 1);
 * \endcode
 *
 * \section gmac_basic_use_case_usage Usage steps
 * \subsection gmac_basic_use_case_usage_code Example code
 * Add to, e.g., main loop in application C-file:
 * \code
 *    gmac_dev_read(&gs_gmac_dev, (uint8_t *) gs_uc_eth_buffer, sizeof(gs_uc_eth_buffer), &ul_frm_size));
 * \endcode
 *
 * \subsection gmac_basic_use_case_usage_flow Workflow
 * -# Start reading the data from the ethernet:
 *   - \code gmac_dev_read(&gs_gmac_dev, (uint8_t *) gs_uc_eth_buffer, sizeof(gs_uc_eth_buffer), &ul_frm_size)); \endcode
 */

#endif /* GMAC_H_INCLUDED */
