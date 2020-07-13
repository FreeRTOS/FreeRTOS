 /**
 * \file
 *
 * \brief GMAC (Ethernet MAC) driver for SAM.
 *
 * Copyright (c) 2013-2016 Atmel Corporation. All rights reserved.
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
/*
 * Support and FAQ: visit <a href="http://www.atmel.com/design-support/">Atmel Support</a>
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

//#define GMAC_RX_UNITSIZE            128     /**< Fixed size for RX buffer  */
#define GMAC_RX_UNITSIZE           1536     /**< Fixed size for RX buffer  */

//#define GMAC_TX_UNITSIZE            1518    /**< Size for ETH frame length */
#define GMAC_TX_UNITSIZE            1536    /**< Size for ETH frame length */

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
	GMAC_OK = 0,         /** 0  Operation OK */
	GMAC_TIMEOUT = 1,    /** 1  GMAC operation timeout */
	GMAC_TX_BUSY,        /** 2  TX in progress */
	GMAC_RX_NO_DATA,     /** 3  No data received */
	GMAC_SIZE_TOO_SMALL, /** 4  Buffer size not enough */
	GMAC_PARAM,          /** 5  Parameter error, TX packet invalid or RX size too small */
	GMAC_RX_ERROR,       /** 6  RX error */
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

/* This is the list of GMAC priority queue */
typedef enum  {
	GMAC_QUE_0 = 0,
#if !(SAM4E)
	GMAC_QUE_1 = 1,
	GMAC_QUE_2 = 2,
	/* Only SAM E70 Rev-B. */
	GMAC_QUE_3 = 3,
	GMAC_QUE_4 = 4,
	GMAC_QUE_5 = 5,
#endif
#  if !defined(__DOXYGEN__)
	GMAC_QUE_N,
#  endif

}gmac_quelist_t;

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
			uint32_t b_len:13,     /**  0..12  Length of frame including FCS */
			b_fcs:1,               /**  13     Receive buffer offset,  bits 13:12 of frame length for jumbo frame */
			b_sof:1,               /**  14     Start of frame */
			b_eof:1,               /**  15     End of frame */
			b_cfi:1,               /**  16     Concatenation Format Indicator */
			b_vlan_priority:3,     /**  17..19 VLAN priority (if VLAN detected) */
			b_priority_detected:1, /**  20     Priority tag detected */
			b_vlan_detected:1,     /**  21     VLAN tag detected */
			b_type_id_match:2,     /**  22..23 Type ID match */
			b_checksumoffload:1,   /**  24     Checksum offload specific function */
			b_addrmatch:2,         /**  25..26 Address register match */
			b_ext_addr_match:1,    /**  27     External address match found */
			reserved:1,            /**  28     */
			b_uni_hash_match:1,    /**  29     Unicast hash match */
			b_multi_hash_match:1,  /**  30     Multicast hash match */
			b_boardcast_detect:1;  /**  31     Global broadcast address detected */
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
			uint32_t b_len:14,   /**  0..13 Length of buffer */
			reserved:1,          /** 14            */
			b_last_buffer:1,     /** 15     Last buffer (in the current frame) */
			b_no_crc:1,          /** 16     No CRC */
			reserved1:3,         /** 17..19        */
			b_checksumoffload:3, /** 20..22 Transmit checksum generation offload errors */
			reserved2:3,         /** 23..25        */
			b_lco:1,             /** 26     Late collision, transmit error detected */
			b_exhausted:1,       /** 27     Buffer exhausted in mid frame */
			b_underrun:1,        /** 28     Transmit underrun */
			b_error:1,           /** 29     Retry limit exceeded, error detected */
			b_wrap:1,            /** 30     Marks last descriptor in TD list */
			b_used:1;            /** 31     User clear, GMAC sets this to 1 once a frame has been successfully transmitted */
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
#if( GMAC_USES_WAKEUP_CALLBACK != 0 )
	/** Optional callback to be invoked once several TDs have been released */
	gmac_dev_wakeup_cb_t func_wakeup_cb;
#endif
	/** RX index for current processing TD */
	uint32_t ul_rx_idx;
	/** Circular buffer head pointer by upper layer (buffer to be sent) */
	int32_t l_tx_head;
	/** Circular buffer tail pointer incremented by handlers (buffer sent) */
	int32_t l_tx_tail;

	/** Number of free TD before wakeup callback is invoked */
	uint32_t ul_wakeup_threshold;
} gmac_device_t;

uint8_t gmac_wait_phy(Gmac* p_gmac, const uint32_t ul_retry);

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
	__DSB();
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
static inline void gmac_set_config(Gmac* p_gmac, uint32_t ul_cfg)
{
	p_gmac->GMAC_NCFGR = ul_cfg;
}

/* Get and set DMA Configuration Register */
static inline void gmac_set_dma(Gmac* p_gmac, uint32_t ul_cfg)
{
	p_gmac->GMAC_DCFGR = ul_cfg;
}

static inline uint32_t gmac_get_dma(Gmac* p_gmac)
{
	return p_gmac->GMAC_DCFGR;
}

/**
 * \brief Get network configuration.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 *
 * \return Network configuration.
 */
static inline uint32_t gmac_get_config(Gmac* p_gmac)
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
	uint32_t ul_clk, ul_value;

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
	ul_value = p_gmac->GMAC_NCFGR;
	ul_value &= ~GMAC_NCFGR_CLK_Msk;
	ul_value |= ul_clk;
	p_gmac->GMAC_NCFGR = ul_value;
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
 * \brief Set Rx buffer size.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param ul_addr   Rx buffer.
 */
static inline void gmac_set_rx_bufsize(Gmac* p_gmac, uint32_t ul_code)
{
	p_gmac->GMAC_DCFGR = (p_gmac->GMAC_DCFGR & ~GMAC_DCFGR_DRBS_Msk)
			| GMAC_DCFGR_DRBS(ul_code);
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
		const uint8_t* p_mac_addr)
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
#if (SAM4E)
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
#else
static inline void gmac_select_mii_mode(Gmac* p_gmac, gmac_mii_mode_t mode)
{
	switch (mode) {
		case GMAC_PHY_MII:
			p_gmac->GMAC_UR |= GMAC_UR_RMII;
			break;

		case GMAC_PHY_RMII:
		default:
			p_gmac->GMAC_UR &= ~GMAC_UR_RMII;
			break;
	}
}
#endif

#if !(SAM4E)
/**
 * \brief Set 1588 timer comparison.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param seconds47   Second comparison high
 * \param seconds31   Second comparison low
 * \param nanosec     Nanosecond Comparison
 */
static inline void gmac_set_tsu_compare(Gmac *p_gmac, uint32_t seconds47, uint32_t seconds31, uint32_t nanosec)
{
	p_gmac->GMAC_SCH = seconds47;
	p_gmac->GMAC_SCL = seconds31;
	p_gmac->GMAC_NSC = nanosec;
}

/**
 * \brief Get interrupt status.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param queue_idx   Index of queue, start from 1
 *
 * \return Interrupt status.
 */
static inline uint32_t gmac_get_priority_interrupt_status(Gmac* p_gmac, gmac_quelist_t queue_idx)
{
	return p_gmac->GMAC_ISRPQ[queue_idx - 1];
}

/**
 * \brief Set base address of TX buffer.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param queue_idx   Index of queue, start from 1
 */
static inline void gmac_set_tx_priority_queue(Gmac* p_gmac, uint32_t ul_addr, gmac_quelist_t queue_idx)
{
    p_gmac->GMAC_TBQBAPQ[queue_idx - 1] = GMAC_TBQB_ADDR_Msk & ul_addr;
}

/**
 * \brief Get base address of TX buffer.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param queue_idx   Index of queue, start from 1
 *
 * \return Base address.
 */
static inline uint32_t gmac_get_tx_priority_queue(Gmac* p_gmac, gmac_quelist_t queue_idx)
{
	return p_gmac->GMAC_TBQBAPQ[queue_idx - 1];
}

/**
 * \brief Set base address of RX buffer.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param queue_idx   Index of queue, start from 1
 */
static inline void gmac_set_rx_priority_queue(Gmac* p_gmac, uint32_t ul_addr, gmac_quelist_t queue_idx)
{
    p_gmac->GMAC_RBQBAPQ[queue_idx - 1] = GMAC_RBQB_ADDR_Msk & ul_addr;
}

/**
 * \brief Get base address of RX buffer.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param queue_idx   Index of queue, start from 1
 *
 * \return Base address.
 */
static inline uint32_t gmac_get_rx_priority_queue(Gmac* p_gmac, gmac_quelist_t queue_idx)
{
	return p_gmac->GMAC_RBQBAPQ[queue_idx - 1];
}

/**
 * \brief Set size of RX buffer.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param queue_idx   Index of queue, start from 1
 */
static inline void gmac_set_rx_priority_bufsize(Gmac* p_gmac, uint32_t ul_size, gmac_quelist_t queue_idx)
{
	p_gmac->GMAC_RBSRPQ[queue_idx - 1] = ul_size;
}

/**
 * \brief Enable or disable credit-based shaping on the second highest priority queue.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to disable, 1 to enable it
 */
static inline void gmac_enable_cbsque_a(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_CBSCR |= GMAC_CBSCR_QAE;
	} else {
		p_gmac->GMAC_CBSCR &= ~GMAC_CBSCR_QAE;
	}
}

/**
 * \brief Enable or disable credit-based shaping on the highest priority queue.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param uc_enable   0 to disable, 1 to enable it
 */
static inline void gmac_enable_cbsque_b(Gmac* p_gmac, uint8_t uc_enable)
{
	if (uc_enable) {
		p_gmac->GMAC_CBSCR |= GMAC_CBSCR_QBE;
	} else {
		p_gmac->GMAC_CBSCR &= ~GMAC_CBSCR_QBE;
	}
}

/**
 * \brief Set credit-based shaping on the highest priority queue.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param idleslope_a   Value for queue A in bytes/second
 */
static inline void gmac_config_idleslope_a(Gmac* p_gmac, uint32_t idleslope_a)
{    
	p_gmac->GMAC_CBSISQA = idleslope_a;
}

/**
 * \brief Set credit-based shaping on the highest priority queue.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param idleslope_b   Value for queue B in bytes/second
 */
static inline void gmac_config_idleslope_b(Gmac* p_gmac, uint32_t idleslope_b)
{    
	p_gmac->GMAC_CBSISQB = idleslope_b;
}

/**
 * \brief Set screening type 1 register.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param reg_val  Value for screening type 1
 * \param index    Index of register
 */
static inline void gmac_write_screener_reg_1(Gmac* p_gmac, uint32_t reg_val, uint32_t index)
{
	p_gmac->GMAC_ST1RPQ[index] = reg_val;
}

/**
 * \brief Set screening type 2 register.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param reg_val  Value for screening type 2
 * \param index    Index of register
 */
static inline void gmac_write_screener_reg_2 (Gmac* p_gmac, uint32_t reg_val, uint32_t index)
{
	p_gmac->GMAC_ST2RPQ[index] = reg_val;
}

/**
 * \brief Enable interrupt(s).
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param ul_source   Interrupt source(s) to be enabled.
 * \param queue_idx   Index of queue, start from 1
 */
static inline void gmac_enable_priority_interrupt(Gmac* p_gmac, uint32_t ul_source, gmac_quelist_t queue_idx)
{
	p_gmac->GMAC_IERPQ[queue_idx - 1] = ul_source;
}

/**
 * \brief Disable interrupt(s).
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param ul_source   Interrupt source(s) to be disabled.
 * \param queue_idx   Index of queue, start from 1
 */
static inline void gmac_disable_priority_interrupt(Gmac* p_gmac, uint32_t ul_source, gmac_quelist_t queue_idx)
{
	p_gmac->GMAC_IDRPQ[queue_idx - 1] = ul_source;
}

/**
 * \brief Get interrupt mask.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param queue_idx   Index of queue, start from 1
 *
 * \return Interrupt mask.
 */
static inline uint32_t gmac_get_priority_interrupt_mask(Gmac* p_gmac, gmac_quelist_t queue_idx)
{
	return p_gmac->GMAC_IMRPQ[queue_idx - 1];
}

/**
 * \brief Set screening type 2 eherType register.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param ethertype  Ethertype compare value
 * \param index    Index of register
 */
static inline void gmac_write_ethtype_reg(Gmac* p_gmac, uint16_t ethertype, uint32_t index)
{
	p_gmac->GMAC_ST2ER[index] = (uint32_t)ethertype;
}

/**
 * \brief Set screening type 2 compare word register.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param c0reg    Compare value 0
 * \param c1reg    Compare value 1
 * \param index    Index of register
 */
static inline void gmac_write_screen_compare_reg(Gmac* p_gmac, uint32_t c0reg, uint16_t c1reg, uint32_t index)
{
	volatile uint32_t *p_PRAS;
	uint32_t ul_dlt;

	ul_dlt = (uint32_t)&(p_gmac->GMAC_ST2CW01);
	ul_dlt = ul_dlt - (uint32_t)&(p_gmac->GMAC_ST2CW00);

	p_PRAS = (volatile uint32_t *)((uint32_t)&(p_gmac->GMAC_ST2CW00) +
			index * ul_dlt);
	*p_PRAS = c0reg;
	p_PRAS = (volatile uint32_t *)((uint32_t)&(p_gmac->GMAC_ST2CW10) +
			index * ul_dlt);
	*p_PRAS = (uint32_t)c1reg;
}

#endif /* !(SAM4E) */

uint8_t gmac_phy_read(Gmac* p_gmac, uint8_t uc_phy_address, uint8_t uc_address,
		uint32_t* p_value);
uint8_t gmac_phy_write(Gmac* p_gmac, uint8_t uc_phy_address,
		uint8_t uc_address, uint32_t ul_value);
void gmac_dev_init(Gmac* p_gmac, gmac_device_t* p_gmac_dev,
		gmac_options_t* p_opt);
uint32_t gmac_dev_read(gmac_device_t* p_gmac_dev, uint8_t* p_frame,
		uint32_t ul_frame_size, uint32_t* p_rcv_size, uint8_t** pp_recv_frame);
uint32_t gmac_dev_write(gmac_device_t* p_gmac_dev, void *p_buffer,
		uint32_t ul_size);
uint32_t gmac_dev_get_tx_load(gmac_device_t* p_gmac_dev);
uint8_t gmac_dev_set_tx_wakeup_callback(gmac_device_t* p_gmac_dev,
		gmac_dev_wakeup_cb_t func_wakeup, uint8_t uc_threshold);
void gmac_dev_reset(gmac_device_t* p_gmac_dev);
void gmac_handler(gmac_device_t* p_gmac_dev);

void gmac_reset_tx_mem(gmac_device_t* p_dev);

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/// @endcond


#	define GMAC_STATS 0

#if( GMAC_STATS != 0 )

	/* Here below some code to study the types and
	frequencies of 	GMAC interrupts. */
	#define GMAC_IDX_RXUBR 0
	#define GMAC_IDX_TUR   1
	#define GMAC_IDX_RLEX  2
	#define GMAC_IDX_TFC   3
	#define GMAC_IDX_RCOMP 4
	#define GMAC_IDX_TCOMP 5
	#define GMAC_IDX_ROVR  6
	#define GMAC_IDX_HRESP 7
	#define GMAC_IDX_PFNZ  8
	#define GMAC_IDX_PTZ   9

	struct SGmacStats {
		unsigned recvCount;
		unsigned rovrCount;
		unsigned bnaCount;
		unsigned sendCount;
		unsigned sovrCount;
		unsigned incompCount;
		unsigned truncCount;

		unsigned intStatus[10];
	};
	extern struct SGmacStats gmacStats;

	struct SIntPair {
		const char *name;
		unsigned mask;
		int index;
	};

	#define MK_PAIR( NAME )   #NAME, GMAC_IER_##NAME, GMAC_IDX_##NAME
	static const struct SIntPair intPairs[] = {
		{ MK_PAIR( RXUBR ) }, /* Enable receive used bit read interrupt. */
		{ MK_PAIR( TUR   ) }, /* Enable transmit underrun interrupt. */
		{ MK_PAIR( RLEX  ) }, /* Enable retry limit  exceeded interrupt. */
		{ MK_PAIR( TFC   ) }, /* Enable transmit buffers exhausted in mid-frame interrupt. */
		{ MK_PAIR( RCOMP ) }, /* Receive complete */
		{ MK_PAIR( TCOMP ) }, /* Enable transmit complete interrupt. */
		{ MK_PAIR( ROVR  ) }, /* Enable receive overrun interrupt. */
		{ MK_PAIR( HRESP ) }, /* Enable Hresp not OK interrupt. */
		{ MK_PAIR( PFNZ  ) }, /* Enable pause frame received interrupt. */
		{ MK_PAIR( PTZ   ) }  /* Enable pause time zero interrupt. */
	};

	void gmac_show_irq_counts ();

#endif

#endif /* GMAC_H_INCLUDED */
