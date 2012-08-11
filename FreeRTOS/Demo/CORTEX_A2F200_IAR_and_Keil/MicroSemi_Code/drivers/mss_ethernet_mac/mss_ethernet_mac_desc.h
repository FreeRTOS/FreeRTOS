/***************************************************************************//**
 * @file
 * SmartFusion MSS Ethernet MAC internal defines header file.
 *
 * (c) Copyright 2007 Actel Corporation
 *
 * SVN $Revision: 2299 $
 * SVN $Date: 2010-02-24 21:21:12 +0000 (Wed, 24 Feb 2010) $
 *******************************************************************************/
#ifndef __MSS_ETHERNET_MAC_DESC_H
#define __MSS_ETHERNET_MAC_DESC_H	1

#ifdef __cplusplus
extern "C" {
#endif 

/*******************************************************************************
 * Receive descriptor bits
 */

/***************************************************************************//**
 * Ownership bit.
 * 1 - Core10/100 owns the descriptor. <br>
 * 0 - The host owns the descriptor. <br>
 * Core10/100 will clear this bit when it completes a current frame reception or 
 * when the data buffers associated with a given descriptor are already full.
 */
#define RDES0_OWN   0x80000000UL

/***************************************************************************//**
 * Filtering fail.
 * When set, indicates that a received frame did not pass the address recognition process.
 * This bit is valid only for the last descriptor of the frame (RDES0.8 set), when the CSR6.30 (receive all) bit
 * is set and the frame is at least 64 bytes long.
 */
#define RDES0_FF    0x40000000UL

/***************************************************************************//**
 * Frame length.
 * Indicates the length, in bytes, of the data transferred into a host memory for a given frame
 * This bit is valid only when RDES0.8 (last descriptor) is set and RDES0.14 (descriptor error) is cleared.
 */
#define RDES0_FL_MASK	0x00003FFFUL
#define RDES0_FL_OFFSET	16

/***************************************************************************//**
 * Error summary.
 * This bit is a logical OR of the following bits:
 * RDES0.1 - CRC error
 * RDES0.6 - Collision seen
 * RDES0.7 - Frame too long
 * RDES0.11 - Runt frame
 * RDES0.14 - Descriptor error
 * This bit is valid only when RDES0.8 (last descriptor) is set.
 */
#define RDES0_ES    0x00008000UL

/***************************************************************************//**
 * Descriptor error.
 * Set by Core10/100 when no receive buffer was available when trying to store the received data.
 * This bit is valid only when RDES0.8 (last descriptor) is set.
 */
#define RDES0_DE    0x00004000UL

/***************************************************************************//**
 * Runt frame.
 * When set, indicates that the frame is damaged by a collision or by a premature termination before the end
 * of a collision window.
 * This bit is valid only when RDES0.8 (last descriptor) is set.
 */
#define RDES0_RF    0x00000800UL

/***************************************************************************//**
 * Multicast frame.
 * When set, indicates that the frame has a multicast address.
 * This bit is valid only when RDES0.8 (last descriptor) is set.
 */
#define RDES0_MF    0x00000400UL

/***************************************************************************//**
 * First descriptor.
 * When set, indicates that this is the first descriptor of a frame.
 */
#define RDES0_FS    0x00000200UL

/***************************************************************************//**
 * Last descriptor.
 * When set, indicates that this is the last descriptor of a frame.
 */
#define RDES0_LS    0x00000100UL

/***************************************************************************//**
 * Frame too long.
 * When set, indicates that a current frame is longer than maximum size of 1,518 bytes, as specified by 802.3.
 * TL (frame too long) in the receive descriptor has been set when the received frame is longer than
 * 1,518 bytes. This flag is valid in all receive descriptors when multiple descriptors are used for one frame.
 */
#define RDES0_TL    0x00000080UL

/***************************************************************************//**
 * Collision seen.
 * When set, indicates that a late collision was seen (collision after 64 bytes following SFD).
 * This bit is valid only when RDES0.8 (last descriptor) is set.
 */
#define RDES0_CS    0x00000040UL

/***************************************************************************//**
 * Frame type.
 * When set, indicates that the frame has a length field larger than 1,500 (Ethernet-type frame). When
 * cleared, indicates an 802.3-type frame.
 * This bit is valid only when RDES0.8 (last descriptor) is set.
 * Additionally, FT is invalid for runt frames shorter than 14 bytes.
 */
#define RDES0_FT    0x00000020UL

/***************************************************************************//**
 * Report on MII error.
 * When set, indicates that an error has been detected by a physical layer chip connected through the MII
 * interface.
 * This bit is valid only when RDES0.8 (last descriptor) is set.
 */
#define RDES0_RE    0x00000008UL

/***************************************************************************//**
 * Dribbling bit.
 * When set, indicates that the frame was not byte-aligned.
 * This bit is valid only when RDES0.8 (last descriptor) is set.
 */
#define RDES0_DB    0x00000004UL

/***************************************************************************//**
 * CRC error.
 * When set, indicates that a CRC error has occurred in the received frame.
 * This bit is valid only when RDES0.8 (last descriptor) is set.
 * Additionally, CE is not valid when the received frame is a runt frame.
 */
#define RDES0_CE    0x00000002UL

/***************************************************************************//**
 * This bit is reset for frames with a legal length.
 */
#define RDES0_ZERO  0x00000001UL

/***************************************************************************//**
 * Receive end of ring.
 * When set, indicates that this is the last descriptor in the receive descriptor ring. Core10/100 returns to the
 * first descriptor in the ring, as specified by CSR3 (start of receive list address).
 */
#define RDES1_RER   0x02000000UL

/***************************************************************************//**
 * Second address chained.
 * When set, indicates that the second buffer's address points to the next descriptor and not to the data buffer.
 * Note that RER takes precedence over RCH.
 */
#define RDES1_RCH   0x01000000UL

/***************************************************************************//**
 * Buffer 2 size.
 * Indicates the size, in bytes, of memory space used by the second data buffer. This number must be a
 * multiple of four. If it is 0, Core10/100 ignores the second data buffer and fetches the next data descriptor.
 * This number is valid only when RDES1.24 (second address chained) is cleared.
 */
#define RDES1_RBS2_MASK		0x7FF
#define RDES1_RBS2_OFFSET	11

/***************************************************************************//**
 * Buffer 1 size
 * Indicates the size, in bytes, of memory space used by the first data buffer. This number must be a multiple of
 * four. If it is 0, Core10/100 ignores the first data buffer and uses the second data buffer.
 */
#define RDES1_RBS1_MASK		0x7FF
#define RDES1_RBS1_OFFSET	0


/*******************************************************************************
 * Transmit descriptor bits
 */

/***************************************************************************//**
 * Ownership bit.
 * 1 - Core10/100 owns the descriptor.
 * 0 - The host owns the descriptor.
 * Core10/100 will clear this bit when it completes a current frame transmission or when the data buffers
 * associated with a given descriptor are empty.
 */
#define TDES0_OWN     0x80000000uL

/***************************************************************************//**
 * Error summary.
 * This bit is a logical OR of the following bits:
 * TDES0.1 - Underflow error
 * TDES0.8 - Excessive collision error
 * TDES0.9 - Late collision
 * TDES0.10 - No carrier
 * TDES0.11 - Loss of carrier
 * This bit is valid only when TDES1.30 (last descriptor) is set.
 */
#define TDES0_ES      ((uint32_t)1 << 15)

/***************************************************************************//**
 * Loss of carrier.
 * When set, indicates a loss of the carrier during a transmission.
 * This bit is valid only when TDES1.30 (last descriptor) is set.
 */
#define TDES0_LO      ((uint32_t)1 << 11)

/***************************************************************************//**
 * No carrier.
 * When set, indicates that the carrier was not asserted by an external transceiver during the transmission.
 * This bit is valid only when TDES1.30 (last descriptor) is set.
 */
#define TDES0_NC      ((uint32_t)1 << 10)

/***************************************************************************//**
 * Late collision.
 * When set, indicates that a collision was detected after transmitting 64 bytes.
 * This bit is not valid when TDES0.1 (underflow error) is set.
 * This bit is valid only when TDES1.30 (last descriptor) is set.
 */
#define TDES0_LC      ((uint32_t)1 << 9)

/***************************************************************************//**
 * Excessive collisions.
 * When set, indicates that the transmission was aborted after 16 retries.
 * This bit is valid only when TDES1.30 (last descriptor) is set.
 */
#define TDES0_EC      ((uint32_t)1 << 8)

/***************************************************************************//**
 * Collision count.
 * This field indicates the number of collisions that occurred before the end of a frame transmission.
 * This value is not valid when TDES0.8 (excessive collisions bit) is set.
 * This bit is valid only when TDES1.30 (last descriptor) is set.
 */
#define TDES0_CC_MASK	0xFu
#define TDES0_CC_OFFSET	3u

/***************************************************************************//**
 * Underflow error.
 * When set, indicates that the FIFO was empty during the frame transmission.
 * This bit is valid only when TDES1.30 (last descriptor) is set.
 */
#define TDES0_UF      ((uint32_t)1 << 1)

/***************************************************************************//**
 * Deferred.
 * When set, indicates that the frame was deferred before transmission. Deferring occurs if the carrier is detected
 * when the transmission is ready to start.
 * This bit is valid only when TDES1.30 (last descriptor) is set.
 */
#define TDES0_DE      (1)

/***************************************************************************//**
 * Interrupt on completion.
 * Setting this flag instructs Core10/100 to set CSR5.0 (transmit interrupt) immediately after processing a
 * current frame.
 * This bit is valid when TDES1.30 (last descriptor) is set or for a setup packet.
 */
#define TDES1_IC      ((uint32_t)1 << 31)

/***************************************************************************//**
 * Last descriptor.
 * When set, indicates the last descriptor of the frame.
 */
#define TDES1_LS      ((uint32_t)1 << 30)

/***************************************************************************//**
 * First descriptor.
 * When set, indicates the first descriptor of the frame.
 */
#define TDES1_FS      ((uint32_t)1 << 29)

/***************************************************************************//**
 * Filtering type.
 * This bit, together with TDES0.22 (FT0), controls a current filtering mode.
 * This bit is valid only for the setup frames.
 */
#define TDES1_FT1     ((uint32_t)1 << 28)

/***************************************************************************//**
 * Setup packet.
 * When set, indicates that this is a setup frame descriptor.
 */
#define TDES1_SET     ((uint32_t)1 << 27)

/***************************************************************************//**
 * Add CRC disable.
 * When set, Core10/100 does not append the CRC value at the end of the frame. The exception is when the
 * frame is shorter than 64 bytes and automatic byte padding is enabled. In that case, the CRC field is added,
 * despite the state of the AC flag.
 */
#define TDES1_AC      ((uint32_t)1 << 26)

/***************************************************************************//**
 * Transmit end of ring.
 * When set, indicates the last descriptor in the descriptor ring.
 */
#define TDES1_TER     ((uint32_t)1 << 25)

/***************************************************************************//**
 * Second address chained.
 * When set, indicates that the second descriptor's address points to the next descriptor and not to the data
 * buffer.
 * This bit is valid only when TDES1.25 (transmit end of ring) is reset.
 */
#define TDES1_TCH     ((uint32_t)1 << 24)

/***************************************************************************//**
 * Disabled padding.
 * When set, automatic byte padding is disabled. Core10/100 normally appends the PAD field after the INFO
 * field when the size of an actual frame is less than 64 bytes. After padding bytes, the CRC field is also
 * inserted, despite the state of the AC flag. When DPD is set, no padding bytes are appended.
 */
#define TDES1_DPD     ((uint32_t)1 << 23)

/***************************************************************************//**
 * Filtering type.
 * This bit, together with TDES0.28 (FT1), controls the current filtering mode.
 * This bit is valid only when the TDES1.27 (SET) bit is set.
 */
#define TDES1_FT0     ((uint32_t)1 << 22)

/***************************************************************************//**
 * Buffer 2 size.
 * Indicates the size, in bytes, of memory space used by the second data buffer. If it is zero, Core10/100 ignores
 * the second data buffer and fetches the next data descriptor.
 * This bit is valid only when TDES1.24 (second address chained) is cleared.
 */
#define TDES1_TBS2_MASK		0x7FF
#define TDES1_TBS2_OFFSET	11u

/***************************************************************************//**
 * Buffer 1 size.
 * Indicates the size, in bytes, of memory space used by the first data buffer. If it is 0, Core10/100 ignores the
 * first data buffer and uses the second data buffer.
 */
#define TDES1_TBS1_MASK		0x7FF
#define TDES1_TBS1_OFFSET	0u

#ifdef __cplusplus
}
#endif

#endif	/* __MSS_ETHERNET_MAC_DESC_H */

