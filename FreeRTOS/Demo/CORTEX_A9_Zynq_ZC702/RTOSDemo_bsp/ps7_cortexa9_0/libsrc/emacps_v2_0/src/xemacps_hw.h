/******************************************************************************
*
* Copyright (C) 2010 - 2014 Xilinx, Inc.  All rights reserved.
*
* Permission is hereby granted, free of charge, to any person obtaining a copy
* of this software and associated documentation files (the "Software"), to deal 
* in the Software without restriction, including without limitation the rights
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
* copies of the Software, and to permit persons to whom the Software is
* furnished to do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in
* all copies or substantial portions of the Software.
*
* Use of the Software is limited solely to applications:
* (a) running on a Xilinx device, or
* (b) that interact with a Xilinx device through a bus or interconnect.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
* XILINX  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF 
* OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
* SOFTWARE.
*
* Except as contained in this notice, the name of the Xilinx shall not be used
* in advertising or otherwise to promote the sale, use or other dealings in
* this Software without prior written authorization from Xilinx.
*
******************************************************************************/
/*****************************************************************************/
/**
*
* @file xemacps_hw.h
* @addtogroup emacps_v2_0
* @{
*
* This header file contains identifiers and low-level driver functions (or
* macros) that can be used to access the PS Ethernet MAC (XEmacPs) device.
* High-level driver functions are defined in xemacps.h.
*
* @note
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -------------------------------------------------------
* 1.00a wsy  01/10/10 First release.
* 1.02a asa  11/05/12 Added hash defines for DMACR burst length configuration.
* 1.05a kpc  28/06/13 Added XEmacPs_ResetHw function prototype
* 1.06a asa  11/02/13 Changed the value for XEMACPS_RXBUF_LEN_MASK from 0x3fff
*					  to 0x1fff. This fixes the CR#744902.
* </pre>
*
******************************************************************************/

#ifndef XEMACPS_HW_H		/* prevent circular inclusions */
#define XEMACPS_HW_H		/* by using protection macros */

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xil_io.h"

#ifdef __cplusplus
extern "C" {
#endif

/************************** Constant Definitions *****************************/

#define XEMACPS_MAX_MAC_ADDR     4   /**< Maxmum number of mac address
                                           supported */
#define XEMACPS_MAX_TYPE_ID      4   /**< Maxmum number of type id supported */
#define XEMACPS_BD_ALIGNMENT     4   /**< Minimum buffer descriptor alignment
                                           on the local bus */
#define XEMACPS_RX_BUF_ALIGNMENT 4   /**< Minimum buffer alignment when using
                                           options that impose alignment
                                           restrictions on the buffer data on
                                           the local bus */

/** @name Direction identifiers
 *
 *  These are used by several functions and callbacks that need
 *  to specify whether an operation specifies a send or receive channel.
 * @{
 */
#define XEMACPS_SEND        1	      /**< send direction */
#define XEMACPS_RECV        2	      /**< receive direction */
/*@}*/

/**  @name MDC clock division
 *  currently supporting 8, 16, 32, 48, 64, 96, 128, 224.
 * @{
 */
typedef enum { MDC_DIV_8 = 0, MDC_DIV_16, MDC_DIV_32, MDC_DIV_48,
	MDC_DIV_64, MDC_DIV_96, MDC_DIV_128, MDC_DIV_224
} XEmacPs_MdcDiv;

/*@}*/

#define XEMACPS_RX_BUF_SIZE 1536 /**< Specify the receive buffer size in
                                       bytes, 64, 128, ... 10240 */
#define XEMACPS_RX_BUF_UNIT   64 /**< Number of receive buffer bytes as a
                                       unit, this is HW setup */

#define XEMACPS_MAX_RXBD     128 /**< Size of RX buffer descriptor queues */
#define XEMACPS_MAX_TXBD     128 /**< Size of TX buffer descriptor queues */

#define XEMACPS_MAX_HASH_BITS 64 /**< Maximum value for hash bits. 2**6 */

/* Register offset definitions. Unless otherwise noted, register access is
 * 32 bit. Names are self explained here.
 */

#define XEMACPS_NWCTRL_OFFSET        0x00000000 /**< Network Control reg */
#define XEMACPS_NWCFG_OFFSET         0x00000004 /**< Network Config reg */
#define XEMACPS_NWSR_OFFSET          0x00000008 /**< Network Status reg */

#define XEMACPS_DMACR_OFFSET         0x00000010 /**< DMA Control reg */
#define XEMACPS_TXSR_OFFSET          0x00000014 /**< TX Status reg */
#define XEMACPS_RXQBASE_OFFSET       0x00000018 /**< RX Q Base address reg */
#define XEMACPS_TXQBASE_OFFSET       0x0000001C /**< TX Q Base address reg */
#define XEMACPS_RXSR_OFFSET          0x00000020 /**< RX Status reg */

#define XEMACPS_ISR_OFFSET           0x00000024 /**< Interrupt Status reg */
#define XEMACPS_IER_OFFSET           0x00000028 /**< Interrupt Enable reg */
#define XEMACPS_IDR_OFFSET           0x0000002C /**< Interrupt Disable reg */
#define XEMACPS_IMR_OFFSET           0x00000030 /**< Interrupt Mask reg */

#define XEMACPS_PHYMNTNC_OFFSET      0x00000034 /**< Phy Maintaince reg */
#define XEMACPS_RXPAUSE_OFFSET       0x00000038 /**< RX Pause Time reg */
#define XEMACPS_TXPAUSE_OFFSET       0x0000003C /**< TX Pause Time reg */

#define XEMACPS_HASHL_OFFSET         0x00000080 /**< Hash Low address reg */
#define XEMACPS_HASHH_OFFSET         0x00000084 /**< Hash High address reg */

#define XEMACPS_LADDR1L_OFFSET       0x00000088 /**< Specific1 addr low reg */
#define XEMACPS_LADDR1H_OFFSET       0x0000008C /**< Specific1 addr high reg */
#define XEMACPS_LADDR2L_OFFSET       0x00000090 /**< Specific2 addr low reg */
#define XEMACPS_LADDR2H_OFFSET       0x00000094 /**< Specific2 addr high reg */
#define XEMACPS_LADDR3L_OFFSET       0x00000098 /**< Specific3 addr low reg */
#define XEMACPS_LADDR3H_OFFSET       0x0000009C /**< Specific3 addr high reg */
#define XEMACPS_LADDR4L_OFFSET       0x000000A0 /**< Specific4 addr low reg */
#define XEMACPS_LADDR4H_OFFSET       0x000000A4 /**< Specific4 addr high reg */

#define XEMACPS_MATCH1_OFFSET        0x000000A8 /**< Type ID1 Match reg */
#define XEMACPS_MATCH2_OFFSET        0x000000AC /**< Type ID2 Match reg */
#define XEMACPS_MATCH3_OFFSET        0x000000B0 /**< Type ID3 Match reg */
#define XEMACPS_MATCH4_OFFSET        0x000000B4 /**< Type ID4 Match reg */

#define XEMACPS_STRETCH_OFFSET       0x000000BC /**< IPG Stretch reg */

#define XEMACPS_OCTTXL_OFFSET        0x00000100 /**< Octects transmitted Low
                                                      reg */
#define XEMACPS_OCTTXH_OFFSET        0x00000104 /**< Octects transmitted High
                                                      reg */

#define XEMACPS_TXCNT_OFFSET         0x00000108 /**< Error-free Frmaes
                                                      transmitted counter */
#define XEMACPS_TXBCCNT_OFFSET       0x0000010C /**< Error-free Broadcast
                                                      Frames counter*/
#define XEMACPS_TXMCCNT_OFFSET       0x00000110 /**< Error-free Multicast
                                                      Frame counter */
#define XEMACPS_TXPAUSECNT_OFFSET    0x00000114 /**< Pause Frames Transmitted
                                                      Counter */
#define XEMACPS_TX64CNT_OFFSET       0x00000118 /**< Error-free 64 byte Frames
                                                      Transmitted counter */
#define XEMACPS_TX65CNT_OFFSET       0x0000011C /**< Error-free 65-127 byte
                                                      Frames Transmitted
                                                      counter */
#define XEMACPS_TX128CNT_OFFSET      0x00000120 /**< Error-free 128-255 byte
                                                      Frames Transmitted
                                                      counter*/
#define XEMACPS_TX256CNT_OFFSET      0x00000124 /**< Error-free 256-511 byte
                                                      Frames transmitted
                                                      counter */
#define XEMACPS_TX512CNT_OFFSET      0x00000128 /**< Error-free 512-1023 byte
                                                      Frames transmitted
                                                      counter */
#define XEMACPS_TX1024CNT_OFFSET     0x0000012C /**< Error-free 1024-1518 byte
                                                      Frames transmitted
                                                      counter */
#define XEMACPS_TX1519CNT_OFFSET     0x00000130 /**< Error-free larger than
                                                      1519 byte Frames
                                                      transmitted counter */
#define XEMACPS_TXURUNCNT_OFFSET     0x00000134 /**< TX under run error
                                                      counter */

#define XEMACPS_SNGLCOLLCNT_OFFSET   0x00000138 /**< Single Collision Frame
                                                      Counter */
#define XEMACPS_MULTICOLLCNT_OFFSET  0x0000013C /**< Multiple Collision Frame
                                                      Counter */
#define XEMACPS_EXCESSCOLLCNT_OFFSET 0x00000140 /**< Excessive Collision Frame
                                                      Counter */
#define XEMACPS_LATECOLLCNT_OFFSET   0x00000144 /**< Late Collision Frame
                                                      Counter */
#define XEMACPS_TXDEFERCNT_OFFSET    0x00000148 /**< Deferred Transmission
                                                      Frame Counter */
#define XEMACPS_TXCSENSECNT_OFFSET   0x0000014C /**< Transmit Carrier Sense
                                                      Error Counter */

#define XEMACPS_OCTRXL_OFFSET        0x00000150 /**< Octects Received register
                                                      Low */
#define XEMACPS_OCTRXH_OFFSET        0x00000154 /**< Octects Received register
                                                      High */

#define XEMACPS_RXCNT_OFFSET         0x00000158 /**< Error-free Frames
                                                      Received Counter */
#define XEMACPS_RXBROADCNT_OFFSET    0x0000015C /**< Error-free Broadcast
                                                      Frames Received Counter */
#define XEMACPS_RXMULTICNT_OFFSET    0x00000160 /**< Error-free Multicast
                                                      Frames Received Counter */
#define XEMACPS_RXPAUSECNT_OFFSET    0x00000164 /**< Pause Frames
                                                      Received Counter */
#define XEMACPS_RX64CNT_OFFSET       0x00000168 /**< Error-free 64 byte Frames
                                                      Received Counter */
#define XEMACPS_RX65CNT_OFFSET       0x0000016C /**< Error-free 65-127 byte
                                                      Frames Received Counter */
#define XEMACPS_RX128CNT_OFFSET      0x00000170 /**< Error-free 128-255 byte
                                                      Frames Received Counter */
#define XEMACPS_RX256CNT_OFFSET      0x00000174 /**< Error-free 256-512 byte
                                                      Frames Received Counter */
#define XEMACPS_RX512CNT_OFFSET      0x00000178 /**< Error-free 512-1023 byte
                                                      Frames Received Counter */
#define XEMACPS_RX1024CNT_OFFSET     0x0000017C /**< Error-free 1024-1518 byte
                                                      Frames Received Counter */
#define XEMACPS_RX1519CNT_OFFSET     0x00000180 /**< Error-free 1519-max byte
                                                      Frames Received Counter */
#define XEMACPS_RXUNDRCNT_OFFSET     0x00000184 /**< Undersize Frames Received
                                                      Counter */
#define XEMACPS_RXOVRCNT_OFFSET      0x00000188 /**< Oversize Frames Received
                                                      Counter */
#define XEMACPS_RXJABCNT_OFFSET      0x0000018C /**< Jabbers Received
                                                      Counter */
#define XEMACPS_RXFCSCNT_OFFSET      0x00000190 /**< Frame Check Sequence
                                                      Error Counter */
#define XEMACPS_RXLENGTHCNT_OFFSET   0x00000194 /**< Length Field Error
                                                      Counter */
#define XEMACPS_RXSYMBCNT_OFFSET     0x00000198 /**< Symbol Error Counter */
#define XEMACPS_RXALIGNCNT_OFFSET    0x0000019C /**< Alignment Error Counter */
#define XEMACPS_RXRESERRCNT_OFFSET   0x000001A0 /**< Receive Resource Error
                                                      Counter */
#define XEMACPS_RXORCNT_OFFSET       0x000001A4 /**< Receive Overrun Counter */
#define XEMACPS_RXIPCCNT_OFFSET      0x000001A8 /**< IP header Checksum Error
                                                      Counter */
#define XEMACPS_RXTCPCCNT_OFFSET     0x000001AC /**< TCP Checksum Error
                                                      Counter */
#define XEMACPS_RXUDPCCNT_OFFSET     0x000001B0 /**< UDP Checksum Error
                                                      Counter */
#define XEMACPS_LAST_OFFSET          0x000001B4 /**< Last statistic counter
						      offset, for clearing */

#define XEMACPS_1588_SEC_OFFSET      0x000001D0 /**< 1588 second counter */
#define XEMACPS_1588_NANOSEC_OFFSET  0x000001D4 /**< 1588 nanosecond counter */
#define XEMACPS_1588_ADJ_OFFSET      0x000001D8 /**< 1588 nanosecond
						      adjustment counter */
#define XEMACPS_1588_INC_OFFSET      0x000001DC /**< 1588 nanosecond
						      increment counter */
#define XEMACPS_PTP_TXSEC_OFFSET     0x000001E0 /**< 1588 PTP transmit second
						      counter */
#define XEMACPS_PTP_TXNANOSEC_OFFSET 0x000001E4 /**< 1588 PTP transmit
						      nanosecond counter */
#define XEMACPS_PTP_RXSEC_OFFSET     0x000001E8 /**< 1588 PTP receive second
						      counter */
#define XEMACPS_PTP_RXNANOSEC_OFFSET 0x000001EC /**< 1588 PTP receive
						      nanosecond counter */
#define XEMACPS_PTPP_TXSEC_OFFSET    0x000001F0 /**< 1588 PTP peer transmit
						      second counter */
#define XEMACPS_PTPP_TXNANOSEC_OFFSET 0x000001F4 /**< 1588 PTP peer transmit
						      nanosecond counter */
#define XEMACPS_PTPP_RXSEC_OFFSET    0x000001F8 /**< 1588 PTP peer receive
						      second counter */
#define XEMACPS_PTPP_RXNANOSEC_OFFSET 0x000001FC /**< 1588 PTP peer receive
						      nanosecond counter */

/* Define some bit positions for registers. */

/** @name network control register bit definitions
 * @{
 */
#define XEMACPS_NWCTRL_FLUSH_DPRAM_MASK	0x00040000 /**< Flush a packet from
							Rx SRAM */
#define XEMACPS_NWCTRL_ZEROPAUSETX_MASK 0x00000800 /**< Transmit zero quantum
                                                         pause frame */
#define XEMACPS_NWCTRL_PAUSETX_MASK     0x00000800 /**< Transmit pause frame */
#define XEMACPS_NWCTRL_HALTTX_MASK      0x00000400 /**< Halt transmission
                                                         after current frame */
#define XEMACPS_NWCTRL_STARTTX_MASK     0x00000200 /**< Start tx (tx_go) */

#define XEMACPS_NWCTRL_STATWEN_MASK     0x00000080 /**< Enable writing to
                                                         stat counters */
#define XEMACPS_NWCTRL_STATINC_MASK     0x00000040 /**< Increment statistic
                                                         registers */
#define XEMACPS_NWCTRL_STATCLR_MASK     0x00000020 /**< Clear statistic
                                                         registers */
#define XEMACPS_NWCTRL_MDEN_MASK        0x00000010 /**< Enable MDIO port */
#define XEMACPS_NWCTRL_TXEN_MASK        0x00000008 /**< Enable transmit */
#define XEMACPS_NWCTRL_RXEN_MASK        0x00000004 /**< Enable receive */
#define XEMACPS_NWCTRL_LOOPEN_MASK      0x00000002 /**< local loopback */
/*@}*/

/** @name network configuration register bit definitions
 * @{
 */
#define XEMACPS_NWCFG_BADPREAMBEN_MASK 0x20000000 /**< disable rejection of
                                                        non-standard preamble */
#define XEMACPS_NWCFG_IPDSTRETCH_MASK  0x10000000 /**< enable transmit IPG */
#define XEMACPS_NWCFG_FCSIGNORE_MASK   0x04000000 /**< disable rejection of
                                                        FCS error */
#define XEMACPS_NWCFG_HDRXEN_MASK      0x02000000 /**< RX half duplex */
#define XEMACPS_NWCFG_RXCHKSUMEN_MASK  0x01000000 /**< enable RX checksum
                                                        offload */
#define XEMACPS_NWCFG_PAUSECOPYDI_MASK 0x00800000 /**< Do not copy pause
                                                        Frames to memory */
#define XEMACPS_NWCFG_MDC_SHIFT_MASK   18	   /**< shift bits for MDC */
#define XEMACPS_NWCFG_MDCCLKDIV_MASK   0x001C0000 /**< MDC Mask PCLK divisor */
#define XEMACPS_NWCFG_FCSREM_MASK      0x00020000 /**< Discard FCS from
                                                        received frames */
#define XEMACPS_NWCFG_LENGTHERRDSCRD_MASK 0x00010000
/**< RX length error discard */
#define XEMACPS_NWCFG_RXOFFS_MASK      0x0000C000 /**< RX buffer offset */
#define XEMACPS_NWCFG_PAUSEEN_MASK     0x00002000 /**< Enable pause RX */
#define XEMACPS_NWCFG_RETRYTESTEN_MASK 0x00001000 /**< Retry test */
#define XEMACPS_NWCFG_EXTADDRMATCHEN_MASK 0x00000200
/**< External address match enable */
#define XEMACPS_NWCFG_1000_MASK        0x00000400 /**< 1000 Mbps */
#define XEMACPS_NWCFG_1536RXEN_MASK    0x00000100 /**< Enable 1536 byte
                                                        frames reception */
#define XEMACPS_NWCFG_UCASTHASHEN_MASK 0x00000080 /**< Receive unicast hash
                                                        frames */
#define XEMACPS_NWCFG_MCASTHASHEN_MASK 0x00000040 /**< Receive multicast hash
                                                        frames */
#define XEMACPS_NWCFG_BCASTDI_MASK     0x00000020 /**< Do not receive
                                                        broadcast frames */
#define XEMACPS_NWCFG_COPYALLEN_MASK   0x00000010 /**< Copy all frames */
#define XEMACPS_NWCFG_JUMBO_MASK       0x00000008 /**< Jumbo frames */
#define XEMACPS_NWCFG_NVLANDISC_MASK   0x00000004 /**< Receive only VLAN
                                                        frames */
#define XEMACPS_NWCFG_FDEN_MASK        0x00000002 /**< full duplex */
#define XEMACPS_NWCFG_100_MASK         0x00000001 /**< 100 Mbps */
#define XEMACPS_NWCFG_RESET_MASK       0x00080000 /**< reset value */
/*@}*/

/** @name network status register bit definitaions
 * @{
 */
#define XEMACPS_NWSR_MDIOIDLE_MASK     0x00000004 /**< PHY management idle */
#define XEMACPS_NWSR_MDIO_MASK         0x00000002 /**< Status of mdio_in */
/*@}*/


/** @name MAC address register word 1 mask
 * @{
 */
#define XEMACPS_LADDR_MACH_MASK        0x0000FFFF /**< Address bits[47:32]
                                                      bit[31:0] are in BOTTOM */
/*@}*/


/** @name DMA control register bit definitions
 * @{
 */
#define XEMACPS_DMACR_RXBUF_MASK		0x00FF0000 /**< Mask bit for RX buffer
													size */
#define XEMACPS_DMACR_RXBUF_SHIFT 		16	/**< Shift bit for RX buffer
												size */
#define XEMACPS_DMACR_TCPCKSUM_MASK		0x00000800 /**< enable/disable TX
													    checksum offload */
#define XEMACPS_DMACR_TXSIZE_MASK		0x00000400 /**< TX buffer memory size */
#define XEMACPS_DMACR_RXSIZE_MASK		0x00000300 /**< RX buffer memory size */
#define XEMACPS_DMACR_ENDIAN_MASK		0x00000080 /**< endian configuration */
#define XEMACPS_DMACR_BLENGTH_MASK		0x0000001F /**< buffer burst length */
#define XEMACPS_DMACR_SINGLE_AHB_BURST	0x00000001 /**< single AHB bursts */
#define XEMACPS_DMACR_INCR4_AHB_BURST	0x00000004 /**< 4 bytes AHB bursts */
#define XEMACPS_DMACR_INCR8_AHB_BURST	0x00000008 /**< 8 bytes AHB bursts */
#define XEMACPS_DMACR_INCR16_AHB_BURST	0x00000010 /**< 16 bytes AHB bursts */
/*@}*/

/** @name transmit status register bit definitions
 * @{
 */
#define XEMACPS_TXSR_HRESPNOK_MASK    0x00000100 /**< Transmit hresp not OK */
#define XEMACPS_TXSR_URUN_MASK        0x00000040 /**< Transmit underrun */
#define XEMACPS_TXSR_TXCOMPL_MASK     0x00000020 /**< Transmit completed OK */
#define XEMACPS_TXSR_BUFEXH_MASK      0x00000010 /**< Transmit buffs exhausted
                                                       mid frame */
#define XEMACPS_TXSR_TXGO_MASK        0x00000008 /**< Status of go flag */
#define XEMACPS_TXSR_RXOVR_MASK       0x00000004 /**< Retry limit exceeded */
#define XEMACPS_TXSR_FRAMERX_MASK     0x00000002 /**< Collision tx frame */
#define XEMACPS_TXSR_USEDREAD_MASK    0x00000001 /**< TX buffer used bit set */

#define XEMACPS_TXSR_ERROR_MASK      (XEMACPS_TXSR_HRESPNOK_MASK | \
                                       XEMACPS_TXSR_URUN_MASK | \
                                       XEMACPS_TXSR_BUFEXH_MASK | \
                                       XEMACPS_TXSR_RXOVR_MASK | \
                                       XEMACPS_TXSR_FRAMERX_MASK | \
                                       XEMACPS_TXSR_USEDREAD_MASK)
/*@}*/

/**
 * @name receive status register bit definitions
 * @{
 */
#define XEMACPS_RXSR_HRESPNOK_MASK    0x00000008 /**< Receive hresp not OK */
#define XEMACPS_RXSR_RXOVR_MASK       0x00000004 /**< Receive overrun */
#define XEMACPS_RXSR_FRAMERX_MASK     0x00000002 /**< Frame received OK */
#define XEMACPS_RXSR_BUFFNA_MASK      0x00000001 /**< RX buffer used bit set */

#define XEMACPS_RXSR_ERROR_MASK      (XEMACPS_RXSR_HRESPNOK_MASK | \
                                       XEMACPS_RXSR_RXOVR_MASK | \
                                       XEMACPS_RXSR_BUFFNA_MASK)
/*@}*/

/**
 * @name interrupts bit definitions
 * Bits definitions are same in XEMACPS_ISR_OFFSET,
 * XEMACPS_IER_OFFSET, XEMACPS_IDR_OFFSET, and XEMACPS_IMR_OFFSET
 * @{
 */
#define XEMACPS_IXR_PTPPSTX_MASK    0x02000000 /**< PTP Psync transmitted */
#define XEMACPS_IXR_PTPPDRTX_MASK   0x01000000 /**< PTP Pdelay_req
						     transmitted */
#define XEMACPS_IXR_PTPSTX_MASK     0x00800000 /**< PTP Sync transmitted */
#define XEMACPS_IXR_PTPDRTX_MASK    0x00400000 /**< PTP Delay_req transmitted
						*/
#define XEMACPS_IXR_PTPPSRX_MASK    0x00200000 /**< PTP Psync received */
#define XEMACPS_IXR_PTPPDRRX_MASK   0x00100000 /**< PTP Pdelay_req received */
#define XEMACPS_IXR_PTPSRX_MASK     0x00080000 /**< PTP Sync received */
#define XEMACPS_IXR_PTPDRRX_MASK    0x00040000 /**< PTP Delay_req received */
#define XEMACPS_IXR_PAUSETX_MASK    0x00004000	/**< Pause frame transmitted */
#define XEMACPS_IXR_PAUSEZERO_MASK  0x00002000	/**< Pause time has reached
                                                     zero */
#define XEMACPS_IXR_PAUSENZERO_MASK 0x00001000	/**< Pause frame received */
#define XEMACPS_IXR_HRESPNOK_MASK   0x00000800	/**< hresp not ok */
#define XEMACPS_IXR_RXOVR_MASK      0x00000400	/**< Receive overrun occurred */
#define XEMACPS_IXR_TXCOMPL_MASK    0x00000080	/**< Frame transmitted ok */
#define XEMACPS_IXR_TXEXH_MASK      0x00000040	/**< Transmit err occurred or
                                                     no buffers*/
#define XEMACPS_IXR_RETRY_MASK      0x00000020	/**< Retry limit exceeded */
#define XEMACPS_IXR_URUN_MASK       0x00000010	/**< Transmit underrun */
#define XEMACPS_IXR_TXUSED_MASK     0x00000008	/**< Tx buffer used bit read */
#define XEMACPS_IXR_RXUSED_MASK     0x00000004	/**< Rx buffer used bit read */
#define XEMACPS_IXR_FRAMERX_MASK    0x00000002	/**< Frame received ok */
#define XEMACPS_IXR_MGMNT_MASK      0x00000001	/**< PHY management complete */
#define XEMACPS_IXR_ALL_MASK        0x00007FFF	/**< Everything! */

#define XEMACPS_IXR_TX_ERR_MASK    (XEMACPS_IXR_TXEXH_MASK |         \
                                     XEMACPS_IXR_RETRY_MASK |         \
                                     XEMACPS_IXR_URUN_MASK  |         \
                                     XEMACPS_IXR_TXUSED_MASK)


#define XEMACPS_IXR_RX_ERR_MASK    (XEMACPS_IXR_HRESPNOK_MASK |      \
                                     XEMACPS_IXR_RXUSED_MASK |        \
                                     XEMACPS_IXR_RXOVR_MASK)

/*@}*/

/** @name PHY Maintenance bit definitions
 * @{
 */
#define XEMACPS_PHYMNTNC_OP_MASK    0x40020000	/**< operation mask bits */
#define XEMACPS_PHYMNTNC_OP_R_MASK  0x20000000	/**< read operation */
#define XEMACPS_PHYMNTNC_OP_W_MASK  0x10000000	/**< write operation */
#define XEMACPS_PHYMNTNC_ADDR_MASK  0x0F800000	/**< Address bits */
#define XEMACPS_PHYMNTNC_REG_MASK   0x007C0000	/**< register bits */
#define XEMACPS_PHYMNTNC_DATA_MASK  0x00000FFF	/**< data bits */
#define XEMACPS_PHYMNTNC_PHYAD_SHIFT_MASK   23	/**< Shift bits for PHYAD */
#define XEMACPS_PHYMNTNC_PHREG_SHIFT_MASK   18	/**< Shift bits for PHREG */
/*@}*/

/* Transmit buffer descriptor status words offset
 * @{
 */
#define XEMACPS_BD_ADDR_OFFSET  0x00000000 /**< word 0/addr of BDs */
#define XEMACPS_BD_STAT_OFFSET  0x00000004 /**< word 1/status of BDs */
/*
 * @}
 */

/* Transmit buffer descriptor status words bit positions.
 * Transmit buffer descriptor consists of two 32-bit registers,
 * the first - word0 contains a 32-bit address pointing to the location of
 * the transmit data.
 * The following register - word1, consists of various information to control
 * the XEmacPs transmit process.  After transmit, this is updated with status
 * information, whether the frame was transmitted OK or why it had failed.
 * @{
 */
#define XEMACPS_TXBUF_USED_MASK  0x80000000 /**< Used bit. */
#define XEMACPS_TXBUF_WRAP_MASK  0x40000000 /**< Wrap bit, last descriptor */
#define XEMACPS_TXBUF_RETRY_MASK 0x20000000 /**< Retry limit exceeded */
#define XEMACPS_TXBUF_URUN_MASK  0x10000000 /**< Transmit underrun occurred */
#define XEMACPS_TXBUF_EXH_MASK   0x08000000 /**< Buffers exhausted */
#define XEMACPS_TXBUF_TCP_MASK   0x04000000 /**< Late collision. */
#define XEMACPS_TXBUF_NOCRC_MASK 0x00010000 /**< No CRC */
#define XEMACPS_TXBUF_LAST_MASK  0x00008000 /**< Last buffer */
#define XEMACPS_TXBUF_LEN_MASK   0x00003FFF /**< Mask for length field */
/*
 * @}
 */

/* Receive buffer descriptor status words bit positions.
 * Receive buffer descriptor consists of two 32-bit registers,
 * the first - word0 contains a 32-bit word aligned address pointing to the
 * address of the buffer. The lower two bits make up the wrap bit indicating
 * the last descriptor and the ownership bit to indicate it has been used by
 * the XEmacPs.
 * The following register - word1, contains status information regarding why
 * the frame was received (the filter match condition) as well as other
 * useful info.
 * @{
 */
#define XEMACPS_RXBUF_BCAST_MASK     0x80000000 /**< Broadcast frame */
#define XEMACPS_RXBUF_MULTIHASH_MASK 0x40000000 /**< Multicast hashed frame */
#define XEMACPS_RXBUF_UNIHASH_MASK   0x20000000 /**< Unicast hashed frame */
#define XEMACPS_RXBUF_EXH_MASK       0x08000000 /**< buffer exhausted */
#define XEMACPS_RXBUF_AMATCH_MASK    0x06000000 /**< Specific address
                                                      matched */
#define XEMACPS_RXBUF_IDFOUND_MASK   0x01000000 /**< Type ID matched */
#define XEMACPS_RXBUF_IDMATCH_MASK   0x00C00000 /**< ID matched mask */
#define XEMACPS_RXBUF_VLAN_MASK      0x00200000 /**< VLAN tagged */
#define XEMACPS_RXBUF_PRI_MASK       0x00100000 /**< Priority tagged */
#define XEMACPS_RXBUF_VPRI_MASK      0x000E0000 /**< Vlan priority */
#define XEMACPS_RXBUF_CFI_MASK       0x00010000 /**< CFI frame */
#define XEMACPS_RXBUF_EOF_MASK       0x00008000 /**< End of frame. */
#define XEMACPS_RXBUF_SOF_MASK       0x00004000 /**< Start of frame. */
#define XEMACPS_RXBUF_LEN_MASK       0x00001FFF /**< Mask for length field */

#define XEMACPS_RXBUF_WRAP_MASK      0x00000002 /**< Wrap bit, last BD */
#define XEMACPS_RXBUF_NEW_MASK       0x00000001 /**< Used bit.. */
#define XEMACPS_RXBUF_ADD_MASK       0xFFFFFFFC /**< Mask for address */
/*
 * @}
 */

/*
 * Define appropriate I/O access method to mempry mapped I/O or other
 * intarfce if necessary.
 */

#define XEmacPs_In32  Xil_In32
#define XEmacPs_Out32 Xil_Out32


/****************************************************************************/
/**
*
* Read the given register.
*
* @param    BaseAddress is the base address of the device
* @param    RegOffset is the register offset to be read
*
* @return   The 32-bit value of the register
*
* @note
* C-style signature:
*    u32 XEmacPs_ReadReg(u32 BaseAddress, u32 RegOffset)
*
*****************************************************************************/
#define XEmacPs_ReadReg(BaseAddress, RegOffset) \
    XEmacPs_In32((BaseAddress) + (RegOffset))


/****************************************************************************/
/**
*
* Write the given register.
*
* @param    BaseAddress is the base address of the device
* @param    RegOffset is the register offset to be written
* @param    Data is the 32-bit value to write to the register
*
* @return   None.
*
* @note
* C-style signature:
*    void XEmacPs_WriteReg(u32 BaseAddress, u32 RegOffset,
*         u32 Data)
*
*****************************************************************************/
#define XEmacPs_WriteReg(BaseAddress, RegOffset, Data) \
    XEmacPs_Out32((BaseAddress) + (RegOffset), (Data))

/************************** Function Prototypes *****************************/
/*
 * Perform reset operation to the emacps interface
 */
void XEmacPs_ResetHw(u32 BaseAddr);

#ifdef __cplusplus
  }
#endif

#endif /* end of protection macro */
/** @} */
