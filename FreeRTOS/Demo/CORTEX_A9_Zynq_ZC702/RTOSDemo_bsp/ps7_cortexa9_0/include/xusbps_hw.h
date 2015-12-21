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
 * @file xusbps_hw.h
* @addtogroup usbps_v2_1
* @{
 *
 * This header file contains identifiers and low-level driver functions (or
 * macros) that can be used to access the device. High-level driver functions
 * are defined in xusbps.h.
 *
 * <pre>
 * MODIFICATION HISTORY:
 *
 * Ver   Who  Date     Changes
 * ----- ---- -------- -----------------------------------------------
 * 1.00a wgr  10/10/10 First release
 * 1.04a nm   10/23/12 Fixed CR# 679106.
 * 1.05a kpc  07/03/13 Added XUsbPs_ResetHw function prototype
 * 2.00a kpc  04/03/14 Fixed CR#777764. Corrected max endpoint vale and masks 
 * </pre>
 *
 ******************************************************************************/
#ifndef XUSBPS_HW_H
#define XUSBPS_HW_H

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xil_io.h"

/************************** Constant Definitions *****************************/


#define XUSBPS_REG_SPACING		4

/** @name Timer 0 Register offsets
 *
 * @{
 */
#define XUSBPS_TIMER0_LD_OFFSET	0x00000080
#define XUSBPS_TIMER0_CTL_OFFSET	0x00000084
/* @} */

/** @name Timer Control Register bit mask
 *
 * @{
 */
#define XUSBPS_TIMER_RUN_MASK		0x80000000
#define XUSBPS_TIMER_STOP_MASK		0x80000000
#define XUSBPS_TIMER_RESET_MASK	0x40000000
#define XUSBPS_TIMER_REPEAT_MASK	0x01000000
/* @} */

/** @name Timer Control Register bit mask
 *
 * @{
 */
#define XUSBPS_TIMER_COUNTER_MASK	0x00FFFFFF
/* @} */

/** @name Device Hardware Parameters
 *
 * @{
 */
#define XUSBPS_HWDEVICE_OFFSET		0x0000000C

#define XUSBPS_EP_NUM_MASK		0x3E
#define XUSBPS_EP_NUM_SHIFT		1
/* @} */

/** @name Capability Regsiter offsets
 */
#define XUSBPS_HCSPARAMS_OFFSET		0x00000104

/** @name Operational Register offsets.
 * Register comments are tagged with "H:" and "D:" for Host and Device modes,
 * respectively.
 * Tags are only present for registers that have a different meaning DEVICE and
 * HOST modes. Most registers are only valid for either DEVICE or HOST mode.
 * Those registers don't have tags.
 * @{
 */
#define XUSBPS_CMD_OFFSET		0x00000140 /**< Configuration */
#define XUSBPS_ISR_OFFSET		0x00000144 /**< Interrupt Status */
#define XUSBPS_IER_OFFSET		0x00000148 /**< Interrupt Enable */
#define XUSBPS_FRAME_OFFSET		0x0000014C /**< USB Frame Index */
#define XUSBPS_LISTBASE_OFFSET		0x00000154 /**< H: Periodic List Base Address */
#define XUSBPS_DEVICEADDR_OFFSET	0x00000154 /**< D: Device Address */
#define XUSBPS_ASYNCLISTADDR_OFFSET	0x00000158 /**< H: Async List Address */
#define XUSBPS_EPLISTADDR_OFFSET	0x00000158 /**< D: Endpoint List Addr */
#define XUSBPS_TTCTRL_OFFSET		0x0000015C /**< TT Control */
#define XUSBPS_BURSTSIZE_OFFSET	0x00000160 /**< Burst Size */
#define XUSBPS_TXFILL_OFFSET		0x00000164 /**< Tx Fill Tuning */
#define XUSBPS_ULPIVIEW_OFFSET		0x00000170 /**< ULPI Viewport */
#define XUSBPS_EPNAKISR_OFFSET		0x00000178 /**< Endpoint NAK IRQ Status */
#define XUSBPS_EPNAKIER_OFFSET		0x0000017C /**< Endpoint NAK IRQ Enable */
#define XUSBPS_PORTSCR1_OFFSET		0x00000184 /**< Port Control/Status 1 */

/* NOTE: The Port Control / Status Register index is 1-based. */
#define XUSBPS_PORTSCRn_OFFSET(n)	\
		(XUSBPS_PORTSCR1_OFFSET + (((n)-1) * XUSBPS_REG_SPACING))


#define XUSBPS_OTGCSR_OFFSET	0x000001A4 /**< OTG Status and Control */
#define XUSBPS_MODE_OFFSET	0x000001A8 /**< USB Mode */
#define XUSBPS_EPSTAT_OFFSET	0x000001AC /**< Endpoint Setup Status */
#define XUSBPS_EPPRIME_OFFSET	0x000001B0 /**< Endpoint Prime */
#define XUSBPS_EPFLUSH_OFFSET	0x000001B4 /**< Endpoint Flush */
#define XUSBPS_EPRDY_OFFSET	0x000001B8 /**< Endpoint Ready */
#define XUSBPS_EPCOMPL_OFFSET	0x000001BC /**< Endpoint Complete */
#define XUSBPS_EPCR0_OFFSET	0x000001C0 /**< Endpoint Control 0 */
#define XUSBPS_EPCR1_OFFSET	0x000001C4 /**< Endpoint Control 1 */
#define XUSBPS_EPCR2_OFFSET	0x000001C8 /**< Endpoint Control 2 */
#define XUSBPS_EPCR3_OFFSET	0x000001CC /**< Endpoint Control 3 */
#define XUSBPS_EPCR4_OFFSET	0x000001D0 /**< Endpoint Control 4 */

#define XUSBPS_MAX_ENDPOINTS	12	   /**< Number of supported Endpoints in
					     *  this core. */
#define XUSBPS_EP_OUT_MASK	0x00000FFF /**< OUR (RX) endpoint mask */
#define XUSBPS_EP_IN_MASK	0x0FFF0000 /**< IN (TX) endpoint mask */
#define XUSBPS_EP_ALL_MASK	0x0FFF0FFF /**< Mask used for endpoint control
					     *  registers */
#define XUSBPS_EPCRn_OFFSET(n)	\
		(XUSBPS_EPCR0_OFFSET + ((n) * XUSBPS_REG_SPACING))

#define  XUSBPS_EPFLUSH_RX_SHIFT   0
#define  XUSBPS_EPFLUSH_TX_SHIFT  16

/* @} */



/** @name Endpoint Control Register (EPCR) bit positions.
 *  @{
 */

/* Definitions for TX Endpoint bits */
#define XUSBPS_EPCR_TXT_CONTROL_MASK	0x00000000 /**< Control Endpoint - TX */
#define XUSBPS_EPCR_TXT_ISO_MASK	0x00040000 /**< Isochronous. Endpoint */
#define XUSBPS_EPCR_TXT_BULK_MASK	0x00080000 /**< Bulk Endpoint - TX */
#define XUSBPS_EPCR_TXT_INTR_MASK	0x000C0000 /**< Interrupt Endpoint */
#define XUSBPS_EPCR_TXS_MASK		0x00010000 /**< Stall TX endpoint */
#define XUSBPS_EPCR_TXE_MASK		0x00800000 /**< Transmit enable  - TX */
#define XUSBPS_EPCR_TXR_MASK		0x00400000 /**< Data Toggle Reset Bit */


/* Definitions for RX Endpoint bits */
#define XUSBPS_EPCR_RXT_CONTROL_MASK	0x00000000 /**< Control Endpoint - RX */
#define XUSBPS_EPCR_RXT_ISO_MASK	0x00000004 /**< Isochronous Endpoint */
#define XUSBPS_EPCR_RXT_BULK_MASK	0x00000008 /**< Bulk Endpoint - RX */
#define XUSBPS_EPCR_RXT_INTR_MASK	0x0000000C /**< Interrupt Endpoint */
#define XUSBPS_EPCR_RXS_MASK		0x00000001 /**< Stall RX endpoint. */
#define XUSBPS_EPCR_RXE_MASK		0x00000080 /**< Transmit enable. - RX */
#define XUSBPS_EPCR_RXR_MASK		0x00000040 /**< Data Toggle Reset Bit */
/* @} */


/** @name USB Command Register (CR) bit positions.
 *  @{
 */
#define XUSBPS_CMD_RS_MASK	0x00000001 /**< Run/Stop */
#define XUSBPS_CMD_RST_MASK	0x00000002 /**< Controller RESET */
#define XUSBPS_CMD_FS01_MASK	0x0000000C /**< Frame List Size bit 0,1 */
#define XUSBPS_CMD_PSE_MASK	0x00000010 /**< Periodic Sched Enable */
#define XUSBPS_CMD_ASE_MASK	0x00000020 /**< Async Sched Enable */
#define XUSBPS_CMD_IAA_MASK	0x00000040 /**< IRQ Async Advance Doorbell */
#define XUSBPS_CMD_ASP_MASK	0x00000300 /**< Async Sched Park Mode Cnt */
#define XUSBPS_CMD_ASPE_MASK	0x00000800 /**< Async Sched Park Mode Enbl */
#define XUSBPS_CMD_SUTW_MASK	0x00002000 /**< Setup TripWire */
#define XUSBPS_CMD_ATDTW_MASK	0x00004000 /**< Add dTD TripWire */
#define XUSBPS_CMD_FS2_MASK	0x00008000 /**< Frame List Size bit 2 */
#define XUSBPS_CMD_ITC_MASK	0x00FF0000 /**< IRQ Threshold Control */
/* @} */


/**
 * @name Interrupt Threshold
 * These definitions are used by software to set the maximum rate at which the
 * USB controller will generate interrupt requests. The interrupt interval is
 * given in number of micro-frames.
 *
 * USB defines a full-speed 1 ms frame time indicated by a Start Of Frame (SOF)
 * packet each and every 1ms. USB also defines a high-speed micro-frame with a
 * 125us frame time. For each micro-frame a SOF (Start Of Frame) packet is
 * generated. Data is sent in between the SOF packets. The interrupt threshold
 * defines how many micro-frames the controller waits before issuing an
 * interrupt after data has been received.
 *
 * For a threshold of 0 the controller will issue an interrupt immediately
 * after the last byte of the data has been received. For a threshold n>0 the
 * controller will wait for n micro-frames before issuing an interrupt.
 *
 * Therefore, a setting of 8 micro-frames (default) means that the controller
 * will issue at most 1 interrupt per millisecond.
 *
 * @{
 */
#define XUSBPS_CMD_ITHRESHOLD_0	0x00 /**< Immediate interrupt. */
#define XUSBPS_CMD_ITHRESHOLD_1	0x01 /**< 1 micro-frame */
#define XUSBPS_CMD_ITHRESHOLD_2	0x02 /**< 2 micro-frames */
#define XUSBPS_CMD_ITHRESHOLD_4	0x04 /**< 4 micro-frames */
#define XUSBPS_CMD_ITHRESHOLD_8	0x08 /**< 8 micro-frames */
#define XUSBPS_CMD_ITHRESHOLD_16	0x10 /**< 16 micro-frames */
#define XUSBPS_CMD_ITHRESHOLD_32	0x20 /**< 32 micro-frames */
#define XUSBPS_CMD_ITHRESHOLD_64	0x40 /**< 64 micro-frames */
#define XUSBPS_CMD_ITHRESHOLD_MAX	XUSBPS_CMD_ITHRESHOLD_64
#define XUSBPS_CMD_ITHRESHOLD_DEFAULT	XUSBPS_CMD_ITHRESHOLD_8
/* @} */



/** @name USB Interrupt Status Register (ISR) / Interrupt Enable Register (IER)
 * bit positions.
 *  @{
 */
#define XUSBPS_IXR_UI_MASK	0x00000001 /**< USB Transaction Complete */
#define XUSBPS_IXR_UE_MASK	0x00000002 /**< Transaction Error */
#define XUSBPS_IXR_PC_MASK	0x00000004 /**< Port Change Detect */
#define XUSBPS_IXR_FRE_MASK	0x00000008 /**< Frame List Rollover */
#define XUSBPS_IXR_AA_MASK	0x00000020 /**< Async Advance */
#define XUSBPS_IXR_UR_MASK	0x00000040 /**< RESET Received */
#define XUSBPS_IXR_SR_MASK	0x00000080 /**< Start of Frame */
#define XUSBPS_IXR_SLE_MASK	0x00000100 /**< Device Controller Suspend */
#define XUSBPS_IXR_ULPI_MASK	0x00000400 /**< ULPI IRQ */
#define XUSBPS_IXR_HCH_MASK	0x00001000 /**< Host Controller Halted
						* Read Only */
#define XUSBPS_IXR_RCL_MASK	0x00002000 /**< USB Reclamation  Read Only */
#define XUSBPS_IXR_PS_MASK	0x00004000 /**< Periodic Sched Status
						* Read Only */
#define XUSBPS_IXR_AS_MASK	0x00008000 /**< Async Sched Status Read only */
#define XUSBPS_IXR_NAK_MASK	0x00010000 /**< NAK IRQ */
#define XUSBPS_IXR_UA_MASK	0x00040000 /**< USB Host Async IRQ */
#define XUSBPS_IXR_UP_MASK	0x00080000 /**< USB Host Periodic IRQ */
#define XUSBPS_IXR_TI0_MASK	0x01000000 /**< Timer 0 Interrupt */
#define XUSBPS_IXR_TI1_MASK	0x02000000 /**< Timer 1 Interrupt */

#define XUSBPS_IXR_ALL			(XUSBPS_IXR_UI_MASK	| \
					 XUSBPS_IXR_UE_MASK		| \
					 XUSBPS_IXR_PC_MASK	| \
					 XUSBPS_IXR_FRE_MASK	| \
					 XUSBPS_IXR_AA_MASK	| \
					 XUSBPS_IXR_UR_MASK		| \
					 XUSBPS_IXR_SR_MASK		| \
					 XUSBPS_IXR_SLE_MASK	| \
					 XUSBPS_IXR_ULPI_MASK		| \
					 XUSBPS_IXR_HCH_MASK	| \
					 XUSBPS_IXR_RCL_MASK	| \
					 XUSBPS_IXR_PS_MASK | \
					 XUSBPS_IXR_AS_MASK		| \
					 XUSBPS_IXR_NAK_MASK		| \
					 XUSBPS_IXR_UA_MASK	| \
					 XUSBPS_IXR_UP_MASK | \
					 XUSBPS_IXR_TI0_MASK | \
					 XUSBPS_IXR_TI1_MASK)
					/**< Mask for ALL IRQ types */
/* @} */


/** @name USB Mode Register (MODE) bit positions.
 *  @{
 */
#define XUSBPS_MODE_CM_MASK		0x00000003 /**< Controller Mode Select */
#define XUSBPS_MODE_CM_IDLE_MASK	0x00000000
#define XUSBPS_MODE_CM_DEVICE_MASK	0x00000002
#define XUSBPS_MODE_CM_HOST_MASK	0x00000003
#define XUSBPS_MODE_ES_MASK		0x00000004 /**< USB Endian Select */
#define XUSBPS_MODE_SLOM_MASK		0x00000008 /**< USB Setup Lockout Mode Disable */
#define XUSBPS_MODE_SDIS_MASK		0x00000010
#define XUSBPS_MODE_VALID_MASK		0x0000001F

/* @} */


/** @name USB Device Address Register (DEVICEADDR) bit positions.
 *  @{
 */
#define XUSBPS_DEVICEADDR_DEVICEAADV_MASK	0x01000000
					/**< Device Addr Auto Advance */
#define XUSBPS_DEVICEADDR_ADDR_MASK		0xFE000000
					/**< Device Address */
#define XUSBPS_DEVICEADDR_ADDR_SHIFT		25
					/**< Address shift */
#define XUSBPS_DEVICEADDR_MAX			127
					/**< Biggest allowed address */
/* @} */

/** @name USB TT Control Register (TTCTRL) bit positions.
 *  @{
 */
#define XUSBPS_TTCTRL_HUBADDR_MASK	0x7F000000 /**< TT Hub Address */
/* @} */


/** @name USB Burst Size Register (BURSTSIZE) bit posisions.
 *  @{
 */
#define XUSBPS_BURSTSIZE_RX_MASK	0x000000FF /**< RX Burst Length */
#define XUSBPS_BURSTSIZE_TX_MASK	0x0000FF00 /**< TX Burst Length */
/* @} */


/** @name USB Tx Fill Tuning Register (TXFILL) bit positions.
 *  @{
 */
#define XUSBPS_TXFILL_OVERHEAD_MASK	0x000000FF
					/**< Scheduler Overhead */
#define XUSBPS_TXFILL_HEALTH_MASK	0x00001F00
					/**< Scheduler Health Cntr */
#define XUSBPS_TXFILL_BURST_MASK	0x003F0000
					/**< FIFO Burst Threshold */
/* @} */


/** @name USB ULPI Viewport Register (ULPIVIEW) bit positions.
 *  @{
 */
#define XUSBPS_ULPIVIEW_DATWR_MASK	0x000000FF /**< ULPI Data Write */
#define XUSBPS_ULPIVIEW_DATRD_MASK	0x0000FF00 /**< ULPI Data Read */
#define XUSBPS_ULPIVIEW_ADDR_MASK	0x00FF0000 /**< ULPI Data Address */
#define XUSBPS_ULPIVIEW_PORT_MASK	0x07000000 /**< ULPI Port Number */
#define XUSBPS_ULPIVIEW_SS_MASK	0x08000000 /**< ULPI Synchronous State */
#define XUSBPS_ULPIVIEW_RW_MASK	0x20000000 /**< ULPI Read/Write Control */
#define XUSBPS_ULPIVIEW_RUN_MASK	0x40000000 /**< ULPI Run */
#define XUSBPS_ULPIVIEW_WU_MASK	0x80000000 /**< ULPI Wakeup */
/* @} */


/** @name Port Status Control Register bit positions.
 *  @{
 */
#define XUSBPS_PORTSCR_CCS_MASK  0x00000001 /**< Current Connect Status */
#define XUSBPS_PORTSCR_CSC_MASK  0x00000002 /**< Connect Status Change */
#define XUSBPS_PORTSCR_PE_MASK	  0x00000004 /**< Port Enable/Disable */
#define XUSBPS_PORTSCR_PEC_MASK  0x00000008 /**< Port Enable/Disable Change */
#define XUSBPS_PORTSCR_OCA_MASK  0x00000010 /**< Over-current Active */
#define XUSBPS_PORTSCR_OCC_MASK  0x00000020 /**< Over-current Change */
#define XUSBPS_PORTSCR_FPR_MASK  0x00000040 /**< Force Port Resume */
#define XUSBPS_PORTSCR_SUSP_MASK 0x00000080 /**< Suspend */
#define XUSBPS_PORTSCR_PR_MASK	  0x00000100 /**< Port Reset */
#define XUSBPS_PORTSCR_HSP_MASK  0x00000200 /**< High Speed Port */
#define XUSBPS_PORTSCR_LS_MASK	  0x00000C00 /**< Line Status */
#define XUSBPS_PORTSCR_PP_MASK	  0x00001000 /**< Port Power */
#define XUSBPS_PORTSCR_PO_MASK	  0x00002000 /**< Port Owner */
#define XUSBPS_PORTSCR_PIC_MASK  0x0000C000 /**< Port Indicator Control */
#define XUSBPS_PORTSCR_PTC_MASK  0x000F0000 /**< Port Test Control */
#define XUSBPS_PORTSCR_WKCN_MASK 0x00100000 /**< Wake on Connect Enable */
#define XUSBPS_PORTSCR_WKDS_MASK 0x00200000 /**< Wake on Disconnect Enable */
#define XUSBPS_PORTSCR_WKOC_MASK 0x00400000 /**< Wake on Over-current Enable */
#define XUSBPS_PORTSCR_PHCD_MASK 0x00800000 /**< PHY Low Power Suspend -
						* Clock Disable */
#define XUSBPS_PORTSCR_PFSC_MASK 0x01000000 /**< Port Force Full Speed
						* Connect */
#define XUSBPS_PORTSCR_PSPD_MASK 0x0C000000 /**< Port Speed */
/* @} */


/** @name On-The-Go Status Control Register (OTGCSR) bit positions.
 *  @{
 */
#define XUSBPS_OTGSC_VD_MASK	 0x00000001 /**< VBus Discharge Bit */
#define XUSBPS_OTGSC_VC_MASK	 0x00000002 /**< VBus Charge Bit */
#define XUSBPS_OTGSC_HAAR_MASK	 0x00000004 /**< HW Assist Auto Reset
				 		       *  Enable Bit */
#define XUSBPS_OTGSC_OT_MASK	 0x00000008 /**< OTG Termination Bit */
#define XUSBPS_OTGSC_DP_MASK	 0x00000010 /**< Data Pulsing Pull-up
				 		       *  Enable Bit */
#define XUSBPS_OTGSC_IDPU_MASK	 0x00000020 /**< ID Pull-up Enable Bit */
#define XUSBPS_OTGSC_HADP_MASK	 0x00000040 /**< HW Assist Data Pulse
							* Enable Bit */
#define XUSBPS_OTGSC_HABA_MASK	 0x00000080 /**< USB Hardware Assist
						       *  B Disconnect to A
						       *  Connect Enable Bit */
#define XUSBPS_OTGSC_ID_MASK	 0x00000100 /**< ID Status Flag */
#define XUSBPS_OTGSC_AVV_MASK	 0x00000200 /**< USB A VBus Valid Interrupt Status Flag */
#define XUSBPS_OTGSC_ASV_MASK	 0x00000400 /**< USB A Session Valid Interrupt Status Flag */
#define XUSBPS_OTGSC_BSV_MASK	 0x00000800 /**< USB B Session Valid Status Flag */
#define XUSBPS_OTGSC_BSE_MASK	 0x00001000 /**< USB B Session End Status Flag */
#define XUSBPS_OTGSC_1MST_MASK	 0x00002000 /**< USB 1 Millisecond Timer Status Flag */
#define XUSBPS_OTGSC_DPS_MASK	 0x00004000 /**< Data Pulse Status Flag */
#define XUSBPS_OTGSC_IDIS_MASK	 0x00010000 /**< USB ID Interrupt Status Flag */
#define XUSBPS_OTGSC_AVVIS_MASK 0x00020000 /**< USB A VBus Valid Interrupt Status Flag */
#define XUSBPS_OTGSC_ASVIS_MASK 0x00040000 /**< USB A Session Valid Interrupt Status Flag */
#define XUSBPS_OTGSC_BSVIS_MASK 0x00080000 /**< USB B Session Valid Interrupt Status Flag */
#define XUSBPS_OTGSC_BSEIS_MASK 0x00100000 /**< USB B Session End Interrupt Status Flag */
#define XUSBPS_OTGSC_1MSS_MASK	 0x00200000 /**< 1 Millisecond Timer Interrupt Status Flag */
#define XUSBPS_OTGSC_DPIS_MASK	 0x00400000 /**< Data Pulse Interrupt Status Flag */
#define XUSBPS_OTGSC_IDIE_MASK	 0x01000000 /**< ID Interrupt Enable Bit */
#define XUSBPS_OTGSC_AVVIE_MASK 0x02000000 /**< USB A VBus Valid Interrupt Enable Bit */
#define XUSBPS_OTGSC_ASVIE_MASK 0x04000000 /**< USB A Session Valid Interrupt Enable Bit */
#define XUSBPS_OTGSC_BSVIE_MASK 0x08000000 /**< USB B Session Valid Interrupt Enable Bit */
#define XUSBPS_OTGSC_BSEE_MASK	 0x10000000 /**< USB B Session End Interrupt Enable Bit */
#define XUSBPS_OTGSC_1MSE_MASK	 0x20000000 /**< 1 Millisecond Timer
						* Interrupt Enable Bit */
#define XUSBPS_OTGSC_DPIE_MASK	 0x40000000 /**< Data Pulse Interrupt
							* Enable Bit */

#define XUSBPS_OTG_ISB_ALL	(XUSBPS_OTGSC_IDIS_MASK |\
				XUSBPS_OTGSC_AVVIS_MASK | \
				XUSBPS_OTGSC_ASVIS_MASK | \
				XUSBPS_OTGSC_BSVIS_MASK | \
				XUSBPS_OTGSC_BSEIS_MASK | \
				XUSBPS_OTGSC_1MSS_MASK | \
				XUSBPS_OTGSC_DPIS_MASK)
				/** Mask for All IRQ status masks */

#define XUSBPS_OTG_IEB_ALL	(XUSBPS_OTGSC_IDIE_MASK |\
				XUSBPS_OTGSC_AVVIE_MASK | \
				XUSBPS_OTGSC_ASVIE_MASK | \
				XUSBPS_OTGSC_BSVIE_MASK | \
				XUSBPS_OTGSC_BSEE_IEB_MASK | \
				XUSBPS_OTGSC_1MSE_MASK | \
				XUSBPS_OTGSC_DPIE_MASK)
				/** Mask for All IRQ Enable masks */
/* @} */


/**< Alignment of the Device Queue Head List BASE. */
#define XUSBPS_dQH_BASE_ALIGN		2048

/**< Alignment of a Device Queue Head structure. */
#define XUSBPS_dQH_ALIGN		64

/**< Alignment of a Device Transfer Descriptor structure. */
#define XUSBPS_dTD_ALIGN		32

/**< Size of one RX buffer for a OUT Transfer Descriptor. */
#define XUSBPS_dTD_BUF_SIZE		4096

/**< Maximum size of one RX/TX buffer. */
#define XUSBPS_dTD_BUF_MAX_SIZE	16*1024

/**< Alignment requirement for Transfer Descriptor buffers. */
#define XUSBPS_dTD_BUF_ALIGN		4096


/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/****************************************************************************/
/**
*
* This macro reads the given register.
*
* @param	BaseAddress is the base address for the USB registers.
* @param	RegOffset is the register offset to be read.
*
* @return	The 32-bit value of the register.
*
* @note		C-style signature:
*		u32 XUsbPs_ReadReg(u32 BaseAddress, u32 RegOffset)
*
*****************************************************************************/
#define XUsbPs_ReadReg(BaseAddress, RegOffset) \
				Xil_In32(BaseAddress + (RegOffset))


/****************************************************************************/
/**
*
* This macro writes the given register.
*
* @param	BaseAddress is the the base address for the USB registers.
* @param	RegOffset is the register offset to be written.
* @param	Data is the the 32-bit value to write to the register.
*
* @return	None.
*
* @note		C-style signature:
*		void XUsbPs_WriteReg(u32 BaseAddress, u32 RegOffset, u32 Data)
*
 *****************************************************************************/
#define XUsbPs_WriteReg(BaseAddress, RegOffset, Data) \
				Xil_Out32(BaseAddress + (RegOffset), (Data))


/************************** Function Prototypes ******************************/
/*
 * Perform reset operation to the USB PS interface
 */
void XUsbPs_ResetHw(u32 BaseAddress);
/************************** Variable Definitions ******************************/

#ifdef __cplusplus
}
#endif

#endif /* XUSBPS_L_H */
/** @} */
