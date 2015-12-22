/******************************************************************************
*
* Copyright (C) 2012 - 2015 Xilinx, Inc.  All rights reserved.
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
/****************************************************************************/
/**
*
* @file xaxipmon_hw.h
*
* This header file contains identifiers and basic driver functions (or
* macros) that can be used to access the AXI Performance Monitor.
*
* Refer to the device specification for more information about this driver.
*
* @note	 None.
*
* <pre>
*
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- -----  -------- -----------------------------------------------------
* 1.00a bss    02/27/12 First release
* 2.00a bss    06/23/12 Updated to support v2_00a version of IP.
* 3.00a bss    09/03/12 Deleted XAPM_AGENT_OFFSET Macro to support
*			v2_01a version of IP.
* 3.01a bss    10/25/12 To support new version of IP:
*			Added XAPM_MCXLOGEN_OFFSET and
*			XAPM_CR_EXTERNAL_TRIGGER_MASK macros.
* 4.00a bss    01/17/13 To support new version of IP:
*			Added XAPM_LATENCYID_OFFSET,
*			XAPM_CR_EVTLOG_EXTTRIGGER_MASK,
*			XAPM_LATENCYID_RID_MASK and XAPM_LATENCYID_WID_MASK
* 5.00a bss   08/26/13  To support new version of IP:
*			Added Macros XAPM_MC10_OFFSET to XAPM_MC47_OFFSET,
*			XAPM_SMC10_OFFSET to XAPM_SMC47_OFFSET.
*			Added macro XAPM_IDMASK_OFFSET, XAPM_SR_OFFSET.
*			Added XAPM_CR_IDFILTER_ENABLE_MASK,
*			XAPM_CR_WRLATENCY_START_MASK,
*			XAPM_CR_WRLATENCY_END_MASK,
*			XAPM_CR_RDLATENCY_START_MASK,
*			XAPM_CR_RDLATENCY_END_MASK, XAPM_MASKID_RID_MASK
*			and XAPM_MASKID_WID_MASK macros.
*			Renamed:
*			XAPM_LATENCYID_OFFSET to XAPM_ID_OFFSET,
*			XAPM_LATENCYID_RID_MASK to XAPM_ID_RID_MASK,
*			XAPM_LATENCYID_WID_MASK to XAPM_ID_WID_MASK.
*
* 6.2  bss  03/02/15 Added XAPM_RID_OFFSET and XAPM_RIDMASK_OFFSET to support
*					 Zynq MP APM.
* </pre>
*
*****************************************************************************/
#ifndef XAXIPMON_HW_H /* Prevent circular inclusions */
#define XAXIPMON_HW_H /* by using protection macros  */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files ********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xil_io.h"

/************************** Constant Definitions ****************************/


/**@name Register offsets of AXIMONITOR in the Device Config
 *
 * The following constants provide access to each of the registers of the
 * AXI PERFORMANCE MONITOR device.
 * @{
 */

#define XAPM_GCC_HIGH_OFFSET		0x0000	/**< Global Clock Counter
							32 to 63 bits  */
#define XAPM_GCC_LOW_OFFSET		0x0004	/**< Global Clock Counter Lower
							0-31 bits  */
#define XAPM_SI_HIGH_OFFSET		0x0020	/**< Sample Interval MSB */
#define XAPM_SI_LOW_OFFSET		0x0024	/**< Sample Interval LSB */
#define XAPM_SICR_OFFSET		0x0028	/**< Sample Interval Control
							Register */
#define XAPM_SR_OFFSET			0x002C	/**< Sample Register */
#define XAPM_GIE_OFFSET			0x0030	/**< Global Interrupt Enable
							Register */
#define XAPM_IE_OFFSET			0x0034	/**< Interrupt Enable Register */
#define XAPM_IS_OFFSET			0x0038	/**< Interrupt Status Register */

#define XAPM_MSR0_OFFSET		0x0044	/**< Metric Selector 0 Register */
#define XAPM_MSR1_OFFSET		0x0048	/**< Metric Selector 1 Register */
#define XAPM_MSR2_OFFSET		0x004C	/**< Metric Selector 2 Register */

#define XAPM_MC0_OFFSET			0x0100	/**< Metric Counter 0 Register */
#define XAPM_INC0_OFFSET		0x0104	/**< Incrementer 0 Register */
#define XAPM_RANGE0_OFFSET		0x0108	/**< Range 0 Register */
#define XAPM_MC0LOGEN_OFFSET		0x010C	/**< Metric Counter 0
							Log Enable Register */
#define XAPM_MC1_OFFSET			0x0110	/**< Metric Counter 1 Register */
#define XAPM_INC1_OFFSET		0x0114	/**< Incrementer 1 Register */
#define XAPM_RANGE1_OFFSET		0x0118	/**< Range 1 Register */
#define XAPM_MC1LOGEN_OFFSET		0x011C	/**< Metric Counter 1
							Log Enable Register */
#define XAPM_MC2_OFFSET			0x0120	/**< Metric Counter 2 Register */
#define XAPM_INC2_OFFSET		0x0124	/**< Incrementer 2 Register */
#define XAPM_RANGE2_OFFSET		0x0128	/**< Range 2 Register */
#define XAPM_MC2LOGEN_OFFSET		0x012C	/**< Metric Counter 2
							Log Enable Register */
#define XAPM_MC3_OFFSET			0x0130	/**< Metric Counter 3 Register */
#define XAPM_INC3_OFFSET		0x0134	/**< Incrementer 3 Register */
#define XAPM_RANGE3_OFFSET		0x0138	/**< Range 3 Register */
#define XAPM_MC3LOGEN_OFFSET		0x013C	/**< Metric Counter 3
							Log Enable Register */
#define XAPM_MC4_OFFSET			0x0140	/**< Metric Counter 4 Register */
#define XAPM_INC4_OFFSET		0x0144	/**< Incrementer 4 Register */
#define XAPM_RANGE4_OFFSET		0x0148	/**< Range 4 Register */
#define XAPM_MC4LOGEN_OFFSET		0x014C	/**< Metric Counter 4
							Log Enable Register */
#define XAPM_MC5_OFFSET			0x0150	/**< Metric Counter 5
							Register */
#define XAPM_INC5_OFFSET		0x0154	/**< Incrementer 5 Register */
#define XAPM_RANGE5_OFFSET		0x0158	/**< Range 5 Register */
#define XAPM_MC5LOGEN_OFFSET		0x015C	/**< Metric Counter 5
							Log Enable Register */
#define XAPM_MC6_OFFSET			0x0160	/**< Metric Counter 6
							Register */
#define XAPM_INC6_OFFSET		0x0164	/**< Incrementer 6 Register */
#define XAPM_RANGE6_OFFSET		0x0168	/**< Range 6 Register */
#define XAPM_MC6LOGEN_OFFSET		0x016C	/**< Metric Counter 6
							Log Enable Register */
#define XAPM_MC7_OFFSET			0x0170	/**< Metric Counter 7
							Register */
#define XAPM_INC7_OFFSET		0x0174	/**< Incrementer 7 Register */
#define XAPM_RANGE7_OFFSET		0x0178	/**< Range 7 Register */
#define XAPM_MC7LOGEN_OFFSET		0x017C	/**< Metric Counter 7
							Log Enable Register */
#define XAPM_MC8_OFFSET			0x0180	/**< Metric Counter 8
							Register */
#define XAPM_INC8_OFFSET		0x0184	/**< Incrementer 8 Register */
#define XAPM_RANGE8_OFFSET		0x0188	/**< Range 8 Register */
#define XAPM_MC8LOGEN_OFFSET		0x018C	/**< Metric Counter 8
							Log Enable Register */
#define XAPM_MC9_OFFSET			0x0190	/**< Metric Counter 9
							Register */
#define XAPM_INC9_OFFSET		0x0194	/**< Incrementer 9 Register */
#define XAPM_RANGE9_OFFSET		0x0198	/**< Range 9 Register */
#define XAPM_MC9LOGEN_OFFSET		0x019C	/**< Metric Counter 9
							Log Enable Register */
#define XAPM_SMC0_OFFSET		0x0200	/**< Sampled Metric Counter
							0 Register */
#define XAPM_SINC0_OFFSET		0x0204	/**< Sampled Incrementer
							0 Register */
#define XAPM_SMC1_OFFSET		0x0210	/**< Sampled Metric Counter
							1 Register */
#define XAPM_SINC1_OFFSET		0x0214	/**< Sampled Incrementer
							1 Register */
#define XAPM_SMC2_OFFSET		0x0220	/**< Sampled Metric Counter
							2 Register */
#define XAPM_SINC2_OFFSET		0x0224	/**< Sampled Incrementer
							2 Register */
#define XAPM_SMC3_OFFSET		0x0230	/**< Sampled Metric Counter
							3 Register */
#define XAPM_SINC3_OFFSET		0x0234	/**< Sampled Incrementer
							3 Register */
#define XAPM_SMC4_OFFSET		0x0240	/**< Sampled Metric Counter
							4 Register */
#define XAPM_SINC4_OFFSET		0x0244	/**< Sampled Incrementer
							4 Register */
#define XAPM_SMC5_OFFSET		0x0250	/**< Sampled Metric Counter
							5 Register */
#define XAPM_SINC5_OFFSET		0x0254	/**< Sampled Incrementer
							5 Register */
#define XAPM_SMC6_OFFSET		0x0260	/**< Sampled Metric Counter
							6 Register */
#define XAPM_SINC6_OFFSET		0x0264	/**< Sampled Incrementer
							6 Register */
#define XAPM_SMC7_OFFSET		0x0270	/**< Sampled Metric Counter
							7 Register */
#define XAPM_SINC7_OFFSET		0x0274	/**< Sampled Incrementer
							7 Register */
#define XAPM_SMC8_OFFSET		0x0280	/**< Sampled Metric Counter
							8 Register */
#define XAPM_SINC8_OFFSET		0x0284	/**< Sampled Incrementer
							8 Register */
#define XAPM_SMC9_OFFSET		0x0290	/**< Sampled Metric Counter
							9 Register */
#define XAPM_SINC9_OFFSET		0x0294	/**< Sampled Incrementer
							9 Register */

#define XAPM_MC10_OFFSET		0x01A0	/**< Metric Counter 10
							Register */
#define XAPM_MC11_OFFSET		0x01B0	/**< Metric Counter 11
							Register */
#define XAPM_MC12_OFFSET		0x0500	/**< Metric Counter 12
							Register */
#define XAPM_MC13_OFFSET		0x0510	/**< Metric Counter 13
							Register */
#define XAPM_MC14_OFFSET		0x0520	/**< Metric Counter 14
							Register */
#define XAPM_MC15_OFFSET		0x0530	/**< Metric Counter 15
							Register */
#define XAPM_MC16_OFFSET		0x0540	/**< Metric Counter 16
							Register */
#define XAPM_MC17_OFFSET		0x0550	/**< Metric Counter 17
							Register */
#define XAPM_MC18_OFFSET		0x0560	/**< Metric Counter 18
							Register */
#define XAPM_MC19_OFFSET		0x0570	/**< Metric Counter 19
							Register */
#define XAPM_MC20_OFFSET		0x0580	/**< Metric Counter 20
							Register */
#define XAPM_MC21_OFFSET		0x0590	/**< Metric Counter 21
							Register */
#define XAPM_MC22_OFFSET		0x05A0	/**< Metric Counter 22
							Register */
#define XAPM_MC23_OFFSET		0x05B0	/**< Metric Counter 23
							Register */
#define XAPM_MC24_OFFSET		0x0700	/**< Metric Counter 24
							Register */
#define XAPM_MC25_OFFSET		0x0710	/**< Metric Counter 25
							Register */
#define XAPM_MC26_OFFSET		0x0720	/**< Metric Counter 26
							Register */
#define XAPM_MC27_OFFSET		0x0730	/**< Metric Counter 27
							Register */
#define XAPM_MC28_OFFSET		0x0740	/**< Metric Counter 28
							Register */
#define XAPM_MC29_OFFSET		0x0750	/**< Metric Counter 29
							Register */
#define XAPM_MC30_OFFSET		0x0760	/**< Metric Counter 30
							Register */
#define XAPM_MC31_OFFSET		0x0770	/**< Metric Counter 31
							Register */
#define XAPM_MC32_OFFSET		0x0780	/**< Metric Counter 32
							Register */
#define XAPM_MC33_OFFSET		0x0790	/**< Metric Counter 33
							Register */
#define XAPM_MC34_OFFSET		0x07A0	/**< Metric Counter 34
							Register */
#define XAPM_MC35_OFFSET		0x07B0	/**< Metric Counter 35
							Register */
#define XAPM_MC36_OFFSET		0x0900	/**< Metric Counter 36
							Register */
#define XAPM_MC37_OFFSET		0x0910	/**< Metric Counter 37
							Register */
#define XAPM_MC38_OFFSET		0x0920	/**< Metric Counter 38
							Register */
#define XAPM_MC39_OFFSET		0x0930	/**< Metric Counter 39
							Register */
#define XAPM_MC40_OFFSET		0x0940	/**< Metric Counter 40
							Register */
#define XAPM_MC41_OFFSET		0x0950	/**< Metric Counter 41
							Register */
#define XAPM_MC42_OFFSET		0x0960	/**< Metric Counter 42
							Register */
#define XAPM_MC43_OFFSET		0x0970	/**< Metric Counter 43
							Register */
#define XAPM_MC44_OFFSET		0x0980	/**< Metric Counter 44
							Register */
#define XAPM_MC45_OFFSET		0x0990	/**< Metric Counter 45
							Register */
#define XAPM_MC46_OFFSET		0x09A0	/**< Metric Counter 46
							Register */
#define XAPM_MC47_OFFSET		0x09B0	/**< Metric Counter 47
							Register */

#define XAPM_SMC10_OFFSET		0x02A0	/**< Sampled Metric Counter
							10 Register */
#define XAPM_SMC11_OFFSET		0x02B0	/**< Sampled Metric Counter
							11 Register */
#define XAPM_SMC12_OFFSET		0x0600	/**< Sampled Metric Counter
							12 Register */
#define XAPM_SMC13_OFFSET		0x0610	/**< Sampled Metric Counter
							13 Register */
#define XAPM_SMC14_OFFSET		0x0620	/**< Sampled Metric Counter
							14 Register */
#define XAPM_SMC15_OFFSET		0x0630	/**< Sampled Metric Counter
							15 Register */
#define XAPM_SMC16_OFFSET		0x0640	/**< Sampled Metric Counter
							16 Register */
#define XAPM_SMC17_OFFSET		0x0650	/**< Sampled Metric Counter
							17 Register */
#define XAPM_SMC18_OFFSET		0x0660	/**< Sampled Metric Counter
							18 Register */
#define XAPM_SMC19_OFFSET		0x0670	/**< Sampled Metric Counter
							19 Register */
#define XAPM_SMC20_OFFSET		0x0680	/**< Sampled Metric Counter
							20 Register */
#define XAPM_SMC21_OFFSET		0x0690	/**< Sampled Metric Counter
							21 Register */
#define XAPM_SMC22_OFFSET		0x06A0	/**< Sampled Metric Counter
							22 Register */
#define XAPM_SMC23_OFFSET		0x06B0	/**< Sampled Metric Counter
							23 Register */
#define XAPM_SMC24_OFFSET		0x0800	/**< Sampled Metric Counter
							24 Register */
#define XAPM_SMC25_OFFSET		0x0810	/**< Sampled Metric Counter
							25 Register */
#define XAPM_SMC26_OFFSET		0x0820	/**< Sampled Metric Counter
							26 Register */
#define XAPM_SMC27_OFFSET		0x0830	/**< Sampled Metric Counter
							27 Register */
#define XAPM_SMC28_OFFSET		0x0840	/**< Sampled Metric Counter
							28 Register */
#define XAPM_SMC29_OFFSET		0x0850	/**< Sampled Metric Counter
							29 Register */
#define XAPM_SMC30_OFFSET		0x0860	/**< Sampled Metric Counter
							30 Register */
#define XAPM_SMC31_OFFSET		0x0870	/**< Sampled Metric Counter
							31 Register */
#define XAPM_SMC32_OFFSET		0x0880	/**< Sampled Metric Counter
							32 Register */
#define XAPM_SMC33_OFFSET		0x0890	/**< Sampled Metric Counter
							33 Register */
#define XAPM_SMC34_OFFSET		0x08A0	/**< Sampled Metric Counter
							34 Register */
#define XAPM_SMC35_OFFSET		0x08B0	/**< Sampled Metric Counter
							35 Register */
#define XAPM_SMC36_OFFSET		0x0A00	/**< Sampled Metric Counter
							36 Register */
#define XAPM_SMC37_OFFSET		0x0A10	/**< Sampled Metric Counter
							37 Register */
#define XAPM_SMC38_OFFSET		0x0A20	/**< Sampled Metric Counter
							38 Register */
#define XAPM_SMC39_OFFSET		0x0A30	/**< Sampled Metric Counter
							39 Register */
#define XAPM_SMC40_OFFSET		0x0A40	/**< Sampled Metric Counter
							40 Register */
#define XAPM_SMC41_OFFSET		0x0A50	/**< Sampled Metric Counter
							41 Register */
#define XAPM_SMC42_OFFSET		0x0A60	/**< Sampled Metric Counter
							42 Register */
#define XAPM_SMC43_OFFSET		0x0A70	/**< Sampled Metric Counter
							43 Register */
#define XAPM_SMC44_OFFSET		0x0A80	/**< Sampled Metric Counter
							44 Register */
#define XAPM_SMC45_OFFSET		0x0A90	/**< Sampled Metric Counter
							45 Register */
#define XAPM_SMC46_OFFSET		0x0AA0	/**< Sampled Metric Counter
							46 Register */
#define XAPM_SMC47_OFFSET		0x0AB0	/**< Sampled Metric Counter
							47 Register */

#define XAPM_CTL_OFFSET		 	0x0300	/**< Control Register */

#define XAPM_ID_OFFSET			0x0304	/**< Latency ID Register */

#define XAPM_IDMASK_OFFSET		0x0308	/**< ID Mask Register */

#define XAPM_RID_OFFSET			0x030C	/**< Latency Write ID Register */

#define XAPM_RIDMASK_OFFSET		0x0310	/**< Read ID Mask Register */

#define XAPM_FEC_OFFSET			0x0400	/**< Flag Enable
							Control Register */

#define XAPM_SWD_OFFSET			0x0404	/**< Software-written
							Data Register */

/* @} */

/**
 * @name AXI Monitor Sample Interval Control Register mask(s)
 * @{
 */

#define XAPM_SICR_MCNTR_RST_MASK	0x00000100 /**< Enable the Metric
							Counter Reset */
#define XAPM_SICR_LOAD_MASK		0x00000002 /**< Load the Sample Interval
							*  Register Value into the
							*  counter */
#define XAPM_SICR_ENABLE_MASK		0x00000001 /**< Enable the downcounter */

/*@}*/


/** @name Interrupt Status/Enable Register Bit Definitions and Masks
 *  @{
 */

#define XAPM_IXR_MC9_OVERFLOW_MASK	0x00001000	/**< Metric Counter 9
							  *  Overflow> */
#define XAPM_IXR_MC8_OVERFLOW_MASK	0x00000800	/**< Metric Counter 8
							  *  Overflow> */
#define XAPM_IXR_MC7_OVERFLOW_MASK   	0x00000400	/**< Metric Counter 7
							  *  Overflow> */
#define XAPM_IXR_MC6_OVERFLOW_MASK   	0x00000200	/**< Metric Counter 6
							  *  Overflow> */
#define XAPM_IXR_MC5_OVERFLOW_MASK   	0x00000100	/**< Metric Counter 5
							  *  Overflow> */
#define XAPM_IXR_MC4_OVERFLOW_MASK   	0x00000080	/**< Metric Counter 4
							  *  Overflow> */
#define XAPM_IXR_MC3_OVERFLOW_MASK   	0x00000040	/**< Metric Counter 3
							  *  Overflow> */
#define XAPM_IXR_MC2_OVERFLOW_MASK   	0x00000020	/**< Metric Counter 2
							  *  Overflow> */
#define XAPM_IXR_MC1_OVERFLOW_MASK   	0x00000010	/**< Metric Counter 1
							  *  Overflow> */
#define XAPM_IXR_MC0_OVERFLOW_MASK   	0x00000008	/**< Metric Counter 0
							  *  Overflow> */
#define XAPM_IXR_FIFO_FULL_MASK   	0x00000004	/**< Event Log FIFO
							  *  full> */
#define XAPM_IXR_SIC_OVERFLOW_MASK   	0x00000002	/**< Sample Interval
							  * Counter Overflow> */
#define XAPM_IXR_GCC_OVERFLOW_MASK	0x00000001	/**< Global Clock Counter
						          *  Overflow> */
#define XAPM_IXR_ALL_MASK		(XAPM_IXR_SIC_OVERFLOW_MASK | \
					XAPM_IXR_GCC_OVERFLOW_MASK |  \
					XAPM_IXR_FIFO_FULL_MASK | \
					XAPM_IXR_MC0_OVERFLOW_MASK | \
					XAPM_IXR_MC1_OVERFLOW_MASK | \
					XAPM_IXR_MC2_OVERFLOW_MASK | \
					XAPM_IXR_MC3_OVERFLOW_MASK | \
					XAPM_IXR_MC4_OVERFLOW_MASK | \
					XAPM_IXR_MC5_OVERFLOW_MASK | \
					XAPM_IXR_MC6_OVERFLOW_MASK | \
					XAPM_IXR_MC7_OVERFLOW_MASK | \
					XAPM_IXR_MC8_OVERFLOW_MASK | \
					XAPM_IXR_MC9_OVERFLOW_MASK)
/* @} */

/**
 * @name AXI Monitor Control Register mask(s)
 * @{
 */

#define XAPM_CR_FIFO_RESET_MASK			0x02000000
						/**< FIFO Reset */
#define XAPM_CR_GCC_RESET_MASK			0x00020000
						/**< Global Clk
						  Counter Reset */
#define XAPM_CR_GCC_ENABLE_MASK			0x00010000
						/**< Global Clk
						   Counter Enable */
#define XAPM_CR_EVTLOG_EXTTRIGGER_MASK  	0x00000200
						/**< Enable External trigger
						to start event Log */
#define XAPM_CR_EVENTLOG_ENABLE_MASK  		0x00000100
						/**< Event Log Enable */

#define XAPM_CR_RDLATENCY_END_MASK  		0x00000080
						/**< Write Latency
							End point */
#define XAPM_CR_RDLATENCY_START_MASK  		0x00000040
						/**< Read Latency
							Start point */
#define XAPM_CR_WRLATENCY_END_MASK  		0x00000020
						/**< Write Latency
							End point */
#define XAPM_CR_WRLATENCY_START_MASK  		0x00000010
						/**< Write Latency
							Start point */
#define XAPM_CR_IDFILTER_ENABLE_MASK  		0x00000008
						/**< ID Filter Enable */

#define XAPM_CR_MCNTR_EXTTRIGGER_MASK  	 	0x00000004
						/**< Enable External
						   trigger to start
						   Metric Counters  */
#define XAPM_CR_MCNTR_RESET_MASK   		0x00000002
						/**< Metrics Counter
						   Reset */
#define XAPM_CR_MCNTR_ENABLE_MASK  		0x00000001
						/**< Metrics Counter
					           Enable */
/*@}*/

/**
 * @name AXI Monitor ID Register mask(s)
 * @{
 */

#define XAPM_ID_RID_MASK			0xFFFF0000 /**< Read ID */

#define XAPM_ID_WID_MASK			0x0000FFFF /**< Write ID */

/*@}*/

/**
 * @name AXI Monitor ID Mask Register mask(s)
 * @{
 */

#define XAPM_MASKID_RID_MASK			0xFFFF0000 /**< Read ID Mask */

#define XAPM_MASKID_WID_MASK			0x0000FFFF /**< Write ID Mask*/

/*@}*/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/*****************************************************************************/
/**
*
* Read a register of the AXI Performance Monitor device. This macro provides
* register access to all registers using the register offsets defined above.
*
* @param	BaseAddress contains the base address of the device.
* @param	RegOffset is the offset of the register to read.
*
* @return	The contents of the register.
*
* @note		C-style Signature:
*		u32 XAxiPmon_ReadReg(u32 BaseAddress, u32 RegOffset);
*
******************************************************************************/
#define XAxiPmon_ReadReg(BaseAddress, RegOffset) \
		(Xil_In32((BaseAddress) + (RegOffset)))

/*****************************************************************************/
/**
*
* Write a register of the AXI Performance Monitor device. This macro provides
* register access to all registers using the register offsets defined above.
*
* @param	BaseAddress contains the base address of the device.
* @param	RegOffset is the offset of the register to write.
* @param	Data is the value to write to the register.
*
* @return	None.
*
* @note 	C-style Signature:
*		void XAxiPmon_WriteReg(u32 BaseAddress,
*					u32 RegOffset,u32 Data)
*
******************************************************************************/
#define XAxiPmon_WriteReg(BaseAddress, RegOffset, Data) \
		(Xil_Out32((BaseAddress) + (RegOffset), (Data)))

/************************** Function Prototypes ******************************/

#ifdef __cplusplus
}
#endif

#endif  /* End of protection macro. */
