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
* @addtogroup axipmon_v6_3
* @{
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
*
* 6.3  kvn  07/02/15 Modified code according to MISRA-C:2012 guidelines.
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

#define XAPM_GCC_HIGH_OFFSET		0x00000000U	/**< Global Clock Counter
							32 to 63 bits  */
#define XAPM_GCC_LOW_OFFSET		0x00000004U	/**< Global Clock Counter Lower
							0-31 bits  */
#define XAPM_SI_HIGH_OFFSET		0x00000020U	/**< Sample Interval MSB */
#define XAPM_SI_LOW_OFFSET		0x00000024U	/**< Sample Interval LSB */
#define XAPM_SICR_OFFSET		0x00000028U	/**< Sample Interval Control
							Register */
#define XAPM_SR_OFFSET			0x0000002CU	/**< Sample Register */
#define XAPM_GIE_OFFSET			0x00000030U	/**< Global Interrupt Enable
							Register */
#define XAPM_IE_OFFSET			0x00000034U	/**< Interrupt Enable Register */
#define XAPM_IS_OFFSET			0x00000038U	/**< Interrupt Status Register */

#define XAPM_MSR0_OFFSET		0x00000044U	/**< Metric Selector 0 Register */
#define XAPM_MSR1_OFFSET		0x00000048U	/**< Metric Selector 1 Register */
#define XAPM_MSR2_OFFSET		0x0000004CU	/**< Metric Selector 2 Register */

#define XAPM_MC0_OFFSET			0x00000100U	/**< Metric Counter 0 Register */
#define XAPM_INC0_OFFSET		0x00000104U	/**< Incrementer 0 Register */
#define XAPM_RANGE0_OFFSET		0x00000108U	/**< Range 0 Register */
#define XAPM_MC0LOGEN_OFFSET		0x0000010CU	/**< Metric Counter 0
							Log Enable Register */
#define XAPM_MC1_OFFSET			0x00000110U	/**< Metric Counter 1 Register */
#define XAPM_INC1_OFFSET		0x00000114U	/**< Incrementer 1 Register */
#define XAPM_RANGE1_OFFSET		0x00000118U	/**< Range 1 Register */
#define XAPM_MC1LOGEN_OFFSET		0x0000011CU	/**< Metric Counter 1
							Log Enable Register */
#define XAPM_MC2_OFFSET			0x00000120U	/**< Metric Counter 2 Register */
#define XAPM_INC2_OFFSET		0x00000124U	/**< Incrementer 2 Register */
#define XAPM_RANGE2_OFFSET		0x00000128U	/**< Range 2 Register */
#define XAPM_MC2LOGEN_OFFSET		0x0000012CU	/**< Metric Counter 2
							Log Enable Register */
#define XAPM_MC3_OFFSET			0x00000130U	/**< Metric Counter 3 Register */
#define XAPM_INC3_OFFSET		0x00000134U	/**< Incrementer 3 Register */
#define XAPM_RANGE3_OFFSET		0x00000138U	/**< Range 3 Register */
#define XAPM_MC3LOGEN_OFFSET		0x0000013CU	/**< Metric Counter 3
							Log Enable Register */
#define XAPM_MC4_OFFSET			0x00000140U	/**< Metric Counter 4 Register */
#define XAPM_INC4_OFFSET		0x00000144U	/**< Incrementer 4 Register */
#define XAPM_RANGE4_OFFSET		0x00000148U	/**< Range 4 Register */
#define XAPM_MC4LOGEN_OFFSET		0x0000014CU	/**< Metric Counter 4
							Log Enable Register */
#define XAPM_MC5_OFFSET			0x00000150U	/**< Metric Counter 5
							Register */
#define XAPM_INC5_OFFSET		0x00000154U	/**< Incrementer 5 Register */
#define XAPM_RANGE5_OFFSET		0x00000158U	/**< Range 5 Register */
#define XAPM_MC5LOGEN_OFFSET		0x0000015CU	/**< Metric Counter 5
							Log Enable Register */
#define XAPM_MC6_OFFSET			0x00000160U	/**< Metric Counter 6
							Register */
#define XAPM_INC6_OFFSET		0x00000164U	/**< Incrementer 6 Register */
#define XAPM_RANGE6_OFFSET		0x00000168U	/**< Range 6 Register */
#define XAPM_MC6LOGEN_OFFSET		0x0000016CU	/**< Metric Counter 6
							Log Enable Register */
#define XAPM_MC7_OFFSET			0x00000170U	/**< Metric Counter 7
							Register */
#define XAPM_INC7_OFFSET		0x00000174U	/**< Incrementer 7 Register */
#define XAPM_RANGE7_OFFSET		0x00000178U	/**< Range 7 Register */
#define XAPM_MC7LOGEN_OFFSET		0x0000017CU	/**< Metric Counter 7
							Log Enable Register */
#define XAPM_MC8_OFFSET			0x00000180U	/**< Metric Counter 8
							Register */
#define XAPM_INC8_OFFSET		0x00000184U	/**< Incrementer 8 Register */
#define XAPM_RANGE8_OFFSET		0x00000188U	/**< Range 8 Register */
#define XAPM_MC8LOGEN_OFFSET		0x0000018CU	/**< Metric Counter 8
							Log Enable Register */
#define XAPM_MC9_OFFSET			0x00000190U	/**< Metric Counter 9
							Register */
#define XAPM_INC9_OFFSET		0x00000194U	/**< Incrementer 9 Register */
#define XAPM_RANGE9_OFFSET		0x00000198U	/**< Range 9 Register */
#define XAPM_MC9LOGEN_OFFSET		0x0000019CU	/**< Metric Counter 9
							Log Enable Register */
#define XAPM_SMC0_OFFSET		0x00000200U	/**< Sampled Metric Counter
							0 Register */
#define XAPM_SINC0_OFFSET		0x00000204U	/**< Sampled Incrementer
							0 Register */
#define XAPM_SMC1_OFFSET		0x00000210U	/**< Sampled Metric Counter
							1 Register */
#define XAPM_SINC1_OFFSET		0x00000214U	/**< Sampled Incrementer
							1 Register */
#define XAPM_SMC2_OFFSET		0x00000220U	/**< Sampled Metric Counter
							2 Register */
#define XAPM_SINC2_OFFSET		0x00000224U	/**< Sampled Incrementer
							2 Register */
#define XAPM_SMC3_OFFSET		0x00000230U	/**< Sampled Metric Counter
							3 Register */
#define XAPM_SINC3_OFFSET		0x00000234U	/**< Sampled Incrementer
							3 Register */
#define XAPM_SMC4_OFFSET		0x00000240U	/**< Sampled Metric Counter
							4 Register */
#define XAPM_SINC4_OFFSET		0x00000244U	/**< Sampled Incrementer
							4 Register */
#define XAPM_SMC5_OFFSET		0x00000250U	/**< Sampled Metric Counter
							5 Register */
#define XAPM_SINC5_OFFSET		0x00000254U	/**< Sampled Incrementer
							5 Register */
#define XAPM_SMC6_OFFSET		0x00000260U	/**< Sampled Metric Counter
							6 Register */
#define XAPM_SINC6_OFFSET		0x00000264U	/**< Sampled Incrementer
							6 Register */
#define XAPM_SMC7_OFFSET		0x00000270U	/**< Sampled Metric Counter
							7 Register */
#define XAPM_SINC7_OFFSET		0x00000274U	/**< Sampled Incrementer
							7 Register */
#define XAPM_SMC8_OFFSET		0x00000280U	/**< Sampled Metric Counter
							8 Register */
#define XAPM_SINC8_OFFSET		0x00000284U	/**< Sampled Incrementer
							8 Register */
#define XAPM_SMC9_OFFSET		0x00000290U	/**< Sampled Metric Counter
							9 Register */
#define XAPM_SINC9_OFFSET		0x00000294U	/**< Sampled Incrementer
							9 Register */

#define XAPM_MC10_OFFSET		0x000001A0U	/**< Metric Counter 10
							Register */
#define XAPM_MC11_OFFSET		0x000001B0U	/**< Metric Counter 11
							Register */
#define XAPM_MC12_OFFSET		0x00000500U	/**< Metric Counter 12
							Register */
#define XAPM_MC13_OFFSET		0x00000510U	/**< Metric Counter 13
							Register */
#define XAPM_MC14_OFFSET		0x00000520U	/**< Metric Counter 14
							Register */
#define XAPM_MC15_OFFSET		0x00000530U	/**< Metric Counter 15
							Register */
#define XAPM_MC16_OFFSET		0x00000540U	/**< Metric Counter 16
							Register */
#define XAPM_MC17_OFFSET		0x00000550U	/**< Metric Counter 17
							Register */
#define XAPM_MC18_OFFSET		0x00000560U	/**< Metric Counter 18
							Register */
#define XAPM_MC19_OFFSET		0x00000570U	/**< Metric Counter 19
							Register */
#define XAPM_MC20_OFFSET		0x00000580U	/**< Metric Counter 20
							Register */
#define XAPM_MC21_OFFSET		0x00000590U	/**< Metric Counter 21
							Register */
#define XAPM_MC22_OFFSET		0x000005A0U	/**< Metric Counter 22
							Register */
#define XAPM_MC23_OFFSET		0x000005B0U	/**< Metric Counter 23
							Register */
#define XAPM_MC24_OFFSET		0x00000700U	/**< Metric Counter 24
							Register */
#define XAPM_MC25_OFFSET		0x00000710U	/**< Metric Counter 25
							Register */
#define XAPM_MC26_OFFSET		0x00000720U	/**< Metric Counter 26
							Register */
#define XAPM_MC27_OFFSET		0x00000730U	/**< Metric Counter 27
							Register */
#define XAPM_MC28_OFFSET		0x00000740U	/**< Metric Counter 28
							Register */
#define XAPM_MC29_OFFSET		0x00000750U	/**< Metric Counter 29
							Register */
#define XAPM_MC30_OFFSET		0x00000760U	/**< Metric Counter 30
							Register */
#define XAPM_MC31_OFFSET		0x00000770U	/**< Metric Counter 31
							Register */
#define XAPM_MC32_OFFSET		0x00000780U	/**< Metric Counter 32
							Register */
#define XAPM_MC33_OFFSET		0x00000790U	/**< Metric Counter 33
							Register */
#define XAPM_MC34_OFFSET		0x000007A0U	/**< Metric Counter 34
							Register */
#define XAPM_MC35_OFFSET		0x000007B0U	/**< Metric Counter 35
							Register */
#define XAPM_MC36_OFFSET		0x00000900U	/**< Metric Counter 36
							Register */
#define XAPM_MC37_OFFSET		0x00000910U	/**< Metric Counter 37
							Register */
#define XAPM_MC38_OFFSET		0x00000920U	/**< Metric Counter 38
							Register */
#define XAPM_MC39_OFFSET		0x00000930U	/**< Metric Counter 39
							Register */
#define XAPM_MC40_OFFSET		0x00000940U	/**< Metric Counter 40
							Register */
#define XAPM_MC41_OFFSET		0x00000950U	/**< Metric Counter 41
							Register */
#define XAPM_MC42_OFFSET		0x00000960U	/**< Metric Counter 42
							Register */
#define XAPM_MC43_OFFSET		0x00000970U	/**< Metric Counter 43
							Register */
#define XAPM_MC44_OFFSET		0x00000980U	/**< Metric Counter 44
							Register */
#define XAPM_MC45_OFFSET		0x00000990U	/**< Metric Counter 45
							Register */
#define XAPM_MC46_OFFSET		0x000009A0U	/**< Metric Counter 46
							Register */
#define XAPM_MC47_OFFSET		0x000009B0U	/**< Metric Counter 47
							Register */

#define XAPM_SMC10_OFFSET		0x000002A0U	/**< Sampled Metric Counter
							10 Register */
#define XAPM_SMC11_OFFSET		0x000002B0U	/**< Sampled Metric Counter
							11 Register */
#define XAPM_SMC12_OFFSET		0x00000600U	/**< Sampled Metric Counter
							12 Register */
#define XAPM_SMC13_OFFSET		0x00000610U	/**< Sampled Metric Counter
							13 Register */
#define XAPM_SMC14_OFFSET		0x00000620U	/**< Sampled Metric Counter
							14 Register */
#define XAPM_SMC15_OFFSET		0x00000630U	/**< Sampled Metric Counter
							15 Register */
#define XAPM_SMC16_OFFSET		0x00000640U	/**< Sampled Metric Counter
							16 Register */
#define XAPM_SMC17_OFFSET		0x00000650U	/**< Sampled Metric Counter
							17 Register */
#define XAPM_SMC18_OFFSET		0x00000660U	/**< Sampled Metric Counter
							18 Register */
#define XAPM_SMC19_OFFSET		0x00000670U	/**< Sampled Metric Counter
							19 Register */
#define XAPM_SMC20_OFFSET		0x00000680U	/**< Sampled Metric Counter
							20 Register */
#define XAPM_SMC21_OFFSET		0x00000690U	/**< Sampled Metric Counter
							21 Register */
#define XAPM_SMC22_OFFSET		0x000006A0U	/**< Sampled Metric Counter
							22 Register */
#define XAPM_SMC23_OFFSET		0x000006B0U	/**< Sampled Metric Counter
							23 Register */
#define XAPM_SMC24_OFFSET		0x00000800U	/**< Sampled Metric Counter
							24 Register */
#define XAPM_SMC25_OFFSET		0x00000810U	/**< Sampled Metric Counter
							25 Register */
#define XAPM_SMC26_OFFSET		0x00000820U	/**< Sampled Metric Counter
							26 Register */
#define XAPM_SMC27_OFFSET		0x00000830U	/**< Sampled Metric Counter
							27 Register */
#define XAPM_SMC28_OFFSET		0x00000840U	/**< Sampled Metric Counter
							28 Register */
#define XAPM_SMC29_OFFSET		0x00000850U	/**< Sampled Metric Counter
							29 Register */
#define XAPM_SMC30_OFFSET		0x00000860U	/**< Sampled Metric Counter
							30 Register */
#define XAPM_SMC31_OFFSET		0x00000870U	/**< Sampled Metric Counter
							31 Register */
#define XAPM_SMC32_OFFSET		0x00000880U	/**< Sampled Metric Counter
							32 Register */
#define XAPM_SMC33_OFFSET		0x00000890U	/**< Sampled Metric Counter
							33 Register */
#define XAPM_SMC34_OFFSET		0x000008A0U	/**< Sampled Metric Counter
							34 Register */
#define XAPM_SMC35_OFFSET		0x000008B0U	/**< Sampled Metric Counter
							35 Register */
#define XAPM_SMC36_OFFSET		0x00000A00U	/**< Sampled Metric Counter
							36 Register */
#define XAPM_SMC37_OFFSET		0x00000A10U	/**< Sampled Metric Counter
							37 Register */
#define XAPM_SMC38_OFFSET		0x00000A20U	/**< Sampled Metric Counter
							38 Register */
#define XAPM_SMC39_OFFSET		0x00000A30U	/**< Sampled Metric Counter
							39 Register */
#define XAPM_SMC40_OFFSET		0x00000A40U	/**< Sampled Metric Counter
							40 Register */
#define XAPM_SMC41_OFFSET		0x00000A50U	/**< Sampled Metric Counter
							41 Register */
#define XAPM_SMC42_OFFSET		0x00000A60U	/**< Sampled Metric Counter
							42 Register */
#define XAPM_SMC43_OFFSET		0x00000A70U	/**< Sampled Metric Counter
							43 Register */
#define XAPM_SMC44_OFFSET		0x00000A80U	/**< Sampled Metric Counter
							44 Register */
#define XAPM_SMC45_OFFSET		0x00000A90U	/**< Sampled Metric Counter
							45 Register */
#define XAPM_SMC46_OFFSET		0x00000AA0U	/**< Sampled Metric Counter
							46 Register */
#define XAPM_SMC47_OFFSET		0x00000AB0U	/**< Sampled Metric Counter
							47 Register */

#define XAPM_CTL_OFFSET		 	0x00000300U	/**< Control Register */

#define XAPM_ID_OFFSET			0x00000304U	/**< Latency ID Register */

#define XAPM_IDMASK_OFFSET		0x00000308U	/**< ID Mask Register */

#define XAPM_RID_OFFSET			0x0000030CU	/**< Latency Write ID Register */

#define XAPM_RIDMASK_OFFSET		0x00000310U	/**< Read ID Mask Register */

#define XAPM_FEC_OFFSET			0x00000400U	/**< Flag Enable
							Control Register */

#define XAPM_SWD_OFFSET			0x00000404U	/**< Software-written
							Data Register */

/* @} */

/**
 * @name AXI Monitor Sample Interval Control Register mask(s)
 * @{
 */

#define XAPM_SICR_MCNTR_RST_MASK	0x00000100U /**< Enable the Metric
							Counter Reset */
#define XAPM_SICR_LOAD_MASK		0x00000002U /**< Load the Sample Interval
							*  Register Value into the
							*  counter */
#define XAPM_SICR_ENABLE_MASK		0x00000001U /**< Enable the downcounter */

/*@}*/


/** @name Interrupt Status/Enable Register Bit Definitions and Masks
 *  @{
 */

#define XAPM_IXR_MC9_OVERFLOW_MASK	0x00001000U	/**< Metric Counter 9
							  *  Overflow> */
#define XAPM_IXR_MC8_OVERFLOW_MASK	0x00000800U	/**< Metric Counter 8
							  *  Overflow> */
#define XAPM_IXR_MC7_OVERFLOW_MASK   	0x00000400U	/**< Metric Counter 7
							  *  Overflow> */
#define XAPM_IXR_MC6_OVERFLOW_MASK   	0x00000200U	/**< Metric Counter 6
							  *  Overflow> */
#define XAPM_IXR_MC5_OVERFLOW_MASK   	0x00000100U	/**< Metric Counter 5
							  *  Overflow> */
#define XAPM_IXR_MC4_OVERFLOW_MASK   	0x00000080U	/**< Metric Counter 4
							  *  Overflow> */
#define XAPM_IXR_MC3_OVERFLOW_MASK   	0x00000040U	/**< Metric Counter 3
							  *  Overflow> */
#define XAPM_IXR_MC2_OVERFLOW_MASK   	0x00000020U	/**< Metric Counter 2
							  *  Overflow> */
#define XAPM_IXR_MC1_OVERFLOW_MASK   	0x00000010U	/**< Metric Counter 1
							  *  Overflow> */
#define XAPM_IXR_MC0_OVERFLOW_MASK   	0x00000008U	/**< Metric Counter 0
							  *  Overflow> */
#define XAPM_IXR_FIFO_FULL_MASK   	0x00000004U	/**< Event Log FIFO
							  *  full> */
#define XAPM_IXR_SIC_OVERFLOW_MASK   	0x00000002U	/**< Sample Interval
							  * Counter Overflow> */
#define XAPM_IXR_GCC_OVERFLOW_MASK	0x00000001U	/**< Global Clock Counter
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

#define XAPM_CR_FIFO_RESET_MASK			0x02000000U
						/**< FIFO Reset */
#define XAPM_CR_GCC_RESET_MASK			0x00020000U
						/**< Global Clk
						  Counter Reset */
#define XAPM_CR_GCC_ENABLE_MASK			0x00010000U
						/**< Global Clk
						   Counter Enable */
#define XAPM_CR_EVTLOG_EXTTRIGGER_MASK  	0x00000200U
						/**< Enable External trigger
						to start event Log */
#define XAPM_CR_EVENTLOG_ENABLE_MASK  		0x00000100U
						/**< Event Log Enable */

#define XAPM_CR_RDLATENCY_END_MASK  		0x00000080U
						/**< Write Latency
							End point */
#define XAPM_CR_RDLATENCY_START_MASK  		0x00000040U
						/**< Read Latency
							Start point */
#define XAPM_CR_WRLATENCY_END_MASK  		0x00000020U
						/**< Write Latency
							End point */
#define XAPM_CR_WRLATENCY_START_MASK  		0x00000010U
						/**< Write Latency
							Start point */
#define XAPM_CR_IDFILTER_ENABLE_MASK  		0x00000008U
						/**< ID Filter Enable */

#define XAPM_CR_MCNTR_EXTTRIGGER_MASK  	 	0x00000004U
						/**< Enable External
						   trigger to start
						   Metric Counters  */
#define XAPM_CR_MCNTR_RESET_MASK   		0x00000002U
						/**< Metrics Counter
						   Reset */
#define XAPM_CR_MCNTR_ENABLE_MASK  		0x00000001U
						/**< Metrics Counter
					           Enable */
/*@}*/

/**
 * @name AXI Monitor ID Register mask(s)
 * @{
 */

#define XAPM_ID_RID_MASK			0xFFFF0000U /**< Read ID */

#define XAPM_ID_WID_MASK			0x0000FFFFU /**< Write ID */

/*@}*/

/**
 * @name AXI Monitor ID Mask Register mask(s)
 * @{
 */

#define XAPM_MASKID_RID_MASK			0xFFFF0000U /**< Read ID Mask */

#define XAPM_MASKID_WID_MASK			0x0000FFFFU /**< Write ID Mask*/

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
/** @} */
