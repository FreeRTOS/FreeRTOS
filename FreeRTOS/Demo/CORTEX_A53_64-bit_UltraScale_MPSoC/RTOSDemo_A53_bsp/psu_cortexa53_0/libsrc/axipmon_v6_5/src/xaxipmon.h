/******************************************************************************
*
* Copyright (C) 2007 - 2015 Xilinx, Inc.  All rights reserved.
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
* @file xaxipmon.h
* @addtogroup axipmon_v6_3
* @{
* @details
*
* The XAxiPmon driver supports the Xilinx AXI Performance Monitor device.
*
* The AXI Performance Monitor device provides following features:
*
*	Configurable number of Metric Counters and Incrementers
* 	Computes performance metrics for Agents connected to
*	monitor slots (Up to 8 slots)
*
* The following Metrics can be computed:
*
* Metrics computed for an AXI4 MM agent:
*	Write Request Count: Total number of write requests by/to the agent.
*	Read Request Count: Total number of read requests given by/to the
*			    agent.
*	Read Latency: It is defined as the time from the start of read address
*       	      transaction to the beginning of the read data service.
*	Write Latency: It is defined as the period needed a master completes
*        	       write data transaction, i.e. from write address
*        	       transaction to write response from slave.
*	Write Byte Count: Total number of bytes written by/to the agent.
*        		  This metric is helpful when calculating the
*        		  throughput of the system.
*	Read Byte Count: Total number of bytes read from/by the agent.
*	Average Write Latency: Average write latency seen by the agent.
*        		       It can be derived from total write latency
*        		       and the write request count.
*	Average Read Latency: Average read latency seen by the agent. It can be
*        		      derived from total read latency and the read
*        		      request count.
*	Master Write Idle Cycle Count: Number of idle cycles caused by the
*        			       masters during write transactions to
*        			       the slave.
*	Slave Write Idle Cycle Count: Number of idle cycles caused by this slave
*        			      during write transactions to the slave.
*	Master Read Idle Cycle Count: Number of idle cycles caused by the
*        			      master during read transactions to the
*        			      slave.
*	Slave Read Idle Cycle Count: Number of idle cycles caused by this slave
*        			     during read transactions to the slave.
*
* Metrics computed for an AXI4-Stream agent:
*
*	Transfer Cycle Count: Total number of writes by/to the agent.
*	Data Byte Count: Total number of data bytes written by/to the agent.
*			 This metric helps in calculating the throughput
*			 of the system.
*	Position Byte Count: Total number of position bytes transferred.
*	Null Byte Count: Total number of null bytes transferred.
*	Packet Count: Total number of packets transferred.
*
* There are three modes : Advanced, Profile and Trace.
* - Advanced mode has 10 Mertic Counters, Sampled Metric Counters, Incrementors
*   and Sampled Incrementors.
* - Profile mode has only 47 Metric Counters and Sampled Metric Counters.
* - Trace mode has no Counters.
* User should refer to the hardware device specification for detailed
* information about the device.
*
* This header file contains the prototypes of driver functions that can
* be used to access the AXI Performance Monitor device.
*
*
* <b> Initialization and Configuration </b>
*
* The device driver enables higher layer software (e.g., an application) to
* communicate to the AXI Performance Monitor device.
*
* XAxiPmon_CfgInitialize() API is used to initialize the AXI Performance Monitor
* device. The user needs to first call the XAxiPmon_LookupConfig() API which
* returns the Configuration structure pointer which is passed as a parameter to
* the XAxiPmon_CfgInitialize() API.
*
*
* <b>Interrupts</b>
*
* The AXI Performance Monitor does not support Interrupts
*
*
* <b> Virtual Memory </b>
*
* This driver supports Virtual Memory. The RTOS is responsible for calculating
* the correct device base address in Virtual Memory space.
*
*
* <b> Threads </b>
*
* This driver is not thread safe. Any needs for threads or thread mutual
* exclusion must be satisfied by the layer above this driver.
*
* <b> Asserts </b>
*
* Asserts are used within all Xilinx drivers to enforce constraints on argument
* values. Asserts can be turned off on a system-wide basis by defining, at
* compile time, the NDEBUG identifier. By default, asserts are turned on and it
* is recommended that users leave asserts on during development.
*
*
* <b> Building the driver </b>
*
* The XAxiPmon driver is composed of several source files. This allows the user
* to build and link only those parts of the driver that are necessary.
*
* <b> Limitations of the driver </b>
*
*
* <br><br>
*
* <pre>
*
* MODIFICATION HISTORY:
*
* Ver   Who    Date     Changes
* ----- -----  -------- -----------------------------------------------------
* 1.00a bss    02/27/12 First release
* 2.00a bss    06/23/12 Updated to support v2_00a version of IP.
* 3.00a bss    09/03/12 To support v2_01_a version of IP:
*			Deleted XAxiPmon_SetAgent, XAxiPmon_GetAgent APIs and
*			added XAPM_FLAG_EVENT, XAPM_FLAG_EVNTSTAR,
*			XAPM_FLAG_EVNTSTOP.
*			Deleted XAxiPmon_SetAgent, XAxiPmon_GetAgent APIs and
*			modified XAxiPmon_SetMetrics, XAxiPmon_GetMetrics APIs
*			in xaxipmon.c
*			Deleted XAPM_AGENT_OFFSET Macro in xaxipmon_hw.h
* 3.01a bss    10/25/12 To support new version of IP:
*			Added XAPM_MCXLOGEN_OFFSET macros in xaxipmon_hw.h.
*			Added XAxiPmon_SetMetricCounterCutOff,
*			XAxiPmon_GetMetricCounterCutOff,
*			XAxiPmon_EnableExternalTrigger and
*			XAxiPmon_DisableExternalTrigger APIs in xaxipmon.c
*			Modified XAxiPmon_SetMetrics and XAxiPmon_GetMetrics
*			(CR #683746) in xaxipmon.c
*			Added XAxiPmon_EnableEventLog,
*			XAxiPmon_DisableMetricsCounter,
*			XAxiPmon_EnableMetricsCounter APIs in xaxipmon.c to
*			replace macros in this file.
*			Added XAPM_FLAG_XXX macros.
*			Added XAxiPmon_StartCounters and XAxiPmon_StopCounters
*			APIs (CR #683799).
*			Added XAxiPmon_StartEventLog and XAxiPmon_StopEventLog
*			APIs (CR #683801).
*			Added XAxiPmon_GetMetricName API (CR #683803).
*			Deleted XAxiPmon_SetAgent, XAxiPmon_GetAgent
*			declarations (CR #677337)
* 4.00a bss    01/17/13 To support new version of IP:
*			Added XAPM_METRIC_SET_12 to XAPM_METRIC_SET_15 macros.
*			Added XAxiPmon_SetLogEnableRanges,
*	  		XAxiPmon_GetLogEnableRanges,
*			XAxiPmon_EnableMetricCounterTrigger,
*			XAxiPmon_DisableMetricCounterTrigger,
*			XAxiPmon_EnableEventLogTrigger,
*			XAxiPmon_DisableEventLogTrigger,
*			XAxiPmon_SetWriteLatencyId,
*			XAxiPmon_SetReadLatencyId,
*			XAxiPmon_GetWriteLatencyId,
*			XAxiPmon_GetReadLatencyId APIs and removed
*			XAxiPmon_SetMetricCounterCutOff,
*			XAxiPmon_GetMetricCounterCutOff,
*			XAxiPmon_EnableExternalTrigger and
*			XAxiPmon_DisableExternalTrigger APIs in xaxipmon.c
*			Added XAPM_LATENCYID_OFFSET,
*			XAPM_CR_EVTLOG_EXTTRIGGER_MASK,
*			XAPM_LATENCYID_RID_MASK and XAPM_LATENCYID_WID_MASK in
*			xaxipmon_hw.h
* 5.00a bss   08/26/13  To support new version of IP:
*			XAxiPmon_SampleMetrics Macro.
*			Modified XAxiPmon_CfgInitialize, Assert functions
*			Added XAxiPmon_GetMetricCounter,
*			XAxiPmon_SetSampleInterval, XAxiPmon_GetSampleInterval,
*			XAxiPmon_SetWrLatencyStart, XAxiPmon_SetWrLatencyEnd,
*			XAxiPmon_SetRdLatencyStart, XAxiPmon_SetRdLatencyEnd,
*			XAxiPmon_GetWrLatencyStart, XAxiPmon_GetWrLatencyEnd,
*			XAxiPmon_GetRdLatencyStart, XAxiPmon_GetRdLatencyEnd,
*			XAxiPmon_SetWriteIdMask, XAxiPmon_SetReadIdMask,
*			XAxiPmon_GetWriteIdMask and XAxiPmon_GetReadIdMask APIs
*			Renamed :
*			XAxiPmon_SetWriteLatencyId to
*			XAxiPmon_SetWriteId, XAxiPmon_SetReadLatencyId to
*			XAxiPmon_SetReadId, XAxiPmon_GetWriteLatencyId to
*			XAxiPmon_GetWriteId and XAxiPmon_SetReadLatencyId to
*			XAxiPmon_GetReadId. in xaxipmon.c
*			Added Macros XAPM_MC10_OFFSET to XAPM_MC47_OFFSET,
*			XAPM_SMC10_OFFSET to XAPM_SMC47_OFFSET,
*			XAPM_IDMASK_OFFSET, XAPM_CR_IDFILTER_ENABLE_MASK,
*			XAPM_CR_WRLATENCY_START_MASK,
*			XAPM_CR_WRLATENCY_END_MASK,
*			XAPM_CR_RDLATENCY_START_MASK,
*			XAPM_CR_RDLATENCY_END_MASK and
*			XAPM_MAX_COUNTERS_PROFILE.
*			Renamed:
*			XAPM_LATENCYID_OFFSET to XAPM_ID_OFFSET,
*			XAPM_LATENCYID_RID_MASK to XAPM_ID_RID_MASK,
*			XAPM_LATENCYID_WID_MASK to XAPM_ID_WID_MASK.
*			in xaxipmon_hw.h.
*			Modified driver tcl to generate new parameters
*			ScaleFactor, ModeProfile, ModeTrace and ModeAdvanced
*			in Config structure.
* 6.0   adk  19/12/13 Updated as per the New Tcl API's
* 6.1   adk  16/04/14 Updated the driver tcl for the newly added parameters in
* 		      The Axi pmon IP.
* 6.2   bss  04/21/14   Updated XAxiPmon_CfgInitialize in xaxipmon.c to Reset
*			counters and FIFOs based on Modes(CR#782671). And if
*			both profile and trace modes are present set mode as
*			Advanced.
* 6.2	bss  03/02/15	To support Zynq MP APM:
*						Added Is32BitFiltering in XAxiPmon_Config structure.
*						Updated XAxiPmon_SetWriteId, XAxiPmon_SetReadId,
*						XAxiPmon_GetWriteId, XAxiPmon_GetReadId
*						XAxiPmon_SetWriteIdMask, XAxiPmon_SetReadIdMask
*						XAxiPmon_GetWriteIdMask, XAxiPmon_GetReadIdMask
*						functions in xaxipmon.c.
*						Added XAPM_RID_OFFSET and XAPM_RIDMASK_OFFSET in
*						xaxipmon_hw.h
*
* 6.3	kvn  07/02/15	Modified code according to MISRA-C:2012 guidelines.
* 6.4   sk   11/10/15 Used UINTPTR instead of u32 for Baseaddress CR# 867425.
*                     Changed the prototype of XAxiPmon_CfgInitialize API.
* </pre>
*
*****************************************************************************/
#ifndef XAXIPMON_H /* Prevent circular inclusions */
#define XAXIPMON_H /* by using protection macros  */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files ********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xstatus.h"
#include "xaxipmon_hw.h"

/************************** Constant Definitions ****************************/


/**
 * @name Macro for Maximum number of Counters
 *
 * @{
 */
#define XAPM_MAX_COUNTERS		10U /**< Maximum number of Counters */
#define XAPM_MAX_COUNTERS_PROFILE	48U /**< Maximum number of Counters */

/*@}*/


/**
 * @name Indices for Metric Counters and Sampled Metric Coounters used with
 * 	 XAxiPmon_GetMetricCounter and XAxiPmon_GetSampledMetricCounter APIs
 * @{
 */

#define XAPM_METRIC_COUNTER_0	0U /**< Metric Counter 0 Register Index */
#define XAPM_METRIC_COUNTER_1	1U /**< Metric Counter 1 Register Index */
#define XAPM_METRIC_COUNTER_2	2U /**< Metric Counter 2 Register Index */
#define XAPM_METRIC_COUNTER_3	3U /**< Metric Counter 3 Register Index */
#define XAPM_METRIC_COUNTER_4	4U /**< Metric Counter 4 Register Index */
#define XAPM_METRIC_COUNTER_5	5U /**< Metric Counter 5 Register Index */
#define XAPM_METRIC_COUNTER_6	6U /**< Metric Counter 6 Register Index */
#define XAPM_METRIC_COUNTER_7	7U /**< Metric Counter 7 Register Index */
#define XAPM_METRIC_COUNTER_8	8U /**< Metric Counter 8 Register Index */
#define XAPM_METRIC_COUNTER_9	9U /**< Metric Counter 9 Register Index */

/*@}*/

/**
 * @name Indices for Incrementers and Sampled Incrementers used with
 * 	 XAxiPmon_GetIncrementer and XAxiPmon_GetSampledIncrementer APIs
 * @{
 */

#define XAPM_INCREMENTER_0	0U /**< Metric Counter 0 Register Index */
#define XAPM_INCREMENTER_1	1U /**< Metric Counter 0 Register Index */
#define XAPM_INCREMENTER_2	2U /**< Metric Counter 0 Register Index */
#define XAPM_INCREMENTER_3	3U /**< Metric Counter 0 Register Index */
#define XAPM_INCREMENTER_4	4U /**< Metric Counter 0 Register Index */
#define XAPM_INCREMENTER_5	5U /**< Metric Counter 0 Register Index */
#define XAPM_INCREMENTER_6	6U /**< Metric Counter 0 Register Index */
#define XAPM_INCREMENTER_7	7U /**< Metric Counter 0 Register Index */
#define XAPM_INCREMENTER_8	8U /**< Metric Counter 0 Register Index */
#define XAPM_INCREMENTER_9	9U /**< Metric Counter 0 Register Index */

/*@}*/

/**
 * @name Macros for Metric Selector Settings
 * @{
 */

#define XAPM_METRIC_SET_0		0U /**< Write Transaction Count */
#define XAPM_METRIC_SET_1		1U /**< Read Transaction Count */
#define XAPM_METRIC_SET_2		2U /**< Write Byte Count */
#define XAPM_METRIC_SET_3		3U /**< Read Byte Count */
#define XAPM_METRIC_SET_4		4U /**< Write Beat Count */
#define XAPM_METRIC_SET_5		5U /**< Total Read Latency */
#define XAPM_METRIC_SET_6		6U /**< Total Write Latency */
#define XAPM_METRIC_SET_7		7U /**< Slv_Wr_Idle_Cnt */
#define XAPM_METRIC_SET_8		8U /**< Mst_Rd_Idle_Cnt */
#define XAPM_METRIC_SET_9		9U /**< Num_BValids */
#define XAPM_METRIC_SET_10		10U /**< Num_WLasts */
#define XAPM_METRIC_SET_11		11U /**< Num_RLasts */
#define XAPM_METRIC_SET_12		12U /**< Minimum Write Latency */
#define XAPM_METRIC_SET_13		13U /**< Maximum Write Latency */
#define XAPM_METRIC_SET_14		14U /**< Minimum Read Latency */
#define XAPM_METRIC_SET_15		15U /**< Maximum Read Latency */
#define XAPM_METRIC_SET_16		16U /**< Transfer Cycle Count */
#define XAPM_METRIC_SET_17		17U /**< Packet Count */
#define XAPM_METRIC_SET_18		18U /**< Data Byte Count */
#define XAPM_METRIC_SET_19		19U /**< Position Byte Count */
#define XAPM_METRIC_SET_20		20U /**< Null Byte Count */
#define XAPM_METRIC_SET_21		21U /**< Slv_Idle_Cnt */
#define XAPM_METRIC_SET_22		22U /**< Mst_Idle_Cnt */
#define XAPM_METRIC_SET_30		30U /**< External event count */


/*@}*/


/**
 * @name Macros for Maximum number of Agents
 * @{
 */

#define XAPM_MAX_AGENTS 	8U /**< Maximum number of Agents */

/*@}*/

/**
 * @name Macros for Flags in Flag Enable Control Register
 * @{
 */

#define XAPM_FLAG_WRADDR	0x00000001 /**< Write Address Flag */
#define XAPM_FLAG_FIRSTWR	0x00000002 /**< First Write Flag */
#define XAPM_FLAG_LASTWR	0x00000004 /**< Last Write Flag */
#define XAPM_FLAG_RESPONSE	0x00000008 /**< Response Flag */
#define XAPM_FLAG_RDADDR	0x00000010 /**< Read Address Flag */
#define XAPM_FLAG_FIRSTRD	0x00000020 /**< First Read Flag */
#define XAPM_FLAG_LASTRD	0x00000040 /**< Last Read Flag */
#define XAPM_FLAG_SWDATA	0x00010000 /**< Software-written Data Flag */
#define XAPM_FLAG_EVENT		0x00020000 /**< Last Read Flag */
#define XAPM_FLAG_EVNTSTOP	0x00040000 /**< Last Read Flag */
#define XAPM_FLAG_EVNTSTART	0x00080000 /**< Last Read Flag */
#define XAPM_FLAG_GCCOVF	0x00100000 /**< Global Clock Counter Overflow
					     *  Flag */
#define XAPM_FLAG_SCLAPSE	0x00200000 /**< Sample Counter Lapse Flag */
#define XAPM_FLAG_MC0		0x00400000U /**< Metric Counter 0 Flag */
#define XAPM_FLAG_MC1		0x00800000U /**< Metric Counter 1 Flag */
#define XAPM_FLAG_MC2		0x01000000U /**< Metric Counter 2 Flag */
#define XAPM_FLAG_MC3		0x02000000U /**< Metric Counter 3 Flag */
#define XAPM_FLAG_MC4		0x04000000U /**< Metric Counter 4 Flag */
#define XAPM_FLAG_MC5		0x08000000U /**< Metric Counter 5 Flag */
#define XAPM_FLAG_MC6		0x10000000U /**< Metric Counter 6 Flag */
#define XAPM_FLAG_MC7		0x20000000U /**< Metric Counter 7 Flag */
#define XAPM_FLAG_MC8		0x40000000U /**< Metric Counter 8 Flag */
#define XAPM_FLAG_MC9		0x80000000U /**< Metric Counter 9 Flag */

/*@}*/

/**
 * @name Macros for Read/Write Latency Start and End points
 * @{
 */
#define XAPM_LATENCY_ADDR_ISSUE		0U /**< Address Issue as start
					point for Latency calculation*/
#define XAPM_LATENCY_ADDR_ACCEPT	1U /**< Address Acceptance as start
					point for Latency calculation*/
#define XAPM_LATENCY_LASTRD		0U /**< Last Read as end point for
					Latency calculation */
#define XAPM_LATENCY_LASTWR		0U /**< Last Write as end point for
					Latency calculation */
#define XAPM_LATENCY_FIRSTRD		1U /**< First Read as end point for
					Latency calculation */
#define XAPM_LATENCY_FIRSTWR		1U /**< First Write as end point for
					Latency calculation */

/*@}*/

/**
 * @name Macros for Modes of APM
 * @{
 */

#define XAPM_MODE_TRACE			2U /**< APM in Trace mode */

#define XAPM_MODE_PROFILE		1U /**< APM in Profile mode */

#define XAPM_MODE_ADVANCED		0U /**< APM in Advanced mode */

/*@}*/

/**************************** Type Definitions *******************************/

/**
 * This typedef contains configuration information for the AXI Performance
 * Monitor device.
 */
typedef struct {
	u16 DeviceId;			/**< Unique ID of device */
	UINTPTR BaseAddress;		/**< Device base address */
	s32 GlobalClkCounterWidth;	/**< Global Clock Counter Width */
	s32 MetricSampleCounterWidth ;	/**< Metric Sample Counters Width */
	u8  IsEventCount;		/**< Event Count Enabled 1 - enabled
							   0 - not enabled */
	u8  NumberofSlots;		/**< Number of Monitor Slots */
	u8  NumberofCounters;		/**< Number of Counters */
	u8  HaveSampledCounters;	/**< Have Sampled Counters 1 - present
							    0 - Not present */
	u8 IsEventLog;			/**< Event Logging Enabled 1 - enabled
							    0 - Not enabled */
	u32 FifoDepth;			/**< Event Log FIFO Depth */
	u32 FifoWidth;			/**< Event Log FIFO Width */
	u32 TidWidth; 			/**< Streaming Interface TID Width */
	u8  ScaleFactor;		/**< Event Count Scaling factor */
	u8  ModeAdvanced;		/**< Advanced Mode */
	u8  ModeProfile;		/**< Profile Mode */
	u8  ModeTrace;			/**< Trace Mode */
	u8  Is32BitFiltering;   /**< 32 bit filtering enabled */
} XAxiPmon_Config;


/**
 * The driver's instance data. The user is required to allocate a variable
 * of this type for every AXI Performance Monitor device in system. A pointer
 * to a variable of this type is then passed to the driver API functions.
 */
typedef struct {
	XAxiPmon_Config Config;	/**< XAxiPmon_Config of current device */
	u32  IsReady;		/**< Device is initialized and ready  */
	u8   Mode;		/**< APM Mode */
} XAxiPmon;

/***************** Macros (Inline Functions) Definitions ********************/


/****************************************************************************/
/**
*
* This routine enables the Global Interrupt.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None.
*
* @note		C-Style signature:
*		void XAxiPmon_IntrGlobalEnable(XAxiPmon *InstancePtr)
*
*****************************************************************************/
#define XAxiPmon_IntrGlobalEnable(InstancePtr)			\
	XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress, 	\
			XAPM_GIE_OFFSET, 1)


/****************************************************************************/
/**
*
* This routine disables the Global Interrupt.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None.
*
* @note		C-Style signature:
*		void XAxiPmon_IntrGlobalDisable(XAxiPmon *InstancePtr)
*
*****************************************************************************/
#define XAxiPmon_IntrGlobalDisable(InstancePtr)				\
	XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress, 		\
				XAPM_GIE_OFFSET, 0)


/****************************************************************************/
/**
*
* This routine enables interrupt(s). Use the XAPM_IXR_* constants defined in
* xaxipmon_hw.h to create the bit-mask to enable interrupts.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	Mask is the mask to enable. Bit positions of 1 will be enabled.
*		Bit positions of 0 will keep the previous setting. This mask is
*		formed by OR'ing XAPM_IXR__* bits defined in xaxipmon_hw.h.
*
* @return	None.
*
* @note		C-Style signature:
*		void XAxiPmon_IntrEnable(XAxiPmon *InstancePtr, u32 Mask)
*
*****************************************************************************/
#define XAxiPmon_IntrEnable(InstancePtr, Mask)				     \
	XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress, XAPM_IE_OFFSET, \
			XAxiPmon_ReadReg((InstancePtr)->Config.BaseAddress, \
			XAPM_IE_OFFSET) | (Mask));


/****************************************************************************/
/**
*
* This routine disable interrupt(s). Use the XAPM_IXR_* constants defined in
* xaxipmon_hw.h to create the bit-mask to disable interrupts.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	Mask is the mask to disable. Bit positions of 1 will be
*		disabled. Bit positions of 0 will keep the previous setting.
*		This mask is formed by OR'ing XAPM_IXR_* bits defined in
*		xaxipmon_hw.h.
*
* @return	None.
*
* @note		C-Style signature:
*		void XAxiPmon_IntrEnable(XAxiPmon *InstancePtr, u32 Mask)
*
*****************************************************************************/
#define XAxiPmon_IntrDisable(InstancePtr, Mask)				     \
	XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress, XAPM_IE_OFFSET, \
			XAxiPmon_ReadReg((InstancePtr)->Config.BaseAddress, \
			XAPM_IE_OFFSET) | (Mask));

/****************************************************************************/
/**
*
* This routine clears the specified interrupt(s).
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param	Mask is the mask to clear. Bit positions of 1 will be cleared.
*		This mask is formed by OR'ing XAPM_IXR_* bits defined in
*		xaxipmon_hw.h.
*
* @return	None.
*
* @note		C-Style signature:
*		void XAxiPmon_IntrClear(XAxiPmon *InstancePtr, u32 Mask)
*
*****************************************************************************/
#define XAxiPmon_IntrClear(InstancePtr, Mask)				     \
	XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress, XAPM_IS_OFFSET, \
			XAxiPmon_ReadReg((InstancePtr)->Config.BaseAddress, \
			XAPM_IS_OFFSET) | (Mask));

/****************************************************************************/
/**
*
* This routine returns the Interrupt Status Register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	Interrupt Status Register contents
*
* @note		C-Style signature:
*		void XAxiPmon_IntrClear(XAxiPmon *InstancePtr)
*
*****************************************************************************/
#define XAxiPmon_IntrGetStatus(InstancePtr)				     \
			XAxiPmon_ReadReg((InstancePtr)->Config.BaseAddress, \
			XAPM_IS_OFFSET);

/****************************************************************************/
/**
*
* This function enables the Global Clock Counter.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None
*
* @note		C-Style signature:
*		void XAxiPmon_EnableGlobalClkCounter(XAxiPmon *InstancePtr)
*
*****************************************************************************/
#define XAxiPmon_EnableGlobalClkCounter(InstancePtr) \
	XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress, XAPM_CTL_OFFSET, \
			XAxiPmon_ReadReg((InstancePtr)->Config.BaseAddress, \
			XAPM_CTL_OFFSET) | XAPM_CR_GCC_ENABLE_MASK);

/****************************************************************************/
/**
*
* This function disbles the Global Clock Counter.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None
*
* @note		C-Style signature:
*		void XAxiPmon_DisableGlobalClkCounter(XAxiPmon *InstancePtr)
*
*****************************************************************************/
#define XAxiPmon_DisableGlobalClkCounter(InstancePtr) \
	XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress, XAPM_CTL_OFFSET, \
			XAxiPmon_ReadReg((InstancePtr)->Config.BaseAddress, \
			XAPM_CTL_OFFSET) & ~(XAPM_CR_GCC_ENABLE_MASK));

/****************************************************************************/
/**
*
* This function enables the specified flag in Flag Control Register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param 	Flag is one of the XAPM_FLAG_* masks defined in xaxipmon.h
*
* @return	None
*
* @note		C-Style signature:
*		void XAxiPmon_EnableFlag(XAxiPmon *InstancePtr)
*
*****************************************************************************/
#define XAxiPmon_EnableFlag(InstancePtr, Flag) \
	XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress, XAPM_FEC_OFFSET, \
			XAxiPmon_ReadReg((InstancePtr)->Config.BaseAddress, \
			XAPM_FEC_OFFSET) | (Flag));

/****************************************************************************/
/**
*
* This function disables the specified flag in Flag Control Register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
* @param 	Flag is one of the XAPM_FLAG_* masks defined in xaxipmon.h*
* @return	None
*
* @note		C-Style signature:
*		void XAxiPmon_DisableFlag(XAxiPmon *InstancePtr)
*
*****************************************************************************/
#define XAxiPmon_DisableFlag(InstancePtr, Flag) \
	XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress, XAPM_FEC_OFFSET, \
			XAxiPmon_ReadReg((InstancePtr)->Config.BaseAddress, \
			XAPM_FEC_OFFSET) & ~(Flag));

/****************************************************************************/
/**
*
* This function loads the sample interval register value into the sample
* interval counter.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None
*
* @note		C-Style signature:
*		void XAxiPmon_LoadSampleIntervalCounter(XAxiPmon *InstancePtr)
*
*****************************************************************************/
#define XAxiPmon_LoadSampleIntervalCounter(InstancePtr) \
       XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress, XAPM_SICR_OFFSET, \
							XAPM_SICR_LOAD_MASK);



/****************************************************************************/
/**
*
* This enables the down count of the sample interval counter.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None
*
* @note		C-Style signature:
*	   void XAxiPmon_EnableSampleIntervalCounter(XAxiPmon *InstancePtr)
*
*****************************************************************************/
#define XAxiPmon_EnableSampleIntervalCounter(InstancePtr) \
	XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress, XAPM_SICR_OFFSET,\
							XAPM_SICR_ENABLE_MASK);


/****************************************************************************/
/**
*
* This disables the down count of the sample interval counter.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None
*
* @note		C-Style signature:
*	    void XAxiPmon_DisableSampleIntervalCounter(XAxiPmon *InstancePtr)
*
*****************************************************************************/
#define XAxiPmon_DisableSampleIntervalCounter(InstancePtr) \
	XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress, XAPM_SICR_OFFSET, \
			XAxiPmon_ReadReg((InstancePtr)->Config.BaseAddress, \
			XAPM_SICR_OFFSET) & ~(XAPM_SICR_ENABLE_MASK));

/****************************************************************************/
/**
*
* This enables Reset of Metric Counters when Sample Interval Counter lapses.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None
*
* @note		C-Style signature:
*		void XAxiPmon_EnableMetricCounterReset(XAxiPmon *InstancePtr)
*
*****************************************************************************/
#define XAxiPmon_EnableMetricCounterReset(InstancePtr) \
	XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress, XAPM_SICR_OFFSET,\
						XAPM_SICR_MCNTR_RST_MASK);

/****************************************************************************/
/**
*
* This disables the down count of the sample interval counter.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None
*
* @note		C-Style signature:
*		void XAxiPmon_DisableMetricCounterReset(XAxiPmon *InstancePtr)
*
*****************************************************************************/
#define XAxiPmon_DisableMetricCounterReset(InstancePtr) \
       XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress, XAPM_SICR_OFFSET, \
			XAxiPmon_ReadReg((InstancePtr)->Config.BaseAddress, \
			XAPM_SICR_OFFSET) & ~(XAPM_SICR_MCNTR_RST_MASK));

/****************************************************************************/
/**
*
* This function enables the ID Filter Masking.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None
*
* @note		C-Style signature:
*		void XAxiPmon_EnableIDFilter(XAxiPmon *InstancePtr)
*
*****************************************************************************/
#define XAxiPmon_EnableIDFilter(InstancePtr) \
	XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress, XAPM_CTL_OFFSET, \
			XAxiPmon_ReadReg((InstancePtr)->Config.BaseAddress, \
			XAPM_CTL_OFFSET) | XAPM_CR_IDFILTER_ENABLE_MASK);

/****************************************************************************/
/**
*
* This function disbles the ID Filter masking.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	None
*
* @note		C-Style signature:
*		void XAxiPmon_DisableIDFilter(XAxiPmon *InstancePtr)
*
*****************************************************************************/
#define XAxiPmon_DisableIDFilter(InstancePtr) \
	XAxiPmon_WriteReg((InstancePtr)->Config.BaseAddress, XAPM_CTL_OFFSET, \
			XAxiPmon_ReadReg((InstancePtr)->Config.BaseAddress, \
			XAPM_CTL_OFFSET) & ~(XAPM_CR_IDFILTER_ENABLE_MASK));

/****************************************************************************/
/**
*
* This function samples Metric Counters to Sampled Metric Counters by
* reading Sample Register and also returns interval. i.e. the number of
* clocks in between previous read to the current read of sample register.
*
* @param	InstancePtr is a pointer to the XAxiPmon instance.
*
* @return	Interval. i.e. the number of clocks in between previous
*		read to the current read of sample register.
*
* @note		C-Style signature:
*		u32 XAxiPmon_SampleMetrics(XAxiPmon *InstancePtr)
*
*****************************************************************************/
#define XAxiPmon_SampleMetrics(InstancePtr) \
       XAxiPmon_ReadReg((InstancePtr)->Config.BaseAddress, XAPM_SR_OFFSET);


/************************** Function Prototypes *****************************/

/**
 * Functions in xaxipmon_sinit.c
 */
XAxiPmon_Config *XAxiPmon_LookupConfig(u16 DeviceId);

/**
 * Functions in xaxipmon.c
 */
s32 XAxiPmon_CfgInitialize(XAxiPmon *InstancePtr,
		XAxiPmon_Config *ConfigPtr, UINTPTR EffectiveAddr);

s32 XAxiPmon_ResetMetricCounter(XAxiPmon *InstancePtr);

void XAxiPmon_ResetGlobalClkCounter(XAxiPmon *InstancePtr);

s32 XAxiPmon_ResetFifo(XAxiPmon *InstancePtr);

void XAxiPmon_SetIncrementerRange(XAxiPmon *InstancePtr, u8 IncrementerNum,
					u16 RangeUpper,	u16 RangeLower);

void XAxiPmon_GetIncrementerRange(XAxiPmon *InstancePtr, u8 IncrementerNum,
				u16 *RangeUpper, u16 *RangeLower);

void XAxiPmon_SetSampleInterval(XAxiPmon *InstancePtr, u32 SampleInterval);

void XAxiPmon_GetSampleInterval(XAxiPmon *InstancePtr, u32 *SampleInterval);

s32 XAxiPmon_SetMetrics(XAxiPmon *InstancePtr, u8 Slot, u8 Metrics,
							u8 CounterNum);

s32 XAxiPmon_GetMetrics(XAxiPmon *InstancePtr, u8 CounterNum, u8 *Metrics,
								u8 *Slot);
void XAxiPmon_GetGlobalClkCounter(XAxiPmon *InstancePtr,u32 *CntHighValue,
							u32 *CntLowValue);

u32 XAxiPmon_GetMetricCounter(XAxiPmon *InstancePtr, u32 CounterNum);

u32 XAxiPmon_GetSampledMetricCounter(XAxiPmon *InstancePtr, u32 CounterNum);

u32 XAxiPmon_GetIncrementer(XAxiPmon *InstancePtr, u32 IncrementerNum);

u32 XAxiPmon_GetSampledIncrementer(XAxiPmon *InstancePtr, u32 IncrementerNum);

void XAxiPmon_SetSwDataReg(XAxiPmon *InstancePtr, u32 SwData);

u32 XAxiPmon_GetSwDataReg(XAxiPmon *InstancePtr);

s32 XAxiPmon_StartEventLog(XAxiPmon *InstancePtr, u32 FlagEnables);

s32 XAxiPmon_StopEventLog(XAxiPmon *InstancePtr);

s32 XAxiPmon_StartCounters(XAxiPmon *InstancePtr, u32 SampleInterval);

s32 XAxiPmon_StopCounters(XAxiPmon *InstancePtr);

void XAxiPmon_EnableMetricsCounter(XAxiPmon *InstancePtr);

void XAxiPmon_DisableMetricsCounter(XAxiPmon *InstancePtr);

void XAxiPmon_SetLogEnableRanges(XAxiPmon *InstancePtr, u32 CounterNum,
					u16 RangeUpper, u16 RangeLower);

void XAxiPmon_GetLogEnableRanges(XAxiPmon *InstancePtr, u32 CounterNum,
					u16 *RangeUpper, u16 *RangeLower);

void XAxiPmon_EnableEventLog(XAxiPmon *InstancePtr);

void XAxiPmon_EnableMetricCounterTrigger(XAxiPmon *InstancePtr);

void XAxiPmon_DisableMetricCounterTrigger(XAxiPmon *InstancePtr);

void XAxiPmon_EnableEventLogTrigger(XAxiPmon *InstancePtr);

void XAxiPmon_DisableEventLogTrigger(XAxiPmon *InstancePtr);

const char * XAxiPmon_GetMetricName(u8 Metrics);

void XAxiPmon_SetWriteId(XAxiPmon *InstancePtr, u32 WriteId);

void XAxiPmon_SetReadId(XAxiPmon *InstancePtr, u32 ReadId);

u32 XAxiPmon_GetWriteId(XAxiPmon *InstancePtr);

u32 XAxiPmon_GetReadId(XAxiPmon *InstancePtr);

void XAxiPmon_SetWrLatencyStart(XAxiPmon *InstancePtr, u8 Param);

void XAxiPmon_SetWrLatencyEnd(XAxiPmon *InstancePtr, u8 Param);

void XAxiPmon_SetRdLatencyStart(XAxiPmon *InstancePtr, u8 Param);

void XAxiPmon_SetRdLatencyEnd(XAxiPmon *InstancePtr, u8 Param);

u8 XAxiPmon_GetWrLatencyStart(XAxiPmon *InstancePtr);

u8 XAxiPmon_GetWrLatencyEnd(XAxiPmon *InstancePtr);

u8 XAxiPmon_GetRdLatencyStart(XAxiPmon *InstancePtr);

u8 XAxiPmon_GetRdLatencyEnd(XAxiPmon *InstancePtr);

void XAxiPmon_SetWriteIdMask(XAxiPmon *InstancePtr, u32 WrMask);

void XAxiPmon_SetReadIdMask(XAxiPmon *InstancePtr, u32 RdMask);

u32 XAxiPmon_GetWriteIdMask(XAxiPmon *InstancePtr);

u32 XAxiPmon_GetReadIdMask(XAxiPmon *InstancePtr);


/**
 * Functions in xaxipmon_selftest.c
 */
s32 XAxiPmon_SelfTest(XAxiPmon *InstancePtr);

#ifdef __cplusplus
}
#endif

#endif  /* End of protection macro. */
/** @} */
