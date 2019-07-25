/******************************************************************************
*
* Copyright (C) 2017 Xilinx, Inc.  All rights reserved.
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
* @file xresetps.h
* @addtogroup xresetps_v1_0
* @{
* @details
*
* The Xilinx Reset Controller driver supports the following features:
*   - Assert reset for specific peripheral.
*   - Deassert reset for specific peripheral.
*   - Pulse reset for specific peripheral.
*   - Get reset status for specific peripheral.
*
* This driver is intended to be RTOS and processor independent. It works with
* physical addresses only.  Any needs for dynamic memory management, threads
* or thread mutual exclusion, virtual memory, or cache control must be
* satisfied by the layer above this driver.
*
* <pre>
* MODIFICATION HISTORY:
* Ver   Who    Date     Changes
* ----- ------ -------- -----------------------------------------------
* 1.00  cjp    09/05/17 First release
* </pre>
*
******************************************************************************/
#ifndef XRESETPS_H		/* prevent circular inclusions */
#define XRESETPS_H		/* by using protection macros */

#ifdef __cplusplus
extern "C" {
#endif

/***************************** Include Files *********************************/
#include "xil_types.h"
#include "xil_assert.h"
#include "xstatus.h"
#include "xresetps_hw.h"

#if defined (__aarch64__)
#include "xil_smc.h"
#endif

/************************** Constant Definitions *****************************/
/*
 * Constants for supported/Not supported reset actions
 */
#define XRESETPS_SUP                   1
#define XRESETPS_NOSUP                 0

/**************************** Type Definitions *******************************/
/**
 * This typedef contains configuration information for the device.
 */
typedef struct {
	u16 DeviceId;                    /**< Unique ID of device */
	u32 BaseAddress;                 /**< Base address of the device */
} XResetPs_Config;

/**
 * The XResetPs driver instance data. The user is required to allocate a
 * variable of this type for every reset controller device in the system.
 * A pointer to a variable of this type is then passed to the driver API
 * functions.
 */
typedef struct {
	XResetPs_Config Config;          /**< Hardware Configuration */
} XResetPs;

/**
 * This typedef defines type of pulse reset to be executed for peripherals.
 * 3 type of pulse reset are possible:
 * 	1. Pulse with no delay and no power state validation
 * 	2. Pulse with delay but no power state validation
 * 	3. Pulse with delay and power state validation
 */
typedef enum {
	XRESETPS_PT_NO_DLY_NO_PSCHK,     /**< No delay, no power state check */
	XRESETPS_PT_DLY_NO_PSCHK,        /**< Delay, no power state check */
	XRESETPS_PT_DLY_PSCHK,           /**< Delay, power state check */
	XRESETPS_PT_INVALID,             /**< Invalid pulse type */
} XResetPs_PulseTypes;

/**
 * This typedef defines reset actions on the peripherals.
 */
typedef enum {
	XRESETPS_RSTACT_RELEASE,
	XRESETPS_RSTACT_ASSERT,
	XRESETPS_RSTACT_PULSE,
} XresetPs_ResetAction;

/**
 * This typedef defines resetIDs of peripherals maps to PMUFW resetIDs. This
 * resetIDs are not offseted by 1000 and are relative.
 */
typedef enum {
	XRESETPS_RSTID_START,
	XRESETPS_RSTID_PCIE_CFG = XRESETPS_RSTID_START,
	XRESETPS_RSTID_PCIE_BRIDGE,
	XRESETPS_RSTID_PCIE_CTRL,
	XRESETPS_RSTID_DP,
	XRESETPS_RSTID_SWDT_CRF,
	XRESETPS_RSTID_AFI_FM5,
	XRESETPS_RSTID_AFI_FM4,
	XRESETPS_RSTID_AFI_FM3,
	XRESETPS_RSTID_AFI_FM2,
	XRESETPS_RSTID_AFI_FM1,
	XRESETPS_RSTID_AFI_FM0,
	XRESETPS_RSTID_GDMA,
	XRESETPS_RSTID_GPU_PP1,
	XRESETPS_RSTID_GPU_PP0,
	XRESETPS_RSTID_GPU,
	XRESETPS_RSTID_GT,
	XRESETPS_RSTID_SATA,
	XRESETPS_RSTID_ACPU3_PWRON,
	XRESETPS_RSTID_ACPU2_PWRON,
	XRESETPS_RSTID_ACPU1_PWRON,
	XRESETPS_RSTID_ACPU0_PWRON,
	XRESETPS_RSTID_APU_L2,
	XRESETPS_RSTID_ACPU3,
	XRESETPS_RSTID_ACPU2,
	XRESETPS_RSTID_ACPU1,
	XRESETPS_RSTID_ACPU0,
	XRESETPS_RSTID_DDR,
	XRESETPS_RSTID_APM_FPD,
	XRESETPS_RSTID_SOFT,
	XRESETPS_RSTID_GEM0,
	XRESETPS_RSTID_GEM1,
	XRESETPS_RSTID_GEM2,
	XRESETPS_RSTID_GEM3,
	XRESETPS_RSTID_QSPI,
	XRESETPS_RSTID_UART0,
	XRESETPS_RSTID_UART1,
	XRESETPS_RSTID_SPI0,
	XRESETPS_RSTID_SPI1,
	XRESETPS_RSTID_SDIO0,
	XRESETPS_RSTID_SDIO1,
	XRESETPS_RSTID_CAN0,
	XRESETPS_RSTID_CAN1,
	XRESETPS_RSTID_I2C0,
	XRESETPS_RSTID_I2C1,
	XRESETPS_RSTID_TTC0,
	XRESETPS_RSTID_TTC1,
	XRESETPS_RSTID_TTC2,
	XRESETPS_RSTID_TTC3,
	XRESETPS_RSTID_SWDT_CRL,
	XRESETPS_RSTID_NAND,
	XRESETPS_RSTID_ADMA,
	XRESETPS_RSTID_GPIO,
	XRESETPS_RSTID_IOU_CC,
	XRESETPS_RSTID_TIMESTAMP,
	XRESETPS_RSTID_RPU_R50,
	XRESETPS_RSTID_RPU_R51,
	XRESETPS_RSTID_RPU_AMBA,
	XRESETPS_RSTID_OCM,
	XRESETPS_RSTID_RPU_PGE,
	XRESETPS_RSTID_USB0_CORERESET,
	XRESETPS_RSTID_USB1_CORERESET,
	XRESETPS_RSTID_USB0_HIBERRESET,
	XRESETPS_RSTID_USB1_HIBERRESET,
	XRESETPS_RSTID_USB0_APB,
	XRESETPS_RSTID_USB1_APB,
	XRESETPS_RSTID_IPI,
	XRESETPS_RSTID_APM_LPD,
	XRESETPS_RSTID_RTC,
	XRESETPS_RSTID_SYSMON,
	XRESETPS_RSTID_AFI_FM6,
	XRESETPS_RSTID_LPD_SWDT,
	XRESETPS_RSTID_FPD,
	XRESETPS_RSTID_RPU_DBG1,
	XRESETPS_RSTID_RPU_DBG0,
	XRESETPS_RSTID_DBG_LPD,
	XRESETPS_RSTID_DBG_FPD,
	XRESETPS_RSTID_APLL,
	XRESETPS_RSTID_DPLL,
	XRESETPS_RSTID_VPLL,
	XRESETPS_RSTID_IOPLL,
	XRESETPS_RSTID_RPLL,
	XRESETPS_RSTID_GPO3PL0,
	XRESETPS_RSTID_GPO3PL1,
	XRESETPS_RSTID_GPO3PL2,
	XRESETPS_RSTID_GPO3PL3,
	XRESETPS_RSTID_GPO3PL4,
	XRESETPS_RSTID_GPO3PL5,
	XRESETPS_RSTID_GPO3PL6,
	XRESETPS_RSTID_GPO3PL7,
	XRESETPS_RSTID_GPO3PL8,
	XRESETPS_RSTID_GPO3PL9,
	XRESETPS_RSTID_GPO3PL10,
	XRESETPS_RSTID_GPO3PL11,
	XRESETPS_RSTID_GPO3PL12,
	XRESETPS_RSTID_GPO3PL13,
	XRESETPS_RSTID_GPO3PL14,
	XRESETPS_RSTID_GPO3PL15,
	XRESETPS_RSTID_GPO3PL16,
	XRESETPS_RSTID_GPO3PL17,
	XRESETPS_RSTID_GPO3PL18,
	XRESETPS_RSTID_GPO3PL19,
	XRESETPS_RSTID_GPO3PL20,
	XRESETPS_RSTID_GPO3PL21,
	XRESETPS_RSTID_GPO3PL22,
	XRESETPS_RSTID_GPO3PL23,
	XRESETPS_RSTID_GPO3PL24,
	XRESETPS_RSTID_GPO3PL25,
	XRESETPS_RSTID_GPO3PL26,
	XRESETPS_RSTID_GPO3PL27,
	XRESETPS_RSTID_GPO3PL28,
	XRESETPS_RSTID_GPO3PL29,
	XRESETPS_RSTID_GPO3PL30,
	XRESETPS_RSTID_GPO3PL31,
	XRESETPS_RSTID_RPU_LS,
	XRESETPS_RSTID_PS_ONLY,
	XRESETPS_RSTID_PL,
	XRESETPS_RSTID_END = XRESETPS_RSTID_PL,
} XResetPs_RstId;

/**
 * This typedef defines possible values for  reset status of peripherals.
 */
typedef enum {
	XRESETPS_RESETRELEASED,
	XRESETPS_RESETASSERTED
} XResetPs_RstStatus;

/***************** Macros (Inline Functions) Definitions *********************/
/****************************************************************************/
/**
*
* Set supported reset action.
*
* @param        StatusSupport indicates if reset status check is supported
* @param        PulseSupport indicates if pulse reset action is supported
* @param        AssertSupport indicates if reset assert/deassert is supported
*
* @return	Supported reset actions
*
* @note         Here bit fields are used decide supported actions as defined
* 		below:
* 		BIT 1 - Assert/Deassert
* 		BIT 2 - Pulse
* 		BIT 3 - Reset status
* 		Bit set indicates corresponding action is supported and
* 		vice versa.
******************************************************************************/
#define XRESETPS_SUPPORTED_ACT(ResetSupport, PulseSupport, AssertSupport) \
		     ((ResetSupport << 2) | (PulseSupport << 1) | AssertSupport)

/****************************************************************************/
/**
*
* Check if assert/dessert reset is supported.
*
* @param        Actions is supported reset actions
*
* @return       1 - Supported
* 		0 - Not Supported
*
* @note         None.
*
******************************************************************************/
#define XRESETPS_CHK_ASSERT_SUPPORT(Actions) ((Actions & 0x1))

/****************************************************************************/
/**
*
* Check if pulse reset is supported.
*
* @param        Actions is supported reset actions
*
* @return       1 - Supported
* 		0 - Not Supported
*
* @note         None.
*
******************************************************************************/
#define XRESETPS_CHK_PULSE_SUPPORT(Actions)  ((Actions & 0x2) >> 1)

/****************************************************************************/
/**
*
* Check if Status check is supported.
*
* @param        Actions is supported reset actions
*
* @return       1 - Supported
* 		0 - Not Supported
*
* @note         None.
*
******************************************************************************/
#define XRESETPS_CHK_STATUS_SUPPORT(Actions) ((Actions & 0x4) >> 2)

/****************************************************************************/
/**
*
* Read the given register.
*
* @param        RegAddress is the address of the register to read
*
* @return       The 32-bit value of the register
*
* @note         None.
*
******************************************************************************/
#define XResetPs_ReadReg(RegAddress) \
				Xil_In32((u32)RegAddress)

/****************************************************************************/
/**
*
* Write the given register.
*
* @param        RegAddress is the address of the register to write
* @param        Data is the 32-bit value to write to the register
*
* @return       None.
*
* @note         None.
*
******************************************************************************/
#define XResetPs_WriteReg(RegAddress, Data) \
				Xil_Out32((u32)RegAddress, (u32)Data)

/************************** Function Prototypes ******************************/

/*
 * Lookup configuration in xresetps_sinit.c.
 */
XResetPs_Config *XResetPs_LookupConfig(u16 DeviceId);

/*
 * Interface functions in xresetps.c
 */
XStatus XResetPs_CfgInitialize(XResetPs *InstancePtr,
			      XResetPs_Config *ConfigPtr, u32 EffectiveAddress);
XStatus XResetPs_ResetAssert(XResetPs *InstancePtr,
						  const XResetPs_RstId ResetID);
XStatus XResetPs_ResetDeassert(XResetPs *InstancePtr,
						  const XResetPs_RstId ResetID);
XStatus XResetPs_ResetPulse(XResetPs *InstancePtr,
						  const XResetPs_RstId ResetID);
XStatus XResetPs_ResetStatus(XResetPs *InstancePtr,
		      const XResetPs_RstId ResetID, XResetPs_RstStatus *Status);

#ifdef __cplusplus
}
#endif
#endif /* end of protection macro */
/** @} */
