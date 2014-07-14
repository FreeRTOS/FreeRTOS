/******************************************************************************
*
* (c) Copyright 2010-14 Xilinx, Inc. All rights reserved.
*
* This file contains confidential and proprietary information of Xilinx, Inc.
* and is protected under U.S. and international copyright and other
* intellectual property laws.
*
* DISCLAIMER
* This disclaimer is not a license and does not grant any rights to the
* materials distributed herewith. Except as otherwise provided in a valid
* license issued to you by Xilinx, and to the maximum extent permitted by
* applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND WITH ALL
* FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES AND CONDITIONS, EXPRESS,
* IMPLIED, OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF
* MERCHANTABILITY, NON-INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE;
* and (2) Xilinx shall not be liable (whether in contract or tort, including
* negligence, or under any other theory of liability) for any loss or damage
* of any kind or nature related to, arising under or in connection with these
* materials, including for any direct, or any indirect, special, incidental,
* or consequential loss or damage (including loss of data, profits, goodwill,
* or any type of loss or damage suffered as a result of any action brought by
* a third party) even if such damage or loss was reasonably foreseeable or
* Xilinx had been advised of the possibility of the same.
*
* CRITICAL APPLICATIONS
* Xilinx products are not designed or intended to be fail-safe, or for use in
* any application requiring fail-safe performance, such as life-support or
* safety devices or systems, Class III medical devices, nuclear facilities,
* applications related to the deployment of airbags, or any other applications
* that could lead to death, personal injury, or severe property or
* environmental damage (individually and collectively, "Critical
* Applications"). Customer assumes the sole risk and liability of any use of
* Xilinx products in Critical Applications, subject only to applicable laws
* and regulations governing limitations on product liability.
*
* THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS PART OF THIS FILE
* AT ALL TIMES.
*
******************************************************************************/
/****************************************************************************/
/**
*
* @file xdevcfg.c
*
* This file contains the implementation of the interface functions for XDcfg
* driver. Refer to the header file xdevcfg.h for more detailed information.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who Date     Changes
* ----- --- -------- ---------------------------------------------
* 1.00a hvm 02/07/11 First release
* 2.00a nm  05/31/12 Updated the driver for CR 660835 so that input length for
*		     source/destination to the XDcfg_InitiateDma, XDcfg_Transfer
*		     APIs is words (32 bit) and not bytes.
* 		     Updated the notes for XDcfg_InitiateDma/XDcfg_Transfer APIs
*		     to add information that 2 LSBs of the Source/Destination
*		     address when equal to 2’b01 indicate the last DMA command
*		     of an overall transfer.
*		     Updated the XDcfg_Transfer function to use the
*		     Destination Address passed to this API for secure transfers
*		     instead of using 0xFFFFFFFF for CR 662197. This issue was
*		     resulting in the failure of secure transfers of
*		     non-bitstream images.
* 2.01a nm  08/27/12 Updated the XDcfg_Transfer API to clear the
*		     QUARTER_PCAP_RATE_EN bit in the control register for
*		     non secure writes for CR 675543.
* 2.02a nm  01/31/13 Fixed CR# 679335.
* 		     Added Setting and Clearing the internal PCAP loopback.
*		     Removed code for enabling/disabling AES engine as BootROM
*		     locks down this setting.
*		     Fixed CR# 681976.
*		     Skip Checking the PCFG_INIT in case of non-secure DMA
*		     loopback.
*		     Fixed CR# 699558.
*		     XDcfg_Transfer fails to transfer data in loopback mode.
* 2.03a nm  04/19/13 Fixed CR# 703728.
*		     Updated the register definitions as per the latest TRM
*		     version UG585 (v1.4) November 16, 2012.
* 3.0   kpc 21/02/14 Implemented new function XDcfg_ClearControlRegister
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xdevcfg.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/************************** Variable Definitions *****************************/

/****************************************************************************/
/**
*
* Initialize the Device Config Interface driver. This function
* must be called before other functions of the driver are called.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
* @param	ConfigPtr is the config structure.
* @param	EffectiveAddress is the base address for the device. It could be
*		a virtual address if address translation is supported in the
*		system, otherwise it is the physical address.
*
* @return
*		- XST_SUCCESS if initialization was successful.
*		- XST_DEVICE_IS_STARTED if the device has already been started.
*
* @note		The very first APB access to the Device Configuration Interface
*		block needs to be a write to the UNLOCK register with the value
*		of 0x757BDF0D. This step is to be done once after reset, any
*		other APB access has to come after this. The APB access is
*		considered illegal if the step is not done or if it is done
*		incorrectly. Furthermore, if any of efuse_sec_cfg[5:0] is high,
*		the following additional actions would be carried out.
*		In other words, if all bits are low, the following steps are not
*		done.
*			1. AES is disabled
*			2. All APB writes disabled
*			3. SoC debug fully enabled
*
******************************************************************************/
int XDcfg_CfgInitialize(XDcfg *InstancePtr,
			 XDcfg_Config *ConfigPtr, u32 EffectiveAddress)
{
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(ConfigPtr != NULL);

	/*
	 * If the device is started, disallow the initialize and return a
	 * status indicating it is started. This allows the user to stop the
	 * device and reinitialize, but prevents a user from inadvertently
	 * initializing.
	 */
	if (InstancePtr->IsStarted == XIL_COMPONENT_IS_STARTED) {
		return XST_DEVICE_IS_STARTED;
	}

	/*
	 * Copy configuration into instance.
	 */
	InstancePtr->Config.DeviceId = ConfigPtr->DeviceId;

	/*
	 * Save the base address pointer such that the registers of the block
	 * can be accessed and indicate it has not been started yet.
	 */
	InstancePtr->Config.BaseAddr = EffectiveAddress;
	InstancePtr->IsStarted = 0;


	/* Unlock the Device Configuration Interface */
	XDcfg_Unlock(InstancePtr);

	/*
	 * Indicate the instance is ready to use, successfully initialized.
	 */
	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;

	return XST_SUCCESS;
}

/****************************************************************************/
/**
*
* The functions enables the PCAP interface by setting the PCAP mode bit in the
* control register.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
*
* @return	None.
*
* @note		Enable FPGA programming	from PCAP interface. Enabling this bit
*		disables all the external interfaces from programming of FPGA
*		except for ICAP. The user needs to ensure that the FPGA is
*		programmed through either PCAP or ICAP.
*
*****************************************************************************/
void XDcfg_EnablePCAP(XDcfg *InstancePtr)
{
	u32 CtrlReg;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);


	CtrlReg = XDcfg_ReadReg(InstancePtr->Config.BaseAddr,
					XDCFG_CTRL_OFFSET);

	XDcfg_WriteReg(InstancePtr->Config.BaseAddr, XDCFG_CTRL_OFFSET,
			(CtrlReg | XDCFG_CTRL_PCAP_MODE_MASK));

}

/****************************************************************************/
/**
*
* The functions disables the PCAP interface by clearing the PCAP mode bit in
* the control register.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XDcfg_DisablePCAP(XDcfg *InstancePtr)
{
	u32 CtrlReg;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);


	CtrlReg = XDcfg_ReadReg(InstancePtr->Config.BaseAddr,
					XDCFG_CTRL_OFFSET);

	XDcfg_WriteReg(InstancePtr->Config.BaseAddr, XDCFG_CTRL_OFFSET,
			(CtrlReg & ( ~XDCFG_CTRL_PCAP_MODE_MASK)));

}

/****************************************************************************/
/**
*
* The function sets the contents of the Control Register.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
* @param	Mask is the 32 bit mask data to be written to the Register.
*		The mask definitions are defined in the xdevcfg_hw.h file.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XDcfg_SetControlRegister(XDcfg *InstancePtr, u32 Mask)
{
	u32 CtrlReg;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);


	CtrlReg = XDcfg_ReadReg(InstancePtr->Config.BaseAddr,
					XDCFG_CTRL_OFFSET);

	XDcfg_WriteReg(InstancePtr->Config.BaseAddr, XDCFG_CTRL_OFFSET,
			(CtrlReg | Mask));

}

/****************************************************************************/
/**
*
* The function Clears the specified bit positions of the Control Register.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
* @param	Mask is the 32 bit value which holds the bit positions to be cleared. 
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XDcfg_ClearControlRegister(XDcfg *InstancePtr, u32 Mask)
{
	u32 CtrlReg;
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);


	CtrlReg = XDcfg_ReadReg(InstancePtr->Config.BaseAddr,
					XDCFG_CTRL_OFFSET);

	XDcfg_WriteReg(InstancePtr->Config.BaseAddr, XDCFG_CTRL_OFFSET,
			(CtrlReg & ~Mask));

}

/****************************************************************************/
/**
*
* The function reads the contents of the Control Register.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
*
* @return	A 32-bit value representing the contents of the Control
*		Register.
*		Use the XDCFG_CTRL_*_MASK constants defined in xdevcfg_hw.h to
*		interpret the returned value.
*
* @note		None.
*
*****************************************************************************/
u32 XDcfg_GetControlRegister(XDcfg *InstancePtr)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the Control Register and return the value.
	 */
	return XDcfg_ReadReg(InstancePtr->Config.BaseAddr, XDCFG_CTRL_OFFSET);
}

/****************************************************************************/
/**
*
* The function sets the contents of the Lock Register. These bits
* can only be set to a 1. They will be cleared after a Power On Reset.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
* @param	Data is the 32 bit data to be written to the Register.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XDcfg_SetLockRegister(XDcfg *InstancePtr, u32 Data)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	XDcfg_WriteReg(InstancePtr->Config.BaseAddr, XDCFG_LOCK_OFFSET, Data);

}

/****************************************************************************/
/**
*
* The function reads the contents of the Lock Register.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
*
* @return	A 32-bit value representing the contents of the Lock
*		Register.
*		Use the XDCFG_CR_*_MASK constants defined in xdevcfg_hw.h to
*		interpret the returned value.
*
* @note		None.
*
*****************************************************************************/
u32 XDcfg_GetLockRegister(XDcfg *InstancePtr)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the Lock Register and return the value.
	 */
	return XDcfg_ReadReg(InstancePtr->Config.BaseAddr, XDCFG_LOCK_OFFSET);
}

/****************************************************************************/
/**
*
* The function sets the contents of the Configuration Register with the
* given value.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
* @param	Data is the 32 bit data to be written to the Register.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XDcfg_SetConfigRegister(XDcfg *InstancePtr, u32 Data)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	XDcfg_WriteReg(InstancePtr->Config.BaseAddr, XDCFG_CFG_OFFSET, Data);

}

/****************************************************************************/
/**
*
* The function reads the contents of the Configuration Register with the
* given value.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
*
* @return	A 32-bit value representing the contents of the Config
*		Register.
*		Use the XDCFG_CFG_*_MASK constants defined in xdevcfg_hw.h to
*		interpret the returned value.
*
* @note		None.
*
*****************************************************************************/
u32 XDcfg_GetConfigRegister(XDcfg *InstancePtr)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	return XDcfg_ReadReg(InstancePtr->Config.BaseAddr, XDCFG_CFG_OFFSET);

}

/****************************************************************************/
/**
*
* The function sets the contents of the Status Register.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
* @param	Data is the 32 bit data to be written to the Register.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
void XDcfg_SetStatusRegister(XDcfg *InstancePtr, u32 Data)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	XDcfg_WriteReg(InstancePtr->Config.BaseAddr, XDCFG_STATUS_OFFSET, Data);

}

/****************************************************************************/
/**
*
* The function reads the contents of the Status Register.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
*
* @return	A 32-bit value representing the contents of the Status
*		Register.
*		Use the XDCFG_STATUS_*_MASK constants defined in
*		xdevcfg_hw.h to interpret the returned value.
*
* @note		None.
*
*****************************************************************************/
u32 XDcfg_GetStatusRegister(XDcfg *InstancePtr)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the Status Register and return the value.
	 */
	return XDcfg_ReadReg(InstancePtr->Config.BaseAddr, XDCFG_STATUS_OFFSET);
}

/****************************************************************************/
/**
*
* The function sets the contents of the ROM Shadow Control Register.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
* @param	Data is the 32 bit data to be written to the Register.
*
* @return	None.
*
* @note		This register is can only be written and is used to control the
*		RAM shadow of 32 bit 4K page ROM pages in user mode
*
*****************************************************************************/
void XDcfg_SetRomShadowRegister(XDcfg *InstancePtr, u32 Data)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	XDcfg_WriteReg(InstancePtr->Config.BaseAddr, XDCFG_ROM_SHADOW_OFFSET,
				Data);

}

/****************************************************************************/
/**
*
* The function reads the contents of the Software ID Register.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
*
* @return	32 Bit boot software ID.
*
* @note		This register is locked for write once the system enters
*		usermode. Hence API for reading the register only is provided.
*
*****************************************************************************/
u32 XDcfg_GetSoftwareIdRegister(XDcfg *InstancePtr)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the Software ID Register and return the value.
	 */
	return XDcfg_ReadReg(InstancePtr->Config.BaseAddr, XDCFG_SW_ID_OFFSET);
}

/****************************************************************************/
/**
*
* The function sets the bit mask for the feature in Miscellaneous Control
* Register.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
* @param	Mask is the bit-mask of the feature to be set.
*
* @return	None.
*
* @note		None
*
*****************************************************************************/
void XDcfg_SetMiscControlRegister(XDcfg *InstancePtr, u32 Mask)
{
	u32 RegData;

	/*
	 * Assert the arguments.
	 */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);


	RegData = XDcfg_ReadReg(InstancePtr->Config.BaseAddr,
					XDCFG_MCTRL_OFFSET);

	XDcfg_WriteReg(InstancePtr->Config.BaseAddr, XDCFG_MCTRL_OFFSET,
				(RegData | Mask));
}

/****************************************************************************/
/**
*
* The function reads the contents of the Miscellaneous Control Register.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
*
* @return	32 Bit boot software ID.
*
* @note		This register is locked for write once the system enters
*		usermode. Hence API to reading the register only is provided.
*
*****************************************************************************/
u32 XDcfg_GetMiscControlRegister(XDcfg *InstancePtr)
{
	/*
	 * Assert the arguments.
	 */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/*
	 * Read the Miscellaneous Control Register and return the value.
	 */
	return XDcfg_ReadReg(InstancePtr->Config.BaseAddr, XDCFG_MCTRL_OFFSET);
}

/******************************************************************************/
/**
*
* This function checks if DMA command queue is full.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
*
* @return	XST_SUCCESS is the DMA is busy
*		XST_FAILURE if the DMA is idle
*
* @note		The DMA queue has a depth of two.
*
****************************************************************************/
u32 XDcfg_IsDmaBusy(XDcfg *InstancePtr)
{

	u32 RegData;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Read the PCAP status register for DMA status */
	RegData = XDcfg_ReadReg(InstancePtr->Config.BaseAddr,
					XDCFG_STATUS_OFFSET);

	if ((RegData & XDCFG_STATUS_DMA_CMD_Q_F_MASK) ==
				XDCFG_STATUS_DMA_CMD_Q_F_MASK){
		return XST_SUCCESS;
	}

	return XST_FAILURE;
}

/******************************************************************************/
/**
*
* This function initiates the DMA transfer.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
* @param	SourcePtr contains a pointer to the source memory where the data
*		is to be transferred from.
* @param	SrcWordLength is the number of words (32 bit) to be transferred
*		for the source transfer.
* @param	DestPtr contains a pointer to the destination memory
*		where the data is to be transferred to.
* @param	DestWordLength is the number of words (32 bit) to be transferred
*		for the Destination transfer.
*
* @return	None.
*
* @note		It is the responsibility of the caller function to ensure that
*		correct values are passed to this function.
*
* 		The 2 LSBs of the SourcePtr (Source)/ DestPtr (Destination)
*		address when equal to 2’b01 indicates the last DMA command of
*		an overall transfer.
*
****************************************************************************/
void XDcfg_InitiateDma(XDcfg *InstancePtr, u32 SourcePtr, u32 DestPtr,
				u32 SrcWordLength, u32 DestWordLength)
{

	XDcfg_WriteReg(InstancePtr->Config.BaseAddr,
				XDCFG_DMA_SRC_ADDR_OFFSET,
				SourcePtr);

	XDcfg_WriteReg(InstancePtr->Config.BaseAddr,
				XDCFG_DMA_DEST_ADDR_OFFSET,
				DestPtr);

	XDcfg_WriteReg(InstancePtr->Config.BaseAddr,
				XDCFG_DMA_SRC_LEN_OFFSET,
				SrcWordLength);

	XDcfg_WriteReg(InstancePtr->Config.BaseAddr,
				XDCFG_DMA_DEST_LEN_OFFSET,
				DestWordLength);
}

/******************************************************************************/
/**
*
* This function Implements the DMA Read Command. This command is used to
* transfer the image data from FPGA to the external memory.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
* @param	SourcePtr contains a pointer to the source memory where the data
*		is to be transferred from.
* @param	SrcWordLength is the number of words (32 bit) to be transferred
*		for the source transfer.
* @param	DestPtr contains a pointer to the destination memory
*		where the data is to be transferred to.
* @param	DestWordLength is the number of words (32 bit) to be transferred
*		for the Destination transfer.
*
* @return	- XST_INVALID_PARAM if source address/length is invalid.
*		- XST_SUCCESS if DMA transfer initiated properly.
*
* @note		None.
*
****************************************************************************/
static u32 XDcfg_PcapReadback(XDcfg *InstancePtr, u32 SourcePtr,
				u32 SrcWordLength, u32 DestPtr,
				u32 DestWordLength)
{
	u32 IntrReg;

	/*
	 * Send READ Frame command to FPGA
	 */
	XDcfg_InitiateDma(InstancePtr, SourcePtr, XDCFG_DMA_INVALID_ADDRESS,
				SrcWordLength, 0);

	/*
	 * Store the enabled interrupts to enable before the actual read
	 * transfer is initiated and Disable all the interrupts temporarily.
	 */
	IntrReg = XDcfg_IntrGetEnabled(InstancePtr);
	XDcfg_IntrDisable(InstancePtr, XDCFG_IXR_ALL_MASK);

	/*
	 * Wait till you get the DMA done for the read command sent
	 */
	 while ((XDcfg_ReadReg(InstancePtr->Config.BaseAddr,
			XDCFG_INT_STS_OFFSET) &
			XDCFG_IXR_D_P_DONE_MASK) ==
			XDCFG_IXR_D_P_DONE_MASK);
	/*
	 * Enable the previously stored Interrupts .
	 */
	XDcfg_IntrEnable(InstancePtr, IntrReg);

	/*
	 * Initiate the DMA write command.
	 */
	XDcfg_InitiateDma(InstancePtr, XDCFG_DMA_INVALID_ADDRESS, (u32)DestPtr,
				0, DestWordLength);

	return XST_SUCCESS;
}


/****************************************************************************/
/**
*
* This function starts the DMA transfer. This function only starts the
* operation and returns before the operation may be completed.
* If the interrupt is enabled, an interrupt will be generated when the
* operation is completed, otherwise it is necessary to poll the Status register
* to determine when it is completed. It is the responsibility of the caller to
* determine when the operation is completed by handling the generated interrupt
* or polling the Status Register.
*
* @param	InstancePtr is a pointer to the XDcfg instance.
* @param	SourcePtr contains a pointer to the source memory where the data
*		is to be transferred from.
* @param	SrcWordLength is the number of words (32 bit) to be transferred
*		for the source transfer.
* @param	DestPtr contains a pointer to the destination memory
*		where the data is to be transferred to.
* @param	DestWordLength is the number of words (32 bit) to be transferred
*		for the Destination transfer.
* @param	TransferType contains the type of PCAP transfer being requested.
*		The definitions can be found in the xdevcfg.h file.
* @return
*		- XST_SUCCESS.if DMA transfer initiated successfully
*		- XST_DEVICE_BUSY if DMA is busy
*		- XST_INVALID_PARAM if invalid Source / Destination address
*			is sent or an invalid Source / Destination length is
*			sent
*
* @note		It is the responsibility of the caller to ensure that the cache
*		is flushed and invalidated both before the DMA operation is
*		started and after the DMA operation completes if the memory
*		pointed to is  cached. The caller must also ensure that the
*		pointers contain physical address rather than a virtual address
*		if address translation is being used.
*
* 		The 2 LSBs of the SourcePtr (Source)/ DestPtr (Destination)
*		address when equal to 2’b01 indicates the last DMA command of
*		an overall transfer.
*
*****************************************************************************/
u32 XDcfg_Transfer(XDcfg *InstancePtr,
			void *SourcePtr, u32 SrcWordLength,
			void *DestPtr, u32 DestWordLength,
			u32 TransferType)
{

	u32 CtrlReg;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);


	if (XDcfg_IsDmaBusy(InstancePtr) == XST_SUCCESS) {
		return XST_DEVICE_BUSY;
	}

	/*
	 * Check whether the fabric is in initialized state
	 */
	if ((XDcfg_ReadReg(InstancePtr->Config.BaseAddr, XDCFG_STATUS_OFFSET)
			& XDCFG_STATUS_PCFG_INIT_MASK) == 0) {
		/*
		 * We don't need to check PCFG_INIT to be high for
		 * non-encrypted loopback transfers.
		 */
		if (TransferType != XDCFG_CONCURRENT_NONSEC_READ_WRITE) {
			return XST_FAILURE;
		}
	}

	if ((TransferType == XDCFG_SECURE_PCAP_WRITE) ||
		(TransferType == XDCFG_NON_SECURE_PCAP_WRITE)) {

		/* Check for valid source pointer and length */
		if ((!SourcePtr) || (SrcWordLength == 0)) {
			return XST_INVALID_PARAM;
		}

		/* Clear internal PCAP loopback */
		CtrlReg = XDcfg_ReadReg(InstancePtr->Config.BaseAddr,
					XDCFG_MCTRL_OFFSET);
		XDcfg_WriteReg(InstancePtr->Config.BaseAddr,
				XDCFG_MCTRL_OFFSET, (CtrlReg &
				~(XDCFG_MCTRL_PCAP_LPBK_MASK)));

		if (TransferType == XDCFG_NON_SECURE_PCAP_WRITE) {
			/*
			 * Clear QUARTER_PCAP_RATE_EN bit
			 * so that the PCAP data is transmitted every clock
			 */
			CtrlReg = XDcfg_ReadReg(InstancePtr->Config.BaseAddr,
						XDCFG_CTRL_OFFSET);

			XDcfg_WriteReg(InstancePtr->Config.BaseAddr,
					XDCFG_CTRL_OFFSET, (CtrlReg &
					  ~XDCFG_CTRL_PCAP_RATE_EN_MASK));

		}
		if (TransferType == XDCFG_SECURE_PCAP_WRITE) {
			/*
			 * AES engine handles only 8 bit data every clock cycle.
			 * Hence, Encrypted PCAP data which is 32 bit data can
			 * only be sent in every 4 clock cycles. Set the control
			 * register QUARTER_PCAP_RATE_EN bit to achieve this
			 * operation.
			 */
			XDcfg_SetControlRegister(InstancePtr,
						XDCFG_CTRL_PCAP_RATE_EN_MASK);
		}

		XDcfg_InitiateDma(InstancePtr, (u32)SourcePtr,
				(u32)DestPtr, SrcWordLength, DestWordLength);

	}

	if (TransferType == XDCFG_PCAP_READBACK) {

		if ((!DestPtr) || (DestWordLength == 0)) {

			return XST_INVALID_PARAM;
		}

		/* Clear internal PCAP loopback */
		CtrlReg = XDcfg_ReadReg(InstancePtr->Config.BaseAddr,
					XDCFG_MCTRL_OFFSET);
		XDcfg_WriteReg(InstancePtr->Config.BaseAddr,
				XDCFG_MCTRL_OFFSET, (CtrlReg &
				~(XDCFG_MCTRL_PCAP_LPBK_MASK)));

		/*
		 * For PCAP readback of FPGA configuration register or memory,
		 * the read command is first sent (written) to the FPGA fabric
		 * which responds by returning the required read data. Read data
		 * from the FPGA is captured if pcap_radata_v is active.A DMA
		 * read transfer is required to obtain the readback command,
		 * which is then sent to the FPGA, followed by a DMA write
		 * transfer to support this mode of operation.
		 */
		return XDcfg_PcapReadback(InstancePtr,
					 (u32)SourcePtr, SrcWordLength,
					 (u32)DestPtr, 	 DestWordLength);
	}


	if ((TransferType == XDCFG_CONCURRENT_SECURE_READ_WRITE) ||
		(TransferType == XDCFG_CONCURRENT_NONSEC_READ_WRITE)) {

		if ((!SourcePtr) || (SrcWordLength == 0) ||
			(!DestPtr) || (DestWordLength == 0)) {
			return XST_INVALID_PARAM;
		}

		if (TransferType == XDCFG_CONCURRENT_NONSEC_READ_WRITE) {
			/* Enable internal PCAP loopback */
			CtrlReg = XDcfg_ReadReg(InstancePtr->Config.BaseAddr,
					XDCFG_MCTRL_OFFSET);
			XDcfg_WriteReg(InstancePtr->Config.BaseAddr,
					XDCFG_MCTRL_OFFSET, (CtrlReg |
					XDCFG_MCTRL_PCAP_LPBK_MASK));

			/*
			 * Clear QUARTER_PCAP_RATE_EN bit
			 * so that the PCAP data is transmitted every clock
			 */
			CtrlReg = XDcfg_ReadReg(InstancePtr->Config.BaseAddr,
						XDCFG_CTRL_OFFSET);

			XDcfg_WriteReg(InstancePtr->Config.BaseAddr,
					XDCFG_CTRL_OFFSET, (CtrlReg &
					  ~XDCFG_CTRL_PCAP_RATE_EN_MASK));

		}
		if (TransferType == XDCFG_CONCURRENT_SECURE_READ_WRITE) {
			/* Clear internal PCAP loopback */
			CtrlReg = XDcfg_ReadReg(InstancePtr->Config.BaseAddr,
						XDCFG_MCTRL_OFFSET);
			XDcfg_WriteReg(InstancePtr->Config.BaseAddr,
					XDCFG_MCTRL_OFFSET, (CtrlReg &
					~(XDCFG_MCTRL_PCAP_LPBK_MASK)));

			/*
			 * Set the QUARTER_PCAP_RATE_EN bit
			 * so that the PCAP data is transmitted every 4 clock
			 * cycles, this is required for encrypted data.
			 */
			XDcfg_SetControlRegister(InstancePtr,
					XDCFG_CTRL_PCAP_RATE_EN_MASK);
		}

		XDcfg_InitiateDma(InstancePtr, (u32)SourcePtr,
				(u32)DestPtr, SrcWordLength, DestWordLength);
	}

	return XST_SUCCESS;
}
