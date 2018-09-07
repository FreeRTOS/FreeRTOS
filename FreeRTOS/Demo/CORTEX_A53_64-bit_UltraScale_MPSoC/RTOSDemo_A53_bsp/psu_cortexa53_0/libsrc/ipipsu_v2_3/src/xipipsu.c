/******************************************************************************
*
* Copyright (C) 2015 - 2016 Xilinx, Inc.  All rights reserved.
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
* @file xipipsu.c
* @addtogroup ipipsu_v2_3
* @{
*
* This file contains the implementation of the interface functions for XIpiPsu
* driver. Refer to the header file xipipsu.h for more detailed information.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver	Who	Date	Changes
* ----- ------ -------- ----------------------------------------------
* 1.00	mjr	03/15/15	First Release
* 2.0	mjr	01/22/16	Fixed response buffer address
*                               calculation. CR# 932582.
* 2.1	kvn	05/05/16	Modified code for MISRA-C:2012 Compliance
* 2.2	kvn	02/17/17	Add support for updating ConfigTable at run time
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/
#include "xipipsu.h"
#include "xipipsu_hw.h"

/************************** Variable Definitions *****************************/
extern XIpiPsu_Config XIpiPsu_ConfigTable[XPAR_XIPIPSU_NUM_INSTANCES];

/****************************************************************************/
/**
 * Initialize the Instance pointer based on a given Config Pointer
 *
 * @param	InstancePtr is a pointer to the instance to be worked on
 * @param	CfgPtr is the device configuration structure containing required
 *		  	hardware build data
 * @param	EffectiveAddress is the base address of the device. If address
 *        	translation is not utilized, this parameter can be passed in using
 *        	CfgPtr->Config.BaseAddress to specify the physical base address.
 * @return	XST_SUCCESS if initialization was successful
 * 			XST_FAILURE in case of failure
 *
 */

XStatus XIpiPsu_CfgInitialize(XIpiPsu *InstancePtr, XIpiPsu_Config * CfgPtr,
		UINTPTR EffectiveAddress)
{
	u32 Index;
	/* Verify arguments */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(CfgPtr != NULL);
	/* Set device base address and ID */
	InstancePtr->Config.DeviceId = CfgPtr->DeviceId;
	InstancePtr->Config.BaseAddress = EffectiveAddress;
	InstancePtr->Config.BitMask = CfgPtr->BitMask;
	InstancePtr->Config.IntId = CfgPtr->IntId;

	InstancePtr->Config.TargetCount = CfgPtr->TargetCount;

	for (Index = 0U; Index < CfgPtr->TargetCount; Index++) {
		InstancePtr->Config.TargetList[Index].Mask =
				CfgPtr->TargetList[Index].Mask;
		InstancePtr->Config.TargetList[Index].BufferIndex =
				CfgPtr->TargetList[Index].BufferIndex;
	}

	/* Mark the component as Ready */
	InstancePtr->IsReady = XIL_COMPONENT_IS_READY;
	return (XST_SUCCESS);
}

/**
 * @brief	Reset the given IPI register set.
 *        	This function can be called to disable the IPIs from all
 *        	the sources and clear any pending IPIs in status register
 *
 * @param 	InstancePtr is the pointer to current IPI instance
 *
 */

void XIpiPsu_Reset(XIpiPsu *InstancePtr)
{

	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/**************Disable***************/

	XIpiPsu_WriteReg(InstancePtr->Config.BaseAddress, XIPIPSU_IDR_OFFSET,
			XIPIPSU_ALL_MASK);

	/**************Clear***************/
	XIpiPsu_WriteReg(InstancePtr->Config.BaseAddress, XIPIPSU_ISR_OFFSET,
			XIPIPSU_ALL_MASK);

}

/**
 * @brief	Trigger an IPI to a Destination CPU
 *
 * @param	InstancePtr is the pointer to current IPI instance
 * @param	DestCpuMask is the Mask of the CPU to which IPI is to be triggered
 *
 *
 * @return	XST_SUCCESS if successful
 * 			XST_FAILURE if an error occurred
 */

XStatus XIpiPsu_TriggerIpi(XIpiPsu *InstancePtr, u32 DestCpuMask)
{

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	/* Trigger an IPI to the Target */
	XIpiPsu_WriteReg(InstancePtr->Config.BaseAddress, XIPIPSU_TRIG_OFFSET,
			DestCpuMask);
	return XST_SUCCESS;

}

/**
 * @brief Poll for an acknowledgement using Observation Register
 *
 * @param	InstancePtr is the pointer to current IPI instance
 * @param	DestCpuMask is the Mask of the destination CPU from which ACK is expected
 * @param	TimeOutCount is the Count after which the routines returns failure
 *
 * @return	XST_SUCCESS if successful
 * 			XST_FAILURE if a timeout occurred
 */

XStatus XIpiPsu_PollForAck(XIpiPsu *InstancePtr, u32 DestCpuMask,
		u32 TimeOutCount)
{
	u32 Flag, PollCount;
	XStatus Status;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);

	PollCount = 0U;
	/* Poll the OBS register until the corresponding DestCpu bit is cleared */
	do {
		Flag = (XIpiPsu_ReadReg(InstancePtr->Config.BaseAddress,
				XIPIPSU_OBS_OFFSET)) & (DestCpuMask);
		PollCount++;
		/* Check if the IPI was Acknowledged by the Target or we Timed Out*/
	} while ((0x00000000U != Flag) && (PollCount < TimeOutCount));

	if (PollCount >= TimeOutCount) {
		Status = XST_FAILURE;
	} else {
		Status = XST_SUCCESS;
	}

	return Status;
}

/**
 * @brief	Get the Buffer Index for a CPU specified by Mask
 *
 * @param	InstancePtr is the pointer to current IPI instance
 * @param	CpuMask is the Mask of the CPU form which Index is required
 *
 * @return	Buffer Index value if CPU Mask is valid
 * 			XIPIPSU_MAX_BUFF_INDEX+1 if not valid
 *
 * @note	Static function used only by XIpiPsu_GetBufferAddress
 *
 */
static u32 XIpiPsu_GetBufferIndex(XIpiPsu *InstancePtr, u32 CpuMask)
{
	u32 BufferIndex;
	u32 Index;
	/* Init Index with an invalid value */
	BufferIndex = XIPIPSU_MAX_BUFF_INDEX + 1U;

	/*Search for CPU in the List */
	for (Index = 0U; Index < InstancePtr->Config.TargetCount; Index++) {
		/*If we find the CPU , then set the Index and break the loop*/
		if (InstancePtr->Config.TargetList[Index].Mask == CpuMask) {
			BufferIndex = InstancePtr->Config.TargetList[Index].BufferIndex;
			break;
		}
	}

	/* Return the Index */
	return BufferIndex;
}

/**
 * @brief	Get the Buffer Address for a given pair of CPUs
 *
 * @param	InstancePtr is the pointer to current IPI instance
 * @param	SrcCpuMask is the Mask for Source CPU
 * @param	DestCpuMask is the Mask for Destination CPU
 * @param	BufferType is either XIPIPSU_BUF_TYPE_MSG or XIPIPSU_BUF_TYPE_RESP
 *
 * @return	Valid Buffer Address if no error
 * 			NULL if an error occurred in calculating Address
 *
 */

static u32* XIpiPsu_GetBufferAddress(XIpiPsu *InstancePtr, u32 SrcCpuMask,
		u32 DestCpuMask, u32 BufferType)
{
#ifdef __aarch64__
	u64 BufferAddr;
#else
	u32 BufferAddr;
#endif

	u32 SrcIndex;
	u32 DestIndex;
	/* Get the buffer indices */
	SrcIndex = XIpiPsu_GetBufferIndex(InstancePtr, SrcCpuMask);
	DestIndex = XIpiPsu_GetBufferIndex(InstancePtr, DestCpuMask);

	/* If we got an invalid buffer index, then return NULL pointer, else valid address */
	if ((SrcIndex > XIPIPSU_MAX_BUFF_INDEX)
			|| (DestIndex > XIPIPSU_MAX_BUFF_INDEX)) {
		BufferAddr = 0U;
	} else {

		if (XIPIPSU_BUF_TYPE_MSG == BufferType) {
			BufferAddr = XIPIPSU_MSG_RAM_BASE
					+ (SrcIndex * XIPIPSU_BUFFER_OFFSET_GROUP)
					+ (DestIndex * XIPIPSU_BUFFER_OFFSET_TARGET);
		} else if (XIPIPSU_BUF_TYPE_RESP == BufferType) {
			BufferAddr = XIPIPSU_MSG_RAM_BASE
					+ (DestIndex * XIPIPSU_BUFFER_OFFSET_GROUP)
					+ (SrcIndex * XIPIPSU_BUFFER_OFFSET_TARGET)
					+ (XIPIPSU_BUFFER_OFFSET_RESPONSE);
		} else {
			BufferAddr = 0U;
		}

	}

	return (u32 *) BufferAddr;
}

/**
 * @brief	Read an Incoming Message from a Source
 *
 * @param 	InstancePtr is the pointer to current IPI instance
 * @param 	SrcCpuMask is the Device Mask for the CPU which has sent the message
 * @param 	MsgPtr is the pointer to Buffer to which the read message needs to be stored
 * @param 	MsgLength is the length of the buffer/message
 * @param 	BufferType is the type of buffer (XIPIPSU_BUF_TYPE_MSG or XIPIPSU_BUF_TYPE_RESP)
 *
 * @return	XST_SUCCESS if successful
 * 			XST_FAILURE if an error occurred
 */

XStatus XIpiPsu_ReadMessage(XIpiPsu *InstancePtr, u32 SrcCpuMask, u32 *MsgPtr,
		u32 MsgLength, u8 BufferType)
{
	u32 *BufferPtr;
	u32 Index;
	XStatus Status;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(MsgPtr != NULL);
	Xil_AssertNonvoid(MsgLength <= XIPIPSU_MAX_MSG_LEN);

	BufferPtr = XIpiPsu_GetBufferAddress(InstancePtr, SrcCpuMask,
			InstancePtr->Config.BitMask, BufferType);
	if (BufferPtr != NULL) {
		/* Copy the IPI Buffer contents into Users's Buffer*/
		for (Index = 0U; Index < MsgLength; Index++) {
			MsgPtr[Index] = BufferPtr[Index];
		}
		Status = XST_SUCCESS;
	} else {
		Status = XST_FAILURE;
	}

	return Status;
}


/**
 * @brief	Send a Message to Destination
 *
 * @param	InstancePtr is the pointer to current IPI instance
 * @param	DestCpuMask is the Device Mask for the destination CPU
 * @param	MsgPtr is the pointer to Buffer which contains the message to be sent
 * @param	MsgLength is the length of the buffer/message
 * @param	BufferType is the type of buffer (XIPIPSU_BUF_TYPE_MSG or XIPIPSU_BUF_TYPE_RESP)
 *
 * @return	XST_SUCCESS if successful
 * 			XST_FAILURE if an error occurred
 */

XStatus XIpiPsu_WriteMessage(XIpiPsu *InstancePtr, u32 DestCpuMask, u32 *MsgPtr,
		u32 MsgLength, u8 BufferType)
{
	u32 *BufferPtr;
	u32 Index;
	XStatus Status;

	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady == XIL_COMPONENT_IS_READY);
	Xil_AssertNonvoid(MsgPtr != NULL);
	Xil_AssertNonvoid(MsgLength <= XIPIPSU_MAX_MSG_LEN);

	BufferPtr = XIpiPsu_GetBufferAddress(InstancePtr,
			InstancePtr->Config.BitMask, DestCpuMask, BufferType);
	if (BufferPtr != NULL) {
		/* Copy the Message to IPI Buffer */
		for (Index = 0U; Index < MsgLength; Index++) {
			BufferPtr[Index] = MsgPtr[Index];
		}
		Status = XST_SUCCESS;
	} else {
		Status = XST_FAILURE;
	}

	return Status;
}

/*****************************************************************************/
/**
*
* Set up the device configuration based on the unique device ID. A table
* contains the configuration info for each device in the system.
*
* @param	DeviceId contains the ID of the device to set up the
*			configuration for.
*
* @return	A pointer to the device configuration for the specified
*			device ID. See xipipsu.h for the definition of
*			XIpiPsu_Config.
*
* @note		This is for safety use case where in this function has to
* 			be called before CfgInitialize. So that driver will be
* 			initialized with the provided configuration. For non-safe
* 			use cases, this is not needed.
*
******************************************************************************/
void XIpiPsu_SetConfigTable(u32 DeviceId, XIpiPsu_Config *ConfigTblPtr)
{
	u32 Index;

	Xil_AssertVoid(ConfigTblPtr != NULL);

	for (Index = 0U; Index < XPAR_XIPIPSU_NUM_INSTANCES; Index++) {
		if (XIpiPsu_ConfigTable[Index].DeviceId == DeviceId) {
			XIpiPsu_ConfigTable[Index].BaseAddress = ConfigTblPtr->BaseAddress;
			XIpiPsu_ConfigTable[Index].BitMask = ConfigTblPtr->BitMask;
			XIpiPsu_ConfigTable[Index].BufferIndex = ConfigTblPtr->BufferIndex;
			XIpiPsu_ConfigTable[Index].IntId = ConfigTblPtr->IntId;
		}
	}
}
/** @} */
