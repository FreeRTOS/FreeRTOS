/******************************************************************************
*
* Copyright (C) 2014 Xilinx, Inc.  All rights reserved.
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
* @file xzdma.c
* @addtogroup zdma_v1_0
* @{
*
* This file contains the implementation of the interface functions for ZDMA
* driver. Refer to the header file xzdma.h for more detailed information.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who     Date     Changes
* ----- ------  -------- ------------------------------------------------------
* 1.0   vns     2/27/15  First release
*       vns    16/10/15  Corrected Destination descriptor addresss calculation
*                        in XZDma_CreateBDList API
* 1.1   vns    05/11/15  Modified XZDma_SetMode to return XST_FAILURE on
*                        selecting DMA mode other than normal mode in
*                        scatter gather mode data transfer and corrected
*                        XZDma_SetChDataConfig API to set over fetch and
*                        src issue parameters correctly.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xzdma.h"

/************************** Function Prototypes ******************************/

static void StubCallBack(void *CallBackRef, u32 Mask);
static void StubDoneCallBack(void *CallBackRef);
static void XZDma_SimpleMode(XZDma *InstancePtr, XZDma_Transfer *Data);
static void XZDma_ScatterGather(XZDma *InstancePtr, XZDma_Transfer *Data,
								u32 Num);
static void XZDma_LinearMode(XZDma *InstancePtr, XZDma_Transfer *Data,
	XZDma_LiDscr *SrcDscrPtr,XZDma_LiDscr *DstDscrPtr, u8 IsLast);
static void XZDma_ConfigLinear(XZDma_LiDscr *DscrPtr, u64 Addr, u32 Size,
								u32 CtrlValue);
static void XZDma_LinkedListMode(XZDma *InstancePtr, XZDma_Transfer *Data,
	XZDma_LlDscr *SrcDscrPtr,XZDma_LlDscr *DstDscrPtr, u8 IsLast);
static void XZDma_ConfigLinkedList(XZDma_LlDscr *DscrPtr, u64 Addr, u32 Size,
					u32 CtrlValue, u64 NextDscrAddr);
static void XZDma_Enable(XZDma *InstancePtr);
static void XZDma_GetConfigurations(XZDma *InstancePtr);

/************************** Function Definitions *****************************/

/*****************************************************************************/
/**
*
* This function initializes an ZDMA core. This function must be called
* prior to using an ZDMA core. Initialization of an ZDMA includes setting
* up the instance data and ensuring the hardware is in a quiescent state and
* resets all the hardware configurations.
*
* @param	InstancePtr is a pointer to the XZDma instance.
* @param	CfgPtr is a reference to a structure containing information
*		about a specific XZDma instance.
* @param	EffectiveAddr is the device base address in the virtual memory
*		address space. The caller is responsible for keeping the
*		address mapping from EffectiveAddr to the device physical
*		base address unchanged once this function is invoked.
*		Unexpected errors may occur if the address mapping changes
*		after this function is called. If address translation is not
*		used, pass in the physical address instead.
*
* @return
*		- XST_SUCCESS if initialization was successful.
*
* @note		None.
*
******************************************************************************/
s32 XZDma_CfgInitialize(XZDma *InstancePtr, XZDma_Config *CfgPtr,
			u32 EffectiveAddr)
{

	/* Verify arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(CfgPtr != NULL);
	Xil_AssertNonvoid(EffectiveAddr != ((u32)0x00));

	InstancePtr->Config.BaseAddress = CfgPtr->BaseAddress;
	InstancePtr->Config.DeviceId = CfgPtr->DeviceId;
	InstancePtr->Config.DmaType = CfgPtr->DmaType;

	InstancePtr->Config.BaseAddress = EffectiveAddr;

	InstancePtr->IsReady = (u32)(XIL_COMPONENT_IS_READY);

	InstancePtr->IsSgDma = FALSE;
	InstancePtr->Mode = XZDMA_NORMAL_MODE;
	InstancePtr->IntrMask = 0x00U;
	InstancePtr->ChannelState = XZDMA_IDLE;

	/*
	 * Set all handlers to stub values, let user configure this
	 * data later
	 */
	InstancePtr->DoneHandler =
				(XZDma_DoneHandler)((void *)StubDoneCallBack);
	InstancePtr->ErrorHandler =
				(XZDma_ErrorHandler)((void *)StubCallBack);

	XZDma_Reset(InstancePtr);
	XZDma_GetConfigurations(InstancePtr);

	return (XST_SUCCESS);

}

/*****************************************************************************/
/**
*
* This function sets the pointer type and mode in which ZDMA needs to transfer
* the data.
*
* @param	InstancePtr is a pointer to the XZDma instance.
* @param	IsSgDma is a variable which specifies whether transfer has to
*		to be done in scatter gather mode or simple mode.
*		- TRUE  - Scatter gather pointer type
*		- FALSE - Simple pointer type
* @param	Mode is the type of the mode in which data has to be initiated
*		- XZDMA_NORMAL_MODE   - Normal data transfer from source to
*					destination (Valid for both Scatter
*					gather and simple types)
*		- XZDMA_WRONLY_MODE  - Write only mode (Valid only for Simple)
*		- XZDMA_RDONLY_MODE  - Read only mode (Valid only for Simple)
*
* @return
*		- XST_SUCCESS - If mode has been set successfully.
*		- XST_FAILURE - If mode has not been set.
*
* @note		Mode cannot be changed while ZDMA is not in IDLE state.
*
******************************************************************************/
s32 XZDma_SetMode(XZDma *InstancePtr, u8 IsSgDma, XZDma_Mode Mode)
{
	u32 Data;
	s32 Status;

	/* Verify arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid((IsSgDma == TRUE) || (IsSgDma == FALSE));
	Xil_AssertNonvoid(Mode <= XZDMA_RDONLY_MODE);

	if (InstancePtr->ChannelState != XZDMA_IDLE) {
		Status = XST_FAILURE;
		goto End;
	}
	else {
		Data = XZDma_ReadReg(InstancePtr->Config.BaseAddress,
						XZDMA_CH_CTRL0_OFFSET);
		/* Simple mode */
		if (IsSgDma != TRUE) {
			Data = (Data & (~XZDMA_CTRL0_POINT_TYPE_MASK));
			if (Mode == XZDMA_NORMAL_MODE) {
				Data &= (~XZDMA_CTRL0_MODE_MASK);
			}
			else if (Mode == XZDMA_WRONLY_MODE) {
				Data |= XZDMA_CTRL0_WRONLY_MASK;
			}
			else {
				Data |= XZDMA_CTRL0_RDONLY_MASK;
			}
			XZDma_WriteReg(InstancePtr->Config.BaseAddress,
						XZDMA_CH_CTRL0_OFFSET, Data);
			InstancePtr->IsSgDma = FALSE;
			InstancePtr->Mode = Mode;
		}

		else {
			if (Mode != XZDMA_NORMAL_MODE) {
				Status = XST_FAILURE;
				goto End;
			}
			else {
				Data |= (XZDMA_CTRL0_POINT_TYPE_MASK);
				Data &= ~(XZDMA_CTRL0_MODE_MASK);
				XZDma_WriteReg(InstancePtr->Config.BaseAddress,
						XZDMA_CH_CTRL0_OFFSET, Data);

				InstancePtr->IsSgDma = TRUE;
				InstancePtr->Mode = Mode;
			}
		}
		Status = XST_SUCCESS;
	}

End:
	return Status;

}

/*****************************************************************************/
/**
*
* This function sets the descriptor type and descriptor pointer's start address
* of both source and destination based on the memory allocated by user and also
* calculates no of descriptors(BDs) can be created in the allocated memory.
*
* @param	InstancePtr is a pointer to the XZDma instance.
* @param	TypeOfDscr is a variable which specifies descriptor type
*		whether Linear or linked list type of descriptor.
*		- XZDMA_LINEAR    - Linear type of descriptor.
*		- XZDMA_LINKEDLIST- Linked list type of descriptor.
* @param	Dscr_MemPtr is a pointer to the allocated memory for creating
*		descriptors. It Should be aligned to 64 bytes.
*
* @param	NoOfBytes specifies the number of bytes allocated for
*		descriptors
*
* @return	The Count of the descriptors can be created.
*
* @note		User should allocate the memory for descriptors which should
*		be capable of how many transfers he wish to do in one start.
*		For Linear mode each descriptor needs 128 bit memory so for
*		one data transfer it requires 2*128 = 256 bits i.e. 32 bytes
*		Similarly for Linked list mode for each descriptor it needs
*		256 bit, so for one data transfer it require 2*256 = 512 bits
*		i.e. 64 bytes.
*
******************************************************************************/
u32 XZDma_CreateBDList(XZDma *InstancePtr, XZDma_DscrType TypeOfDscr,
					UINTPTR Dscr_MemPtr, u32 NoOfBytes)
{
	u32 Size;

	/* Verify arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid((TypeOfDscr == XZDMA_LINEAR) ||
					(TypeOfDscr == XZDMA_LINKEDLIST));
	Xil_AssertNonvoid(Dscr_MemPtr != 0x00);
	Xil_AssertNonvoid(NoOfBytes != 0x00U);

	InstancePtr->Descriptor.DscrType = TypeOfDscr;

	if (TypeOfDscr == XZDMA_LINEAR) {
		Size = sizeof(XZDma_LiDscr);
	}
	else {
		Size = sizeof(XZDma_LlDscr);
	}
	InstancePtr->Descriptor.DscrCount =
						(NoOfBytes >> 1) / Size;
	InstancePtr->Descriptor.SrcDscrPtr = (void *)Dscr_MemPtr;
	InstancePtr->Descriptor.DstDscrPtr =
			(void *)Dscr_MemPtr + (Size * InstancePtr->Descriptor.DscrCount);

	Xil_DCacheInvalidateRange((INTPTR)Dscr_MemPtr, NoOfBytes);

	return (InstancePtr->Descriptor.DscrCount);
}

/*****************************************************************************/
/**
*
* This function sets the data attributes and control configurations of a
* ZDMA core based on the inputs provided.
*
* @param	InstancePtr is a pointer to the XZDma instance.
* @param	Configure is a pointer to the XZDma_ChDataConfig structure
*		which has all the configuration fields.
*		The fields of the structure are:
*		- OverFetch - Allows over fetch or not
*			- 0 - Not allowed to over-fetch on SRC
*			- 1 - Allowed to over-fetch on SRC
*		- SrcIssue  - Outstanding transaction on SRC
*			- Range is 1 to 32
*		- SrcBurstType - Burst Type for SRC AXI transaction
*			- XZDMA_FIXED_BURST - Fixed burst
*			- XZDMA_INCR_BURST  - Incremental burst
*		- SrcBurstLen - AXI Length for Data Read.
*			- Range of values is (1,2,4,8,16).
*		- DstBurstType - Burst Type for SRC AXI transaction
*			- XZDMA_FIXED_BURST - Fixed burst
*			- XZDMA_INCR_BURST - Incremental burst
*		- DstBurstLen     - AXI Length for Data write.
*			- Range of values is (1,2,4,8,16).
*		- SrcCache - AXI cache bits for Data read
*		- SrcQos - Configurable QoS bits for AXI Data read
*		- DstCache - AXI cache bits for Data write
*		- DstQos - configurable QoS bits for AXI Data write
*
* @return
* 		- XST_FAILURE  If ZDMA Core is not in Idle state and
* 		- XST_SUCCESS If Configurations are made successfully
*
* @note
* 		- These configurations will last till we modify or Reset
*		  by XZDma_Reset(XZDma *InstancePtr).
* 		- Configurations should be modified only when ZDMA channel
* 		  is IDLE this can be confirmed by using
*		  XZDma_ChannelState(XZDma *InstancePtr) API.
*
******************************************************************************/
s32 XZDma_SetChDataConfig(XZDma *InstancePtr, XZDma_DataConfig *Configure)
{
	u32 Data;
	s32 Status;

	/* Verify arguments */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(Configure != NULL);

	if (InstancePtr->ChannelState != XZDMA_IDLE) {
		Status = XST_FAILURE;
	}
	else {
		InstancePtr->DataConfig.DstBurstType = Configure->DstBurstType;
		InstancePtr->DataConfig.DstBurstLen = Configure->DstBurstLen;
		InstancePtr->DataConfig.SrcBurstType = Configure->SrcBurstType;
		InstancePtr->DataConfig.SrcBurstLen = Configure->SrcBurstLen;
		InstancePtr->DataConfig.OverFetch = Configure->OverFetch;
		InstancePtr->DataConfig.SrcIssue = Configure->SrcIssue;
		InstancePtr->DataConfig.SrcCache = Configure->SrcCache;
		InstancePtr->DataConfig.SrcQos = Configure->SrcQos;
		InstancePtr->DataConfig.DstCache = Configure->DstCache;
		InstancePtr->DataConfig.DstQos = Configure->DstQos;

		/* Setting over fetch */
		Data = XZDma_ReadReg(InstancePtr->Config.BaseAddress,
				XZDMA_CH_CTRL0_OFFSET) & (~XZDMA_CTRL0_OVR_FETCH_MASK);

		Data |= (((u32)(Configure->OverFetch) <<
				XZDMA_CTRL0_OVR_FETCH_SHIFT) &
					XZDMA_CTRL0_OVR_FETCH_MASK);

		XZDma_WriteReg(InstancePtr->Config.BaseAddress,
					XZDMA_CH_CTRL0_OFFSET, Data);

		/* Setting source issue */
		Data = XZDma_ReadReg(InstancePtr->Config.BaseAddress,
						XZDMA_CH_CTRL1_OFFSET) & (~XZDMA_CTRL1_SRC_ISSUE_MASK);
		Data |= (u32)(Configure->SrcIssue & XZDMA_CTRL1_SRC_ISSUE_MASK);

		XZDma_WriteReg(InstancePtr->Config.BaseAddress,
						XZDMA_CH_CTRL1_OFFSET, Data);

		/* Setting Burst length and burst type */
		Data = XZDma_ReadReg(InstancePtr->Config.BaseAddress,
						XZDMA_CH_DATA_ATTR_OFFSET);
		Data = (Data & (~(XZDMA_DATA_ATTR_ARBURST_MASK |
				 XZDMA_DATA_ATTR_ARLEN_MASK |
				 XZDMA_DATA_ATTR_AWBURST_MASK |
				 XZDMA_DATA_ATTR_AWLEN_MASK |
				 XZDMA_DATA_ATTR_ARCACHE_MASK |
				 XZDMA_DATA_ATTR_AWCACHE_MASK |
				 XZDMA_DATA_ATTR_AWQOS_MASK |
				 XZDMA_DATA_ATTR_ARQOS_MASK)));

		Data |= ((((u32)(Configure->SrcBurstType) <<
				XZDMA_DATA_ATTR_ARBURST_SHIFT) &
				XZDMA_DATA_ATTR_ARBURST_MASK) |
				(((u32)(Configure->SrcCache) <<
				XZDMA_DATA_ATTR_ARCACHE_SHIFT) &
				XZDMA_DATA_ATTR_ARCACHE_MASK) |
				(((u32)(Configure->SrcQos) <<
				XZDMA_DATA_ATTR_ARQOS_SHIFT) &
				XZDMA_DATA_ATTR_ARQOS_MASK) |
			(((u32)(Configure->SrcBurstLen) <<
				XZDMA_DATA_ATTR_ARLEN_SHIFT) &
				XZDMA_DATA_ATTR_ARLEN_MASK) |
			(((u32)(Configure->DstBurstType) <<
				XZDMA_DATA_ATTR_AWBURST_SHIFT) &
				XZDMA_DATA_ATTR_AWBURST_MASK) |
			(((u32)(Configure->DstCache) <<
				XZDMA_DATA_ATTR_AWCACHE_SHIFT) &
				XZDMA_DATA_ATTR_AWCACHE_MASK) |
			(((u32)(Configure->DstQos) <<
				XZDMA_DATA_ATTR_AWQOS_SHIFT) &
				XZDMA_DATA_ATTR_AWQOS_MASK) |
			(((u32)(Configure->DstBurstLen)) &
				XZDMA_DATA_ATTR_AWLEN_MASK));

		XZDma_WriteReg(InstancePtr->Config.BaseAddress,
					XZDMA_CH_DATA_ATTR_OFFSET, Data);
		Status = XST_SUCCESS;
	}

	return Status;

}

/*****************************************************************************/
/**
*
* This function gets the data attributes and control configurations of a
* ZDMA core.
*
* @param	InstancePtr is a pointer to the XZDma instance.
* @param	Configure is a pointer to the XZDma_ChDataConfig structure
*		which has all the configuration fields.
*		The fields of the structure are:
*		- OverFetch - Allows over fetch or not
*			- 0 - Not allowed to over-fetch on SRC
*			- 1 - Allowed to over-fetch on SRC
*		- SrcIssue  - Outstanding transaction on SRC
*			- Range is 1 to 32
*		- SrcBurstType - Burst Type for SRC AXI transaction
*			- XZDMA_FIXED_BURST - Fixed burst
*			- XZDMA_INCR_BURST  - Incremental burst
*		- SrcBurstLen - AXI Length for Data Read.
*			- Can be max of 16 to be compatible with AXI3
*		- DstBurstType - Burst Type for SRC AXI transaction
*			- XZDMA_FIXED_BURST - Fixed burst
*			- XZDMA_INCR_BURST - Incremental burst
*		- DstBurstLen     - AXI Length for Data write.
*			- Can be max of 16 to be compatible with AXI3
*		- SrcCache - AXI cache bits for Data read
*		- SrcQos - Configurable QoS bits for AXI Data read
*		- DstCache - AXI cache bits for Data write
*		- DstQos - Configurable QoS bits for AXI Data write
*
* @return	None
*
* @note		None.
*
******************************************************************************/
void XZDma_GetChDataConfig(XZDma *InstancePtr, XZDma_DataConfig *Configure)
{

	/* Verify arguments */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Configure != NULL);

	Configure->SrcBurstType = InstancePtr->DataConfig.SrcBurstType;
	Configure->SrcCache = InstancePtr->DataConfig.SrcCache;
	Configure->SrcQos = InstancePtr->DataConfig.SrcQos;
	Configure->SrcBurstLen = InstancePtr->DataConfig.SrcBurstLen;

	Configure->DstBurstType = InstancePtr->DataConfig.DstBurstType;
	Configure->DstCache = InstancePtr->DataConfig.DstCache;
	Configure->DstQos = InstancePtr->DataConfig.DstQos;
	Configure->DstBurstLen = InstancePtr->DataConfig.DstBurstLen;

	Configure->OverFetch = InstancePtr->DataConfig.OverFetch;
	Configure->SrcIssue = InstancePtr->DataConfig.SrcIssue;

}

/*****************************************************************************/
/**
*
* This function sets the descriptor attributes based on the inputs provided
* in the structure.
*
* @param	InstancePtr is a pointer to the XZDma instance.
* @param	Configure is a pointer to the XZDma_ChDscrConfig structure
*		which has all the configuration fields.
*		The fields of the structure are:
*		- AxCoherent - AXI transactions generated for the descriptor.
*			- 0 - Non coherent
*			- 1 - Coherent
*		- AXCache    - AXI cache bit used for DSCR fetch
*				(both on SRC and DST Side)
*		- AXQos      - QoS bit used for DSCR fetch
*				(both on SRC and DST Side)
*
* @return
*		- XST_FAILURE  If ZDMA core is not in Idle state and
* 		- XST_SUCCESS If Configurations are made successfully
*
* @note		None.
*
******************************************************************************/
s32 XZDma_SetChDscrConfig(XZDma *InstancePtr, XZDma_DscrConfig *Configure)
{
	u32 Data;
	s32 Status;

	/* Verify arguments */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(Configure != NULL);

	if (InstancePtr->ChannelState != XZDMA_IDLE) {
		Status = XST_FAILURE;
	}

	else {
		InstancePtr->DscrConfig.AXCache = Configure->AXCache;
		InstancePtr->DscrConfig.AXQos = Configure->AXQos;
		InstancePtr->DscrConfig.AxCoherent = Configure->AxCoherent;

		Data = ((((u32)(Configure->AxCoherent) <<
				XZDMA_DSCR_ATTR_AXCOHRNT_SHIFT) &
				XZDMA_DSCR_ATTR_AXCOHRNT_MASK) |
			(((u32)(Configure->AXCache) <<
				XZDMA_DSCR_ATTR_AXCACHE_SHIFT) &
				XZDMA_DSCR_ATTR_AXCACHE_MASK) |
			(((u32)Configure->AXQos) &
				XZDMA_DSCR_ATTR_AXQOS_MASK));

		XZDma_WriteReg(InstancePtr->Config.BaseAddress,
				XZDMA_CH_DSCR_ATTR_OFFSET, Data);

		Status = XST_SUCCESS;
	}

	return Status;
}

/*****************************************************************************/
/**
*
* This function gets the descriptor attributes of the channel.
*
* @param	InstancePtr is a pointer to the XZDma instance.
* @param	Configure is a pointer to the XZDma_ChDscrConfig structure
*		which has all the configuration fields.
*		The fields of the structure are:
*		- AxCoherent - AXI transactions generated for the descriptor.
*			- 0 - Non coherent
*			- 1 - Coherent
*		- AXCache    - AXI cache bit used for DSCR fetch
*				(both on SRC and DST Side)
*		- AXQos      - QoS bit used for DSCR fetch
*				(both on SRC and DST Side)
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XZDma_GetChDscrConfig(XZDma *InstancePtr, XZDma_DscrConfig *Configure)
{

	/* Verify arguments */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Configure != NULL);

	Configure->AXCache = InstancePtr->DscrConfig.AXCache;
	Configure->AXQos = InstancePtr->DscrConfig.AXQos;
	Configure->AxCoherent = InstancePtr->DscrConfig.AxCoherent;

}

/*****************************************************************************/
/**
*
* This function preloads the buffers which will be used in write only mode.
* In write only mode the data in the provided buffer will be written in
* destination address for specified size.
*
* @param	InstancePtr is a pointer to the XZDma instance.
* @param	Buffer is a pointer to an array of 64/128 bit data.
*		i.e. pointer to 32 bit array of size 2/4
*		 - Array of Size 2 for ADMA
*		 - Array of Size 4 for GDMA
*
* @return	None.
*
* @note		Valid only in simple mode.
* 		Prior to call this function ZDMA instance should be set in
* 		Write only mode by using
*		XZDma_SetMode(XZDma *InstancePtr, u8 IsSgDma,
*							XZDma_Mode Mode)
*		To initiate data transfer after this API need to call
*		XZDma_Start(XZDma *InstancePtr, XZDma_Transfer *Data, u32 Num)
*		In which only destination fields has to be filled.
*
******************************************************************************/
void XZDma_WOData(XZDma *InstancePtr, u32 *Buffer)
{
	u32 *LocBuf = Buffer;

	/* Verify arguments */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Buffer != NULL);

	if (InstancePtr->Config.DmaType == (u8)0) {
		XZDma_WriteReg(InstancePtr->Config.BaseAddress,
				XZDMA_CH_WR_ONLY_WORD0_OFFSET, *LocBuf);
		LocBuf++;
		XZDma_WriteReg(InstancePtr->Config.BaseAddress,
				XZDMA_CH_WR_ONLY_WORD1_OFFSET, *LocBuf);
		LocBuf++;
		XZDma_WriteReg(InstancePtr->Config.BaseAddress,
				XZDMA_CH_WR_ONLY_WORD2_OFFSET, *LocBuf);
		LocBuf++;
		XZDma_WriteReg(InstancePtr->Config.BaseAddress,
				XZDMA_CH_WR_ONLY_WORD3_OFFSET, *LocBuf);
	}

	else {
		XZDma_WriteReg(InstancePtr->Config.BaseAddress,
				XZDMA_CH_WR_ONLY_WORD0_OFFSET, *LocBuf);
		LocBuf++;
		XZDma_WriteReg(InstancePtr->Config.BaseAddress,
				XZDMA_CH_WR_ONLY_WORD1_OFFSET, *LocBuf);
	}

}

/*****************************************************************************/
/**
*
* This function resume the paused state of ZDMA core and starts the transfer
* from where it has paused.
*
* @param	InstancePtr is a pointer to the XZDma instance.
*
* @return	None.
*
* @note		Valid only for scatter gather mode.
*
******************************************************************************/
void XZDma_Resume(XZDma *InstancePtr)
{
	u32 Value;

	/* Verify arguments */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsSgDma == TRUE);
	Xil_AssertVoid(InstancePtr->ChannelState == XZDMA_PAUSE);

	Value = XZDma_ReadReg(InstancePtr->Config.BaseAddress,
		XZDMA_CH_CTRL0_OFFSET) & (~XZDMA_CTRL0_CONT_ADDR_MASK);
	Value |= XZDMA_CTRL0_CONT_MASK;
	InstancePtr->ChannelState = XZDMA_BUSY;
	XZDma_WriteReg(InstancePtr->Config.BaseAddress,
				XZDMA_CH_CTRL0_OFFSET, Value);
}

/*****************************************************************************/
/**
*
* This function resets the ZDMA core.
*
* @param	InstancePtr is a pointer to the XZDma instance.
*
* @return	None.
*
* @note		This function resets all the configurations made previously.
*		Disables all the interrupts and clears interrupt status.
*
*****************************************************************************/
void XZDma_Reset(XZDma *InstancePtr)
{

	/* Verify arguments */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->ChannelState == XZDMA_IDLE);

	/* Disable's the channel */
	XZDma_DisableCh(InstancePtr);

	/* Disables all interrupts */
	XZDma_DisableIntr(InstancePtr, XZDMA_IXR_ALL_INTR_MASK);
	XZDma_IntrClear(InstancePtr, XZDMA_IXR_ALL_INTR_MASK);
	InstancePtr->IntrMask = 0x00U;

	/* All configurations are being reset */
	XZDma_WriteReg(InstancePtr->Config.BaseAddress, XZDMA_CH_CTRL0_OFFSET,
					XZDMA_CTRL0_RESET_VALUE);
	XZDma_WriteReg(InstancePtr->Config.BaseAddress, XZDMA_CH_CTRL1_OFFSET,
					XZDMA_CTRL1_RESET_VALUE);
	XZDma_WriteReg(InstancePtr->Config.BaseAddress,
		XZDMA_CH_DATA_ATTR_OFFSET, XZDMA_DATA_ATTR_RESET_VALUE);
	XZDma_WriteReg(InstancePtr->Config.BaseAddress,
		XZDMA_CH_DSCR_ATTR_OFFSET, XZDMA_DSCR_ATTR_RESET_VALUE);

	/* Clears total byte */
	XZDma_TotalByteClear(InstancePtr);

	/* Clears interrupt count of both source and destination channels */
	(void)XZDma_GetSrcIntrCnt(InstancePtr);
	(void)XZDma_GetDstIntrCnt(InstancePtr);

	InstancePtr->ChannelState = XZDMA_IDLE;

}

/*****************************************************************************/
/**
*
* This function returns the state of ZDMA core.
*
* @param	InstancePtr is a pointer to the XZDma instance.
*
* @return	This function returns state of ZDMA core
*		- XZDMA_IDLE - If ZDMA core is in idle state.
*		- XZDMA_PAUSE - If ZDMA is in paused state.
*		- XZDMA_BUSY - If ZDMA is in busy state.
* @note		None.
*		C-style signature:
*		XZDmaState XZDma_ChannelState(XZDma *InstancePtr)
*
******************************************************************************/
XZDmaState XZDma_ChannelState(XZDma *InstancePtr)
{
	XZDmaState Status;
	u32 Value;

	/* Verify arguments */
	Xil_AssertNonvoid(InstancePtr != NULL);

	Value = XZDma_ReadReg(InstancePtr->Config.BaseAddress,
			(XZDMA_CH_STS_OFFSET)) & (XZDMA_STS_ALL_MASK);

	if ((Value == XZDMA_STS_DONE_MASK) ||
			(Value == XZDMA_STS_DONE_ERR_MASK)) {
		Status = XZDMA_IDLE;
	}
	else if (Value == XZDMA_STS_PAUSE_MASK) {
		Status = XZDMA_PAUSE;
	}
	else {
		Status = XZDMA_BUSY;
	}

	return Status;

}

/*****************************************************************************/
/**
*
* This function sets all the required fields for initiating data transfer. Data
* transfer elements needs to be passed through structure pointer.
* Data transfer can be done in any of the three modes (simple, Linear or Linked
* List) based on the selected mode but before calling this API make sure that
* ZDMA is in Idle state.
*
* @param	InstancePtr is a pointer to the XZDma instance.
* @param	Data is a pointer of array to the XZDma_Transfer structure which
*		has all the configuration fields for initiating data transfer.
*		The fields of the structure are:
*		- SrcAddr      - Source address
*		- DstAddr     - Destination address
*		- Size      - size of the data to be transferred in bytes
*		- SrcCoherent  - AXI transactions generated to process the
*				descriptor payload for source channel
*			- 0 - Non coherent
*			- 1 - Coherent
*		- DstCoherent - AXI transactions generated to process the
*				descriptor payload for destination channel
*			- 0 - Non coherent
*			- 1 - Coherent
*		- Pause 	-  Valid only for scatter gather mode.
*				Will pause after completion of this descriptor.
* @param	Num specifies number of array elements of Data pointer.
*		- For simple mode Num should be equal to 1
*		- For Scatter gather mode (either linear or linked list) Num
*		  can be any choice. (But based on which memory should be
*		  allocated by Application) It should be less than the return
*		  value of XZDma_CreateBDList.
*
* @return
*		- XST_SUCCESS - if ZDMA initiated the transfer.
*		- XST_FAILURE - if ZDMA has not initiated data transfer.
*
* @note		After Pause to resume the transfer need to use the following
*		API
*		- XZDma_Resume
*		User should provide allocated memory and descriptor type in
*		scatter gather mode through the following API before calling
*		the start API.
*		- XZDma_SetDescriptorType(XZDma *InstancePtr,
*			XZDma_DscrType TypeOfDscr, UINTPTR Dscr_MemPtr,
*							u32 NoOfBytes)
*
******************************************************************************/
s32 XZDma_Start(XZDma *InstancePtr, XZDma_Transfer *Data, u32 Num)
{
	s32 Status;

	/* Verify arguments */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(Data != NULL);
	Xil_AssertNonvoid(Num != 0x00U);

	if ((InstancePtr->ChannelState == XZDMA_BUSY) &&
			(Num >= InstancePtr->Descriptor.DscrCount)) {
		Status = XST_FAILURE;
	}
	else {
		if (InstancePtr->IsSgDma != TRUE) {
			XZDma_SimpleMode(InstancePtr, Data);
			Status = XST_SUCCESS;
		}
		else {

			XZDma_ScatterGather(InstancePtr, Data, Num);
			Status = XST_SUCCESS;
		}

		XZDma_Enable(InstancePtr);
	}

	return Status;
}

/*****************************************************************************/
/**
*
* This static function sets all the required fields for initiating data
* transfer in simple mode.
*
* @param	InstancePtr is a pointer to the XZDma instance.
* @param	Data is a pointer of array to the XZDma_Transfer structure
*		which has all the configuration fields for initiating data
*		transfer.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
static void XZDma_SimpleMode(XZDma *InstancePtr, XZDma_Transfer *Data)
{

	u32 Value;

	/* Verify arguments */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Data != NULL);

	XZDma_WriteReg((InstancePtr->Config.BaseAddress),
		XZDMA_CH_SRC_DSCR_WORD0_OFFSET,
			(Data->SrcAddr & XZDMA_WORD0_LSB_MASK));
	XZDma_WriteReg((InstancePtr->Config.BaseAddress),
		XZDMA_CH_SRC_DSCR_WORD1_OFFSET,
		(((u64)Data->SrcAddr >> XZDMA_WORD1_MSB_SHIFT) &
		XZDMA_WORD1_MSB_MASK));

	XZDma_WriteReg((InstancePtr->Config.BaseAddress),
		XZDMA_CH_DST_DSCR_WORD0_OFFSET,
		(Data->DstAddr & XZDMA_WORD0_LSB_MASK));
	XZDma_WriteReg((InstancePtr->Config.BaseAddress),
		XZDMA_CH_DST_DSCR_WORD1_OFFSET,
		(((u64)Data->DstAddr >> XZDMA_WORD1_MSB_SHIFT) &
		XZDMA_WORD1_MSB_MASK));

	XZDma_WriteReg((InstancePtr->Config.BaseAddress),
		XZDMA_CH_SRC_DSCR_WORD2_OFFSET,
		(Data->Size & XZDMA_WORD2_SIZE_MASK));
	XZDma_WriteReg((InstancePtr->Config.BaseAddress),
		XZDMA_CH_DST_DSCR_WORD2_OFFSET,
		(Data->Size & XZDMA_WORD2_SIZE_MASK));

	Value = (u32)(Data->SrcCoherent & XZDMA_WORD3_COHRNT_MASK);
	XZDma_WriteReg((InstancePtr->Config.BaseAddress),
		XZDMA_CH_SRC_DSCR_WORD3_OFFSET, Value);

	Value = (u32)(Data->DstCoherent & XZDMA_WORD3_COHRNT_MASK);
	XZDma_WriteReg((InstancePtr->Config.BaseAddress),
			XZDMA_CH_DST_DSCR_WORD3_OFFSET, Value);

}

/*****************************************************************************/
/**
*
* This static function sets all the required fields for initiating data
* transfer in scatter gather mode.
*
* @param	InstancePtr is a pointer to the XZDma instance.
* @param	Data is a pointer of array to the XZDma_Transfer structure
*		which has all the configuration fields for initiating data
*		transfer.
* @param	Num specifies number of array elements of Data pointer.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
static void XZDma_ScatterGather(XZDma *InstancePtr, XZDma_Transfer *Data,
								u32 Num)
{
	u32 Count = 0x00U;
	u8 Last;
	XZDma_Transfer *LocalData = Data;
	XZDma_LiDscr *LiSrcDscr =
		(XZDma_LiDscr *)(void *)(InstancePtr->Descriptor.SrcDscrPtr);
	XZDma_LiDscr *LiDstDscr =
		(XZDma_LiDscr *)(void *)(InstancePtr->Descriptor.DstDscrPtr);
	XZDma_LlDscr *LlSrcDscr =
		(XZDma_LlDscr *)(void *)(InstancePtr->Descriptor.SrcDscrPtr);
	XZDma_LlDscr *LlDstDscr =
		(XZDma_LlDscr *)(void *)(InstancePtr->Descriptor.DstDscrPtr);

	/* Verify arguments */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Data != NULL);
	Xil_AssertVoid(Num != 0x00U);

	if (InstancePtr->Descriptor.DscrType == XZDMA_LINEAR) {
		Last = FALSE;
		do {
			if (Count == (Num- 1)) {
				Last = TRUE;
			}
			XZDma_LinearMode(InstancePtr, LocalData, LiSrcDscr,
							LiDstDscr, Last);
			Count++;
			LiSrcDscr++;
			LiDstDscr++;
			LocalData++;
		} while(Count < Num);
	}
	else {
		Last = FALSE;
		do {
			if (Count == (Num - 1)) {
				Last = TRUE;
			}
			XZDma_LinkedListMode(InstancePtr, LocalData, LlSrcDscr,
							LlDstDscr, Last);
			Count++;
			LlDstDscr++;
			LlSrcDscr++;
			LocalData++;
		} while(Count < Num);
	}

	XZDma_WriteReg(InstancePtr->Config.BaseAddress,
		XZDMA_CH_SRC_START_LSB_OFFSET,
		((UINTPTR)(InstancePtr->Descriptor.SrcDscrPtr) &
					XZDMA_WORD0_LSB_MASK));
	XZDma_WriteReg(InstancePtr->Config.BaseAddress,
		XZDMA_CH_SRC_START_MSB_OFFSET,
		(((u64)(UINTPTR)(InstancePtr->Descriptor.SrcDscrPtr) >>
			XZDMA_WORD1_MSB_SHIFT) & XZDMA_WORD1_MSB_MASK));
	XZDma_WriteReg(InstancePtr->Config.BaseAddress,
		XZDMA_CH_DST_START_LSB_OFFSET,
		((UINTPTR)(InstancePtr->Descriptor.DstDscrPtr) &
					XZDMA_WORD0_LSB_MASK));
	XZDma_WriteReg(InstancePtr->Config.BaseAddress,
		XZDMA_CH_DST_START_MSB_OFFSET,
		(((u64)(UINTPTR)(InstancePtr->Descriptor.DstDscrPtr) >>
			XZDMA_WORD1_MSB_SHIFT) & XZDMA_WORD1_MSB_MASK));
}

/*****************************************************************************/
/**
*
* This static function sets all the required fields for initiating data
* transfer in Linear descriptor type.
*
* @param	InstancePtr is a pointer to the XZDma instance.
* @param	Data is a pointer of array to the XZDma_Transfer structure which
*		has all the configuration fields for initiating data transfer.
* @param	SrcDscrPtr is descriptor pointer of source in which Data fields
*		has to be filled.
* @param	DstDscrPtr is descriptor pointer of destination in which Data
*		fields has to be filled.
* @param	IsLast specifies whether provided descriptor pointer is last
*		one or not.
*		- XZDMA_TRUE - If descriptor is last
*		- XZDMA_FALSE - If descriptor is not last
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
static void XZDma_LinearMode(XZDma *InstancePtr, XZDma_Transfer *Data,
	XZDma_LiDscr *SrcDscrPtr, XZDma_LiDscr *DstDscrPtr, u8 IsLast)
{
	u32 Value;

	/* Verify arguments */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Data != NULL);
	Xil_AssertVoid(SrcDscrPtr != NULL);
	Xil_AssertVoid(DstDscrPtr != NULL);
	Xil_AssertVoid((IsLast == TRUE) || (IsLast == FALSE));

	if (Data->Pause == TRUE) {
		Value = XZDMA_WORD3_CMD_PAUSE_MASK;
	}
	else if (IsLast == TRUE) {
		Value = XZDMA_WORD3_CMD_STOP_MASK;
	}
	else {
		Value = XZDMA_WORD3_CMD_NXTVALID_MASK;
	}
	if (Data->SrcCoherent == TRUE) {
		Value |= XZDMA_WORD3_COHRNT_MASK;
	}

	XZDma_ConfigLinear(SrcDscrPtr, (u64)Data->SrcAddr, Data->Size, Value);

	Value = 0U;

	if (Data->DstCoherent == TRUE) {
		Value |= XZDMA_WORD3_COHRNT_MASK;
	}

	XZDma_ConfigLinear(DstDscrPtr, (u64)Data->DstAddr, Data->Size, Value);

}

/*****************************************************************************/
/**
*
* This static function sets all the required fields for initiating data
* transfer in Linear descriptor type.
*
* @param	DscrPtr is a pointer to source/destination descriptor.
* @param	Addr is a 64 bit variable which denotes the address of data.
* @param	Size specifies the amount of the data to be transferred.
* @param	CtrlValue contains all the control fields of descriptor.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
static void XZDma_ConfigLinear(XZDma_LiDscr *DscrPtr, u64 Addr, u32 Size,
								u32 CtrlValue)
{
	/* Verify arguments */
	Xil_AssertVoid(DscrPtr != NULL);
	Xil_AssertVoid(Addr != 0x00U);

	DscrPtr->Address = Addr;
	DscrPtr->Size = Size & XZDMA_WORD2_SIZE_MASK;
	DscrPtr->Cntl = CtrlValue;

	Xil_DCacheFlushRange((UINTPTR)DscrPtr, sizeof(XZDma_LlDscr));

}

/*****************************************************************************/
/**
*
* This static function sets all the required fields for initiating data
* transfer in Linked list descriptor type.
*
* @param	InstancePtr is a pointer to the XZDma instance.
* @param	Data is a pointer of array to the XZDma_Transfer structure which
*		has all the configuration fields for initiating data transfer.
* @param	SrcDscrPtr is descriptor pointer of source in which Data fields
*		has to be filled.
* @param	DstDscrPtr is descriptor pointer of destination in which Data
*		fields has to be filled.
* @param	IsLast specifies whether provided descriptor pointer is last
*		one or not.
*		- TRUE - If descriptor is last
*		- FALSE - If descriptor is not last
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
static void XZDma_LinkedListMode(XZDma *InstancePtr, XZDma_Transfer *Data,
	XZDma_LlDscr *SrcDscrPtr,XZDma_LlDscr *DstDscrPtr, u8 IsLast)
{
	u32 Value;
	XZDma_LlDscr *NextSrc = SrcDscrPtr;
	XZDma_LlDscr *NextDst = DstDscrPtr;
	u64 NextSrcAdrs = 0x00U;
	u64 NextDstAdrs = 0x00U;

	/* Verify arguments */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(Data != NULL);
	Xil_AssertVoid(SrcDscrPtr != NULL);
	Xil_AssertVoid(DstDscrPtr != NULL);
	Xil_AssertVoid((IsLast == TRUE) || (IsLast == FALSE));

	NextDst++;
	NextSrc++;

	if (Data->Pause == TRUE) {
		Value = XZDMA_WORD3_CMD_PAUSE_MASK;
		if (IsLast != TRUE) {
			NextSrcAdrs = (u64)(UINTPTR)NextSrc;
			NextDstAdrs = (u64)(UINTPTR)NextDst;
		}
	}
	else if (IsLast == TRUE) {
		Value = XZDMA_WORD3_CMD_STOP_MASK;
	}
	else {
		Value = XZDMA_WORD3_CMD_NXTVALID_MASK;
		NextSrcAdrs = (u64)(UINTPTR)NextSrc;
		NextDstAdrs = (u64)(UINTPTR)NextDst;
	}
	if (Data->SrcCoherent == TRUE) {
		Value |= XZDMA_WORD3_COHRNT_MASK;
	}

	XZDma_ConfigLinkedList(SrcDscrPtr, (u64)Data->SrcAddr,
					Data->Size, Value, NextSrcAdrs);

	Value = 0U;

	if (Data->DstCoherent == TRUE) {
		Value |= XZDMA_WORD3_COHRNT_MASK;
	}

	XZDma_ConfigLinkedList(DstDscrPtr, (u64)Data->DstAddr,
					Data->Size, Value, NextDstAdrs);

}

/*****************************************************************************/
/**
*
* This static function sets all the required fields for initiating data
* transfer in Linked list descriptor type.
*
* @param	DscrPtr is a pointer to source/destination descriptor.
* @param	Addr is a 64 bit variable which denotes the address of data.
* @param	Size specifies the amount of the data to be transferred.
* @param	CtrlValue contains all the control fields of descriptor.
* @param	NextDscrAddr is the address of next descriptor.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
static void XZDma_ConfigLinkedList(XZDma_LlDscr *DscrPtr, u64 Addr, u32 Size,
			u32 CtrlValue, u64 NextDscrAddr)
{
	/* Verify arguments */
	Xil_AssertVoid(DscrPtr != NULL);
	Xil_AssertVoid(Addr != 0x00U);

	DscrPtr->Address = Addr;
	DscrPtr->Size = Size & XZDMA_WORD2_SIZE_MASK;
	DscrPtr->Cntl = CtrlValue;
	DscrPtr->NextDscr = NextDscrAddr;
	DscrPtr->Reserved = 0U;

	Xil_DCacheFlushRange((UINTPTR)DscrPtr, sizeof(XZDma_LlDscr));
}

/*****************************************************************************/
/**
* This static function enable's all the interrupts which user intended to
* enable and enables the ZDMA channel for initiating data transfer.
*
* @param	InstancePtr is a pointer to the XZDma instance.
* @return	None.
*
* @note		None.
*
******************************************************************************/

static void XZDma_Enable(XZDma *InstancePtr)
{
	/* Verify arguments */
	Xil_AssertVoid(InstancePtr != NULL);

	XZDma_WriteReg(InstancePtr->Config.BaseAddress, XZDMA_CH_IEN_OFFSET,
			(InstancePtr->IntrMask & XZDMA_IXR_ALL_INTR_MASK));
	InstancePtr->ChannelState = XZDMA_BUSY;
	XZDma_EnableCh(InstancePtr);

}

/*****************************************************************************/
/**
* This static function gets all the reset configurations of ZDMA.
*
* @param	InstancePtr is a pointer to the XZDma instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
static void XZDma_GetConfigurations(XZDma *InstancePtr)
{
	/* Verify arguments */
	Xil_AssertVoid(InstancePtr != NULL);

	InstancePtr->DataConfig.SrcIssue = (u8)XZDMA_CTRL1_SRC_ISSUE_MASK;
	InstancePtr->DataConfig.SrcBurstType = XZDMA_INCR_BURST;
	InstancePtr->DataConfig.SrcBurstLen = 0xFU;
	InstancePtr->DataConfig.OverFetch = 1U;
	InstancePtr->DataConfig.DstBurstType = XZDMA_INCR_BURST;
	InstancePtr->DataConfig.DstBurstLen = 0xFU;
	InstancePtr->DataConfig.SrcCache = 0x2U;
	InstancePtr->DataConfig.DstCache = 0x2U;
	InstancePtr->DataConfig.SrcQos = 0x0U;
	InstancePtr->DataConfig.DstQos = 0x0U;

	InstancePtr->DscrConfig.AXCache = 0U;
	InstancePtr->DscrConfig.AXQos = 0U;
	InstancePtr->DscrConfig.AxCoherent = 0U;
}

/*****************************************************************************/
/**
*
* This routine is a stub for the asynchronous callbacks. The stub is here in
* case the upper layer forgot to set the handlers. On initialization, All
* handlers are set to this callback. It is considered an error for this
* handler to be invoked.
*
* @param	CallBackRef is a callback reference passed in by the upper
*		layer when setting the callback functions, and passed back to
*		the upper layer when the callback is invoked.
* @param	Mask is the type of the interrupts to enable. Use OR'ing of
*		XZDMA_IXR_DMA_*_MASK constants defined in xzdma_hw.h to create
*		this parameter value.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
static void StubCallBack(void *CallBackRef, u32 Mask)
{
	/* Verify arguments. */
	Xil_AssertVoid(CallBackRef != NULL);
	Xil_AssertVoid(Mask != (u32)0x00);
	Xil_AssertVoidAlways();
}

/*****************************************************************************/
/**
*
* This routine is a stub for the DMA done callback. The stub is here in
* case the upper layer forgot to set the handlers. On initialization, Done
* handler are set to this callback.
*
* @param	CallBackRef is a callback reference passed in by the upper
*		layer when setting the callback functions, and passed back to
*		the upper layer when the callback is invoked.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
static void StubDoneCallBack(void *CallBackRef)
{
	/* Verify arguments. */
	Xil_AssertVoid(CallBackRef != NULL);
	Xil_AssertVoidAlways();
}
/** @} */
