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
* @file xcsudma.c
* @addtogroup csudma_v1_0
* @{
*
* This file contains the implementation of the interface functions for CSU_DMA
* driver. Refer to the header file xcsudma.h for more detailed information.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who     Date     Changes
* ----- ------  -------- ---------------------------------------------------
* 1.0   vnsld   22/10/14 First release
* 1.1   adk     10/05/16 Fixed CR#951040 race condition in the recv path when
*                        source and destination points to the same buffer.
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xcsudma.h"

/************************** Function Prototypes ******************************/


/************************** Function Definitions *****************************/

/*****************************************************************************/
/**
*
* This function initializes an CSU_DMA core. This function must be called
* prior to using an CSU_DMA core. Initialization of an CSU_DMA includes setting
* up the instance data and ensuring the hardware is in a quiescent state.
*
* @param	InstancePtr is a pointer to the XCsuDma instance.
* @param	CfgPtr is a reference to a structure containing information
*		about a specific XCsuDma instance.
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
s32 XCsuDma_CfgInitialize(XCsuDma *InstancePtr, XCsuDma_Config *CfgPtr,
			u32 EffectiveAddr)
{

	/* Verify arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(CfgPtr != NULL);
	Xil_AssertNonvoid(EffectiveAddr != ((u32)0x0));

	/* Setup the instance */
	(void)memcpy((void *)&(InstancePtr->Config), (const void *)CfgPtr,
						sizeof(XCsuDma_Config));
	InstancePtr->Config.BaseAddress = EffectiveAddr;

	XCsuDma_Reset();

	InstancePtr->IsReady = (u32)(XIL_COMPONENT_IS_READY);

	return (XST_SUCCESS);

}

/*****************************************************************************/
/**
*
* This function sets the starting address and amount(size) of the data to be
* transfered from/to the memory through the AXI interface.
*
* @param	InstancePtr is a pointer to XCsuDma instance to be worked on.
* @param	Channel represents the type of channel either it is Source or
* 		Destination.
*		Source channel      - XCSUDMA_SRC_CHANNEL
*		Destination Channel - XCSUDMA_DST_CHANNEL
* @param	Addr is a 64 bit variable which holds the starting address of
* 		data which needs to write into the memory(DST) (or read	from
* 		the memory(SRC)).
* @param	Size is a 32 bit variable which represents the number of 4 byte
* 		words needs to be transfered from starting address.
* @param	EnDataLast is to trigger an end of message. It will enable or
* 		disable data_inp_last signal to stream interface when current
* 		command is completed. It is applicable only to source channel
* 		and neglected for destination channel.
* 		-	1 - Asserts data_inp_last signal.
* 		-	0 - data_inp_last will not be asserted.
*
* @return	None.
*
* @note		Data_inp_last signal is asserted simultaneously with the
* 		data_inp_valid signal associated with the final 32-bit word
*		transfer.
*
******************************************************************************/
void XCsuDma_Transfer(XCsuDma *InstancePtr, XCsuDma_Channel Channel,
					UINTPTR Addr, u32 Size, u8 EnDataLast)
{
	/* Verify arguments */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(((Addr) & (u64)(XCSUDMA_ADDR_LSB_MASK)) == (u64)0x00);
	Xil_AssertVoid((Channel == (XCSUDMA_SRC_CHANNEL)) ||
					(Channel == (XCSUDMA_DST_CHANNEL)));
	Xil_AssertVoid(Size <= (u32)(XCSUDMA_SIZE_MAX));
	Xil_AssertVoid(InstancePtr->IsReady == (u32)(XIL_COMPONENT_IS_READY));

	/* Flushing cache memory */
	if (Channel == (XCSUDMA_SRC_CHANNEL)) {
		Xil_DCacheFlushRange(Addr, Size << (u32)(XCSUDMA_SIZE_SHIFT));
	}
	/* Invalidating cache memory */
	else {
#if defined(__aarch64__)
		Xil_DCacheInvalidateRange(Addr, Size <<
					(u32)(XCSUDMA_SIZE_SHIFT));
#else
		Xil_DCacheFlushRange(Addr, Size << (u32)(XCSUDMA_SIZE_SHIFT));
#endif
	}

	XCsuDma_WriteReg(InstancePtr->Config.BaseAddress,
		((u32)(XCSUDMA_ADDR_OFFSET) +
		((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF))),
				((u32)(Addr) & (u32)(XCSUDMA_ADDR_MASK)));

	XCsuDma_WriteReg(InstancePtr->Config.BaseAddress,
		((u32)(XCSUDMA_ADDR_MSB_OFFSET) +
			((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF))),
		(((u64)Addr >> (u32)(XCSUDMA_MSB_ADDR_SHIFT)) &
					(u32)(XCSUDMA_MSB_ADDR_MASK)));

	if (EnDataLast == (u8)(XCSUDMA_LAST_WORD_MASK)) {
		XCsuDma_WriteReg(InstancePtr->Config.BaseAddress,
			((u32)(XCSUDMA_SIZE_OFFSET) +
				((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF))),
			((Size << (u32)(XCSUDMA_SIZE_SHIFT)) |
					(u32)(XCSUDMA_LAST_WORD_MASK)));
	}
	else {
		XCsuDma_WriteReg(InstancePtr->Config.BaseAddress,
			((u32)(XCSUDMA_SIZE_OFFSET) +
				((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF))),
				(Size << (u32)(XCSUDMA_SIZE_SHIFT)));
	}
}

/*****************************************************************************/
/**
*
* This function returns the current address location of the memory, from where
* it has to read the data(SRC) or the location where it has to write the data
* (DST) based on the channel selection.
*
* @param	InstancePtr is a pointer to XCsuDma instance to be worked on.
* @param	Channel represents the type of channel either it is Source or
* 		Destination.
*		Source channel      - XCSUDMA_SRC_CHANNEL
*		Destination Channel - XCSUDMA_DST_CHANNEL
*
* @return	Address is a 64 bit variable which holds the current address.
*		- From this location data has to be read(SRC)
*		- At this location data has to be written(DST)
*
* @note		None.
*
******************************************************************************/
u64 XCsuDma_GetAddr(XCsuDma *InstancePtr, XCsuDma_Channel Channel)
{
	u64 FullAddr;

	/* Verify arguments */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid((Channel == (XCSUDMA_SRC_CHANNEL)) ||
					(Channel == (XCSUDMA_DST_CHANNEL)));

	FullAddr = XCsuDma_ReadReg(InstancePtr->Config.BaseAddress,
				((u32)(XCSUDMA_ADDR_OFFSET) +
			((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF))));

	FullAddr |= (u64)((u64)XCsuDma_ReadReg(InstancePtr->Config.BaseAddress,
			((u32)(XCSUDMA_ADDR_MSB_OFFSET) +
			((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF)))) <<
				(u64)(XCSUDMA_MSB_ADDR_SHIFT));

	return FullAddr;
}

/*****************************************************************************/
/**
*
* This function returns the size of the data yet to be transfered from memory
* to CSU_DMA or CSU_DMA to memory based on the channel selection.
*
* @param	InstancePtr is a pointer to XCsuDma instance to be worked on.
* @param	Channel represents the type of channel either it is Source or
* 		Destination.
*		Source channel      - XCSUDMA_SRC_CHANNEL
*		Destination Channel - XCSUDMA_DST_CHANNEL
*
* @return	Size is amount of data yet to be transfered.
*
* @note		None.
*
******************************************************************************/
u32 XCsuDma_GetSize(XCsuDma *InstancePtr, XCsuDma_Channel Channel)
{
	u32 Size;

	/* Verify arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid((Channel == (XCSUDMA_SRC_CHANNEL)) ||
					(Channel == (XCSUDMA_DST_CHANNEL)));

	Size = XCsuDma_ReadReg(InstancePtr->Config.BaseAddress,
		((u32)(XCSUDMA_SIZE_OFFSET) +
		((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF)))) >>
					(u32)(XCSUDMA_SIZE_SHIFT);

	return Size;
}

/*****************************************************************************/
/**
*
* This function pause the Channel data tranfer to/from memory or to/from stream
* based on pause type.
*
* @param	InstancePtr is a pointer to XCsuDma instance to be worked on.
* @param	Channel represents the type of channel either it is Source or
* 		Destination.
*		Source channel      - XCSUDMA_SRC_CHANNEL
*		Destination Channel - XCSUDMA_DST_CHANNEL
* @param	Type is type of the pause to be enabled.
*		- XCSUDMA_PAUSE_MEMORY(0) - Pause memory
*			- SRC Stops issuing of new read commands to memory.
*			- DST Stops issuing of new write commands to memory.
*		- XCSUDMA_PAUSE_STREAM(1) - Pause stream
*			- SRC Stops transfer of data from FIFO to Stream.
*			- DST Stops transfer of data from stream to FIFO.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XCsuDma_Pause(XCsuDma *InstancePtr, XCsuDma_Channel Channel,
						XCsuDma_PauseType Type)
{
	/* Verify arguments. */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid((Type == (XCSUDMA_PAUSE_MEMORY)) ||
				(Type == (XCSUDMA_PAUSE_STREAM)));
	Xil_AssertVoid((Channel == (XCSUDMA_SRC_CHANNEL)) ||
					(Channel == (XCSUDMA_DST_CHANNEL)));
	Xil_AssertVoid(InstancePtr->IsReady == (u32)(XIL_COMPONENT_IS_READY));

	/* Pause Memory Read/Write/Stream operations */
	if (Type == (XCSUDMA_PAUSE_MEMORY)) {
		XCsuDma_WriteReg(InstancePtr->Config.BaseAddress,
			((u32)(XCSUDMA_CTRL_OFFSET) +
				((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF))),
			(XCsuDma_ReadReg(InstancePtr->Config.BaseAddress,
				((u32)(XCSUDMA_CTRL_OFFSET) +
				((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF)))) |
					(u32)(XCSUDMA_CTRL_PAUSE_MEM_MASK)));
	}
	if (Type == (XCSUDMA_PAUSE_STREAM)) {
		XCsuDma_WriteReg(InstancePtr->Config.BaseAddress,
			((u32)(XCSUDMA_CTRL_OFFSET) +
				((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF))),
			(XCsuDma_ReadReg(InstancePtr->Config.BaseAddress,
				((u32)(XCSUDMA_CTRL_OFFSET) +
				(Channel * (u32)XCSUDMA_OFFSET_DIFF))) |
				(u32)(XCSUDMA_CTRL_PAUSE_STRM_MASK)));
	}
}

/*****************************************************************************/
/**
*
* This functions checks whether Channel's memory or stream is paused or not
* based on the given pause type.
*
* @param	InstancePtr is a pointer to XCsuDma instance to be worked on.
* @param	Channel represents the type of channel either it is Source or
* 		Destination.
*		Source channel      - XCSUDMA_SRC_CHANNEL
*		Destination Channel - XCSUDMA_DST_CHANNEL
* @param	Type is type of the pause which needs to be checked.
*		- XCSUDMA_PAUSE_MEMORY(0) - Pause memory
*			- SRC Stops issuing of new read commands to memory.
*			- DST Stops issuing of new write commands to memory.
*		- XCSUDMA_PAUSE_STREAM(1) - Pause stream
*			- SRC Stops transfer of data from FIFO to Stream.
*			- DST Stops transfer of data from stream to FIFO.
*
* @return	Returns the pause status.
*		- TRUE if it is in paused state.
*		- FALSE if it is not in pause state.
*
* @note		None.
*
******************************************************************************/
s32 XCsuDma_IsPaused(XCsuDma *InstancePtr, XCsuDma_Channel Channel,
		XCsuDma_PauseType Type)
{

	u32 Data;
	s32 PauseState;

	/* Verify arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid((Channel == (XCSUDMA_SRC_CHANNEL)) ||
					(Channel == (XCSUDMA_DST_CHANNEL)));
	Xil_AssertNonvoid((Type == (XCSUDMA_PAUSE_MEMORY)) ||
					(Type == (XCSUDMA_PAUSE_STREAM)));

	Data = XCsuDma_ReadReg(InstancePtr->Config.BaseAddress,
			((u32)(XCSUDMA_CTRL_OFFSET) +
			((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF))));

	/* To know Pause condition of Memory Read/Write/Stream operations */
	if (Type == (XCSUDMA_PAUSE_MEMORY)) {
		if ((Data & (u32)(XCSUDMA_CTRL_PAUSE_MEM_MASK)) ==
								(u32)0x00) {
			PauseState = (s32)(FALSE);
		}
		else {
			PauseState = (s32)(TRUE);
		}
	}
	else {
		if ((Data & (u32)(XCSUDMA_CTRL_PAUSE_STRM_MASK)) ==
								(u32)0x00) {
				PauseState = (s32)(FALSE);
		}
		else {
			PauseState = (s32)(TRUE);
		}
	}

	return (s32)PauseState;

}

/*****************************************************************************/
/**
*
* This function resumes the channel if it is in paused state and continues
* where it has left or no effect if it is not in paused state, based on the
* type of pause.
*
* @param	InstancePtr is a pointer to XCsuDma instance to be worked on.
* @param	Channel represents the type of channel either it is Source or
* 		Destination.
*		Source channel      - XCSUDMA_SRC_CHANNEL
*		Destination Channel - XCSUDMA_DST_CHANNEL
* @param	Type is type of the pause to be Resume if it is in pause
*		state.
*		- XCSUDMA_PAUSE_MEMORY(0) - Pause memory
*			- SRC Stops issuing of new read commands to memory.
*			- DST Stops issuing of new write commands to memory.
*		- XCSUDMA_PAUSE_STREAM(1) - Pause stream
*			- SRC Stops transfer of data from FIFO to Stream.
*			- DST Stops transfer of data from stream to FIFO.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XCsuDma_Resume(XCsuDma *InstancePtr, XCsuDma_Channel Channel,
		XCsuDma_PauseType Type)
{
	u32 Data;
	/* Verify arguments. */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid((Type == (XCSUDMA_PAUSE_MEMORY)) ||
			(Type == (XCSUDMA_PAUSE_STREAM)));
	Xil_AssertVoid((Channel == (XCSUDMA_SRC_CHANNEL)) ||
					(Channel == (XCSUDMA_DST_CHANNEL)));
	Xil_AssertVoid(InstancePtr->IsReady == (u32)(XIL_COMPONENT_IS_READY));

	Data = XCsuDma_ReadReg(InstancePtr->Config.BaseAddress,
			((u32)(XCSUDMA_CTRL_OFFSET) +
		((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF))));

	if (Type == (XCSUDMA_PAUSE_MEMORY)) {
		XCsuDma_WriteReg(InstancePtr->Config.BaseAddress,
		((u32)(XCSUDMA_CTRL_OFFSET) +
		((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF))),
		(Data &
				(~(XCSUDMA_CTRL_PAUSE_MEM_MASK))));
	}
	if (Type == (XCSUDMA_PAUSE_STREAM)) {
		XCsuDma_WriteReg(InstancePtr->Config.BaseAddress,
		((u32)(XCSUDMA_CTRL_OFFSET) +
		(((u32)Channel) * (u32)(XCSUDMA_OFFSET_DIFF))),
			( Data &
			(~(XCSUDMA_CTRL_PAUSE_STRM_MASK))));
	}
}

/*****************************************************************************/
/**
*
* This function returns the sum of all the data read from AXI memory. It is
* valid only one we use CSU_DMA source channel.
*
* @param	InstancePtr is a pointer to XCsuDma instance to be worked on.
*
* @return	Returns the sum of all the data read from memory.
*
* @note		Before start of the transfer need to clear this register to get
*		correct sum otherwise it adds to previous value which results
*		to wrong output.
*		Valid only for source channel
*
******************************************************************************/
u32 XCsuDma_GetCheckSum(XCsuDma *InstancePtr)
{
	u32 ChkSum;

	/* Verify arguments. */
	Xil_AssertNonvoid(InstancePtr != NULL);
	Xil_AssertNonvoid(InstancePtr->IsReady ==
				(u32)(XIL_COMPONENT_IS_READY));

	ChkSum = XCsuDma_ReadReg(InstancePtr->Config.BaseAddress,
						(u32)(XCSUDMA_CRC_OFFSET));

	return ChkSum;

}
/*****************************************************************************/
/**
*
* This function clears the check sum of the data read from AXI memory. It is
* valid only for CSU_DMA source channel.
*
* @param	InstancePtr is a pointer to XCsuDma instance to be worked on.
*
* @return	Returns the sum of all the data read from memory.
*
* @note		Before start of the transfer need to clear this register to get
*		correct sum otherwise it adds to previous value which results
*		to wrong output.
*
******************************************************************************/
void XCsuDma_ClearCheckSum(XCsuDma *InstancePtr)
{

	/* Verify arguments. */
	Xil_AssertVoid(InstancePtr != NULL);

	XCsuDma_WriteReg(InstancePtr->Config.BaseAddress,
		(u32)(XCSUDMA_CRC_OFFSET), (u32)(XCSUDMA_CRC_RESET_MASK));
}

/*****************************************************************************/
/**
* This function cofigures all the values of CSU_DMA's Channels with the values
* of updated XCsuDma_Configure structure.
*
* @param	InstancePtr is a pointer to XCsuDma instance to be worked on.
* @param	Channel represents the type of channel either it is Source or
* 		Destination.
*		Source channel      - XCSUDMA_SRC_CHANNEL
*		Destination Channel - XCSUDMA_DST_CHANNEL
* @param	ConfigurValues is a pointer to the structure XCsuDma_Configure
*		whose values are used to configure CSU_DMA core.
*		- SssFifoThesh   When the DST FIFO level >= this value,
*		  the SSS interface signal, "data_out_fifo_level_hit" will be
*		  asserted. This mechanism can be used by the SSS to flow
*		  control data that is being looped back from the SRC DMA.
*			- Range is (0x10 to 0x7A) threshold is 17 to 123
*			entries.
*			- It is valid only for DST CSU_DMA IP.
*		- ApbErr          When accessed to invalid APB the resulting
*		  pslerr will be
*			- 0 - 1'b0
*			- 1 - 1'b1
*		- EndianType      Type of endianness
*			- 0 doesn't change order
*			- 1 will flip the order.
*		- AxiBurstType....Type of the burst
*			- 0 will issue INCR type burst
*			- 1 will issue FIXED type burst
*		- TimeoutValue    Time out value for timers
*			- 0x000 to 0xFFE are valid inputs
*			- 0xFFF clears both timers
*		- FifoThresh......Programmed watermark value
*			- Range is 0x00 to 0x80 (0 to 128 entries).
*		- Acache         Sets the AXI CACHE bits on the AXI Write/Read
*		channel.
*			- Cacheable ARCACHE[1] for SRC Channel and AWCACHE[1]
*			  for DST channel are always 1, we need to configure
*			  remaining 3 signal support
*			  (Bufferable, Read allocate and Write allocate).
*			Valid inputs are:
*			- 0x000 - Cacheable, but do not allocate
*			- 0x001 - Cacheable and bufferable, but do not allocate
*			- 0x010 - Cacheable write-through, allocate on reads
*				  only
*			- 0x011 - Cacheable write-back, allocate on reads only
*			- 0x100 - Cacheable write-through, allocate on writes
*				  only
*			- 0x101 - Cacheable write-back, allocate on writes only
*			- 0x110 - Cacheable write-through, allocate on both
*				  reads and writes
*			- 0x111 - Cacheable write-back, allocate on both reads
*				  and writes
*		- RouteBit        To select route
*			- 0 : Command will be routed normally
*			- 1 : Command will be routed to APU's cache controller
*		- TimeoutEn       To enable or disable time out counters
*			- 0 : The 2 Timeout counters are disabled
*			- 1 : The 2 Timeout counters are enabled
*		- TimeoutPre      Set the prescaler value for the timeout in
*		clk (~2.5ns) cycles
*			- Range is 0x000(Prescaler enables timer every cycles)
*			  to 0xFFF(Prescaler enables timer every 4096 cycles)
*		- MaxOutCmds      Controls the maximumum number of outstanding
*		AXI read commands issued.
*			- Range is 0x0(Up to 1 Outstanding Read command
*			  allowed) to 0x8 (Up to 9 Outstanding Read
*			  command allowed)
*
* @return	None.
*
* @note		To use timers timeout value Timeout enable field should be
*		enabled.
*
******************************************************************************/
void XCsuDma_SetConfig(XCsuDma *InstancePtr, XCsuDma_Channel Channel,
					XCsuDma_Configure *ConfigurValues)
{
	u32 Data;

	/* Verify arguments. */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(InstancePtr->IsReady == (u32)(XIL_COMPONENT_IS_READY));
	Xil_AssertVoid(ConfigurValues != NULL);
	Xil_AssertVoid((Channel == (XCSUDMA_SRC_CHANNEL)) ||
				(Channel == (XCSUDMA_DST_CHANNEL)));
	Xil_AssertVoid(XCsuDma_IsBusy(InstancePtr, Channel) != (s32)(TRUE));

	Data = (((ConfigurValues->EndianType <<
			(u32)(XCSUDMA_CTRL_ENDIAN_SHIFT)) &
			(u32)(XCSUDMA_CTRL_ENDIAN_MASK)) |
		((ConfigurValues->ApbErr <<
			(u32)(XCSUDMA_CTRL_APB_ERR_SHIFT)) &
			(u32)(XCSUDMA_CTRL_APB_ERR_MASK)) |
		((ConfigurValues->AxiBurstType <<
			(u32)(XCSUDMA_CTRL_BURST_SHIFT)) &
			(u32)(XCSUDMA_CTRL_BURST_MASK)) |
		((ConfigurValues->TimeoutValue <<
			(u32)(XCSUDMA_CTRL_TIMEOUT_SHIFT)) &
			(u32)(XCSUDMA_CTRL_TIMEOUT_MASK)) |
		((ConfigurValues->FifoThresh <<
			(u32)(XCSUDMA_CTRL_FIFO_THRESH_SHIFT)) &
			(u32)(XCSUDMA_CTRL_FIFO_THRESH_MASK)));
	if(Channel == XCSUDMA_DST_CHANNEL) {
		Data = Data | (u32)((ConfigurValues->SssFifoThesh <<
				(u32)(XCSUDMA_CTRL_SSS_FIFOTHRESH_SHIFT)) &
				(u32)(XCSUDMA_CTRL_SSS_FIFOTHRESH_MASK));
	}

	XCsuDma_WriteReg(InstancePtr->Config.BaseAddress,
			((u32)(XCSUDMA_CTRL_OFFSET) +
			((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF))), Data);

	Data = (XCsuDma_ReadReg(InstancePtr->Config.BaseAddress,
			((u32)(XCSUDMA_CTRL2_OFFSET) +
			((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF)))) &
				(u32)(XCSUDMA_CTRL2_RESERVED_MASK));
	Data |= (((ConfigurValues->Acache <<
			(u32)(XCSUDMA_CTRL2_ACACHE_SHIFT)) &
			(u32)(XCSUDMA_CTRL2_ACACHE_MASK)) |
		((ConfigurValues->RouteBit <<
			(u32)(XCSUDMA_CTRL2_ROUTE_SHIFT)) &
			(u32)(XCSUDMA_CTRL2_ROUTE_MASK)) |
		((ConfigurValues->TimeoutEn <<
			(u32)(XCSUDMA_CTRL2_TIMEOUT_EN_SHIFT)) &
			(u32)(XCSUDMA_CTRL2_TIMEOUT_EN_MASK)) |
		((ConfigurValues->TimeoutPre <<
			(u32)(XCSUDMA_CTRL2_TIMEOUT_PRE_SHIFT)) &
			(u32)(XCSUDMA_CTRL2_TIMEOUT_PRE_MASK)) |
		((ConfigurValues->MaxOutCmds) &
			(u32)(XCSUDMA_CTRL2_MAXCMDS_MASK)));

	XCsuDma_WriteReg(InstancePtr->Config.BaseAddress,
		((u32)(XCSUDMA_CTRL2_OFFSET) +
			((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF))), Data);
}

/*****************************************************************************/
/**
*
* This function updates XCsuDma_Configure structure members with the cofigured
* values of CSU_DMA's Channel.
*
* @param	InstancePtr is a pointer to XCsuDma instance to be worked on.
* @param	Channel represents the type of channel either it is Source or
* 		Destination.
*		Source channel      - XCSUDMA_SRC_CHANNEL
*		Destination Channel - XCSUDMA_DST_CHANNEL
* @param	ConfigurValues is a pointer to the structure XCsuDma_Configure
*		whose members are updated with configurations of CSU_DMA core.
*		- SssFifoThesh   When the DST FIFO level >= this value,
*		  the SSS interface signal, "data_out_fifo_level_hit" will be
*		  asserted. This mechanism can be used by the SSS to flow
*		  control data that is being looped back from the SRC DMA.
*			- Range is (0x10 to 0x7A) threshold is 17 to 123
*			entries.
*			- It is valid only for DST CSU_DMA IP.
*		- ApbErr          When accessed to invalid APB the resulting
*		  pslerr will be
*			- 0 - 1'b0
*			- 1 - 1'b1
*		- EndianType      Type of endianness
*			- 0 doesn't change order
*			- 1 will flip the order.
*		- AxiBurstType....Type of the burst
*			- 0 will issue INCR type burst
*			- 1 will issue FIXED type burst
*		- TimeoutValue    Time out value for timers
*			- 0x000 to 0xFFE are valid inputs
*			- 0xFFF clears both timers
*		- FifoThresh......Programmed watermark value
*			- Range is 0x00 to 0x80 (0 to 128 entries).
*		- Acache         Sets the AXI CACHE bits on the AXI Write/Read
*		channel.
*			- Cacheable ARCACHE[1] for SRC Channel and AWCACHE[1]
*			  for DST channel are always 1, we need to configure
*			  remaining 3 signal support
*			  (Bufferable, Read allocate and Write allocate).
*			Valid inputs are:
*			- 0x000 - Cacheable, but do not allocate
*			- 0x001 - Cacheable and bufferable, but do not allocate
*			- 0x010 - Cacheable write-through, allocate on reads
*				  only
*			- 0x011 - Cacheable write-back, allocate on reads only
*			- 0x100 - Cacheable write-through, allocate on writes
*				  only
*			- 0x101 - Cacheable write-back, allocate on writes only
*			- 0x110 - Cacheable write-through, allocate on both
*				  reads and writes
*			- 0x111 - Cacheable write-back, allocate on both reads
*				  and writes
*		- RouteBit        To select route
*			- 0 : Command will be routed based normally
*			- 1 : Command will be routed to APU's cache controller
*		- TimeoutEn       To enable or disable time out counters
*			- 0 : The 2 Timeout counters are disabled
*			- 1 : The 2 Timeout counters are enabled
*		- TimeoutPre      Set the prescaler value for the timeout in
*		clk (~2.5ns) cycles
*			- Range is 0x000(Prescaler enables timer every cycles)
*			 to 0xFFF(Prescaler enables timer every 4096 cycles)
*		- MaxOutCmds      Controls the maximumum number of outstanding
*		AXI read commands issued.
*			- Range is 0x0(Up to 1 Outstanding Read command
*			allowed) to 0x8 (Up to 9 Outstanding Read command
*			allowed)
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XCsuDma_GetConfig(XCsuDma *InstancePtr, XCsuDma_Channel Channel,
				XCsuDma_Configure *ConfigurValues)
{
	u32 Data;

	/* Verify arguments. */
	Xil_AssertVoid(InstancePtr != NULL);
	Xil_AssertVoid(ConfigurValues != NULL);
	Xil_AssertVoid((Channel == (XCSUDMA_SRC_CHANNEL)) ||
				(Channel == (XCSUDMA_DST_CHANNEL)));

	Data = XCsuDma_ReadReg(InstancePtr->Config.BaseAddress,
		((u32)(XCSUDMA_CTRL_OFFSET) +
			((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF))));

	if (Channel == (XCSUDMA_DST_CHANNEL)) {
		ConfigurValues->SssFifoThesh =
			(u8)((Data &
				(u32)(XCSUDMA_CTRL_SSS_FIFOTHRESH_MASK)) >>
				(u32)(XCSUDMA_CTRL_SSS_FIFOTHRESH_SHIFT));
	}
	ConfigurValues->ApbErr =
		(u8)((Data & (u32)(XCSUDMA_CTRL_APB_ERR_MASK)) >>
				(u32)(XCSUDMA_CTRL_APB_ERR_SHIFT));
	ConfigurValues->EndianType =
		(u8)((Data & (u32)(XCSUDMA_CTRL_ENDIAN_MASK)) >>
				(u32)(XCSUDMA_CTRL_ENDIAN_SHIFT));
	ConfigurValues->AxiBurstType =
		(u8)((Data & (u32)(XCSUDMA_CTRL_BURST_MASK)) >>
				(u32)(XCSUDMA_CTRL_BURST_SHIFT));
	ConfigurValues->TimeoutValue =
		((Data & (u32)(XCSUDMA_CTRL_TIMEOUT_MASK)) >>
				(u32)(XCSUDMA_CTRL_TIMEOUT_SHIFT));
	ConfigurValues->FifoThresh =
		(u8)((Data & (u32)(XCSUDMA_CTRL_FIFO_THRESH_MASK)) >>
				(u32)(XCSUDMA_CTRL_FIFO_THRESH_SHIFT));

	Data = XCsuDma_ReadReg(InstancePtr->Config.BaseAddress,
			((u32)(XCSUDMA_CTRL2_OFFSET) +
			((u32)Channel * (u32)(XCSUDMA_OFFSET_DIFF))));

	ConfigurValues->Acache =
			(u8)((Data & (u32)(XCSUDMA_CTRL2_ACACHE_MASK)) >>
					(u32)(XCSUDMA_CTRL2_ACACHE_SHIFT));
	ConfigurValues->RouteBit =
			(u8)((Data & (u32)(XCSUDMA_CTRL2_ROUTE_MASK)) >>
					(u32)(XCSUDMA_CTRL2_ROUTE_SHIFT));
	ConfigurValues->TimeoutEn =
			(u8)((Data & (u32)(XCSUDMA_CTRL2_TIMEOUT_EN_MASK)) >>
				(u32)(XCSUDMA_CTRL2_TIMEOUT_EN_SHIFT));
	ConfigurValues->TimeoutPre =
			(u16)((Data & (u32)(XCSUDMA_CTRL2_TIMEOUT_PRE_MASK)) >>
				(u32)(XCSUDMA_CTRL2_TIMEOUT_PRE_SHIFT));
	ConfigurValues->MaxOutCmds =
			(u8)((Data & (u32)(XCSUDMA_CTRL2_MAXCMDS_MASK)));

}
/** @} */
