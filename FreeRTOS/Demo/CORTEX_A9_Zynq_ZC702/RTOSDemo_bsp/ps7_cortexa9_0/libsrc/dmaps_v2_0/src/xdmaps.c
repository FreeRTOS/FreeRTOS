/******************************************************************************
*
* Copyright (C) 2009 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xdmaps.c
* @addtogroup dmaps_v2_0
* @{
*
* This file contains the implementation of the interface functions for XDmaPs
* driver. Refer to the header file xdmaps.h for more detailed information.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  	Date     Changes
* ----- ------ -------- ----------------------------------------------
* 1.00	hbm    08/19/2010 First Release
* 1.00  nm     05/25/2011 Updated for minor doxygen corrections
* 1.02a sg     05/16/2012 Made changes for doxygen and moved some function
*			  header from the xdmaps.h file to xdmaps.c file
*			  Other cleanup for coding guidelines and CR 657109
*			  and CR 657898
* 1.03a sg     07/16/2012 changed inline to __inline for CR665681
* 1.04a nm     10/22/2012 Fixed CR# 681671.
* 1.05a nm     04/15/2013 Fixed CR# 704396. Removed warnings when compiled
*			  with -Wall and -Wextra option in bsp.
*	       05/01/2013 Fixed CR# 700189. Changed XDmaPs_BuildDmaProg()
*			  function description.
*			  Fixed CR# 704396. Removed unused variables
*			  UseM2MByte & MemBurstLen from XDmaPs_BuildDmaProg()
*			  function.
* 1.07a asa    11/02/13. Made changes to fix compilation issues for iarcc.
*			   Removed the PDBG prints. By default they were always
*			   defined out and never used. The PDBG is non-standard for
*			   Xilinx drivers and no other driver does something similar.
*			   Since there is no easy way to fix compilation issues with
*			   the IARCC compiler around PDBG, it is better to remove it.
*			   Users can always use xil_printfs if they want to debug.
* </pre>
*
*****************************************************************************/

/***************************** Include Files ********************************/

#include <string.h>

#include "xstatus.h"
#include "xdmaps.h"
#include "xil_io.h"
#include "xil_cache.h"

#include "xil_printf.h"


/************************** Constant Definitions ****************************/

/* The following constant defines the amount of error that is allowed for
 * a specified baud rate. This error is the difference between the actual
 * baud rate that will be generated using the specified clock and the
 * desired baud rate.
 */

/**************************** Type Definitions ******************************/

/***************** Macros (Inline Functions) Definitions ********************/


/************************** Function Prototypes *****************************/
static int XDmaPs_Exec_DMAKILL(u32 BaseAddr,
				unsigned int Channel,
				unsigned int Thread);

static void XDmaPs_BufPool_Free(XDmaPs_ProgBuf *Pool, void *Buf);

static int XDmaPs_Exec_DMAGO(u32 BaseAddr, unsigned int Channel, u32 DmaProg);

static void XDmaPs_DoneISR_n(XDmaPs *InstPtr, unsigned Channel);
static void *XDmaPs_BufPool_Allocate(XDmaPs_ProgBuf *Pool);
static int XDmaPs_BuildDmaProg(unsigned Channel, XDmaPs_Cmd *Cmd,
				unsigned CacheLength);

static void XDmaPs_Print_DmaProgBuf(char *Buf, int Length);



/************************** Variable Definitions ****************************/

/****************************************************************************/
/**
*
* Initializes a specific XDmaPs instance such that it is ready to be used.
* The data format of the device is setup for 8 data bits, 1 stop bit, and no
* parity by default. The baud rate is set to a default value specified by
* Config->DefaultBaudRate if set, otherwise it is set to 19.2K baud. The
* receive FIFO threshold is set for 8 bytes. The default operating mode of the
* driver is polled mode.
*
* @param	InstPtr is a pointer to the XDmaPs instance.
* @param	Config is a reference to a structure containing information
*		about a specific XDmaPs driver.
* @param	EffectiveAddr is the device base address in the virtual memory
*		address space. The caller is responsible for keeping the
*		address mapping from EffectiveAddr to the device physical base
*		address unchanged once this function is invoked. Unexpected
*		errors may occur if the address mapping changes after this
*		function is called. If address translation is not used, pass in
*		the physical address instead.
*
* @return
*
*		- XST_SUCCESS on initialization completion
*
* @note		None.
*
*****************************************************************************/
int XDmaPs_CfgInitialize(XDmaPs *InstPtr,
			  XDmaPs_Config *Config,
			  u32 EffectiveAddr)
{
	int Status = XST_SUCCESS;
	unsigned int CacheLength = 0;
	u32 CfgReg;
	unsigned Channel;
	XDmaPs_ChannelData *ChanData;

	/*
	 * Assert validates the input arguments
	 */
	Xil_AssertNonvoid(InstPtr != NULL);
	Xil_AssertNonvoid(Config != NULL);

	/*
	 * Setup the driver instance using passed in parameters
	 */
	InstPtr->Config.DeviceId = Config->DeviceId;
	InstPtr->Config.BaseAddress = EffectiveAddr;

	CfgReg = XDmaPs_ReadReg(EffectiveAddr, XDMAPS_CR1_OFFSET);
	CacheLength = CfgReg & XDMAPS_CR1_I_CACHE_LEN_MASK;
	if (CacheLength < 2 || CacheLength > 5)
		CacheLength = 0;
	else
		CacheLength = 1 << CacheLength;

	InstPtr->CacheLength = CacheLength;

	memset(InstPtr->Chans, 0,
	       sizeof(XDmaPs_ChannelData[XDMAPS_CHANNELS_PER_DEV]));

	for (Channel = 0; Channel < XDMAPS_CHANNELS_PER_DEV; Channel++) {
		ChanData = InstPtr->Chans + Channel;
		ChanData->ChanId = Channel;
		ChanData->DevId = Config->DeviceId;
	}

	InstPtr->IsReady = 1;

	return Status;
}

/****************************************************************************/
/**
*
* Reset the DMA Manager.
*
* @param	InstPtr is the DMA instance.
*
* @return	0 on success, -1 on time out
*
* @note		None.
*
*****************************************************************************/
int XDmaPs_ResetManager(XDmaPs *InstPtr)
{
	int Status;
	Status = XDmaPs_Exec_DMAKILL(InstPtr->Config.BaseAddress,
				      0, 0);

	return Status;
}

/****************************************************************************/
/**
*
* Reset the specified DMA Channel.
*
* @param	InstPtr is the DMA instance.
* @param	Channel is the channel to be reset.
*
* @return	0 on success, -1 on time out
*
* @note		None.
*
*****************************************************************************/
int XDmaPs_ResetChannel(XDmaPs *InstPtr, unsigned int Channel)
{
	int Status;
	Status = XDmaPs_Exec_DMAKILL(InstPtr->Config.BaseAddress,
				      Channel, 1);

	return Status;

}

/*****************************************************************************/
/**
*
* Driver fault interrupt service routine
* This is the one that connects the GIC
*
* @param	InstPtr is the DMA instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XDmaPs_FaultISR(XDmaPs *InstPtr)
{

	void *DmaProgBuf;
	u32 Fsm; /* Fault status DMA manager register value */
	u32 Fsc; /* Fault status DMA channel register value */
	u32 FaultType; /* Fault type DMA manager register value */

	u32 BaseAddr = InstPtr->Config.BaseAddress;

	u32 Pc; /* DMA Pc or channel Pc */
	XDmaPs_ChannelData *ChanData;

	unsigned Chan;
	unsigned DevId;

	XDmaPs_Cmd *DmaCmd;

	Fsm = XDmaPs_ReadReg(BaseAddr, XDMAPS_FSM_OFFSET) & 0x01;
	Fsc = XDmaPs_ReadReg(BaseAddr, XDMAPS_FSC_OFFSET) & 0xFF;


	DevId = InstPtr->Config.DeviceId;

	if (Fsm) {
		/*
		 * if DMA manager is fault
		 */
		FaultType = XDmaPs_ReadReg(BaseAddr, XDMAPS_FTM_OFFSET);
		Pc = XDmaPs_ReadReg(BaseAddr, XDMAPS_DPC_OFFSET);

		xil_printf("PL330 device %d fault with type: %x at Pc %x\n",
			   DevId,
			   FaultType, Pc);

		/* kill the DMA manager thread */
		/* Should we disable interrupt?*/
		XDmaPs_Exec_DMAKILL(BaseAddr, 0, 0);
	}

	/*
	 * check which channel faults and kill the channel thread
	 */
	for (Chan = 0;
	     Chan < XDMAPS_CHANNELS_PER_DEV;
	     Chan++) {
		if (Fsc & (0x01 << Chan)) {
			FaultType =
				XDmaPs_ReadReg(BaseAddr,
						XDmaPs_FTCn_OFFSET(Chan));
			Pc = XDmaPs_ReadReg(BaseAddr,
					     XDmaPs_CPCn_OFFSET(Chan));

			/* kill the channel thread */
			/* Should we disable interrupt? */
			XDmaPs_Exec_DMAKILL(BaseAddr, Chan, 1);

			/*
			 * get the fault type and fault Pc and invoke the
			 * fault callback.
			 */
			ChanData = InstPtr->Chans + Chan;

			DmaCmd = ChanData->DmaCmdToHw;

			/* Should we check DmaCmd is not null */
			DmaCmd->DmaStatus = -1;
			DmaCmd->ChanFaultType = FaultType;
			DmaCmd->ChanFaultPCAddr = Pc;
			ChanData->DmaCmdFromHw = DmaCmd;
			ChanData->DmaCmdToHw = NULL;

			if (!ChanData->HoldDmaProg) {
				DmaProgBuf = (void *)DmaCmd->GeneratedDmaProg;
				if (DmaProgBuf)
					XDmaPs_BufPool_Free(ChanData->ProgBufPool,
							     DmaProgBuf);
				DmaCmd->GeneratedDmaProg = NULL;
			}

			if (InstPtr->FaultHandler)
				InstPtr->FaultHandler(Chan,
						      DmaCmd,
						      InstPtr->FaultRef);

		}
	}

}

/*****************************************************************************/
/**
*
* Set the done handler for a channel.
*
* @param	InstPtr is the DMA instance.
* @param	Channel is the channel number.
* @param	DoneHandler is the done interrupt handler.
* @param	CallbackRef is the callback reference data.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
int XDmaPs_SetDoneHandler(XDmaPs *InstPtr,
			   unsigned Channel,
			   XDmaPsDoneHandler DoneHandler,
			   void *CallbackRef)
{
	XDmaPs_ChannelData *ChanData;

	Xil_AssertNonvoid(InstPtr != NULL);

	if (Channel >= XDMAPS_CHANNELS_PER_DEV)
		return XST_FAILURE;


	ChanData = InstPtr->Chans + Channel;

	ChanData->DoneHandler = DoneHandler;
	ChanData->DoneRef = CallbackRef;

	return 0;
}

/*****************************************************************************/
/**
*
* Set the fault handler for a channel.
*
* @param	InstPtr is the DMA instance.
* @param	FaultHandler is the fault interrupt handler.
* @param	CallbackRef is the callback reference data.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
int XDmaPs_SetFaultHandler(XDmaPs *InstPtr,
			    XDmaPsFaultHandler FaultHandler,
			    void *CallbackRef)
{
	Xil_AssertNonvoid(InstPtr != NULL);

	InstPtr->FaultHandler = FaultHandler;
	InstPtr->FaultRef = CallbackRef;

	return XST_SUCCESS;
}



/****************************************************************************/
/**
* Construction function for DMAEND instruction. This function fills the program
* buffer with the constructed instruction.
*
* @param	DmaProg the DMA program buffer, it's the starting address for
*		the instruction being constructed
*
* @return 	The number of bytes for this instruction which is 1.
*
* @note		None.
*
*****************************************************************************/
__inline int XDmaPs_Instr_DMAEND(char *DmaProg)
{
	/*
	 * DMAEND encoding:
	 * 7 6 5 4 3 2 1 0
	 * 0 0 0 0 0 0 0 0
	 */
	*DmaProg = 0x0;

	return 1;
}

__inline void XDmaPs_Memcpy4(char *Dst, char *Src)
{
	*Dst = *Src;
	*(Dst + 1) = *(Src + 1);
	*(Dst + 2) = *(Src + 2);
	*(Dst + 3) = *(Src + 3);
}

/****************************************************************************/
/**
*
* Construction function for DMAGO instruction. This function fills the program
* buffer with the constructed instruction.
*
* @param	DmaProg is the DMA program buffer, it's the starting address
*		for the instruction being constructed
* @param	Cn is the Channel number, 0 - 7
* @param	Imm is 32-bit immediate number written to the Channel Program
*		Counter.
* @param	Ns is Non-secure flag. If Ns is 1, the DMA channel operates in
*		the Non-secure state. If Ns is 0, the execution depends on the
*		security state of the DMA manager:
*		DMA manager is in the Secure state, DMA channel operates in the
*		Secure state.
*		DMA manager is in the Non-secure state, DMAC aborts.
*
* @return	The number of bytes for this instruction which is 6.
*
* @note		None
*
*****************************************************************************/
__inline int XDmaPs_Instr_DMAGO(char *DmaProg, unsigned int Cn,
			       u32 Imm, unsigned int Ns)
{
	/*
	 * DMAGO encoding:
	 * 15 14 13 12 11 10 09 08 07 06 05 04 03 02 01 00
	 *  0  0  0  0  0 |cn[2:0]| 1  0  1  0  0  0 ns  0
	 *
	 * 47 ... 16
	 *  imm[32:0]
	 */
	*DmaProg = 0xA0 | ((Ns << 1) & 0x02);

	*(DmaProg + 1) = (u8)(Cn & 0x07);

	// *((u32 *)(DmaProg + 2)) = Imm;
	XDmaPs_Memcpy4(DmaProg + 2, (char *)&Imm);

	/* success */
	return 6;
}

/****************************************************************************/
/**
*
* Construction function for DMALD instruction. This function fills the program
* buffer with the constructed instruction.
*
* @param	DmaProg the DMA program buffer, it's the starting address for the
*		instruction being constructed
*
* @return 	The number of bytes for this instruction which is 1.
*
* @note		None.
*
*****************************************************************************/
__inline int XDmaPs_Instr_DMALD(char *DmaProg)
{
	/*
	 * DMALD encoding
	 * 7 6 5 4 3 2 1  0
	 * 0 0 0 0 0 1 bs x
	 *
	 * Note: this driver doesn't support conditional load or store,
	 * so the bs bit is 0 and x bit is 0.
	 */
	*DmaProg = 0x04;
	return 1;
}

/****************************************************************************/
/**
*
* Construction function for DMALP instruction. This function fills the program
* buffer with the constructed instruction.
*
* @param	DmaProg is the DMA program buffer, it's the starting address
*		for the instruction being constructed
* @param	Lc is the Loop counter register, can either be 0 or 1.
* @param	LoopIterations: the number of interations, LoopInterations - 1
*		will be encoded in the DMALP instruction.
*
* @return 	The number of bytes for this instruction which is 2.
*
* @note		None.
*
*****************************************************************************/
__inline int XDmaPs_Instr_DMALP(char *DmaProg, unsigned Lc,
			       unsigned LoopIterations)
{
	/*
	 * DMALP encoding
	 * 15   ...   8 7 6 5 4 3 2 1  0
	 * | iter[7:0] |0 0 1 0 0 0 lc 0
	 */
	*DmaProg = (u8)(0x20 | ((Lc & 1) << 1));
	*(DmaProg + 1) = (u8)(LoopIterations - 1);
	return 2;
}

/****************************************************************************/
/**
*
* Construction function for DMALPEND instruction. This function fills the
* program buffer with the constructed instruction.
*
* @param	DmaProg is the DMA program buffer, it's the starting address
*		for the instruction being constructed
* @param	BodyStart is the starting address of the loop body. It is used
* 		to calculate the bytes of backward jump.
* @param	Lc is the Loop counter register, can either be 0 or 1.
*
* @return 	The number of bytes for this instruction which is 2.
*
* @note	None.
*
*****************************************************************************/
__inline int XDmaPs_Instr_DMALPEND(char *DmaProg, char *BodyStart, unsigned Lc)
{
	/*
	 * DMALPEND encoding
	 * 15       ...        8 7 6 5 4  3 2  1  0
	 * | backward_jump[7:0] |0 0 1 nf 1 lc bs x
	 *
	 * lc: loop counter
	 * nf is for loop forever. The driver does not support loop forever,
	 * so nf is 1.
	 * The driver does not support conditional LPEND, so bs is 0, x is 0.
	 */
	*DmaProg = 0x38 | ((Lc & 1) << 2);
	*(DmaProg + 1) = (u8)(DmaProg - BodyStart);

	return 2;
}

/*
 * Register number for the DMAMOV instruction
 */
#define XDMAPS_MOV_SAR 0x0
#define XDMAPS_MOV_CCR 0x1
#define XDMAPS_MOV_DAR 0x2

/****************************************************************************/
/**
*
* Construction function for DMAMOV instruction. This function fills the
* program buffer with the constructed instruction.
*
* @param	DmaProg is the DMA program buffer, it's the starting address
*		for the instruction being constructed
* @param	Rd is the register id, 0 for SAR, 1 for CCR, and 2 for DAR
* @param	Imm is the 32-bit immediate number
*
* @return 	The number of bytes for this instruction which is 6.
*
* @note		None.
*
*****************************************************************************/
__inline int XDmaPs_Instr_DMAMOV(char *DmaProg, unsigned Rd, u32 Imm)
{
	/*
	 * DMAMOV encoding
	 * 15 4 3 2 1 10 ... 8 7 6 5 4 3 2 1 0
	 *  0 0 0 0 0 |rd[2:0]|1 0 1 1 1 1 0 0
	 *
	 * 47 ... 16
	 *  imm[32:0]
	 *
	 * rd: b000 for SAR, b001 CCR, b010 DAR
	 */
	*DmaProg = 0xBC;
	*(DmaProg + 1) = Rd & 0x7;
	// *((u32 *)(DmaProg + 2)) = Imm;
	XDmaPs_Memcpy4(DmaProg + 2, (char *)&Imm);

	return 6;
}

/****************************************************************************/
/**
*
* Construction function for DMANOP instruction. This function fills the
* program buffer with the constructed instruction.
*
* @param	DmaProg is the DMA program buffer, it's the starting address
*		for the instruction being constructed
* @return 	The number of bytes for this instruction which is 1.
*
* @note		None.
*
*****************************************************************************/
__inline int XDmaPs_Instr_DMANOP(char *DmaProg)
{
	/*
	 * DMANOP encoding
	 * 7 6 5 4 3 2 1 0
	 * 0 0 0 1 1 0 0 0
	 */
	*DmaProg = 0x18;
	return 1;
}

/****************************************************************************/
/**
*
* Construction function for DMARMB instruction. This function fills the
* program buffer with the constructed instruction.
*
* @param	DmaProg is the DMA program buffer, it's the starting address
*		for the instruction being constructed
*
* @return 	The number of bytes for this instruction which is 1.
*
* @note		None.
*
*****************************************************************************/
__inline int XDmaPs_Instr_DMARMB(char *DmaProg)
{
	/*
	 * DMARMB encoding
	 * 7 6 5 4 3 2 1 0
	 * 0 0 0 1 0 0 1 0
	 */
	*DmaProg = 0x12;
	return 1;
}

/****************************************************************************/
/**
*
* Construction function for DMASEV instruction. This function fills the
* program buffer with the constructed instruction.
*
* @param	DmaProg is the DMA program buffer, it's the starting address
*		for the instruction being constructed
* @param	EventNumber is the Event number to signal.
*
* @return 	The number of bytes for this instruction which is 2.
*
* @note		None.
*
*****************************************************************************/
__inline int XDmaPs_Instr_DMASEV(char *DmaProg, unsigned int EventNumber)
{
	/*
	 * DMASEV encoding
	 * 15 4 3 2 1  10 9 8 7 6 5 4 3 2 1 0
	 * |event[4:0]| 0 0 0 0 0 1 1 0 1 0 0
	 */
	*DmaProg = 0x34;
	*(DmaProg + 1) = (u8)(EventNumber << 3);

	return 2;
}


/****************************************************************************/
/**
*
* Construction function for DMAST instruction. This function fills the
* program buffer with the constructed instruction.
*
* @param	DmaProg is the DMA program buffer, it's the starting address
*		for the instruction being constructed
*
* @return 	The number of bytes for this instruction which is 1.
*
* @note		None.
*
*****************************************************************************/
__inline int XDmaPs_Instr_DMAST(char *DmaProg)
{
	/*
	 * DMAST encoding
	 * 7 6 5 4 3 2 1  0
	 * 0 0 0 0 1 0 bs x
	 *
	 * Note: this driver doesn't support conditional load or store,
	 * so the bs bit is 0 and x bit is 0.
	 */
	*DmaProg = 0x08;
	return 1;
}


/****************************************************************************/
/**
*
* Construction function for DMAWMB instruction. This function fills the
* program buffer with the constructed instruction.
*
* @param	DmaProg is the DMA program buffer, it's the starting address
*		for the instruction being constructed
*
* @return 	The number of bytes for this instruction which is 1.
*
* @note		None.
*
*****************************************************************************/
__inline int XDmaPs_Instr_DMAWMB(char *DmaProg)
{
	/*
	 * DMAWMB encoding
	 * 7 6 5 4 3 2 1 0
	 * 0 0 0 1 0 0 1 0
	 */
	*DmaProg = 0x13;
	return 1;
}

/****************************************************************************/
/**
*
* Conversion function from the endian swap size to the bit encoding of the CCR
*
* @param	EndianSwapSize is the endian swap size, in terms of bits, it
*		could be 8, 16, 32, 64, or 128(We are using DMA assembly syntax)
*
* @return	The endian swap size bit encoding for the CCR.
*
* @note	None.
*
*****************************************************************************/
__inline unsigned XDmaPs_ToEndianSwapSizeBits(unsigned int EndianSwapSize)
{
	switch (EndianSwapSize) {
	case 0:
	case 8:
		return 0;
	case 16:
		return 1;
	case 32:
		return 2;
	case 64:
		return 3;
	case 128:
		return 4;
	default:
		return 0;
	}

}

/****************************************************************************/
/**
*
* Conversion function from the burst size to the bit encoding of the CCR
*
* @param	BurstSize is the burst size. It's the data width.
*		In terms of bytes, it could be 1, 2, 4, 8, 16, 32, 64, or 128.
*		It must be no larger than the bus width.
*		(We are using DMA assembly syntax.)
*
* @note		None.
*
*****************************************************************************/
__inline unsigned XDmaPs_ToBurstSizeBits(unsigned BurstSize)
{
	switch (BurstSize) {
	case 1:
		return 0;
	case 2:
		return 1;
	case 4:
		return 2;
	case 8:
		return 3;
	case 16:
		return 4;
	case 32:
		return 5;
	case 64:
		return 6;
	case 128:
		return 7;
	default:
		return 0;
	}
}


/****************************************************************************/
/**
*
* Conversion function from PL330 bus transfer descriptors to CCR value. All the
* values passed to the functions are in terms of assembly languages, not in
* terms of the register bit encoding.
*
* @param	ChanCtrl is the Instance of XDmaPs_ChanCtrl.
*
* @return	The 32-bit CCR value.
*
* @note		None.
*
*****************************************************************************/
u32 XDmaPs_ToCCRValue(XDmaPs_ChanCtrl *ChanCtrl)
{
	/*
	 * Channel Control Register encoding
	 * [31:28] - endian_swap_size
	 * [27:25] - dst_cache_ctrl
	 * [24:22] - dst_prot_ctrl
	 * [21:18] - dst_burst_len
	 * [17:15] - dst_burst_size
	 * [14]    - dst_inc
	 * [13:11] - src_cache_ctrl
	 * [10:8] - src_prot_ctrl
	 * [7:4]  - src_burst_len
	 * [3:1]  - src_burst_size
	 * [0]     - src_inc
	 */

	unsigned es =
		XDmaPs_ToEndianSwapSizeBits(ChanCtrl->EndianSwapSize);

	unsigned dst_burst_size =
		XDmaPs_ToBurstSizeBits(ChanCtrl->DstBurstSize);
	unsigned dst_burst_len = (ChanCtrl->DstBurstLen - 1) & 0x0F;
	unsigned dst_cache_ctrl = (ChanCtrl->DstCacheCtrl & 0x03)
		| ((ChanCtrl->DstCacheCtrl & 0x08) >> 1);
	unsigned dst_prot_ctrl = ChanCtrl->DstProtCtrl & 0x07;
	unsigned dst_inc_bit = ChanCtrl->DstInc & 1;

	unsigned src_burst_size =
		XDmaPs_ToBurstSizeBits(ChanCtrl->SrcBurstSize);
	unsigned src_burst_len = (ChanCtrl->SrcBurstLen - 1) & 0x0F;
	unsigned src_cache_ctrl = (ChanCtrl->SrcCacheCtrl & 0x03)
		| ((ChanCtrl->SrcCacheCtrl & 0x08) >> 1);
	unsigned src_prot_ctrl = ChanCtrl->SrcProtCtrl & 0x07;
	unsigned src_inc_bit = ChanCtrl->SrcInc & 1;

	u32 ccr_value = (es << 28)
		| (dst_cache_ctrl << 25)
		| (dst_prot_ctrl << 22)
		| (dst_burst_len << 18)
		| (dst_burst_size << 15)
		| (dst_inc_bit << 14)
		| (src_cache_ctrl << 11)
		| (src_prot_ctrl << 8)
		| (src_burst_len << 4)
		| (src_burst_size << 1)
		| (src_inc_bit);

	return ccr_value;
}

/****************************************************************************/
/**
* Construct a loop with only DMALD and DMAST as the body using loop counter 0.
* The function also makes sure the loop body and the lpend is in the same
* cache line.
*
* @param	DmaProgStart is the very start address of the DMA program.
*		This is used to calculate whether the loop is in a cache line.
* @param	CacheLength is the icache line length, in terms of bytes.
*		If it's zero, the performance enhancement feature will be
*		turned off.
* @param	DmaProgLoopStart The starting address of the loop (DMALP).
* @param	LoopCount The inner loop count. Loop count - 1 will be used to
* 		initialize the loop counter.
*
* @return	The number of bytes the loop has.
*
* @note		None.
*
*****************************************************************************/
int XDmaPs_ConstructSingleLoop(char *DmaProgStart,
				int CacheLength,
				char *DmaProgLoopStart,
				int LoopCount)
{
	int CacheStartOffset;
	int CacheEndOffset;
	int NumNops;
	char *DmaProgBuf = DmaProgLoopStart;

	DmaProgBuf += XDmaPs_Instr_DMALP(DmaProgBuf, 0, LoopCount);

	if (CacheLength > 0) {
		/*
		 * the CacheLength > 0 switch is ued to turn on/off nop
		 * insertion
		 */
		CacheStartOffset = DmaProgBuf - DmaProgStart;
		CacheEndOffset = CacheStartOffset + 3;

		/*
		 * check whether the body and lpend fit in one cache line
		 */
		if (CacheStartOffset / CacheLength
		    != CacheEndOffset / CacheLength) {
			/* insert the nops */
			NumNops = CacheLength
				- CacheStartOffset % CacheLength;
			while (NumNops--) {
				DmaProgBuf +=
					XDmaPs_Instr_DMANOP(DmaProgBuf);
			}
		}
	}

	DmaProgBuf += XDmaPs_Instr_DMALD(DmaProgBuf);
	DmaProgBuf += XDmaPs_Instr_DMAST(DmaProgBuf);
	DmaProgBuf += XDmaPs_Instr_DMALPEND(DmaProgBuf,
					     DmaProgBuf - 2, 0);

	return DmaProgBuf - DmaProgLoopStart;
}

/****************************************************************************/
/**
* Construct a nested loop with only DMALD and DMAST in the inner loop body.
* It uses loop counter 1 for the outer loop and loop counter 0 for the
* inner loop.
*
* @param	DmaProgStart is the very start address of the DMA program.
*		This is used to calculate whether the loop is in a cache line.
* @param	CacheLength is the icache line length, in terms of bytes.
*		If it's zero, the performance enhancement feature will be
*		turned off.
* @param	DmaProgLoopStart The starting address of the loop (DMALP).
* @param	LoopCountOuter The outer loop count. Loop count - 1 will be
*		used to initialize the loop counter.
* @param	LoopCountInner The inner loop count. Loop count - 1 will be
*		used to initialize the loop counter.
*
* @return	The number byes the nested loop program has.
*
* @note		None.
*
*****************************************************************************/
int XDmaPs_ConstructNestedLoop(char *DmaProgStart,
				int CacheLength,
				char *DmaProgLoopStart,
				unsigned int LoopCountOuter,
				unsigned int LoopCountInner)
{
	int CacheStartOffset;
	int CacheEndOffset;
	int NumNops;
	char *InnerLoopStart;
	char *DmaProgBuf = DmaProgLoopStart;

	DmaProgBuf += XDmaPs_Instr_DMALP(DmaProgBuf, 1, LoopCountOuter);
	InnerLoopStart = DmaProgBuf;

	if (CacheLength > 0) {
		/*
		 * the CacheLength > 0 switch is ued to turn on/off nop
		 * insertion
		 */
		if (CacheLength < 8) {
			/*
			 * if the cache line is too small to fit both loops
			 * just align the inner loop
			 */
			DmaProgBuf +=
				XDmaPs_ConstructSingleLoop(DmaProgStart,
							    CacheLength,
							    DmaProgBuf,
							    LoopCountInner);
			/* outer loop end */
			DmaProgBuf +=
				XDmaPs_Instr_DMALPEND(DmaProgBuf,
						       InnerLoopStart,
						       1);

			/*
			 * the nested loop is constructed for
			 * smaller cache line
			 */
			return DmaProgBuf - DmaProgLoopStart;
		}

		/*
		 * Now let's handle the case where a cache line can
		 * fit the nested loops.
		 */
		CacheStartOffset = DmaProgBuf - DmaProgStart;
		CacheEndOffset = CacheStartOffset + 7;

		/*
		 * check whether the body and lpend fit in one cache line
		 */
		if (CacheStartOffset / CacheLength
		    != CacheEndOffset / CacheLength) {
			/* insert the nops */
			NumNops = CacheLength
				- CacheStartOffset % CacheLength;
			while (NumNops--) {
				DmaProgBuf +=
					XDmaPs_Instr_DMANOP(DmaProgBuf);
			}
		}
	}

	/* insert the inner DMALP */
	DmaProgBuf += XDmaPs_Instr_DMALP(DmaProgBuf, 0, LoopCountInner);

	/* DMALD and DMAST instructions */
	DmaProgBuf += XDmaPs_Instr_DMALD(DmaProgBuf);
	DmaProgBuf += XDmaPs_Instr_DMAST(DmaProgBuf);

	/* inner DMALPEND */
	DmaProgBuf += XDmaPs_Instr_DMALPEND(DmaProgBuf,
					     DmaProgBuf - 2, 0);
	/* outer DMALPEND */
	DmaProgBuf += XDmaPs_Instr_DMALPEND(DmaProgBuf,
					     InnerLoopStart, 1);

	/* return the number of bytes */
	return DmaProgBuf - DmaProgLoopStart;
}

/*
 * [31:28] endian_swap_size	b0000
 * [27:25] dst_cache_ctrl	b000
 * [24:22] dst_prot_ctrl	b000
 * [21:18] dst_burst_len	b0000
 * [17:15] dst_burst_size	b000
 * [14]    dst_inc		b0
 * [27:25] src_cache_ctrl	b000
 * [24:22] src_prot_ctrl	b000
 * [21:18] src_burst_len	b0000
 * [17:15] src_burst_size	b000
 * [14]    src_inc		b0
 */
#define XDMAPS_CCR_SINGLE_BYTE	(0x0)
#define XDMAPS_CCR_M2M_SINGLE_BYTE	((0x1 << 14) | 0x1)


/****************************************************************************/
/**
*
* Construct the DMA program based on the descriptions of the DMA transfer.
* The function handles memory to memory DMA transfers.
* It also handles unalgined head and small amount of residue tail.
*
* @param	Channel DMA channel number
* @param	Cmd is the DMA command.
* @param	CacheLength is the icache line length, in terms of bytes.
*		If it's zero, the performance enhancement feature will be
*		turned off.
*
* @returns	The number of bytes for the program.
*
* @note		None.
*
*****************************************************************************/
static int XDmaPs_BuildDmaProg(unsigned Channel, XDmaPs_Cmd *Cmd,
				unsigned CacheLength)
{
	/*
	 * unpack arguments
	 */
	char *DmaProgBuf = (char *)Cmd->GeneratedDmaProg;
	unsigned DevChan = Channel;
	unsigned long DmaLength = Cmd->BD.Length;
	u32 SrcAddr = Cmd->BD.SrcAddr;

	unsigned SrcInc = Cmd->ChanCtrl.SrcInc;
	u32 DstAddr = Cmd->BD.DstAddr;
	unsigned DstInc = Cmd->ChanCtrl.DstInc;

	char *DmaProgStart = DmaProgBuf;

	unsigned int BurstBytes;
	unsigned int LoopCount;
	unsigned int LoopCount1 = 0;
	unsigned int LoopResidue = 0;
	unsigned int TailBytes;
	unsigned int TailWords;
	int DmaProgBytes;
	u32 CCRValue;
	unsigned int Unaligned;
	unsigned int UnalignedCount;
	unsigned int MemBurstSize = 1;
	u32 MemAddr = 0;
	unsigned int Index;
	unsigned int SrcUnaligned = 0;
	unsigned int DstUnaligned = 0;

	XDmaPs_ChanCtrl *ChanCtrl;
	XDmaPs_ChanCtrl WordChanCtrl;
	static XDmaPs_ChanCtrl Mem2MemByteCC;

	Mem2MemByteCC.EndianSwapSize = 0;
	Mem2MemByteCC.DstCacheCtrl = 0;
	Mem2MemByteCC.DstProtCtrl = 0;
	Mem2MemByteCC.DstBurstLen = 1;
	Mem2MemByteCC.DstBurstSize = 1;
	Mem2MemByteCC.DstInc = 1;
	Mem2MemByteCC.SrcCacheCtrl = 0;
	Mem2MemByteCC.SrcProtCtrl = 0;
	Mem2MemByteCC.SrcBurstLen = 1;
	Mem2MemByteCC.SrcBurstSize = 1;
	Mem2MemByteCC.SrcInc = 1;

	ChanCtrl = &Cmd->ChanCtrl;

	/* insert DMAMOV for SAR and DAR */
	DmaProgBuf += XDmaPs_Instr_DMAMOV(DmaProgBuf,
					   XDMAPS_MOV_SAR,
					   SrcAddr);
	DmaProgBuf += XDmaPs_Instr_DMAMOV(DmaProgBuf,
					 XDMAPS_MOV_DAR,
					 DstAddr);


	if (ChanCtrl->SrcInc)
		SrcUnaligned = SrcAddr % ChanCtrl->SrcBurstSize;

	if (ChanCtrl->DstInc)
		DstUnaligned = DstAddr % ChanCtrl->DstBurstSize;

	if ((SrcUnaligned && DstInc) || (DstUnaligned && SrcInc)) {
		ChanCtrl = &Mem2MemByteCC;
	}

	if (ChanCtrl->SrcInc) {
		MemBurstSize = ChanCtrl->SrcBurstSize;
		MemAddr = SrcAddr;

	} else if (ChanCtrl->DstInc) {
		MemBurstSize = ChanCtrl->DstBurstSize;
		MemAddr = DstAddr;
	}

	/* check whether the head is aligned or not */
	Unaligned = MemAddr % MemBurstSize;

	if (Unaligned) {
		/* if head is unaligned, transfer head in bytes */
		UnalignedCount = MemBurstSize - Unaligned;
		CCRValue = XDMAPS_CCR_SINGLE_BYTE
			| (SrcInc & 1)
			| ((DstInc & 1) << 14);

		DmaProgBuf += XDmaPs_Instr_DMAMOV(DmaProgBuf,
						   XDMAPS_MOV_CCR,
						   CCRValue);

		for (Index = 0; Index < UnalignedCount; Index++) {
			DmaProgBuf += XDmaPs_Instr_DMALD(DmaProgBuf);
			DmaProgBuf += XDmaPs_Instr_DMAST(DmaProgBuf);
		}

		DmaLength -= UnalignedCount;
	}

	/* now the burst transfer part */
	CCRValue = XDmaPs_ToCCRValue(ChanCtrl);
	DmaProgBuf += XDmaPs_Instr_DMAMOV(DmaProgBuf,
					   XDMAPS_MOV_CCR,
					   CCRValue);

	BurstBytes = ChanCtrl->SrcBurstSize * ChanCtrl->SrcBurstLen;

	LoopCount = DmaLength / BurstBytes;
	TailBytes = DmaLength % BurstBytes;

	/*
	 * the loop count register is 8-bit wide, so if we need
	 * a larger loop, we need to have nested loops
	 */
	if (LoopCount > 256) {
		LoopCount1 = LoopCount / 256;
		if (LoopCount1 > 256) {
			xil_printf("DMA operation cannot fit in a 2-level "
				   "loop for channel %d, please reduce the "
				   "DMA length or increase the burst size or "
				   "length",
				   Channel);
			return 0;
		}
		LoopResidue = LoopCount % 256;

		if (LoopCount1 > 1)
			DmaProgBuf +=
				XDmaPs_ConstructNestedLoop(DmaProgStart,
							    CacheLength,
							    DmaProgBuf,
							    LoopCount1,
							    256);
		else
			DmaProgBuf +=
				XDmaPs_ConstructSingleLoop(DmaProgStart,
							    CacheLength,
							    DmaProgBuf,
							    256);

		/* there will be some that cannot be covered by
		 * nested loops
		 */
		LoopCount = LoopResidue;
	}

	if (LoopCount > 0) {
		DmaProgBuf += XDmaPs_ConstructSingleLoop(DmaProgStart,
							    CacheLength,
							    DmaProgBuf,
							    LoopCount);
	}

	if (TailBytes) {
		/* handle the tail */
		TailWords = TailBytes / MemBurstSize;
		TailBytes = TailBytes % MemBurstSize;

		if (TailWords) {
			WordChanCtrl = *ChanCtrl;
			/*
			 * if we can transfer the tail in words, we will
			 * transfer words as much as possible
			 */
			WordChanCtrl.SrcBurstSize = MemBurstSize;
			WordChanCtrl.SrcBurstLen = 1;
			WordChanCtrl.DstBurstSize = MemBurstSize;
			WordChanCtrl.DstBurstLen = 1;


			/*
			 * the burst length is 1
			 */
			CCRValue = XDmaPs_ToCCRValue(&WordChanCtrl);

			DmaProgBuf +=
				XDmaPs_Instr_DMAMOV(DmaProgBuf,
						   XDMAPS_MOV_CCR,
						   CCRValue);
			DmaProgBuf +=
				XDmaPs_ConstructSingleLoop(DmaProgStart,
							    CacheLength,
							    DmaProgBuf,
							    TailWords);

		}

		if (TailBytes) {
			/*
			 * for the rest, we'll tranfer in bytes
			 */
			/*
			 * So far just to be safe, the tail bytes
			 * are transfered in a loop. We can optimize a little
			 * to perform a burst.
			 */
			CCRValue = XDMAPS_CCR_SINGLE_BYTE
				| (SrcInc & 1)
				| ((DstInc & 1) << 14);

			DmaProgBuf +=
				XDmaPs_Instr_DMAMOV(DmaProgBuf,
						   XDMAPS_MOV_CCR,
						   CCRValue);

			DmaProgBuf +=
				XDmaPs_ConstructSingleLoop(DmaProgStart,
							    CacheLength,
							    DmaProgBuf,
							    TailBytes);

		}
	}

	DmaProgBuf += XDmaPs_Instr_DMASEV(DmaProgBuf, DevChan);
	DmaProgBuf += XDmaPs_Instr_DMAEND(DmaProgBuf);

	DmaProgBytes = DmaProgBuf - DmaProgStart;

	Xil_DCacheFlushRange((u32)DmaProgStart, DmaProgBytes);

	return DmaProgBytes;

}


/****************************************************************************/
/**
*
* Generate a DMA program based for the DMA command, the buffer will be pointed
* by the GeneratedDmaProg field of the command.
*
* @param	InstPtr is then DMA instance.
* @param	Channel is the DMA channel number.
* @param	Cmd is the DMA command.
*
* @return	- XST_SUCCESS on success.
* 		- XST_FAILURE if it fails
*
* @note		None.
*
*****************************************************************************/
int XDmaPs_GenDmaProg(XDmaPs *InstPtr, unsigned int Channel, XDmaPs_Cmd *Cmd)
{
	void *Buf;
	int ProgLen;
	XDmaPs_ChannelData *ChanData;
	XDmaPs_ChanCtrl *ChanCtrl;

	Xil_AssertNonvoid(InstPtr != NULL);
	Xil_AssertNonvoid(Cmd != NULL);


	if (Channel > XDMAPS_CHANNELS_PER_DEV)
		return XST_FAILURE;

	ChanData = InstPtr->Chans + Channel;
	ChanCtrl = &Cmd->ChanCtrl;

	if (ChanCtrl->SrcBurstSize * ChanCtrl->SrcBurstLen
	    != ChanCtrl->DstBurstSize * ChanCtrl->DstBurstLen) {
		xil_printf("source burst_size * burst_len does not match "
			   "that of destination\r\n");
		return XST_FAILURE;
	}


	/*
	 * unaligned fixed address is not supported
	 */
	if (!ChanCtrl->SrcInc && Cmd->BD.SrcAddr % ChanCtrl->SrcBurstSize) {
		xil_printf("source address is fixed but is unaligned\r\n");
		return XST_FAILURE;
	}

	if (!ChanCtrl->DstInc && Cmd->BD.DstAddr % ChanCtrl->DstBurstSize) {
		xil_printf("destination address is fixed but is "
			   "unaligned\r\n");
		return XST_FAILURE;
	}

	Buf = XDmaPs_BufPool_Allocate(ChanData->ProgBufPool);
	if (Buf == NULL) {
		xil_printf("failed to allocate program buffer\r\n");
		return XST_FAILURE;
	}

	Cmd->GeneratedDmaProg = Buf;
	ProgLen = XDmaPs_BuildDmaProg(Channel, Cmd,
				       InstPtr->CacheLength);
	Cmd->GeneratedDmaProgLength = ProgLen;


#ifdef XDMAPS_DEBUG
	XDmaPs_Print_DmaProg(Cmd);
#endif

	if (ProgLen <= 0) {
		/* something wrong, release the buffer */
		XDmaPs_BufPool_Free(ChanData->ProgBufPool, Buf);
		Cmd->GeneratedDmaProgLength = 0;
		Cmd->GeneratedDmaProg = NULL;
		return XST_FAILURE;
	}

	return XST_SUCCESS;
}


/****************************************************************************/
/**
 * Free the DMA program buffer that is pointed by the GeneratedDmaProg field
 * of the command.
 *
 * @param	InstPtr is then DMA instance.
 * @param	Channel is the DMA channel number.
 * @param	Cmd is the DMA command.
 *
 * @return	XST_SUCCESS on success.
 * 		XST_FAILURE if there is any error.
 *
 * @note	None.
 *
 ****************************************************************************/
int XDmaPs_FreeDmaProg(XDmaPs *InstPtr, unsigned int Channel, XDmaPs_Cmd *Cmd)
{

	void *Buf;
	XDmaPs_ChannelData *ChanData;

	Xil_AssertNonvoid(InstPtr != NULL);
	Xil_AssertNonvoid(Cmd != NULL);

	if (Channel > XDMAPS_CHANNELS_PER_DEV)
		return XST_FAILURE;

	Buf = (void *)Cmd->GeneratedDmaProg;
	ChanData = InstPtr->Chans + Channel;

	if (Buf) {
		XDmaPs_BufPool_Free(ChanData->ProgBufPool, Buf);
		Cmd->GeneratedDmaProg = 0;
		Cmd->GeneratedDmaProgLength = 0;
	}

	return XST_SUCCESS;
}


/****************************************************************************/
/**
*
* Start a DMA command. The command can only be invoked when the channel
* is idle. The driver takes the command, generates DMA program if needed,
* then pass the program to DMAC to execute.
*
* @param	InstPtr is then DMA instance.
* @param	Channel is the DMA channel number.
* @param	Cmd is the DMA command.
* @param	HoldDmaProg is tag indicating whether the driver can release
* 		the allocated DMA buffer or not. If a user wants to examine the
* 		generated DMA program, the flag should be set to 1. After the
* 		DMA program is finished, a user needs to explicity free the
*		buffer.
*
* @return
*		- XST_SUCCESS on success
*		- XST_DEVICE_BUSY if DMA is busy
*		- XST_FAILURE on other failures
*
* @note		None.
*
****************************************************************************/
int XDmaPs_Start(XDmaPs *InstPtr, unsigned int Channel,
		  XDmaPs_Cmd *Cmd,
		  int HoldDmaProg)
{
	int Status;
	u32 DmaProg = 0;
	u32 Inten;

	Xil_AssertNonvoid(InstPtr != NULL);
	Xil_AssertNonvoid(Cmd != NULL);


	Cmd->DmaStatus = XST_FAILURE;

	if (XDmaPs_IsActive(InstPtr, Channel))
		return XST_DEVICE_BUSY;

	if (!Cmd->UserDmaProg && !Cmd->GeneratedDmaProg) {
		Status = XDmaPs_GenDmaProg(InstPtr, Channel, Cmd);
		if (Status)
			return XST_FAILURE;
	}

	InstPtr->Chans[Channel].HoldDmaProg = HoldDmaProg;

	if (Cmd->UserDmaProg)
		DmaProg = (u32)Cmd->UserDmaProg;
	else if (Cmd->GeneratedDmaProg)
		DmaProg = (u32)Cmd->GeneratedDmaProg;

	if (DmaProg) {
		/* enable the interrupt */
		Inten = XDmaPs_ReadReg(InstPtr->Config.BaseAddress,
					XDMAPS_INTEN_OFFSET);
		Inten |= 0x01 << Channel; /* set the correpsonding bit */
		XDmaPs_WriteReg(InstPtr->Config.BaseAddress,
				 XDMAPS_INTEN_OFFSET,
				 Inten);
		Inten = XDmaPs_ReadReg(InstPtr->Config.BaseAddress,
				XDMAPS_INTEN_OFFSET);

		InstPtr->Chans[Channel].DmaCmdToHw = Cmd;

		if (Cmd->ChanCtrl.SrcInc) {
			Xil_DCacheFlushRange(Cmd->BD.SrcAddr, Cmd->BD.Length);
		}
		if (Cmd->ChanCtrl.DstInc) {
			Xil_DCacheInvalidateRange(Cmd->BD.DstAddr,
					Cmd->BD.Length);
		}

		Status = XDmaPs_Exec_DMAGO(InstPtr->Config.BaseAddress,
					    Channel, DmaProg);
	}
	else {
		InstPtr->Chans[Channel].DmaCmdToHw = NULL;
		Status = XST_FAILURE;
	}

	return Status;
}

/****************************************************************************/
/**
*
* Checks  whether the DMA channel is active or idle.
*
* @param	InstPtr is the DMA instance.
* @param	Channel is the DMA channel number.
*
* @return	0: if the channel is idle
* 		1: otherwise
*
* @note		None.
*
*****************************************************************************/
int XDmaPs_IsActive(XDmaPs *InstPtr, unsigned int Channel)
{
	Xil_AssertNonvoid(InstPtr != NULL);

	/* Need to assert Channel is in range */
	if (Channel > XDMAPS_CHANNELS_PER_DEV)
		return  0;

	return InstPtr->Chans[Channel].DmaCmdToHw != NULL;
}



/****************************************************************************/
/**
*
* Allocate a buffer of the DMA program buffer from the pool.
*
* @param	Pool the DMA program pool.
*
* @return	The allocated buffer, NULL if there is any error.
*
* @note		None.
*
*****************************************************************************/
static void *XDmaPs_BufPool_Allocate(XDmaPs_ProgBuf *Pool)
{
	int Index;

	Xil_AssertNonvoid(Pool != NULL);

	for (Index = 0; Index < XDMAPS_MAX_CHAN_BUFS; Index++) {
		if (!Pool[Index].Allocated) {
			Pool[Index].Allocated = 1;
			return Pool[Index].Buf;
		}
	}

	return NULL;

}

/*****************************************************************************/
/**
*
* Driver done interrupt service routine for channel 0. We need this done ISR
* mainly because the driver needs to release the DMA program buffer.
* This is the one that connects the GIC
*
* @param	InstPtr is the DMA instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XDmaPs_DoneISR_0(XDmaPs *InstPtr)
{
	XDmaPs_DoneISR_n(InstPtr, 0);
}

/*****************************************************************************/
/**
*
* Driver done interrupt service routine for channel 1. We need this done ISR
* mainly because the driver needs to release the DMA program buffer.
* This is the one that connects the GIC
*
* @param	InstPtr is the DMA instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XDmaPs_DoneISR_1(XDmaPs *InstPtr)
{
	XDmaPs_DoneISR_n(InstPtr, 1);
}

/*****************************************************************************/
/**
*
* Driver done interrupt service routine for channel 2. We need this done ISR
* mainly because the driver needs to release the DMA program buffer.
* This is the one that connects the GIC
*
* @param	InstPtr is the DMA instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XDmaPs_DoneISR_2(XDmaPs *InstPtr)
{
	XDmaPs_DoneISR_n(InstPtr, 2);
}

/*****************************************************************************/
/**
*
* Driver done interrupt service routine for channel 3. We need this done ISR
* mainly because the driver needs to release the DMA program buffer.
* This is the one that connects the GIC
*
* @param	InstPtr is the DMA instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XDmaPs_DoneISR_3(XDmaPs *InstPtr)
{
	XDmaPs_DoneISR_n(InstPtr, 3);
}

/*****************************************************************************/
/**
*
* Driver done interrupt service routine for channel 4. We need this done ISR
* mainly because the driver needs to release the DMA program buffer.
* This is the one that connects the GIC
*
* @param	InstPtr is the DMA instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XDmaPs_DoneISR_4(XDmaPs *InstPtr)
{
	XDmaPs_DoneISR_n(InstPtr, 4);
}

/*****************************************************************************/
/**
*
* Driver done interrupt service routine for channel 5. We need this done ISR
* mainly because the driver needs to release the DMA program buffer.
* This is the one that connects the GIC
*
* @param	InstPtr is the DMA instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XDmaPs_DoneISR_5(XDmaPs *InstPtr)
{
	XDmaPs_DoneISR_n(InstPtr, 5);
}

/*****************************************************************************/
/**
*
* Driver done interrupt service routine for channel 6. We need this done ISR
* mainly because the driver needs to release the DMA program buffer.
* This is the one that connects the GIC
*
* @param	InstPtr is the DMA instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XDmaPs_DoneISR_6(XDmaPs *InstPtr)
{
	XDmaPs_DoneISR_n(InstPtr, 6);
}

/*****************************************************************************/
/**
*
* Driver done interrupt service routine for channel 7. We need this done ISR
* mainly because the driver needs to release the DMA program buffer.
* This is the one that connects the GIC
*
* @param	InstPtr is the DMA instance.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XDmaPs_DoneISR_7(XDmaPs *InstPtr)
{
	XDmaPs_DoneISR_n(InstPtr, 7);
}

#ifndef XDMAPS_MAX_WAIT
#define XDMAPS_MAX_WAIT 4000
#endif

/****************************************************************************/
/**
* Use the debug registers to kill the DMA thread.
*
* @param	BaseAddr is DMA device base address.
* @param	Channel is the DMA channel number.
* @param	Thread is Debug thread encoding.
* 		0: DMA manager thread, 1: DMA channel.
*
* @return	0 on success, -1 on time out
*
* @note		None.
*
*****************************************************************************/
static int XDmaPs_Exec_DMAKILL(u32 BaseAddr,
				unsigned int Channel,
				unsigned int Thread)
{
	u32 DbgInst0;
	int WaitCount;

	DbgInst0 = XDmaPs_DBGINST0(0, 0x01, Channel, Thread);

	/* wait while debug status is busy */
	WaitCount = 0;
	while ((XDmaPs_ReadReg(BaseAddr, XDMAPS_DBGSTATUS_OFFSET)
	       & XDMAPS_DBGSTATUS_BUSY)
	       && (WaitCount < XDMAPS_MAX_WAIT))
		WaitCount++;

	if (WaitCount >= XDMAPS_MAX_WAIT) {
		/* wait time out */
		xil_printf("PL330 device at %x debug status busy time out\n",
		       BaseAddr);

		return -1;
	}

	/* write debug instruction 0 */
	XDmaPs_WriteReg(BaseAddr, XDMAPS_DBGINST0_OFFSET, DbgInst0);

	XDmaPs_WriteReg(BaseAddr, XDMAPS_DBGINST1_OFFSET, 0);


	/* run the command in DbgInst0 and DbgInst1 */
	XDmaPs_WriteReg(BaseAddr, XDMAPS_DBGCMD_OFFSET, 0);

	return 0;
}

/****************************************************************************/
/**
*
*
* Free a buffer of the DMA program buffer.
* @param	Pool the DMA program pool.
* @param	Buf the DMA program buffer to be release.
*
* @return	None
*
* @note		None.
*
*****************************************************************************/
static void XDmaPs_BufPool_Free(XDmaPs_ProgBuf *Pool, void *Buf)
{
	int Index;
	Xil_AssertVoid(Pool != NULL);

	for (Index = 0; Index < XDMAPS_MAX_CHAN_BUFS; Index++) {
		if (Pool[Index].Buf == Buf) {
			if (Pool[Index].Allocated) {
				Pool[Index].Allocated = 0;
			}
		}
	}
}

/*****************************************************************************/
/**
* XDmaPs_Exec_DMAGO - Execute the DMAGO to start a channel.
*
* @param	BaseAddr PL330 device base address
* @param	Channel Channel number for the device
* @param	DmaProg DMA program starting address, this should be DMA address
*
* @return	0 on success, -1 on time out
*
* @note		None.
*
****************************************************************************/
static int XDmaPs_Exec_DMAGO(u32 BaseAddr, unsigned int Channel, u32 DmaProg)
{
	char DmaGoProg[8];
	u32 DbgInst0;
	u32 DbgInst1;

	int WaitCount;

	XDmaPs_Instr_DMAGO(DmaGoProg, Channel, DmaProg, 0);

	DbgInst0 = XDmaPs_DBGINST0(*(DmaGoProg + 1), *DmaGoProg, 0, 0);
	DbgInst1 = (u32)DmaProg;

	/* wait while debug status is busy */
	WaitCount = 0;
	while ((XDmaPs_ReadReg(BaseAddr, XDMAPS_DBGSTATUS_OFFSET)
	       & XDMAPS_DBGSTATUS_BUSY)
	       && (WaitCount < XDMAPS_MAX_WAIT)) {

		WaitCount++;
	}

	if (WaitCount >= XDMAPS_MAX_WAIT) {
		xil_printf("PL330 device at %x debug status busy time out\r\n",
			   BaseAddr);
		return -1;
	}

	/* write debug instruction 0 */
	XDmaPs_WriteReg(BaseAddr, XDMAPS_DBGINST0_OFFSET, DbgInst0);
	/* write debug instruction 1 */
	XDmaPs_WriteReg(BaseAddr, XDMAPS_DBGINST1_OFFSET, DbgInst1);


	/* wait while the DMA Manager is busy */
	WaitCount = 0;
	while ((XDmaPs_ReadReg(BaseAddr,
				XDMAPS_DS_OFFSET) & XDMAPS_DS_DMA_STATUS)
	       != XDMAPS_DS_DMA_STATUS_STOPPED
	       && WaitCount <= XDMAPS_MAX_WAIT) {
		WaitCount++;
	}

	if (WaitCount >= XDMAPS_MAX_WAIT) {
		xil_printf("PL330 device at %x debug status busy time out\r\n",
			   BaseAddr);
		return -1;
	}

	/* run the command in DbgInst0 and DbgInst1 */
	XDmaPs_WriteReg(BaseAddr, XDMAPS_DBGCMD_OFFSET, 0);

	return 0;
}


/****************************************************************************/
/**
*
* It's the generic Done ISR.
* @param	InstPtr is the DMA instance.
* @param	Channel is the DMA channel numer.
*
* @return	None.*
*
* @note		None.
*
*****************************************************************************/
static void XDmaPs_DoneISR_n(XDmaPs *InstPtr, unsigned Channel)
{

	void *DmaProgBuf;
	XDmaPs_ChannelData *ChanData;
	XDmaPs_Cmd *DmaCmd;
	//u32 Value;

	ChanData = InstPtr->Chans + Channel;

	/*Value = XDmaPs_ReadReg(InstPtr->Config.BaseAddress,
			XDMAPS_INTSTATUS_OFFSET);*/

	/* clear the interrupt status */
	XDmaPs_WriteReg(InstPtr->Config.BaseAddress,
			XDMAPS_INTCLR_OFFSET,
			1 << ChanData->ChanId);

	/*Value = XDmaPs_ReadReg(InstPtr->Config.BaseAddress,
			XDMAPS_INTSTATUS_OFFSET);*/


	if ((DmaCmd = ChanData->DmaCmdToHw)) {
		if (!ChanData->HoldDmaProg) {
			DmaProgBuf = (void *)DmaCmd->GeneratedDmaProg;
			if (DmaProgBuf)
				XDmaPs_BufPool_Free(ChanData->ProgBufPool,
						     DmaProgBuf);
			DmaCmd->GeneratedDmaProg = NULL;
		}

		DmaCmd->DmaStatus = 0;
		ChanData->DmaCmdToHw = NULL;
		ChanData->DmaCmdFromHw = DmaCmd;

		if (ChanData->DoneHandler)
			ChanData->DoneHandler(Channel, DmaCmd,
					      ChanData->DoneRef);
	}

}


/****************************************************************************/
/**
* Prints the content of the buffer in bytes
* @param	Buf is the buffer.
* @param	Length is the length of the DMA program.
*
* @return	None.
*
* @note		None.
****************************************************************************/
static void XDmaPs_Print_DmaProgBuf(char *Buf, int Length)
{
	int Index;
	for (Index = 0; Index < Length; Index++)
		xil_printf("[%x] %x\r\n", Index, Buf[Index]);

}
/****************************************************************************/
/**
* Print the Dma Prog Contents.
*
* @param	Cmd is the command buffer.
*
* @return	None.
*
* @note		None.
*
*****************************************************************************/
 void XDmaPs_Print_DmaProg(XDmaPs_Cmd *Cmd)
{
	if (Cmd->GeneratedDmaProg && Cmd->GeneratedDmaProgLength) {
		xil_printf("Generated DMA program (%d):\r\n",
			   Cmd->GeneratedDmaProgLength);
		XDmaPs_Print_DmaProgBuf((char *)Cmd->GeneratedDmaProg,
					 Cmd->GeneratedDmaProgLength);
	}

	if (Cmd->UserDmaProg && Cmd->UserDmaProgLength) {
		xil_printf("User defined DMA program (%d):\r\n",
			   Cmd->UserDmaProgLength);
		XDmaPs_Print_DmaProgBuf((char *)Cmd->UserDmaProg,
					 Cmd->UserDmaProgLength);
	}
}


/** @} */
