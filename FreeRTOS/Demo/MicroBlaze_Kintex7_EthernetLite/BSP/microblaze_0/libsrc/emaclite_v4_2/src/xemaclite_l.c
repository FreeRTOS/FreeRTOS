/******************************************************************************
*
* Copyright (C) 2004 - 2014 Xilinx, Inc.  All rights reserved.
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
* @file xemaclite_l.c
* @addtogroup emaclite_v4_1
* @{
*
* This file contains the minimal, polled functions to send and receive Ethernet
* frames.
*
* Refer to xemaclite.h for more details.
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who  Date     Changes
* ----- ---- -------- -----------------------------------------------
* 1.00a ecm  06/01/02 First release
* 1.01a ecm  03/31/04 Additional functionality and the _AlignedRead and
*                     _AlignedWrite functions.
* 1.11a mta  03/21/07 Updated to new coding style
* 2.01a ktn  07/20/09 Updated the XEmacLite_AlignedWrite and
*                     XEmacLite_AlignedRead functions to use volatile
*                     variables so that they are not optimized.
* 3.00a ktn  10/22/09 The macros have been renamed to remove _m from the name.
* 4.1   nsk  07/13/15 Added Length check in XEmacLite_AlignedWrite function
*                     to avoid extra write operation (CR 843707).
* 4.2   sk   11/10/15 Used UINTPTR instead of u32 for Baseaddress CR# 867425.
*                     Changed the prototypes of XEmacLite_SendFrame,
*                     XEmacLite_RecvFrame, XEmacLite_AlignedWrite,
*                     XEmacLite_AlignedRead APIs.
*
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/

#include "xil_types.h"
#include "xil_assert.h"
#include "xemaclite_l.h"
#include "xemaclite_i.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/
void XEmacLite_AlignedWrite(void *SrcPtr, UINTPTR *DestPtr, unsigned ByteCount);
void XEmacLite_AlignedRead(UINTPTR *SrcPtr, void *DestPtr, unsigned ByteCount);

/************************** Variable Definitions *****************************/

/*****************************************************************************/
/**
*
* Send an Ethernet frame. The size is the total frame size, including header.
* This function blocks waiting for the frame to be transmitted.
*
* @param 	BaseAddress is the base address of the device
* @param 	FramePtr is a pointer to frame
* @param 	ByteCount is the size, in bytes, of the frame
*
* @return	None.
*
* @note
*
* This function call is blocking in nature, i.e. it will wait until the
* frame is transmitted. This function can hang and not exit if the
* hardware is not configured properly.
*
* If the ping buffer is the destination of the data, the argument should be
* DeviceAddress + XEL_TXBUFF_OFFSET.
* If the pong buffer is the destination of the data, the argument should be
* DeviceAddress + XEL_TXBUFF_OFFSET + XEL_BUFFER_OFFSET.
* The function does not take the different buffers into consideration.
*
******************************************************************************/
void XEmacLite_SendFrame(UINTPTR BaseAddress, u8 *FramePtr, unsigned ByteCount)
{
	u32 Register;

	/*
	 * Write data to the EmacLite
	 */
	XEmacLite_AlignedWrite(FramePtr, (UINTPTR *) (BaseAddress), ByteCount);

	/*
	 * The frame is in the buffer, now send it
	 */
	XEmacLite_WriteReg(BaseAddress,  XEL_TPLR_OFFSET,
				(ByteCount & (XEL_TPLR_LENGTH_MASK_HI |
				XEL_TPLR_LENGTH_MASK_LO)));


	Register = XEmacLite_GetTxStatus(BaseAddress);
	XEmacLite_SetTxStatus(BaseAddress, Register | XEL_TSR_XMIT_BUSY_MASK);

	/*
	 * Loop on the status waiting for the transmit to be complete.
	 */
	while (!XEmacLite_IsTxDone(BaseAddress));

}


/*****************************************************************************/
/**
*
* Receive a frame. Wait for a frame to arrive.
*
* @param	BaseAddress is the base address of the device
* @param	FramePtr is a pointer to a buffer where the frame will
*		be stored.
*
* @return
*
* The type/length field of the frame received.  When the type/length field
* contains the type , XEL_MAX_FRAME_SIZE bytes will be copied out of the
* buffer and it is up to the higher layers to sort out the frame.
*
* @note
*
* This function call is blocking in nature, i.e. it will wait until a
* frame arrives.
*
* If the ping buffer is the source of the data, the argument should be
* DeviceAddress + XEL_RXBUFF_OFFSET.
* If the pong buffer is the source of the data, the argument should be
* DeviceAddress + XEL_RXBUFF_OFFSET + XEL_BUFFER_OFFSET.
* The function does not take the different buffers into consideration.
*
******************************************************************************/
u16 XEmacLite_RecvFrame(UINTPTR BaseAddress, u8 *FramePtr)
{
	u16 LengthType;
	u16 Length;
	u32 Register;

	/*
	 * Wait for a frame to arrive - this is a blocking call
	 */
	while (XEmacLite_IsRxEmpty(BaseAddress));

	/*
	 * Get the length of the frame that arrived, only 32-bit reads are
	 * allowed LengthType is in the upper half of the 32-bit word.
	 */
	Register = XEmacLite_ReadReg(BaseAddress, XEL_RPLR_OFFSET);
	LengthType = (u16) ((Register >> 16) &
			    (XEL_RPLR_LENGTH_MASK_HI |
			     XEL_RPLR_LENGTH_MASK_LO));

	/*
	 * Check if length is valid
	 */
	if (LengthType > XEL_MAX_FRAME_SIZE) {
		/*
		 * Field contain type, use max frame size and
		 * let user parse it
		 */
		Length = XEL_MAX_FRAME_SIZE;
	}
	else {
		/*
		 * Use the length in the frame, plus the header and trailer
		 */
		Length = LengthType + XEL_HEADER_SIZE + XEL_FCS_SIZE;
	}

	/*
	 * Read each byte from the EmacLite
	 */
	XEmacLite_AlignedRead((UINTPTR *) (BaseAddress + XEL_RXBUFF_OFFSET),
			      FramePtr, Length);

	/*
	 * Acknowledge the frame
	 */
	Register = XEmacLite_GetRxStatus(BaseAddress);
	Register &= ~XEL_RSR_RECV_DONE_MASK;
	XEmacLite_SetRxStatus(BaseAddress, Register);

	return LengthType;
}

/******************************************************************************/
/**
*
* This function aligns the incoming data and writes it out to a 32-bit
* aligned destination address range.
*
* @param	SrcPtr is a pointer to incoming data of any alignment.
* @param	DestPtr is a pointer to outgoing data of 32-bit alignment.
* @param	ByteCount is the number of bytes to write.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XEmacLite_AlignedWrite(void *SrcPtr, UINTPTR *DestPtr, unsigned ByteCount)
{
	unsigned Index;
	unsigned Length = ByteCount;
	volatile u32 AlignBuffer;
	volatile u32 *To32Ptr;
	u32 *From32Ptr;
	volatile u16 *To16Ptr;
	u16 *From16Ptr;
	volatile u8 *To8Ptr;
	u8 *From8Ptr;

	To32Ptr = DestPtr;

	if ((((u32) SrcPtr) & 0x00000003) == 0) {

		/*
		 * Word aligned buffer, no correction needed.
		 */
		From32Ptr = (u32 *) SrcPtr;

		while (Length > 3) {
			/*
			 * Output each word destination.
			 */
			*To32Ptr++ = *From32Ptr++;

			/*
			 * Adjust length accordingly
			 */
			Length -= 4;
		}

		/*
		 * Set up to output the remaining data, zero the temp buffer
		 first.
		 */
		AlignBuffer = 0;
		To8Ptr = (u8 *) &AlignBuffer;
		From8Ptr = (u8 *) From32Ptr;

	}
	else if ((((u32) SrcPtr) & 0x00000001) != 0) {
		/*
		 * Byte aligned buffer, correct.
		 */
		AlignBuffer = 0;
		To8Ptr = (u8 *) &AlignBuffer;
		From8Ptr = (u8 *) SrcPtr;

		while (Length > 3) {
			/*
			 * Copy each byte into the temporary buffer.
			 */
			for (Index = 0; Index < 4; Index++) {
				*To8Ptr++ = *From8Ptr++;
			}

			/*
			 * Output the buffer
			 */
			*To32Ptr++ = AlignBuffer;

			/*.
			 * Reset the temporary buffer pointer and adjust length.
			 */
			To8Ptr = (u8 *) &AlignBuffer;
			Length -= 4;
		}

		/*
		 * Set up to output the remaining data, zero the temp buffer
		 * first.
		 */
		AlignBuffer = 0;
		To8Ptr = (u8 *) &AlignBuffer;

	}
	else {
		/*
		 * Half-Word aligned buffer, correct.
		 */
		AlignBuffer = 0;

		/*
		 * This is a funny looking cast. The new gcc, version 3.3.x has
		 * a strict cast check for 16 bit pointers, aka short pointers.
		 * The following warning is issued if the initial 'void *' cast
		 * is  not used:
		 * 'dereferencing type-punned pointer will break strict-aliasing
		 * rules'
		 */

		To16Ptr = (u16 *) ((void *) &AlignBuffer);
		From16Ptr = (u16 *) SrcPtr;

		while (Length > 3) {
			/*
			 * Copy each half word into the temporary buffer.
			 */
			for (Index = 0; Index < 2; Index++) {
				*To16Ptr++ = *From16Ptr++;
			}

			/*
			 * Output the buffer.
			 */
			*To32Ptr++ = AlignBuffer;

			/*
			 * Reset the temporary buffer pointer and adjust length.
			 */

			/*
			 * This is a funny looking cast. The new gcc, version
			 * 3.3.x has a strict cast check for 16 bit pointers,
			 * aka short  pointers. The following warning is issued
			 * if the initial 'void *' cast is not used:
			 * 'dereferencing type-punned pointer will break
			 * strict-aliasing  rules'
			 */
			To16Ptr = (u16 *) ((void *) &AlignBuffer);
			Length -= 4;
		}

		/*
		 * Set up to output the remaining data, zero the temp buffer
		 * first.
		 */
		AlignBuffer = 0;
		To8Ptr = (u8 *) &AlignBuffer;
		From8Ptr = (u8 *) From16Ptr;
	}

	/*
	 * Output the remaining data, zero the temp buffer first.
	 */
	for (Index = 0; Index < Length; Index++) {
		*To8Ptr++ = *From8Ptr++;
	}
	if (Length) {
		*To32Ptr++ = AlignBuffer;
	}
}

/******************************************************************************/
/**
*
* This function reads from a 32-bit aligned source address range and aligns
* the writes to the provided destination pointer alignment.
*
* @param	SrcPtr is a pointer to incoming data of 32-bit alignment.
* @param	DestPtr is a pointer to outgoing data of any alignment.
* @param	ByteCount is the number of bytes to read.
*
* @return	None.
*
* @note		None.
*
******************************************************************************/
void XEmacLite_AlignedRead(UINTPTR *SrcPtr, void *DestPtr, unsigned ByteCount)
{
	unsigned Index;
	unsigned Length = ByteCount;
	volatile u32 AlignBuffer;
	u32 *To32Ptr;
	volatile u32 *From32Ptr;
	u16 *To16Ptr;
	volatile u16 *From16Ptr;
	u8 *To8Ptr;
	volatile u8 *From8Ptr;

	From32Ptr = (u32 *) SrcPtr;

	if ((((u32) DestPtr) & 0x00000003) == 0) {

		/*
		 * Word aligned buffer, no correction needed.
		 */
		To32Ptr = (u32 *) DestPtr;

		while (Length > 3) {
			/*
			 * Output each word.
			 */
			*To32Ptr++ = *From32Ptr++;

			/*
			 * Adjust length accordingly.
			 */
			Length -= 4;
		}

		/*
		 * Set up to read the remaining data.
		 */
		To8Ptr = (u8 *) To32Ptr;

	}
	else if ((((u32) DestPtr) & 0x00000001) != 0) {
		/*
		 * Byte aligned buffer, correct.
		 */
		To8Ptr = (u8 *) DestPtr;

		while (Length > 3) {
			/*
			 * Copy each word into the temporary buffer.
			 */
			AlignBuffer = *From32Ptr++;
			From8Ptr = (u8 *) &AlignBuffer;

			/*
			 * Write data to destination.
			 */
			for (Index = 0; Index < 4; Index++) {
				*To8Ptr++ = *From8Ptr++;
			}

			/*
			 * Adjust length
			 */
			Length -= 4;
		}

	}
	else {
		/*
		 * Half-Word aligned buffer, correct.
		 */
		To16Ptr = (u16 *) DestPtr;

		while (Length > 3) {
			/*
			 * Copy each word into the temporary buffer.
			 */
			AlignBuffer = *From32Ptr++;

			/*
			 * This is a funny looking cast. The new gcc, version
			 * 3.3.x has a strict cast check for 16 bit pointers,
			 * aka short pointers. The following warning is issued
			 * if the initial 'void *' cast is not used:
			 * 'dereferencing type-punned pointer will break
			 *  strict-aliasing rules'
			 */
			From16Ptr = (u16 *) ((void *) &AlignBuffer);

			/*
			 * Write data to destination.
			 */
			for (Index = 0; Index < 2; Index++) {
				*To16Ptr++ = *From16Ptr++;
			}

			/*
			 * Adjust length.
			 */
			Length -= 4;
		}

		/*
		 * Set up to read the remaining data.
		 */
		To8Ptr = (u8 *) To16Ptr;
	}

	/*
	 * Read the remaining data.
	 */
	AlignBuffer = *From32Ptr++;
	From8Ptr = (u8 *) &AlignBuffer;

	for (Index = 0; Index < Length; Index++) {
		*To8Ptr++ = *From8Ptr++;
	}
}
/** @} */
