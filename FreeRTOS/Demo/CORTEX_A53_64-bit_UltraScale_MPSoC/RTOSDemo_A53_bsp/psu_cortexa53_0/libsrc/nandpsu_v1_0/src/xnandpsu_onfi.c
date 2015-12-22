/******************************************************************************
*
* Copyright (C) 2015 Xilinx, Inc. All rights reserved.
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
* @file xnandpsu_onfi.c
*
* This file contains the implementation of ONFI specific functions.
*
* @note		None
*
* <pre>
* MODIFICATION HISTORY:
*
* Ver   Who    Date	   Changes
* ----- ----   ----------  -----------------------------------------------
* 1.0   nm     05/06/2014  First release
* </pre>
*
******************************************************************************/

/***************************** Include Files *********************************/
#include "xnandpsu_onfi.h"
#include "xnandpsu.h"

/************************** Constant Definitions *****************************/

/**************************** Type Definitions *******************************/

/***************** Macros (Inline Functions) Definitions *********************/

/************************** Function Prototypes ******************************/

/*****************************************************************************/
/**
*
* This function calculates ONFI paramater page CRC.
*
* @param	Parambuf is a pointer to the ONFI paramater page buffer.
* @param	StartOff is the starting offset in buffer to calculate CRC.
* @param	Length is the number of bytes for which CRC is calculated.
*
* @return
*		CRC value.
* @note
*		None.
*
******************************************************************************/
u32 XNandPsu_OnfiParamPageCrc(u8 *ParamBuf, u32 StartOff, u32 Length)
{
	const u32 CrcInit = 0x4F4EU;
	const u32 Order = 16U;
	const u32 Polynom = 0x8005U;
	u32 i, j, c, Bit;
	u32 Crc = CrcInit;
	u32 DataIn;
	u32 DataByteCount = 0U;
	u32 CrcMask, CrcHighBit;

	CrcMask = ((u32)(((u32)1 << (Order - (u32)1)) -(u32)1) << (u32)1) | (u32)1;
	CrcHighBit = (u32)((u32)1 << (Order - (u32)1));
	/*
	 * CRC covers the data bytes between byte 0 and byte 253
	 * (ONFI 1.0, section 5.4.1.36)
	 */
	for(i = StartOff; i < Length; i++) {
		DataIn = ParamBuf[i];
		c = (u32)DataIn;
		DataByteCount++;
		for(j = 0x80U; j; j >>= 1U) {
			Bit = Crc & CrcHighBit;
			Crc <<= 1U;
			if ((c & j) != 0U) {
				Bit ^= CrcHighBit;
			}
			if (Bit != 0U) {
				Crc ^= Polynom;
			}
		}
		Crc &= CrcMask;
	}
	return Crc;
}
